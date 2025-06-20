import cvc5
from cvc5 import Kind
import json
from collections import defaultdict
from functools import reduce, partial
from util import pretty_print_str_with_brackets, transitive_closure
import datetime
from os import getpid
import multiprocessing
import argparse
from enum import Enum
import random
from subprocess import run
import itertools

from pprint import pprint

from parse_schema import parse_schema, ground_depth
from cedar2json import to_json

import sys
sys.setrecursionlimit(15000)

parser = argparse.ArgumentParser(description='Main program for running the synthesis')
parser.add_argument('--single', action='store_true', help='Run a single synthesis')
# optional argument if single synthesis: number of allows and denies
parser.add_argument('--num_allows', type=int, help='Number of allows', default=None)
parser.add_argument('--num_denies', type=int, help='Number of denies', default=None)
parser.add_argument('--num_conj', '-d', type=int, help='Number of conjunctions', default=None)
parser.add_argument('--verbose','-v', action='store_true', help='Print the grammar and solutions', default=False)
parser.add_argument('--vv', action='store_true', help='Very verbose', default=False)
parser.add_argument('--eq', '-e', action='store_true', help='Find equivalent policy', default=False)
parser.add_argument('--slice', type=int, help='Pick one rule to restrict', default=None)


class Solver():
    def __init__(self, entity_schema, actions, action_scope, hierarchy, entity_store_json, orig_policy, verbose=False, vv=False):
        self.verbose = verbose
        self.vv = vv
        self.actions = actions
        self.action_scope = action_scope
        
        slv = cvc5.Solver()
        self.slv = slv
        tm = slv.getTermManager()
        self.tm = tm
        slv.setLogic("QF_DTSFS")
        slv.setOption("produce-models", "true")
        slv.setOption("random-freq", "0.5")
        slv.setOption("produce-unsat-cores", "true")
        slv.setOption("minimal-unsat-cores", "true")
        # unsat-core-mode=sat-proof
        slv.setOption("unsat-cores-mode", "sat-proof")
        from datetime import datetime
        slv.setOption("sat-random-seed", str(int(datetime.now().timestamp())))
        # tm = cvc5.TermManager()
        self.bool_sort = slv.getBooleanSort()
        self.string_sort = slv.getStringSort()
        self.int_sort = slv.getIntegerSort()

        self.entity_type_map = {'': -1}
        self.entity_map_flat = {'': -1}
        self.entity_map = defaultdict(dict)
        self.entity_map[''] = {'': -1}
        # Define the Entity datatype
        # input_parser = None
        input_parser = cvc5.InputParser(slv)
        input_parser.setStringInput(cvc5.InputLanguage.SMT_LIB_2_6,
        """(declare-datatype Entity ((EntityCtor (type Int) (id Int))))""", "myInput")
        sm = input_parser.getSymbolManager()
        cmd = input_parser.nextCommand()
        # print(f"Executing command {cmd}:")
        cmd.invoke(slv, sm)
        input_parser.setStringInput(cvc5.InputLanguage.SMT_LIB_2_6,
        """EntityCtor""", "myInput")
        entity_ctor_fun = input_parser.nextTerm()
        self.entity_sort = entity_ctor_fun.getSort().getDatatypeConstructorCodomainSort()
        # exit()


        # entity_ctor = slv.mkDatatypeConstructorDecl("Entity")
        # entity_ctor.addSelector("type", int_sort)
        # entity_ctor.addSelector("id", int_sort)
        # entity_sort = slv.declareDatatype("Entity", entity_ctor)
        # entity_ctor_fun = entity_sort.getDatatype().getConstructor("Entity").getTerm()
        self.entity = lambda x, y: slv.mkTerm(Kind.APPLY_CONSTRUCTOR, entity_ctor_fun, slv.mkInteger(self.entity_type_map[x]), slv.mkInteger(self.entity_map_flat[y]))

        # Define has_attr function
        has_attr_entity_arg = slv.mkVar(self.entity_sort, "Entity")
        # has_attr_type_arg = slv.mkVar(self.string_sort, "Type")
        has_attr_attr_arg = slv.mkVar(self.string_sort, "attr")
        has_attr_type_ite = {}
        # has_attr_list = []

        # get attrs
        get_attrs = {}
        types_with_defined_grammar = ["Long", "String", "Boolean"]
        to_define_grammar_types = []

        # hierarchy of types
        entity_in_entity = slv.mkVar(self.entity_sort, "e1")
        entity_in_in = slv.mkVar(self.entity_sort, "e2")
        entity_heirarchies = []

        # helper functions
        entity_id_selector = self.entity_sort.getDatatype().getConstructor("EntityCtor").getSelector("id").getTerm()
        self.id_of_entity = lambda x: slv.mkTerm(Kind.APPLY_SELECTOR, entity_id_selector, x)
        entity_type_selector = self.entity_sort.getDatatype().getConstructor("EntityCtor").getSelector("type").getTerm()
        self.type_of_entity = lambda x: slv.mkTerm(Kind.APPLY_SELECTOR, entity_type_selector, x)

        entity_eq_arg1 = slv.mkVar(self.entity_sort, "entity1")
        entity_eq_arg2 = slv.mkVar(self.entity_sort, "entity2")
        entity_eq_fun = slv.mkTerm(Kind.EQUAL, entity_eq_arg1, entity_eq_arg2)
        self.entity_eq = slv.defineFun("entity_eq", [entity_eq_arg1, entity_eq_arg2], self.bool_sort, entity_eq_fun)

        self.type_id_counter = 0
        list_entity_types = []
        for type in entity_schema.keys():
            self.entity_type_map[type] = self.type_id_counter
            self.type_id_counter += 1
            has_attr_type = self.type_of_entity(has_attr_entity_arg)
            type_cond = slv.mkTerm(Kind.EQUAL, has_attr_type, slv.mkInteger(self.entity_type_map[type]))
            ite = partial(slv.mkTerm,Kind.ITE, type_cond)
            has_attr_type_ite[type] = [ite, []]
            list_entity_types.append(type)

        if verbose:
            print("Entity type map: ", self.entity_type_map)

        list_entities = defaultdict(list)

        self.entity_id_counter = 0
        # Parse entities in entity store
        # For each entity
        for e in entity_store_json:
            entity_type = e["uid"]["__entity"]["type"]
            id = e["uid"]["__entity"]["id"]
            self.entity_map[entity_type][id] = self.entity_id_counter
            self.entity_map_flat[id] = self.entity_id_counter
            self.entity_id_counter += 1
            list_entities[entity_type].append(self.entity(entity_type, id))
            if entity_type not in entity_schema:
                raise ValueError(f"Entity type {entity_type} not found in schema")
        
        if verbose:
            print("Entity map: ", self.entity_map)

        for e in entity_store_json:
            attrs = e["attrs"]
            entity_type = e["uid"]["__entity"]["type"]
            id = e["uid"]["__entity"]["id"]
            # For every attribute in the entity
            for attr_name, attr_val in attrs.items():
                # check type of attribute in schema
                if attr_name not in entity_schema[entity_type]:
                    raise ValueError(f"Attribute {attr_name} not found in schema for entity type {type}")
                attr_type_str = entity_schema[entity_type][attr_name]
                attr_type = self.get_type_of(attr_type_str)
                if (attr_name, attr_type_str) not in get_attrs:
                    default_val = self.default_val_of(attr_type_str)
                    get_attrs[(attr_name, attr_type_str)] = ["__get_attr_" + attr_name + "_" + self.get_canonical_type_name(attr_type_str), [slv.mkVar(self.entity_sort, "e")], attr_type, {}, default_val]
                get_attr_arg = get_attrs[(attr_name, attr_type_str)][1][0]
                parsed_value = self.parse_type(attr_type_str, attr_val)

                
                get_attr_ite = partial(slv.mkTerm, Kind.ITE, slv.mkTerm(Kind.EQUAL, self.id_of_entity(get_attr_arg),slv.mkInteger(self.entity_map_flat[id])) , parsed_value)
                # add to get_attrs dict
                if entity_type not in get_attrs[(attr_name, attr_type_str)][3]:
                    get_attr_type_ite = partial(slv.mkTerm, Kind.ITE, slv.mkTerm(Kind.EQUAL, self.type_of_entity(get_attr_arg), slv.mkInteger(self.entity_type_map[entity_type])))
                    get_attrs[(attr_name, attr_type_str)][3][entity_type] = [get_attr_type_ite, []]
                get_attrs[(attr_name, attr_type_str)][3][entity_type][1].append(get_attr_ite)

                has_attr_cond_name = slv.mkTerm(Kind.EQUAL, has_attr_attr_arg, slv.mkString(attr_name))
                # has_attr_cond_type = slv.mkTerm(Kind.EQUAL, has_attr_type_arg, slv.mkString(self.get_canonical_type_name(attr_type_str)))
                has_attr_cond_entity_name = slv.mkTerm(Kind.EQUAL, self.id_of_entity(has_attr_entity_arg),slv.mkInteger(self.entity_map_flat[id]))

                has_attr_cond = slv.mkTerm(Kind.AND, has_attr_cond_name, has_attr_cond_entity_name) # has_attr_cond_type


                has_attr_type_ite[entity_type][1].append(partial(slv.mkTerm, Kind.ITE, has_attr_cond, slv.mkTrue()))

            # parents
            parents = e["parents"]
            for parent in parents:
                parent_type = parent["__entity"]["type"]
                parent_id = parent["__entity"]["id"]
                # print((entity_type, id), (parent_type, parent_id))
                entity_heirarchies.append(((entity_type, id), (parent_type, parent_id)))

        # Functions in the policy grammar
        entity_is_arg_entity = slv.mkVar(self.entity_sort, "entity")
        entity_is_arg_type = slv.mkVar(self.int_sort, "type")
        entity_is_fun = slv.mkTerm(Kind.EQUAL, slv.mkTerm(Kind.APPLY_SELECTOR, self.entity_sort.getDatatype().getConstructor("EntityCtor").getSelector("type").getTerm(), entity_is_arg_entity), entity_is_arg_type)
        self.entity_is = slv.defineFun("entity_is", [entity_is_arg_entity, entity_is_arg_type], self.bool_sort, entity_is_fun)

        # allow_header: (p and a and r) and body
        allow_header_principal = slv.mkVar(self.bool_sort, "p")
        allow_header_action = slv.mkVar(self.bool_sort, "a")
        allow_header_resource = slv.mkVar(self.bool_sort, "r")
        allow_header_predbody = slv.mkVar(self.bool_sort, "predbody")
        allow_header_body = slv.mkTerm(Kind.AND, slv.mkTerm(Kind.AND, slv.mkTerm(Kind.AND, allow_header_principal, allow_header_action), allow_header_resource), allow_header_predbody)
        allow_header = slv.defineFun("allow_header", [allow_header_principal, allow_header_action, allow_header_resource, allow_header_predbody], self.bool_sort, allow_header_body)

        # deny_header: (p and a and r) => not body
        deny_header_principal = slv.mkVar(self.bool_sort, "p")
        deny_header_action = slv.mkVar(self.bool_sort, "a")
        deny_header_resource = slv.mkVar(self.bool_sort, "r")
        deny_header_predbody = slv.mkVar(self.bool_sort, "predbody")
        deny_header_body = slv.mkTerm(Kind.IMPLIES, slv.mkTerm(Kind.AND, slv.mkTerm(Kind.AND, deny_header_principal, deny_header_action), deny_header_resource), slv.mkTerm(Kind.NOT, deny_header_predbody))
        deny_header = slv.defineFun("deny_header", [deny_header_principal, deny_header_action, deny_header_resource, deny_header_predbody], self.bool_sort, deny_header_body)

        # Define has_attr function
        has_attr_bodies = []
        # outer = ite on type
        # inner = list of ite on the particular entity name
        for _, (outer, inner) in has_attr_type_ite.items():
            try:
                body = reduce(lambda a, b: lambda e: a(b(e)), inner)(slv.mkFalse())
            except TypeError:
                body = slv.mkFalse()
            has_attr_bodies.append(partial(outer, body))

        has_attr_body = reduce(lambda a, b: lambda e: a(b(e)), has_attr_bodies)(slv.mkFalse())
        # self.has_attr = slv.defineFun("has_attr", [has_attr_entity_arg, has_attr_type_arg, has_attr_attr_arg], self.bool_sort, has_attr_body)
        self.has_attr = slv.defineFun("has_attr", [has_attr_entity_arg, has_attr_attr_arg], self.bool_sort, has_attr_body)

        # Define get_attrs functions
        self.get_attrs_func = {}
        for (name, type), inner in get_attrs.items():
            *_args, func_body, default_arg = inner
            get_attr_bodies = []
            # outer = ite on type
            # inner = list of ite on the particular entity name
            for _, (outer, inner) in func_body.items():
                body = reduce(lambda a, b: lambda e: a(b(e)), inner)(default_arg)
                get_attr_bodies.append(partial(outer, body))
            get_attr_body = reduce(lambda a, b: lambda e: a(b(e)), get_attr_bodies)(default_arg)
            get_attr = slv.defineFun(*_args, get_attr_body)
            self.get_attrs_func[name] = (get_attr, type)
            if type[0] != "Entity" and type not in types_with_defined_grammar:
                # we need to add a grammar rule for this type
                types_with_defined_grammar.append(type)
                to_define_grammar_types.append(type)

        # Define contexts
        self.contexts = []
        self.contexts_action_map = defaultdict(dict)
        for action, keys in action_scope.items():
            if 'context' in keys['appliesTo']:
                ctx_shape = keys['appliesTo']['context']['attributes']
                for attr, attr_type in ctx_shape.items():
                    # print(attr_type)
                    if attr_type['type'] == "Entity":
                        raise NotImplementedError("Context attribute of type Entity is not supported")
                    t = self.get_type_of((attr_type['type'],))
                    option_t = tm.mkNullableSort(t)
                    self.contexts.append((attr, option_t))
                    self.contexts_action_map[action][attr]= (option_t, attr_type['required'])

        # Sanity check.
        # If context has attributes of same name but different types, then error
        for (a1, t1), (a2, t2) in itertools.combinations(self.contexts, 2):
            if a1 == a2 and t1 != t2:
                raise ValueError(f"Context attribute {a1} has different types {t1} and {t2}, not supported")
        
        self.context_sort = tm.mkRecordSort(*self.contexts)
        self.context_type = self.context_sort.getDatatype()

        context_has_ctx = slv.mkVar(self.context_sort, "ctx")
        context_has_attr_name = slv.mkVar(self.string_sort, "name")
        context_has_body_lst = []
        for f, t in self.contexts:
            if_name_f = slv.mkTerm(Kind.EQUAL, context_has_attr_name, slv.mkString(f))
            ctx_f = slv.mkTerm(Kind.APPLY_SELECTOR, self.context_type.getSelector(f).getTerm(), context_has_ctx)
            not_null_test = slv.mkNullableIsSome(ctx_f)
            # if_non_null = slv.mkTerm(Kind.APPLY_UF, not_null_test, ctx_f)
            test = slv.mkTerm(Kind.AND, if_name_f, not_null_test)
            context_has_body_lst.append(test)
        context_has_body = slv.mkTerm(Kind.OR, slv.mkFalse(), *context_has_body_lst) if context_has_body_lst else slv.mkFalse()
        self.context_has = slv.defineFun("ctx_has_attr", [context_has_ctx, context_has_attr_name], self.bool_sort, context_has_body)
        # exit()
        # Define entity hierarchy predicate

        # obtain the transitive closure of the entity hierarchy
        entity_heirarchy_closure = transitive_closure(entity_heirarchies)
        heirarchy_cond = [
            slv.mkTerm(
                Kind.AND,
                slv.mkTerm(Kind.EQUAL, self.entity(type, id), entity_in_entity),
                slv.mkTerm(Kind.EQUAL, self.entity(parent_type, parent_id), entity_in_in)) for (type, id), (parent_type, parent_id) in entity_heirarchy_closure]
        heirarchy_ites = [partial(slv.mkTerm, Kind.ITE, cond, slv.mkTrue()) for cond in heirarchy_cond]
        entity_in_body = reduce(lambda a, b: lambda e: a(b(e)), heirarchy_ites)(slv.mkFalse()) if heirarchy_ites else slv.mkFalse()
        self.entity_in = slv.defineFun("entity_in", [entity_in_entity, entity_in_in], self.bool_sort, entity_in_body)

        # Also consider attribute depths, e.g. principal.attr1.attr2.attr3
        attribute_depths = [ground_depth(entity_schema, i) for i in range(1, 3+1)]
        # Get entities that can be obtained from attributes
        list_entities_from_attr = defaultdict(list)
        from_attr = defaultdict(list)
        attr_getter = defaultdict(list)

        entity_var = slv.mkVar(self.entity_sort, "e")
        for depth_i_attr in attribute_depths:
            for attr_chain in depth_i_attr:
                chain_iter = iter(attr_chain)
                (type0, attr0, attr_type) = next(chain_iter)
                # name = [type0, attr0]
                term = slv.mkTerm(Kind.APPLY_UF, self.get_attrs_func[attr0][0], entity_var)
                for (type, attr, attr_type) in chain_iter:
                    term = slv.mkTerm(Kind.APPLY_UF, self.get_attrs_func[attr][0], term)
                    # name.append(attr)
                # print('.'.join(name))
                # e of type type0 has a getter term.sub(entity_var, e) that outputs attr_type
                attr_getter[type0].append([term, attr_type])
                # for adding to grammar (type not entity)
                from_attr[self.get_canonical_type_name(attr_type)].append(term)
                if attr_type[0] == "Entity":
                    # for adding to grammar
                    list_entities_from_attr[attr_type[1]].append(term)


        # Encode original policy as smt
        policy_json = json.loads(to_json(orig_policy))
        self.num_rules = len(policy_json)
        ## Rule_vars
        self.rule_p = slv.mkVar(self.entity_sort, "p")
        self.rule_a = slv.mkVar(self.string_sort, "a")
        self.rule_r = slv.mkVar(self.entity_sort, "r")
        self.rule_ctx = slv.mkVar(self.context_sort, "ctx")

        allow_rules_list = []
        deny_rules_list = []
        self.encoded_rules = []
        self.encoded_rules_metadata = []
        # Parse header
        for policy in policy_json:
            effect = policy["effect"]
            p_restriction, a_restriction, r_restriction = None, None, None
            metadata = {}
            for var in policy["variables"]:
                ident = var["ident"]
                target = None
                match ident: 
                    case "Principal":
                        target = self.rule_p
                    case "Action":
                        target = self.rule_a
                    case "Resource":
                        target = self.rule_r
                restriction = None
                if "rel" in var:
                    match var["rel"]:
                        case "Eq":
                            expr = var['rel_to']['expr']['initial']['initial']['initial']['initial']['item']['item']
                            match expr["stype"]:
                                case 'ref':
                                    if ident == "Action":
                                        restriction = slv.mkTerm(Kind.EQUAL, target, slv.mkString(expr['val']['eid']))
                                        metadata["Action"] = ("Eq", expr['val']['eid'])
                                    else:
                                        restriction = slv.mkTerm(Kind.APPLY_UF,self.entity_eq, target, self.entity(expr['val']['path'], expr['val']['eid']))
                                        metadata[ident] = ("Eq", (expr['val']['path'], expr['val']['eid']))
                                case _:
                                    raise Exception()
                        case "In":
                            expr = var['rel_to']['expr']['initial']['initial']['initial']['initial']['item']['item']
                            match expr["stype"]:
                                case 'ref':
                                    if ident == "Action":
                                        restriction = slv.mkTerm(Kind.EQUAL, target, slv.mkString(expr['val']['eid']))
                                        metadata["Action"] = ("Eq", expr['val']['eid'])
                                    else:
                                        restriction = slv.mkTerm(Kind.APPLY_UF,self.entity_in, target, self.entity(expr['val']['path'], expr['val']['eid']))
                                        metadata[ident] = ("In", (expr['val']['path'], expr['val']['eid']))
                                case 'list':
                                    if ident != "Action":
                                        print("This is impossible")
                                        raise Exception("cannot have \"principal/resource in [entities...]\"")
                                    _actions = [entry['expr']['initial']['initial']['initial']['initial']['item']['item']['val']['eid'] for entry in expr['val']]
                                    action_restriction = slv.mkTerm(Kind.EQUAL, target, slv.mkString(actions[0]))
                                    for a in _actions[1:]:
                                        action_restriction = slv.mkTerm(Kind.OR, slv.mkTerm(Kind.EQUAL, target, slv.mkString(a)), action_restriction)
                                    restriction = action_restriction
                                    metadata["Action"] = ("List", _actions)
                elif "is" in var:
                    t = var["is"]
                    restriction = slv.mkTerm(Kind.APPLY_UF,self.entity_is, target, slv.mkInteger(self.entity_type_map[t]))
                    metadata[ident] = ("Is", t)
                else:
                    restriction = slv.mkTrue()
                    metadata[ident] = ("True", None)
                match ident:
                    case "Principal":
                        p_restriction = restriction
                    case "Action":
                        a_restriction = restriction
                    case "Resource":
                        r_restriction = restriction
            assert(len(policy["conditions"]) <= 1)
            cond = self.parse_expr(policy["conditions"][0]) if len(policy["conditions"]) == 1 else slv.mkTrue()
            metadata["cond"] = cond
            if effect == "Permit":
                rule = slv.mkTerm(Kind.APPLY_UF, allow_header, p_restriction, a_restriction, r_restriction, cond)
                allow_rules_list.append(rule)
            else:
                rule = slv.mkTerm(Kind.APPLY_UF, deny_header, p_restriction, a_restriction, r_restriction, cond)
                deny_rules_list.append(rule)
            self.encoded_rules_metadata.append(metadata)
            self.encoded_rules.append(rule)
        

    def get_type_of(self, type):
        type_0, *type_args = type
        if type_0 == "Entity":
            return self.entity_sort
        elif type_0 == "Long":
            return self.slv.getIntegerSort()
        elif type_0 == "String":
            return self.slv.getStringSort()
        elif type_0 == "Boolean":
            return self.slv.getBooleanSort()
        elif type_0 == "Set":
            set_of_type = self.get_type_of(type_args[0])
            return self.slv.mkSetSort(set_of_type)
        elif type_0 == "Record":
            raise NotImplementedError("Record type not implemented")
        else:
            raise NotImplementedError(f"Type {type} not implemented")

    def default_val_of(self, type):
        type_0, *type_args = type
        if type_0 == "Long":
            return self.slv.mkInteger(0)
        elif type_0 == "String":
            return self.slv.mkString("")
        elif type_0 == "Boolean":
            return self.slv.mkFalse()
        elif type_0 == "Entity":
            return self.entity("", "")
        elif type_0 == "Set":
            return self.slv.mkEmptySet(self.slv.mkSetSort(self.get_type_of(type_args[0])))
        elif type_0 == "Record":
            raise NotImplementedError("Record type not implemented")
        else:
            raise NotImplementedError(f"Type {type} not implemented")
        
    def parse_type(self, type, json):
        type_0, *type_args = type
        if type_0 == "Entity":
            e_type = json["__entity"]["type"]
            e_id = json["__entity"]["id"]
            return self.entity(e_type, e_id)
        elif type_0 == "Long":
            return self.slv.mkInteger(json)
        elif type_0 == "String":
            return self.slv.mkString(json)
        elif type_0 == "Boolean":
            return self.slv.mkBoolean(json)
        elif type_0 == "Set":
            items = (self.parse_type(type_args[0], item) for item in json)
            set_singletons = (self.slv.mkTerm(Kind.SET_SINGLETON, i) for i in items)
            try:
                return reduce(lambda a, b: self.slv.mkTerm(Kind.SET_UNION, a, b), set_singletons)
            except TypeError:
                return self.slv.mkEmptySet(self.slv.mkSetSort(self.get_type_of(type_args[0])))
        elif type_0 == "Record":
            raise NotImplementedError("Record type not implemented")
        else:
            raise NotImplementedError(f"Type {type} not implemented")

    def get_canonical_type_name(self, type):
        type_0, *_ = type
        if type_0 == "Entity":
            return str(type)
        elif type_0 == "Long":
            return "Long"
        elif type_0 == "String":
            return "String"
        elif type_0 == "Boolean":
            return "Boolean"
        elif type_0 == "Set":
            return str(type)
        elif type_0 == "Record":
            raise NotImplementedError("Record type not implemented")
        else:
            raise NotImplementedError(f"Type {type} not implemented")

    ######## Symbolic compiler of the initial policy ########
    def parse_primary(self, primary_json):
        assert(primary_json['type'] == 'primary')
        match primary_json['stype']:
            case 'literal':
                print("primary", primary_json)
                pass
            case 'ref':
                val = primary_json['val']
                path = val["path"]
                eid = val["eid"]
                # print(entity(path, eid))
                if path != "Action":
                    return self.entity(path, eid)
                else:
                    # Action::eid
                    return self.slv.mkString(eid)
            case 'name':
                match primary_json['val']:
                    case 'Principal':
                        return self.rule_p
                    case 'Action':
                        return self.rule_a
                    case 'Resource':
                        return self.rule_r
                    case 'Context':
                        return self.rule_ctx
                if primary_json['val'] in self.entity_type_map:
                    return self.slv.mkInteger(self.entity_type_map[primary_json['val']])
                if primary_json['val'] in self.actions:
                    return self.slv.mkString(primary_json['val'])
                return self.slv.mkString(primary_json['val'])
            case 'expr':
                return self.parse_expr(primary_json['val'])
            case 'eList':
                print("primary", primary_json)
                pass
        print(primary_json)
        raise NotImplementedError

    def parse_member(self, member_json):
        assert(member_json['type'] == 'member')
        item = self.parse_primary(member_json['item'])
        if 'access' not in member_json:
            return item
        new_item = item
        if item.getSort() == self.entity_sort:
            for access in member_json['access']:
                new_item = self.slv.mkTerm(Kind.APPLY_UF, self.get_attrs_func[access][0], new_item)
        elif item.getSort() == self.context_sort:
            access = member_json['access'][0]
            # print(self.tm.mkNullableVal(self.context_type.getSelector(access).getTerm()))
            new_item = self.tm.mkNullableVal(self.slv.mkTerm(Kind.APPLY_SELECTOR, self.context_type.getSelector(access).getTerm(), new_item))
            for access in member_json['access'][1:]:
                if new_item.getSort() != self.entity_sort:
                    raise Exception("Attribute access is not an entity")
                new_item = self.slv.mkTerm(Kind.APPLY_SELECTOR, self.get_attrs_func[access][0], new_item)
        return new_item


    def parse_unary(self, unary_json):
        assert(unary_json['type'] == 'unary')
        item = self.parse_member(unary_json['item'])
        match unary_json['op']:
            case 'None':
                return item
            case 'Bang':
                for _ in range(int(unary_json['count'])):
                    item = self.slv.mkTerm(Kind.NOT, item)
                return item
            case 'Dash':
                pass
        return NotImplemented()

    def parse_mult(self, mult_json):
        assert(mult_json['type'] == 'mult')
        if 'extended' not in mult_json:
            return self.parse_unary(mult_json['initial'])
        assert(len(mult_json['extended']) == 1)
        ext = mult_json['extended'][0]
        match ext['op']:
            case 'Times':
                pass
            case 'Divide':
                pass
            case 'Mod':
                pass
        raise NotImplementedError

    def parse_add(self, add_json):
        assert(add_json['type'] == 'add')
        if 'extended' not in add_json:
            return self.parse_mult(add_json['initial'])
        assert(len(add_json['extended']) == 1)
        ext = add_json['extended'][0]
        rval = self.parse_mult(ext['initial'])
        match ext['op']:
            case 'Plus':
                pass
            case 'Minus':
                pass
        raise NotImplementedError

    def parse_relation(self, rel_json):
        match rel_json["ctype"]:
            case "common":
                initial = self.parse_add(rel_json['initial'])
                if 'extended' not in rel_json:
                    return initial
                assert(len(rel_json['extended']) == 1)
                ext = rel_json['extended'][0]
                rval = self.parse_add(ext['rel_to'])
                match ext['rel']:
                    case "Less":
                        pass
                    case "LessEq":
                        pass
                    case "GreaterEq":
                        pass
                    case "Greater":
                        pass
                    case "NotEq":
                        pass
                    case "Eq":
                        if rval.getSort() == self.entity_sort:
                            return self.slv.mkTerm(Kind.APPLY_UF, self.entity_eq, initial, rval)
                        else:
                            return self.slv.mkTerm(Kind.EQUAL, initial, rval)
                    case "In":
                        if rval.getSort() == self.entity_sort:
                            return self.slv.mkTerm(Kind.APPLY_UF, self.entity_in, initial, rval)
                        else:
                            # set
                            assert(rval.getSort().isSet())
                            return self.slv.mkTerm(Kind.SET_MEMBER, initial, rval)
                        # return self.slv.mkTerm(Kind.APPLY_UF, self.entity_in, initial, rval)
            case "has":
                # print(rel_json)
                field = self.parse_add(rel_json['field'])
                target = self.parse_add(rel_json['target'])
                if target.getSort() == self.entity_sort:
                    assert(field.getSort() == self.string_sort)
                    assert(target.getSort() == self.entity_sort)
                    return self.slv.mkTerm(Kind.APPLY_UF, self.has_attr, target, field)
                elif target.getSort() == self.context_sort:
                    return self.slv.mkTerm(Kind.APPLY_UF, self.context_has, target, field)
                raise Exception
            case "is_in":
                target = self.parse_add(rel_json['target'])
                entity_type =  self.parse_add(rel_json['entity_type'])
                if "in_entity" in rel_json:
                    raise NotImplementedError
                return self.slv.mkTerm(Kind.APPLY_UF, self.entity_is, target, entity_type)
        print(rel_json["ctype"])
        raise NotImplementedError

    def parse_and(self, and_json):
        assert(and_json['type'] == 'and')
        initial = self.parse_relation(and_json['initial'])
        if 'extended' not in and_json:
            return initial
        rv = initial
        for ands in and_json['extended']:
            val = self.parse_relation(ands)
            rv = self.slv.mkTerm(Kind.AND, rv, val)
        return rv

    def parse_expr(self, expr_json):
        assert(expr_json['type'] == 'expr')
        expr = expr_json['expr']
        match expr_json['stype']:
            case 'singleton_expr': # A singular And expression
                return self.parse_and(expr)
            case 'or': # A disjunction of expressions
                rv = self.parse_and(expr['initial'])
                for ext in expr['extended']:
                    val = self.parse_and(ext)
                    rv = self.slv.mkTerm(Kind.OR, rv, val)
                return rv
            case 'ite':
                raise NotImplemented("Not implemented ite for policy encoding")
        raise ValueError()

    def get_pt(self, log, synth_rule, check_log=False):
        # declare input variables for the functions-to-synthesize
        principal = self.slv.mkConst(self.entity_sort, "principal")
        action = self.slv.mkConst( self.string_sort, "action")
        resource = self.slv.mkConst(self.entity_sort, "resource")
        ctx = self.slv.mkConst(self.context_sort, "ctx")
        self.slv.assertFormula(self.slv.mkTerm(Kind.GEQ, self.id_of_entity(principal), self.slv.mkInteger(0)))
        self.slv.assertFormula(self.slv.mkTerm(Kind.LEQ, self.id_of_entity(principal), self.slv.mkInteger(self.entity_id_counter)))
        self.slv.assertFormula(self.slv.mkTerm(Kind.GEQ, self.type_of_entity(principal), self.slv.mkInteger(0)))
        self.slv.assertFormula(self.slv.mkTerm(Kind.LEQ, self.type_of_entity(principal), self.slv.mkInteger(self.type_id_counter)))
        self.slv.assertFormula(self.slv.mkTerm(Kind.GEQ, self.id_of_entity(resource), self.slv.mkInteger(0)))
        self.slv.assertFormula(self.slv.mkTerm(Kind.LEQ, self.id_of_entity(resource), self.slv.mkInteger(self.entity_id_counter)))
        self.slv.assertFormula(self.slv.mkTerm(Kind.GEQ, self.type_of_entity(resource), self.slv.mkInteger(0)))
        self.slv.assertFormula(self.slv.mkTerm(Kind.LEQ, self.type_of_entity(resource), self.slv.mkInteger(self.type_id_counter)))
        # slv.assertFormula(slv.mkTerm(Kind.NOT, slv.mkTerm(Kind.EQUAL, action, slv.mkString(""))))
        # print(encoded_rules[synth_rule])
        sat = self.encoded_rules[synth_rule].substitute([self.rule_p, self.rule_a, self.rule_r, self.rule_ctx], [principal, action, resource, ctx])
        self.slv.assertFormula(sat)
        if self.verbose:
            print("Asserting: ", sat)
        # action need to be one of the actions
        action_arg_restriction = self.slv.mkTerm(Kind.OR, *[self.slv.mkTerm(Kind.EQUAL, action, self.slv.mkString(a)) for a in self.actions])
        self.slv.assertFormula(action_arg_restriction)
        if self.verbose:
            print("Action restriction: ", action_arg_restriction)

        # print(entity_type_map)
        # print(action_scope)
        # print(self.contexts_action_map)
        for a in self.action_scope:
            rtypes = self.action_scope[a]["appliesTo"]["resourceTypes"]
            ptypes = self.action_scope[a]["appliesTo"]["principalTypes"]
            # action = a => r in rtypes and p in ptypes
            action_restriction = self.slv.mkTerm(Kind.EQUAL, action, self.slv.mkString(a))
            principal_restriction = self.slv.mkTerm(Kind.OR, self.slv.mkFalse(), *[self.slv.mkTerm(Kind.EQUAL, self.type_of_entity(principal), self.slv.mkInteger(self.entity_type_map[p])) for p in ptypes])
            resource_restriction = self.slv.mkTerm(Kind.OR, self.slv.mkFalse(), *[self.slv.mkTerm(Kind.EQUAL, self.type_of_entity(resource), self.slv.mkInteger(self.entity_type_map[r])) for r in rtypes])
            self.slv.assertFormula(self.slv.mkTerm(Kind.IMPLIES, action_restriction, self.slv.mkTerm(Kind.AND, principal_restriction, resource_restriction)))
            if self.verbose:
                # print(f"Action restriction: {action_restriction}")
                # print(f"Principal restriction: {principal_restriction}")
                # print(f"Resource restriction: {resource_restriction}")
                print("Action-Type restriction:" , self.slv.mkTerm(Kind.IMPLIES, action_restriction, self.slv.mkTerm(Kind.AND, principal_restriction, resource_restriction)))
            # ctx restriction
            for f, t in self.contexts:
                if f in self.contexts_action_map[a]:
                    _, required = self.contexts_action_map[a][f]
                    ctx_restriction = self.slv.mkTerm(Kind.APPLY_SELECTOR, self.context_type.getSelector(f).getTerm(), ctx)
                    if required:
                        term = self.slv.mkTerm(Kind.IMPLIES, action_restriction, self.slv.mkTerm(Kind.NOT, self.slv.mkNullableIsNull(ctx_restriction)))
                        self.slv.assertFormula(term)
                        if self.verbose:
                            print("Context restriction: ", term)
                    # else:
                        # print("who cares: ", f, t)
                else:
                    ctx_restriction = self.slv.mkTerm(Kind.APPLY_SELECTOR, self.context_type.getSelector(f).getTerm(), ctx)
                    term = self.slv.mkTerm(Kind.IMPLIES, action_restriction, self.slv.mkNullableIsNull(ctx_restriction))
                    self.slv.assertFormula(term)
                    if self.verbose:
                        print("Context restriction: ", term)
                        



        entity_type_rmap = {v: k for k, v in self.entity_type_map.items()}
        entity_name_rmap = {v: k for k, v in self.entity_map_flat.items()}
        # ptype = T => id in entity_name_rmap[T]
        for e in [principal, resource]:
            for type in entity_type_rmap:
                if type == -1:
                    continue
                type_restriction = self.slv.mkTerm(Kind.EQUAL, self.type_of_entity(e), self.slv.mkInteger(type))
                id_restriction = self.slv.mkTerm(Kind.OR, self.slv.mkFalse(), *[self.slv.mkTerm(Kind.EQUAL, self.id_of_entity(e), self.slv.mkInteger(id)) for id in self.entity_map[entity_type_rmap[type]].values()])
                self.slv.assertFormula(self.slv.mkTerm(Kind.IMPLIES, type_restriction, id_restriction))
            
        # distance_func_list = []
        # d_principal = self.slv.mkVar(self.entity_sort, "p")
        # for e in [principal, resource]:
        #     for type in entity_type_rmap:
        #         if type == -1:
        #             continue
        #         type_eq = self.slv.mkTerm(Kind.EQUAL, self.type_of_entity(e), self.slv.mkInteger(type))
        #         id_eq = self.slv.mkTerm(Kind.EQUAL, self.id_of_entity(e), d_principal)
                
        # distance_func = self.slv.defineFun("distance", [d_principal], self.int_sort, )

        def log_entry(p, a, r, entry_ctx, decision):
            entry_ctx_encoded = self.parse_ctx(entry_ctx)
            constraint = self.slv.mkTerm(Kind.NOT, self.slv.mkTerm( Kind.AND,
                self.slv.mkTerm(Kind.EQUAL, self.type_of_entity(principal), self.slv.mkInteger(self.entity_type_map[p[0]])),
                self.slv.mkTerm(Kind.EQUAL, self.id_of_entity(principal), self.slv.mkInteger(self.entity_map_flat[p[1]])),
                self.slv.mkTerm(Kind.EQUAL, self.type_of_entity(resource), self.slv.mkInteger(self.entity_type_map[r[0]])),
                self.slv.mkTerm(Kind.EQUAL, self.id_of_entity(resource), self.slv.mkInteger(self.entity_map_flat[r[1]])),
                self.slv.mkTerm(Kind.EQUAL, action, self.slv.mkString(a)),
                self.slv.mkTerm(Kind.EQUAL, ctx, entry_ctx_encoded)
            ))

            self.slv.assertFormula(constraint)
            if check_log:
                truth = self.encoded_rules[synth_rule].substitute(
                    [self.rule_p, self.rule_a, self.rule_r, self.rule_ctx],
                    [self.entity(*p), self.slv.mkString(a), self.entity(*r), entry_ctx_encoded])
                sanity_check = self.slv.mkTerm(Kind.EQUAL, truth, self.slv.mkTrue() if decision else self.slv.mkFalse())
                self.slv.assertFormula(sanity_check)
                if self.verbose:
                    # print("Log entry: ", constraint)
                    print("Sanity check: ", sanity_check)
                    
        for l in log:
            log_entry(*l)

        # r2 = slv.checkSatAssuming(action_arg_restriction)
        r2 = self.slv.checkSat()
        if r2.isSat():
            # print(slv.simplify(encoded_rules[synth_rule]))
            p = self.slv.getValue(principal)
            p_type = entity_type_rmap[self.slv.getValue(self.type_of_entity(p)).toPythonObj()]
            p_id = entity_name_rmap[self.slv.getValue(self.id_of_entity(p)).toPythonObj()]
            a = self.slv.getValue(action).toPythonObj()
            r = self.slv.getValue(resource)
            r_type = entity_type_rmap[self.slv.getValue(self.type_of_entity(r)).toPythonObj()]
            r_id = entity_name_rmap[self.slv.getValue(self.id_of_entity(r)).toPythonObj()]
            context = self.slv.getValue(ctx)
            context_dict = {}
            for f, t in self.contexts:
                c_f = self.slv.mkTerm(Kind.APPLY_SELECTOR, self.context_type.getSelector(f).getTerm(), context)
                v = self.slv.getValue(c_f)
                v_is_null = self.slv.getValue(self.tm.mkNullableIsNull(v)).toPythonObj()
                if v_is_null:
                    # print("is null")
                    context_dict[f] = None
                else:
                    # print(v)
                    v = self.slv.getValue(self.tm.mkNullableVal(v))
                    if v.getSort() == self.entity_sort:
                        # raise Exception("Not implemented yet")
                        print(entity_type_rmap[self.slv.getValue(self.type_of_entity(v)).toPythonObj()], entity_name_rmap[self.slv.getValue(self.id_of_entity(v)).toPythonObj()])
                        context_dict[f] = entity_type_rmap[self.slv.getValue(self.type_of_entity(v)).toPythonObj()], entity_name_rmap[self.slv.getValue(self.id_of_entity(v)).toPythonObj()]
                    else:
                        context_dict[f] = v.toPythonObj()
                    
            return ((p_type, p_id), a, (r_type, r_id), context_dict), ()
        elif r2.isUnsat():
            # pretty_print_str_with_brackets(str(self.slv.getUnsatCore()))
            return False, self.slv.getUnsatCore()

    def evaluate_req(self, synth_rule, p, a, r, ctx):
        _ = self.slv.checkSat()
        _ctx = self.parse_ctx(ctx)
        truth = self.slv.getValue(
                    self.encoded_rules[synth_rule].substitute(
                        [self.rule_p, self.rule_a, self.rule_r, self.rule_ctx],
                        [self.entity(*p), self.slv.mkString(a), self.entity(*r), _ctx])
                )
        return truth.toPythonObj()

    def parse_ctx(self, ctx):
        _ctx = []
        for f, t in self.contexts:
            s = t.getNullableElementSort()
            if f not in ctx:
                _ctx.append(self.slv.mkNullableNull(t))
                continue
            v = ctx[f]
            if v is not None:
                if s.isBoolean():
                    _ctx.append(self.slv.mkNullableSome(self.slv.mkBoolean(v)))
                elif s.isInteger():
                    _ctx.append(self.slv.mkNullableSome(self.slv.mkInteger(v)))
                elif s.isString():
                    _ctx.append(self.slv.mkNullableSome(self.slv.mkString(v)))
                else:
                    raise NotImplementedError(f"Unsupported sort {s} for context")
            else:
                _ctx.append(self.slv.mkNullableNull(t))
                # _ctx = slv.mkNullableSome()
        parsed_ctx = self.slv.mkTerm(Kind.APPLY_CONSTRUCTOR, self.context_type[0].getTerm(), *(_ctx))
        return parsed_ctx