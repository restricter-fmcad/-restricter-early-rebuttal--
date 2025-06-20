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



class SynthMode(Enum):
    MULTIPLE_RULES = 1
    ONE_RULE_WITH_CONJUNCTIONS = 2


def solve(entity_schema, actions, action_scope, hierarchy, entity_store_json, log, orig_policy, args, verbose=False, vv=False, synth_rule = None, compl=None, oracle=False, eq=False, noise=None):
    mode = None
    if args["num_allows"] is not None and args["num_denies"] is not None:
        mode = SynthMode.MULTIPLE_RULES
    elif args["num_conj"] is not None and args["num_conj"] > 0:
        mode = SynthMode.ONE_RULE_WITH_CONJUNCTIONS
    else:
        raise ValueError("Invalid mode")
    
    
    slv = cvc5.Solver()
    tm = cvc5.TermManager()
    slv.setOption("sygus", "true")
    # slv.setOption("random-freq", "1.0")
    slv.setOption("incremental", "true")
    if vv:
        slv.setOption("output", "sygus")
    slv.setOption("decision", "internal")
    # if oracle:
    #     slv.setOption("trace", "sygus-engine-debug")

    # slv.setOption("nl-ext-rewrite", "false")
    slv.setLogic("HO_ALL")

    # tm = cvc5.TermManager()
    bool_sort = slv.getBooleanSort()
    string_sort = slv.getStringSort()
    int_sort = slv.getIntegerSort()

    # Define the option datatype
    # t = slv.mkParamSort("t")
    # option_decl = slv.mkDatatypeDecl("Option")
    # option_some = slv.mkDatatypeConstructorDecl("Some")
    # option_some.addSelector("val", t)
    # option_none = slv.mkDatatypeConstructorDecl("None")
    # option_decl.addConstructor(option_some)
    # option_decl.addConstructor(option_none)
    # option_sort = slv.mkDatatypeSorts([option_decl])[0]
    # print(option_sort.getDatatypeArity())
    # print(option_sort)
    # exit()

    entity_type_map = {'': -1}
    entity_map_flat = {'': -1}
    entity_map = defaultdict(dict)
    entity_map[''] = {'': -1}
    # Define the Entity datatype
    # input_parser = None
    input_parser = cvc5.InputParser(slv)
    input_parser.setStringInput(cvc5.InputLanguage.SYGUS_2_1,
    """(declare-datatype Entity ((EntityCtor (type Int) (id Int))))""", "myInput")
    sm = input_parser.getSymbolManager()
    cmd = input_parser.nextCommand()
    # print(f"Executing command {cmd}:")
    cmd.invoke(slv, sm)
    input_parser.setStringInput(cvc5.InputLanguage.SYGUS_2_1,
    """EntityCtor""", "myInput")
    entity_ctor_fun = input_parser.nextTerm()
    entity_sort = entity_ctor_fun.getSort().getDatatypeConstructorCodomainSort()
    # exit()


    # entity_ctor = slv.mkDatatypeConstructorDecl("Entity")
    # entity_ctor.addSelector("type", int_sort)
    # entity_ctor.addSelector("id", int_sort)
    # entity_sort = slv.declareDatatype("Entity", entity_ctor)
    # entity_ctor_fun = entity_sort.getDatatype().getConstructor("Entity").getTerm()
    entity = lambda x, y: slv.mkTerm(Kind.APPLY_CONSTRUCTOR, entity_ctor_fun, slv.mkInteger(entity_type_map[x]), slv.mkInteger(entity_map_flat[y]))

    def get_type_of(type):
        type_0, *type_args = type
        if type_0 == "Entity":
            return entity_sort
        elif type_0 == "Long":
            return slv.getIntegerSort()
        elif type_0 == "String":
            return slv.getStringSort()
        elif type_0 == "Boolean":
            return slv.getBooleanSort()
        elif type_0 == "Set":
            set_of_type = get_type_of(type_args[0])
            return slv.mkSetSort(set_of_type)
        elif type_0 == "Record":
            raise NotImplementedError("Record type not implemented")
        else:
            raise NotImplementedError(f"Type {type} not implemented")

    def default_val_of(type):
        type_0, *type_args = type
        if type_0 == "Long":
            return slv.mkInteger(0)
        elif type_0 == "String":
            return slv.mkString("")
        elif type_0 == "Boolean":
            return slv.mkFalse()
        elif type_0 == "Entity":
            return entity("", "")
        elif type_0 == "Set":
            return slv.mkEmptySet(slv.mkSetSort(get_type_of(type_args[0])))
        elif type_0 == "Record":
            raise NotImplementedError("Record type not implemented")
        else:
            raise NotImplementedError(f"Type {type} not implemented")
        
    def parse_type(type, json):
        type_0, *type_args = type
        if type_0 == "Entity":
            e_type = json["__entity"]["type"]
            e_id = json["__entity"]["id"]
            return entity(e_type, e_id)
        elif type_0 == "Long":
            return slv.mkInteger(json)
        elif type_0 == "String":
            return slv.mkString(json)
        elif type_0 == "Boolean":
            return slv.mkBoolean(json)
        elif type_0 == "Set":
            items = (parse_type(type_args[0], item) for item in json)
            set_singletons = (slv.mkTerm(Kind.SET_SINGLETON, i) for i in items)
            try:
                return reduce(lambda a, b: slv.mkTerm(Kind.SET_UNION, a, b), set_singletons)
            except TypeError:
                return slv.mkEmptySet(slv.mkSetSort(get_type_of(type_args[0])))
        elif type_0 == "Record":
            raise NotImplementedError("Record type not implemented")
        else:
            raise NotImplementedError(f"Type {type} not implemented")

    def get_canonical_type_name(type):
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

    # Define has_attr function
    has_attr_entity_arg = slv.mkVar(entity_sort, "Entity")
    # has_attr_type_arg = slv.mkVar(string_sort, "Type")
    has_attr_attr_arg = slv.mkVar(string_sort, "attr")
    has_attr_type_ite = {}
    # has_attr_list = []

    # get attrs
    get_attrs = {}
    primitive_types = ["Long", "String", "Boolean"]
    types_with_defined_grammar = ["Long", "String", "Boolean"]
    to_define_grammar_types = []

    # hierarchy of types
    entity_in_entity = slv.mkVar(entity_sort, "e1")
    entity_in_in = slv.mkVar(entity_sort, "e2")
    entity_hierarchies = []

    # helper functions
    entity_id_selector = entity_sort.getDatatype().getConstructor("EntityCtor").getSelector("id").getTerm()
    id_of_entity = lambda x: slv.mkTerm(Kind.APPLY_SELECTOR, entity_id_selector, x)
    entity_type_selector = entity_sort.getDatatype().getConstructor("EntityCtor").getSelector("type").getTerm()
    type_of_entity = lambda x: slv.mkTerm(Kind.APPLY_SELECTOR, entity_type_selector, x)

    entity_eq_arg1 = slv.mkVar(entity_sort, "entity1")
    entity_eq_arg2 = slv.mkVar(entity_sort, "entity2")
    entity_eq_fun = slv.mkTerm(Kind.EQUAL, entity_eq_arg1, entity_eq_arg2)
    entity_eq = slv.defineFun("entity_eq", [entity_eq_arg1, entity_eq_arg2], bool_sort, entity_eq_fun)

    type_id_counter = 0
    list_entity_types = []
    for type in entity_schema.keys():
        entity_type_map[type] = type_id_counter
        type_id_counter += 1
        has_attr_type = type_of_entity(has_attr_entity_arg)
        type_cond = slv.mkTerm(Kind.EQUAL, has_attr_type, slv.mkInteger(entity_type_map[type]))
        ite = partial(slv.mkTerm,Kind.ITE, type_cond)
        has_attr_type_ite[type] = [ite, []]
        list_entity_types.append(type)

    if verbose:
        print("Entity type map: ", entity_type_map)

    list_entities = defaultdict(list)

    entity_id_counter = 0
    # Parse entities in entity store
    # For each entity
    for e in entity_store_json:
        entity_type = e["uid"]["__entity"]["type"]
        id = e["uid"]["__entity"]["id"]
        entity_map[entity_type][id] = entity_id_counter
        entity_map_flat[id] = entity_id_counter
        entity_id_counter += 1
        list_entities[entity_type].append(entity(entity_type, id))
        if entity_type not in entity_schema:
            raise ValueError(f"Entity type {entity_type} not found in schema")
    
    if verbose:
        print("Entity map: ", entity_map)

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
            attr_type = get_type_of(attr_type_str)
            if (attr_name, attr_type_str) not in get_attrs:
                default_val = default_val_of(attr_type_str)
                get_attrs[(attr_name, attr_type_str)] = ["__get_attr_" + attr_name + "_" + get_canonical_type_name(attr_type_str), [slv.mkVar(entity_sort, "e")], attr_type, {}, default_val]
            get_attr_arg = get_attrs[(attr_name, attr_type_str)][1][0]
            parsed_value = parse_type(attr_type_str, attr_val)

            
            get_attr_ite = partial(slv.mkTerm, Kind.ITE, slv.mkTerm(Kind.EQUAL, id_of_entity(get_attr_arg),slv.mkInteger(entity_map_flat[id])) , parsed_value)
            # add to get_attrs dict
            if entity_type not in get_attrs[(attr_name, attr_type_str)][3]:
                get_attr_type_ite = partial(slv.mkTerm, Kind.ITE, slv.mkTerm(Kind.EQUAL, type_of_entity(get_attr_arg), slv.mkInteger(entity_type_map[entity_type])))
                get_attrs[(attr_name, attr_type_str)][3][entity_type] = [get_attr_type_ite, []]
            get_attrs[(attr_name, attr_type_str)][3][entity_type][1].append(get_attr_ite)

            has_attr_cond_name = slv.mkTerm(Kind.EQUAL, has_attr_attr_arg, slv.mkString(attr_name))
            # has_attr_cond_type = slv.mkTerm(Kind.EQUAL, has_attr_type_arg, slv.mkString(get_canonical_type_name(attr_type_str)))
            has_attr_cond_entity_name = slv.mkTerm(Kind.EQUAL, id_of_entity(has_attr_entity_arg),slv.mkInteger(entity_map_flat[id]))

            # has_attr_cond = slv.mkTerm(Kind.AND, slv.mkTerm(Kind.AND, has_attr_cond_name, has_attr_cond_type), has_attr_cond_entity_name)
            has_attr_cond = slv.mkTerm(Kind.AND, has_attr_cond_name, has_attr_cond_entity_name)


            has_attr_type_ite[entity_type][1].append(partial(slv.mkTerm, Kind.ITE, has_attr_cond, slv.mkTrue()))

        # parents
        parents = e["parents"]
        for parent in parents:
            parent_type = parent["__entity"]["type"]
            parent_id = parent["__entity"]["id"]
            entity_hierarchies.append(((entity_type, id), (parent_type, parent_id)))

    # Functions in the policy grammar
    entity_is_arg_entity = slv.mkVar(entity_sort, "entity")
    entity_is_arg_type = slv.mkVar(int_sort, "type")
    entity_is_fun = slv.mkTerm(Kind.EQUAL, slv.mkTerm(Kind.APPLY_SELECTOR, entity_sort.getDatatype().getConstructor("EntityCtor").getSelector("type").getTerm(), entity_is_arg_entity), entity_is_arg_type)
    entity_is = slv.defineFun("entity_is", [entity_is_arg_entity, entity_is_arg_type], bool_sort, entity_is_fun)

    # allow_header: (p and a and r) and body
    allow_header_principal = slv.mkVar(bool_sort, "p")
    allow_header_action = slv.mkVar(bool_sort, "a")
    allow_header_resource = slv.mkVar(bool_sort, "r")
    allow_header_predbody = slv.mkVar(bool_sort, "predbody")
    allow_header_body = slv.mkTerm(Kind.AND, slv.mkTerm(Kind.AND, slv.mkTerm(Kind.AND, allow_header_principal, allow_header_action), allow_header_resource), allow_header_predbody)
    allow_header = slv.defineFun("allow_header", [allow_header_principal, allow_header_action, allow_header_resource, allow_header_predbody], bool_sort, allow_header_body)

    # deny_header: (p and a and r) => not body
    deny_header_principal = slv.mkVar(bool_sort, "p")
    deny_header_action = slv.mkVar(bool_sort, "a")
    deny_header_resource = slv.mkVar(bool_sort, "r")
    deny_header_predbody = slv.mkVar(bool_sort, "predbody")
    deny_header_body = slv.mkTerm(Kind.IMPLIES, slv.mkTerm(Kind.AND, slv.mkTerm(Kind.AND, deny_header_principal, deny_header_action), deny_header_resource), slv.mkTerm(Kind.NOT, deny_header_predbody))
    deny_header = slv.defineFun("deny_header", [deny_header_principal, deny_header_action, deny_header_resource, deny_header_predbody], bool_sort, deny_header_body)

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
    # has_attr = slv.defineFun("has_attr", [has_attr_entity_arg, has_attr_type_arg, has_attr_attr_arg], bool_sort, has_attr_body)
    has_attr = slv.defineFun("has_attr", [has_attr_entity_arg, has_attr_attr_arg], bool_sort, has_attr_body)

    # Define get_attrs functions
    get_attrs_func = {}
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
        # *_, return_type = _args
        # if oracle:
        #     with open(ORACLE_FUNCTIONS_FILE, "a") as f:
        #         f.write(f"\"(declare-fun |{_args[0]}| (Entity) {_args[2]})\\n\"\n")
        get_attrs_func[name] = (get_attr, type)
        if type[0] != "Entity" and type not in types_with_defined_grammar:
            # we need to add a grammar rule for this type
            types_with_defined_grammar.append(type)
            to_define_grammar_types.append(type)

    # Define contexts
        contexts = []
        for action, keys in action_scope.items():
            if 'context' in keys['appliesTo']:
                ctx_shape = keys['appliesTo']['context']['attributes']
                for attr, attr_type in ctx_shape.items():
                    t = get_type_of((attr_type['type'],))
                    option_t = tm.mkNullableSort(t)
                    contexts.append((attr, option_t))

        # Sanity check.
        # If context has attributes of same name but different types, then error
        for (a1, t1), (a2, t2) in itertools.combinations(contexts, 2):
            if a1 == a2 and t1 != t2:
                raise ValueError(f"Context attribute {a1} has different types {t1} and {t2}, not supported")
        
        context_sort = tm.mkRecordSort(*contexts)
        context_type = context_sort.getDatatype()

        context_has_ctx = slv.mkVar(context_sort, "ctx")
        context_has_attr_name = slv.mkVar(string_sort, "name")
        context_has_body_lst = []
        for f, t in contexts:
            if_name_f = slv.mkTerm(Kind.EQUAL, context_has_attr_name, slv.mkString(f))
            ctx_f = slv.mkTerm(Kind.APPLY_SELECTOR, context_type.getSelector(f).getTerm(), context_has_ctx)
            not_null_test = slv.mkNullableIsSome(ctx_f)
            # if_non_null = slv.mkTerm(Kind.APPLY_UF, not_null_test, ctx_f)
            test = slv.mkTerm(Kind.AND, if_name_f, not_null_test)
            context_has_body_lst.append(test)
        context_has_body = slv.mkTerm(Kind.OR, slv.mkFalse(), *context_has_body_lst) if context_has_body_lst else slv.mkFalse()
        context_has = slv.defineFun("ctx_has_attr", [context_has_ctx, context_has_attr_name], bool_sort, context_has_body)

    # Define entity hierarchy predicate

    # obtain the transitive closure of the entity hierarchy
    entity_hierarchy_closure = transitive_closure(entity_hierarchies)
    heirarchy_cond = [
        slv.mkTerm(
            Kind.AND,
            slv.mkTerm(Kind.EQUAL, entity(type, id), entity_in_entity),
            slv.mkTerm(Kind.EQUAL, entity(parent_type, parent_id), entity_in_in)) for (type, id), (parent_type, parent_id) in entity_hierarchy_closure]
    heirarchy_ites = [partial(slv.mkTerm, Kind.ITE, cond, slv.mkTrue()) for cond in heirarchy_cond]
    entity_in_body = reduce(lambda a, b: lambda e: a(b(e)), heirarchy_ites)(slv.mkFalse()) if heirarchy_ites else slv.mkFalse()
    entity_in = slv.defineFun("entity_in", [entity_in_entity, entity_in_in], bool_sort, entity_in_body)
    # if verbose:
    #     print("-"*20)
    #     pretty_print_str_with_brackets(str(entity_in_body))



    # declare input variables for the functions-to-synthesize
    principal = slv.declareSygusVar("principal", entity_sort)
    action = slv.declareSygusVar("action", string_sort)
    resource = slv.declareSygusVar("resource", entity_sort)
    ctx = slv.declareSygusVar("context", context_sort)

    # Also consider attribute depths, e.g. principal.attr1.attr2.attr3
    attribute_depths = [ground_depth(entity_schema, i) for i in range(1, 3+1)]
    # Get entities that can be obtained from attributes
    list_entities_from_attr = defaultdict(list)
    from_attr = defaultdict(list)
    attr_getter = defaultdict(list)
    # for e in [principal, resource]:
    #     for depth_i_attr in attribute_depths:
    #         for attr_chain in depth_i_attr:
    #             chain_iter = iter(attr_chain)
    #             (type, attr, attr_type) = next(chain_iter)
    #             term = slv.mkTerm(Kind.APPLY_UF, get_attrs_func[attr][0], e)
    #             for (type, attr, attr_type) in chain_iter:
    #                 term = slv.mkTerm(Kind.APPLY_UF, get_attrs_func[attr][0], term)
    #                 # for adding to grammar (type not entity)
    #             from_attr[get_canonical_type_name(attr_type)].append(term)
    #             if attr_type[0] == "Entity":
    #                 # for adding to grammar
    #                 list_entities_from_attr[attr_type[1]].append(term)
    entity_var = slv.mkVar(entity_sort, "e")
    for depth_i_attr in attribute_depths:
        for attr_chain in depth_i_attr:
            chain_iter = iter(attr_chain)
            (type0, attr0, attr_type) = next(chain_iter)
            # name = [type0, attr0]
            term = slv.mkTerm(Kind.APPLY_UF, get_attrs_func[attr0][0], entity_var)
            for (type, attr, attr_type) in chain_iter:
                term = slv.mkTerm(Kind.APPLY_UF, get_attrs_func[attr][0], term)
                # name.append(attr)
            # print('.'.join(name))
            # e of type type0 has a getter term.sub(entity_var, e) that outputs attr_type
            attr_getter[type0].append([term, attr_type])
            # for adding to grammar (type not entity)
            from_attr[get_canonical_type_name(attr_type)].append(term)
            if attr_type[0] == "Entity":
                # for adding to grammar
                list_entities_from_attr[attr_type[1]].append(term)
    # print(attr_getter)
    # exit()
    """declare the grammar non-terminals"""

    # Constant non-terminals
    policy_shape = slv.mkVar(bool_sort, "Policy")
    allows = slv.mkVar(bool_sort, "Allows")
    denies = slv.mkVar(bool_sort, "Denies")
    allow = slv.mkVar(bool_sort, "Allow")
    deny = slv.mkVar(bool_sort, "Deny")
    # headers
    principal_head = slv.mkVar(bool_sort, "PrincipalHead")
    action_head = slv.mkVar(bool_sort, "ActionHead")
    resource_head = slv.mkVar(bool_sort, "ResourceHead")

    # To be generated:
    # body of policy
    phi = slv.mkVar(bool_sort, "Phi")
    disj = slv.mkVar(bool_sort, "DISJ")
    conj = slv.mkVar(bool_sort, "CONJ")
    # rand = slv.mkVar(bool_sort, "RAND")
    # ror = slv.mkVar(bool_sort, "ROR")
    # randa = slv.mkVar(bool_sort, "RANDA")
    # rora = slv.mkVar(bool_sort, "RORA")
    entity_eqs = slv.mkVar(bool_sort, "EntityEq")
    entity_ins = slv.mkVar(bool_sort, "EntityIn")
    attr_expressions = slv.mkVar(bool_sort, "AttrExpr")
    restricted_atoms = slv.mkVar(bool_sort, "RestrictedAtoms")
    # types and entities
    types = slv.mkVar(int_sort, "Types")
    entity_grammar = slv.mkVar(entity_sort, "Entities")
    entity_from_attr_grammar = slv.mkVar(entity_sort, "EntitiesFromAttr")
    const_entity_grammar = slv.mkVar(entity_sort, "ConstEntities")
    action_grammar = slv.mkVar(string_sort, "Actions")

    grammar_for_const_entities = {rt: slv.mkVar(entity_sort, "__Const_Entities_" + rt) for rt in list_entities.keys()}
    grammar_for_entity_from_attr = {rt: slv.mkVar(entity_sort, "__Entities_Attr_" + rt) for rt in list_entities_from_attr.keys()}
    # print(grammar_for_entity_from_attr)
    grammar_for_entities = {rt: slv.mkVar(entity_sort, "__Entities_" + rt) for rt in list_entities.keys()}
    grammar_for_other_types = {}
    for rt in to_define_grammar_types:
        if rt[0] in primitive_types:
            # print("__Value_" + str(rt[0]))
            grammar_for_other_types[rt] = slv.mkVar(get_type_of(rt), "__Value_" + str(rt[0]))
        else:
            grammar_for_other_types[rt] = slv.mkVar(get_type_of(rt), "__Type_" + str(rt))


    grammar = slv.mkGrammar([principal, action, resource, ctx], 
        # Constant grammar non-terminals and entity_grammar (which will be generated)
        [policy_shape] + 
        ([allows, denies, deny] if mode == SynthMode.MULTIPLE_RULES else []) +
        [allow, principal_head, action_head, resource_head, phi] +
        ([conj, disj] if mode == SynthMode.ONE_RULE_WITH_CONJUNCTIONS else []) +
        [entity_ins, attr_expressions, # entity_eqs, rand, randa, ror, rora, 
        types, entity_grammar, const_entity_grammar, action_grammar, entity_from_attr_grammar]
        # grammar containing constants for each entity type
        + list(grammar_for_entities.values())
        + list(grammar_for_other_types.values())
        + list(grammar_for_const_entities.values())
        + list(grammar_for_entity_from_attr.values())
    )
    # Constant grammar non-terminals
    if mode == SynthMode.MULTIPLE_RULES:
        # Optimization: Only have allows
        if args["num_denies"] == 0:
            grammar.addRules(policy_shape, [allows])
        else:
            grammar.addRules(policy_shape, [slv.mkTerm(Kind.AND, allows, denies)])

        restricted_allows = None
        restricted_deny = None

        if args["num_allows"] == 1:
            restricted_allows = allow
        elif args["num_allows"] <= 0:
            restricted_allows = slv.mkFalse()
        else:
            restricted_allows = slv.mkTerm(Kind.OR, allow, allow)
            for _ in range(args["num_allows"]-2):
                restricted_allows = slv.mkTerm(Kind.OR, restricted_allows, allow)

        if args["num_denies"] == 1:
            restricted_deny = deny
        elif args["num_denies"] <= 0:
            restricted_deny = slv.mkTrue()
        else:
            restricted_deny = slv.mkTerm(Kind.AND, deny, deny)
            for _ in range(args["num_denies"]-2):
                restricted_deny = slv.mkTerm(Kind.OR, restricted_deny, deny)
        grammar.addRules(allows, [slv.mkFalse()] + ([restricted_allows] if restricted_allows is not None else []))
        grammar.addRules(denies, [slv.mkTrue()] + ([restricted_deny] if restricted_deny is not None else []))
        grammar.addRules(allow, [slv.mkTerm(Kind.APPLY_UF,allow_header, principal_head, action_head, resource_head, phi)])
        grammar.addRules(deny, [slv.mkTerm(Kind.APPLY_UF,deny_header, principal_head, action_head, resource_head, phi)])

        grammar.addRules(phi, [
            slv.mkFalse(),
            slv.mkTrue(),
            slv.mkTerm(Kind.AND, phi, phi),
            slv.mkTerm(Kind.OR, phi, phi),
            slv.mkTerm(Kind.NOT, phi),
            attr_expressions,
            # entity_eqs,
            entity_ins,
            slv.mkTerm(Kind.APPLY_UF, entity_is, principal, types),
            slv.mkTerm(Kind.APPLY_UF, entity_is, resource, types),
        ])
    else:
        grammar.addRules(policy_shape, [allow])
        # Exactly args.num_conj number of conjunctions
        if args["num_conj"] == 0:
            grammar.addRules(conj, [slv.mkTrue()])
        elif args["num_conj"] == 1:
            grammar.addRules(conj, [disj])
        else:
            ands = slv.mkTerm(Kind.AND, disj, disj)
            for _ in range(args["num_conj"]-2):
                ands = slv.mkTerm(Kind.AND, ands, disj)
            grammar.addRules(conj, [ands])
        grammar.addRules(disj, [phi,
        ])

        grammar.addRules(phi, [
            attr_expressions,
            # entity_eqs,
            entity_ins,
            slv.mkTerm(Kind.APPLY_UF, entity_is, principal, types),
            slv.mkTerm(Kind.APPLY_UF, entity_is, resource, types),
            action_head
        ])



    attr_expressions_grammar = [] #[slv.mkTrue()]
    entity_ins_grammar = []

    # a.attr op b.attr
    for input_type_1, input_type_2 in itertools.product(attr_getter.keys(), repeat=2):
        for (get1, rt1), (get2, rt2) in itertools.product(attr_getter[input_type_1], attr_getter[input_type_2]):
            # the type of entity is the same
            if rt1 == rt2:
                for e1, e2 in itertools.combinations([principal, resource], r=2):
                    # if e1 == e2 and (input_type_1 != input_type_2 or get1 == get2):
                    #     continue
                    attr_is_term1 = slv.mkTerm(Kind.APPLY_UF, entity_is, e1, slv.mkInteger(entity_type_map[input_type_1]))
                    attr_is_term2 = slv.mkTerm(Kind.APPLY_UF, entity_is, e2, slv.mkInteger(entity_type_map[input_type_2]))
                    get_attr_term1 = get1.substitute(entity_var, e1)
                    get_attr_term2 = get2.substitute(entity_var, e2)
                    eq_term = slv.mkTerm(Kind.APPLY_UF, entity_eq, get_attr_term1, get_attr_term2) if rt1[0] == "Entity" else slv.mkTerm(Kind.EQUAL, get_attr_term1, get_attr_term2)
                    term = slv.mkTerm(Kind.IMPLIES,slv.mkTerm(Kind.AND, attr_is_term1, attr_is_term2), eq_term)
                    attr_expressions_grammar.append(term)
                    term = slv.mkTerm(Kind.IMPLIES,slv.mkTerm(Kind.AND, attr_is_term1, attr_is_term2), slv.mkTerm(Kind.NOT, eq_term))
                    attr_expressions_grammar.append(term)
            if rt1[0] == "Entity" and rt2[0] == "Entity" and\
                rt1[1] in hierarchy and rt2[1] in hierarchy[rt1[1]]: # rt1 can be a member of rt2
                for e1, e2 in itertools.product([principal, resource], repeat=2):
                    if e1 == e2 and input_type_1 != input_type_2:
                        continue
                    attr_is_term1 = slv.mkTerm(Kind.APPLY_UF, entity_is, e1, slv.mkInteger(entity_type_map[input_type_1]))
                    attr_is_term2 = slv.mkTerm(Kind.APPLY_UF, entity_is, e2, slv.mkInteger(entity_type_map[input_type_2]))
                    get_attr_term1 = get1.substitute(entity_var, e1)
                    get_attr_term2 = get2.substitute(entity_var, e2)
                    eq_term = slv.mkTerm(Kind.APPLY_UF, entity_in, get_attr_term1, get_attr_term2)
                    term = slv.mkTerm(Kind.IMPLIES,slv.mkTerm(Kind.AND, attr_is_term1, attr_is_term2), eq_term)
                    # print(term)
                    entity_ins_grammar.append(term)
            if rt2[0] == "Set" and (rt2[1] == rt1):
                # raise NotImplementedError()
                for e1, e2 in itertools.product([principal, resource], repeat=2):
                    attr_is_term1 = slv.mkTerm(Kind.APPLY_UF, entity_is, e1, slv.mkInteger(entity_type_map[input_type_1]))
                    attr_is_term2 = slv.mkTerm(Kind.APPLY_UF, entity_is, e2, slv.mkInteger(entity_type_map[input_type_2]))
                    get_attr_term1 = get1.substitute(entity_var, e1)
                    get_attr_term2 = get2.substitute(entity_var, e2)
                    eq_term = slv.mkTerm(Kind.SET_MEMBER, get_attr_term1, get_attr_term2)
                    term = slv.mkTerm(Kind.IMPLIES,slv.mkTerm(Kind.AND, attr_is_term1, attr_is_term2), eq_term)
                    attr_expressions_grammar.append(term)

    # e.f1 == ctx.f2
    for f, _t in contexts:
        t = _t.getNullableElementSort()

        # ctx has f1 and e is t => ctx.f1 == e.f2
        for entity_t in attr_getter.keys():
            for get, rt in attr_getter[entity_t]:
                if t != get_type_of(rt):
                        continue
                for e in [principal, resource]:
                    # context has f
                    ctx_has_term = slv.mkTerm(Kind.APPLY_UF, context_has, ctx, slv.mkString(f))
                    # entity is type
                    entity_is_term = slv.mkTerm(Kind.APPLY_UF, entity_is, e, slv.mkInteger(entity_type_map[entity_t]))
                    # maybe_ctx_attr has type Nullable t
                    maybe_ctx_attr = slv.mkTerm(Kind.APPLY_SELECTOR, context_type.getSelector(f).getTerm(), ctx)
                    # since we ensure ctx has term, we can get the value directly
                    really_ctx_attr = tm.mkNullableVal(maybe_ctx_attr)
                    entity_attr = get.substitute(entity_var, e)
                    eq_term = slv.mkTerm(Kind.EQUAL, really_ctx_attr, entity_attr)
                    term = slv.mkTerm(Kind.IMPLIES, entity_is_term, slv.mkTerm(Kind.AND, ctx_has_term, eq_term))
                    attr_expressions_grammar.append(term)
        # ctx has f => ctx.f = true or false
        if t == bool_sort:
            ctx_has_term = slv.mkTerm(Kind.APPLY_UF, context_has, ctx, slv.mkString(f))
            maybe_ctx_attr = slv.mkTerm(Kind.APPLY_SELECTOR, context_type.getSelector(f).getTerm(), ctx)
            # since we ensure ctx has term, we can get the value directly
            really_ctx_attr = tm.mkNullableVal(maybe_ctx_attr)
            eq_term = slv.mkTerm(Kind.EQUAL, really_ctx_attr, slv.mkTrue())
            term = slv.mkTerm(Kind.AND, ctx_has_term, eq_term)
            attr_expressions_grammar.append(term)
            eq_term = slv.mkTerm(Kind.EQUAL, really_ctx_attr, slv.mkFalse())
            term = slv.mkTerm(Kind.AND, ctx_has_term, eq_term)
            attr_expressions_grammar.append(term)
        
    # print(attr_getter)

    for input_type_1 in attr_getter.keys():
        for get, rt in attr_getter[input_type_1]:
            if rt[0] == "Entity":
                for e1, e2 in itertools.product([principal, resource], repeat=2):
                    if e1 == e2 and input_type_1 != rt[1]:
                        continue
                    attr_is_term1 = slv.mkTerm(Kind.APPLY_UF, entity_is, e1, slv.mkInteger(entity_type_map[input_type_1]))
                    attr_is_term2 = slv.mkTerm(Kind.APPLY_UF, entity_is, e2, slv.mkInteger(entity_type_map[rt[1]]))
                    get_attr_term = get.substitute(entity_var, e1)
                    eq_term = slv.mkTerm(Kind.APPLY_UF, entity_eq, get_attr_term, e2)
                    term = slv.mkTerm(Kind.IMPLIES,slv.mkTerm(Kind.AND, attr_is_term1, attr_is_term2), eq_term)
                    # print(term)
                    attr_expressions_grammar.append(term)

                    # e1 is type => e1.f in e2
                    if rt[1] in hierarchy:
                        for in_t in hierarchy[rt[1]]:
                            # print(rt[1], in_t)
                            attr_is_term2 = slv.mkTerm(Kind.APPLY_UF, entity_is, e2, slv.mkInteger(entity_type_map[in_t]))
                            in_1 = slv.mkTerm(Kind.APPLY_UF, entity_in, get_attr_term, e2)
                            term = slv.mkTerm(Kind.IMPLIES, slv.mkTerm(Kind.AND, attr_is_term1, attr_is_term2), in_1)
                            # print(term)
                            entity_ins_grammar.append(term)
                    # e1 is type => e2 in e1.f
                    for in_t in hierarchy.keys():
                        if rt[1] in hierarchy[in_t]:
                            # print(in_t, rt[1])
                            attr_is_term2 = slv.mkTerm(Kind.APPLY_UF, entity_is, e2, slv.mkInteger(entity_type_map[in_t]))
                            in_2 = slv.mkTerm(Kind.APPLY_UF, entity_in, e2, get_attr_term)
                            term = slv.mkTerm(Kind.IMPLIES, slv.mkTerm(Kind.AND, attr_is_term1, attr_is_term2), in_2)
                            # print(term)
                            entity_ins_grammar.append(term)
                    
                        
            
                for e in [principal, resource]:
                    # e is type => e = const_e
                    attr_is = slv.mkTerm(Kind.APPLY_UF, entity_is, e, slv.mkInteger(entity_type_map[input_type_1]))
                    get_attr_term = get.substitute(entity_var, e)
                    for e2 in list_entities[rt[1]]:
                        term = slv.mkTerm(Kind.IMPLIES, attr_is, slv.mkTerm(Kind.APPLY_UF, entity_eq, get_attr_term, e2))
                        attr_expressions_grammar.append(term)
                        # term = slv.mkTerm(Kind.IMPLIES, attr_is, slv.mkTerm(Kind.NOT, slv.mkTerm(Kind.APPLY_UF, entity_eq, get_attr_term, e2)))
                        # attr_expressions_grammar.append(term)
            elif rt[0] == "Set":
                assert rt[1][0] == "Entity"
                for e1, e2 in itertools.product([principal, resource], repeat=2):
                    attr_is_term1 = slv.mkTerm(Kind.APPLY_UF, entity_is, e1, slv.mkInteger(entity_type_map[input_type_1]))
                    attr_is_term2 = slv.mkTerm(Kind.APPLY_UF, entity_is, e2, slv.mkInteger(entity_type_map[rt[1][1]]))
                    get_attr_term = get.substitute(entity_var, e1)
                    in_term = slv.mkTerm(Kind.SET_MEMBER, e2, get_attr_term)
                    term = slv.mkTerm(Kind.IMPLIES,slv.mkTerm(Kind.AND, attr_is_term1, attr_is_term2), in_term)
                    # print(term)
                    attr_expressions_grammar.append(term)
            # e.f = true or false
            elif rt[0] == "Boolean":
                for e in [principal, resource]:
                    attr_is_term = slv.mkTerm(Kind.APPLY_UF, entity_is, e, slv.mkInteger(entity_type_map[input_type_1]))
                    get_attr_term = get.substitute(entity_var, e)
                    # boolean equality
                    eq_term = slv.mkTerm(Kind.EQUAL, get_attr_term, slv.mkTrue())
                    term = slv.mkTerm(Kind.IMPLIES, attr_is_term, eq_term)
                    attr_expressions_grammar.append(term)
                    eq_term = slv.mkTerm(Kind.EQUAL, get_attr_term, slv.mkFalse())
                    term = slv.mkTerm(Kind.IMPLIES, attr_is_term, eq_term)
                    attr_expressions_grammar.append(term)
    # exit()
    # print(len(attr_expressions_grammar))
    # exit()
    grammar.addRules(attr_expressions, attr_expressions_grammar)
    # XXX: ugly hack to make sure that the grammar is not empty
    grammar.addRules(entity_ins, entity_ins_grammar if entity_ins_grammar else [slv.mkTrue()])
    print("Size of conjuncts: ", len(attr_expressions_grammar)+len(entity_ins_grammar) + len(actions))
    # exit()

    grammar.addRules(types, [slv.mkInteger(t) for t in range(type_id_counter)])

    # parse attributes of principals, and add to grammar
    


    # entity_grammar
    for rt, entities in list_entities.items():
        grammar.addRules(grammar_for_const_entities[rt], entities)

    for rt in list_entities:
        grammar.addRules(grammar_for_entities[rt], [grammar_for_const_entities[rt]] + list_entities_from_attr[rt]
        )

    list_of_const_entites = list(reduce(lambda x, y: x + y, (e for e in list_entities.values()), []))
    list_of_var_entities = list(reduce(lambda x, y: x + y, (e for e in list_entities_from_attr.values()), []))

    for rt in grammar_for_entity_from_attr:
        grammar.addRules(grammar_for_entity_from_attr[rt], list_entities_from_attr[rt])

    grammar.addRules(const_entity_grammar, list_of_const_entites)
    grammar.addRules(entity_from_attr_grammar, list_of_var_entities)
    # grammar for all entities
    grammar.addRules(entity_grammar, [const_entity_grammar, entity_from_attr_grammar, principal, resource])
    # actions
    grammar.addRules(action_grammar, [slv.mkString(s) for s in actions])
    

    for rt in to_define_grammar_types:
        if rt[0] == "Boolean":
            grammar.addRules(grammar_for_other_types[rt], [slv.mkTrue(), slv.mkFalse()])# + from_attr["Boolean"])
        else:
            # TODO: implement this by collecting every possible values in the attributes?
            grammar.addRules(grammar_for_other_types[rt], [default_val_of(rt)] + from_attr[get_canonical_type_name(rt)])


    # Encode original policy as smt
    policy_json = json.loads(to_json(orig_policy))

    ## Negative Examples
    negative_example_p = slv.mkVar(entity_sort, "p")
    negative_example_a = slv.mkVar(string_sort, "a")
    negative_example_r = slv.mkVar(entity_sort, "r")
    rule_ctx = slv.mkVar(context_sort, "context")

    ######## Symbolic compiler of the initial policy ########
    def parse_primary(primary_json):
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
                    return entity(path, eid)
                else:
                    # Action::eid
                    return slv.mkString(eid)
            case 'name':
                match primary_json['val']:
                    case 'Principal':
                        return negative_example_p
                    case 'Action':
                        return negative_example_a
                    case 'Resource':
                        return negative_example_r
                    case 'Context':
                        return rule_ctx
                if primary_json['val'] in entity_type_map:
                    return slv.mkInteger(entity_type_map[primary_json['val']])
                if primary_json['val'] in actions:
                    return slv.mkString(primary_json['val'])
                return slv.mkString(primary_json['val'])
            case 'expr':
                return parse_expr(primary_json['val'])
            case 'eList':
                print("primary", primary_json)
                pass
        raise NotImplemented

    def parse_member(member_json):
        assert(member_json['type'] == 'member')
        item = parse_primary(member_json['item'])
        if 'access' not in member_json:
            return item
        new_item = item
        if item.getSort() == entity_sort:
            for access in member_json['access']:
                new_item = slv.mkTerm(Kind.APPLY_UF, get_attrs_func[access][0], new_item)
        elif item.getSort() == context_sort:
            access = member_json['access'][0]
            # print(self.tm.mkNullableVal(self.context_type.getSelector(access).getTerm()))
            new_item = tm.mkNullableVal(slv.mkTerm(Kind.APPLY_SELECTOR, context_type.getSelector(access).getTerm(), new_item))
            for access in member_json['access'][1:]:
                if new_item.getSort() != entity_sort:
                    raise Exception("Attribute access is not an entity")
                new_item = slv.mkTerm(Kind.APPLY_SELECTOR, get_attrs_func[access][0], new_item)
        return new_item

    def parse_unary(unary_json):
        assert(unary_json['type'] == 'unary')
        item = parse_member(unary_json['item'])
        match unary_json['op']:
            case 'None':
                return item
            case 'Bang':
                for _ in range(int(unary_json['count'])):
                    item = slv.mkTerm(Kind.NOT, item)
                return item
            case 'Dash':
                pass
        return NotImplemented()

    def parse_mult(mult_json):
        assert(mult_json['type'] == 'mult')
        if 'extended' not in mult_json:
            return parse_unary(mult_json['initial'])
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

    def parse_add(add_json):
        assert(add_json['type'] == 'add')
        if 'extended' not in add_json:
            return parse_mult(add_json['initial'])
        assert(len(add_json['extended']) == 1)
        ext = add_json['extended'][0]
        rval = parse_mult(ext['initial'])
        match ext['op']:
            case 'Plus':
                pass
            case 'Minus':
                pass
        raise NotImplementedError

    def parse_relation(rel_json):
        match rel_json["ctype"]:
            case "common":
                initial = parse_add(rel_json['initial'])
                if 'extended' not in rel_json:
                    return initial
                assert(len(rel_json['extended']) == 1)
                ext = rel_json['extended'][0]
                rval = parse_add(ext['rel_to'])
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
                        if rval.getSort() == entity_sort:
                            return slv.mkTerm(Kind.APPLY_UF, entity_eq, initial, rval)
                        else:
                            return slv.mkTerm(Kind.EQUAL, initial, rval)
                    case "In":
                        if rval.getSort() == entity_sort:
                            return slv.mkTerm(Kind.APPLY_UF, entity_in, initial, rval)
                        else:
                            # set
                            assert(rval.getSort().isSet())
                            return slv.mkTerm(Kind.SET_MEMBER, initial, rval)
            case "has":
                field = parse_add(rel_json['field'])
                target = parse_add(rel_json['target'])
                if target.getSort() == entity_sort:
                    assert(field.getSort() == string_sort)
                    assert(target.getSort() == entity_sort)
                    return slv.mkTerm(Kind.APPLY_UF, has_attr, target, field)
                elif target.getSort() == context_sort:
                    return slv.mkTerm(Kind.APPLY_UF, context_has, target, field)
                raise Exception
            case "is_in":
                target = parse_add(rel_json['target'])
                entity_type =  parse_add(rel_json['entity_type'])
                if "in_entity" in rel_json:
                    raise NotImplementedError
                return slv.mkTerm(Kind.APPLY_UF, entity_is, target, entity_type)
        print(rel_json["ctype"])
        raise NotImplementedError

    def parse_and(and_json):
        assert(and_json['type'] == 'and')
        initial = parse_relation(and_json['initial'])
        if 'extended' not in and_json:
            return initial
        rv = initial
        for ands in and_json['extended']:
            val = parse_relation(ands)
            rv = slv.mkTerm(Kind.AND, rv, val)
        return rv

    def parse_expr(expr_json):
        assert(expr_json['type'] == 'expr')
        expr = expr_json['expr']
        match expr_json['stype']:
            case 'singleton_expr': # A singular And expression
                return parse_and(expr)
            case 'or': # A disjunction of expressions
                rv = parse_and(expr['initial'])
                for ext in expr['extended']:
                    val = parse_and(ext)
                    rv = slv.mkTerm(Kind.OR, rv, val)
                return rv
            case 'ite':
                raise NotImplemented("Not implemented ite for policy encoding")
        raise ValueError()

    allow_rules_list = []
    deny_rules_list = []
    encoded_rules = []
    encoded_rules_metadata = []
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
                    target = negative_example_p
                case "Action":
                    target = negative_example_a
                case "Resource":
                    target = negative_example_r
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
                                    restriction = slv.mkTerm(Kind.APPLY_UF,entity_eq, target, entity(expr['val']['path'], expr['val']['eid']))
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
                                    restriction = slv.mkTerm(Kind.APPLY_UF,entity_in, target, entity(expr['val']['path'], expr['val']['eid']))
                                    metadata[ident] = ("In", (expr['val']['path'], expr['val']['eid']))
                            case 'list':
                                if ident != "Action":
                                    print("This is impossible")
                                    raise Exception("cannot have \"principal/resource in [entities...]\"")
                                _actions = [entry['expr']['initial']['initial']['initial']['initial']['item']['item']['val']['eid'] for entry in expr['val']]
                                action_restriction = slv.mkTerm(Kind.EQUAL, target, slv.mkString(_actions[0]))
                                for a in _actions[1:]:
                                    action_restriction = slv.mkTerm(Kind.OR, slv.mkTerm(Kind.EQUAL, target, slv.mkString(a)), action_restriction)
                                restriction = action_restriction
                                metadata["Action"] = ("List", _actions)
            elif "is" in var:
                t = var["is"]
                restriction = slv.mkTerm(Kind.APPLY_UF,entity_is, target, slv.mkInteger(entity_type_map[t]))
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
        cond = parse_expr(policy["conditions"][0]) if len(policy["conditions"]) == 1 else slv.mkTrue()
        metadata["cond"] = cond
        if effect == "Permit":
            rule = slv.mkTerm(Kind.APPLY_UF, allow_header, p_restriction, a_restriction, r_restriction, cond)
            allow_rules_list.append(rule)
        else:
            rule = slv.mkTerm(Kind.APPLY_UF, deny_header, p_restriction, a_restriction, r_restriction, cond)
            deny_rules_list.append(rule)
        encoded_rules_metadata.append(metadata)
        encoded_rules.append(rule)
    
    if synth_rule is None:
        grammar.addRules(principal_head, [
            slv.mkTrue(),
            slv.mkTerm(Kind.APPLY_UF,entity_eq, principal, const_entity_grammar),
            slv.mkTerm(Kind.APPLY_UF,entity_is, principal, types),
            slv.mkTerm(Kind.APPLY_UF,entity_in, principal, const_entity_grammar)
        ])
        grammar.addRules(action_head, [
            slv.mkTrue(),
            slv.mkTerm(Kind.EQUAL, action, action_grammar)
        ])
        grammar.addRules(resource_head, [
            slv.mkTrue(),
            slv.mkTerm(Kind.APPLY_UF,entity_eq, resource, const_entity_grammar),
            slv.mkTerm(Kind.APPLY_UF,entity_is, resource, types),
            slv.mkTerm(Kind.APPLY_UF,entity_in, principal, const_entity_grammar)
        ])
        # grammar.addRules(allow,
        #     [slv.mkTerm(Kind.APPLY_UF, allow_header, principal_head, action_head, resource_head, conj)]
        # )
    else:
        # We only focus on one rule.
        metadata = encoded_rules_metadata[synth_rule]
        # print("metadata:", metadata)
        match metadata["Principal"]:
            case ("Eq", (type, id)):
                print((type, id))
                grammar.addRules(principal_head, [
                    slv.mkTerm(Kind.APPLY_UF,entity_eq, principal, entity(type, id)),
                ])
            case ("In", (type, id)):
                grammar.addRules(principal_head, [
                    slv.mkTerm(Kind.APPLY_UF,entity_in, principal, entity(type, id)),
                    # slv.mkTerm(Kind.APPLY_UF,entity_eq, principal, const_entity_grammar),
                    # slv.mkTerm(Kind.APPLY_UF,entity_is, principal, types),
                    # slv.mkTerm(Kind.APPLY_UF,entity_in, principal, const_entity_grammar),
                    # slv.mkTrue(),
                ])
            case ("Is", t):
                grammar.addRules(principal_head, [
                    # slv.mkTerm(Kind.APPLY_UF,entity_eq, principal, grammar_for_const_entities[t]),
                    slv.mkTerm(Kind.APPLY_UF,entity_is, principal, slv.mkInteger(entity_type_map[t]))
                ])
            case ("True", _):
                grammar.addRules(principal_head, [
                    # slv.mkTerm(Kind.APPLY_UF,entity_eq, principal, const_entity_grammar),
                    # slv.mkTerm(Kind.APPLY_UF,entity_is, principal, types),
                    # slv.mkTerm(Kind.APPLY_UF,entity_in, principal, const_entity_grammar),
                    slv.mkTrue(),
                ])
        match metadata["Action"]:
            case ("Eq", a):
                grammar.addRules(action_head, [
                    slv.mkTerm(Kind.EQUAL, action, slv.mkString(a))
                ])
            case ("List", _actions):
                action_restriction = slv.mkTerm(Kind.EQUAL, action, slv.mkString(_actions[0]))
                for a in _actions[1:]:
                    action_restriction = slv.mkTerm(Kind.OR, slv.mkTerm(Kind.EQUAL, action, slv.mkString(a)), action_restriction)
                grammar.addRules(action_head, [
                    action_restriction
                ])
            case ("True", _):
                grammar.addRules(action_head, [
                    slv.mkTerm(Kind.EQUAL, action, action_grammar),
                    slv.mkTrue(),
                ])
        match metadata["Resource"]:
            case ("Eq", (type, id)):
                grammar.addRules(resource_head, [
                    slv.mkTerm(Kind.APPLY_UF,entity_eq, resource, entity(type, id)),
                ])
            case ("In", (type, id)):
                grammar.addRules(resource_head, [
                    slv.mkTerm(Kind.APPLY_UF,entity_in, principal, entity(type, id)),
                ])
            case ("Is", t):
                grammar.addRules(resource_head, [
                    slv.mkTerm(Kind.APPLY_UF,entity_is, resource, slv.mkInteger(entity_type_map[t]))
                ])
            case ("True", _):
                grammar.addRules(resource_head, [
                    slv.mkTrue(),
                ])
        grammar.addRules(allow,
            [slv.mkTerm(Kind.APPLY_UF,
                allow_header,
                principal_head, action_head, resource_head,
                slv.mkTerm(Kind.AND,
                    metadata["cond"].substitute([negative_example_p, negative_example_a, negative_example_r, rule_ctx], [principal, action, resource, ctx]),
                    conj
                )
                ),
            ]
        )

    if verbose:
        pretty_print_str_with_brackets(str(grammar))
        sys.stdout.flush()

    # exit()
    policies = slv.synthFun("policies", [principal, action, resource, ctx], bool_sort, grammar)

    slv.addSygusAssume(slv.mkTerm(Kind.GEQ, id_of_entity(principal), slv.mkInteger(0)))
    slv.addSygusAssume(slv.mkTerm(Kind.LEQ, id_of_entity(principal), slv.mkInteger(entity_id_counter)))
    slv.addSygusAssume(slv.mkTerm(Kind.GEQ, type_of_entity(principal), slv.mkInteger(0)))
    slv.addSygusAssume(slv.mkTerm(Kind.LEQ, type_of_entity(principal), slv.mkInteger(type_id_counter)))
    slv.addSygusAssume(slv.mkTerm(Kind.GEQ, id_of_entity(resource), slv.mkInteger(0)))
    slv.addSygusAssume(slv.mkTerm(Kind.LEQ, id_of_entity(resource), slv.mkInteger(entity_id_counter)))
    slv.addSygusAssume(slv.mkTerm(Kind.GEQ, type_of_entity(resource), slv.mkInteger(0)))
    slv.addSygusAssume(slv.mkTerm(Kind.LEQ, type_of_entity(resource), slv.mkInteger(type_id_counter)))

    def py_ctx_to_smt(point_ctx):
        _ctx = []
        for f, t in contexts:
            s = t.getNullableElementSort()
            if f not in point_ctx:
                _ctx.append(slv.mkNullableNull(t))
                continue
            v = point_ctx[f]
            if v is not None:
                if s.isBoolean():
                    _ctx.append(slv.mkNullableSome(slv.mkBoolean(v)))
                elif s.isInteger():
                    _ctx.append(slv.mkNullableSome(slv.mkInteger(v)))
                elif s.isString():
                    _ctx.append(slv.mkNullableSome(slv.mkString(v)))
                else:
                    raise NotImplementedError(f"Unsupported sort {s} for context")
            else:
                _ctx.append(slv.mkNullableNull(t))
                # _ctx = slv.mkNullableSome()
        ctx = slv.mkTerm(Kind.APPLY_CONSTRUCTOR, context_type[0].getTerm(), *(_ctx))
        return ctx

        # semantic constraints: satisfy the log
    def log_entry(p, a, r, ctx, decision):
        ctx_smt = py_ctx_to_smt(ctx)
        constraint = slv.mkTerm(
            Kind.EQUAL,
            slv.mkTerm(Kind.APPLY_UF, policies, entity(*p), slv.mkString(a), entity(*r), ctx_smt),
            slv.mkTrue() if decision else slv.mkFalse())
        return constraint
    
    if not eq:
        constraints = []
        if noise is not None:
            for l in log:
                constraints.append(slv.mkTerm(Kind.ITE, log_entry(*l), slv.mkInteger(1), slv.mkInteger(0)))
            threshold = int(len(log)*(1 - noise))
            sum_satisfied = slv.mkTerm(Kind.ADD, *constraints)
            noise_log_constraint = slv.mkTerm(Kind.GEQ, sum_satisfied, slv.mkInteger(threshold))
            slv.addSygusConstraint(noise_log_constraint)
            if verbose:
                print(f"Log noise constraint: num_satisfied_log >= {threshold}")
        else:
            for l in log:
                # print(l)
                entry = log_entry(*l)
                slv.addSygusConstraint(entry)
                if verbose:
                    print(f"Log consistency: {entry}")
        

    else:
        # require exactly the same semantic
        orig_rule_applied = encoded_rules[0].substitute([negative_example_p, negative_example_a, negative_example_r], [principal, action, resource])
        # print(rule)
        constraint = slv.mkTerm(Kind.EQUAL, orig_rule_applied, slv.mkTerm(Kind.APPLY_UF, policies, principal, action, resource))
        # print(constraint)
        slv.addSygusConstraint(constraint)

    if compl is not None:
        # At least one of the points in the complement set is not allowed
        negation_predicate_lst = []
        for point in compl:
            # create ctx
            ctx_smt = py_ctx_to_smt(point[3])
            random_point_false = slv.mkTerm(Kind.NOT,
                                            slv.mkTerm(
                                                Kind.APPLY_UF, policies,
                                                entity(*point[0]),
                                                slv.mkString(point[1]),
                                                entity(*point[2]),
                                                ctx_smt
                                                ))
            negation_predicate_lst.append(random_point_false)
        

        if len(negation_predicate_lst) == 1:
            slv.addSygusConstraint(negation_predicate_lst[0])
            if verbose: print(f"Negating point in may_allow: {negation_predicate_lst[0]}")
        else:
            negation_predicate = slv.mkTerm(Kind.OR, *negation_predicate_lst)
            slv.addSygusConstraint(negation_predicate)
            if verbose: print(f"Negating point in may_allow: {negation_predicate}")



    if verbose:
        print(f"Process ID: {getpid()}")
        print(datetime.datetime.now())


    # return
    if (slv.checkSynth().hasSolution()):
        # pretty_print_str_with_brackets(str(slv.getSynthSolutions([policies])[0]))
        with open(f"sols/sol", "a") as f:
            pretty_print_str_with_brackets(str(grammar), out=f)
            pretty_print_str_with_brackets(str(slv.getSynthSolutions([policies])[0]), out=f)
            f.write("\n")
            f.write(str(datetime.datetime.now()) + "\n")

            s = slv.simplify(slv.getSynthSolutions([policies])[0])
            # s = slv.getSynthSolutions([policies])[0]
            # print(slv.simplify(slv.getSynthSolutions([policies])[0]))
            unparser = Unparser(entity_type_map, entity_map_flat)
            # print(unparser.rule_to_str(s))
            f.write("unparsed: \n")
            f.write(unparser.rule_to_str(s))
            f.write("\n")

        print(f"Solved")

        sols = []
        sol = unparser.rule_to_str(s)
        # return unparser.rule_to_str(s)
        while (slv.checkSynthNext().hasSolution()):
            # pretty_print_str_with_brackets(str(slv.getSynthSolutions([policies])[0]))
            s = slv.simplify(slv.getSynthSolutions([policies])[0])
            sols.append(unparser.rule_to_str(s))
            # print("We found another one")
        print(sols)
        return sol

    else:
        print(f"What")
        return False

class Unparser():
    def __init__(self, entity_type_map, entity_name_map):
        # reverse the entity_type_map
        self.entity_type_map = {v: k for k, v in entity_type_map.items()}
        # reverse the entity_name_map
        self.entity_name_map = {v: k for k, v in entity_name_map.items()}

    def rule_to_str(self, rule):
        match rule.getKind():
            case Kind.LAMBDA:
                return self.rule_to_str(rule[1])
            case Kind.APPLY_UF:
                return self.unparse_func(rule)
            case Kind.AND:
                return "(" + " && ".join([self.rule_to_str(r) for r in rule]) + ")"
                # return f"({self.rule_to_str(rule[0])} && {self.rule_to_str(rule[1])})"
            case Kind.IMPLIES:
                return f"(!({self.rule_to_str(rule[0])}) || {self.rule_to_str(rule[1])})"
            case Kind.EQUAL:
                return f"{self.rule_to_str(rule[0])} == {self.rule_to_str(rule[1])}"
            case Kind.OR:
               return "(" + " || ".join([self.rule_to_str(r) for r in rule]) + ")"
            case Kind.NOT:
                return f"(!({self.rule_to_str(rule[0])}))"
            case Kind.VARIABLE:
                return str(rule)
            case Kind.CONST_STRING:
                # XXX: no differentiation between strings and actions
                return "Action::\"" + rule.toPythonObj() + "\""
            case Kind.APPLY_CONSTRUCTOR:
                assert str(rule[0]) == "EntityCtor"
                t = self.entity_type_map[rule[1].toPythonObj()]
                # print(t)
                name = self.entity_name_map[rule[2].toPythonObj()]
                return f"{t}::\"{name}\""
            case Kind.APPLY_SELECTOR:
                if rule[0].getSort().getDatatypeSelectorDomainSort().isNullable():
                    return self.rule_to_str(rule[1])
                elif self.rule_to_str(rule[1]) == "context":
                    # ctx.sth
                    return f"context.{rule[0]}"

                raise Exception()
            case Kind.SET_MEMBER:
                return f"{self.rule_to_str(rule[0])} in {self.rule_to_str(rule[1])}"
            case _:
                print(rule.getKind())
                print(rule)
                raise NotImplementedError("The unparse rule for kind {} is not implemented".format(rule.getKind()))

    def action_rule_to_str(self, rule):
        match rule.getKind():
            case Kind.EQUAL:
                l, r = rule[0], rule[1]
                if self.rule_to_str(l) == "action":
                    return "action == " + self.rule_to_str(r)
                else:
                    return "action == " + self.rule_to_str(l)
            case Kind.OR:
                action_list = []
                for r in rule:
                    assert r.getKind() == Kind.EQUAL
                    l, r = r[0], r[1]
                    if self.rule_to_str(l) == "action":
                        action_list.append(self.rule_to_str(r))
                    else:
                        action_list.append(self.rule_to_str(l))
                return "action in [" + ", ".join(action_list) + "]"
                # print(rules)
            case _:
                raise NotImplementedError("Kind {} is not possible in action header".format(rule.getKind()))

    def unparse_func(self, child):
        name, *args = list(child)
        match str(name):
            case "allow_header":
                p, a, r, body = args
                p_parsed = self.rule_to_str(p) if p.getKind() != Kind.CONST_BOOLEAN else "principal"
                if a.getKind() != Kind.CONST_BOOLEAN:
                    a_parsed = self.action_rule_to_str(a)
                else:
                    a_parsed = "action"
                r_parsed = self.rule_to_str(r) if r.getKind() != Kind.CONST_BOOLEAN else "resource"
                return f"permit({p_parsed}, {a_parsed}, {r_parsed})\nwhen {{{self.rule_to_str(body)}}};"
            case "entity_is":
                e1, e2 = args
                return f"{self.rule_to_str(e1)} is {self.entity_type_map[e2.toPythonObj()]}"
            case "entity_eq":
                e1, e2 = args
                return f"{self.rule_to_str(e1)} == {self.rule_to_str(e2)}"
            case "entity_in":
                e1, e2 = args
                return f"{self.rule_to_str(e1)} in {self.rule_to_str(e2)}"
            case "has_attr":
                e1, e2 = args
                return f"{self.rule_to_str(e1)} has {e2.toPythonObj()}"
            case "ctx_has_attr":
                e1, e2 = args
                return f"{self.rule_to_str(e1)} has {e2.toPythonObj()}"
        if "__get_attr" in str(name):
            # parse name
            attr_name = str(name).partition("__get_attr_")[2].split("_")[0]
            # print(f"Get attribute {attr_name}")
            real_arg = self.rule_to_str(args[0])
            return f"{real_arg}.{attr_name}"
        raise NotImplementedError("The unparse rule for function {} is not implemented".format(name))


