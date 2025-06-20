import json

primitive_types = ["Boolean", "Long", "String"]

def parse_type(type_json):
    _t = (type_json["type"],)
    match _t:
        case ("Boolean",):
            pass
        case ("Long",):
            pass
        case ("String",):
            pass
        case ("Set",):
            _t = ("Set", parse_type(type_json["element"]))
        case ("Record",):
            attrs = []
            for attrname, attrinfo in type_json["attributes"].items():
                t = parse_type(attrinfo)
                attrs.append((attrname, t))
            _t = ("Record", attrs)
        case ("Entity",):
            _t = ("Entity", type_json["name"])
        case ("Extension",):
            raise NotImplemented("Not implemented: Extension")
        case _:
            raise TypeError(f"Unknown type: {_t}")
    return _t

def parse_schema(schema_json: dict):
    entity_types = schema_json[""]["entityTypes"]
    entity_names = []
    entity_info = {}
    entity_parent_info = {}
    for entity_name, info in entity_types.items():
        # print(f"Type: {entity_name}")
        entity_names.append(entity_name)
        if "memberOfTypes" in info:
            entity_parent_info[entity_name] = info["memberOfTypes"]
            # print(f"  Member of types: {info['memberOfTypes']}")
        attrs = {}
        if "shape" in info:
            # print("  Attributes:")
            for attrname, attrinfo in info["shape"]["attributes"].items():
                t = parse_type(attrinfo)
                # print(f"    {attrname}: {t}")
                attrs[attrname] = t
        entity_info[entity_name] = attrs
    actions = schema_json[""]["actions"]
    action_names = list(actions.keys())
    return entity_info, action_names, actions, entity_parent_info

def ground_depth(entity_info, depth=0):
    if depth == 0:
        return []
    if depth == 1:
        accessible = []
        for entity_name, attrs in entity_info.items():
            for attr_name, attr_type in attrs.items():
                accessible.append([(entity_name, attr_name, attr_type)])
        return accessible
    accessible = ground_depth(entity_info, depth-1)
    new_accessible = []
    for *prev_path, (entity_name, attr_name, attr_type) in accessible:
        type_name, *info = attr_type
        if type_name == "Entity":
            entity_type = info[0]
            for _attr_name, _attr_type in entity_info[entity_type].items():
                new_accessible.append(prev_path + [(entity_name, attr_name, (type_name, *info)), (entity_type, _attr_name, _attr_type)])
        elif type_name == "Record":
            print("ummm")
            raise NotImplemented("Record type not implemented")
    return new_accessible

def print_ground_depth(entity_info, depth=0):
    accessible = ground_depth(entity_info, depth)
    for path in accessible:
        path_iter = iter(path)
        entity_name, attr_name, _ = next(path_iter)
        print(f"{entity_name}.{attr_name}", end="")
        if depth > 1:
            print(".", end="")
        print(".".join([f"{attr_name}" for _, attr_name, _ in path_iter]), end="")
        print(": ", path[-1][2])
    

if __name__ == "__main__":
    # with open('gdrive.cedarschema.json') as f:
        # data = json.loads(f.read())
    # entities = parse_schema(data)
    # print_ground_depth(entities, 4)
    # print("------")
    with open('../tinytodo/tinytodo.cedarschema.json') as f:
        data = json.loads(f.read())
    entities, actions = parse_schema(data)
    print(entities)
    print("------")
    for i in range(1,5):
        print_ground_depth(entities, i)
    