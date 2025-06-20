import sys

def pretty_print_str_with_brackets(s, out=sys.stdout):
    """
    Given a string s with nested brackets without newline, pretty print with same
    indentation level for each bracket level.
    """
    indent = 0
    in_quotes = False
    for i, c in enumerate(s):
        if not in_quotes and c == '(':
            print('\n'+'  '*indent + c, end='', file=out)
            indent += 2
        elif not in_quotes and c == ')':
            indent -= 2
            if s[i-1] != ')':
                print(')', end="", file=out)
                if len(s)>i+2 and s[i+1] == ')':
                    print("", file=out)
            else:
                print('  '*indent + c, file=out)
        elif c == '"' or c == "|":
            in_quotes = not in_quotes
            print(c, end='', file=out)
        else:
            print(c, end='', file=out)
    print("", file=out)


# https://stackoverflow.com/questions/8673482/transitive-closure-python-tuples
def transitive_closure(a):
    closure = set(a)
    while True:
        new_relations = set((x,w) for x,y in closure for q,w in closure if q == y)

        closure_until_now = closure | new_relations

        if closure_until_now == closure:
            break

        closure = closure_until_now

    return closure