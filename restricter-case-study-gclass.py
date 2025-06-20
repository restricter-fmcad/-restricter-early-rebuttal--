import translate_entity_store
import argparse
import json
from collections import defaultdict
import datetime
from get_pt import Solver
from copy import deepcopy
from random import shuffle, seed

parser = argparse.ArgumentParser(description='Main program for running Restricter')
parser.add_argument('--num_conj', '-d', type=int, help='Number of conjunctions', default=1)
parser.add_argument('--size', '-s', type=int, help='Entity Size', required=True)
parser.add_argument('--eop', '-e', help='Percentage of exercised overprivileges', type=int, default=None)
parser.add_argument('--repeat', '-r', type=int, help='Number of repeats for the experiment', default=1)
parser.add_argument('--verbose','-v', action='store_true', help='Print the grammar and solutions', default=False)
parser.add_argument('--vv', action='store_true', help='Very verbose', default=False)
parser.add_argument('--slice', type=int, help='Pick one rule to restrict', required=True)

parser.add_argument('--entities_prefix', type=str, default="cedar-restrict-case-studies/dist/GClassroom/entities")
parser.add_argument('--log_prefix', type=str, default="cedar-restrict-case-studies/dist/GClassroom/logs")

parser.add_argument('--log_size', default=None, help='Size of log slice. If not provided, will use the full slice', type=int)
parser.add_argument('--seed', type=int, default=196883, help='Random seed for shuffling')
parser.add_argument('--num_req_negation', '-n', type=int, default=1, help='Number of requests to negate each loop')


args = parser.parse_args()




policy_to_slice = args.slice
size = args.size
restrict_alg_noise = None
if args.eop is not None:
    restrict_alg_noise = args.eop / 100.0

max_fail = 5

pick_point_times = []
fail_times = []
success_times = []
time_to_first_success = []

schema_file = 'gclassroom.schema.json'
policy_file = "gclassroom.cedar"

entity_file = f"{args.entities_prefix}.{size}.json"
with open(policy_file) as f:
    policy_text = f.read()
if args.verbose:
    print("Parsing schema")
    print(datetime.datetime.now())
with open(schema_file) as f:
    entity_schema, actions, action_scope, hierarchy = translate_entity_store.parse_schema(json.loads(f.read()))
if args.verbose:
    print("OK")
    print("Parsing Entity store")
    print(datetime.datetime.now())
with open(entity_file) as f:
    entity_store_json = json.loads(f.read())

if args.verbose:
    print("OK")
    print(datetime.datetime.now())



slices = defaultdict(list)
# read log
log = []

# Log translation
with open(f"{args.log_prefix}.{size}.json") as f:
    _log = json.loads(f.read())
for entry in _log:
    principal = entry["request"]["principal"]
    p_t, p_name = principal.split("::")
    p_name = p_name.replace("\"", "")
    action = entry["request"]["action"]
    action = action.split("::")[1].replace("\"", "")
    resource = entry["request"]["resource"]
    r_t, r_name = resource.split("::")
    r_name = r_name.replace("\"", "")
    context = entry["request"]["context"]
    decision = True if entry["result"] == "ALLOW" else False
    log.append(((p_t, p_name), action, (r_t, r_name), context, decision))

# Slicing
slices = defaultdict(list)
pt_solver = Solver(entity_schema, actions, action_scope, hierarchy, entity_store_json, policy_text, verbose=False, vv=args.vv)
for req in log:
    p, a, r, ctx, d = req

    if not d:
        continue
    for rule in range(pt_solver.num_rules):
        # evaluate req against rule, if it is allowed and the
        # request is allowed in the original log (so no deny rule
        # denies it), add it to the slice
        if d and pt_solver.evaluate_req(rule, p, a, r, ctx) == d:
            slices[f'policy{rule}'].append(req)
            

print(f"size of log: {len(log)}")
sliced = slices[f'policy{policy_to_slice}']
print("slice size: ", len(sliced))
if not sliced:
    print("No slices found for this policy")
    exit(1)


if args.log_size is not None:
    seed(196883)
    shuffle(sliced)
    sliced = sliced[:args.log_size]
    print("Truncated slice size: ", len(sliced))

all_compl_pts = []

print(datetime.datetime.now())
for _ in range(args.repeat):
    x = True
    blocked = deepcopy(sliced)
    success_time = []
    pick_point_time = []
    fail_time = []

    first_success = False
    num_fail = 0
    policy = policy_text
    t_start = datetime.datetime.now()
    to_synth = policy_to_slice if not first_success else 0 
    while policy:
        last_policy = policy
        if first_success:
            print("Tightening found")
            print(policy)
        to_synth = policy_to_slice if not first_success else 0 
        
        pt_solver = Solver(entity_schema, actions, action_scope, hierarchy, entity_store_json, policy, verbose=False, vv=args.vv)
        
        compl_list = []
        
        for _ in range(args.num_req_negation):
            t0 = datetime.datetime.now()
            x, unsat_core = pt_solver.get_pt(blocked, synth_rule=to_synth, check_log=False)
            t1 = datetime.datetime.now()
            if not x:
                print("Cannot find a point to negate")
                if args.verbose:
                    print("Unsat core: ", unsat_core)
                break
            print("Point picking takes ", t1 - t0)
            pick_point_time.append(t1 - t0)
            print("Negating point", x)
            compl_list.append(x)
            all_compl_pts.append(x)
            blocked.append((*x, False))
        
        if not compl_list:
            print("No points to negate")
            break

        policy = translate_entity_store.solve(entity_schema, actions, action_scope, hierarchy, entity_store_json, sliced, policy, vars(args) | {"num_allows": None}, verbose=args.verbose, vv=args.vv, synth_rule=to_synth, compl=compl_list, noise=restrict_alg_noise)
        t2 = datetime.datetime.now()
        if not policy:
            print(f"Time taken (fail): {t2 - t1}")
            fail_time.append(t2 - t1)
            num_fail += 1
            if num_fail >= max_fail:
                print("Too many failures, stopping")
                break
            else:
                print("Retrying with last policy")
                policy = last_policy
        else:
            print(f"Time taken (success): {t2 - t1}")
            if not first_success:
                time_to_first_success.append(num_fail)
            success_time.append(t2 - t1)
            first_success = True

    pt_solver = Solver(entity_schema, actions, action_scope, hierarchy, entity_store_json, last_policy, verbose=False, vv=args.vv)

    print("Final policy:")
    print(last_policy)

    for req in sliced:
        new_decision = pt_solver.evaluate_req(to_synth, req[0], req[1], req[2], req[3])
        if not new_decision:
            print(f"Suspected noise: {req}")
    pick_point_times.append(pick_point_time)
    fail_times.append(fail_time)
    success_times.append(success_time)

    print("Cannot improve further")
    
print("Point picking: ", [[t.total_seconds() for t in pick_point_time] for pick_point_time in pick_point_times])
print("Failure: ", [[t.total_seconds() for t in fail_time] for fail_time in fail_times])
print("Success: ", [[t.total_seconds() for t in success_time] for success_time in success_times])
print("Time to first success: ", time_to_first_success)


