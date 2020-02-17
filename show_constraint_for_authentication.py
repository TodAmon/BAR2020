import angr
import z3
import bar2020
project = angr.Project("authentication", load_options={'auto_load_libs':True})
check_addr = 0x4005d6
state = project.factory.call_state(check_addr, 0xc00000)
for i in range(0,64):
    s = state.solver.BVS("sym"+str(i), 8)
    state.memory.store(0xc00000 + i, s)
sm = project.factory.simulation_manager(state)
while len(sm.active) > 0:
    sm.explore(find=lambda s: "reject" in s.posix.dumps(1).decode())
constraints = [bar2020.claripy_constraint_list_to_z3(
    found.solver.constraints) for found in sm.found]
inz3 = z3.simplify(z3.Or(constraints))
print(str(bar2020.restore_variable_names(inz3)))

