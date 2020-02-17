import angr
import z3
import os
import claripy
import archinfo
import logging
import bar2020

logging.getLogger("angr").setLevel(logging.WARNING)
logging.getLogger("bar2020").setLevel(logging.WARNING)
logger = logging.getLogger(__name__)
logger.setLevel(logging.INFO)

def get_function_address(cfg, function_name, plt=None):
    """
    Returns the address of the function, 
    or raises an AnalyzeError if it can't be found.
    """
    found = [
        addr
        for addr, func in cfg.kb.functions.items()
        if function_name == func.name and (plt is None or func.is_plt == plt)
    ]
    if found:
        return found[0]
    raise Exception("No address found for function : " + function_name)

binary = str(os.path.join(os.path.dirname(os.path.abspath(__file__)), "sub1or2"))
project = angr.Project(binary, auto_load_libs=False)
cfg = project.analyses.CFGFast(normalize=True)
function_name = "sub1or2"
start_address = get_function_address(cfg, function_name)
entry_state = project.factory.entry_state()

symbolic_integer = claripy.BVS("y_intle:32", 32)
symbolic_integer_le = claripy.Concat(
    claripy.Extract(7,0,symbolic_integer),
    claripy.Extract(15,8,symbolic_integer),
    claripy.Extract(23,16,symbolic_integer),
    claripy.Extract(31,24,symbolic_integer))
print("vex for 0x40053b: ")
project.factory.block(0x40053b).vex.pp()
call_state = project.factory.call_state(start_address,
                                        symbolic_integer_le, ret_addr=0x0)
simulation_manager = project.factory.simulation_manager(call_state)
while simulation_manager.active:
    for i in range(0,len(simulation_manager.active)):
        state = simulation_manager.active[i]
        memaddr4 = state.solver.eval(state.regs.rbp) - 4
        memval4 = state.memory.load(memaddr4,4, endness=archinfo.Endness.LE)

        if state.addr == 0x400537:
            print("after the first decrement of x we have y:")
            print("in Claripy: " + str(memval4))
            inz3 = bar2020.restore_variable_names(
                claripy.backends.z3.convert(memval4))
            print("as Z3 sexpr: " + str(inz3.sexpr()))
            print("as Z3 __str__: " + str(inz3))

        if state.addr == 0x400544:
            print("***RETURN PATH FOUND, return result in eax:")
            print(claripy.backends.z3.convert(state.regs.eax).sexpr())
            print("***path-constraint is:")
            inz3 = bar2020.claripy_constraint_list_to_z3(state.solver.constraints)
            inz3_typed = bar2020.restore_variable_names(inz3,{"y": "intle32"})
            inz3 = bar2020.restore_variable_names(inz3)

            inz3_std_simplify_only = z3.simplify(inz3_typed)
            inz3_ctx_simplify_only = bar2020.ctx_solver_simplify(inz3_typed)
            inz3_ctx_simplify_both_std_first = bar2020.ctx_solver_simplify(
                inz3_std_simplify_only)
            inz3_ctx_simplify_both_ctx_first = z3.simplify(inz3_ctx_simplify_only)
            print(inz3.sexpr())
            print("converted to integer domain directly")
            answer = bar2020.from_bv_to_int_domain(inz3_typed)
            print(str(answer))
            print("and then run through ctx-solver-simplify")
            print(bar2020.ctx_solver_simplify(answer))
            print("converted to integer domain from std simplify only")
            answer = bar2020.from_bv_to_int_domain(inz3_std_simplify_only)
            print(str(answer))
            print("and then run through ctx-solver-simplify")
            print(bar2020.ctx_solver_simplify(answer))
            print("converted to integer domain from ctx simplify only")
            answer = bar2020.from_bv_to_int_domain(inz3_ctx_simplify_only)
            print(str(answer))
            print("and then run through ctx-solver-simplify")
            print(bar2020.ctx_solver_simplify(answer))
            print("converted to integer domain from both std first")
            answer = bar2020.from_bv_to_int_domain(inz3_ctx_simplify_both_std_first)
            print(str(answer))
            print("and then run through ctx-solver-simplify")
            print(bar2020.ctx_solver_simplify(answer))
            print("converted to integer domain from both ctx first")
            answer = bar2020.from_bv_to_int_domain(inz3_ctx_simplify_both_ctx_first)
            print(str(answer))
            print("and then we run through ctx-solver-simplify")
            answer = bar2020.ctx_solver_simplify(answer) 
            print(answer)
            
    simulation_manager.step(num_inst=1)

