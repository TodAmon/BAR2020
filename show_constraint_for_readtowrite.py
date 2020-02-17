import angr
import z3
import bar2020
import claripy

project = angr.Project("readtowrite", load_options={'auto_load_libs':True})
check_addr = 0x4005d6
state = project.factory.call_state(check_addr, 0xc00000, 0xc00100)
for i in range(0,4):
    s = state.solver.BVS("sym"+str(i), 8)
    state.memory.store(0xc00000 + i, s)
    state.memory.store(0xc00100 + i, 0)

sm = project.factory.simulation_manager(state)
while sm.active:
    for state in sm.active:
        if state.addr == 0x400631:
            print("***FOUND A PATH***")
            path_constraint = bar2020.claripy_constraint_list_to_z3(
                state.solver.constraints) 
            path_constraint = bar2020.restore_variable_names(path_constraint)
            buf = bar2020.restore_variable_names(claripy.backends.z3.convert(
                state.mem[state.regs.eax].int.resolved))
            print("Buffer value: " + buf.sexpr())
            #for now, sequencing check depends on concat being broken up
            buf = z3.simplify(buf)
            print("Buffer value: " + buf.sexpr())
            buf_with_sequences = bar2020.replace_bv_sequences_with_conjectures(
                buf, "sym")
            print("Buf with sequences: " + str(buf_with_sequences.sexpr()))
            print("Integer domain buffer value: " + bar2020.from_bv_to_int_domain(
                buf_with_sequences).sexpr()) 
            print("Path constraint as Z3 sexpr: " + path_constraint.sexpr())
            #for now, sequencing check depends on concat being broken up
            path_constraint = z3.simplify(path_constraint)            
            pc_with_sequences = bar2020.replace_bv_sequences_with_conjectures(
                path_constraint, "sym")
            print("Path constraint with sequences:" + str(pc_with_sequences.sexpr()))
            path_constraint_i = bar2020.from_bv_to_int_domain(pc_with_sequences)
            print("Path constraint in integer domain: " + str(path_constraint_i))
            spi = bar2020.ctx_solver_simplify(path_constraint_i)
            print("Simplified path constraint: " + str(bar2020.ctx_solver_simplify(spi)))
        
    sm.step(num_inst=1)
    
