import z3
import bar2020

#setup
y = z3.BitVec('y_intle:32', 32)
i_y = z3.Int('y_intle:32')
ex3124 = z3.Extract(31, 24, y)
ex2316 = z3.Extract(23, 16, y)
ex158 = z3.Extract(15, 8, y)
ex70 = z3.Extract(7, 0, y)
yconcat = z3.Concat(ex70, ex158, ex2316, ex3124)

#example of typed variables
bv_value1 = (yconcat == z3.BitVecVal(-2,32))
answer = bar2020.from_bv_to_int_domain(bv_value1)
print("As bit-vector: " + str(bv_value1) + " in integer domain: " + str(answer))
assert(bar2020.same_constraint_single_variable(answer,z3.Int('y_intle:32') == -2))

#another example
bv_value2 = z3.And(ex3124 == z3.BitVecVal(-2,8),
                  ex2316 == z3.BitVecVal(-1,8),
                  ex158 == z3.BitVecVal(-1,8),
                  ex70 == z3.BitVecVal(-1,8))
answer = bar2020.from_bv_to_int_domain(bv_value2)
print("As bit-vector: " + str(bv_value2) + " in integer domain: " + str(answer))
assert(bar2020.same_constraint_single_variable(answer,z3.Int('y_intle:32') == -2))

#check two values are the same
assert(bar2020.same_value_single_variable(bv_value1, bv_value2))

#example of conversion not precise
variable_relationship = (z3.BV2Int(yconcat) == i_y)
i_value = i_y + 1
bv_value3 = yconcat + z3.BitVecVal(1, 32)
value_relationship = (z3.BV2Int(bv_value3) == i_value)
(same, model, explanation) = (
    bar2020.single_variable_bit_vector_domain_equals_integer_domain(
    i_y, y, variable_relationship,
    i_value, bv_value3, value_relationship,
    True, True, bv_type='intle:32'))
print("Is conversion precise for bit-vector:" +
      str(bv_value3) + " in integer domain:" + str(i_value))
print(explanation)

#check given constraints that should make them precise
i_value = i_y - 2
bv_value4 = yconcat + z3.BitVecVal(-2, 32)
value_relationship = (z3.BV2Int(bv_value4) == i_value)
i_condition = i_y > 6
bv_condition = yconcat > z3.BitVecVal(6, 32)
print("Alas, can we prove that bit-vector: " + str(bv_value4) +
      " in integer domain: " + str(i_value) + " under constraints: " +
      str(i_condition) + " and " + str(bv_condition) + " is precise?")
print("... wait for demonstration of timeout")
(same, model, explanation) = (
    bar2020.single_variable_bit_vector_domain_equals_integer_domain(
    i_y, y, variable_relationship,
    i_value, bv_value4, value_relationship,
    i_condition, bv_condition, bv_type='intle:32'))
print(explanation)

#example using logic synthesis
constraint = z3.And(z3.Or(y > 6, y == 6), z3.Not(y == 6))
using_sis = bar2020.simplify_z3_boolean_using_logic_synthesis_approach(constraint)
print("Using sis, we can simplify " + str(constraint) + " to " + str(using_sis))
            


