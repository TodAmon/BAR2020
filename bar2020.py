"""This package is part of a prototype / proof-of-concept for working with 
path constraints obtained from symbolic execution.  
It is intended solely to reproduce the results reported in the BAR 2020 
Workshop Paper:  'Creating Human Readable Path Constraints from Symbolic Execution' """

import os
import math
import logging
import itertools
import tempfile
import subprocess
import bitstring
import z3
import claripy

logger = logging.getLogger(__name__)
def all_uninterpreted(f):
    if f.decl().kind() == z3.Z3_OP_UNINTERPRETED:
        return [f]
    else:
        results = []
        for child in f.children():
            results.extend(all_uninterpreted(child))
        return results

def bv_value_to_int_value(bv_value, bv_type, force_big_endian=False):
    if bv_type == "intle:32" and not force_big_endian:
        f = [x for x in bitstring.BitArray(uint=bv_value.as_long(), length=32).cut(8)]
        return z3.IntVal(bitstring.pack('int:8, int:8, int:8, int:8',
                                        f[3].int, f[2].int, f[1].int, f[0].int).int)
    elif bv_type == "intbe:32" or (bv_type == "intle:32" and force_big_endian):
        return z3.IntVal(bv_value.as_signed_long())
    elif bv_type == "uintbe:32" or (bv_type == "uintle:32" and force_big_endian):
        return z3.IntVal(bv_value.as_long())
    else:
        raise NotImplementedError("unrecognized type: " + bv_type)

def integer_to_bv_value(i_value, bv_type):
    if bv_type == "intle:32":
        f = [x for x in bitstring.BitArray(int=i_value, length=32).cut(8)]
        return z3.BitVecVal(bitstring.pack('int:8, int:8, int:8, int:8',
                                           f[3].int, f[2].int, f[1].int, f[0].int).int, 32)
    elif bv_type == "intbe:32":
        return z3.BitVecVal(i_value, 32)
    elif bv_type == "uintbe:32": #...TODO... uint has not been tested at all
        return z3.BitVecVal(i_value, 32)
    else:
        raise NotImplementedError("unrecognized type: " + bv_type)

def is_typed_bv_le32(bv_variable):
    if not z3.is_bv(bv_variable):
        return False
    if not bv_variable.decl().kind() == z3.Z3_OP_UNINTERPRETED:
        return False
    if bv_variable.size() != 32:
        return False
    if bv_variable.decl().name().endswith("_intle:32"):
        return True
    return False

def get_children_of(z3from):
    children = z3from.children()
    children_converted = []
    found_one_bv = False
    found_one_not_bv = False
    for child in children:
        converted_child = from_bv_to_int_domain(child)
        if z3.is_bv(converted_child):
            found_one_bv = True
        else:
            found_one_not_bv = True
        children_converted.append(converted_child)
    #if some of the children are still bv but not all of them, its a problem
    if found_one_bv and found_one_not_bv:
        return children
    return children_converted

def is_typed_bv_be32(bv_variable):
    if not z3.is_bv(bv_variable):
        return False
    if not bv_variable.decl().kind() == z3.Z3_OP_UNINTERPRETED:
        return False
    if bv_variable.size() != 32:
        return False
    if bv_variable.decl().name().endswith("_intbe:32"):
        return True
    return False

def bv_value_allowed(bv_value, bv_variable, bv_condition):
    solver = z3.Solver()
    solver.add(bv_variable == bv_value)
    solver.add(bv_condition)
    check = solver.check()
    if check == z3.unsat:
        return False
    elif check == z3.sat:
        return True
    else:
        return None

def create_eqn_expression(z3from, expressions_map):
    eqn = "("
    first = True
    if z3from.decl().kind() == z3.Z3_OP_AND:
        for child in z3from.children():
            if not first:
                eqn += " "
            else:
                first = False
            eqn += create_eqn_expression(child, expressions_map)
        eqn += ")"
    elif z3from.decl().kind() == z3.Z3_OP_OR:
        for child in z3from.children():
            if not first:
                eqn += " + "
            else:
                first = False
            eqn += create_eqn_expression(child, expressions_map)
        eqn += ")"
    elif z3from.decl().kind() == z3.Z3_OP_NOT:
        eqn = create_eqn_expression(z3from.children()[0], expressions_map) + "' "
    else:
        eqn = expressions_map[z3from]
    return eqn

def set_of_all_variables_in(elist_or_set):
    """Return a set of all variables appearing in any list or set of expressions"""
    result = set()
    for e in elist_or_set:
        result = result.union(all_uninterpreted(e))
    return result

def has_free_variable(elist_or_set, vlist_or_set=None):
    if vlist_or_set is None:
        vlist_or_set = set_of_all_variables_in(elist_or_set)
    for v in vlist_or_set:
        count = 0
        for e in elist_or_set:
            if v in all_uninterpreted(e):
                count += 1
        if count == 1:
            return True
    return False

def dont_cares_for_combo(etuple):
    def generate_potential_dont_care(btuple, etuple):
        def apply(b, e):
            return e if b else z3.Not(e)
        return z3.And([apply(btuple[index], e) for index, e in enumerate(etuple)])
    dc_in_combo = []
    bools = [True, False]
    for check in list(itertools.product(bools, repeat=len(etuple))):
        potential_dc = generate_potential_dont_care(check, etuple)
        solver = z3.Solver()
        solver.add(potential_dc)
        if solver.check() == z3.unsat:
            dc_in_combo.append(potential_dc)
    return dc_in_combo

def set_of_expressions_in(z3from, convert_leq_geq=True):
    """list of expressions in a z3 expression (e.g., remove all the boolean connectives)"""
    result = set()
    if not z3.is_expr(z3from):
        return result
    elif (z3from.decl().kind() == z3.Z3_OP_AND or
          z3from.decl().kind() == z3.Z3_OP_OR or
          z3from.decl().kind() == z3.Z3_OP_NOT):

        for child in z3from.children():
            result.update(set_of_expressions_in(child, convert_leq_geq))
    elif (z3from.decl().kind() == z3.Z3_OP_EQ or
          z3from.decl().kind() == z3.Z3_OP_SGT or
          z3from.decl().kind() == z3.Z3_OP_SLT or
          z3from.decl().kind() == z3.Z3_OP_GT or
          z3from.decl().kind() == z3.Z3_OP_LT or
          z3from.decl().kind() == z3.Z3_OP_UGT or
          z3from.decl().kind() == z3.Z3_OP_ULT or
          False ): 
        result.add(z3from)

    elif (z3from.decl().kind() == z3.Z3_OP_SGEQ or
          z3from.decl().kind() == z3.Z3_OP_UGEQ or
          z3from.decl().kind() == z3.Z3_OP_GE):
        if convert_leq_geq == True:
            lh = z3from.children()[0]
            rh = z3from.children()[1]
            result.add(lh > rh)
            result.add(lh == rh)
        else:
            result.add(z3from)

    elif (z3from.decl().kind() == z3.Z3_OP_SLEQ or
          z3from.decl().kind() == z3.Z3_OP_ULEQ or
          z3from.decl().kind() == z3.Z3_OP_LE):
        if convert_leq_geq == True:
            lh = z3from.children()[0]
            rh = z3from.children()[1]
            result.add(lh < rh)
            result.add(lh == rh)
        else:
            result.add(z3from)
    elif (z3from.decl().kind() == z3.Z3_OP_TRUE or
          z3from.decl().kind() == z3.Z3_OP_FALSE):
        pass
    else:
        logger.warning("DID not handle decl().kind() of " + str(z3from.decl().kind()))
    return result

def generate_eqn_for_boolean_expression(z3from, dc_limit=None):
    """Returns a triple (mapping, onset_eqn_string, dcset_eqn_string) where mapping is a dict and 
    onset_eqn_string is a string corresponding to the Synopsys equation format representation for 
    the onset for the z3from expression, and dcset likewise for the don't care set.
    Return (None, None, None) if no mapping is possible"""
    #TODO:  syntactic manipulation/normalization, e.g., we dont
    #want x > 5 and 5 < x as two separate constraints...
    expressions = set_of_expressions_in(z3from, convert_leq_geq=False) #more needed
    if dc_limit == None:
        dc_limit = len(expressions)
    else:
        dc_limit = min(len(expressions), dc_limit)
    dont_cares = []
    for nvar in range(2, dc_limit+1):
        comb = itertools.combinations(expressions, nvar)
        for c in comb:
            if not has_free_variable([x for x in c]):
                dont_cares.extend(dont_cares_for_combo(c))
    eqn_string = "#Synopsis eqn format for expression\n"
    inorder_string = "INORDER ="
    label_index = 0
    expressions_map = {}
    for expr in expressions:
        if label_index > 25:
            prefix = int(label_index / 26)
            if prefix > 25:
                raise NotImplementedError("too many variables!")
            c = chr(ord('a') + prefix - 1) + chr(ord('a') + label_index % 26)
        else:
            c = chr(ord('a') + label_index)
        inorder_string += " " + c + "\n"
        label_index += 1
        expressions_map[expr] = c
    inorder_string += ";\n"
    eqn_string += inorder_string
    eqn_string += "OUTORDER = f1;\n"
    eqn_string += "f1 = "
    dc_eqn_string = eqn_string
    eqn_string += create_eqn_expression(z3from, expressions_map) + ";\n"
    if len(dont_cares) > 0:
        dc_eqn_string += create_eqn_expression(z3.Or(dont_cares), expressions_map) + ";\n"
    else:
        dc_eqn_string = None
    return (expressions_map, eqn_string, dc_eqn_string)

def read_eqn_assuming_sop(eqn_string, label_to_expression_map):
    def labels_in_sop_expression(sop_expression):
        def clean(variable):
            return variable.replace('!', '')
        products = sop_expression.split(" + ")
        variables = [product.split("*") for product in products]
        flat_variables = [item for sublist in variables for item in sublist]
        flat_variables = [clean(v) for v in flat_variables]
        return flat_variables
    def build_definitions(lines):
        definitions = {}
        start_building = False
        last_key = None
        last_value = None
        for line in lines:
            if line.startswith("Don't care"):
                break  #we don't care about the actual don't cares
            elif line.startswith("OUTORDER = "):
                start_building = True
            elif start_building:
                if "=" in line:
                    if last_key is not None:
                        definitions[last_key] = last_value
                    last_key = line[: line.index(' = ')]
                    last_value = line[line.index(" = ") + len(" = "):]
                else:
                    last_value += line
        if last_key is not None:
            definitions[last_key] = last_value
        return definitions
    def build_z3_sum_of_products(sop_expression):
        def build_z3_product(product_expression):
            z3_terms = []
            terms = product_expression.split('*')
            for term in terms:
                if term.startswith("!"):
                    z3_terms.append(z3.Not(label_to_expression_map[term[1:]]))
                else:
                    z3_terms.append(label_to_expression_map[term])
            if len(z3_terms) > 1:
                return z3.And(z3_terms)
            elif len(z3_terms) == 1:
                return z3_terms[0]
            else:
                raise NotImplementedError("there were no terms???")
        products = sop_expression.split(" + ")
        z3_products = []
        for product in products:
            z3_products.append(build_z3_product(product))

        if len(z3_products) > 1:
            return z3.Or(z3_products)
        elif len(z3_products) == 1:
            return z3_products[0]
        else:
            raise NotImplementedError("there were no products")
    lines = eqn_string.split('\n')
    if len(lines) < 1:
        raise NotImplementedError("eqn was empty for some reason?????")
    outvar = None
    for line in lines:
        if line.startswith("OUTORDER = "):
            outvar = line[len("OUTORDER = "):-1]
    if outvar is None:
        raise NotImplementedError("eqn file format missing OUTORDER\n" + str(lines))
    label_to_expression_map['1'] = True
    label_to_expression_map['0'] = False
    definitions_map = build_definitions(lines)
    definitions_map = {k: v[:-1] for k, v in definitions_map.items()} 
    if outvar in label_to_expression_map:
        raise NotImplementedError("we assumed you ould not have variable named: " + outvar)

    while len(definitions_map) > 0:
        for label, sop_expression in definitions_map.items():
            labels = labels_in_sop_expression(sop_expression)
            check = [label in label_to_expression_map for label in labels]
            if all(check):
                z3_expression = build_z3_sum_of_products(sop_expression)
                label_to_expression_map[label] = z3_expression
                del definitions_map[label]
                break
    return label_to_expression_map[outvar]

def get_sis():
    if not 'SIS_FOR_BAR2020' in os.environ:
        raise NotImplementedError("SIS_FOR_BAR2020 should point to sis binary")
    return os.environ['SIS_FOR_BAR2020']
        

def create_pla(pla_file, eqn):
    with tempfile.NamedTemporaryFile(mode='w') as eqn_file:
        eqn_file.write(eqn)
        eqn_file.flush()
        sis = get_sis()
        try:
            out = subprocess.run(
                [sis, "-t", "eqn", "-T", "pla", "-o", pla_file.name, eqn_file.name],
                stdout=subprocess.PIPE, stderr=subprocess.PIPE
            )
            if not out.returncode == 0:
                logger.error("subprocess failed!!!! could not generate pla")
                raise NotImplementedError("a problem running SIS to generate pla")
        except Exception as ex:
            raise NotImplementedError("could not run sis!" + str(ex))

def simplify_z3_boolean_using_logic_synthesis_approach(expr, dclimit=None):
    (mymap, eqn, dceqn) = generate_eqn_for_boolean_expression(expr, dclimit)
    if dceqn == None or len(dceqn) == 0:
        return expr
    with tempfile.NamedTemporaryFile(mode='r+') as pla_file:
        with tempfile.NamedTemporaryFile(mode='r+') as dcpla_file:        
            create_pla(pla_file, eqn)
            create_pla(dcpla_file, dceqn)
            plastring = pla_file.read()
            dcstring = dcpla_file.read()
    just_onset = []
    found_obf1 = False
    number_of_terms = 0
    dca = dcstring.split('\n')
    for line in dca:
        if found_obf1 and number_of_terms == 0:
            number_of_terms = int(line[3:])
        elif found_obf1:
            just_onset.append(line)
            if len(just_onset) == number_of_terms:
                break
        elif line == ".ob f1":
            found_obf1 = True
    dc_set = [x[0:-1] + "-" for x in just_onset]
    plaa = plastring.split('\n')
    plafirst = plaa[0:-2] #the last two lines are ".e" and ''
    plalast = plaa[-2:]
    newpla = plafirst
    newpla.extend(dc_set)
    newpla.extend(plalast)
    newplastring = "\n".join(newpla)
    with tempfile.NamedTemporaryFile(mode='w') as newpla_file:
        newpla_file.write(newplastring)
        newpla_file.flush()
        with tempfile.NamedTemporaryFile(mode='r+') as neweqn_file:        
            sis = get_sis()
            try:
                #sis_command = "full_simplify;decomp -g;full_simplify"
                sis_command = "full_simplify"
                out = subprocess.run(
                    [sis, "-t", "pla", "-c", sis_command, "-T", "eqn",
                     "-o", neweqn_file.name, newpla_file.name],
                    stdout=subprocess.PIPE, stderr=subprocess.PIPE
                )
                if not out.returncode == 0:
                    logger.error("subprocess failed!!!! problem running SIS fully simplify")
                    raise NotImplementedError("a problem running SIS full simplify")
            except Exception:
                raise NotImplementedError("could not run sis")
            simplified_string = neweqn_file.read()            
    label_to_expression_map = { v: k for k, v in mymap.items() }
    simplified_z3_boolean_expression = read_eqn_assuming_sop(simplified_string,
                                                             label_to_expression_map)
    return simplified_z3_boolean_expression

def claripy_constraint_list_to_z3(constraints_list):
    z3list = []
    for constraint in constraints_list:
        z3list.append(claripy.backends.z3.convert(constraint))
    return z3.And(*z3list)

def claripy_constraint_to_z3(constraint):
    return claripy.backends.z3.convert(constraint)

def restore_variable_names(inz3, type_annotation_map={}):
    """supports stripping angr detritus and annotating"""
    all_variable_names = list(set(all_uninterpreted(inz3)))
    for variable in all_variable_names:
        if "_" in variable.decl().name():
            index = variable.decl().name().index("_")            
            newname = variable.decl().name()[:index]
        else:
            newname = variable.decl().name()
        if newname in type_annotation_map:
            newname = newname + "_" + type_annotation_map[newname]

        if variable.sort().kind() == z3.Z3_INT_SORT:
            inz3 = z3.substitute(inz3, (variable, z3.Int(newname)))
        elif variable.sort().kind() == z3.Z3_BV_SORT:
            size = variable.size()
            inz3 = z3.substitute(inz3, (variable, z3.BitVec(newname, size)))
    return inz3

def ctx_solver_simplify(expression_in_z3):
    tactic = z3.Tactic("ctx-solver-simplify")
    result = z3.Repeat(tactic).apply(expression_in_z3).as_expr()
    return result

def all_uninterpreted(f):
    if f.decl().kind() == z3.Z3_OP_UNINTERPRETED:
        return [f]
    else:
        results = []
        for child in f.children():
            results.extend(all_uninterpreted(child))
        return results

def from_bv_to_int_domain(z3from, typestr=None):
    """attempt to convert the-bit-vector expression z3from to the integer domain
    If this expression is a value, you can specify its type."""
    def return_and_log(z3from, result, msg=None):
        logger.info(" ")
        logger.info("---------------------------")
        logger.info("convert_from_bv_to_int_domain on: " + str(z3from.sexpr()))
        logger.info("convert result is " + str(result))
        logger.info("number of arguments at top level: " + str(z3from.num_args()))
        if msg is not None:
            logger.info(msg)
        logger.info("---------------------------------------------------------")
        logger.info(" ")
        return result
    #this is problematic... at times our pattern matching relies on simplification
    #e.g., different forms of extract, at times simplification can make things worse
    #TODO. remove the simplification by handling more patterns.
    z3from = z3.simplify(z3from, push_ite_bv=True)

    if z3from.decl().kind() == z3.Z3_OP_UNINTERPRETED:
        label = z3from.decl().name()
        return return_and_log(z3from, z3.Int(label))

    if not z3.is_expr(z3from):
        return return_and_log(z3from, z3from, "CONVERSION ERROR: not an expression on ")

    if z3from.decl().kind() == z3.Z3_OP_SGEQ:
        (lhs, rhs) = get_lhs_rhs(z3from)
        return return_and_log(z3from, lhs >= rhs)

    if z3from.decl().kind() == z3.Z3_OP_SLEQ:
        (lhs, rhs) = get_lhs_rhs(z3from)
        return return_and_log(z3from, lhs <= rhs)

    if z3from.decl().kind() == z3.Z3_OP_SGT:
        (lhs, rhs) = get_lhs_rhs(z3from)
        return return_and_log(z3from, lhs > rhs)
    
    if z3from.decl().kind() == z3.Z3_OP_SLT:
        (lhs, rhs) = get_lhs_rhs(z3from)
        return return_and_log(z3from, lhs < rhs)

    if z3from.decl().kind() == z3.Z3_OP_BADD and z3from.num_args() == 2:
        (lhs, rhs) = get_lhs_rhs(z3from)
        return return_and_log(z3from, lhs + rhs)

    if z3from.decl().kind() == z3.Z3_OP_BMUL and z3from.num_args() == 2:
        (lhs, rhs) = get_lhs_rhs(z3from)
        return return_and_log(z3from, lhs * rhs)

    if z3from.decl().kind() == z3.Z3_OP_BSUB and z3from.num_args() == 2 :
        (lhs, rhs) = get_lhs_rhs(z3from)
        return return_and_log(z3from, lhs - rhs)

    if z3from.decl().kind() == z3.Z3_OP_BADD and z3from.num_args() > 2:
        converted_children_list = get_children_of(z3from)
        for i in range(len(converted_children_list)):
            if i == 0:
                result = converted_children_list[0]
            else:
                result = result + converted_children_list[i]
        return return_and_log(z3from, result)

    #TODO >2 arguments for BMUL, BSUB, and other operators
    if z3from.decl().kind() == z3.Z3_OP_BNUM:
        if typestr is None:
            #all bitvectors are treated as signed long in the absence of typing
            return return_and_log(z3from, z3from.as_signed_long())
        if typestr == "intle:32" and z3from.size() == 32:
            return bv_value_to_int_value(z3from, typestr)
        if typestr == "intbe:32" and z3from.size() == 32:
            return bv_value_to_int_value(z3from, typestr)
        logger.warning("MORE CODE NEEDED TO HANDLE type " + typestr + "!!!!")
        return return_and_log(z3from, z3from.as_signed_long())
    #for BAR2020, we don't worry about premature simplification
    #if check_special_concat_extract_concat(z3from, typestr):
    if z3from.decl().kind() == z3.Z3_OP_CONCAT:
        #eliminate concat(concat(concat(... ) using simplify
        z3from_simplified = z3.simplify(z3from)
        #if all variables in the concat are the same
        all_are_extract = True
        same_variable = True
        is_bitvec32 = True
        ends_with_concat_of_zero = False
        ends_with_concat_of_zero_size = 0
        bv_variable = None
        last_variable = ""
        concat_extract_list = []
        for i in range(z3from_simplified.num_args()):
            arg = z3from_simplified.arg(i)
            if (z3.is_bv(arg) and arg.decl().kind() == z3.Z3_OP_BNUM and
                i == z3from_simplified.num_args()-1 and arg.as_signed_long() == 0):
                ends_with_concat_of_zero = True
                ends_with_concat_of_zero_size = arg.size()
                continue
            concat_extract_list.append(arg)
            if not arg.decl().kind() == z3.Z3_OP_EXTRACT:
                all_are_extract = False
            else:
                if i == 0:
                    last_variable = arg.arg(0).decl().name()
                    bv_variable = arg.arg(0)
                else:
                    if str(arg.arg(0)) != last_variable:
                        same_variable = False
                if not str(arg.arg(0).sort()) == "BitVec(32)" : #TODO..find const
                    is_bitvec32 = False

        conditions = [all_are_extract, same_variable, is_bitvec32]
        if all(conditions):
            if not ends_with_concat_of_zero:
                if not is_typed_bv_le32(bv_variable):
                    return_and_log(z3from, z3from, "CONVERSION ERROR for " +
  bv_variable.decl().name() + ", at present can only handle types of intle:32")
                if confirm_concat_little_endian_hypothesis(32,concat_extract_list,0):
                    return return_and_log(z3from, z3.Int(last_variable))
                return_and_log(z3from, z3from, "CONVERSION ERROR for " +
  bv_variable.decl().name() + ", could not handle concat due to declared little endian " +
  "but doesn't look like little endian")
            else:
                if not is_typed_bv_le32(bv_variable):
                    return_and_log(z3from, z3from, "CONVERSION ERROR for " +
  bv_variable.decl().name() + " , at present can only handle types of intle:32")
                if confirm_concat_little_endian_hypothesis(32,concat_extract_list,
                                                           ends_with_concat_of_zero_size):
                    constant = int(math.pow(2,ends_with_concat_of_zero_size))
                    return return_and_log(z3from, z3.Int(last_variable) * constant)
                return_and_log(z3from, z3from, "CONVERSION ERROR for " +
  bv_variable.decl().name() + ", could not handle concat due to declared little endian " +
  "but doesn't look like little endian")

        return return_and_log(z3from, z3from, "CONVERSION ERROR for " +
                              str(z3from) + ", could not handle concat")

    if z3from.decl().kind() == z3.Z3_OP_AND:
        #deal with and of booleans and extract
        z3from_simplified = z3.simplify(z3from)
        # we need to pull out things of type Extract(31,24,y_intle:32) == 3
        equality_extracts = []
        other = []
        for i in range(z3from_simplified.num_args()):
            arg = z3from_simplified.arg(i)
            kind = arg.decl().kind()
            if not kind == z3.Z3_OP_EQ:
                other.append(arg)
                continue
            arg1kind = arg.arg(0).decl().kind()
            arg2kind = arg.arg(1).decl().kind()
            if not arg1kind == z3.Z3_OP_EXTRACT and not arg2kind == z3.Z3_OP_EXTRACT:
                other.append(arg)
                continue
            if not arg1kind == z3.Z3_OP_BNUM and not arg2kind == z3.Z3_OP_BNUM:
                other.append(arg)
                continue
            equality_extracts.append(arg)
        #TODO.now partition the extracts for different variables and different sizes,
        #e.g. intle:16, etc. for now, just see if there are exactly four of them 
        if len(equality_extracts) == 0:
            process = []
            for x in other:
                process.append(from_bv_to_int_domain(x))
            return return_and_log(z3from, z3.And(*process),
                                  "via process and without equality extracts")
        if len(equality_extracts) == 4:
            #in z3, it is just a bit vector with extracts
            xbytes = [0,0,0,0]
            for i in range(len(equality_extracts)):
                ee = equality_extracts[i]
                extract_arg = ee.arg(0)
                number_arg = ee.arg(1)
                #TODO...handle arg1 is the number
                if not extract_arg.decl().kind() == z3.Z3_OP_EXTRACT:
                    return return_and_log(z3from, z3from, "TROUBLE 1")
                if not number_arg.decl().kind() == z3.Z3_OP_BNUM:
                    return return_and_log(z3from, z3from, "TROUBLE 1b")
                partial_number = number_arg.as_long()
                #todo..what if the extract is not on a variable at all????
                if i == 0:
                    last_variable = extract_arg.arg(0).decl().name()
                elif not last_variable == extract_arg.arg(0).decl().name():
                    return return_and_log(z3from, z3from, "EXTRACT VARIABLES ARE DIFFERENT")
                start = extract_arg.params()[0]
                stop = extract_arg.params()[1]
                if start < stop or stop + 7 != start:
                    return return_and_log(z3from, z3from, "TROUBLE3" + " start: " +
                                          str(start) + " stop: " + str(stop))
                if stop == 0 or stop == 8 or stop == 16 or stop == 24:
                    xbytes[int(stop/8)] = partial_number
                else:
                    return return_and_log(z3from, z3from, "TROUBLE 4")
            n = bitstring.pack('uint:8, uint:8, uint:8, uint:8',
                               xbytes[3], xbytes[2], xbytes[1], xbytes[0])
            #AGAIN NOTE SPECIAL TREATMENT AS INTLE
            extract_equality = z3.Int(last_variable) == n.intle
        else:
            return return_and_log(z3from, z3from, "extract equality on " +
                                  str(len(equality_extracts)) + " more needed")
        if len(other) > 0:
            #should be easy to fix
            return return_and_log(z3from,z3from, "FIX THE other booleans plus extract")
        return return_and_log(z3from, extract_equality)

    if z3from.decl().kind() == z3.Z3_OP_OR:
        #at present, no special checks for or
        orme = []
        for child in z3from.children():
            child_converted = from_bv_to_int_domain(child)
            orme.append(child_converted)
        result = z3.Or(orme)
        return return_and_log(z3from, result)

    if z3from.decl().kind() == z3.Z3_OP_NOT:
        child = from_bv_to_int_domain(z3from.children()[0])
        return return_and_log(z3from, z3.Not(child))

    if z3from.decl().kind() == z3.Z3_OP_EQ:
        if all_args_bitvectors(z3from):
            #special check for single bit extract
            if sign_check(z3from):
                answer = evaluate_sign_check(z3from)
                return return_and_log(z3from, answer)
            #else it is nothing special
            if sign_check_with_ite(z3from):
                answer = evaluate_sign_check_with_ite(z3from)
                return return_and_log(z3from, answer)
            (lhs, rhs) = get_lhs_rhs(z3from)
            return return_and_log(z3from, lhs == rhs)
        
        return return_and_log(z3from, z3.And(*z3from.children()),
                                  "-----AVOIDED sign check, explore further")
    if z3from.decl().kind() == z3.Z3_OP_ITE:
        ite = []
        for child in z3from.children():
            child_converted = from_bv_to_int_domain(child)
            ite.append(child_converted)
        result = z3.If(ite[0],ite[1],ite[2])
        return return_and_log(z3from, result)
    if z3.is_bv(z3from):
        msg = ("CONVERSION ERROR!  No conversion options found for kind: " +
        str(z3from.decl().kind()) + " attempting to convert: " + str(z3from))
    else:
        msg = "did not pass any check"
    return return_and_log(z3from,z3from, msg)

def all_args_bitvectors(z3from):
    isargbv = [ z3.is_bv(x) for x in z3from.children()]
    return all(isargbv)

def same_value_single_variable(v1, v2_with_same_variable_as_v1):
    vv1 = list(set(all_uninterpreted(v1)))
    assert len(vv1) == 1
    same_as_vv1_check = list(set(all_uninterpreted(v2_with_same_variable_as_v1)))
    assert len(same_as_vv1_check) == 1
    assert (vv1[0].decl().name() == same_as_vv1_check[0].decl().name())
    vv1 = vv1[0]
    if vv1.sort().kind() == z3.Z3_INT_SORT:
        vv2 = z3.Int(vv1.decl().name() + vv1.decl().name())
    elif vv1.sort().kind() == z3.Z3_BV_SORT:
        vv2 = z3.BitVec(vv1.decl().name() + vv1.decl().name(), vv1.size())
    v2 = z3.substitute(v2_with_same_variable_as_v1, (vv1, vv2))
    #we now have v1 and v2, with v2 using a different variable name.
    solver = z3.Solver()
    solver.add(vv1 == vv2)
    solver.add(z3.Not(v1 == v2))
    if solver.check() == z3.unsat:
        return True
    return False

def single_variable_bit_vector_domain_equals_integer_domain(i_variable, bv_variable,
    variable_relationship, i_value, bv_value, value_relationship, i_condition,
    bv_condition, bv_type=None):
    """check if a value and condition for a single bit vector variable is equivalent 
    to a value and condition in the integer domain.  If they are equivalent, 
    return (True, True) if unable to determine if they are equivalent, return (False, False)
    if able to determine they are not equivalent, return (False, <model>) where model 
    is an example where the two domains differ.  You can use the model's eval function to 
    examine your two variables, possibly using "sexpr" on the eval to see it in hex.
       #bv_value must be expressed as a constraint
    """
    try:
        solver = z3.Solver()
        solver.add(z3.simplify(variable_relationship))
        if not i_condition is True:
            solver.add(z3.simplify(i_condition))
        if not bv_condition is True:
            solver.add(z3.simplify(bv_condition))
        solver.add(z3.simplify(z3.Not(value_relationship)))
        solver.set("timeout",1000 * 10) #10 seconds
        check = solver.check()
        if check == z3.sat:
            model = solver.model()
            eval_i_variable = model.eval(i_variable)
            eval_bv_variable = model.eval(bv_variable)
            v1 = z3.simplify(z3.substitute(i_value, (i_variable, eval_i_variable)))
            v2 = z3.simplify(z3.substitute(bv_value, (bv_variable, eval_bv_variable)))
            try:
                as_sexpr = eval_bv_variable.sexpr()
                if bv_type == 'intle:32' and eval_i_variable.is_int():
                    eval_int = eval_i_variable.as_long()
                    f = [x for x in bitstring.BitArray(uint=eval_int, length=32).cut(8)]
                    int32le_value = bitstring.pack('int:8, int:8, int:8, int:8',
                                            f[3].int, f[2].int, f[1].int, f[0].int).intle
                    as_sexpr = as_sexpr + " e.g., " + str(int32le_value) + " intle:32"
            except Exception as ex:
                logger.info("could net get sexpr for type " + str(type(eval_bv_variable)))
                as_sexpr = None
            explanation = (
                "Not a precise conversion.  E.g., when " + str(i_variable) + " is " +
                str(eval_i_variable) + "(" + as_sexpr + ") the values differ, e.g., " +
                str(v1) + " vs. " + str(v2) #+ extra
            )
            return (False, model, explanation)
        if check == z3.unsat:
            return (True, True, "same domain")
        return (False, False, "unable to determine due to solver timeout")
    except Exception as ex:
        logger.info("Unclear due to exception: " + str(ex))
        return (False, False, "unable to determine")

def same_constraint_single_variable(c1, c2_with_same_variable_as_c1):
    vc1 = list(set(all_uninterpreted(c1)))
    assert len(vc1) == 1
    same_as_vc1_check = list(set(all_uninterpreted(c2_with_same_variable_as_c1)))
    assert len(same_as_vc1_check) == 1
    assert vc1[0].decl().name() == same_as_vc1_check[0].decl().name()
    vc1 = vc1[0]
    if vc1.sort().kind() == z3.Z3_INT_SORT:
        vc2 = z3.Int(vc1.decl().name() + vc1.decl().name())
    elif vc1.sort().kind() == z3.Z3_BV_SORT:
        vc2 = z3.BitVec(vc1.decl().name() + vc1.decl().name(), vc1.size())
    c2 = z3.substitute(c2_with_same_variable_as_c1, (vc1, vc2)) 
    #we now have c1 and c2, with c2 using a different variable name.
    solver = z3.Solver()
    solver.add(vc1 == vc2)
    solver.add(z3.Or(z3.And(c1, z3.Not(c2)), z3.And(z3.Not(c1), c2)))
    if solver.check() == z3.unsat:
        return True
    return False

def sign_check(z3from):
    (z3from_ex, z3from_num) = resolve_two_children(z3from, z3.Z3_OP_EXTRACT, z3.Z3_OP_BNUM)
    if z3from_ex is None or z3from_num is None:
        return False
    #ensure a single bit extract
    if z3from_ex.params()[0] != z3from_ex.params()[1]:
        return False
    #ensure the number is 0 or 1
    if z3from_num.as_long() < 0 or z3from_num.as_long() > 1:
        return False
    #ensure it is sign-bit extract
    if z3from_ex.children()[0].size() != z3from_ex.params()[0] + 1:
        return False
    return True

def evaluate_sign_check(z3from):
    (z3from_ex, z3from_num) = resolve_two_children(z3from, z3.Z3_OP_EXTRACT, z3.Z3_OP_BNUM)
    thing_extracted = z3from_ex.arg(0)
    #TODO..more checks needed for when sign bit is checked not for the entire extract
    if thing_extracted.decl().kind() == z3.Z3_OP_UNINTERPRETED:
        #TODO  probably need a check on LE32 here
        variable = thing_extracted.decl().name()
        z3from_int = z3.Int(variable)
    else:
        z3from_int = from_bv_to_int_domain(thing_extracted)
    if z3from_num.as_long() == 0:
        return z3from_int >= 0
    return z3from_int < 0

def get_lhs_rhs(z3from):
    """this will need to generalize, for 3 children, etc."""
    lh = z3from.children()[0]
    rh = z3from.children()[1]
    lhs = from_bv_to_int_domain(lh)
    rhs = from_bv_to_int_domain(rh)
    if not compatible_kinds(lhs,rhs):
        logger.warning("Could not convert both sides from bit-vector to int")
        logger.warning(str(lh) + str(lhs) + str(rh) + str(rhs))
        return (lh, rh)
    return (lhs, rhs)

def resolve_two_children(z3from, kinda, kindb):
    lh = z3from.children()[0]
    rh = z3from.children()[1]
    if lh.decl().kind() == kinda and rh.decl().kind() == kindb:
        return (lh, rh)
    if lh.decl().kind() == kindb and rh.decl().kind() == kinda:
        return (rh, lh)
    return None, None

def sign_check_with_ite(z3from):
    #instead of == 0 or == 1 we have == if(condition, 0, 1) or if(condition, 1, 0)
    (z3from_ex, z3from_ite) = resolve_two_children(z3from, z3.Z3_OP_EXTRACT, z3.Z3_OP_ITE)
    if z3from_ex is None or z3from_ite is None:
        return False
    #ensure the ite is 0, 1
    a = z3from_ite.arg(1)
    b = z3from_ite.arg(2)
    if not ((a == 0 and b == 1) or (a == 1 and b == 0)):
        return False
    #ensure a single bit extract
    if z3from_ex.params()[0] != z3from_ex.params()[1]:
        return False
    #ensure it is sign-bit extract
    if z3from_ex.children()[0].size() != z3from_ex.params()[0] + 1:
        return False
    return True

def compatible_kinds(lhs, rhs):
    return (z3.is_bv(lhs) and z3.is_bv(rhs)) or (not z3.is_bv(lhs) and not z3.is_bv(rhs))

def evaluate_sign_check_with_ite(z3from):
    (z3from_ex, z3from_ite) = resolve_two_children(z3from, z3.Z3_OP_EXTRACT, z3.Z3_OP_ITE)
    #TODO:  need check for bit being extracted is sign bit!!!!!!!
    thing_extracted = z3from_ex.arg(0)
    z3from_int = from_bv_to_int_domain(thing_extracted)
    a = z3from_ite.arg(1)
    c = from_bv_to_int_domain(z3from_ite.arg(0))
    cond = z3.simplify(c)
    if a == 0:
        return z3.Or(z3.And(z3from_int >= 0, cond), z3.And(z3from_int < 0, z3.Not(cond)))
    return z3.Or(z3.And(z3from_int < 0, cond), z3.And(z3from_int >= 0, z3.Not(cond)))

def replace_bv_sequences_with_conjectures(z3from, prefix):
    """ Returns a modified z3 expression substituting conjectures in place of sequences"""
    concat_sequences = find_symbolic_byte_concat_sequences(z3from, prefix)
    also = find_symbolic_variables_in_numerical_expressions(z3from)
    #the idea here is that any concat sequence of length 4 will be replaced with
    #an integer conjecture... if the variables in that integer conjecture are also
    #involved in numerical expressions, we strengthen the conjecture
    modified_z3 = z3from
    for s in concat_sequences:
        if abs(s[1]-s[0]) + 1 == 4:
            if all_in_sequence_in_set(s, also, prefix):
                conjecture_label = "?"
            else:
                conjecture_label = "??"
            if s[0] < s[1]:
                #it is a sequence like sym_0, sym_1, sym_2, sym_3
                s0 = z3.BitVec(prefix + str(s[0]), 8)
                s1 = z3.BitVec(prefix + str(s[0]+1), 8)
                s2 = z3.BitVec(prefix + str(s[0]+2), 8)
                s3 = z3.BitVec(prefix + str(s[0]+3), 8)
                s32 = z3.BitVec(prefix+"[" + str(s[0]) + "-" + str(s[1]) + "]-" +
                                conjecture_label + "_intbe:32", 32)
                modified_z3 = z3.substitute(modified_z3, (s0, z3.Extract(31, 24, s32)))
                modified_z3 = z3.substitute(modified_z3, (s1, z3.Extract(23, 16, s32)))
                modified_z3 = z3.substitute(modified_z3, (s2, z3.Extract(15, 8, s32)))
                modified_z3 = z3.substitute(modified_z3, (s3, z3.Extract(7, 0, s32)))
            else:
                # it is a sequence like sym_3, sym_2, sym_1, sym_0
                s3 = z3.BitVec(prefix + str(s[0]), 8)
                s2 = z3.BitVec(prefix + str(s[0] - 1), 8)
                s1 = z3.BitVec(prefix + str(s[0] - 2), 8)
                s0 = z3.BitVec(prefix + str(s[0] - 3), 8)
                s32 = z3.BitVec(prefix + "[" + str(s[1]) + "-" + str(s[0]) + "]-" +
                                conjecture_label + "_intle:32", 32)
                modified_z3 = z3.substitute(modified_z3, (s0, z3.Extract(31, 24, s32)))
                modified_z3 = z3.substitute(modified_z3, (s1, z3.Extract(23, 16, s32)))
                modified_z3 = z3.substitute(modified_z3, (s2, z3.Extract(15, 8, s32)))
                modified_z3 = z3.substitute(modified_z3, (s3, z3.Extract(7, 0, s32)))
            #more type conjectures needed for different types and sizes
    return modified_z3

def bv_extract_indices_consistent_with_little_endian(byte_index, extract_from,
                                                     extract_to, missing_bits):
    """
    Essentially given a little endian number of given size, we expect a certain specific 
    extract value for each byte in the number.  This checks for each byte.  
    Note that missing_bits makes this a lot more complicated,
    especially if it means we are missing entire bytes.
    example, missing 1 bit size 32
    (6,0) (15, 8), (23,16), (31,24)
    example, missing 10 bits size 32
    (13, 8), (23,16), (31,24)
    """
    missing_bytes = int(missing_bits / 8)
    missing_bits_in_byte = missing_bits % 8
    multiplier = byte_index + 1 + missing_bytes
    expected_extract_to = (multiplier-1)*8
    if byte_index > 0:
        expected_extract_from = multiplier*8 -1
    else:
        expected_extract_from = multiplier*8 - 1 - missing_bits_in_byte
    return extract_from == expected_extract_from and extract_to == expected_extract_to


def confirm_concat_little_endian_hypothesis(size, concat_extract_list, missing_bits):
    missing_bytes = int(missing_bits / 8)
    if not int(size/8) - missing_bytes == len(concat_extract_list):
        return False
    for index in range(len(concat_extract_list)):
        if not bv_extract_indices_consistent_with_little_endian(index,
          concat_extract_list[index].params()[0], concat_extract_list[index].params()[1],
          missing_bits):
            return False
    return True

def find_all_symbolic_variables(z3from):
    results = set()
    if not z3from.decl().kind() == z3.Z3_OP_UNINTERPRETED:
        children = z3from.children()
        for child in children:
            found_in_child = find_all_symbolic_variables(child)
            results = results.union(found_in_child)
        #TODO... consider args and parameters both, so this is not complete
    else:
        results.add(z3from)
    return results

def kind_is_numerical(kind):
    numerical = [
        z3.Z3_OP_LE,
        z3.Z3_OP_GE,
        z3.Z3_OP_LT,
        z3.Z3_OP_GT,
        z3.Z3_OP_ADD,
        z3.Z3_OP_SUB,
        z3.Z3_OP_UMINUS,
        z3.Z3_OP_MUL,
        z3.Z3_OP_DIV,
        z3.Z3_OP_IDIV,
        z3.Z3_OP_REM,
        z3.Z3_OP_MOD,
        z3.Z3_OP_BNEG,
        z3.Z3_OP_BADD,
        z3.Z3_OP_BSUB,
        z3.Z3_OP_BMUL,
        z3.Z3_OP_BSDIV,
        z3.Z3_OP_BUDIV,
        z3.Z3_OP_BSREM,
        z3.Z3_OP_BUREM,
        z3.Z3_OP_BSMOD,
        z3.Z3_OP_BSDIV0,
        z3.Z3_OP_BUDIV0,
        z3.Z3_OP_BSREM0,
        z3.Z3_OP_BUREM0,
        z3.Z3_OP_BSMOD0,
        z3.Z3_OP_ULEQ,
        z3.Z3_OP_SLEQ,
        z3.Z3_OP_UGEQ,
        z3.Z3_OP_SGEQ,
        z3.Z3_OP_ULT,
        z3.Z3_OP_SLT,
        z3.Z3_OP_UGT,
        z3.Z3_OP_SGT]
    return kind in numerical

def find_symbolic_variables_in_numerical_expressions(z3from):
    # find any symbolic variables that appear in numerical expressions.
    results = set()
    kind = z3from.decl().kind()
    if not (kind == z3.Z3_OP_UNINTERPRETED):
        if kind_is_numerical(kind):
            results = results.union(find_all_symbolic_variables(z3from))
        else:
            children = z3from.children()
            for child in children:
                found_in_child = find_symbolic_variables_in_numerical_expressions(child)
                results = results.union(found_in_child)
            #TODO... misses arguments that are not children.
    return results

def find_symbolic_byte_concat_sequences(z3from, prefix):
    """Given a constraint and a variable prefix like "sym_", return a list of concat 
    sequences. For example, if we find Concat(sym_0, sym_1, sym_2) and 
    Concat(sym_12,sym_11,sym_10,sym_9) we return [ (0,2), (12,9) ]"""
    # TODO.. currently relies on simplify expanding
    # Concat(Concat(Concat(sym_0, sym_1), sym_2), sym_3) to
    # Concat(sym_0, sym_1, sym_2, sym_3)
    results = []
    if not (z3from.decl().kind() == z3.Z3_OP_CONCAT):
        children = z3from.children()
        for child in children:
            found_in_child = find_symbolic_byte_concat_sequences(child, prefix)
            results.extend(found_in_child)
        return results
    #now handle the concat.
    start = None
    stop = None
    for i in range(z3from.num_args()):
        arg = z3from.arg(i)
        #if other things are present in the concat sequence, we don't worry about that...
        #e.g., numbers could be there, or things can get ugly like we saw with addition.
        if arg.decl().kind() == z3.Z3_OP_UNINTERPRETED and z3.is_bv(arg) and arg.size() == 8:
            label = arg.decl().name()
            if label.startswith(prefix):
                number = int(label[len(prefix):])
                if start is None:
                    start = number
                else:
                    if stop == None or number == stop + 1 or number == stop - 1:
                        stop = number
                    else:
                        logger.warning("found another symbolic but not in sequence..." +
                                       "not certain how to handle")
                        break
        elif not arg.decl().kind() == z3.Z3_OP_BNUM:
            children = arg.children()
            for child in children:
                found_in_child = find_symbolic_byte_concat_sequences(child, prefix)
                results.extend(found_in_child)
    if not start == None and not stop == None:
        results.extend([(start,stop)])
    return results

def all_in_sequence_in_set(sequence_pair, checkset, prefix):
    """ Given a prefix like 'sym_' and a sequence pair like (0,3) check to see 
    if every variable constructed from the prefix
    and the sequence pair is in the checkset which is a list of z3 variables"""
    low = min(sequence_pair[1], sequence_pair[0])
    high = max(sequence_pair[1], sequence_pair[0])
    checklabels = [v.decl().name() for v in checkset ]
    for number in range(low, high + 1):
        label = prefix + str(number)
        if not label in checklabels:
            return False
    return True
