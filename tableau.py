ALLOWED_PROP_LETTERS = ["p", "q", "r", "s"]
ALLOWED_FOL_PREDICATES = ["P", "Q", "R", "S"]
ALLOWED_FOL_VARIABLES = ["x", "y", "z", "w"]
ALLOWED_FOL_CONSTANTS = ["a", "b", "c", "d", "e", "f", "g", "h", "i", "j"]
ALLOWED_CONNECTIVES = ["=>", "\/", "/\\"]
result = []
BINARY_DICT = {}
FORMULA_TYPE = {}
MAX_CONSTANTS = 10

def parse_prop(fmla):
    global result
    if len(fmla) == 1 and fmla in ALLOWED_PROP_LETTERS:
        result.append([0])
        return result[0]
    if fmla.startswith('~'):
        result.append([1])
        return parse_prop(fmla[1:])
    if fmla.startswith('(') and fmla.endswith(')'):
        index = findmainConnective(fmla)
        result.append([fmla[1: index], fmla[index: index+2], fmla[index+2: -1]])
        if index == -1:
            return None
        return parse_prop(fmla[1: index]) and parse_prop(fmla[index+2: -1])
    return None

def parse_fol(fmla, formula = True):
    global result
    if len(fmla) == 6 and fmla[0] in ALLOWED_FOL_PREDICATES and fmla[1] == "(" and fmla[3] == "," and fmla[5] == ")":
        if formula:
            if fmla[2] in ALLOWED_FOL_VARIABLES and fmla[4] in ALLOWED_FOL_VARIABLES:
                result.append([0])
                return result[0]
        else:
            result.append([0])
            return result[0]
    if fmla.startswith('~'):
        result.append([1])
        if formula:
            return parse_fol(fmla[1:])
        return parse_fol(fmla[1:], False)
    if fmla.startswith("E") and fmla[1] in ALLOWED_FOL_VARIABLES:
        result.append([2])
        if formula:
            return parse_fol(fmla[2:])
        return parse_fol(fmla[2:], False)
    if fmla.startswith("A") and fmla[1] in ALLOWED_FOL_VARIABLES:
        result.append([3])
        if formula:
            return parse_fol(fmla[2:])
        return parse_fol(fmla[2:], False)
    if fmla.startswith('(') and fmla.endswith(')'):
        index = findmainConnective(fmla)
        result.append([fmla[1: index], fmla[index: index+2], fmla[index+2: -1]])
        if index == -1:
            return None
        if formula:
            return parse_fol(fmla[1: index]) and parse_fol(fmla[index+2: -1])
        return parse_fol(fmla[1: index], False) and parse_fol(fmla[index+2: -1], False)
    return None

def findmainConnective(fmla):
    count = 0
    for i in range(len(fmla) - 2):
        if fmla[i] == "(":
            count += 1
        if fmla[i] == ")":
            count -= 1
        if count == 1 and fmla[i: i+2] in ALLOWED_CONNECTIVES:
            return i
    return -1

def parse(fmla):
    global result, parseOutputs, BINARY_DICT, FORMULA_TYPE
    prop_result = parse_prop(fmla)
    result = []
    fol_result = parse_fol(fmla)
    result = []
    if prop_result:
        FORMULA_TYPE[fmla] = 0
        if prop_result[0] == 0:
            return 6
        elif prop_result[0] == 1:
            return 7
        else:
            BINARY_DICT[fmla] = [prop_result[0], prop_result[1], prop_result[2]]
            return 8
    elif fol_result:
        FORMULA_TYPE[fmla] = 1
        if fol_result[0] == 0:
            return 1
        elif fol_result[0] == 1:
            return 2
        elif fol_result[0] == 2:
            return 4
        elif fol_result[0] == 3:
            return 3
        else:
            BINARY_DICT[fmla] = [fol_result[0], fol_result[1], fol_result[2]]
            return 5
    else:
        return 0
 
def satisfiable_prop(tableau):
    global result
    while len(tableau) > 0:
        theory = tableau.pop(0)
        if finished_prop(theory) and contradiction_prop(theory):
            return True
        else:
            for fmla in theory:
                if not is_literal_prop(fmla):
                    category, elements = alpha_or_beta(fmla)
                    result = []
                    theory.remove(fmla)
                    #alpha
                    if category == 0:
                        for element in elements:
                            theory.add(element)
                        if contradiction_prop(theory) and not theory in tableau:
                            tableau.append(theory)
                    #beta
                    else:
                        theory_1 = theory.copy()
                        theory_1.add(elements[0])
                        theory_2 = theory.copy()
                        theory_2.add(elements[1])
                        if contradiction_prop(theory_1) and not theory_1 in tableau:
                            tableau.append(theory_1)
                        if contradiction_prop(theory_2) and not theory_2 in tableau:
                            tableau.append(theory_2)
                    break
    return False 

def alpha_or_beta(fmla, neg = False):
    global result
    result = []
    parsing_result = parse_prop(fmla)
    if not parsing_result:
        return None
    if parsing_result[0] == 0:  
        return 0, [fmla]  
    if parsing_result[0] == 1:  
        result = []
        return alpha_or_beta(fmla[1:], not neg)  
    else:  
        left, connective, right = parsing_result[0], parsing_result[1], parsing_result[2]
        if connective == "/\\":
            if neg:
                return 1, ['~' + left, '~' + right]  
            return 0, [left, right]  
        elif connective == "\/":
            if neg:
                return 0, ['~' + left, '~' + right]  
            return 1, [left, right] 
        elif connective == "=>":
            if neg:
                return 0, [left, '~' + right]  
            return 1, ['~' + left, right]  

def is_literal_prop(fmla):
    return len(fmla) == 1 or len(fmla) == 2

def finished_prop(fmlas):
    for fmla in fmlas:
        if not is_literal_prop(fmla):
            return False
    return True

def contradiction_prop(fmlas):
    positives = []
    negatives = []
    for fmla in fmlas:
        if is_literal_prop(fmla):
            if len(fmla) == 1 and not fmla in negatives:
                positives.append(fmla)
            elif len(fmla) == 2 and not fmla[-1] in positives:
                negatives.append(fmla[-1])
            else:
                return False
    return True

def satisfiable_fol(tableau):
    global result
    constants_num = 0
    while len(tableau) > 0:
        theory = tableau.pop(0)
        if contradiction_fol(theory[0]) and finished_fol(theory[0], theory[1], constants_num):
            return 1    
        else:
            for fmla in theory[0]:
                if not is_literal_fol(fmla):
                    category, elements = alpha_beta_delta_gamma(fmla)
                    result = []
                    theory[0].remove(fmla)
                    #alpha
                    if category == 0:
                        for element in elements:
                            if not element in theory[0]:
                                theory[0].insert(0, element)
                        
                        if contradiction_fol(theory[0]) and not theory in tableau:
                            tableau.append(theory)
                    #beta
                    elif category == 1:
                        theory_1 = [theory[0].copy(), theory[1].copy()]
                        theory_2 = [theory[0].copy(), theory[1].copy()]
                
                        if not elements[0] in theory_1[0]:
                            theory_1[0].insert(0, elements[0])
                        
                        if not elements[1] in theory_2[0]:
                            theory_2[0].insert(0, elements[1])

                        if contradiction_fol(theory_1[0]) and not theory_1 in tableau:
                            tableau.append(theory_1)
                        if contradiction_fol(theory_2[0]) and not theory_2 in tableau:
                            tableau.append(theory_2)
                    #delta
                    elif category == 2:
                        if constants_num > 9:
                            return 2
                        new_constant = ALLOWED_FOL_CONSTANTS[constants_num]
                        constants_num += 1
                        substitute = substitute_fol(elements[0], new_constant)
                        if not substitute in theory[0]:
                            theory[0].insert(0, substitute)
                        if contradiction_fol(theory[0]) and not theory in tableau:
                            tableau.append(theory)
                    else:
                        theory[0].append(fmla)
                        closed_term_index = 0
                        if closed_term_index >= constants_num:
                            tableau.append(theory)
                            continue
                        if fmla in theory[1].keys():
                            closed_term_index =  theory[1][fmla]
                            if closed_term_index >= constants_num:
                                tableau.append(theory)
                                continue
                            theory[1][fmla] = closed_term_index + 1
                        else:
                            theory[1][fmla] = 1
                        substitute = substitute_fol(elements[0], ALLOWED_FOL_CONSTANTS[closed_term_index])
                        
                        if not substitute in theory[0]:
                            theory[0].insert(0, substitute)
                        if contradiction_fol(theory[0]) and not theory in tableau:
                            tableau.append(theory)
                    break
    return 0

def is_literal_fol(fmla):
    return len(fmla) == 6 or len(fmla) == 7

def finished_fol(fmlas, dic, n):
    for fmla in fmlas:
        if not is_literal_fol(fmla):
            if not isGamma(fmla):
                return False
            else:
                if dic == {}:
                    return False
                if fmla not in dic.keys():
                    return False
                if dic[fmla] != n:
                    return False
    return True

def isGamma(fmla):
    global result
    type, _ = alpha_beta_delta_gamma(fmla)
    result = []
    if type == 3:
        return True
    return False

def contradiction_fol(fmlas):
    positives = []
    negatives = []
    for fmla in fmlas:
        if is_literal_fol(fmla):
            if len(fmla) == 6 and not fmla in negatives:
                positives.append(fmla)
            elif len(fmla) == 7 and not fmla[1:] in positives:
                negatives.append(fmla[1:])
            else:
                return False
    return True

def is_balanced(fmla):
    count = 0
    for char in fmla:
        if char == "(":
            count += 1
        elif char == ")":
            count -= 1
        if count < 0:
            return False
    return count == 0

def alpha_beta_delta_gamma(fmla, neg = False):
    global result
    result = []
    parsing_result = parse_fol(fmla, False)
    if not parsing_result:
        return None
    if parsing_result[0] == 0:
        return 0, [fmla]
    if parsing_result[0] == 1:
        result = []
        if fmla[1:3] == "Ex":
            return 3, [fmla]
        if fmla[1:3] == "Ax":
            return 2, [fmla]
        return alpha_beta_delta_gamma(fmla[1:], not neg)
    if parsing_result[0] == 2:
        return 2, [fmla]
    if parsing_result[0] == 3:
        return 3, [fmla]
    if parsing_result[0] not in [0, 1, 2, 3]:
        left, connective, right = parsing_result[0], parsing_result[1], parsing_result[2]
        if connective == "/\\":
            if neg:
                return 1, ['~' + left, '~' + right]
            return 0, [left, right]
        elif connective == "\/":
            if neg:
                return 0, ['~' + left, '~' + right]
            return 1, [left, right]
        elif connective == "=>":
            if neg:
                return 0, [left, '~' + right]
            return 1, ['~' + left, right]

def substitute_fol(fmla, constant):
    if not fmla:
        return None
    hasNegation = False
    if fmla[0] == "~":
        variable = fmla[2]
        hasNegation = True
    elif fmla[0] in "AE":
        variable = fmla[1]
    else:
        return fmla
    firstBracketIndex = fmla.find("(")
    firstIndex = firstBracketIndex - 1 if fmla[firstBracketIndex - 1] in ALLOWED_FOL_PREDICATES else firstBracketIndex
    first = fmla[:firstIndex]
    second = fmla[firstIndex:]
    if first.count(variable) > 1:
        return "~" + fmla[3:] if hasNegation else fmla[2:]
    result1 = "~" + first[3:] if hasNegation else first[2:]
    result2 = ""
    i = 0
    while i <= len(second) - 1:
        if second[i] not in "AE" and second[i] == variable:
            result2 += constant
            i += 1
        elif second[i] in "AE":
            for j in range(len(second) - 1, i, -1):
                if is_balanced(second[i: j]):
                    result2 += second[i: j]
                    i = j
                    break
        else:
            result2 += second[i]
            i += 1
    resultAll = result1 + result2
    return resultAll

def lhs(fmla):
    return BINARY_DICT[fmla][0]

def con(fmla):
    return BINARY_DICT[fmla][1]

def rhs(fmla):
    return BINARY_DICT[fmla][2]

def theory(fmla):
    global FORMULA_TYPE
    if FORMULA_TYPE[fmla] == 0:
        return {fmla}
    return [[fmla], {}]

def sat(tableau):
    global result
    result = []
    if isinstance(tableau[0], set):
        return satisfiable_prop(tableau)
    else:
        return satisfiable_fol(tableau)

#DO NOT MODIFY THE CODE BELOW
f = open('input.txt')

parseOutputs = ['not a formula',
                'an atom',
                'a negation of a first order logic formula',
                'a universally quantified formula',
                'an existentially quantified formula',
                'a binary connective first order formula',
                'a proposition',
                'a negation of a propositional formula',
                'a binary connective propositional formula']

satOutput = ['is not satisfiable', 'is satisfiable', 'may or may not be satisfiable']


firstline = f.readline()

PARSE = False
if 'PARSE' in firstline:
    PARSE = True

SAT = False
if 'SAT' in firstline:
    SAT = True

for line in f:
    if line[-1] == '\n':
        line = line[:-1]
    parsed = parse(line)

    if PARSE:
        output = "%s is %s." % (line, parseOutputs[parsed])
        if parsed in [5,8]:
            output += " Its left hand side is %s, its connective is %s, and its right hand side is %s." % (lhs(line), con(line) ,rhs(line))
        print(output)

    if SAT:
        if parsed:
            tableau = [theory(line)]
            print('%s %s.' % (line, satOutput[sat(tableau)]))
        else:
            print('%s is not a formula.' % line)
