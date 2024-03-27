def eliminate_implication(expression):
    quantifiers = ""
    new_exp = ""
    
    skip_next = False #flag to skip the next character after '∀' or '∃'
    
    for char in range(len(expression)):
        if skip_next:
            skip_next = False
            continue

        if expression[char] == '∀' or expression[char] == '∃':
            quantifiers += expression[char] + expression[char + 1]
            skip_next = True
        else:
            new_exp += expression[char]

    x =""
    i = 0
    while i < len(quantifiers) and quantifiers[i] == expression[i]:
        i += 1

    if i < len(quantifiers):
        x = quantifiers[i:]
        quantifiers = quantifiers[:i]

    #split the expression by '->'
    parts = new_exp.split('->')

    #if there is no -> in the expression, return the expression as it is
    if len(parts) == 1:
        return expression

    p = parts[0].strip()  #left-hand side of '->'
    q = parts[1].strip()  #right-hand side of '->' 

    return quantifiers + "(~" + p + ") ∨ " + x + "(" + q + ")"

def move_negation(expression):
    def apply_demorgan(expression):
        c = ''
        for char in range(len(expression)):
            if expression[char] == '∧':
                c += '∧'
            elif expression[char] == '∨':
                c += '∨'

        parts = expression[2:].split(c) 
        if c == '∧':
            return '~' + parts[0].strip() + ' ∨ ~'+ parts[1].strip() + ' '
        else:
            return '~' + parts[0].strip() + ' ∧ ~'+ parts[1].strip() + ' '
    
    count = 0
    new_exp = ""

    while count < len(expression):
        if expression[count:count+2] == '~(': #first occurrence of '~('
            start = count
            count += 1 
            balance = 1  #track of parentheses balance
            while count < len(expression):
                if expression[count] == '(':
                    balance += 1
                elif expression[count] == ')':
                    balance -= 1
                    if balance == 0: #found the matching closing parenthesis
                        new_exp += apply_demorgan(expression[start:count+1])
                        count += 1
                        break
                count += 1
        else:
            new_exp += expression[count]
        count += 1

    return new_exp
    
def remove_double_not(expression):
    new_exp = ""
    char = 0
    while char < len(expression):
        if expression[char] == '~' and expression[char + 1] == '~':
            char += 2  #skip both '~' characters
        else:
            new_exp += expression[char]
            char += 1
    return new_exp

def standardize_variables(expression):
    
    def next_letter(letter): 
        next_char = chr((ord(letter.lower()) - ord('a') + 1) % 26 + ord('a'))
        return next_char
    
    vars = []
    var = ""
    x = 0
    new_exp = ""
    index = 0
    while index < len(expression):
        char = expression[index]
        if char in {'∀', '∃'}:
            var = expression[index + 1]
            for i in range(len(expression[index + 2:])):
                if expression[i] == var:
                    x = i + index + 2
                    break
            for v, idx in vars:
                if v == var:
                    var = next_letter(var)
                    break

            vars.append((var, index + 1))
            new_exp += char + var
            index += 2  #skip the next character after '∀' or '∃'
        
        else:
            new_exp += char
            index += 1
    

    for i in range(len(new_exp)):
        if i == x:
            new_exp = new_exp[:i+1] + var + new_exp[i+2:] 
            break

    return new_exp
    
def prenex_form(expression):
    new_exp = ""
    quantifiers = ""
    skip_next = False

    for char in range(len(expression)):
        if skip_next:
            skip_next = False
            continue

        if expression[char] == '∀' or expression[char] == '∃':
            quantifiers += expression[char] + expression[char + 1]
            skip_next = True
        else:
            new_exp += expression[char]

    return quantifiers + new_exp

def eliminate_universal_quantifiers(expression):
    new_exp = ""
    skip_next = False

    for char in range(len(expression)):
        if skip_next:
            skip_next = False
            continue

        if expression[char] == '∀':
            skip_next = True
        else:
            new_exp += expression[char]

    return new_exp


def transform_expression(expression):
    eliminated_expression = eliminate_implication(expression)
    print("Eliminated Implication:", eliminated_expression)

    negated_expression = move_negation(eliminated_expression)
    print("Negated Expression:", negated_expression)

    removed_not = remove_double_not(negated_expression)
    print("Removed Double Negation:", removed_not)

    standardized_expression = standardize_variables(removed_not)
    print("Standardized Variables:", standardized_expression)

    prenex_expression = prenex_form(standardized_expression)
    print("Prenex Form:", prenex_expression)

    universal_expression = eliminate_universal_quantifiers(prenex_expression)
    print("Eliminated Universal Quantifiers:", universal_expression)

    return universal_expression

expression = ["∀x∀z(p(x) ∧ ~r(x,z)) -> ∃xq(x)", "∀yq(y) -> ∃xq(x)"]
for i in expression:
    print("Original Expression:", i)
    final = transform_expression(i)
    print("Final Result:", final)
