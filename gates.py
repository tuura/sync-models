def and_gate(a, b):
    return a and b

def nor_gate(a, b):
    return not (a or b)

def cgate1(a, b, c):
    return not (((not a) or b) and c)

def c_element(q, a, b):
    if a and b:
        return True
    elif (not a) and (not b):
        return False
    else:
        return q

def celem_var1(q, a, b):
    return c_element(q, not a, not b)
