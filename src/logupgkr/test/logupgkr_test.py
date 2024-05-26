import unittest
from src.common_util.curve import Scalar

one = Scalar(1)
neg_one = Scalar(-1)

"""  
Prover calculate
"""
def test_m(X):
    return {tuple([neg_one]): Scalar(1),
            tuple([one]): Scalar(1)}.get(tuple(X))

def test_t(X):
    return {tuple([neg_one]): Scalar(1),
            tuple([one]): Scalar(2)}.get(tuple(X))

def test_w1(X):
    return {tuple([neg_one]): Scalar(1),
            tuple([one]): Scalar(2)}.get(tuple(X))

def test2_m(X):
    return {tuple([neg_one, neg_one]): Scalar(3),
            tuple([neg_one, one]): Scalar(3),
            tuple([one, neg_one]): Scalar(1),
            tuple([one, one]): Scalar(1)}.get(tuple(X))

def test2_t(X):
    return {tuple([neg_one, neg_one]): Scalar(1),
            tuple([neg_one, one]): Scalar(2),
            tuple([one, neg_one]): Scalar(3),
            tuple([one, one]): Scalar(4)}.get(tuple(X))

def test2_w1(X):
    return {tuple([neg_one, neg_one]): Scalar(1),
            tuple([neg_one, one]): Scalar(2),
            tuple([one, neg_one]): Scalar(3),
            tuple([one, one]): Scalar(1)}.get(tuple(X))

def test2_w2(X):
    return {tuple([neg_one, neg_one]): Scalar(2),
            tuple([neg_one, one]): Scalar(1),
            tuple([one, neg_one]): Scalar(4),
            tuple([one, one]): Scalar(2)}.get(tuple(X))


"""  
Predefine
"""

#test_w = [w1, w2]
test_w = [test_w1]
test2_w = [test2_w1, test2_w2]
test_a = Scalar(1) # random scalar given by the verifier

def i_y(Y: list[Scalar]):
    """
    i(y) in w_i(y)
    000 -> 1
    001 -> 2
    111 -> 8 X
    00 -> 1
    11 -> 4
    """
    
    # Convert the input list of Scalar to binary representation
    bits = []
    for value in Y:
        if value == neg_one:
            bits.append('0')
        else:
            bits.append('1')
    value = 0
    
    # Calculate the integer value based on the binary string
    for bit in bits:
        value = (value << 1) + int(bit)
    
    # Map the integer value to the specified values based on length
    # Note: 
    return value

def p(X, Y, m):
    if all(value == one for value in Y):
        return m(X)
    else:
        return one

def q(X, Y, t, w, a):
    if all(value == one for value in Y):
        return a - t(X)
    else:
        return a - w[i_y(Y) - 1](X)        

def generate_combinations(length):
    if length == 0:
        return [[]]
    else:
        result = []
        for combination in generate_combinations(length - 1):
            result.append(combination + [neg_one])
            result.append(combination + [one])
        return result

class TestLogUPGKR(unittest.TestCase):
    def test_simple_p_q(self):
        Y = []
        fraction_sum = Scalar(0)
        for X in generate_combinations(1):
            fraction_sum = fraction_sum + p(X, Y, test_m) / q(X, Y, test_t, test_w, test_a)
        assert fraction_sum == Scalar(0)
    def test_p_q(self):
        Y = [one, neg_one]
        fraction_sum = Scalar(0)
        for X in generate_combinations(2):
            fraction_sum = fraction_sum + p(X, Y, test2_m) / q(X, Y, test2_t, test2_w, test_a)
        assert fraction_sum == Scalar(0)
        