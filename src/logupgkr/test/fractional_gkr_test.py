import unittest
from typing import Callable
from collections import defaultdict
from src.common_util.curve import Scalar
from src.common_util.mle_poly import generate_combinations
from src.logupgkr.fractional_gkr import Circuit, Layer, Node

one = Scalar(1)
neg_one = Scalar(-1)

"""  
Prover calculate
"""
# Test1
test_n = 1 # 2^n rows
test_k = 1 # 2^k - 1 columns
def test_m(X: list[Scalar]) -> Scalar:
    result = {tuple([neg_one]): Scalar(1),
            tuple([one]): Scalar(1)}.get(tuple(X))
    if result is None:
        raise ValueError("Invalid input")
    else:
        return result

def test_t(X: list[Scalar]) -> Scalar:
    result = {tuple([neg_one]): Scalar(1),
            tuple([one]): Scalar(2)}.get(tuple(X))
    if result is None:
        raise ValueError("Invalid input")
    else:
        return result

def test_w1(X: list[Scalar]) -> Scalar:
    result: Scalar | None = {tuple([neg_one]): Scalar(1),
            tuple([one]): Scalar(2)}.get(tuple(X))
    if result is None:
        raise ValueError("Invalid input")
    else:
        return result

test_w = [test_w1]

# Test2
test2_n = 2 # 2^n rows
test2_k = 2 # 2^k - 1 columns
def test2_m(X: list[Scalar]) -> Scalar:
    result = {tuple([neg_one, neg_one]): Scalar(7),
              tuple([neg_one, one]): Scalar(3),
              tuple([one, neg_one]): Scalar(1),
              tuple([one, one]): Scalar(1)}.get(tuple(X))
    if result is None:
        raise ValueError("Invalid input")
    else:
        return result

def test2_t(X: list[Scalar]) -> Scalar:
    result = {tuple([neg_one, neg_one]): Scalar(1),
            tuple([neg_one, one]): Scalar(2),
            tuple([one, neg_one]): Scalar(3),
            tuple([one, one]): Scalar(4)}.get(tuple(X))
    if result is None:
        raise ValueError("Invalid input")
    else:
        return result

def test2_w1(X: list[Scalar]) -> Scalar:
    result = {tuple([neg_one, neg_one]): Scalar(1),
            tuple([neg_one, one]): Scalar(2),
            tuple([one, neg_one]): Scalar(3),
            tuple([one, one]): Scalar(1)}.get(tuple(X))
    if result is None:
        raise ValueError("Invalid input")
    else:
        return result

def test2_w2(X: list[Scalar]) -> Scalar:
    result = {tuple([neg_one, neg_one]): Scalar(2),
            tuple([neg_one, one]): Scalar(1),
            tuple([one, neg_one]): Scalar(4),
            tuple([one, one]): Scalar(2)}.get(tuple(X))
    if result is None:
        raise ValueError("Invalid input")
    else:
        return result

def test2_w3(X: list[Scalar]) -> Scalar: # TODO: figure out how to pad, we need to pad 1 extra column because of the 2^k - 1, I padded with 1
    result = {tuple([neg_one, neg_one]): Scalar(1),
            tuple([neg_one, one]): Scalar(1),
            tuple([one, neg_one]): Scalar(1),
            tuple([one, one]): Scalar(1)}.get(tuple(X))
    if result is None:
        raise ValueError("Invalid input")
    else:
        return result

test2_w = [test2_w1, test2_w2, test2_w3]
test_a = Scalar(42) # random scalar given by the verifier


"""  
Predefine
"""

def i_y(Y: list[Scalar]):
    """
    i(y) in w_i(y) in α − wi(y)( X ))
    000 -> 1
    001 -> 2
    111 -> 8
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

def p(X: list[Scalar], Y: list[Scalar], m: Callable[[list[Scalar]], Scalar]):
    if all(value == one for value in Y):
        return m(X)
    else:
        return -one

def q(X, Y, t: Callable[[list[Scalar]], Scalar], w: list[Callable[[list[Scalar]], Scalar]], a: Scalar):
    """  
    params:
    t: table
    w: witness
    a: alias of α, challenge
    """
    if all(value == one for value in Y):
        return a - t(X)
    else:
        return a - w[i_y(Y)](X)              

def generate_test_fractional_gkr_circuit_value() -> tuple[list[list[tuple[tuple[Scalar, ...], Scalar]]], list[list[tuple[tuple[Scalar, ...], Scalar]]]]:
    def q_one_layer_up(qs):
        groups = defaultdict(list)
        length = max(len(t[0]) for t in qs)

        for binary, value in qs:
            prefix = binary[:length-1]
            groups[tuple(prefix)].append(value)

        def denominator(qs):
            # these are q_k_plus_one_pos, q_k_plus_one_neg
            if len(qs) != 2:
                raise ValueError("Invalid input")
            return qs[0] * qs[1]
        return [(k, denominator(v)) for k, v in groups.items()]
    
    def p_one_layer_up(index_and_p: list[tuple[tuple[Scalar,...], Scalar]], index_and_q: list[tuple[tuple[Scalar,...], Scalar]]):
        """  
        params:
        index_and_p: [([x1, x2, x3], p), (...)...]
        index_and_q: [([x1, x2, x3], p), (...)...]

        examples:
        [([1, -1, 1], 10)]
        """
        p_groups = defaultdict(defaultdict) # prefix -> postfix -> value
        q_groups = defaultdict(defaultdict) # prefix -> postfix -> value
        prefix_list: set[tuple[Scalar,...]] = set() # set[tuple[index in hypercube]], list is unhashable, turn it into tuple

        index_and_p_length = max(len(t[0]) for t in index_and_p)
        index_and_q_length = max(len(t[0]) for t in index_and_q)
        if index_and_p_length != index_and_q_length:
            raise ValueError("p and q length mismatch")
        length = index_and_p_length
        for binary, value in index_and_p:
            prefix: tuple[Scalar,...] = binary[:length-1]
            post_fix: Scalar = binary[length-1]
            p_groups[tuple(prefix)][post_fix] = value
        for binary, value in index_and_q:
            prefix: tuple[Scalar,...] = binary[:length-1]
            post_fix: Scalar = binary[length-1]
            tuple_prefix: tuple[Scalar,...] = tuple(prefix)
            q_groups[tuple_prefix][post_fix] = value
            prefix_list.add(tuple_prefix)

        nominators: list[tuple[tuple[Scalar,...], Scalar]] = [] # [(prefix: tuple, value: Scalar)]
        for pre in prefix_list:
            postfix_ps = p_groups[tuple(pre)]
            postfix_qs = q_groups[tuple(pre)]
            p_k_plus_one_neg, p_k_plus_one_pos, q_k_plus_one_neg, q_k_plus_one_pos = None, None, None, None
            if len(postfix_ps) != 2 or len(postfix_qs) != 2:
                raise ValueError("Invalid input")
            p_k_plus_one_pos = postfix_ps.get(one)
            p_k_plus_one_neg = postfix_ps.get(neg_one)
            q_k_plus_one_pos = postfix_qs.get(one)
            q_k_plus_one_neg = postfix_qs.get(neg_one)
            if p_k_plus_one_neg is None or p_k_plus_one_pos is None or q_k_plus_one_neg is None or q_k_plus_one_pos is None:
                raise ValueError("Invalid input")
            nominators.append((pre, p_k_plus_one_pos * q_k_plus_one_neg + p_k_plus_one_neg * q_k_plus_one_pos))
        return nominators

    def perform_layers(index_and_p: list[tuple[tuple[Scalar,...], Scalar]]|None, index_and_q: list[tuple[tuple[Scalar,...], Scalar]], config=None):
        """
        params:
        index_and_p: [((x1, x2, x3), p), (...)...]
            representing [(index: tuple, p: Scalar), ...]
            An index_and_p represents a layer of the circuit
        index_and_q: [((x1, x2, x3), p), (...)...]

        returns:
        index_and_p_layers: [[((x1, x2, x3), p), ...], ...]
            representing [layer1, layer2, ...]
        index_and_q_layers: [[((x1, x2, x3), q), ...], ...]

        Note:
        You can only calculate q, simply configure the config to "q"
        """
        index_and_p_layers = [index_and_p] if index_and_p is not None else []
        index_and_q_layers = [index_and_q]
        while True:
            if config == "p" and index_and_p is not None:
                next_round = p_one_layer_up(index_and_p, index_and_q)
                index_and_p = next_round
                index_and_q = q_one_layer_up(index_and_q)
                index_and_p_layers.append(index_and_p)
                index_and_q_layers.append(index_and_q)
            elif config == "q":
                next_round = q_one_layer_up(index_and_q)
                index_and_q = next_round
                index_and_q_layers.append(index_and_q)
            else:
                raise ValueError("Invalid config")

            if next_round is None:
                raise ValueError("Invalid next round")
            if len(next_round) == 1:
                break
        return index_and_p_layers, index_and_q_layers
    # Generate the bottom most layer
    index_and_p = []
    index_and_q = []
    for X in generate_combinations(test2_n):
            for Y in generate_combinations(test2_k):
                index_and_p.append((tuple(X+Y), p(X, Y, test2_m)))
                index_and_q.append((tuple(X+Y), q(X, Y, test2_t, test2_w, test_a)))
    # Generate the layers above till the top
    index_and_p_layers, index_and_q_layers  = perform_layers(index_and_p, index_and_q, config="p")
    def print_layers(layers):
        print("Printing layers:")
        for i, round_result in enumerate(layers):
            print(f"Round {i}:")
            for prefix, value in round_result:
                print(f"({prefix}, {value})")
            print()
    # print_layers(index_and_p_layers)
    # print_layers(index_and_q_layers)
    return index_and_p_layers, index_and_q_layers


def init_test_circuit():
    # index_and_p_layers represents [(index: tuple, p: Scalar), ...]
    index_and_p_layers, index_and_q_layers = generate_test_fractional_gkr_circuit_value()
    circuit = Circuit(5)
    
    layer = Layer(
        {
            0: Node(),
            1: Node(),
        }
    )
    #p_0 = Node([0], Scalar(0))
    #q_0 = Node([1], Scalar(2430480)) # 38, 39, 40, 41

    def W0func(arr):
        if(arr == [Scalar(0)]):
            return Scalar(36)
        elif (arr == [Scalar(1)]):
            return Scalar(6)
    

    
    """ c.layers[0].add_func(W0func) """
    """ c.add_node(0, 0, [0], 36, left=b1, right=b2) """
    """ c.add_node(0, 1, [1], 6, left=b3, right=b4) """

class TestLogUPGKR(unittest.TestCase):
    def test_p_and_q_single_column(self):
        fraction_sum = Scalar(0)
        # test_n is row and test_k is column
        for X in generate_combinations(test_n):
            for Y in generate_combinations(test_k):
                fraction_sum = fraction_sum + p(X, Y, test_m) / q(X, Y, test_t, test_w, test_a)
                print(q(X, Y, test_t, test_w, test_a))
        assert fraction_sum == Scalar(0)
    def test_p_and_q_two_column(self):
        fraction_sum = Scalar(0)
        for X in generate_combinations(test2_n):
            for Y in generate_combinations(test2_k):
                fraction_sum = fraction_sum + p(X, Y, test2_m) / q(X, Y, test2_t, test2_w, test_a)
                print(f"p: {p(X, Y, test2_m)},  q: {q(X, Y, test2_t, test2_w, test_a)}")
        assert fraction_sum == Scalar(0)
    def test_prove_layer(self):
        generate_test_fractional_gkr_circuit_value()
        pass