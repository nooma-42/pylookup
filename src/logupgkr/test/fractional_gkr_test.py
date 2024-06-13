import unittest
from typing import Callable
from collections import defaultdict
from src.common_util.curve import Scalar
from src.common_util.mle_poly import generate_combinations
from src.logupgkr.fractional_gkr import Circuit, Layer, Node

# NOTE: it's 1 and -1 in the original paper, not sure the difference on performance
one = Scalar(1)
zero = Scalar(0)

"""  
Test fixture
NOTE: Prover has to calculate
"""
# Test1
test1_n = 1 # 2^n rows
test1_k = 1 # 2^k - 1 columns
def test1_m(X: list[Scalar]) -> Scalar:
    result = {tuple([zero]): Scalar(1),
            tuple([one]): Scalar(1)}.get(tuple(X))
    if result is None:
        raise ValueError("Invalid input")
    else:
        return result

def test1_t(X: list[Scalar]) -> Scalar:
    result = {tuple([zero]): Scalar(1),
            tuple([one]): Scalar(2)}.get(tuple(X))
    if result is None:
        raise ValueError("Invalid input")
    else:
        return result

def test1_w1(X: list[Scalar]) -> Scalar:
    result: Scalar | None = {tuple([zero]): Scalar(1),
            tuple([one]): Scalar(2)}.get(tuple(X))
    if result is None:
        raise ValueError("Invalid input")
    else:
        return result

test1_w = [test1_w1]

# Test2
test2_n = 2 # 2^n rows
test2_k = 2 # 2^k - 1 columns
def test2_m(X: list[Scalar]) -> Scalar:
    result = {tuple([zero, zero]): Scalar(7),
              tuple([zero, one]): Scalar(3),
              tuple([one, zero]): Scalar(1),
              tuple([one, one]): Scalar(1)}.get(tuple(X))
    if result is None:
        raise ValueError("Invalid input")
    else:
        return result

def test2_t(X: list[Scalar]) -> Scalar:
    result = {tuple([zero, zero]): Scalar(1),
            tuple([zero, one]): Scalar(2),
            tuple([one, zero]): Scalar(3),
            tuple([one, one]): Scalar(4)}.get(tuple(X))
    if result is None:
        raise ValueError("Invalid input")
    else:
        return result

def test2_w1(X: list[Scalar]) -> Scalar:
    result = {tuple([zero, zero]): Scalar(1),
            tuple([zero, one]): Scalar(2),
            tuple([one, zero]): Scalar(3),
            tuple([one, one]): Scalar(1)}.get(tuple(X))
    if result is None:
        raise ValueError("Invalid input")
    else:
        return result

def test2_w2(X: list[Scalar]) -> Scalar:
    result = {tuple([zero, zero]): Scalar(2),
            tuple([zero, one]): Scalar(1),
            tuple([one, zero]): Scalar(4),
            tuple([one, one]): Scalar(2)}.get(tuple(X))
    if result is None:
        raise ValueError("Invalid input")
    else:
        return result

def test2_w3(X: list[Scalar]) -> Scalar: # TODO: figure out how to pad, we need to pad 1 extra column because of the 2^k - 1, I padded with 1 UPDATE: shd be okay atm
    result = {tuple([zero, zero]): Scalar(1),
            tuple([zero, one]): Scalar(1),
            tuple([one, zero]): Scalar(1),
            tuple([one, one]): Scalar(1)}.get(tuple(X))
    if result is None:
        raise ValueError("Invalid input")
    else:
        return result

test2_w = [test2_w1, test2_w2, test2_w3]
test1_a = Scalar(42) # random scalar given by the verifier


"""  
Function based on the paper
NOTE: these are predefined
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
        if value == zero:
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

"""  
Circuit generation
"""

def generate_test_fractional_gkr_circuit_value(test_n, test_k, test_w, test_a) -> dict[int, list[tuple[tuple[Scalar, ...], Scalar, Scalar]]]:
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
            p_k_plus_one_neg = postfix_ps.get(zero)
            q_k_plus_one_pos = postfix_qs.get(one)
            q_k_plus_one_neg = postfix_qs.get(zero)
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
    for X in generate_combinations(test_n):
            for Y in generate_combinations(test_k):
                index_and_p.append((tuple(X+Y), p(X, Y, test2_m)))
                index_and_q.append((tuple(X+Y), q(X, Y, test2_t, test_w, test_a)))
    # Generate the layers above till the top
    index_and_p_layers, index_and_q_layers  = perform_layers(index_and_p, index_and_q, config="p")

    def combine_layers(p_layers: list[list[tuple[tuple[Scalar, ...], Scalar]]], q_layers: list[list[tuple[tuple[Scalar, ...], Scalar]]]) -> list[list[tuple[tuple[Scalar, ...], Scalar, Scalar]]]:
        combined_layers = []

        for round_p, round_q in zip(p_layers, q_layers):
            round_combined = []
            for prefix_p, value_p in round_p:
                for prefix_q, value_q in round_q:
                    if prefix_p == prefix_q:
                        round_combined.append((prefix_p, value_p, value_q))
                        break
            combined_layers.append(round_combined)

        return combined_layers

    def print_layers(layers):
        print("Printing layers:")
        for i, round_result in enumerate(layers):
            print(f"Round {i}:")
            for item in round_result:
                if len(item) == 2:
                    prefix, value = item
                    print(f"({prefix}, {value})")
                elif len(item) == 3:
                    prefix, value_p, value_q = item
                    print(f"({prefix}, {value_p}, {value_q})")
            print()
    index_and_layers: list[list[tuple[tuple[Scalar, ...], Scalar, Scalar]]] = combine_layers(index_and_p_layers, index_and_q_layers)
    #print_layers(index_and_p_layers)
    #print_layers(index_and_q_layers)
    #print_layers(index_and_layers)
    index_and_layers.reverse()
    return {i: layer for i, layer in enumerate(index_and_layers)}


def init_test_circuit(test_n, test_k, test_w, test_a) -> Circuit:
    def generate_p_q_functions(index_and_layers: dict[int, list[tuple[tuple[Scalar, ...], Scalar, Scalar]]], config=None) -> dict[int, Callable[[list[Scalar]], Scalar]]:
        if config not in ["p", "q"]:
            raise ValueError("Invalid config")
        i_functions = {}

        for layer_idx, layer in index_and_layers.items():
            layer_map = {tuple(prefix): q for prefix, _, q in layer} if config == "q" else {tuple(prefix): p for prefix, p, _ in layer}

            def layer_function(arr: list[int]) -> Scalar:
                prefix = tuple(arr)
                if prefix in layer_map:
                    return layer_map[prefix]
                else:
                    raise ValueError(f"Invalid input array for layer {layer_idx}: {arr}")

            i_functions[layer_idx] = layer_function
        return i_functions

    def generate_node_dict(index_and_layers: dict[int, list[tuple[tuple[Scalar, ...], Scalar, Scalar]]]) -> dict[int, dict[int, Node]]:
        node_dicts = {}
        for layer_idx, layer in index_and_layers.items():
            node_dict = {}
            for idx, (prefix, p, q) in enumerate(layer):
                node_dict[idx] = Node(list(prefix), p, q)
            node_dicts[layer_idx] = node_dict
        return node_dicts

    # index_and_layers represents [(index: tuple, p: Scalar, q: Scalar), ...]
    index_and_layers: dict[int, list[tuple[tuple[Scalar, ...], Scalar, Scalar]]] = generate_test_fractional_gkr_circuit_value(test_n, test_k, test_w, test_a)
    node_dicts: dict[int, dict[int, Node]] = generate_node_dict(index_and_layers)
    layers: dict[int, Layer] = {layer_idx: Layer(node_dict) for layer_idx, node_dict in node_dicts.items()}
    p_i = generate_p_q_functions(index_and_layers, config="p")
    q_i = generate_p_q_functions(index_and_layers, config="q")
    return Circuit(layers, p_i, q_i)

class TestLogUPGKR(unittest.TestCase):
    def test_p_and_q_single_column(self):
        fraction_sum = Scalar(0)
        # test_n is row and test_k is column
        for X in generate_combinations(test1_n):
            for Y in generate_combinations(test1_k):
                fraction_sum = fraction_sum + p(X, Y, test1_m) / q(X, Y, test1_t, test1_w, test1_a)
                print(q(X, Y, test1_t, test1_w, test1_a))
        assert fraction_sum == Scalar(0)
    def test_p_and_q_two_column(self):
        fraction_sum = Scalar(0)
        for X in generate_combinations(test2_n):
            for Y in generate_combinations(test2_k):
                fraction_sum = fraction_sum + p(X, Y, test2_m) / q(X, Y, test2_t, test2_w, test1_a)
                print(f"p: {p(X, Y, test2_m)},  q: {q(X, Y, test2_t, test2_w, test1_a)}")
        assert fraction_sum == Scalar(0)
    def test_prove_layer(self):
        circuit = init_test_circuit(test2_n, test2_k, test2_w, test1_a)
        pass