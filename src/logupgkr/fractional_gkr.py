# Code modified from https://github.com/jeong0982/gkr
import math
from typing import Callable
from dataclasses import dataclass
from src.common_util.curve import Scalar
from src.common_util.mle_poly import (
    get_multi_ext, eval_expansion, eval_univariate, get_ext,
    monomial, term, polynomial
)
from src.common_util.sumcheck import prove_sumcheck, verify_sumcheck
from src.logupgkr.transcript import Transcript

one = Scalar(1)
zero = Scalar(0)

@dataclass
class Node:
  """  
  p represents nominator
  q represents denominator
  """
  def __init__(self, binary_index: list[Scalar], p: Scalar, q: Scalar):
    self.binary_index: list[Scalar] = binary_index
    self.p = p 
    self.q = q

class Layer:
    def __init__(self, index_and_nodes: dict[int, Node]) -> None:
        index_and_nodes = dict(sorted(index_and_nodes.items()))
        self.nodes: list[Node] = [index_and_nodes[i] for i in range(len(index_and_nodes))]

    def get_node(self, index) -> Node:
        return self.nodes[index]

    def nodes_length(self):
        return len(self.nodes)

class Circuit:
    """  
    params:
        index_and_layers: [[((x1, x2, x3), p, q), ...], ...]
                representing [layer1, layer2, ...]
        p_i represents a dict from layer_number to nominator function
            for example, the expected form is:
            p_i[0] = W0func
            ```
            def W0func(arr):
                if(arr == [Scalar(0)]):
                    return Scalar(36)
                elif (arr == [Scalar(1)]):
                    return Scalar(6)
            ```
        q_i represents a dict from layer_number to denominator function, similar to p_i
    """
    def __init__(self, index_and_layers: dict[int, Layer], p_i: dict[int, Callable[[list[Scalar]], Scalar]], q_i: dict[int, Callable[[list[Scalar]], Scalar]]):
        index_and_layers = dict(sorted(index_and_layers.items()))
        self.layers: list[Layer] = [index_and_layers[i] for i in range(len(index_and_layers))]
        self.p_i: dict[int, Callable[[list[Scalar]], Scalar]] = p_i
        self.q_i: dict[int, Callable[[list[Scalar]], Scalar]]= q_i
    
    def get_node(self, layer, index):
        return self.layers[layer].get_node(index)

    def depth(self):
        return len(self.layers)

    def layer_length(self, layer):
        return self.layers[layer].nodes_length()
    
    def k_i(self, layer):
        return int(math.log2(self.layer_length(layer)))

@dataclass
class Proof:
    def __init__(self) -> None:
      self.sumcheck_proofs: list[list[list[Scalar]]] = []
      self.sumcheck_rs: list[list[Scalar]] = []
      self.f_values: list[Scalar] = [] # f(r) at each layer
      self.p_k_plus_one_reduceds: list[list[Scalar]] = [] # multivariate reduced to univariate polynomial for verifier
      self.q_k_plus_one_reduceds: list[list[Scalar]] = [] # multivariate reduced to univariate polynomial for verifier
      self.D: list[list[Scalar]] = [] # function D : {0, 1}k0 → F claimed to equal W0 (the function mapping output gate labels to output values)
      self.z: list[list[Scalar]] = [] # randomness for next layer, this will combine with sumcheck_r and input to sumcheck verification final check
      self.r_stars: list[Scalar] = [] # randomness for l(), l(r*) => r_i+1
      self.k: list[int] = [] # k_i, the variable count at each layer, 4 nodes -> 2 variables

      # circuit info
      self.d : int = 0 # depth of the circuit
      self.input_func : list[list[Scalar]] = [] # input function, the bottom most layer function

def reduce_multiple_polynomial(b: list[Scalar], c: list[Scalar], w: polynomial) -> list[Scalar]:
    """
    reduce multiple polynomial p(y, +1), p(y, 0) to p'() univariate polynomials and q(y, +1), q(y, 0) to q'() for verifier

    params:
    b: list[Scalar], verifier must evalute w at this random points
    c: list[Scalar], verifier must evalute w at this random points
    w: polynomial, polynomial to be reduced

    returns:
    list[Scalar], all the coefficients of the reduced polynomial

    NOTE:
    In original GKR in Proof Argument and Zero Knowledge, this is q = reduce_multiple_polynomial(b*, c*, W_i+1)
    univariate q(0) and q(1) replace W_i+1(b*) W_i+1(c*)

    lemma 3.8 in Proof Argument and Zero Knowledge
    """
    assert(len(b) == len(c))
    t = []
    new_poly_terms = []
    for b_i, c_i in zip(b, c):
        new_const = b_i
        gradient = c_i - b_i
        t.append(term(gradient, 1, new_const))
    
    for mono in w.terms:
        new_terms = []
        for each in mono.terms:
            new_term = t[each.x_i - 1] * each.coeff
            new_term.const += each.const
            new_terms.append(new_term)
        new_poly_terms.append(monomial(mono.coeff, new_terms))

    poly = polynomial(new_poly_terms, w.constant)
    return poly.get_all_coefficients()

def ell(p1: list[Scalar], p2: list[Scalar], t: Scalar, k_i_plus_one: int) -> list[Scalar]:
    """  
    reduce verification at two points into verification at a single point. F->F^k_i+1

    params:
    p1: point1
    p2: point2
    t: ∈ F, random point to evaluate the linear function

    returns:
    r_next ∈ F^k_i+1
    
    NOTE:
    1. ell is the latex syntax l
    2. Using 2 points to construct a linear function and evaluate it at a single point t, for example, r_i+1 = l(r*). l(0) = b*, l(1) = c*
    3. output = p1 + t(p2-p1), we adjust the output to the range of the number of elements of the curve
    4. The detail of this function is described in lemma 3.8 in Proof Argument and Zero Knowledge
    """
    consts = p1
    output: list[Scalar] = [Scalar.zero()]*len(p2)
    other_term = [Scalar.zero()]*len(p2)
    for i in range(len(p2)):
        other_term[i] = p2[i] - consts[i]
    for i in range(len(p2)):
        output[i] = consts[i] + t*other_term[i]
    if len(output) < k_i_plus_one: # TODO: This might not be safe
        output += [Scalar.zero()]*(k_i_plus_one - len(output))
    else:
        output = output[:k_i_plus_one]
    return output


def prove_layer(circuit: Circuit, current_layer_num: int, r: list[Scalar], transcript: Transcript) -> tuple[list[list[Scalar]], list[Scalar], list[Scalar], Scalar, Scalar, list[Scalar], list[Scalar]]:
    """ 
    Prove each layer with sumcheck protocol

    params:
    circuit: Circuit
    current_layer_num: int
    r_k: a random scalar vector. This will be used in sumcheck

    returns:
    sumcheck_proof: list[list[Scalar]], containing all the coefficients of each round
    sumcheck_r: list[Scalar], hash of the coefficients of each round as a randomness
    r_k_plus_one: Scalar
    f_result_value: Scalar

    NOTE:
    At each layer, we need to:
    1. Calculate the polynomial p_k, q_k and use them to calculate f
    2. Claim f(r) by evaluate f at all r_i from previous layer and the summation of the rest of the variables evaluated at both 0 and 1
    3. Run sumcheck protocol for each adjacent layers. We generate a list of coefficient as sumcheck proof and hash of the coefficients as randomness
    4. Reduce multiple polynomial p(y, +1), p(y, 0) to p'() univariate polynomials and q(y, +1), q(y, 0) to q'() for verifier
    """
    next_layer_num: int = current_layer_num + 1
    
    # 1. Calculate the polynomial p_k q_k. They are the fraction nominator and denominator, p_k+1(, 1), # p_k+1(, 0) aka p_k+1(, +1), # p_k+1(, -1) in paper
    p_k_plus_one_one: polynomial = get_ext(f=circuit.p_i[next_layer_num], v=circuit.k_i(next_layer_num), last_element=one)
    q_k_plus_one_one: polynomial = get_ext(f=circuit.q_i[next_layer_num], v=circuit.k_i(next_layer_num), last_element=one)
    p_k_plus_one_zero: polynomial = get_ext(f=circuit.p_i[next_layer_num], v=circuit.k_i(next_layer_num), last_element=zero)
    q_k_plus_one_zero: polynomial = get_ext(f=circuit.q_i[next_layer_num], v=circuit.k_i(next_layer_num), last_element=zero)
    p_k: polynomial = p_k_plus_one_one * q_k_plus_one_zero + p_k_plus_one_zero * q_k_plus_one_one
    q_k: polynomial = q_k_plus_one_one * q_k_plus_one_zero
    # TODO: make this random linear combined
    f: polynomial = p_k + q_k
    
    # 2. Claim f(r) by evaluate f at r_k from previous layer
    f_result = polynomial(f.terms, f.constant)
    f_result_value: Scalar = one
    assert len(r) == circuit.k_i(current_layer_num)
    for j, x in enumerate(r, 1):
        if j == len(r):
            f_result_value = f_result.eval_univariate(x)
        f_result: polynomial = f_result.eval_i(x, j)

    # 3. Run sumcheck protocol for each adjacent layers, NOTE: sumcheck_r
    sumcheck_proof, sumcheck_r = prove_sumcheck(g=f, v=circuit.k_i(next_layer_num), transcript=transcript) 

    # 4. Reduce multiple polynomial p(y, +1), p(y, 0) to p'() univariate polynomials and q(y, +1), q(y, 0) to q'() for verifier
    next_p: polynomial = get_ext(circuit.p_i[next_layer_num], circuit.k_i(next_layer_num))
    next_q: polynomial = get_ext(circuit.q_i[next_layer_num], circuit.k_i(next_layer_num))
    p_k_plus_one_reduced: list[Scalar] = reduce_multiple_polynomial(sumcheck_r + [one], sumcheck_r + [zero], next_p)
    q_k_plus_one_reduced: list[Scalar] = reduce_multiple_polynomial(sumcheck_r + [one], sumcheck_r + [zero], next_q)
    # TODO replace this with merlin transcript
    r_k_star: Scalar = Scalar(sum(list(map(lambda x : int(x), sumcheck_proof[len(sumcheck_proof) - 1])))) # FIXME: sum in this line should be hash
    r_k_plus_one: list[Scalar] = ell(sumcheck_r + [one], sumcheck_r + [zero], r_k_star, circuit.k_i(next_layer_num)) # r_i+1 = l(r*), m_i+1 = q(r*)

    return sumcheck_proof, sumcheck_r, r_k_plus_one, r_k_star, f_result_value, p_k_plus_one_reduced, q_k_plus_one_reduced

def verify_layer(m: Scalar, sumcheck_proof: list[list[Scalar]], sumcheck_r: list[Scalar], k: int, r_k_star: Scalar, p_k_plus_one_reduced: list[Scalar], q_k_plus_one_reduced: list[Scalar]) -> tuple[bool, Scalar|None]:
    """
    params:
    m: claimed value of f(r) at the current layer

    m = [Scalar.zero()]*proof.d
    m[0] = eval_expansion(proof.D, proof.z[0])

    NOTE:
    At each layer, we need to:
    1. Verify the sumcheck protocol for each adjacent layers
    2. Check if f(r) is equal to the claimed value
    """
    # 1. Verify the sumcheck protocol for each adjacent layers
    p_q_plus_one_dict: dict[str, Scalar] = {
        "p_k_plus_one_one": eval_univariate(p_k_plus_one_reduced, one), 
        "p_k_plus_one_zero": eval_univariate(p_k_plus_one_reduced, zero), 
        "q_k_plus_one_one": eval_univariate(q_k_plus_one_reduced, one), 
        "q_k_plus_one_zero": eval_univariate(q_k_plus_one_reduced, zero)
    }
    valid = verify_sumcheck(claim=m, proof=sumcheck_proof, r=sumcheck_r, v=k, config="FRACTIONAL_GKR", p_q_plus_one_dict=p_q_plus_one_dict)
    
    if not valid:
        return False, None
    else:
        m_next: Scalar = eval_univariate(p_k_plus_one_reduced, r_k_star) + eval_univariate(q_k_plus_one_reduced, r_k_star)
        return True, m_next # m_next should be the input of the next layer


def prove(circuit: Circuit):
    # At the start of the protocol P sends a function D : {0, 1}k0 → F claimed to equal W0 (the function mapping output gate labels to output values)
    transcript = Transcript(b"fractional_gkr_please_pass_verification_QAQ")
    proof = Proof()
    proof.D = get_multi_ext(circuit.p_i[0], circuit.k_i(0)) + get_multi_ext(circuit.q_i[0], circuit.k_i(0)) 
    proof.z = [[]] * circuit.depth()
    proof.z[0] = [Scalar.zero()] * circuit.k_i(0) # k_0 is 0 in this case
    
    for i in range(len(proof.z[0])):
        proof.z[0][i] = Scalar(1) # assuming this random scalar is given by the verifier

    for current_layer_num in range(circuit.depth() - 1):
        (sumcheck_proof, 
         sumcheck_r, 
         r_k_plus_one, 
         r_k_star, 
         f_value, 
         p_k_plus_one_reduced, 
         q_k_plus_one_reduced
         ) = prove_layer(circuit, current_layer_num, proof.z[current_layer_num])
        proof.sumcheck_proofs.append(sumcheck_proof)
        proof.sumcheck_rs.append(sumcheck_r)
        proof.r_stars.append(r_k_star)
        proof.f_values.append(f_value)
        proof.p_k_plus_one_reduceds.append(p_k_plus_one_reduced)
        proof.q_k_plus_one_reduceds.append(q_k_plus_one_reduced)
        proof.z[current_layer_num + 1] = r_k_plus_one
        proof.k.append(circuit.k_i(current_layer_num))

    proof.input_func = get_multi_ext(circuit.p_i[circuit.depth() - 1], circuit.k_i(circuit.depth() - 1)) + get_multi_ext(circuit.q_i[circuit.depth() - 1], circuit.k_i(circuit.depth() - 1)) # TODO make this random linear combined
    proof.d = circuit.depth()
    return proof

def verify(proof: Proof):
    # V picks a random r0 ∈ Fk0 and lets m0 ← ˜D(r0). The remainder of the protocol is devoted to confirming that m0 = ˜W0(r0). 
    m: list[Scalar] = [Scalar.zero()]*proof.d
    m[0] = eval_expansion(proof.D, proof.z[0])

    for current_layer_num in range(proof.d - 1):
        out: tuple[bool, Scalar|None] = verify_layer(
            m[current_layer_num], 
            proof.sumcheck_proofs[current_layer_num], 
            proof.sumcheck_rs[current_layer_num], 
            current_layer_num,
            proof.r_stars[current_layer_num],
            proof.p_k_plus_one_reduceds[current_layer_num], 
            proof.q_k_plus_one_reduceds[current_layer_num]
        )
        if len(out) == 2 and out[1] is not None:
            valid = out[0]
            if not valid:
                return False
            m[current_layer_num + 1] = out[1]
        elif len(out) and not out:
            return False
    if m[proof.d - 1] != eval_expansion(proof.input_func, proof.z[proof.d - 1]):
        return False
    return True
