# Code modified from https://github.com/jeong0982/gkr
import math
import time
from typing import Callable
from dataclasses import dataclass
from src.common_util.curve import Scalar
from src.common_util.mle_poly import (
    get_multi_ext, eval_expansion, eval_univariate, get_ext,
    monomial, term, polynomial
)
from src.common_util.sumcheck import prove_sumcheck, verify_sumcheck


@dataclass
class Node:
  """  
  p represents nominator
  q represents denominator
  """
  def __init__(self, binary_index: list[int], p: Scalar, q: Scalar):
    self.binary_index: list[int] = binary_index
    self.p = p 
    self.q = q

class Layer:
    def __init__(self, index_and_nodes: dict[int, Node]) -> None:
        index_and_nodes = dict(sorted(index_and_nodes.items()))
        self.nodes = [index_and_nodes[i] for i in range(len(index_and_nodes))]

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

class Proof:
    def __init__(self, proofs, r, f, D, q, z, r_stars, d, w, adds, mults, k) -> None:
      self.sumcheck_proofs : list[list[list[Scalar]]] = proofs
      self.sumcheck_r : list[list[Scalar]] = r
      self.f : list[Scalar] = f
      self.D : list[list[Scalar]] = D
      self.q : list[list[Scalar]] = q
      self.z : list[list[Scalar]] = z
      self.r : list[Scalar] = r_stars

      # circuit info
      self.d : int = d
      self.input_func : list[list[Scalar]] = w
      self.add : list[list[list[Scalar]]] = adds
      self.mult : list[list[list[Scalar]]] = mults
      self.k : list[int] = k

    def to_dict(self):
        to_serialize = dict()
        to_serialize['sumcheckProof'] = list(map(lambda x: list(map(lambda y: list(map(lambda z: repr(z), y)), x)), self.sumcheck_proofs))
        to_serialize['sumcheckr'] = list(map(lambda x: list(map(lambda y: repr(y), x)), self.sumcheck_r))
        to_serialize['f'] = list(map(lambda x: repr(x), self.f))
        to_serialize['q'] = list(map(lambda x: list(map(lambda y: repr(y), x)), self.q))
        to_serialize['z'] = list(map(lambda x: list(map(lambda y: repr(y), x)), self.z))
        to_serialize['D'] = list(map(lambda x: list(map(lambda y: repr(y), x)), self.D))
        to_serialize['r'] = list(map(lambda x: repr(x), self.r))
        to_serialize['inputFunc'] = list(map(lambda x: list(map(lambda y: repr(y), x)), self.input_func))
        to_serialize['add'] = list(map(lambda x: list(map(lambda y: list(map(lambda z: repr(z), y)), x)), self.add))
        to_serialize['mult'] = list(map(lambda x: list(map(lambda y: list(map(lambda z: repr(z), y)), x)), self.mult))
        return to_serialize

def prove_layer(circuit: Circuit, current_layer_num: int):
    """ 
    Prove each layer with sumcheck protocol

    params:
    circuit: Circuit
    current_layer_num: int
    r_k: a random scalar vector. This will be used in sumcheck
    """
    next_layer_num: int = current_layer_num + 1
    
    # Calculate the polynomial p_k q_k. They are the fraction nominator and denominator, p_k+1(, +1), # p_k+1(, -1)
    p_k_plus_one_pos: polynomial = get_ext(f=circuit.p_i[next_layer_num], v=circuit.k_i(next_layer_num), last_element=Scalar(1))
    q_k_plus_one_pos: polynomial = get_ext(f=circuit.q_i[next_layer_num], v=circuit.k_i(next_layer_num), last_element=Scalar(1))
    p_k_plus_one_neg: polynomial = get_ext(f=circuit.p_i[next_layer_num], v=circuit.k_i(next_layer_num), last_element=Scalar(-1))
    q_k_plus_one_neg: polynomial = get_ext(f=circuit.q_i[next_layer_num], v=circuit.k_i(next_layer_num), last_element=Scalar(-1))
    p_k: polynomial = p_k_plus_one_pos * q_k_plus_one_neg + p_k_plus_one_neg * q_k_plus_one_pos
    q_k: polynomial = q_k_plus_one_pos * q_k_plus_one_neg
    # TODO: make this random linear combination
    f: polynomial = p_k + q_k
    
    # FIXME: how does it prove sumcheck without knowing r? thinking about add r, # FIXME v
    sumcheck_proof, sumcheck_r = prove_sumcheck(g=f, v=circuit.k_i(next_layer_num), offset=0) 
    # TODO replace this with merlin transcript
    r_k_plus_one: Scalar = Scalar(sum(list(map(lambda x : int(x), sumcheck_proof)))) # FIXME: sum in this line should be hash
    
    return sumcheck_proof, sumcheck_r, r_k_plus_one

""" 
def prove(circuit: Circuit, D):
    start_time = time.time()

    D_poly = get_multi_ext(D, circuit.k_i(0))
    z = [[]] * circuit.depth()
    z[0] = [Scalar.zero()] * circuit.k_i(0)
    sumcheck_proofs = []
    q = []
    f_res = []
    sumcheck_r = []
    r_stars = []

    for i in range(len(z[0])):
        z[0][i] = Scalar(1) # random scalar given by the verifier

    for i in range(circuit.depth() - 1):
        sumcheck_proof, r, r_star, f_result_value, q_i, next_r = prove_layer(circuit, sumcheck_proofs, sumcheck_r, i) # FIXME check order
        sumcheck_proofs.append(sumcheck_proof)
        sumcheck_r.append(r)
        r_stars.append(r_star)
        f_res.append(f_result_value)
        q.append(q_i)
        z[i + 1] = next_r

    w_input = get_multi_ext(circuit.w_i(circuit.depth() - 1), circuit.k_i(circuit.depth() - 1))
    adds = []
    mults = []
    k = []
    for i in range(circuit.depth() - 1):
        adds.append(get_multi_ext(circuit.add_i(i), circuit.k_i(i) + 2 * circuit.k_i(i + 1)))
        mults.append(get_multi_ext(circuit.mult_i(i), circuit.k_i(i) + 2 * circuit.k_i(i + 1)))
        k.append(circuit.k_i(i))
    k.append(circuit.k_i(circuit.depth() - 1))
    proof = Proof(sumcheck_proofs, sumcheck_r, f_res, D_poly, q, z, r_stars, circuit.depth(), w_input, adds, mults, k)
    print("proving time :", time.time() - start_time)
    return proof

def verify(proof: Proof):
    start = time.time()
    m = [Scalar.zero()]*proof.d
    m[0] = eval_expansion(proof.D, proof.z[0])

    for i in range(proof.d - 1):
        # verify_layer()
        valid = verify_sumcheck(m[i], proof.sumcheck_proofs[i], proof.sumcheck_r[i], 2 * proof.k[i + 1])
        if not valid:
            return False
        else:
            # wi+1 but univariated
            q_i = proof.q[i]
            q_zero = eval_univariate(q_i, Scalar.zero())
            q_one = eval_univariate(q_i, Scalar.one())

            modified_f = eval_expansion(proof.add[i], proof.z[i] + proof.sumcheck_r[i]) * (q_zero + q_one) \
                        + eval_expansion(proof.mult[i], proof.z[i] + proof.sumcheck_r[i]) * (q_zero * q_one)

            sumcheck_p = proof.sumcheck_proofs[i]
            sumcheck_p_hash = Scalar(sum(list(map(lambda x : int(x), sumcheck_p[len(sumcheck_p) - 1])))) # FIXME: sum in this line should be hash

            if (proof.f[i] != modified_f) or (sumcheck_p_hash != proof.r[i]):
                print("verifying time :", time.time() - start)
                return False
            else:
                m[i + 1] = eval_univariate(q_i, proof.r[i])
    if m[proof.d - 1] != eval_expansion(proof.input_func, proof.z[proof.d - 1]):
        print("verifying time :", time.time() - start)
        return False
    print("verifying time :", time.time() - start)
    return True
 """