# Code modified from https://github.com/jeong0982/gkr
#mle sumcheck instead of binary
from src.common_util.mle_poly import (
    polynomial, 
    monomial,
    term,
    generate_binary, 
    eval_univariate, 
    evaluate_indices,
)
from src.common_util.curve import Scalar
from src.logupgkr.transcript import Transcript
from dataclasses import dataclass
def append_squeeze(transcript: Transcript, items: list[Scalar]) -> Scalar:
    """
    append the items to the transcript and squeeze a challenge
    """
    for coeff in items:
        transcript.append_scalar(label=b"sumcheck_coeff", item=coeff)
    return transcript.get_and_append_challenge(b"sumcheck_squeeze_challenge")

@dataclass
class SumcheckProof:
    claim: Scalar
    coefficients: list[list[Scalar]] # containing all the coefficients of each round
    r: list[Scalar] # hash of the coefficients of each round as a randomness
    num_var: int
    l: polynomial # oracle

def prove_sumcheck(g: polynomial, transcript: Transcript) -> SumcheckProof:
    """
    params:
    g: the polynomial to prove
    
    returns:
    proof: containing all the coefficients of each round
    r: randomness generated in each round
    
    NOTE: 
    1. this notation follows Proof Argument and Zero Knowledge by Justin Thaler
    """
    assert g.num_var() > 0
    proof = SumcheckProof(Scalar.zero(), [], [], g.num_var(), polynomial([]))
    
    # At the start of the protocol, the prover sends a value C1 claimed to equal the value H
    c1 = Scalar.zero()
    for assignment in generate_binary(g.num_var()):
        c1 += g.evaluate(assignment)
    proof.claim = c1

    # Round 1 to Round v
    for round in range(1, g.num_var() + 1):
        if round > 1:
            g_j = evaluate_indices(g, 1, round - 1, proof.r)
        else:
            # we have no random variable to evaluate the first round
            g_j = g
        if round < g.num_var():
            g_j = evaluate_indices(g_j, round + 1, g.num_var())
            r_j = append_squeeze(transcript, g_j.get_all_coefficients())
            proof.r.append(r_j)
        if round == g.num_var():
            # Make an oracle for verifier to query
            
        proof.coefficients.append(g_j.get_all_coefficients())

    return proof

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
    t: dict[int, term] = {}
    new_poly_terms = []
    for i, (b_i, c_i) in enumerate(zip(b, c), 1):
        new_const: Scalar = b_i
        gradient: Scalar = c_i - b_i
        t[i] = (term(gradient, i, new_const))
    
    for mono in w.terms:
        new_terms: list[term] = []
        for i, each in enumerate(mono.terms):
            new_term: term | None = t[each.x_i] * each.coeff
            if new_term is not None:
                new_term.const += each.const
                new_terms.append(new_term)
            # FIXME else
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

def oracle_query(l: polynomial, proof: SumcheckProof, transcript: Transcript) -> bool:
    """  
    l: oracle, it's an univariate polynomial
    proof: SumcheckProof
    transcript: to non interactively generate randomness
    """
    final_challenge = transcript.get_and_append_challenge(b"final_challenge")
    if eval_univariate(proof.coefficients[proof.num_var - 1], final_challenge) == l.evaluate(final_challenge):
        return True
    return False

# TODO accommodate +1 -1 case 
def verify_sumcheck(proof: SumcheckProof, transcript: Transcript) -> bool:
    """  
    params:
    proof: SumcheckProof
    transcript: to non interactively generate randomness

    Note:
    - Verifier either have a oracle query to g or calculate g herself
    - this implementation is for the case that verifier is given the oracle query access in aligned with GKR protocol mentioned in Proof Argument and Zero Knowledge by Justin Thaler
    """
    expected = proof.claim
    # Round 1 to Round v-1
    # where
    # round 1 C_1 ?= g_j(0) + g_j(1)
    # round 2 to round v: g_j-1(r_j-1) ?= g_j(0) + g_j(1)
    for round in range(1, proof.num_var):
        q_zero = eval_univariate(proof.coefficients[round - 1], Scalar.zero())
        q_one = eval_univariate(proof.coefficients[round - 1], Scalar.one())
        if q_zero + q_one != expected:
            return False
        if append_squeeze(transcript, proof.coefficients[round - 1]) != proof.r[round - 1]:
            return False
        expected = eval_univariate(proof.coefficients[round - 1], proof.r[round - 1])
    
    # Round v final check: g_v(r_v) ?= g(r1, r2, ..., rv)
    if oracle_query(l, proof, transcript):
        return True
    return False

    """ if p_q_plus_one_dict is None:
        raise ValueError("p_q_plus_one_dict must be provided in fractional gkr sumcheck")
    if p_q_plus_one_dict["p_k_plus_one_one"] is None or p_q_plus_one_dict["p_k_plus_one_zero"] is None or p_q_plus_one_dict["q_k_plus_one_one"] is None or p_q_plus_one_dict["q_k_plus_one_zero"] is None:
        raise ValueError("Invalid p_q_plus_one_dict")
    f_r_k: Scalar = (p_q_plus_one_dict["p_k_plus_one_one"] * p_q_plus_one_dict["q_k_plus_one_zero"] + p_q_plus_one_dict["p_k_plus_one_zero"] * p_q_plus_one_dict["q_k_plus_one_one"]) + p_q_plus_one_dict["q_k_plus_one_one"] * p_q_plus_one_dict["q_k_plus_one_zero"] """