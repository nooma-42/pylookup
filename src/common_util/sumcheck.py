# Code modified from https://github.com/jeong0982/gkr
#mle sumcheck instead of binary
from src.common_util.mle_poly import polynomial, generate_binary, eval_univariate, evaluate_indices
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
    proof = SumcheckProof(Scalar.zero(), [], [])
    
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
        proof.coefficients.append(g_j.get_all_coefficients())
    
    # This final challenge is not used but we need to get it to make the transcript consistent, because verifier will squeeze the final challenge
    transcript.get_and_append_challenge(b"final_challenge")
    
    return proof

# TODO accommodate +1 -1 case 
def verify_sumcheck(proof: SumcheckProof, transcript: Transcript, g: polynomial) -> bool:
    """  
    params:
    proof: SumcheckProof
    transcript: to non interactively generate randomness
    g: the polynomial to verify

    Note:
    - Verifier either have a oracle query to g or calculate g herself, this implementation is for the case that verifier calculate g herself
    """    

    # round 1 C_1 ?= g_j(0) + g_j(1)
    # round 2 to round v: g_j-1(r_j-1) ?= g_j(0) + g_j(1)
    expected = proof.claim
    for round in range(1, g.num_var()):
        q_zero = eval_univariate(proof.coefficients[round - 1], Scalar.zero())
        q_one = eval_univariate(proof.coefficients[round - 1], Scalar.one())
        if q_zero + q_one != expected:
            return False
        if append_squeeze(transcript, proof.coefficients[round - 1]) != proof.r[round - 1]:
            return False
        expected = eval_univariate(proof.coefficients[round - 1], proof.r[round - 1])
    
    # Final check: g_v(r_v) ?= g(r1, r2, ..., rv)
    if g is None:
        raise ValueError("g must be provided in default sumcheck")
    g_result = polynomial(g.terms[:], g.constant)
    final_challenge = transcript.get_and_append_challenge(b"final_challenge") # FIXME: this trigger error in fractional gkr
    proof.r.append(final_challenge)
    g_result = g_result.evaluate(proof.r)
    if g_result == eval_univariate(proof.coefficients[g.num_var() - 1], final_challenge):
        return True
    return False
