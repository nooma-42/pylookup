# Code copied from https://github.com/jeong0982/gkr
#mle sumcheck instead of binary
from src.common_util.mle_poly import polynomial, generate_binary, eval_univariate
from src.common_util.curve import Scalar
from src.common_util.util import *

def prove_sumcheck(g: polynomial, v: int, offset: int):
    """
    g: the polynomial to prove
    v: number of variables
    offset: index to start from e.g. x_5: evaluate g at x_5, x_6, ... x_v
    NOTE: 
    1. the offset begins from 0, meaning index begins from x_2, because i + 2 + start, because we make x_1 a variable in the first round
    2. this notation follows Proof Argument and Zero Knowledge by Justin Thaler
    """
    proof = []
    r = []
    # first round
    # g1(X1)=∑(x2,⋯,xv)∈{0,1}^v g(X_1,x_2,⋯,x_v)    
    g_1 = polynomial([])
    assignments = generate_binary(v - 1)

    for assignment in assignments:
        g_1_sub = polynomial(g.terms[:], g.constant)
        
        # Loop through every bit of the assignment
        for i, x_i in enumerate(assignment):
            idx = i + 2 + offset # the offset begins from 0, meaning index begins from x_2, because i + 2 + start
            g_1_sub = g_1_sub.eval_i(x_i, idx)
        g_1 += g_1_sub
    proof.append(g_1.get_all_coefficients())

    r_1 = Scalar(sum(list(map(lambda x : int(x), g_1.get_all_coefficients())))) # FIXME: sum in this line should be hash
    r.append(r_1)

    # 1 < j < v round
    for j in range(1, v - 1):
        g_j = polynomial(g.terms[:], g.constant)
        assignments = generate_binary(v - j - 1)
        for i, r_i in enumerate(r):
            idx = i + 1 + offset
            g_j = g_j.eval_i(r_i, idx)
        
        res_g_j = polynomial([])
        for assignment in assignments:
            g_j_sub = polynomial(g_j.terms[:], g_j.constant)
            for k, x_i in enumerate(assignment):
                idx = j + k + offset + 1
                g_j_sub = g_j_sub.eval_i(x_i, idx)
            res_g_j += g_j_sub
        proof.append(res_g_j.get_all_coefficients())

        r_n = Scalar(sum(list(map(lambda x : int(x), proof[len(proof) - 1]))))
        r.append(r_n)

    # last round
    g_v = polynomial(g.terms[:], g.constant)
    for i, r_i in enumerate(r):
        idx = i + 1 + offset
        g_v = g_v.eval_i(r_i, idx)
    proof.append(g_v.get_all_coefficients())

    r_v = Scalar(sum(list(map(lambda x : int(x), proof[len(proof) - 1]))))
    r.append(r_v)

    return proof, r

def verify_sumcheck(claim: Scalar, proof: list[list[Scalar]], r: list[Scalar], v: int):
    bn = len(proof)
    if(v == 1 and (eval_univariate(proof[0], Scalar.zero()) + eval_univariate(proof[0], Scalar.one())) == claim):
        return True
    expected = claim
    for i in range(bn):
        q_zero = eval_univariate(proof[i], Scalar.zero())
        q_one = eval_univariate(proof[i], Scalar.one())

        if q_zero + q_one != expected:
            return False
        if Scalar(sum(list(map(lambda x : int(x), proof[i])))) != r[i]:
            return False
        expected = eval_univariate(proof[i], r[i])

    return True

def verify_sumcheck_with_eval(claim: Scalar, proof: list[list[Scalar]], r: list[Scalar], v: int):
    # verify sumcheck and return g(r)
    bn = len(proof)
    expected = claim
    for i in range(bn):
        q_zero = eval_univariate(proof[i], Scalar.zero())
        q_one = eval_univariate(proof[i], Scalar.one())

        if q_zero + q_one != expected:
            return False, expected
        if Scalar(sum(list(map(lambda x : int(x), proof[i])))) != r[i]:
            return False, expected
        expected = eval_univariate(proof[i], r[i])

    return True, expected