import unittest
from src.common_util.sumcheck import prove_sumcheck, verify_sumcheck, reduce_multiple_polynomial
from src.common_util.curve import Scalar
from src.common_util.mle_poly import (
    polynomial, term, monomial, 
    get_multi_ext, 
    eval_univariate,
)
from src.logupgkr.transcript import Transcript # TODO change to common transcript

def test_polynomial():
    a = Scalar(2)
    b = Scalar(3)
    c = Scalar(4)
    d = Scalar(5)
    e = Scalar(1)

    term1 = term(coeff=a, i=1, const=e)  # (2 * x_1 + 1)
    term2 = term(coeff=b, i=2, const=c)  # (3 * x_2 + 4)
    term3 = term(coeff=a, i=3, const=a)  # (2 * x_3 + 2)

    monomial1 = monomial(coeff=d, terms=[term1, term2, term3])  # 5 * ((2 * x_1 + 1) * (3 * x_2 + 4) * (2 * x_3 + 2))
    poly = polynomial(terms=[monomial1]) # 5 * ((2 * x_1 + 1) * (3 * x_2 + 4) * (2 * x_3 + 2)) + 6
    return poly


def test_polynomial2():
    a = Scalar(2)
    b = Scalar(3)
    c = Scalar(4)
    d = Scalar(5)
    e = Scalar(1)

    term1 = term(coeff=a, i=1, const=e)  # (2 * x_1 + 1)
    term2 = term(coeff=b, i=2, const=c)  # (3 * x_2 + 4)
    
    monomial1 = monomial(coeff=d, terms=[term1, term2])  # 5 * ((2 * x_1 + 1) * (3 * x_2 + 4))
    # you can't have extra const term in this polynomial
    poly = polynomial(terms=[monomial1]) # 5 * ((2 * x_1 + 1) * (3 * x_2 + 4))
    return poly

def test_polynomial3():
    a = Scalar(2)
    d = Scalar(5)
    e = Scalar(1)
    term1 = term(coeff=a, i=1, const=e)  # (2 * x_1 + 1)
    monomial1 = monomial(coeff=d, terms=[term1])  # 5 * (2 * x_1 + 1)
    poly = polynomial(terms=[monomial1]) # 5 * (2 * x_1 + 1)
    return poly

def test_polynomial_function2(values):
    x_1, x_2  = values
    return 5 * (2 * x_1 + 1) * (3 * x_2 + 4)

zero = Scalar.zero()
one = Scalar.one()

def mult_layer_zero(arr: list[Scalar]) -> Scalar:
    if len(arr) == 3:
        if arr == [zero, zero, one]:
            return one
        elif arr == [one, one, zero]:
            return one
        elif arr == [zero, one, zero]: # [0, 1, 0]
            return one
        else:
            return zero
    else:
        raise ValueError("Invalid input length")

def W0Func(bitstring):
  if bitstring == [zero]:
    return Scalar(36)
  elif bitstring == [one]:
    return Scalar(6)

def W1Func(bitstring):
  if bitstring == [zero, zero]:
    return Scalar(9)
  elif bitstring == [zero, one]:
    return Scalar(4)
  elif bitstring == [one, zero]:
    return Scalar(6)
  elif bitstring == [one, one]:
    return Scalar(1)

class TestSumcheck(unittest.TestCase):
    def test_t(self):
        def D_func(arr: list[Scalar]) -> Scalar:
            if arr == [Scalar.zero()]:
                return Scalar(36)
            elif arr == [Scalar.one()]:
                return Scalar(6)
            else:
                raise ValueError("Invalid input")
        print(get_multi_ext(D_func, 1))

    def test_reduce_multiple_polynomial(self):
        """  
        proof argument zero knowledge 4.5.2 
        """
        term1 = term(coeff=Scalar(3), i=1, const=Scalar(0))  # 3 * x_1
        term2 = term(coeff=Scalar(1), i=2, const=Scalar(0))  # x_2
        term3 = term(coeff=Scalar(2), i=2, const=Scalar(0))  # 3 * x_2
        
        monomial1 = monomial(coeff=Scalar(1), terms=[term1, term2])  # 3 * x_1 * x_2
        monomial2 = monomial(coeff=Scalar(1), terms=[term3])  # 3 * x_2
        w = polynomial(terms=[monomial1, monomial2], c=Scalar(0))
        b = [Scalar(2), Scalar(4)]
        c = [Scalar(3), Scalar(2)]

        l = reduce_multiple_polynomial(b, c, w)
        l_one = eval_univariate(l, one)
        l_zero = eval_univariate(l, zero)
        
        assert l_one == w.evaluate(c)
        assert l_zero == w.evaluate(b)

    def test_prove_sumcheck(self):
        transcript = Transcript(b"test_sumcheck")
        f = test_polynomial2()
        prove_sumcheck(f, transcript)

    def test_verify_sumcheck(self):
        transcript = Transcript(b"test_sumcheck")
        f = test_polynomial()
        proof = prove_sumcheck(f, transcript)        
        transcript2 = Transcript(b"test_sumcheck")
        self.assertTrue(verify_sumcheck(proof, transcript2, f), "Verification failed")
    
    def test_verify_sumcheck2(self):
        transcript = Transcript(b"test_sumcheck")
        f = test_polynomial2()
        proof = prove_sumcheck(f, transcript)        
        transcript2 = Transcript(b"test_sumcheck")
        self.assertTrue(verify_sumcheck(proof, transcript2, f), "Verification failed")

    def test_verify_sumcheck3(self):
        transcript = Transcript(b"test_sumcheck")
        f = test_polynomial3()
        proof = prove_sumcheck(f, transcript)        
        transcript2 = Transcript(b"test_sumcheck")
        self.assertTrue(verify_sumcheck(proof, transcript2, f), "Verification failed")