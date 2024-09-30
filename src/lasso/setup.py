import random
import py_ecc.bn128 as b
from dataclasses import dataclass
from src.common_util.curve import Scalar, G1Point, G2Point, ec_lincomb
from src.common_util.mle_poly import polynomial, term

@dataclass
class mvKzgProof():
    w: list[G1Point]

@dataclass
class Setup(object):
    length: int
    max_degree: int
    powers_of_x: list[G1Point]
    powers_of_x2: list[G2Point]

    def __init__(self, length: int, max_degree: int):
        self.generate_srs(length, max_degree)

    @classmethod
    def generate_srs(self, length: int, max_degree: int):
        self.max_degree = max_degree
        print("Start to generate structured reference string")
        # random number, normally comes from MPC(Multi-Party Computation)
        t_list = [random.randint(1, Scalar.field_modulus-1) for _ in range(length)]
        powers_of_x = [b.G1]
        for t in t_list:
            now_len = len(powers_of_x)
            for i in range(1, max_degree+1):
                power = t**i
                for j in range(now_len):
                    powers_of_x.append(b.multiply(powers_of_x[j], power))
        '''
        powers_of_x = 
        [G1, G1 * t1, ..., G1 * t1**maxd,
        G1 * t2, G1 * t1 * t2, ..., G1 * t1**maxd,
        ...
        G1 * t2**maxd, G1 * t1 * t2**maxd, ..., G1 * t1**maxd * t2**maxd,
        ...]
        '''
        
        powers_of_x2 = [0 for _ in range(length+1)]
        powers_of_x2[0] = b.G2
        for i in range(length):
            powers_of_x2[i+1] = b.multiply(b.G2, t_list[i])

        print("Finished to generate structured reference string")
        self.powers_of_x = powers_of_x
        self.powers_of_x2 = powers_of_x2

    @classmethod
    def commit_g1(self, poly: polynomial, n: int) -> G1Point:
        mexp = poly.get_multi_expansion(n)
        comb_list = []
        for term in mexp.terms:
            if term[0] != Scalar(0):
                index = 0
                now = 1
                for i in range(1, len(term)):
                    index += now*term[i]
                    now *= (self.max_degree+1)
                comb_list.append((self.powers_of_x[index.n], term[0]))
        return ec_lincomb(comb_list)
    
    @classmethod
    def commit_g2(self, term: term) -> G2Point:
        index = term.x_i
        comb_list = [(self.powers_of_x2[index], term.coeff), (b.G2, term.const)]
        return ec_lincomb(comb_list)
    
    @classmethod
    def prove(self, poly: polynomial, point: list[Scalar], eval: Scalar) -> mvKzgProof:
        n = len(point)
        p = polynomial(poly.terms[:], poly.constant)
        w = []
        for i in range(n):
            q = p.quotient_single_term(point[i], i+1)
            g = self.commit_g1(q, n)
            # Note: g would be None when q is zero polynomial
            w.append(g)
            p = p.eval_i(point[i], i+1)
        return mvKzgProof(w)
    
    @classmethod
    def eval_and_prove(self, poly: polynomial, point: list[Scalar]) -> tuple[Scalar, mvKzgProof]:
        n = len(point)
        p = polynomial(poly.terms[:], poly.constant)
        w = []
        for i in range(n):
            q = p.quotient_single_term(point[i], i+1)
            w.append(self.commit_g1(q, n))
            p = p.eval_i(point[i], i+1)
        return p.constant, mvKzgProof(w)
    
    @classmethod
    def verify(self, commitment: G1Point, point: list[Scalar], eval: Scalar, proof: mvKzgProof) -> bool:
        comb_lhs = ec_lincomb([(commitment, Scalar(1)), (b.G1, -eval)])
        pairing_lhs = b.pairing(b.G2, comb_lhs)
        pairing_rhs = 1
        for i, (a, w) in enumerate(zip(point, proof.w)):
            if w != None:
                comb_rhs = self.commit_g2(term(Scalar(1), i+1, -a))
                pairing_rhs *= b.pairing(comb_rhs, w)
        return pairing_lhs == pairing_rhs
    
