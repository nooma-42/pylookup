from dataclasses import dataclass
from src.common_util.curve import Scalar, G1Point

# This is a simple SOS table that decompose the table 
class SOSTable:
    l: int
    c: int
    k: int
    alpha: int
    tables: list[list[int]]

    def __init__(self, l: int, c: int, k: int, tables: list[list[int]]):
        self.l = l
        self.c = c
        self.k = k
        self.alpha = k * c
        self.tables = tables
        assert(len(tables) == self.alpha)

    def g_func(self, r: list):
        assert(len(r) == self.alpha)
        '''
        The g function.
        r could be a list of Scalar or poly.Polynomial or mle_poly.polynomial.
        ret would be the same type as r_1.
        Here we have g(r_1, ..., r_c) = 1 + r_1 + r_2 * 2**l + ... + r_c * 2**(l*(c-1))
            that represent the table [1, 2, ..., 2**(l*c)].
        Need to override this function.
        '''
        ret = Scalar(1)
        mul = Scalar(1)
        for i in range(self.alpha):
            ret = r[i] * mul + ret
            mul *= Scalar(2**self.l)
        return ret

    def get_index(self, value: int):
        '''
        Return the index of each subtable for any element in the table.
        With the SOS structure, we should be able to get the indexes 
            without iterating through the whole table.
        Here we return the indexes for the element in the table [1, 2, ..., 2**(l*c)]
        Need to override this function
        '''
        val = value - 1
        index = []
        for i in range(self.c):
            index.append(val % (2**self.l))
            val //= (2**self.l)
        return index

class Params:
    table: SOSTable

    def __init__(self, table: SOSTable):
        self.table = table

@dataclass
class GrandProductData:
    # See https://eprint.iacr.org/2020/1275.pdf, Section 5
    f_0_r: Scalar    # f(0, r)
    f_1_r: Scalar    # f(1, r)
    f_r_0: Scalar    # f(r, 0)
    f_r_1: Scalar    # f(r, 1)
    product: Scalar  # f(1, .., 1, 0)
    f_0_r_proof: G1Point
    f_1_r_proof: G1Point
    f_r_0_proof: G1Point
    f_r_1_proof: G1Point
    product_proof: G1Point

def log_ceil(n: int):
    # return smallest int that >= log(n)
    return len(bin(n-1))-2

def hash_tuple(element: tuple[Scalar, Scalar, Scalar], tau: Scalar, gamma: Scalar) -> Scalar:
    return element[0]*gamma*gamma + element[1]*gamma + element[2] - tau
