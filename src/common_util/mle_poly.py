# Code copied from https://github.com/jeong0982/gkr
from src.common_util.curve import Scalar
from typing import Callable
from src.common_util.util import length_expansion

class term:
    def __init__(self, coeff: Scalar, i: int, const: Scalar) -> None:
        self.coeff = coeff
        self.x_i = i
        self.const = const
    
    def __eq__(self, other):
        if not isinstance(other, term):
            return False
        if self.coeff != other.coeff:
            return False
        if self.x_i != other.x_i:
            return False
        if self.const != other.const:
            return False
        return True

    def eval(self, x: Scalar):
        return self.coeff * x + self.const

    def is_constant(self):
        if self.coeff == Scalar.zero():
            return True
        else:
            return False
    
    def convert(self):
        return UnivariateExpansion([self.const, self.coeff], 1)

    def __mul__(self, other):
        if isinstance(other, Scalar):
            return term(self.coeff * other, self.x_i, self.const * other)

    def __str__(self):
        return f"({self.coeff} * x_{self.x_i} + {self.const})"

    def __repr__(self):
        return self.__str__()
    
class monomial:
    def __init__(self, coeff: Scalar, terms: list[term]) -> None:
        self.terms: list[term] = terms
        self.coeff = coeff

    def __mul__(self, other):
        return monomial(self.coeff * other.coeff, self.terms + other.terms)

    def __str__(self):
        terms_str = " * ".join([str(term) for term in self.terms])
        return f"{self.coeff} * ({terms_str})"

    def __repr__(self):
        return self.__str__()
    
    def __eq__(self, other):
        if not isinstance(other, monomial):
            return False
        if self.coeff != other.coeff:
            return False
        if len(self.terms) != len(other.terms):
            return False
        for i in range(len(self.terms)):
            if self.terms[i] != other.terms[i]:
                return False
        return True

    def mult(self, n):
        self.coeff *= n

    def apply(self):
        res = self.coeff
        new_terms = []
        if self.coeff == Scalar.zero():
            return Scalar.zero()
        for t in self.terms:
            if t.coeff == Scalar.zero():
                if t.const == Scalar.zero():
                    return Scalar.zero()
                res *= t.const
            else:
                new_terms.append(t)
        if new_terms == []:
            return res
        return monomial(res, new_terms)

    # univariate
    def eval_univariate(self, x: Scalar):
        res = self.coeff
        for t in self.terms:
            res_t = t.eval(x)
            if res_t == Scalar.zero():
                return Scalar.zero()
            else:
                res *= res_t
        return res
    
    def get_expansion(self) -> 'UnivariateExpansion':
        res = self.terms[0].convert() * self.coeff
        if len(self.terms) == 1:
            return res
        else:
            for t in self.terms[1:]:
                res *= t
            return res
        
    def get_multi_expansion(self, v: int) -> 'MultivariateExpansion':
        mexp = const2mexp(self.coeff, v)
        for term in self.terms:
            mexp *= term
        return mexp

class polynomial:
    def __init__(self, terms: list[monomial], c=Scalar.zero()) -> None:
        self.terms = terms
        self.constant = c

    def __add__(self, other):
        if isinstance(other, polynomial):
            return polynomial(self.terms + other.terms, self.constant + other.constant)
        else:
            assert isinstance(other, Scalar)
            return polynomial(self.terms, self.constant + other)

    def __mul__(self, other):
        if isinstance(other, polynomial):
            new_terms = []
            for a in self.terms:
                for b in other.terms:
                    new_terms.append(a * b)
            for a in self.terms:
                if other.constant != Scalar.zero():
                    new_terms.append(monomial(a.coeff * other.constant, a.terms))
            for b in other.terms:
                if self.constant != Scalar.zero():
                    new_terms.append(monomial(b.coeff * self.constant, b.terms))
            new_constant = self.constant * other.constant
            return polynomial(new_terms, new_constant)
        else:
            assert isinstance(other, Scalar)
            new_terms = []
            for a in self.terms:
                if other != Scalar.zero():
                    new_terms.append(monomial(a.coeff * other, a.terms))
            new_constant = self.constant * other
            return polynomial(new_terms, new_constant)

    def eval_i(self, x_i: Scalar, i: int):
        """  
        evaluate variable index i with x_i
        """
        if i == 0:
            raise ValueError("i should start from 1")
        new_terms_poly = []
        new_constant = self.constant
        for mono in self.terms:
            new_terms = []
            result = mono.coeff
            for term in mono.terms:
                if term.x_i == i:
                    subres = term.eval(x_i)
                    if subres == Scalar.zero():
                        new_terms = []
                        result = Scalar.zero()
                        break
                    else:
                        result *= subres
                else:
                    new_terms.append(term)
            if len(new_terms) == 0:
                new_constant += result
            else:
                new_mono = monomial(result, new_terms)
                new_terms_poly.append(new_mono)
        poly = polynomial(new_terms_poly, new_constant).apply_all()
        return poly

    def eval(self, x: list[Scalar]):
        poly = polynomial(self.terms[:], self.constant)
        for i, x_i in enumerate(x):
            poly = poly.eval_i(x_i, i+1)
        return poly.constant

    def shift(self, idx: int):
        new_terms_poly = []
        new_constant = self.constant
        for mono in self.terms:
            new_terms = []
            new_coeff = mono.coeff
            for t in mono.terms:
                new_terms.append(term(t.coeff, t.x_i + idx, t.const))
            new_mono = monomial(new_coeff, new_terms)
            new_terms_poly.append(new_mono)
        poly = polynomial(new_terms_poly, new_constant).apply_all()
        return poly

    def is_univariate(self):
        i = 0
        for term in self.terms:
            for t in term.terms:
                if i == 0:
                    i = t.x_i
                else:
                    if i != t.x_i:
                        return False
                    else:
                        continue
        if i != 0:
            return True
        else:
            return False

    def apply_all(self):
        """  
        Simplify polynomial
        
        Note:
        for example, p1 can be simplified to p2
        p1: 6 * ((3 * x_1 + 4) * (1 * x_1 + 2)) + 3 * ((0 * x_1 + 5) * (1 * x_1 + 2)) + 0
        p2: 6 * ((3 * x_1 + 4) * (1 * x_1 + 2)) + 15 * ((1 * x_1 + 2)) + 0
        """
        new_terms = []
        new_const = self.constant
        for t in self.terms:
            subres = t.apply()
            if isinstance(subres, Scalar):
                new_const += subres
            else:
                new_terms.append(subres)
        return polynomial(new_terms, new_const)

    # for univariate
    def eval_univariate(self, x: Scalar):
        res = Scalar.zero()
        for term in self.terms:
            res += term.eval_univariate(x)
        return res + self.constant

    def get_highest_degree(self):
        highest = 0
        for term in self.terms:
            if len(term.terms) > highest:
                highest = len(term.terms)
        return highest
    
    def get_all_coefficients(self):
        p = self.apply_all()
        exp = p.get_expansion()
        return list(reversed(exp.coeffs))

    def get_expansion(self) -> 'UnivariateExpansion':
        """  
        Expand polynomial to univariate expansion
        Note: 
        1. 5 * ((2 * x_1 + 1) * (3 * x_2 + 4)) expands to 20 * x^0 + 55 * x^1 + 30 * x^2.
        2. 5 * ((3 * x_2 + 4)) + 15 ((3 * x_2 + 4)) + 0 expands to 20 * x^0 + 80 * x^1.
            terms expands to [20, 15] and [60, 45] respectively.
        """
        res = UnivariateExpansion([Scalar.zero()], 0)
        for t in self.terms:
            res += t.get_expansion()
        return res
    
    def get_multi_expansion(self, v: int) -> 'MultivariateExpansion':
        mexp = const2mexp(self.constant, v)
        for mono in self.terms:
            mexp += mono.get_multi_expansion(v)
        return mexp

    def quotient_single_term(self, value: Scalar, i: int):
        '''
        return the quotient of f/(x_i-value)
        '''
        new_terms_poly = []
        new_constant = Scalar(0)
        for mono in self.terms:
            terms = mono.terms.copy()
            coeff = mono.coeff
            while True:
                new_terms = []
                this_coeff = coeff
                next_coeff = coeff
                has_x_i = False
                for term in terms:
                    if has_x_i:
                        new_terms.append(term)
                    else:
                        if term.x_i == i:
                            has_x_i = True
                            this_coeff *= term.coeff
                            next_coeff *= term.eval(value)
                        else:
                            new_terms.append(term)
                if not has_x_i:
                    break
                if len(new_terms) == 0:
                    new_constant += this_coeff
                    break
                else:
                    new_mono = monomial(this_coeff, new_terms)
                    new_terms_poly.append(new_mono)
                    terms = new_terms
                    coeff = next_coeff
                
        poly = polynomial(new_terms_poly, new_constant).apply_all()
        return poly

    def __str__(self):
        terms_str = " + ".join([str(term) for term in self.terms])
        return f"{terms_str} + {self.constant}"

    def __repr__(self):
        return self.__str__()
    
    def __eq__(self, value: object) -> bool:
        if not isinstance(value, polynomial):
            return False
        if len(self.terms) != len(value.terms):
            return False
        for i in range(len(self.terms)):
            if self.terms[i] != value.terms[i]:
                return False
        if self.constant != value.constant:
            return False
        return True

class UnivariateExpansion:
    def __init__(self, coeffs: list[Scalar], deg: int) -> None:
        self.coeffs = coeffs
        self.deg = deg

    def __add__(self, other):
        new_coeffs = []
        highest_deg = self.deg if self.deg >= other.deg else other.deg

        a_c = length_expansion(self.coeffs, highest_deg + 1)
        b_c = length_expansion(other.coeffs, highest_deg + 1)

        for i in range(highest_deg + 1):
            new_coeffs.append(a_c[i] + b_c[i])
        return UnivariateExpansion(new_coeffs, highest_deg)
    
    def __mul__(self, other):
        if isinstance(other, term):
            m = list(map(lambda x: x * other.coeff, self.coeffs))
            m.insert(0, Scalar.zero())
            m_exp = UnivariateExpansion(m, self.deg + 1)
            c = list(map(lambda x: x * other.const, self.coeffs))
            c_exp = UnivariateExpansion(c, self.deg)
            return m_exp + c_exp
        elif isinstance(other, Scalar):
            return UnivariateExpansion(list(map(lambda x: x * other, self.coeffs)), self.deg)
        else:
            raise NotImplementedError

    def __str__(self):
        return " + ".join([f"{self.coeffs[i]}*x^{i}" for i in range(self.deg + 1)])

    def __repr__(self):
        return f"UnivariateExpansion(coeffs={self.coeffs}, deg={self.deg})"

# [[coeff, deg(x_1), ... , deg(x_v)], ...]
class MultivariateExpansion:
    def __init__(self, terms: list[list[Scalar]], v: int) -> None:
        self.terms = terms
        self.v = v
    
    def __mul__(self, other):
        if isinstance(other, term):
            res = []
            for t in self.terms:
                new_t1 = t[:]
                i = other.x_i
                new_t1[i] += 1
                new_t1[0] *= other.coeff
                res.append(new_t1)

                new_t2 = t[:]
                new_t2[0] *= other.const
                res.append(new_t2)
            return MultivariateExpansion(res, self.v)
    
    def __add__(self, other):
        if isinstance(other, MultivariateExpansion):
            assert (self.v == other.v)
            return MultivariateExpansion(self.terms + other.terms, self.v)


# generate input {0, 1}^(bit_count)
def generate_binary(bit_count) -> list[list[Scalar]]:
    binary = []

    def genbin(n, bs=[]):
        if len(bs) == n:
            binary.append(bs)
        else:
            b_zero = bs + [Scalar.zero()]
            b_one = bs + [Scalar.one()]
            genbin(n, b_zero)
            genbin(n, b_one)

    genbin(bit_count)
    return binary

# univariate
def eval_univariate(coeffs: list[Scalar], x: Scalar):
    result = coeffs[0]
    for i in range(1, len(coeffs)):
        result *= x
        result += coeffs[i]
    return result

# for multilinear extension
# w = {0, 1}^v
# multilinear Lagrange basis polynomials
def chi(w: list[Scalar], x: list[Scalar]):
    prod = Scalar.one()
    for i in range(len(x)):
        prod = prod * (x[i]*w[i] + (Scalar.one() - x[i])*(Scalar.one() - w[i]))
    return prod

def chi_w(w: list[Scalar]):
    prod = []
    for i, w_i in enumerate(w):
        if w_i == Scalar.zero():
            prod.append(term(Scalar(-1), i + 1, Scalar(1)))
        elif w_i == Scalar.one():
            prod.append(term(Scalar(1), i + 1, Scalar(0)))
    
    mono = monomial(Scalar.one(), prod)
    return mono

# for f(x) in gkr
def chi_w_from_k(w: list[Scalar], k: int) -> monomial:
    """  
    params:
    w: {0, 1}^v
    k: index of x_i, k = 1 means x_1

    return:
    multilinear extension of chi_w

    Example:
    w = [1, 0, 1]
    k = 2
    Given bn128, the output is:
    1 * ((1 * x_2 + 0) * (21888242871839275222246405745257275088548364400416034343698204186575808495616 * x_3 + 1) * (1 * x_4 + 0))
    """
    prod = []
    for i, w_i in enumerate(w):
        if w_i == Scalar.zero():
            prod.append(term(Scalar(-1), i + k, Scalar(1)))
        elif w_i == Scalar.one():
            prod.append(term(Scalar(1), i + k, Scalar(0)))
        else:
            raise ValueError("Invalid value in w, should be 0 or 1")
    mono = monomial(Scalar.one(), prod)
    return mono

# Similar to chi_w, but extend to w \notin {0, 1}^n
def eq_mle(w: list[Scalar]):
    prod = []
    for i, w_i in enumerate(w):
        prod.append(term(w_i*2-1, i+1, 1-w_i))
    
    mono = monomial(Scalar.one(), prod)
    return mono


def eq_mle_poly(w: list[Scalar]):
    return polynomial([eq_mle(w)])

def eval_ext(f: Callable[[list[Scalar]], Scalar], r: list[Scalar]) -> Scalar:
    w = generate_binary(len(r))
    acc = Scalar.zero()
    for w_i in w:
        acc += f(w_i) * chi(w_i, r)
    return acc

def eval_expansion(f: list[list[Scalar]], r: list[Scalar]) -> Scalar:
    """ 
    Evaluate multivariate polynomial expansion at point r 
    input:  [30, 1, 1], [40, 1, 0], [15, 0, 1], [26, 0, 0]
        representing 30 x1 * x2 + 40 x1 + 15 x2 + 26
    
    TODO add input output example
    """
    assert (len(r) + 1 == len(f[0]))
    res = Scalar.zero()
    for t in f:
        subres = Scalar.zero()
        for i, x in enumerate(t):
            if i == 0:
                subres = t[0]
            else:
                subres *= r[i - 1] ** x
        res += subres
    return res

def get_multi_ext(f: Callable[[list[Scalar]], Scalar], v: int) -> list[list[Scalar]]:
    """
    Return expansion of multivariate polynomial
    
    Parameters:
    input: f()=5 * ((2 * x_1 + 1) * (3 * x_2 + 4)) + 6
        this input expands to 30 x1 * x2 + 40 x1 + 15 x2 + 26
    output:  [30, 1, 1], [40, 1, 0], [15, 0, 1], [26, 0, 0]
    
    Note: 
    coefficient 30, 1 x1, 1 x2 
    """
    w_set = generate_binary(v)
    ext_f = []
    res = []
    
    # get multilinear extension lagrange basis
    for w in w_set:
        res = chi_w(w)
        if f(w) == Scalar.zero():
            continue
        res.mult(f(w))
        ext_f.append(res)

    g = []
    term_pool = dict()

    empty_term = [Scalar.zero()] * (v + 1)
    for term in ext_f:
        subres = MultivariateExpansion([], v)
        for t in term.terms:
            if len(subres.terms) == 0:
                t_expansion1 = empty_term[:]
                t_expansion1[t.x_i] = Scalar.one()
                t_expansion1[0] = term.coeff * t.coeff
                t_expansion2 = empty_term[:]
                t_expansion2[0] = t.const * term.coeff
                subres = MultivariateExpansion([t_expansion1, t_expansion2], v)
            else:
                subres = subres * t
        for one_term in subres.terms:
            if tuple(one_term[1:]) in term_pool:
                idx = term_pool[tuple(one_term[1:])]
                g[idx][0] += one_term[0]
            else:
                term_pool[tuple(one_term[1:])] = len(g)
                g.append(one_term)
    if len(g) == 0:
        g = [empty_term]
        return g
    g_final = []
    for term in g:
        if term[0] != Scalar.zero():
            g_final.append(term)
    return g_final

# r : {0, 1}^v
def get_ext(f: Callable[[list[Scalar]], Scalar], v: int) -> polynomial:
    w_set = generate_binary(v)
    try:
        f(w_set[0])
    except ValueError as e:
        raise ValueError("Invalid input or function") from e
    ext_f = []
    for w in w_set:
        res = chi_w(w)
        if f(w) == Scalar.zero():
            continue
        res.mult(f(w))
        ext_f.append(res)
    return polynomial(ext_f)

def get_ext_from_k(f: Callable[[list[Scalar]], Scalar], v: int, k: int) -> polynomial:
    """  
    Return expansion of multivariate polynomial

    params:
    f: function to evaluate  
    v: numbers of bit in w
    k: index of x_i, k = 1 means x_1

    example:
    f()=5 * ((2 * x_1 + 1) * (3 * x_2 + 4)) + 6
    you can also pass in a function that takes in a list of scalars and returns a scalar without explicit definition based on the terms
    this input expands to 30 x1 * x2 + 40 x1 + 15 x2 + 26
    """ 
    w_set = generate_binary(v)
    try:
        f(w_set[0])
    except ValueError as e:
        raise ValueError("Invalid input or function") from e
    if k < 1:
        raise ValueError("Invalid index")

    ext_f = []
    for w in w_set:
        res = chi_w_from_k(w, k)
        if f(w) == Scalar.zero():
            continue
        res.mult(f(w))
        ext_f.append(res)
    return polynomial(ext_f)

def get_multi_poly_lagrange(values: list[Scalar], length: int) -> polynomial:
    '''
    get length-variate polynomial with multilinear lagrange basis
    f = \sum_{w \in {0,1}^n} values[w] * chi_w(w)
    '''
    w_set = generate_binary(length)
    assert(len(w_set) == len(values))
    ext_f = []
    for w, val in zip(w_set, values):
        res = chi_w(w)
        if val == Scalar.zero():
            continue
        res.mult(val)
        ext_f.append(res)
    poly = polynomial(ext_f)
    return poly

def get_single_term_poly(term: term) -> polynomial:
    mono = monomial(Scalar(1), [term])
    return polynomial([mono])

def const2mexp(value: Scalar, v: int) -> MultivariateExpansion:
    term = [Scalar(0) for _ in range(v+1)]
    term[0] = value
    return MultivariateExpansion([term], v)
one = Scalar(1)
neg_one = Scalar(-1)

def generate_combinations(length) -> list[list[Scalar]]:
    """  
    TODO: Add description
    """
    if length == 0:
        return [[]]
    else:
        result = []
        for combination in generate_combinations(length - 1):
            result.append(combination + [neg_one])
            result.append(combination + [one])
        return result
    
def reduce_multiple_polynomial(b: list[Scalar], c: list[Scalar], w: polynomial) -> list[Scalar]:
    """  
    Reduce multiple polynomial evaluation to one

    params:
    b, c: two points on hypercube
    w: multilinear evaluation polynomial

    Return:
    w(l()): the restriction of W to l

    Example:
    b = (2, 4) c=(3, 2)
    w = 3x1x2 + 2x2
    l(0) = b, l(1) = c, t -> (t + 2, 4 - 2t)
    the restriction of W to l is 3(t + 2)(4 - 2t) + 2(4 - 2t) = -6t^2 - 4t + 32
    
    Note: 
    1. 4.5.2 in Proof Argument and Zero Knowledge by Justin Thaler
    2. This implementation only consider 2 evaluations
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

def ell(p1: list[Scalar], p2: list[Scalar], t: Scalar) -> list[Scalar]:
    """  
    reduce verification at two points into verification at a single point

    Params:
    p1, p2: two points on hypercube
    t: random input chosen by the verifier, this input to l and get next layer randomness. r_i+1 = l(r*)
    
    Returns:
    r_i+1: randomness for next layer

    Example:
    p1 = b*, p2 = c*, t = r*
    l(r*) = b* + (r*) * (c* - b*)

    Note:
    ell(p1, p2, t) = p1 + t * (p2 - p1), which represents the evaluation of a polynomial at the point ell(p1, p2, t) \
        using the linear function l(x) = p1 + x * (p2 - p1), i.e. l(0) = p1 and l(1) = p2
    """
    consts = p1
    output = [Scalar.zero()]*len(p2)
    other_term = [Scalar.zero()]*len(p2)
    for i in range(len(p2)):
        other_term[i] = p2[i] - consts[i]
    for i in range(len(p2)):
        output[i] = consts[i] + t*other_term[i]
    return output
