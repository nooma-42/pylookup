from dataclasses import dataclass
from src.common_util.poly import Polynomial, Basis
from src.common_util.curve import Scalar
from src.plookup.program import Params, aggregate, aggregate_poly
from src.plookup.setup import Setup
from src.plookup.transcript import Transcript, Message1, Message2, Message3, Message4, Message5

@dataclass
class Proof:
    msg_1: Message1
    msg_2: Message2
    msg_3: Message3
    msg_4: Message4
    msg_5: Message5

    def flatten(self):
        proof = {}
        # msg_1
        proof["f_comm"] = self.msg_1.f_comm
        proof["h1_comm"] = self.msg_1.h1_comm
        proof["h2_comm"] = self.msg_1.h2_comm
        # msg_2
        proof["z_comm"] = self.msg_2.z_comm
        # msg_3
        proof["q_comm"] = self.msg_3.q_comm
        # msg_4
        proof["f_eval"] = self.msg_4.f_eval
        proof["h1_eval"] = self.msg_4.h1_eval
        proof["h2_eval"] = self.msg_4.h2_eval
        proof["z_eval"] = self.msg_4.z_eval
        proof["h1_g_eval"] = self.msg_4.h1_g_eval
        proof["h2_g_eval"] = self.msg_4.h2_g_eval
        proof["z_g_eval"] = self.msg_4.z_g_eval
        # msg_5
        proof["agg_witness_comm"] = self.msg_5.agg_witness_comm
        proof["agg_g_witness_comm"] = self.msg_5.agg_g_witness_comm
        
        return proof

@dataclass
class Prover:
    # the notations follow the plookup paper (https://eprint.iacr.org/2020/315.pdf)
    table: list[int]
    n: int
    H: list[Scalar] # [1, ..., g^n]
    # Note that H in the paper is [g, g^2, ..., g^{n+1}=1]
    f: list[Scalar]
    t: list[Scalar]

    def __init__(self, setup: Setup, params: Params):
        self.setup = setup
        self.table = params.table
        self.n = params.order - 1
        self.H = params.roots
        # vanish = x^(n+1) - 1
        self.vanish = Polynomial([Scalar(-1)]+[Scalar(0)]*self.n+[Scalar(1)], Basis.MONOMIAL)

    def prove(self, witness: list[int]):
        transcript = Transcript(b"plonk_plookup")
        # Round 1
        msg_1 = self.round_1(witness)

        self.beta, self.gamma = transcript.round_1(msg_1)
        # Round 2
        # alpha is preserved for multiple tables as in the paper
        msg_2 = self.round_2()
        
        # The paper assumed an ideal party to do the check
        # We use kzg commitment to do the check
        # reference: https://github.com/kevaundray/plookup
        self.delta = transcript.round_2(msg_2)
        # Round 3
        # generate the kzg proof of the equations
        # use delta to aggregate the proof
        msg_3 = self.round_3()

        self.zeta = transcript.round_3(msg_3, self.n+1)
        # Round 4
        # evaluate the polynomials at a random point zeta
        # generate the kzg proof of the evaluations
        msg_4 = self.round_4()
        
        self.eps = transcript.round_4(msg_4)
        # Round 5
        # generate the kzg proof of the evaluations
        # use delta to aggregate the proof
        msg_5 = self.round_5()

        return Proof(msg_1, msg_2, msg_3, msg_4, msg_5)

    def round_1(self, witness: list[int]) -> Message1:
        assert(len(witness) <= self.n)
        # pad witness to length n
        witness += [witness[-1]] * (self.n - len(witness))
        # pad f to length n+1; otherwise, we can't set the Polynomial with Basis.LAGRANGE
        # f is of degree n, not n-1. To make it with degree n-1, we can have f % Ln.
        # but it doesn't seems necessary to do that
        self.f = list(map(Scalar, witness))
        self.f.append(self.f[-1])
        self.f_poly = Polynomial(self.f, Basis.LAGRANGE)
        self.t = list(map(Scalar, self.table))
        self.t_poly = Polynomial(self.t, Basis.LAGRANGE)
        self.s = list(map(Scalar, Prover.sorted_by_table(witness, self.table)))
        self.h1 = Polynomial(self.s[:self.n+1], Basis.LAGRANGE)
        self.h2 = Polynomial(self.s[self.n:], Basis.LAGRANGE)
        self.f_comm = self.setup.commit_g1(self.f_poly)
        self.h1_comm = self.setup.commit_g1(self.h1)
        self.h2_comm = self.setup.commit_g1(self.h2)
        return Message1(self.f_comm, self.h1_comm, self.h2_comm)
    
    def round_2(self):
        self.z = self.compute_polynomial(self.beta, self.gamma)
        self.z_comm = self.setup.commit_g1(self.z)
        return Message2(self.z_comm)
    
    def round_3(self):
        self.q = self.quotient_poly()
        self.q_comm = self.setup.commit_g1(self.q)
        return Message3(self.q_comm)
    
    def round_4(self):
        self.f_eval = self.f_poly.eval(self.zeta)
        self.t_eval = self.t_poly.eval(self.zeta)
        self.h1_eval = self.h1.eval(self.zeta)
        self.h2_eval = self.h2.eval(self.zeta)
        self.z_eval = self.z.eval(self.zeta)
        self.q_eval = self.q.eval(self.zeta) # don't need to send this
        self.g_zeta = self.H[1] * self.zeta  # g * zeta
        self.t_g_eval = self.t_poly.eval(self.g_zeta)
        self.h1_g_eval = self.h1.eval(self.g_zeta)
        self.h2_g_eval = self.h2.eval(self.g_zeta)
        self.z_g_eval = self.z.eval(self.g_zeta)
        return Message4(
            self.f_eval, self.h1_eval, self.h2_eval, self.z_eval,
            self.h1_g_eval, self.h2_g_eval, self.z_g_eval
        )
    
    def round_5(self):
        agg_poly = aggregate_poly(self.eps, [self.f_poly, self.h1, self.h2, self.z, self.q]).to_mononial()
        agg_eval = aggregate(self.eps, [self.f_eval, self.h1_eval, self.h2_eval, self.z_eval, self.q_eval])
        self.agg_witness = (agg_poly - agg_eval) / Polynomial([-self.zeta, Scalar(1)], Basis.MONOMIAL)
        self.agg_witness_comm = self.setup.commit_g1(self.agg_witness)
        agg_g_poly = aggregate_poly(self.eps, [self.h1, self.h2, self.z]).to_mononial()
        agg_g_eval = aggregate(self.eps, [self.h1_g_eval, self.h2_g_eval, self.z_g_eval])
        self.agg_g_witness = (agg_g_poly - agg_g_eval) / Polynomial([-self.g_zeta, Scalar(1)], Basis.MONOMIAL)
        self.agg_g_witness_comm = self.setup.commit_g1(self.agg_g_witness)
        return Message5(self.agg_witness_comm, self.agg_g_witness_comm)

    @staticmethod
    def sorted_by_table(witness: list[int], table: list[int]):
        data = table + witness
        index = {}
        for i, t in enumerate(table):
            index[t] = i
        for w in witness:
            assert(w in index)
        return sorted(data, key=lambda x: index[x])
    
    def compute_polynomial(self, beta: Scalar, gamma: Scalar):
        value = [Scalar(1)]
        numer = Scalar(1)
        denom = Scalar(1)
        for i in range(1, self.n):
            numer = numer * (Scalar(1)+beta) * (gamma+self.f[i-1]) \
                * (gamma*(Scalar(1)+beta)+self.t[i-1]+beta*self.t[i])
            denom = denom * (gamma*(Scalar(1)+beta)+self.s[i-1]+beta*self.s[i]) \
                * (gamma*(Scalar(1)+beta)+self.s[self.n+i-1]+beta*self.s[self.n+i])
            value.append(numer/denom)

        value.append(Scalar(1))
        return Polynomial(value, Basis.LAGRANGE)

    def quotient_poly(self) -> Polynomial:
        L0 = Polynomial([Scalar(1) if i == 0 else Scalar(0) for i in range(self.n+1)], Basis.LAGRANGE).ifft()      # same as L_1(x) in paper
        Ln = Polynomial([Scalar(1) if i == self.n else Scalar(0) for i in range(self.n+1)], Basis.LAGRANGE).ifft() # same as L_{n+1}(x) in paper
        Z = self.z.ifft()
        # L0(x)(Z(x)-1)
        poly_a = L0 * (Z - Scalar(1))
        # lhs - rhs
        poly_b = self.get_poly_b()
        # Ln(x)(h1(x)-h2(gx))
        poly_c = Ln * (self.h1 - self.h2.shift(1)).ifft()
        # Ln(x)(Z(x)-1)
        poly_d = Ln * (Z - Scalar(1))
        
        agg = aggregate_poly(self.delta, [poly_a, poly_b, poly_c, poly_d])
        return agg / self.vanish

    def get_poly_b(self) -> Polynomial:
        front = Polynomial([-self.H[self.n], Scalar(1)], Basis.MONOMIAL)
        # In the paper, front = x - g^{n+1}, which equals to x - 1
        # Here we have front = x - H[n], which is actually x - g^n
        lhs = front * self.z.ifft() * (Scalar(1) + self.beta) * (self.f_poly.ifft() + self.gamma) * \
            (self.t_poly + self.t_poly.shift(1) * self.beta + self.gamma * (Scalar(1) + self.beta)).ifft()
        rhs = front * self.z.shift(1).ifft() * \
            (self.h1 + self.h1.shift(1) * self.beta + self.gamma * (Scalar(1) + self.beta)).ifft() * \
            (self.h2 + self.h2.shift(1) * self.beta + self.gamma * (Scalar(1) + self.beta)).ifft()
        return lhs - rhs
