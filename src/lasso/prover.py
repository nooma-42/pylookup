from dataclasses import dataclass
from src.common_util.curve import Scalar
from src.common_util.mle_poly import polynomial, get_multi_poly_lagrange, eq_mle_poly
from src.common_util.sumcheck import prove_sumcheck
from src.lasso.program import Params, SOSTable, GrandProductData, log_ceil, hash_tuple
from src.lasso.setup import Setup
from src.lasso.transcript import Transcript, Message1, Message2, Message3, Message4, Message5

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
        proof["a_comm"] = self.msg_1.a_comm
        proof["logm"] = self.msg_1.logm
        proof["dim_comm"] = self.msg_1.dim_comm
        # msg_2
        proof["a_eval"] = self.msg_2.a_eval
        proof["a_eval_proof"] = self.msg_2.a_eval_proof
        proof["E_comm"] = self.msg_2.E_comm
        proof["read_ts_comm"] = self.msg_2.read_ts_comm
        proof["final_cts_comm"] = self.msg_2.final_cts_comm
        # msg_3
        proof["h_sumcheck_proof"] = self.msg_3.h_sumcheck_proof
        proof["rz"] = self.msg_3.rz
        proof["E_eval"] = self.msg_3.E_eval
        proof["E_eval_proof"] = self.msg_3.E_eval_proof
        # msg_4
        proof["S0_comm"] = self.msg_4.S0_comm
        proof["S_comm"] = self.msg_4.S_comm
        proof["RS_comm"] = self.msg_4.RS_comm
        proof["WS_comm"] = self.msg_4.WS_comm
        # msg_5
        proof["S0_sumcheck_proof"] = self.msg_5.S0_sumcheck_proof
        proof["S_sumcheck_proof"] = self.msg_5.S_sumcheck_proof
        proof["RS_sumcheck_proof"] = self.msg_5.RS_sumcheck_proof
        proof["WS_sumcheck_proof"] = self.msg_5.WS_sumcheck_proof
        proof["r_prime"] = self.msg_5.r_prime
        proof["r_prime2"] = self.msg_5.r_prime2
        proof["r_prime3"] = self.msg_5.r_prime3
        proof["r_prime4"] = self.msg_5.r_prime4
        proof["S0_data"] = self.msg_5.S0_data
        proof["S_data"] = self.msg_5.S_data
        proof["RS_data"] = self.msg_5.RS_data
        proof["WS_data"] = self.msg_5.WS_data
        proof["E_eval2"] = self.msg_5.E_eval2
        proof["dim_eval"] = self.msg_5.dim_eval
        proof["read_ts_eval"] = self.msg_5.read_ts_eval
        proof["final_cts_eval"] = self.msg_5.final_cts_eval
        proof["E_eval2_proof"] = self.msg_5.E_eval2_proof
        proof["dim_eval_proof"] = self.msg_5.dim_eval_proof
        proof["read_ts_eval_proof"] = self.msg_5.read_ts_eval_proof
        proof["final_cts_eval_proof"] = self.msg_5.final_cts_eval_proof
        return proof

@dataclass
class Prover:
    # the notations follow the lasso paper (https://eprint.iacr.org/2023/1216.pdf)
    table: SOSTable
    l: int
    c: int
    k: int
    alpha: int
    m: int
    logm: int

    def __init__(self, setup: Setup, params: Params):
        self.setup = setup
        self.table = params.table
        self.l = self.table.l
        self.c = self.table.c
        self.k = self.table.k
        self.alpha = self.table.alpha

    def prove(self, witness: list[int]):
        transcript = Transcript(b"lasso")
        # Round 1
        msg_1 = self.round_1(witness)

        self.r = transcript.round_1(msg_1)
        # Round 2
        msg_2 = self.round_2()
        
        transcript.round_2(msg_2)
        # Round 3
        msg_3 = self.round_3()

        self.tau, self.gamma = transcript.round_3(msg_3)
        # Round 4
        msg_4 = self.round_4()

        transcript.round_4(msg_4)
        # Round 5
        msg_5 = self.round_5()

        return Proof(msg_1, msg_2, msg_3, msg_4, msg_5)

    def round_1(self, witness: list[int]) -> Message1:
        self.m = len(witness)
        self.logm = log_ceil(self.m)
        assert(self.logm <= self.l)

        self.a = [Scalar(0) for _ in range(2**self.logm)]
        for i in range(self.m):
            self.a[i] = Scalar(witness[i])
        self.a_poly = get_multi_poly_lagrange(self.a, self.logm)
        self.a_comm = self.setup.commit_g1(self.a_poly, self.logm)
        self.indexes = []
        for w in witness:
            self.indexes.append(self.table.get_index(w))

        self.dim_poly, self.dim_values = [], []
        for i in range(self.c):
            values = [0 for _ in range(2**self.logm)]
            for j in range(self.m):
                values[j] = self.indexes[j][i]
            self.append_poly_and_values(self.dim_poly, self.dim_values, values, self.logm)

        self.dim_comm = [self.setup.commit_g1(poly, self.logm) for poly in self.dim_poly]
        return Message1(self.a_comm, self.logm, self.dim_comm)
    
    def round_2(self):
        self.a_eval, self.a_eval_proof = self.setup.eval_and_prove(self.a_poly, self.r)

        self.E_poly, self.read_poly, self.write_poly, self.final_poly = [], [], [], []
        self.E_values, self.read_values, self.write_values, self.final_values = [], [], [], []
        for i in range(self.alpha):
            # Offline memory checking, or "Memory in the head"
            # See Spartan(https://eprint.iacr.org/2019/550.pdf), Section 7.2.1
            E_val = [0 for _ in range(2**self.logm)]
            read_ts = [0 for _ in range(2**self.logm)]
            write_cts = [0 for _ in range(2**self.logm)]
            final_cts = [0 for _ in range(2**self.l)]
            for j in range(self.m):
                index = self.indexes[j][i//self.k]
                E_val[j] = self.table.tables[i][index]
                ts = final_cts[index]
                read_ts[j] = ts
                write_cts[j] = ts+1
                final_cts[index] = ts+1

            self.append_poly_and_values(self.E_poly, self.E_values, E_val, self.logm)
            self.append_poly_and_values(self.read_poly, self.read_values, read_ts, self.logm)
            self.append_poly_and_values(self.write_poly, self.write_values, write_cts, self.logm)
            self.append_poly_and_values(self.final_poly, self.final_values, final_cts, self.l)
        
        self.E_comm = [self.setup.commit_g1(poly, self.logm) for poly in self.E_poly]
        self.read_comm = [self.setup.commit_g1(poly, self.logm) for poly in self.read_poly]
        self.final_comm = [self.setup.commit_g1(poly, self.l) for poly in self.final_poly]
        return Message2(self.a_eval, self.a_eval_proof, self.E_comm, self.read_comm, self.final_comm)
    
    def round_3(self):
        # sumcheck protocol on h(k) = eq(r, k) * g(...E_i(k))
        h_poly = eq_mle_poly(self.r) * self.table.g_func(self.E_poly)
        self.h_sumcheck_proof, self.rz = prove_sumcheck(h_poly, self.logm, 1)
        self.E_eval, self.E_eval_proof = [], []
        for E in self.E_poly:
            self.append_eval_and_proof(self.E_eval, self.E_eval_proof, E, self.rz)
        return Message3(self.h_sumcheck_proof, self.rz, self.E_eval, self.E_eval_proof)
    
    def round_4(self):
        self.S0_poly, self.S_poly, self.RS_poly, self.WS_poly = [], [], [], []
        self.S0_comm, self.S_comm, self.RS_comm, self.WS_comm = [], [], [], []
        for i in range(self.alpha):
            S0, S, RS, WS = [], [], [], []
            for j in range(2**self.l):
                S0.append((Scalar(j), Scalar(self.table.tables[i][j]), Scalar(0)))
                S.append((Scalar(j), Scalar(self.table.tables[i][j]), self.final_values[i][j]))
            for j in range(2**self.logm):
                RS.append((self.dim_values[i][j], self.E_values[i][j], self.read_values[i][j]))
                WS.append((self.dim_values[i][j], self.E_values[i][j], self.write_values[i][j]))

            S0_poly = self.grand_product_poly(S0, self.l)
            S_poly = self.grand_product_poly(S, self.l)
            RS_poly = self.grand_product_poly(RS, self.logm)
            WS_poly = self.grand_product_poly(WS, self.logm)
            self.S0_poly.append(S0_poly)
            self.S_poly.append(S_poly)
            self.RS_poly.append(RS_poly)
            self.WS_poly.append(WS_poly)
            self.S0_comm.append(self.setup.commit_g1(S0_poly, self.l+1))
            self.S_comm.append(self.setup.commit_g1(S_poly, self.l+1))
            self.RS_comm.append(self.setup.commit_g1(RS_poly, self.logm+1))
            self.WS_comm.append(self.setup.commit_g1(WS_poly, self.logm+1))

        return Message4(self.S0_comm, self.S_comm, self.RS_comm, self.WS_comm)
    
    def round_5(self):
        self.S0_sumcheck_proof, self.S_sumcheck_proof, self.RS_sumcheck_proof, self.WS_sumcheck_proof = [], [], [], []
        self.r_prime, self.r_prime2, self.r_prime3, self.r_prime4 = [], [], [], []
        self.S0_data, self.S_data, self.RS_data, self.WS_data,  = [], [], [], []
        self.E_eval2, self.dim_eval, self.read_eval, self.final_eval = [], [], [], []
        self.E_eval2_proof, self.dim_eval_proof, self.read_eval_proof, self.final_eval_proof = [], [], [], []
        for i in range(self.alpha):
            self.handle_grand_product_sumcheck(self.S0_sumcheck_proof, self.r_prime, self.S0_poly[i], self.l)
            self.handle_grand_product_sumcheck(self.S_sumcheck_proof, self.r_prime2, self.S_poly[i], self.l)
            self.handle_grand_product_sumcheck(self.RS_sumcheck_proof, self.r_prime3, self.RS_poly[i], self.logm)
            self.handle_grand_product_sumcheck(self.WS_sumcheck_proof, self.r_prime4, self.WS_poly[i], self.logm)
            self.S0_data.append(self.generate_grand_product_data(self.S0_poly[i], self.r_prime[i]))
            self.S_data.append(self.generate_grand_product_data(self.S_poly[i], self.r_prime2[i]))
            self.RS_data.append(self.generate_grand_product_data(self.RS_poly[i], self.r_prime3[i]))
            self.WS_data.append(self.generate_grand_product_data(self.WS_poly[i], self.r_prime4[i]))
            self.append_eval_and_proof(self.E_eval2, self.E_eval2_proof, self.E_poly[i], self.r_prime3[i])
            self.append_eval_and_proof(self.dim_eval, self.dim_eval_proof, self.dim_poly[i//self.k], self.r_prime3[i])
            self.append_eval_and_proof(self.read_eval, self.read_eval_proof, self.read_poly[i], self.r_prime3[i])
            self.append_eval_and_proof(self.final_eval, self.final_eval_proof, self.final_poly[i], self.r_prime2[i])

        return Message5(self.S0_sumcheck_proof, self.S_sumcheck_proof, self.RS_sumcheck_proof, self.WS_sumcheck_proof,
                        self.r_prime, self.r_prime2, self.r_prime3, self.r_prime4,
                        self.S0_data, self.S_data, self.RS_data, self.WS_data,
                        self.E_eval2, self.dim_eval, self.read_eval, self.final_eval,
                        self.E_eval2_proof, self.dim_eval_proof, self.read_eval_proof, self.final_eval_proof)

    def append_poly_and_values(self, poly_list, value_list, values: list, length: int):
        _values = list(map(Scalar, values))
        value_list.append(_values)
        poly_list.append(get_multi_poly_lagrange(_values, length))

    def append_eval_and_proof(self, eval_list, proof_list, poly: polynomial, point: list[Scalar]):
        eval, proof = self.setup.eval_and_prove(poly, point)
        eval_list.append(eval)
        proof_list.append(proof)
    
    def grand_product_poly(self, multiset: list[tuple[Scalar, Scalar, Scalar]], length: int):
        # see https://eprint.iacr.org/2020/1275.pdf, section 5
        f = [hash_tuple(s, self.tau, self.gamma) for s in multiset] # f(0,x) = v(x)
        for i in range(len(f)-1):
            f.append(f[2*i]*f[2*i+1]) # f(1,x) = f(x,0) * f(x,1)
        f.append(Scalar(0))
        poly_f = get_multi_poly_lagrange(f, length+1)
        return poly_f
    
    def grand_product_sumcheck(self, poly: polynomial, length: int):
        # sumcheck protocol on g(k) = eq(r,k) * (f(1,k)-f(k,0)*f(k,1))
        diff_poly = poly.eval_i(Scalar(1), 1).shift(-1) + poly.eval_i(Scalar(0), length+1) * poly.eval_i(Scalar(1), length+1) * Scalar(-1)
        g_poly = eq_mle_poly(self.r) * diff_poly
        return prove_sumcheck(g_poly, length, 1)
    
    def handle_grand_product_sumcheck(self, data_list, r_list, poly: polynomial, length: int):
        data, r = self.grand_product_sumcheck(poly, length)
        data_list.append(data)
        r_list.append(r)

    def generate_grand_product_data(self, f: polynomial, r: list[Scalar]):
        f_0_r, f_0_r_proof = self.setup.eval_and_prove(f, [Scalar(0)]+r)
        f_1_r, f_1_r_proof = self.setup.eval_and_prove(f, [Scalar(1)]+r)
        f_r_0, f_r_0_proof = self.setup.eval_and_prove(f, r+[Scalar(0)])
        f_r_1, f_r_1_proof = self.setup.eval_and_prove(f, r+[Scalar(1)])
        product, product_proof = self.setup.eval_and_prove(f, [Scalar(1)]*len(r)+[Scalar(0)])
        return GrandProductData(f_0_r, f_1_r, f_r_0, f_r_1, product, 
            f_0_r_proof, f_1_r_proof, f_r_0_proof, f_r_1_proof, product_proof)
