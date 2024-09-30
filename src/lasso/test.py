import random
from src.lasso.setup import Setup
from src.lasso.program import Params, SOSTable
from src.lasso.prover import Prover, Proof
from src.lasso.verifier import Verifier

# setup: public setup includes srs
# public_table: public table
# witness: values to lookup
def prover(setup: Setup, params: Params, witness: list[int]):
    print("Beginning prover test")

    print("table: ", params.table.tables)
    print("witness: ", witness)

    prover = Prover(setup, params)
    proof = prover.prove(witness)
    print("Prover test success")

    return proof

def prover_simple_array(setup: Setup, params: Params):
    print("Beginning prover_simple_array test")
    # values to lookup
    witness = [1, 4, 9, 16]
    proof = prover(setup, params, witness)
    return proof

def prover_random_lookup(setup: Setup, params: Params):
    print("Beginning prover_random_lookup test")
    # values to lookup
    witness = []
    for _ in range(16):
        witness.append(random.randint(1, 2**16))

    proof = prover(setup, params, witness)
    return proof

def verifier(setup: Setup, params: Params, proof: Proof):
    print("Beginning verifier test")
    verifier = Verifier(setup, params)
    assert verifier.verify(proof)
    print("Verifier test success")

# A simple table that simply form [1, ..., 2**length]
# For simplicity, we require that l | length
# Each subtable is just [0, 1, ..., 2**l - 1]
class SimpleSOSTable(SOSTable):
    def __init__(self, length, l):
        assert(length%l == 0)
        c = length // l
        tables = [[i for i in range(2**l)] for _ in range(c)]
        super().__init__(l, length//l, 1, tables)
        

def simple_test():
    # public table
    total_bits = 4
    subtable_bits = 2
    table = SimpleSOSTable(total_bits, subtable_bits)

    # do setup
    setup = Setup(subtable_bits+1, 1)
    # set public params
    params = Params(table)
    # run prover
    proof = prover_simple_array(setup, params)
    # run verifier
    verifier(setup, params, proof)

def random_test():
    # public table
    total_bits = 16
    subtable_bits = 4
    table = SimpleSOSTable(total_bits, subtable_bits)

    # do setup
    setup = Setup(subtable_bits+1, 3)
    # set public params
    params = Params(table)
    # run prover
    proof = prover_random_lookup(setup, params)
    # run verifier
    verifier(setup, params, proof)

if __name__ == "__main__":
    simple_test()
    random_test()
