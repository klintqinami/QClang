# Imports OpenQASM intermediate IR and executes it on the local_qasm_simulator.

import sys
import qiskit

if sys.version_info < (3,0):
    raise Exception("Please use Python version 3 or greater.")

def main():
    if (len(sys.argv) != 2):
        print("Usage: python3 run_qasm.py [qasm_filename]")
    name = "test"
    qp = qiskit.QuantumProgram()
    qp.load_qasm_file(sys.argv[1], name=name)
    ret = qp.execute([name], backend="local_qasm_simulator", shots=1,\
          max_credits=5, hpc=None, timeout=60*60*24)

    sim_result = ret.get_counts(name)
    sim_result_keys = sim_result.keys()

    print(ret)
    print(sim_result)
    print(sim_result_keys)
    return
    
if __name__ == "__main__":
    main()
