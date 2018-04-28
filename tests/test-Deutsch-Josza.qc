/* Create a bunch of either true or false qubits */
qubit[] const_qubit(int len, bool val) {
	int i;
	qubit[] out;
	
	out = new qubit[](len);
	for (i = 0; i < len; i = i + 1)
		out[i] = val;

	return out;
}

int main() {
    /* QClang implementation of Deutsch-Josza Algorith */
    int i;
    int strlen;

    qubit[] test_bits;
    bit[] measure_bits;
    qubit answer;

    /* Create Qubit array for oracle query */
    strlen = 10;
    measure_bits = new bit[](strlen);

    /* Create superposition state */
    test_bits = hadamard(const_qubit(strlen, false));

    answer = hadamard(true);

    /* Query oracle  */
    answer = !answer;

    /* Apply hadamard again */
    test_bits = hadamard(test_bits);

    /* Measure */
    measure_bits = measure(test_bits);

    return 0;
}
