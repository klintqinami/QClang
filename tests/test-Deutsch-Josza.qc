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
    test_bits = hadamard(new qubit[](strlen));

    answer = hadamard(true);

    /* Query oracle  */
    answer = !answer;

    /* Apply hadamard again */
    test_bits = hadamard(test_bits);

    /* Measure */
    measure_bits = measure(test_bits);

    return 0;
}
