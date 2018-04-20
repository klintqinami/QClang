int main() {
    /* QClang implementation of Deutsch-Josza Algorith */
    int i;
    int strlen;

    qubit[] test_bits;
    bit[] measure_bits;
    qubit answer;

    /* Create Qubit array for oracle query */
    strlen = 10;
    test_bits = new qubit[](strlen);
    measure_bits = new bit[](strlen);

    /* Create superposition state */
    for (i = 0; i < strlen; i = i + 1) {
        test_bits[i] = hadamard(test_bits[i]);
    } 

    answer = !answer;
    answer = hadamard(answer);

    /* Query oracle  */
    answer = !answer;

    /* Apply hadamard again */
    for (i = 0; i < strlen; i = i + 1) {
        test_bits[i] = hadamard(test_bits[i]);
    } 

    /* Measure */
    for (i = 0; i < strlen; i = i + 1) {
        measure_bits[i] = measure(test_bits[i]);
    } 

    return 0;
}
