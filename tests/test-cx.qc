int main() {
	qubit q1;
	qubit q2;
	tup(qubit, qubit) tuple;

	/* entangle q1 and q2 */
	tuple = CX(hadamard(q1), q2);
	/* unentangle */
	tuple = CX(tuple[0], tuple[1]);
	q1 = hadamard(tuple[0]);
	q2 = hadamard(tuple[1]);
	measure(q1);
	measure(q2);
	return 0;
}
