int main() {
	qubit q1;
	qubit q2;

	/* entangle q1 and q2 */
	(q1, q2) = CX(hadamard(false), false);
	/* unentangle */
	(q1, q2) = CX(q1, q2);
	q1 = hadamard(q1);
	measure(q1);
	measure(q2);
	return 0;
}
