int main() {
	qubit[] a;
	qubit[] b;

	b = new qubit[](3);
	b[0] = false;
	b[1] = false;
	b[2] = false;
	a = hadamard(b);
	return 0;
}
