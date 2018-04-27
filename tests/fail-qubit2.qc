int main() {
	qubit a;
	qubit b;
	qubit c;
	a = b;
	(c, a) = (b, c);
	return 0;
}
