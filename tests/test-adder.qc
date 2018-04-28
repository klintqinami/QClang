/* gates transcribed from qelib1.inc */
qubit tdg(qubit a)
{
	float pi;
	
	pi = 3.14159265359;
	return U(0., 0., -pi / 4., a);
}

qubit t(qubit a)
{
	float pi;

	pi = 3.14159265359;
	return U(0., 0., pi / 4., a);
}

tup(qubit, qubit, qubit) CCX(qubit a, qubit b, qubit c)
{
	(b, c) = CX(b, hadamard(c)); c = tdg(c);
	(a, c) = CX(a, c); c = t(c);
	(b, c) = CX(b, c); c = tdg(c);
	(a, c) = CX(a, c); b = t(b); c = hadamard(t(c));
	(a, b) = CX(a, b);
	(a, b) = CX(t(a), tdg(b));
	return (a, b, c);
}

/* adapted from QISKit/examples/generic/adder.qasm */

tup(qubit, qubit, qubit) majority(qubit a, qubit b, qubit c)
{
	(c, b) = CX(c, b);
	(c, a) = CX(c, a);
	return CCX(a, b, c);
}

tup(qubit, qubit, qubit) unmaj(qubit a, qubit b, qubit c)
{
	(a, b, c) = CCX(a, b, c);
	(c, a) = CX(c, a);
	(a, b) = CX(a, b);
	return (a, b, c);
}

tup(qubit[], qubit) ripple_add(qubit[] a, qubit[] b)
{
	qubit carry;
	qubit cout;
	qubit[] out;
	int i;

	out = new qubit[](length(a));
	carry = false;
	for (i = 0; i < length(a); i = i + 1) {
		(b[i], a[i], carry) = majority(carry, b[i], a[i]);
	}

	(carry, cout) = CX(carry, false);

	for (i = length(a) - 1; i >= 0; i = i - 1) {
		(carry, out[i], a[i]) = unmaj(b[i], a[i], carry);
	}

	return (out, cout);
}

bit[] meas_array(qubit[] a) {
	int i;
	bit[] out;

	out = new bit[](length(a));
	for (i = 0; i < length(a); i = i + 1) {
		out[i] = measure(a[i]);
	}

	return out;
}

int main() {
	qubit[] a;
	qubit[] b;
	qubit cout;

	a = new qubit[](4);
	b = new qubit[](4);

	a[3] = false; a[2] = false; a[1] = false; a[0] = true; /* a = 0001 */
	b[3] = true; b[2] = true; b[1] = true; b[0] = true; /* b = 1111 */
	(b, cout) = ripple_add(a, b);
	meas_array(b);
	measure(cout);
	return 0;
}
