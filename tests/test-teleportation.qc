tup(qubit, qubit) epr_pair()
{
	return CX(hadamard(false), false);
}

tup(bit, bit) measure_bell(qubit a, qubit b)
{
	(a, b) = CX(a, b);
	return (measure(hadamard(a)), measure(b));
}

qubit teleport(qubit alice)
{
	qubit shared;
	qubit bob;
	bit meas1;
	bit meas2;

	(shared, bob) = epr_pair();
	(shared, bob) = barrier(shared, bob);
	/* enabling this causes the output to be random, which our test script can't handle atm */
	/* (meas1, meas2) = measure_bell(alice, shared); */

	/* TODO invert based on measurement */
	return bob;
}

int main()
{
	qubit alice;
	qubit bob;

	alice = true;
	bob = teleport(alice);

	return 0;
}
