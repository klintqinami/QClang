qubit foo(qubit q)
{
	return hadamard(q);
}

int main() {
	qubit q;
	
	q = foo(false);
	measure(q);
}

