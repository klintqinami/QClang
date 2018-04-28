qubit foo(qubit q)
{
	return !q;
}

int main() {
	qubit q;
	
	q = foo(false);
	measure(q);
	return 0;
}

