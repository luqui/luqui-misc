#include <iostream>
#include <list>

const int compute_to = 200;

template <int num, int div>
struct AnyDivisors
{
	static const bool value = 
		num % div == 0 || AnyDivisors<num, div-1>::value;
};

template <int num>
struct AnyDivisors<num, 1>
{
	static const bool value = false;
};


template<int num>
struct Sqrt
{
	static const int value = 
		Sqrt<num-1>::value * Sqrt<num-1>::value < num
			? Sqrt<num-1>::value + 1
			: Sqrt<num-1>::value;
};

template<>
struct Sqrt<2>
{
	static const int value = 2;
};

struct PrimeQ 
{
	virtual ~PrimeQ() { }

	virtual bool is_prime() const = 0;
	virtual const PrimeQ* prev() const = 0;
	virtual int value() const = 0;
};

template <int num>
struct PrimeQList : public PrimeQ
{
	PrimeQList<num-1> prev_value;
	
	static const bool is_prime_value = 
		!AnyDivisors<num, Sqrt<num>::value>::value;
	
	bool is_prime() const {
		return is_prime_value;
	}

	const PrimeQ* prev() const {
		return &prev_value;
	}

	int value() const {
		return num;
	}
};

template <>
struct PrimeQList<2> : public PrimeQ
{
	bool is_prime() const {
		return true;
	}

	const PrimeQ* prev() const {
		return 0;
	}

	int value() const {
		return 2;
	}
};

int main()
{
	std::list<int> prime_list;
	
	PrimeQ* primes = new PrimeQList<compute_to>;
	const PrimeQ* cptr = primes;
	while (cptr) {
		if (cptr->is_prime()) {
			prime_list.push_front(cptr->value());
		}
		cptr = cptr->prev();
	}

	for (std::list<int>::const_iterator i = prime_list.begin(); i != prime_list.end(); ++i) {
		std::cout << *i << "\n";
	}
}
