#include <iostream>

co_import "main.co";

void cpp_function() {
	std::cout << "Hello from C++!\n";
}

template<typename T>
class ComuneClassTest {
	T* data;
	int size;
	int capacity;
public:
	ComuneClassTest();
	void do_thing();
};

int main() {
	cpp_function();
	return comune_main();
}