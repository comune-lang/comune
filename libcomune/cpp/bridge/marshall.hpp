#pragma once

namespace co {

	template<typename T> 
	class Pin {
		T data;

		Pin() = delete;
		Pin(Pin&& other) = delete;
		Pin(const Pin& other) = delete;
		Pin& operator=(Pin&& other) = delete;
		Pin& operator=(const Pin& other) = delete;
	public:
		T& operator*() & { 
			return data;
		}

		const T& operator*() const& { 
			return data;
		}

		template<typename... Args>
		Pin(Args... args) {
			new(&data) T(args...);
		}

		~Pin() { data.drop(); }		
	};

	
	template<typename T>
	class MoveGuard {
		T data;
		
		MoveGuard() = delete;
		MoveGuard(MoveGuard&& other) = delete;
		MoveGuard& operator=(MoveGuard&& other) = delete;
	public:
		template<typename... Args>
		MoveGuard(Args... args) {
			new(&data) T(args...);
		}

		MoveGuard(const MoveGuard& other) {
			*this = other;
		}

		MoveGuard& operator=(const MoveGuard& other) {
			if (&data != this)
				data = other.data.clone();
		}

		T& operator*() & {
			return data;
		}

		const T& operator*() const& {
			return data;
		}

		~MoveGuard() {
			data.drop();
		}
	}

	
	template<typename T> 
	class DropGuard {
		union { T data; };
		bool live;

		DropGuard(const DropGuard& other) = delete;
		DropGuard& operator=(const DropGuard& other) = delete;
	public:
		DropGuard(): live(false) {}

		template<typename... Args>
		DropGuard(Args... args) {
			new(&data) T(args...);
			live = true;
		}

		DropGuard(DropGuard&& other) {
			assert(other.live);
			memcpy(&this->data, &other.data, sizeof(T));
			other.live = false; this->live = true;
		}

		DropGuard& operator=(DropGuard&& other) {
			assert(other.live);
			memcpy(&this->data, &other.data, sizeof(T));
			other.live = false; this->live = true;
			return *this;
		}

		T& operator*() & {
			assert(this->live);
			return data;
		}

		const T& operator*() const& {
			assert(this->live);
			return data;
		}

		~DropGuard() {
			if (live) 
				data.drop();
		}
	};
}