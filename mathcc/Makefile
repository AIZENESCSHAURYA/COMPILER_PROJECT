CXX ?= g++
CXXFLAGS ?= -O2 -std=c++17 -Wall -Wextra -Wno-unused-parameter
bin/mathcc: src/*.hpp src/main.cpp
	@mkdir -p bin
	$(CXX) $(CXXFLAGS) src/main.cpp -o bin/mathcc
WASI_SDK ?= /opt/wasi-sdk
wasm:
	@mkdir -p web/wasm
	$(WASI_SDK)/bin/clang++ --target=wasm32-wasi --sysroot=$(WASI_SDK)/share/wasi-sysroot -O2 -std=c++17 -fno-exceptions -DMATHCC_NO_EXCEPTIONS -Wno-unused-parameter src/main.cpp -o web/wasm/mathcc.wasm -Wl,--strip-all
site: wasm
	python3 web/build_site.py
web: bin/mathcc
	python3 web/server.py
test: bin/mathcc
	python3 tests/run_tests.py
clean:
	rm -rf bin
