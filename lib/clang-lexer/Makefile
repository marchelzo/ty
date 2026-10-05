CXX ?= c++
LLVM_CONFIG ?= llvm-config-18
CXXFLAGS ?= -O2

lexer.so: lexer.cc
	$(CXX) $(CXXFLAGS) -std=c++17 -fPIC -shared -I$(shell $(LLVM_CONFIG) --includedir) -o $@ $< -L$(shell $(LLVM_CONFIG) --libdir) -l:libclang-cpp.so.18.1 -lLLVM-18

clean:
	rm -f lexer.so

.PHONY: clean
