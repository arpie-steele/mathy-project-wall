metamath : submodules/metamath-exe/*.c submodules/metamath-exe/*.h
	gcc -I submodules/metamath-exe -O3 -funroll-loops -finline-functions -fomit-frame-pointer -Wall -pedantic -o $@ submodules/metamath-exe/m*.c
