all: CATONUXMV STATE INPUT
	gcc -std=c11 src/main.c objects/caToNuXmv.o objects/state.o objects/input.o -o reo2nuXmv
CATONUXMV:
	mkdir -p objects
	gcc -std=c11 -c src/headers/caToNuXmv.c -o objects/caToNuXmv.o
STATE: 
	mkdir -p objects
	gcc -std=c11 -c src/headers/state.c -o objects/state.o
INPUT: 
	mkdir -p objects
	gcc -std=c11 -c src/headers/input.c -o objects/input.o
debug: CATONUXMV STATE INPUT
	gcc -std=c11 -g src/main.c objects/caToNuXmv.o objects/state.o objects/input.o  -o reo2nuXmv
clean:
	rm -rf objects/*.o
