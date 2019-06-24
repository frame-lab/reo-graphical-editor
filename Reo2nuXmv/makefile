all: CATONUXMV STATE INPUT
	gcc src/main.c objects/caToNuXmv.o objects/state.o objects/input.o -o reo2nuXmv
CATONUXMV:
	mkdir -p objects
	gcc -c src/headers/caToNuXmv.c -o objects/caToNuXmv.o
STATE: 
	mkdir -p objects
	gcc -c src/headers/state.c -o objects/state.o
INPUT: 
	mkdir -p objects
	gcc -c src/headers/input.c -o objects/input.o
debug: CATONUXMV STATE INPUT
	gcc -g src/main.c objects/caToNuXmv.o objects/state.o objects/input.o  -o reo2nuXmv
clean:
	rm -rf objects/*.o
