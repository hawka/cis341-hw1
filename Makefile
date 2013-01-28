all: main

main: *.ml
	ocamlbuild main.native main.byte

test: main
	./main.native --test

clean:
	rm -rf _build/ main.native main.byte

top: all
	cd _build && echo '#load "x86.cmo";;\n#use "interpreter.ml";;' > .ocamlinit && ocaml && rm .ocamlinit
