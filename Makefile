all: main

main: *.ml
	ocamlbuild main.native main.byte

test: main
	./main.native --test

clean:
	rm -rf _build/ main.native main.byte
