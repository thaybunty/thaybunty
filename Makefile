OCAML = ocamlfind ocamlc -w "-8-10-11-14-25-26" -g -package batteries -linkpkg -thread

all:
			$(OCAML) interpreter_bigstep.ml -o test

clean:
	rm *.cmo
	rm *.cmi
	rm output
