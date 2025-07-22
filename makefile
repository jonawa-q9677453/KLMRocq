.PHONY: all clean

all: _CoqProject
	+$(MAKE) -f Makefile.coq

_CoqProject:
	echo "-R A-Comprehensive-Formalization-of-Propositional-Logic-in-Coq Logic" > _CoqProject
	echo "-R KLM KLM" >> _CoqProject

clean:
	+$(MAKE) -f Makefile.coq clean
	find . -name "*.vo" -delete
	find . -name "*.glob" -delete
	find . -name "*.vok" -delete
	find . -name "*.vos" -delete
	find . -name ".*.aux" -delete
