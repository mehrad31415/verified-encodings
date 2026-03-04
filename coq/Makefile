COQPROJECT := _CoqProject
COQMAKEFILE := Makefile.coq

all: $(COQMAKEFILE)
	$(MAKE) -f $(COQMAKEFILE)

$(COQMAKEFILE): $(COQPROJECT)
	coq_makefile -f $(COQPROJECT) -o $(COQMAKEFILE)

clean: $(COQMAKEFILE)
	$(MAKE) -f $(COQMAKEFILE) cleanall
	rm -f $(COQMAKEFILE) $(COQMAKEFILE).conf

.PHONY: all clean
