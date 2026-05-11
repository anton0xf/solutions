COQMAKEFILE := CoqMakefile

all: $(COQMAKEFILE)
	$(MAKE) -f $(COQMAKEFILE)

$(COQMAKEFILE): _CoqProject
	coq_makefile -f _CoqProject -o $(COQMAKEFILE)

clean: $(COQMAKEFILE)
	$(MAKE) -f $(COQMAKEFILE) clean

.PHONY: all clean
