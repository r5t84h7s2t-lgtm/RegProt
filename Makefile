ISABELLE ?= isabelle
SESSION := RegProt
ENTRY := $(CURDIR)/src/system/RegProt_Model.thy

.PHONY: build check open clean

build:
	$(ISABELLE) build -D . $(SESSION)

check: build

open: build
	$(ISABELLE) jedit -d . -l $(SESSION) $(ENTRY)

clean:
	$(ISABELLE) build -c -D . $(SESSION)
