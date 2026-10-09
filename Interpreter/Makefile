RKT = /usr/bin/env racket
RACO = /usr/bin/env raco

all: tests
.PHONY : all

# Racket dependencies, as declared in info.rkt.
.PHONY: deps
deps:
	$(info Installing Racket dependencies ...)
	$(RACO) pkg install --auto --no-docs

tests: test-examples.rkt
	$(info Running all examples ...)
	$(RKT) $<

.PHONY: clean
clean:
	rm -rf compiled/ sister-language/compiled/ sister-language/tests/compiled/
