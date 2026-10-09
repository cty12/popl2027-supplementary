AGD = /usr/bin/env agda

all: proofs
.PHONY : all

proofs: src/LambdaAlphaRefStar/Theories/MainTheorems.agda
	$(info Checking all proofs ...)
	$(AGD) $<

.PHONY: clean
clean:
	rm -rf _build/
