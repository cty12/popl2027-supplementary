# Artifact image for LambdaAlphaRefStar (POPL 2027).
#
# Pins the toolchain versions the READMEs call for:
#   Agda 2.8.0 + Agda standard library v2.3   (Theories/README.md)
#   Racket v9.2 [cs]                          (Interpreter/readme.md)
#
# Fedora 43 packages Agda 2.8.0, so the compiler needs no source build. The
# standard library is cloned at its upstream tag rather than taken from the
# distro, so the pin is an immutable git tag instead of a Fedora packaging
# revision. Racket comes from the official installer, since the distro package
# lags the version the interpreter was tested on.
#
# Build:  docker build -t lambdaalpharefstar .
# Run:    docker run --rm lambdaalpharefstar
#
# The default command runs the two Makefiles: it checks the Agda proofs and
# then runs the interpreter's example tests.

FROM fedora:43

ARG AGDA_VERSION=2.8.0
ARG AGDA_STDLIB_VERSION=2.3
ARG RACKET_VERSION=9.2

RUN dnf install -y --setopt=install_weak_deps=False \
      "Agda-${AGDA_VERSION}" git make tar gzip \
 && dnf clean all

RUN git clone --depth 1 --branch "v${AGDA_STDLIB_VERSION}" \
      https://github.com/agda/agda-stdlib.git /opt/agda-stdlib

# Register the standard library so `depend: standard-library` resolves. No
# `defaults` file is needed: Agda consults it only for files with no enclosing
# .agda-lib, and Theories/lambda-alpha-ref-star.agda-lib declares the dependency
# itself.
RUN mkdir -p /root/.config/agda \
 && echo /opt/agda-stdlib/standard-library.agda-lib \
      > /root/.config/agda/libraries

# Racket, from the official installer. `racket-minimal` plus the dependencies
# declared in Interpreter/info.rkt is enough to run the examples.
RUN curl -fsSL -o /tmp/racket.sh \
      "https://download.racket-lang.org/releases/${RACKET_VERSION}/installers/racket-minimal-${RACKET_VERSION}-x86_64-linux-cs.sh" \
 && sh /tmp/racket.sh --in-place --dest /opt/racket \
 && rm /tmp/racket.sh
ENV PATH="/opt/racket/bin:${PATH}"

WORKDIR /artifact
COPY . /artifact

# Racket dependencies declared in Interpreter/info.rkt (base, rackunit-lib,
# graph-lib).
RUN make -C Interpreter deps

# Type check the proofs at build time so the standard library's interface files
# are baked into the image. The CMD below still checks them, but then finds
# everything up to date and finishes in seconds rather than minutes.
RUN make -C Theories

# Run Agda typechecker on proofs in Theories and run test suite for the
# prototype implementation in Interpreter
CMD ["sh", "-c", "make -C Theories && make -C Interpreter"]
