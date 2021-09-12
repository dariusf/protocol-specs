FROM ocaml/opam:ubuntu-ocaml-4.12
ADD . /protocol
WORKDIR /protocol

USER root

RUN ltl3tools/install.sh

# For tests
RUN apt-get install golang -y

RUN opam update && opam install . --deps-only --with-test --locked
RUN eval $(opam env) && make
ENV PATH="/protocol/_build/install/default/bin:${PATH}"
USER opam