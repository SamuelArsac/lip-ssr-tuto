FROM coqorg/coq:8.20-ocaml-4.14-flambda
RUN eval $(opam env "--switch=${COMPILER}" --set-switch)
RUN opam update -y
RUN opam install -y coq-lsp
RUN opam install -y vscoq-language-server
RUN opam install -y coq-mathcomp-character
RUN opam install -y coq-mathcomp-zify
RUN opam install -y coq-mathcomp-zify
RUN opam install -y coq-mathcomp-algebra-tactics
RUN opam install -y coq-mathcomp-analysis
RUN opam install -y vscoq-language-server
