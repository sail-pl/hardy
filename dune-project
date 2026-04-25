(lang dune 3.22)
(using rocq 0.12)
(name hardy)

(using menhir 3.0)

(generate_opam_files true)

(source
(github sail-pl/hardy))

(authors "Térence Clastres, Frédéric Dabrowski")

(maintainers "Térence Clastres")

(license COPYING)

(package
  (name hardy)
  (synopsis "Hardy is a proof of concept synchronous reactive program verification framework enabling deductive verification of temporal properties.")
  (depends 
  (ocaml (>= 5.4.0))
  why3
  alt-ergo
  (rocq (>= 9.2))
  dune
  menhir
  (ocamlformat (and (= 0.26.1) :with-dev-setup))
  (ocaml-lsp-server :with-dev-setup)
  zarith
  ocamlgraph
  progress
  shexp
  )
)
