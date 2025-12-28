(lang dune 3.11)
(using coq 0.8)
(name hardy)

(using menhir 2.1)

(generate_opam_files true)

(source
(github sail-pl/hardy))

(authors "Térence Clastres, Frédéric Dabrowski")

(maintainers "Térence Clastres")

; (license LICENSE)

; (documentation https://url/to/documentation)

(package
  (name hardy)
   (synopsis "A short synopsis")
   (description "A longer description")
  (depends 
  (ocaml (>= 5.4.0))
  why3
  alt-ergo
  (coq (>= 8.18))
  dune
  menhir
  (ocamlformat (and (= 0.26.1) :with-dev-setup))
  (ocaml-lsp-server :with-dev-setup)
  zarith
  ocamlgraph
  progress
  nottui-unix

  )
  ; (tags
  ; (topics "to describe" your project))
  )
