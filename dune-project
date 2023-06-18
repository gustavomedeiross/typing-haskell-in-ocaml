(lang dune 3.2)

(name thio)

(generate_opam_files true)

(source
 (github gustavomdeiros/thio))

(authors "Gustavo Medeiros")

(maintainers "Gustavo Medeiros")

(license LICENSE)

(package
 (name thio)
 (synopsis "Typing Haskell in OCaml")
 (description "Port of the \"Typing Haskell in Haskell\" code in OCaml")
 (depends ocaml dune)
 (tags
  (topics "to describe" your project)))

(using menhir 2.1)

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/dune-files.html#dune-project
