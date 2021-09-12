(lang dune 2.7)

(using menhir 2.1)

;(using mdx 0.1)

(cram enable)

(generate_opam_files true)

(source
 (github dariusf/protocol-specs))

; (license ISC)

(authors "Darius Foo")

(maintainers "darius.foo.tw@gmail.com")

(package
 (name protocol)
 (synopsis "A protocol specification language")
 (description "A protocol specification language")
 (depends
  (ppx_expect (and :with-test (>= v0.14.1)))
  (ppx_deriving
   (>= 5.2.1))
  (cmdliner
   (>= 1.0.4))
  (pprint
   (>= 20200410))
  (containers
   (>= 3.0))
  (menhir
   (>= 20210419))
  (ocamlgraph
   (>= 2.0.0))
  (visitors
   (>= 20210608))
  (ppx_string
   (>= v0.14.1))
  (dune
   (> 2.8))))
