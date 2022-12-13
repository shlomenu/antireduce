(lang dune 3.6)

(name antireduce)

(generate_opam_files true)

(package
 (name antireduce)
 (version "0.1.0")
 (synopsis
  "Domain-generic polymorphic lambda calculus program representations with inverse beta reduction")
 (description
  "A reimplementation of core functionalities of the DreamCoder program synthesis system")
 (depends core core_unix ppx_jane ppx_compare ppx_yojson_conv)
 (license "MIT")
 (authors "Eli Whitehouse <eliw55@gmail.com>")
 (maintainers "Eli Whitehouse <eliw55@gmail.com>")
 (source
  (github shlomenu/antireduce))
 (bug_reports "https://github.com/shlomenu/antireduce/issues"))
