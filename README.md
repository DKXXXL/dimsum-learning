# Appendix and Coq development for DimSum: A Decentralized Approach to Multi-language Semantics and Verification

This folder contains the appendix and the Coq development for the POPL'23 submission "DimSum: A Decentralized Approach to Multi-language Semantics and Verification".

## Appendix

The appendix for the paper can be found in `appendix.pdf`.

## Installation

It is recommended to install the dependencies of DimSum via [opam](https://opam.ocaml.org/doc/Install.html)
(version 2.0.0 or newer) into a new switch. This can be done via the
following commands.

```
opam switch create . ocaml-variants.4.14.0+options ocaml-option-flambda --no-install
opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git
make builddep
eval $(opam env)
```

Afterwards, run the following command to build the development (replace 8 by a suitable number of parallel jobs to spawn):

```
make -j 8
```

You might need to run `eval $(opam env)` to update the environment of your shell.


## Differences to the Paper

Before exploring the Coq development, note the following differences between the paper and the mechanization:
- The language Rec is called Rec in the Coq development.
- `module` in the Coq development does not contain an initial state.
  A module as defined in the paper is `mod_state` in the Coq development.
  Combinators and languages in Coq are defined as Coq `module` and provide the initial state in a separate definition (usually called `initial_COMBINATOR_NAME_state`).
- The definition of the DimSum simulation is `sim` in `theories/proof_techniques.v`.
  For historic reasons, the Coq development mostly uses an equivalent definition: `trefines` in `theories/trefines.v`.
  The two definitions are proven equivalent by `sim_trefines` in `theories/proof_techniques.v`.
- Spec programs in the Coq development also have `put` and `get` constructors to access private state.
  This does not give additional expressive power but makes some Spec programs easier to write.
- As mentioned briefly in the paper, the instructions in Asm are composed of micro instructions.
  The instructions shown in the paper are `deep_asm_instr` in the mechanization.

## Guide through the Coq development

Section 2:
- Verification of the running example including programs and specifications: `theories/memmove.v`
- Proof rules in Figure 5:
  - `asm-link-syn`: `asm_link_refines_prod` and `asm_prod_refines_link` in `theories/asm.v`
  - `rec-link-syn`: `imp_link_refines_prod` and `imp_prod_refines_link` in `theories/rec.v`
  - `asm-link-horizontal`: `asm_prod_trefines` in `theories/asm.v`
  - `rec-link-horizontal`: `imp_prod_trefines` in `theories/rec.v`
  - `rec-wrapper-compat`: `rec_to_asm_trefines` in `theories/rec_to_asm.v`
  - `compiler-correct`: `compile_correct` in `theories/compiler/compiler.v`
  - `rec-to-asm-link`: `rec_to_asm_combine` in `theories/rec_to_asm.v`
- Definition of the Rec to Asm wrapper: `rec_to_asm` in `theories/rec_to_asm.v`

Section 3.1:
- Definition of module: `module`, `mod_state` in `theories/module.v`
- Definition of the multi-step relation: `lhas_trace` in `theories/lrefines.v`
- Definition of refinement / simulation: `sim` in `theories/proof_techniques.v` / `trefines` in `theories/trefines.v`
- Lemma 3.1: `trefines_preorder` in `theories/trefines.v`
- Theorem 3.2: `trefines_lrefines` in `theories/refines_meta.v`

Section 3.2:
- Definition of Spec: `mod_itree` in `theories/itree.v`

Section 3.3:
- Product: `mod_seq_product` in `theories/seq_product.v`
- Filter: `mod_seq_map` in `theories/seq_product.v`
  - Note that the filter is defined using more primitive combinators not discussed in the paper.
- Linking: `mod_link` in `theories/link.v`
- (Kripke) wrappers: `mod_prepost` in `theories/prepost.v`
- Rules in Figure 10:
  - `product-compat`: `mod_seq_product_trefines` in `theories/seq_product.v`
  - `filter-compat`: `mod_seq_map_trefines` in `theories/seq_product.v`
  - `link-compat`: `mod_link_trefines` in `theories/link.v`
  - `wrapper-compat`: `mod_prepost_trefines` in `theories/prepost.v`

Section 4:
- Definition of Asm:
  - Syntax: `deep_asm_instr` in `theories/asm.v`
  - Module Semantics: `asm_module`, `deep_to_asm_instrs` in `theories/asm.v`
  - Syntactic Linking: `asm_link` in `theories/asm.v`
  - Semantic Linking: `asm_prod` in `theories/asm.v`
- Definition of Rec:
  - Syntax: `expr` in `theories/rec.v`
  - Module Semantics: `rec_module` in `theories/rec.v`
  - Syntactic Linking: `rec_link` in `theories/rec.v`
  - Semantic Linking: `imp_prod` in `theories/rec.v`
- Coroutine Library:
  - Definition of the linking operator: `coro_prod` in `theories/coroutine.v`
  - `yield`: `yield_asm` in `theories/coroutine.v`
  - `coro-link`: `coro_spec` in `theories/coroutine.v`
  - Verification of the example: `theories/coroutine_example.v`

Section 5:
- Compiler: `theories/compiler/compiler.v`
  - Compiler correctness: compiler_correct in `theories/compiler/compiler.v`
    - Note that the compiler_correct lemma only allows compiling
      single functions but they can be combined using
      `rec_to_asm_combine` in `theories/rec_to_asm.v` and the equivalence
      of syntactic and semantic linking.
  - SSA pass: `theories/compiler/ssa.v`
  - Linearize pass: `theories/compiler/linearize.v`
  - Mem2Reg pass: `theories/compiler/mem2reg.v`
  - Codegen pass: `theories/compiler/codegen.v`
- Rec-to-rec wrapper: `rec_heap_bij` in `theories/imp_heap_bij_own.v`
- `rec-to-asm-vertical`: `r2a_bij_vertical` in `theories/r2a_bij_vertical.v`


### Axioms
The development relies on the following non-constructive axioms:
* Functional form of the (non extensional) axiom of choice, Choice (`FunctionalChoice` of `Coq.Logic.ChoiceFacts`)
* (Dependent) Functional Extensionality, (D)FE (`functional_extensionality_dep` from `Coq.Logic.FunctionalExtensionality`)
* Proof Irrelevance, PI (`proof_irrelevance` from `Coq.Logic.ProofIrrelevance`)
* Excluded Middle (already implied by the combination of Choice and FE), XM (`classic` from `Coq.Logic.Classical_Prop`)
* Invariance by Substitution of Reflexive Equality Proofs (already implied XM), UIP (`Eq_rect_eq` from `Coq.Logic.EqdepFacts`)
These axioms [can be safely added to Coq](https://github.com/coq/coq/wiki/The-Logic-of-Coq#what-axioms-can-be-safely-added-to-coq).
