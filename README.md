# Coq development for DimSum: A Decentralized Approach to Multi-language Semantics and Verification

This folder contains the Coq development for the paper "DimSum: A Decentralized Approach to Multi-language Semantics and Verification".

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
- The definition of the DimSum simulation is `sim` in `dimsum/proof_techniques.v`.
  For historic reasons, the Coq development mostly uses an equivalent definition: `trefines` in `dimsum/trefines.v`.
  The two definitions are proven equivalent by `sim_trefines` in `dimsum/proof_techniques.v`.
- Spec programs in the Coq development also have `put` and `get` constructors to access private state.
  This does not give additional expressive power but makes some Spec programs easier to write.
- As mentioned briefly in the paper, the instructions in Asm are composed of micro instructions.
  The instructions shown in the paper are `deep_asm_instr` in the mechanization.

## Guide through the Coq development

Section 2:
- Verification of the running example including programs and specifications: `dimsum_examples/memmove.v`
- Proof rules in Figure 5:
  - `asm-link-syn`: `asm_syn_link_refines_link` and `asm_link_refines_syn_link` in `dimsum_examples/asm.v`
  - `rec-link-syn`: `rec_syn_link_refines_link` and `rec_link_refines_syn_link` in `dimsum_examples/rec.v`
  - `asm-link-horizontal`: `asm_link_trefines` in `dimsum_examples/asm.v`
  - `rec-link-horizontal`: `rec_link_trefines` in `dimsum_examples/rec.v`
  - `rec-wrapper-compat`: `rec_to_asm_trefines` in `dimsum_examples/rec_to_asm.v`
  - `compiler-correct`: `compile_correct` in `dimsum_examples/compiler/compiler.v`
  - `rec-to-asm-link`: `rec_to_asm_combine` in `dimsum_examples/rec_to_asm.v`
- Definition of the Rec to Asm wrapper: `rec_to_asm` in `dimsum_examples/rec_to_asm.v`

Section 3.1:
- Definition of module: `module` in `dimsum/module.v`
- Definition of the multi-step relation: `lhas_trace` in `dimsum/lrefines.v`
- Definition of refinement / simulation: `sim` in `dimsum/proof_techniques.v` / `trefines` in `dimsum/trefines.v`
- Lemma 3.1: `trefines_preorder` in `dimsum/trefines.v`
- Theorem 3.2: `trefines_lrefines` in `dimsum/refines_meta.v`

Section 3.2:
- Definition of Spec: `itree_mod` in `dimsum/itree.v`

Section 3.3:
- Product: `seq_product_mod` in `dimsum/seq_product.v`
- Filter: `seq_map_mod` in `dimsum/seq_product.v`
  - Note that the filter is defined using more primitive combinators not discussed in the paper.
- Linking: `link_mod` in `dimsum/link.v`
- (Kripke) wrappers: `prepost_mod` in `dimsum/prepost.v`
- Rules in Figure 10:
  - `product-compat`: `seq_product_mod_trefines` in `dimsum/seq_product.v`
  - `filter-compat`: `seq_map_mod_trefines` in `dimsum/seq_product.v`
  - `link-compat`: `link_mod_trefines` in `dimsum/link.v`
  - `wrapper-compat`: `prepost_mod_trefines` in `dimsum/prepost.v`

Section 4:
- Definition of Asm:
  - Syntax: `deep_asm_instr` in `dimsum_examples/asm.v`
  - Module Semantics: `asm_mod`, `deep_to_asm_instrs` in `dimsum_examples/asm.v`
  - Syntactic Linking: `asm_syn_link` in `dimsum_examples/asm.v`
  - Semantic Linking: `asm_link` in `dimsum_examples/asm.v`
- Definition of Rec:
  - Syntax: `expr` in `dimsum_examples/rec.v`
  - Module Semantics: `rec_mod` in `dimsum_examples/rec.v`
  - Syntactic Linking: `rec_syn_link` in `dimsum_examples/rec.v`
  - Semantic Linking: `rec_link` in `dimsum_examples/rec.v`
- Coroutine Library:
  - Definition of the linking operator: `coro_link` in `dimsum_examples/coroutine.v`
  - `yield`: `yield_asm` in `dimsum_examples/coroutine.v`
  - `coro-link`: `coro_spec` in `dimsum_examples/coroutine.v`
  - Verification of the example: `dimsum_examples/coroutine_example.v`

Section 5:
- Compiler: `dimsum_examples/compiler/compiler.v`
  - Compiler correctness: compiler_correct in `dimsum_examples/compiler/compiler.v`
    - Note that the compiler_correct lemma only allows compiling
      single functions but they can be combined using
      `rec_to_asm_combine` in `dimsum_examples/rec_to_asm.v` and the equivalence
      of syntactic and semantic linking.
  - SSA pass: `dimsum_examples/compiler/ssa.v`
  - Linearize pass: `dimsum_examples/compiler/linearize.v`
  - Mem2Reg pass: `dimsum_examples/compiler/mem2reg.v`
  - Codegen pass: `dimsum_examples/compiler/codegen.v`
- Rec-to-rec wrapper: `rec_heap_bij` in `dimsum_examples/rec_heap_bij.v`
- `rec-to-asm-vertical`: `r2a_bij_vertical` in `dimsum_examples/r2a_bij_vertical.v`


### Axioms
The development relies on the following non-constructive axioms:
* Functional form of the (non extensional) axiom of choice, Choice (`FunctionalChoice` of `Coq.Logic.ChoiceFacts`)
* (Dependent) Functional Extensionality, (D)FE (`functional_extensionality_dep` from `Coq.Logic.FunctionalExtensionality`)
* Proof Irrelevance, PI (`proof_irrelevance` from `Coq.Logic.ProofIrrelevance`)
* Excluded Middle (already implied by the combination of Choice and FE), XM (`classic` from `Coq.Logic.Classical_Prop`)
* Invariance by Substitution of Reflexive Equality Proofs (already implied XM), UIP (`Eq_rect_eq` from `Coq.Logic.EqdepFacts`)
These axioms [can be safely added to Coq](https://github.com/coq/coq/wiki/The-Logic-of-Coq#what-axioms-can-be-safely-added-to-coq).
