# Constant Domain Basic First-Order Logic

This Lean 4 library formalizes constant domain basic first-order logic (BQL<sub>CD</sub>) and its reflexive-root variant (BQL<sub>CD</sub><sup>r</sup>). Both use transitive Kripke frames. Every world in a model shares one nonempty domain of individuals, so quantifiers range over the same objects at every world. A world forces an implication A → B when every accessible world that forces A also forces B. [Kripke semantics](BQL/Semantics.lean)

The two logics differ in where they test consequence. Basic logic tests it at every world. The reflexive-root variant tests it at worlds that can access themselves. At such a world, A and A → B together entail B. Its successors can still be irreflexive, which is why the natural deduction calculus restricts conditional proof. When proofs may use fresh parameters, the two calculi prove exactly the same sentences from empty premises in every base language, including languages without constants. [Natural deduction](BQL/Deduction.lean) · [Comparison theorem](BQL/Comparison.lean) · [Two-world counterexample](BQL/Examples.lean)

The main theorem for the reflexive-root calculus is `BQL.adequate`. It proves `Derivable Γ a ↔ Entails Γ a` for any set of sentence premises and any base signature, including one without constants. The library follows Ben Middleton’s *Binary Kripke Semantics for a Strong Logic for Naive Truth* (arXiv:2001.00936v4). [Soundness and completeness](BQL/Parameters.lean) · [Paper on arXiv](https://arxiv.org/abs/2001.00936v4)

## Build and inspect

The project uses Lean 4.19.0 and its bundled standard library. From this directory, run

```sh
lake --wfail build
```

Import the library to inspect the statements and their axiom dependencies.

```lean
import BQL

#check BQL.Model.Forces
#check BQL.adequate
#check BQL.sameTheorems
#check BQL.reduction
#check BQL.Identity.adequateRules
#check BQL.Truth.omegaConsistency_all
#check BQL.Truth.omegaConsistency_ex
#print axioms BQL.adequate
```

## Formalized results

| Paper | Lean declarations and proof files |
| --- | --- |
| §3. Kripke semantics | `Model.Forces`, `Model.persistence`, `Entails` and `compactness`. The compactness proof constructs an ultrafilter extending the cones of finite premise sets and proves the forcing equivalence for the product. [Semantics](BQL/Semantics.lean) · [Compactness](BQL/Compactness.lean) |
| §4. Restricted natural deduction | `Derivation`, `relativeDeduction`, `regularity`, `reduction`, `unrestrictedOr` and `unrestrictedEx`. [Calculus](BQL/Deduction.lean) · [Reduction](BQL/Reduction.lean) · [Derived rules](BQL/DerivedRules.lean) · [Elimination](BQL/Elimination.lean) |
| §5. Soundness and completeness | `generalizedSoundness`, `Canonical.relativeExtension`, `Canonical.truthLemma`, `Canonical.primeExtension` and `completeness`. Finite support and compactness allow the canonical construction over a countable signature to establish strong completeness over an arbitrary signature. [Prime saturation](BQL/Saturation.lean) · [Canonical model](BQL/Canonical.lean) · [Extension](BQL/PrimeExtension.lean) · [Completeness](BQL/Completeness.lean) · [Parameter language](BQL/Parameters.lean) |
| §5. Disjunction and existence | `intersection`, `disjunctionProperty` and `existenceProperty`. The existence theorem returns a closed term of the **base** language. [Intersection lemma](BQL/Intersection.lean) · [Properties](BQL/Properties.lean) |
| §6. Basic and reflexive-root calculi | `sameTheorems` requires a constant in the language of the proofs. Applying it in `parameters L` supplies that constant and gives the equivalence for every sentence of the base language `L`. `internalModusPonensFails` gives the two-world counterexample to unrestricted conditional proof. [Comparison](BQL/Comparison.lean) · [Parameter language](BQL/Parameters.lean) · [Counterexamples](BQL/Examples.lean) |
| §7. Identity | `Identity.adequateRules` proves soundness and completeness for equality introduction and substitution with world-dependent congruences, and for the calculus with excluded middle for equality and actual identity. `Identity.diagonalDisjunctionFailure` verifies the failure of the disjunction property for actual identity. [Rules](BQL/EqualityCalculus.lean) · [Quotient model](BQL/Quotient.lean) · [Disjunction and existence](BQL/IdentityRules.lean) |
| Appendix. Naive truth | `Truth.standardModel`, `Truth.omegaConsistency_all`, `Truth.omegaConsistency_ex`, `Truth.nonTriviality` and `Truth.omegaRuleNontrivial`. The arithmetic language includes primitive recursive programs, an injective Gödel coding, curried induction and all sentence instances of the Tarski biconditional. [Arithmetic and coding](BQL/Arithmetic.lean) · [NT and its model](BQL/NaiveTruth.lean) · [Consistency results](BQL/Consequences.lean) |

## Reading the formalization

`Formula L n` has free variables in `Fin n`. Zero names the newest variable under a binder. In the two-context judgment `Derivation L k Γ Δ a`, the conditional premise of modus ponens can use only permanent assumptions from `Γ`. Rules that discharge an assumption put it in `Δ`. A quantifier premise extends the variable scope, which enforces freshness. At the level of base-language consequence, `Derivable` embeds the premises and conclusion into the language with countably many fresh constants. [Syntax](BQL/Syntax.lean) · [Deduction](BQL/Deduction.lean) · [Parameters](BQL/Parameters.lean)

Two proofs use different constructions from the exposition. The disjunction and existence proofs glue countermodels below a common reflexive root. The existence proof uses a shared domain of terms with additional names and an erasure argument to recover a base-language witness. [Gluing and witness extraction](BQL/Properties.lean)

The appendix represents transfinite stages by sets of earlier valuations, closed under successors and unions. The local extension of truth is the least fixed point of its operator. The final global stage contains its own valuation and is the unique reflexive world. Lean also proves well-foundedness and countability of the stage order, verifies the box bounds at stages ω·k + n, and gives a counterexample to uncurried induction. [Iteration](BQL/Iteration.lean) · [Standard model construction](BQL/TruthModel.lean) · [Counterexample](BQL/TruthStages.lean) · [Stage bounds](BQL/OrdinalBounds.lean)

## Connection to relevant logic

The paper also identifies the reflexive-root calculus with TJKᵈ⁺. In Lean, `equivalentTJK` establishes equivalence of the two proof systems, and `tjk_iff_entails` gives TJKᵈ⁺ the same Kripke consequence relation. The original calculus and the Bᵈ⁺, DJᵈ⁺ and TJᵈ⁺ hierarchy from §2 are available through `Relevant`. Its existential-elimination flag gives both presentations of TJK, and `redundantExistentialElim` proves they derive the same conclusions. [Relevant calculi and equivalence](BQL/TJK.lean) · [Semantic characterization](BQL/Consequences.lean)
