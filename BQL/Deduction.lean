import BQL.Semantics

/-! The two contexts encode the discharge condition C5. Only the permanent
context may supply open assumptions to the conditional premise of detachment.
An extra free variable in a quantifier premise serves as its eigenparameter. -/
namespace BQL
open Formula

abbrev Depth := Option Nat

/-- A numeral bounds nesting into conditional premises of modus ponens.
`none` admits arbitrarily many such steps. -/
def Below : Depth → Depth → Prop
  | _, none => True
  | some j, some k => j < k
  | none, some _ => False

abbrev ExtraRules (L : Language) := {n : Nat} → List (Formula L n) → Formula L n → Prop

inductive Tree (L : Language) (rules : ExtraRules L) : Depth →
    {n : Nat} → Theory L n → Theory L n → Formula L n → Prop where
  | global : Γ a → Tree L rules k Γ Δ a
  | hyp : Δ a → Tree L rules k Γ Δ a
  | topI : Tree L rules k Γ Δ top
  | botE : Tree L rules k Γ Δ bot → Tree L rules k Γ Δ a
  | andI : Tree L rules k Γ Δ a → Tree L rules k Γ Δ b → Tree L rules k Γ Δ (conj a b)
  | andL : Tree L rules k Γ Δ (conj a b) → Tree L rules k Γ Δ a
  | andR : Tree L rules k Γ Δ (conj a b) → Tree L rules k Γ Δ b
  | orL : Tree L rules k Γ Δ a → Tree L rules k Γ Δ (disj a b)
  | orR : Tree L rules k Γ Δ b → Tree L rules k Γ Δ (disj a b)
  | orE : Tree L rules k Γ Δ (disj a b) → Tree L rules k Γ (insert a Δ) c →
      Tree L rules k Γ (insert b Δ) c → Tree L rules k Γ Δ c
  | impI : Tree L rules k Γ (insert a Δ) b → Tree L rules k Γ Δ (imp a b)
  | impE : Below j k → Tree L rules k Γ Δ a → Tree L rules j Γ empty (imp a b) → Tree L rules k Γ Δ b
  | trans : Tree L rules k Γ Δ (imp a b) → Tree L rules k Γ Δ (imp b c) → Tree L rules k Γ Δ (imp a c)
  | meet : Tree L rules k Γ Δ (imp a b) → Tree L rules k Γ Δ (imp a c) → Tree L rules k Γ Δ (imp a (conj b c))
  | join : Tree L rules k Γ Δ (imp a c) → Tree L rules k Γ Δ (imp b c) → Tree L rules k Γ Δ (imp (disj a b) c)
  | internalAll : Tree L rules k Γ Δ (all (imp a.lift b)) → Tree L rules k Γ Δ (imp a (all b))
  | internalEx : Tree L rules k Γ Δ (all (imp a b.lift)) → Tree L rules k Γ Δ (imp (ex a) b)
  | allI : Tree L rules k (lifted Γ) (lifted Δ) a → Tree L rules k Γ Δ (all a)
  | allE (t) : Tree L rules k Γ Δ (all a) → Tree L rules k Γ Δ (a.inst t)
  | exI (t) : Tree L rules k Γ Δ (a.inst t) → Tree L rules k Γ Δ (ex a)
  | exE : Tree L rules k Γ Δ (ex a) → Tree L rules k (lifted Γ) (insert a (lifted Δ)) b.lift →
      Tree L rules k Γ Δ b
  | cd : Tree L rules k Γ Δ (all (disj a.lift b)) → Tree L rules k Γ Δ (disj a (all b))

  | extra {ps : List (Formula L n)} : rules ps a → (∀ b ∈ ps, Tree L rules k Γ Δ b) → Tree L rules k Γ Δ a

abbrev Derivation (L : Language) (k : Depth) {n} (Γ Δ : Theory L n) (a : Formula L n) :=
  Tree L (fun _ _ => False) k Γ Δ a

namespace Derivation
export Tree (global hyp topI botE andI andL andR orL orR orE impI impE meet trans join internalAll internalEx allI allE exI exE cd)
end Derivation

abbrev Deriv (L : Language) (mp : Bool) {n} (Γ Δ : Theory L n) (a : Formula L n) := Derivation L (if mp then none else some 0) Γ Δ a

variable {L : Language} {n : Nat} {Γ Δ : Theory L n} {a b c : Formula L n} {mp : Bool}

abbrev Proves (Γ : Theory L n) (a : Formula L n) := Deriv L true Γ empty a
abbrev Basic (Γ : Theory L n) (a : Formula L n) := Deriv L false Γ empty a

/-- Generalized soundness also applies to extensions by locally valid rules. -/
theorem Tree.soundAt {rules : ExtraRules L} (M : Model L)
    (ok : ∀ {n} {ps : List (Formula L n)} {a}, rules ps a → ∀ w ρ,
      (∀ b ∈ ps, M.Forces w ρ b) → M.Forces w ρ a)
    (p : Tree L rules k Γ Δ a) : ∀ w u ρ, M.acc w w → M.acc w u →
      M.Satisfies w ρ Γ → M.Satisfies u ρ Δ → M.Forces u ρ a := by
  induction p with
  | global h => exact fun _ _ ρ _ e g _ => M.persistence e ρ _ (g _ h)
  | hyp h => exact fun _ _ _ _ _ _ d => d _ h
  | topI => exact fun _ _ _ _ _ _ _ => True.intro
  | botE _ ih => exact fun w u ρ r e g d => False.elim (ih w u ρ r e g d)
  | andI _ _ h k => exact fun w u ρ r e g d => ⟨h w u ρ r e g d, k w u ρ r e g d⟩
  | andL _ h => exact fun w u ρ r e g d => (h w u ρ r e g d).1
  | andR _ h => exact fun w u ρ r e g d => (h w u ρ r e g d).2
  | orL _ h => exact fun w u ρ r e g d => Or.inl (h w u ρ r e g d)
  | orR _ h => exact fun w u ρ r e g d => Or.inr (h w u ρ r e g d)
  | orE _ _ _ h l k =>
    intro w u ρ r e g d
    exact (h w u ρ r e g d).elim
      (fun ha => l w u ρ r e g (M.sat_insert ha d))
      (fun hb => k w u ρ r e g (M.sat_insert hb d))
  | impI _ h =>
    intro w u ρ r e g d z uz ha
    exact h w z ρ r (M.trans e uz) g (M.sat_insert ha (M.sat_persist uz d))
  | impE _ _ _ h k =>
    intro w u ρ r e g d
    exact k w w ρ r r g (fun _ h => h.elim) u e (h w u ρ r e g d)
  | trans _ _ h k =>
    exact fun w u ρ r e g d z uz ha => k w u ρ r e g d z uz (h w u ρ r e g d z uz ha)
  | meet _ _ h k =>
    exact fun w u ρ r e g d z uz ha => ⟨h w u ρ r e g d z uz ha, k w u ρ r e g d z uz ha⟩
  | join _ _ h k =>
    exact fun w u ρ r e g d z uz hab => hab.elim (h w u ρ r e g d z uz) (k w u ρ r e g d z uz)
  | internalAll _ h =>
    intro w u ρ r e g d z uz ha x
    exact h w u ρ r e g d x z uz ((M.forces_lift ..).2 ha)
  | internalEx _ h =>
    intro w u ρ r e g d z uz ⟨x,hx⟩
    exact (M.forces_lift ..).1 (h w u ρ r e g d x z uz hx)
  | allI _ h =>
    exact fun w u ρ r e g d x => h w u _ r e (M.sat_lifted g x) (M.sat_lifted d x)
  | allE t _ h =>
    exact fun w u ρ r e g d => (M.forces_inst ..).2 (h w u ρ r e g d (M.eval ρ t))
  | exI t _ h =>
    exact fun w u ρ r e g d => ⟨M.eval ρ t, (M.forces_inst ..).1 (h w u ρ r e g d)⟩
  | exE _ _ h k =>
    intro w u ρ r e g d
    obtain ⟨x,hx⟩ := h w u ρ r e g d
    exact (M.forces_lift ..).1 (k w u _ r e (M.sat_lifted g x) (M.sat_insert hx (M.sat_lifted d x)))
  | cd _ h =>
    intro w u ρ r e g d
    apply Classical.or_iff_not_imp_left.mpr
    intro hn x
    exact (h w u ρ r e g d x).resolve_left (fun hl => hn ((M.forces_lift ..).1 hl))

  | extra rule _ ih => exact fun w u ρ r e g d => ok rule u ρ (fun b hb => ih b hb w u ρ r e g d)

theorem generalizedSoundness (p : Derivation L k Γ Δ a) : RelativeEntails Γ Δ a :=
  fun M => p.soundAt M (fun h => h.elim)

theorem soundness (p : Proves Γ a) : Entails Γ a :=
  fun M w ρ r g => generalizedSoundness p M w w ρ r r g (fun _ h => h.elim)

end BQL
