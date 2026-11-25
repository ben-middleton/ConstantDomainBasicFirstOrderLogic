import BQL.Comparison
import BQL.IdentityRules

namespace BQL
open Formula

/-- External detachment at designated worlds (§3). -/
theorem modusPonensAtRoot (a b : Sentence L) : Entails (Canonical.single (conj a (imp a b))) b := by
  intro M w ρ loop g
  have pair := g _ rfl
  exact pair.2 w loop pair.1

private def terminal : Model ⟨fun _ => Empty, fun _ => Empty⟩ where
  W := Unit
  D := Unit
  worlds := ⟨()⟩
  domain := ⟨()⟩
  acc _ _ := False
  trans := False.elim
  func := Empty.elim
  rel := Empty.elim
  persist := fun e => e.elim

/-- A reflexive root sees a dead end where ⊤ and ⊤ → ⊥ both hold. -/
theorem internalModusPonensFails :
    ¬Entails (L := ⟨fun _ => Empty, fun _ => Empty⟩) (V := 0) empty (imp (conj top (imp top bot)) bot) := by
  intro h
  exact h terminal.under none Fin.elim0 trivial (fun _ h => h.elim) (some ()) trivial
    ⟨trivial,fun z e => by cases z <;> exact e.elim⟩

namespace Identity
private def constants : Nat → Type
  | 0 => Bool
  | _+1 => Empty
private inductive Equality : Nat → Type where | eq : Equality 2
private def exampleLanguage : Language := ⟨constants,Equality⟩

private def classicalModel (collapse : Bool) : Model exampleLanguage where
  W := Unit
  D := Bool
  worlds := ⟨()⟩
  domain := ⟨true⟩
  acc _ _ := True
  trans := fun _ _ => trivial
  func := fun {k} f => match k,f with
    | 0,c => fun _ => collapse || c
    | _+1,f => Empty.elim f
  rel := fun {k} r _ ts => match k,r,ts with
    | _, .eq, ts => ts 0 = ts 1
  persist := fun _ => id

private def same : Sentence exampleLanguage :=
  eqF Equality.eq (constTerm false) (constTerm true)

theorem diagonalDisjunctionFailure :
    Proof Equality.eq true empty (disj same (imp same bot)) ∧
    ¬Proof Equality.eq true empty same ∧ ¬Proof Equality.eq true empty (imp same bot) := by
  have diag b : Diagonal Equality.eq (classicalModel b) := fun _ _ _ => Iff.rfl
  refine ⟨(adequateEquality ..).2 ?_,fun p => ?_,fun p => ?_⟩
  · intro M cg dg w ρ _ _
    by_cases eq : M.eval ρ (constTerm false) = M.eval ρ (constTerm true)
    · exact Or.inl ((forces_eq ..).2 ((dg rfl ..).2 eq))
    · exact Or.inr (fun u _ h => eq ((dg rfl ..).1 ((forces_eq ..).1 h)))
  · have h := (adequateEquality ..).1 p (classicalModel false) (diagonalCongruent _ _ (diag false))
      (fun _ => diag false) () Fin.elim0 trivial (fun _ h => h.elim)
    exact Bool.noConfusion (show false = true from h)
  · have h := (adequateEquality ..).1 p (classicalModel true) (diagonalCongruent _ _ (diag true))
      (fun _ => diag true) () Fin.elim0 trivial (fun _ h => h.elim)
    exact h () trivial rfl

end Identity
end BQL
