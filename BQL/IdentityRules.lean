import BQL.Quotient
import BQL.Properties

namespace BQL.Identity
open Formula
variable {L : Language} {E : L.Rel 2}

theorem term_congr (M : Model L) (w) (cg : Congruent E M w) {ρ σ : Fin n → M.D}
    (eq : ∀ i, EqAt E M w (ρ i) (σ i)) (t : Term L n) : EqAt E M w (M.eval ρ t) (M.eval σ t) := by
  induction t with
  | var i => exact eq i
  | app f _ ih => exact cg.func f _ _ ih

theorem forcing_congr (M : Model L) (cg : ∀ w, Congruent E M w) (w)
    {ρ σ : Fin n → M.D} (eq : ∀ i, EqAt E M w (ρ i) (σ i)) (a : Formula L n) :
    M.Forces w ρ a ↔ M.Forces w σ a := by
  induction a generalizing w with
  | top | bot => rfl
  | atom r ts =>
    have he i := term_congr M w (cg w) eq (ts i)
    exact ⟨(cg w).rel r _ _ he,(cg w).rel r _ _ (fun i => (cg w).equiv.symm (he i))⟩
  | conj _ _ ih ik => exact and_congr (ih w eq) (ik w eq)
  | disj _ _ ih ik => exact or_congr (ih w eq) (ik w eq)
  | imp _ _ ih ik =>
    have future z (e : M.acc w z) i : EqAt E M z (ρ i) (σ i) := M.persist e (eq i)
    exact ⟨fun h z e hx => (ik z (future z e)).1 (h z e ((ih z (future z e)).2 hx)),
      fun h z e hx => (ik z (future z e)).2 (h z e ((ih z (future z e)).1 hx))⟩
  | all _ ih => exact forall_congr' (fun d => ih w (Fin.cases ((cg w).equiv.refl d) eq))
  | ex _ ih => exact exists_congr (fun d => ih w (Fin.cases ((cg w).equiv.refl d) eq))

abbrev Proof (E : L.Rel 2) (d : Bool) (Γ : Theory L 0) (a : Sentence L) :=
  Derivable (fun b => Γ b ∨ Laws E d b) a

theorem identityIntro (s : Term L 0) : Proof E d Γ (eqF E s s) := by
  apply (adequateEquality ..).2
  exact fun M cg _ w ρ _ _ => (forces_eq ..).2 ((cg w).equiv.refl (M.eval ρ s))

theorem identityElim {s t : Term L 0} {a : Formula L 1} (e : Proof E d Γ (eqF E s t))
    (h : Proof E d Γ (a.inst s)) : Proof E d Γ (a.inst t) := by
  apply (adequateEquality ..).2
  intro M cg dg w ρ r g
  have he := (forces_eq ..).1 ((adequateEquality ..).1 e M cg dg w ρ r g)
  have ha := (M.forces_inst ..).1 ((adequateEquality ..).1 h M cg dg w ρ r g)
  apply (M.forces_inst ..).2
  exact (forcing_congr M cg w (ρ := extend ρ (M.eval ρ s)) (σ := extend ρ (M.eval ρ t))
    (Fin.cases he (fun i => (cg w).equiv.refl (ρ i))) a).1 ha

private theorem close_fragment (a : Formula L n) (h : NegativeFragment a) : NegativeFragment (close a) := by
  induction n with
  | zero => exact h
  | succ _ ih => exact ih (all a) (.all h)
private theorem agreement_fragment (k : Nat) : NegativeFragment (agree E k) := by
  have aux {n j} (as : Fin j → Formula L n) (h : ∀ i, NegativeFragment (as i)) : NegativeFragment (meetAll as) := by
    induction j with
    | zero => exact .top
    | succ j ih => exact .conj (h 0) (ih _ (fun i => h i.succ))
  exact aux _ (fun _ => .atom)

theorem laws_fragment {a : Sentence L} (h : Laws E false a) : NegativeFragment a := by
  cases h <;> apply close_fragment
  case refl => exact .atom
  case symm => exact .imp .atom .atom
  case trans => exact .imp (.conj .atom .atom) .atom
  case func => exact .imp (agreement_fragment _) .atom
  case rel => exact .imp (.conj (agreement_fragment _) .atom) .atom
  case em flag => contradiction

theorem congruenceDisjunction {Γ : Theory L 0} (hf : ∀ a, Γ a → NegativeFragment a)
    (p : Proof E false Γ (disj a b)) : Proof E false Γ a ∨ Proof E false Γ b :=
  (disjunctionProperty _ (fun a h => h.elim (hf a) laws_fragment) _ _ (adequate.mp p)).imp adequate.mpr adequate.mpr

theorem congruenceExistence {Γ : Theory L 0} (hf : ∀ a, Γ a → NegativeFragment a)
    (c : Term L 0) (p : Proof E false Γ (ex a)) : ∃ t, Proof E false Γ (a.inst t) :=
  (existenceProperty _ (fun a h => h.elim (hf a) laws_fragment) c a (adequate.mp p)).imp (fun _ => adequate.mpr)

end BQL.Identity
