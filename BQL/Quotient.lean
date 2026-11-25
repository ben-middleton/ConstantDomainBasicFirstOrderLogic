import BQL.Identity

namespace BQL.Identity
variable {L : Language} (E : L.Rel 2)

private noncomputable def rep (s : Setoid D) (x : Quotient s) : D :=
  Classical.choose (Quotient.exists_rep x)

private theorem mk_rep (s : Setoid D) (x : Quotient s) : Quotient.mk s (rep s x) = x :=
  Classical.choose_spec (Quotient.exists_rep x)

private theorem same_rep (s : Setoid D) (x : D) : s.r (rep s (Quotient.mk s x)) x :=
  Quotient.exact (mk_rep s _)

structure Rigid (M : Model L) where
  setoid : Setoid M.D
  agrees : ∀ w x y, EqAt E M w x y ↔ setoid.r x y
  congruent : ∀ w, Congruent E M w

namespace Rigid
variable {E} {M : Model L} (R : Rigid E M)

noncomputable def quotient : Model L where
  W := M.W
  D := Quotient R.setoid
  domain := M.domain.elim (fun x => ⟨Quotient.mk _ x⟩)
  worlds := M.worlds
  acc := M.acc
  trans := M.trans
  func f ts := Quotient.mk _ (M.func f (fun i => rep R.setoid (ts i)))
  rel r w ts := M.rel r w (fun i => rep R.setoid (ts i))
  persist := M.persist

theorem diagonal : Diagonal E R.quotient := by
  intro w x y
  change M.rel E w (fun i => rep R.setoid (two x y i)) ↔ x = y
  rw [map_two]
  refine (R.agrees w _ _).trans ⟨fun h => ?_,fun e => e ▸ R.setoid.refl _⟩
  exact (mk_rep _ x).symm.trans ((Quotient.sound h).trans (mk_rep _ y))

theorem term (t : Term L n) (ρ : Fin n → M.D) :
    R.quotient.eval (Quotient.mk R.setoid ∘ ρ) t = Quotient.mk R.setoid (M.eval ρ t) := by
  induction t with
  | var => rfl
  | app f ts ih =>
    apply Quotient.sound
    obtain ⟨w⟩ := M.worlds
    apply (R.agrees w ..).1
    apply (R.congruent w).func
    intro i
    change EqAt E M w (rep _ (R.quotient.eval _ (ts i))) _
    rw [ih]
    exact (R.agrees w ..).2 (same_rep _ _)

theorem forces (w : M.W) (ρ : Fin n → M.D) (a : Formula L n) :
    R.quotient.Forces w (Quotient.mk R.setoid ∘ ρ) a ↔ M.Forces w ρ a := by
  induction a generalizing w with
  | top | bot => rfl
  | atom r ts =>
    change M.rel r w (fun i => rep _ (R.quotient.eval _ (ts i))) ↔ M.rel r w _
    simp only [term]
    have eq i := (R.agrees w ..).2 (same_rep R.setoid (M.eval ρ (ts i)))
    exact ⟨(R.congruent w).rel r _ _ eq,(R.congruent w).rel r _ _ (fun i => (R.congruent w).equiv.symm (eq i))⟩
  | conj _ _ ih ik => exact and_congr (ih ..) (ik ..)
  | disj _ _ ih ik => exact or_congr (ih ..) (ik ..)
  | imp _ _ ih ik => simp only [Model.Forces,ih,ik]; rfl
  | all a ih =>
    constructor
    · intro h x
      apply (ih w _).1
      exact (show Quotient.mk R.setoid ∘ extend ρ x = extend (Quotient.mk R.setoid ∘ ρ) (Quotient.mk _ x)
        from funext (fun j => Fin.cases rfl (fun _ => rfl) j)) ▸ h _
    · intro h x
      induction x using Quotient.ind with
      | _ y => exact (show Quotient.mk R.setoid ∘ extend ρ y = extend (Quotient.mk R.setoid ∘ ρ) (Quotient.mk _ y)
          from funext (fun j => Fin.cases rfl (fun _ => rfl) j)) ▸ (ih ..).2 (h y)
  | ex a ih =>
    constructor
    · rintro ⟨x,h⟩
      induction x using Quotient.ind with
      | _ y =>
        refine ⟨y,(ih ..).1 ?_⟩
        exact (show Quotient.mk R.setoid ∘ extend ρ y = extend (Quotient.mk R.setoid ∘ ρ) (Quotient.mk _ y)
          from funext (fun j => Fin.cases rfl (fun _ => rfl) j)) ▸ h
    · rintro ⟨y,h⟩
      exact ⟨_,(show Quotient.mk R.setoid ∘ extend ρ y = extend (Quotient.mk R.setoid ∘ ρ) (Quotient.mk _ y)
          from funext (fun j => Fin.cases rfl (fun _ => rfl) j)) ▸ (ih ..).2 h⟩
end Rigid

def restricted (d : Bool) (Γ : Theory L 0) (a : Sentence L) :=
  ∀ M : Model L, (∀ w, Congruent E M w) → (d = true → Diagonal E M) →
    ∀ w η, M.acc w w → M.Satisfies w η Γ → M.Forces w η a

/-- The axiomatic presentations of the two identity extensions. -/
theorem adequateEquality (d : Bool) (Γ : Theory L 0) (a : Sentence L) :
    Derivable (fun b => Γ b ∨ Laws E d b) a ↔ restricted E d Γ a := by
  rw [adequate]
  constructor
  · intro h M cg dg w η loop g
    exact h M w η loop (fun b hb => hb.elim (g b) (laws_hold E M cg dg w η b))
  · intro h M w η loop g
    have laws : M.Satisfies w η (Laws E d) := fun b hb => g b (Or.inr hb)
    let N := generated M w loop
    let root : N.W := ⟨w,loop⟩
    have cg (u : N.W) : Congruent E N u := by
      have c := laws_congruent E M w u.val u.property laws
      exact ⟨c.equiv,c.func,c.rel⟩
    have ng : N.Satisfies root η Γ := fun b hb => (generated_forces M w loop root η b).2 (g b (Or.inl hb))
    apply (generated_forces M w loop root η a).1
    cases d with
    | false => exact h N cg (fun e => by contradiction) root η loop ng
    | true =>
      let R : Rigid E N := {
        setoid := ⟨EqAt E M w,(cg root).equiv⟩
        congruent := cg
        agrees := by
          intro u x y
          refine ⟨fun ex => ?_,fun eq => M.persist u.property eq⟩
          have em := (forces_close ..).1 (laws _ (.em rfl)) (two x y)
          exact em.elim ((forces_eq ..).1) (fun hn => (hn u.val u.property ((forces_eq ..).2 ex)).elim) }
      apply (R.forces root η a).1
      exact h R.quotient (diagonalCongruent E _ R.diagonal) (fun _ => R.diagonal) root _ loop
        (fun b hb => (R.forces root η b).2 (ng b hb))

end BQL.Identity
