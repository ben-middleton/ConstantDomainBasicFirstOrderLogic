import BQL.Reduction

namespace BQL
open Formula
namespace Derivation
variable {L : Language} {Γ Δ G D : Theory L n} {a : Formula L n}

private def Replace (k : Depth) (G D Γ : Theory L n) := ∀ ⦃a⦄, Γ a → Derivation L k G D a
private theorem underInsert (h : Replace k G D Γ) (a : Formula L n) : Replace k G (insert a D) (insert a Γ) := by
  rintro _ (rfl | hx)
  · exact here
  · exact (h hx).add _

private theorem underLift (h : Replace k G D Γ) : Replace k (lifted G) (lifted D) (lifted Γ) :=
  fun _ ⟨_,hx,e⟩ => e ▸ (h hx).lift

theorem noBelowZero (j : Depth) : ¬ Below j (some 0) := by cases j <;> simp [Below]

/-- Simultaneous cut into a detachment-free proof, with arbitrary proofs for
the substituted assumptions. -/
theorem cutBasic (p : Derivation L i Γ Δ a) (base : i = some 0)
    (g : Replace k G D Γ) (d : Replace k G D Δ) : Derivation L k G D a := by
  induction p with
  | extra h => exact h.elim
  | global h => exact g h
  | hyp h => exact d h
  | topI => exact .topI
  | botE _ h => exact .botE (h base g d)
  | andI _ _ h v => exact .andI (h base g d) (v base g d)
  | andL _ h => exact .andL (h base g d)
  | andR _ h => exact .andR (h base g d)
  | orL _ h => exact .orL (h base g d)
  | orR _ h => exact .orR (h base g d)
  | impE e => exact (noBelowZero _ (base ▸ e)).elim
  | impI _ h => exact .impI (h base (fun _ h => (g h).add _) (underInsert d _))
  | orE _ _ _ h u v =>
    exact .orE (h base g d)
      (u base (fun _ h => (g h).add _) (underInsert d _))
      (v base (fun _ h => (g h).add _) (underInsert d _))
  | trans _ _ h v => exact .trans (h base g d) (v base g d)
  | meet _ _ h v => exact .meet (h base g d) (v base g d)
  | join _ _ h v => exact .join (h base g d) (v base g d)
  | allI _ h => exact .allI (h base (underLift g) (underLift d))
  | allE t _ h => exact .allE t (h base g d)
  | exI t _ h => exact .exI t (h base g d)
  | exE _ _ h v =>
    exact .exE (h base g d)
      (v base (fun _ h => (underLift g h).add _) (underInsert (underLift d) _))
  | internalAll _ h => exact .internalAll (h base g d)
  | internalEx _ h => exact .internalEx (h base g d)
  | cd _ h => exact .cd (h base g d)

theorem pad {a : Formula L n} (h : Derivation L k Γ Δ (a.boxes i)) (ij : i ≤ j) :
    Derivation L k Γ Δ (a.boxes j) := by
  induction ij with
  | refl => exact h
  | step _ ih => exact constant ih

end Derivation

namespace Tree
export Derivation (pad cutBasic)
end Tree

private theorem basicBranch {Γ : Theory L n} {a b : Formula L n} (p : Basic (insert a Γ) b) :
    Derivation L none Γ (insert a empty) b :=
  p.cutBasic rfl (fun _ h => h.elim (fun e => e ▸ Derivation.here) Derivation.global) (fun _ h => h.elim)

theorem unrestrictedOr {Γ : Theory L n} {a b c : Formula L n} (h : Proves Γ (disj a b))
    (l : Proves (insert a Γ) c) (r : Proves (insert b Γ) c) : Proves Γ c := by
  obtain ⟨i,li⟩ := reduction l
  obtain ⟨j,rj⟩ := reduction r
  apply unbox (k := max i j)
  exact .orE h (basicBranch (li.pad (Nat.le_max_left ..))) (basicBranch (rj.pad (Nat.le_max_right ..)))

theorem lift_boxes (a : Formula L n) (k) : (a.boxes k).lift = a.lift.boxes k := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg box ih

theorem unrestrictedEx {Γ : Theory L n} {a : Formula L (n+1)} {b : Formula L n}
    (h : Proves Γ (ex a)) (p : Proves (insert a (lifted Γ)) b.lift) : Proves Γ b := by
  obtain ⟨k,p⟩ := reduction p
  apply unbox (k := k)
  apply Derivation.exE h
  rw [lift_boxes]
  exact p.cutBasic rfl (fun _ h => h.elim (fun e => e ▸ Derivation.here) Derivation.global) (fun _ h => h.elim)

end BQL
