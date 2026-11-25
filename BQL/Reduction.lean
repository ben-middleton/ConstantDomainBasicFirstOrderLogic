import BQL.Structural

namespace BQL
open Formula
namespace Derivation
variable {L : Language} {a b c x : Formula L n} {Γ Δ : Theory L n}

theorem here : Derivation L k Γ (insert a Δ) a := .hyp (Or.inl rfl)
theorem identity : Derivation L k Γ Δ (imp a a) := .impI here

theorem constant (h : Derivation L k Γ Δ a) : Derivation L k Γ Δ (imp x a) := .impI (h.add _)

theorem release (p : Derivation L k Γ Δ (imp (conj x a) b)) : Derivation L k Γ Δ (imp x (imp a b)) :=
  .impI (.trans (.meet (constant here) identity) (p.add _))

theorem distribution : Derivation L k Γ Δ (imp (conj x (disj a b)) (disj (conj x a) (conj x b))) :=
  .impI (.orE (.andR here) (.orL (.andI ((andL here).add _) here))
    (.orR (.andI ((andL here).add _) here)))

theorem infiniteDistribution {a : Formula L (n+1)} :
    Derivation L k Γ Δ (imp (conj x (ex a)) (ex (conj x.lift a))) := by
  apply impI
  apply exE (andR here)
  change Derivation _ _ _ _ (ex ((conj x.lift a).subst (up (fun i => .var i.succ))))
  apply exI (.var 0)
  rw [open_lift_binder]
  exact .andI (.andL (.hyp (Or.inr ⟨_,Or.inl rfl,rfl⟩))) here

private def Guarded (k : Depth) (Γ D Δ : Theory L n) (x : Formula L n) :=
  ∀ ⦃a⦄, Δ a → Derivation L k Γ D (imp x a)

private theorem extendGuard (g : Guarded k Γ D Δ x) (a : Formula L n) :
    Guarded k Γ D (insert a Δ) (conj x a) := by
  rintro b (rfl | h)
  · exact .impI (.andR here)
  · exact .trans (.impI (.andL here)) (g h)

private theorem liftGuard (g : Guarded k Γ D Δ x) :
    Guarded k (lifted Γ) (lifted D) (lifted Δ) x.lift :=
  fun _ ⟨_,ha,e⟩ => e ▸ (g ha).lift

/-- One step of relative deduction. The target depth must still admit the
conditional subproof of each modus ponens at the source depth. -/
theorem discharge (p : Derivation L k Γ Δ a) (cap : ∀ j, Below j k → DepthLE j m)
    (x : Formula L n) {D} (g : Guarded m Γ D Δ x) : Derivation L m Γ D (imp x a) := by
  induction p with
  | extra h => exact h.elim
  | global h => exact constant (.global h)
  | hyp h => exact g h
  | topI => exact constant .topI
  | botE _ h => exact .trans (h cap x g) (.impI (.botE here))
  | andI _ _ h v => exact .meet (h cap x g) (v cap x g)
  | andL _ h => exact .trans (h cap x g) (.impI (.andL here))
  | andR _ h => exact .trans (h cap x g) (.impI (.andR here))
  | orL _ h => exact .trans (h cap x g) (.impI (.orL here))
  | orR _ h => exact .trans (h cap x g) (.impI (.orR here))
  | impI _ h => exact release (h cap _ (extendGuard g _))
  | impE e _ major h _ =>
    exact .trans (h cap x g) ((major.raise (cap _ e)).weaken (fun _ => id) (fun _ h => h.elim))
  | orE _ _ _ h u v =>
    exact .trans (.trans (.meet identity (h cap x g)) distribution)
      (.join (u cap _ (extendGuard g _)) (v cap _ (extendGuard g _)))
  | trans _ _ h v => exact .trans (.meet (h cap x g) (v cap x g)) (.impI (.trans (.andL here) (.andR here)))
  | meet _ _ h v => exact .trans (.meet (h cap x g) (v cap x g)) (.impI (.meet (.andL here) (.andR here)))
  | join _ _ h v => exact .trans (.meet (h cap x g) (v cap x g)) (.impI (.join (.andL here) (.andR here)))
  | allI _ h => exact .internalAll (.allI (h cap _ (liftGuard g)))
  | allE t _ h => exact .trans (h cap x g) (.impI (.allE t here))
  | exI t _ h => exact .trans (h cap x g) (.impI (.exI t here))
  | exE _ _ h v =>
    exact .trans (.trans (.meet identity (h cap x g)) infiniteDistribution)
      (.internalEx (.allI (v cap _ (extendGuard (liftGuard g) _))))
  | cd _ h => exact .trans (h cap x g) (.impI (.cd here))
  | internalAll _ h => exact .trans (h cap x g) (.impI (.internalAll here))
  | internalEx _ h => exact .trans (h cap x g) (.impI (.internalEx here))

theorem peel (p : Derivation L (some (k+1)) Γ empty a) : Derivation L (some k) Γ empty a.box := by
  apply discharge p _ top (fun _ h => h.elim)
  intro j e
  cases j <;> simp_all [Below,DepthLE] <;> omega

end Derivation

namespace Tree
export Derivation (peel discharge constant)
end Tree

private theorem boxes_succ (a : Formula L n) (k) : a.box.boxes k = a.boxes (k+1) := by
  induction k with
  | zero => rfl
  | succ _ ih => exact congrArg box ih

theorem reduceAt {Γ : Theory L n} {a : Formula L n} (p : Derivation L (some k) Γ empty a) :
    Basic Γ (a.boxes k) := by
  induction k generalizing a with
  | zero => exact p
  | succ k ih => exact boxes_succ a k ▸ ih p.peel

theorem reduction {Γ : Theory L n} {a : Formula L n} (p : Proves Γ a) :
    ∃ k, Basic Γ (a.boxes k) := by
  obtain ⟨k,hk⟩ := p.bounded
  exact ⟨k,reduceAt (hk k (Nat.le_refl _))⟩

theorem unbox {Γ : Theory L n} {a : Formula L n} (p : Proves Γ (a.boxes k)) : Proves Γ a := by
  induction k with
  | zero => exact p
  | succ _ ih => exact ih (.impE (j := none) trivial .topI p)

end BQL
