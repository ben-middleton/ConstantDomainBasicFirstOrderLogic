import BQL.FiniteSupport
import BQL.Completeness
import BQL.TJK

namespace BQL
open Formula
variable {L : Language} {Γ Δ : Theory L n} {a : Formula L n}

namespace Derivation
theorem memberOfConjunction (xs : List (Formula L n)) (h : Derivation L k Γ Δ (conjunction xs))
    {a} (ha : a ∈ xs) : Derivation L k Γ Δ a := by
  induction xs with
  | nil => contradiction
  | cons b xs ih => exact (List.mem_cons.mp ha).elim (fun e => e ▸ andL h) (fun hm => ih (andR h) hm)

theorem allEmbedding {a : Formula L (n+1)} (m) (p : Derivation L k Γ Δ (all (a.boxes m))) :
    Derivation L k Γ Δ ((all a).boxes m) := by
  induction m generalizing Γ Δ with
  | zero => exact p
  | succ m ih => exact trans (internalAll p) (impI (ih here))
end Derivation

/-- Section 4 uses index 0 for a proof whose conditional premises are
detachment-free. Its index n thus corresponds to depth n+1 here. -/
theorem relativeDeduction (xs : List (Formula L n)) (p : Derivation L (some (k+1)) Γ (fun b => b ∈ xs) a) :
    Basic Γ ((imp (conjunction xs) a).boxes k) := by
  apply reduceAt
  apply p.discharge _ (conjunction xs)
  · intro b hb
    exact .impI (Derivation.memberOfConjunction xs Derivation.here hb)
  · intro j e
    cases j <;> simp_all [Below,Derivation.DepthLE] <;> omega

private theorem liftRule {G : Theory L n} (p : Basic Γ a) (x : Formula L n)
    (h : ∀ b, Γ b → Basic G (imp x b)) : Basic G (imp x a) := by
  have q : Derivation L (some 0) G Γ a := p.cutBasic rfl (fun _ ha => .hyp ha) (fun _ h => h.elim)
  exact q.discharge (fun j hj => (Derivation.noBelowZero j hj).elim) x (fun _ => h _)

def boxed (Γ : Theory L n) (k : Nat) : Theory L n := fun a => ∃ b, Γ b ∧ b.boxes k = a

theorem regularity (p : Basic Γ a) (k) : Basic (boxed Γ k) (a.boxes k) := by
  induction k with
  | zero => exact p.weaken (fun b hb => ⟨b,hb,rfl⟩) (fun _ => id)
  | succ k ih =>
    apply liftRule ih top
    rintro _ ⟨b,hb,rfl⟩
    exact .global ⟨b,hb,rfl⟩

theorem internalization (xs : List (Formula L n)) (p : Basic (fun b => b ∈ xs) a) :
    TJK L e empty (imp (conjunction xs) a) := by
  apply TJK.internalize p rfl (conjunction xs) _ (fun _ h => h.elim)
  intro b hb
  have h : Basic empty (imp (conjunction xs) b) :=
    .impI (Derivation.memberOfConjunction xs Derivation.here hb)
  exact TJK.ofRoot (h.raise trivial)

namespace Canonical

/-- Closure under derivations from the whole theory follows from the
one-premise closure and conjunction fields of a canonical point. -/
theorem Point.basicClosure (w : Point L) {a : Sentence L} (p : Basic w.mem a) : w.mem a := by
  obtain ⟨xs,hx,pr⟩ := FiniteSupport.finitePremises p
  have hc : w.mem (conjunction xs) := by
    clear pr
    induction xs with
    | nil => exact w.top
    | cons b xs ih => exact w.meet (hx b (.head _)) (ih (fun _ h => hx _ (.tail _ h)))
  apply w.closed _ hc
  exact pr.cutBasic rfl (fun _ hb => Derivation.memberOfConjunction xs (.global rfl) hb) (fun _ h => h.elim)

theorem Point.rootClosure (w : Point L) (loop : Access w w) {a : Sentence L} (p : Proves w.mem a) : w.mem a := by
  obtain ⟨j,q⟩ := reduction p
  have h := w.basicClosure q
  clear q
  induction j with
  | zero => exact h
  | succ _ ih => exact ih (loop h w.top)

private def unitModel (L : Language) : Model L where
  W := Unit
  D := Unit
  worlds := ⟨()⟩
  domain := ⟨()⟩
  acc _ _ := True
  trans := fun _ _ => trivial
  func _ _ := ()
  rel _ _ _ := False
  persist := fun _ => id

theorem pointNonempty (c : Term L 0) : Nonempty (Point L) := by
  let M := unitModel L
  let η : Fin 0 → M.D := Fin.elim0
  refine ⟨⟨M.Forces () η, trivial,id,?_,fun ha hb => ⟨ha,hb⟩,id,?_,?_⟩⟩
  · intro a b p h
    exact soundness (p.raise trivial) M () η trivial (fun _ e => e ▸ h)
  · intro a h d
    cases d
    exact (M.forces_inst ..).1 (h c)
  · rintro a ⟨d,hd⟩
    cases d
    exact ⟨c,(M.forces_inst ..).2 hd⟩

end Canonical
end BQL
