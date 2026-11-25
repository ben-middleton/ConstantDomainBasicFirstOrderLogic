import BQL.NaiveTruth

namespace BQL.Truth
open Formula Iteration

def initial : standard.W :=
  ⟨sup (fun _ => False),.limit _ (fun _ h => h.elim)⟩

def successorWorld (w : standard.W) : standard.W := ⟨next arithmetic coding w.val,.step w.property⟩

theorem successorEdge (w : standard.W) : standard.acc (successorWorld w) w :=
  ⟨fun _ => Or.inl, Or.inr rfl⟩

theorem initialTerminal (u : standard.W) : ¬standard.acc initial u := fun h => by
  obtain ⟨_,hf,_⟩ := h.2
  exact hf

theorem rootSees (u : standard.W) : standard.acc standardRoot u :=
  ⟨contained _ u.property, contained _ (.step u.property) (Or.inr rfl)⟩

def finiteWorld : Nat → standard.W
  | 0 => initial
  | n+1 => successorWorld (finiteWorld n)

theorem finiteBoxes (n : Nat) : standard.Forces (finiteWorld n) closedEnv ((bot : AFml 0).boxes (n+1)) := by
  induction n with
  | zero => exact fun u e => (initialTerminal u e).elim
  | succ n ih =>
    intro z e _
    change standard.Forces z closedEnv ((bot : AFml 0).boxes (n+1))
    rcases e.2 with old | same
    · -- The new world inherits every old successor valuation.
      obtain ⟨u,sub,eq⟩ := origin arithmetic coding (finiteWorld n).property old
      have edge : standard.acc (finiteWorld n) u := ⟨sub,eq.symm ▸ old⟩
      have hu := (truth arithmetic coding _ u closedEnv).1 (standard.persistence edge _ _ ih)
      apply (truth ..).2
      exact eq ▸ hu
    · have h := (truth arithmetic coding _ (finiteWorld n) closedEnv).1 ih
      exact (truth ..).2 (same.symm ▸ h)

theorem finiteStrict (n : Nat) : ¬standard.Forces (finiteWorld n) closedEnv ((bot : AFml 0).boxes n) := by
  induction n with
  | zero => exact id
  | succ n ih => exact fun h => ih (h _ (successorEdge _) trivial)

theorem rootBeyondFinite (n : Nat) : standardRoot ≠ finiteWorld n := by
  intro eq
  have h := finiteBoxes n
  rw [← eq] at h
  have impossible (k : Nat) : ¬standard.Forces standardRoot closedEnv ((bot : AFml 0).boxes k) := by
    induction k with
    | zero => exact id
    | succ k ih => exact fun h => ih (h _ (root_loop ..) trivial)
  exact impossible _ h

theorem classicalDoubleNegationFails :
    ¬standard.Forces standardRoot closedEnv (imp (imp (equal zeroTerm zeroTerm) bot) bot) := fun h =>
  h initial (rootSees _) (fun u e => (initialTerminal u e).elim)

/-- The usual uncurried induction principle already fails for the predicate y = 0. -/
theorem uncurriedInductionFails :
    let a : AFml 1 := equal (.var 0) zeroTerm
    let step := a.subst (extend (fun i => .var i.succ) (successor (.var 0)))
    ¬standard.Forces standardRoot closedEnv (imp (conj (a.inst zeroTerm) (all (imp a step))) (all a)) := by
  intro a step h
  have hall := h initial (rootSees _) ⟨rfl,fun _ u e => (initialTerminal u e).elim⟩
  exact Nat.noConfusion (show 1 = 0 from hall (1 : Nat))

end BQL.Truth
