import BQL.TruthStages

/-! Closure-stage bounds from the appendix. Natural numbers code both finite
iterations of the box connective and the observations that distinguish successive
worlds. Limit stages below are unions of predecessor sets. -/
namespace BQL.Truth
open Formula Iteration Encoding

namespace BoxCode

private def add : PR 2 := .recu (.proj 0) (.comp .succ (fun _ => .proj 0))
private theorem run_add (xs : Fin 2 → Nat) : add.run xs = xs 0 + xs 1 := by
  change Nat.rec (motive := fun _ => Nat) (xs 1) (fun _ r => r+1) (xs 0) = _
  generalize xs 0 = x
  induction x with
  | zero => exact (Nat.zero_add _).symm
  | succ k ih => exact (congrArg Nat.succ ih).trans (Nat.succ_add ..).symm

private def double : PR 1 := .comp add (fun _ => .proj 0)
private theorem run_double (xs : Fin 1 → Nat) : double.run xs = 2*(xs 0) := by
  unfold double
  rw [PR.run,run_add]
  change xs 0 + xs 0 = _
  omega

private def succOf (p : PR 1) : PR 1 := .comp .succ (fun _ => p)
private def doubleOf (p : PR 1) : PR 1 := .comp double (fun _ => p)

private def tag : Nat → PR 1
  | 0 => succOf double
  | k+1 => succOf (succOf (doubleOf (tag k)))

private theorem run_tag (k) (xs : Fin 1 → Nat) : (tag k).run xs = pair k (xs 0) := by
  induction k with
  | zero => exact congrArg Nat.succ (run_double xs)
  | succ k ih =>
    change double.run (fun _ => (tag k).run xs) + 2 = _
    rw [run_double,ih,pair]

private def box : PR 1 := .comp (tag 6) (fun _ => tag (Godel.formula (top : AFml 0)))

private theorem run_box (a : AFml 0) :
    box.run (fun _ => Godel.formula a) = Godel.formula a.box := by
  change (tag 6).run _ = _
  rw [run_tag,run_tag]
  rfl

/-- Binary program on a box count and a sentence code. -/
def iterate : PR 2 := .recu (.proj 0) (.comp box (fun _ => .proj 0))

theorem run_iterate (a : AFml 0) (n : Nat) :
    iterate.run (extend (fun _ => Godel.formula a) n) = Godel.formula (a.boxes n) := by
  change Nat.rec (motive := fun _ => Nat) (Godel.formula a) (fun _ r => box.run (fun _ => r)) n = _
  induction n with
  | zero => rfl
  | succ n ih => exact (congrArg (fun r => box.run (fun _ => r)) ih).trans (run_box _)

end BoxCode

def omegaBox (a : AFml 0) : AFml 0 :=
  ex (truthOf (.app BoxCode.iterate (extend (fun _ => (numeral (coding.code a)).lift) (.var 0))))

theorem omegaBox_iff (w : standard.W) (a : AFml 0) :
    standard.Forces w closedEnv (omegaBox a) ↔ ∃ n, standard.Forces w closedEnv (a.boxes n) := by
  apply exists_congr
  intro n

  have v : standard.eval (extend closedEnv n) (numeral (coding.code a)).lift = coding.code a :=
    (standard.eval_lift ..).trans ((eval_standard ..).trans (value_numeral _))
  have args : (fun j => standard.eval (extend closedEnv n)
      (extend (fun _ : Fin 1 => (numeral (coding.code a)).lift) (.var 0) j)) =
      extend (fun _ : Fin 1 => Godel.formula a) n := funext (fun j => Fin.cases rfl (fun _ => v) j)
  change extension arithmetic coding w.val (BoxCode.iterate.run (fun j => standard.eval (extend closedEnv n)    (extend (fun _ : Fin 1 => (numeral (coding.code a)).lift) (.var 0) j))) ↔ _
  rw [args,BoxCode.run_iterate]
  exact transparency ..

def advance (w : standard.W) : Nat → standard.W
  | 0 => w
  | n+1 => successorWorld (advance w n)

private theorem nextBox {w : standard.W} {a : AFml 0} (h : standard.Forces w closedEnv (Formula.box a)) :
    standard.Forces (successorWorld w) closedEnv (Formula.box (Formula.box a)) := by
  intro z e _
  apply (truth ..).2
  rcases e.2 with old | same
  · obtain ⟨u,sub,eq⟩ := origin arithmetic coding w.property old
    exact eq ▸ (truth ..).1 (standard.persistence (w := w) (u := u) ⟨sub,eq.symm ▸ old⟩ closedEnv _ h)
  · exact same.symm ▸ (truth ..).1 h

theorem advanceTrue {w : standard.W} {a : AFml 0} (h : standard.Forces w closedEnv a.box) (n) :
    standard.Forces (advance w n) closedEnv (a.boxes (n+1)) := by
  induction n with
  | zero => exact h
  | succ _ ih => exact nextBox ih

theorem advanceFalse {w : standard.W} {a : AFml 0} (h : ¬standard.Forces w closedEnv a) (n) :
    ¬standard.Forces (advance w n) closedEnv (a.boxes n) := by
  induction n with
  | zero => exact h
  | succ _ ih => exact fun hh => ih (hh _ (successorEdge _) trivial)

def limitWorld (W : Nat → standard.W) : standard.W :=
  ⟨sup (fun s => ∃ n, (successorWorld (W n)).val = s),
    .limit _ (fun _ ⟨n,e⟩ => e ▸ (successorWorld (W n)).property)⟩

theorem limitEdge (W : Nat → standard.W) (n) : standard.acc (limitWorld W) (W n) :=
  ⟨fun _ h => ⟨_,⟨n,rfl⟩,Or.inl h⟩,⟨_,⟨n,rfl⟩,Or.inr rfl⟩⟩

theorem limitTrue {w : standard.W} {a : AFml 0} (h : standard.Forces w closedEnv a.box) :
    standard.Forces (limitWorld (advance w)) closedEnv (omegaBox a).box := by
  intro z e _
  obtain ⟨_,⟨n,rfl⟩,old | same⟩ := e.2
  · obtain ⟨u,sub,eq⟩ := origin arithmetic coding (advance w n).property old
    have edge : standard.acc (advance w n) u := ⟨sub,eq.symm ▸ old⟩
    have hu := standard.persistence edge closedEnv _ ((omegaBox_iff _ _).2 ⟨_,advanceTrue h n⟩)
    exact (truth ..).2 (eq ▸ (truth ..).1 hu)
  · exact (truth ..).2 (same.symm ▸ (truth ..).1 ((omegaBox_iff _ _).2 ⟨_,advanceTrue h n⟩))

theorem limitFalse {w : standard.W} {a : AFml 0} (h : ¬standard.Forces w closedEnv a) :
    ¬standard.Forces (limitWorld (advance w)) closedEnv (omegaBox a) := by
  intro hh
  obtain ⟨n,hn⟩ := (omegaBox_iff ..).1 hh
  exact advanceFalse h n (standard.persistence (limitEdge _ n) _ _ hn)

/-- Stage ω·k and the corresponding k-fold iteration of □^{<ω}. -/
def omegaStage : Nat → standard.W
  | 0 => initial
  | k+1 => limitWorld (advance (omegaStage k))

def omegaFormula : Nat → AFml 0
  | 0 => bot
  | k+1 => omegaBox (omegaFormula k)

theorem omegaStageBounds (k n : Nat) :
    standard.Forces (advance (omegaStage k) n) closedEnv ((omegaFormula k).boxes (n+1)) ∧
    ¬standard.Forces (advance (omegaStage k) n) closedEnv ((omegaFormula k).boxes n) := by
  have h : standard.Forces (omegaStage k) closedEnv (omegaFormula k).box ∧
      ¬standard.Forces (omegaStage k) closedEnv (omegaFormula k) := by
    induction k with
    | zero => exact ⟨finiteBoxes 0,id⟩
    | succ k ih => exact ⟨limitTrue ih.1,limitFalse ih.2⟩
  exact ⟨advanceTrue h.1 n,advanceFalse h.2 n⟩

private def instanceCode (i : Instance arithmetic) : Nat :=
  pair i.arity (pair (Godel.formula i.formula) (tuple i.env))

private theorem instance_inj {i j} (h : instanceCode i = instanceCode j) : i = j := by
  cases i with | mk a ρ =>
    cases j with | mk b σ =>
      obtain ⟨rfl,h⟩ := pair_eq.mp h
      obtain ⟨hf,he⟩ := pair_eq.mp h
      cases Godel.formula_inj hf
      cases funext (tuple_inj he)
      rfl

private abbrev observation (w : standard.W) := point arithmetic coding w.val
private def Loss (w : standard.W) (i : Instance arithmetic) :=
  observation w i ∧ ¬observation (successorWorld w) i

private theorem observation_mono {u v : standard.W} (uv : Subset u.val v.val) :
    Subset (observation v) (observation u) := fun i =>
  localMono arithmetic uv (decreasing arithmetic coding uv) i.env i.formula

private theorem stopped {w : standard.W} (h : ¬∃ i, Loss w i) : successorWorld w = standardRoot := by
  have eq : observation w = observation (successorWorld w) :=
    antisymm (fun i hi => Classical.byContradiction (fun hn => h ⟨i,hi,hn⟩))
      (observation_mono (fun _ => Or.inl))
  apply (reflexive_iff_root ..).1
  exact ⟨fun _ => id,Or.inr eq.symm⟩

private theorem strictNext {u v : standard.W} (h : ¬Subset v.val u.val) :
    Subset (successorWorld u).val v.val :=
  successor_below _ (fun _ _ => Or.inl) u.property v.property h

private noncomputable def worldCode (w : standard.W) : Nat := by
  classical
  exact if w = standardRoot then 0 else if h : ∃ i, Loss w i then instanceCode (Classical.choose h) + 2 else 1

private theorem distinguish {u v : standard.W} (h : ¬Subset v.val u.val) : worldCode u ≠ worldCode v := by
  classical
  have ur : u ≠ standardRoot := fun e => h (e ▸ contained _ v.property)
  by_cases vr : v = standardRoot
  · simp only [worldCode,if_neg ur,if_pos vr]
    split <;> omega
  · simp only [worldCode,if_neg ur,if_neg vr]
    split <;> rename_i hu <;> split <;> rename_i hv
    · intro eq
      have hi := instance_inj (Nat.add_right_cancel eq)
      have loss := Classical.choose_spec hu
      exact loss.2 (observation_mono (strictNext h) (hi.symm ▸ (Classical.choose_spec hv).1))
    · omega
    · omega
    · have vu : Subset standardRoot.val v.val := stopped hu ▸ strictNext h
      exact (vr (Subtype.ext (antisymm (contained _ v.property) vu))).elim

/-- The closure chain has only countably many stages. Every strict loss is
identified by a coded formula and assignment. The root and its possible
predecessor with the same valuation receive separate codes. -/
theorem countableStages : ∃ f : standard.W → Nat, ∀ u v, f u = f v → u = v := by
  classical
  refine ⟨worldCode,fun u v e => ?_⟩
  by_cases uv : Subset u.val v.val
  · by_cases vu : Subset v.val u.val
    · exact Subtype.ext (antisymm uv vu)
    · exact (distinguish vu e).elim
  · exact (distinguish uv e.symm).elim

end BQL.Truth
