import BQL.NaiveTruth
import BQL.TJK
import BQL.IdentityRules

namespace BQL
open Formula

/-- The paper's main equivalence, with no assumption on the base signature. -/
theorem tjk_iff_entails {L : Language} (Γ : Theory L 0) (a : Sentence L) :
    TJK (parameters L) true (image (inclusion L) Γ) ((inclusion L).form a) ↔ Entails Γ a :=
  equivalentTJK.symm.trans adequate

namespace Truth
open Iteration
variable (A : Arithmetic) (C : Coding A)

/-- Inflationary presentation of the local iteration, starting at the empty
union. On every generated stage, its successor is exactly the paper's Φ(X). -/
def localStep (S : Predecessors A) (X : Nat → Prop) := fun i => X i ∨ operator A C S X i

theorem localIncreasing (S : Predecessors A) {X} (h : Stage (localStep A C S) X) :
    Subset X (operator A C S X) := by
  induction h with
  | @step x _ ih =>
    intro i hi
    have lift := operatorMono A C (X := x) (Y := localStep A C S x) (S := S) (T := S) (fun _ => id) (fun _ => Or.inl)
    exact hi.elim (fun hx => lift (ih hx)) (fun hx => lift hx)
  | limit s _ ih =>
    rintro i ⟨x,hx,hi⟩
    exact operatorMono A C (fun _ => id) (fun _ h => ⟨x,hx,h⟩) (ih x hx hi)

theorem localSuccessor (S : Predecessors A) {X} (h : Stage (localStep A C S) X) :
    localStep A C S X = operator A C S X :=
  antisymm (fun _ hx => hx.elim (fun h' => localIncreasing A C S h h') id) (fun _ => Or.inr)

theorem localConvergence (S : Predecessors A) : total (localStep A C S) = extension A C S := by
  let f := localStep A C S
  have inc X : Subset X (f X) := fun _ => Or.inl
  refine antisymm ?_ (fun _ he => he _ (fun _ hx => (fixed f inc) ▸ (show f (total f) _ from Or.inr hx)))
  rintro i ⟨X,hX,hi⟩
  have below {x} (h : Stage f x) : Subset x (extension A C S) := by
    induction h with
    | @step x _ ih =>
      rintro i (h | h)
      · exact ih h
      · exact (closure A C S) ▸ operatorMono A C (fun _ => id) ih h
    | limit _ _ ih => exact fun _ ⟨_,hx,h⟩ => ih _ hx h
  exact below hX hi

theorem omegaConsistencyStrong (a : AFml 1) (h : ∀ n, Proves NT (a.inst (numeral n))) :
    ¬Proves NT (ex (imp a bot)) := by
  intro p
  obtain ⟨n,hn⟩ := soundness p standard standardRoot closedEnv (root_loop ..) (standardModel _)
  have ha := (standard.forces_inst ..).1 (soundness (h n) standard standardRoot closedEnv (root_loop ..) (standardModel _))
  rw [eval_standard,value_numeral] at ha
  exact hn standardRoot (root_loop ..) ha

/-- Simultaneous closure under ordinary derivability and the ω-rule. -/
inductive OmegaClosure : AFml 0 → Prop where
  | ax : NT a → OmegaClosure a
  | consequence (Γ : Theory ArithmeticLanguage 0) : (∀ b, Γ b → OmegaClosure b) → Proves Γ a → OmegaClosure a
  | omega (a : AFml 1) : (∀ n, OmegaClosure (a.inst (numeral n))) → OmegaClosure (all a)

theorem omegaClosureSound {a} (p : OmegaClosure a) : standard.Forces standardRoot closedEnv a := by
  induction p with
  | ax h => exact standardModel _ _ h
  | consequence _ _ p ih => exact soundness p _ _ _ (root_loop ..) ih
  | omega a _ ih =>
    intro n
    have h := (standard.forces_inst ..).1 (ih n)
    rwa [eval_standard,value_numeral] at h

theorem omegaRuleNontrivial : ¬OmegaClosure bot := omegaClosureSound

theorem tjkOmegaConsistency (a : AFml 1) :
    ((∀ n, TJK ArithmeticLanguage true NT (a.inst (numeral n))) →
      ¬TJK ArithmeticLanguage true (insert (all a) NT) bot) ∧
    (TJK ArithmeticLanguage true NT (ex a) →
      ∃ n, ¬TJK ArithmeticLanguage true (insert (a.inst (numeral n)) NT) bot) :=
  ⟨fun h p => omegaConsistency_all a (fun n => (h n).toRoot) p.toRoot,
    fun h => (omegaConsistency_ex a h.toRoot).imp (fun _ hn p => hn p.toRoot)⟩

theorem tjkNontrivial : ¬TJK ArithmeticLanguage true NT bot := fun p => nonTriviality p.toRoot
end Truth
end BQL
