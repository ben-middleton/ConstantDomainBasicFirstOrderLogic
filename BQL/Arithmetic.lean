import BQL.Encoding
import BQL.TruthModel

namespace BQL.Truth

/-- Programs for the primitive recursive functions. In primitive recursion
the recursion argument is first and the step receives the previous value first. -/
inductive PR : Nat → Type where
  | zero : PR 0
  | succ : PR 1
  | proj (i : Fin n) : PR n
  | comp (f : PR k) (g : Fin k → PR n) : PR n
  | recu (base : PR n) (step : PR (n+2)) : PR (n+1)

def PR.run : {n : Nat} → PR n → (Fin n → Nat) → Nat
  | _, .zero, _ => 0
  | _, .succ, xs => (xs 0)+1
  | _, .proj i, xs => xs i
  | _, .comp f g, xs => f.run (fun i => (g i).run xs)
  | _, .recu b s, xs =>
    let ys := fun i => xs i.succ
    Nat.rec (b.run ys) (fun k r => s.run (extend (extend ys k) r)) (xs 0)

abbrev ArithmeticLanguage := language PR

def zeroTerm : Term ArithmeticLanguage n := .app .zero Fin.elim0
def successor (t : Term ArithmeticLanguage n) : Term ArithmeticLanguage n := .app .succ (fun _ => t)

def numeral : Nat → Term ArithmeticLanguage 0
  | 0 => zeroTerm
  | n+1 => successor (numeral n)

def arithmetic : Arithmetic := ⟨PR,PR.run⟩

@[simp] theorem value_zero (ρ : Fin n → Nat) : termVal arithmetic ρ zeroTerm = 0 := rfl
@[simp] theorem value_succ (ρ : Fin n → Nat) (t : Term ArithmeticLanguage n) :
    termVal arithmetic ρ (successor t) = termVal arithmetic ρ t + 1 := rfl
@[simp] theorem value_numeral (n : Nat) : termVal arithmetic closedEnv (numeral n) = n := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg Nat.succ ih

namespace Godel
open Encoding

def program : {n : Nat} → PR n → Nat
  | _, .zero => pair 0 0
  | _, .succ => pair 1 0
  | _, .proj i => pair 2 i
  | _, .comp (k := k) f g => pair 3 (pair k (pair (program f) (tuple (fun i => program (g i)))))
  | _, .recu b s => pair 4 (pair (program b) (program s))

theorem program_inj {a b : PR n} (h : program a = program b) : a = b := by
  induction a with
  | zero => cases b <;> simp_all [program]
  | succ => cases b <;> simp_all [program]
  | proj i => cases b <;> simp_all [program,Fin.ext_iff]
  | comp f g ih ik =>
    cases b <;> simp only [program,pair_eq,Nat.reduceEqDiff, false_and, and_self_left,
      true_and, reduceCtorEq] at h
    rename_i k f' g'
    obtain ⟨rfl,ef,eg⟩ := h
    rw [ih ef]
    exact congrArg _ (funext (fun j => ik j (tuple_inj eg j)))
  | recu b s ih ik =>
    cases b <;> simp [program] at h
    obtain ⟨rfl,rfl⟩ := And.intro (ih h.1) (ik h.2)
    rfl

def term : Term ArithmeticLanguage n → Nat
  | .var i => pair 0 i
  | .app (n := k) f ts => pair 1 (pair k (pair (program f) (tuple (fun i => term (ts i)))))

theorem term_inj {a b : Term ArithmeticLanguage n} (h : term a = term b) : a = b := by
  induction a generalizing b with
  | var i => cases b <;> simp_all [term,Fin.ext_iff]
  | app f ts ih =>
    cases b <;> simp only [term,pair_eq,Nat.reduceEqDiff,false_and,true_and] at h
    obtain ⟨rfl,ef,et⟩ := h
    rw [program_inj ef]
    exact congrArg _ (funext (fun j => ih j (tuple_inj et j)))

def formula : {n : Nat} → Formula ArithmeticLanguage n → Nat
  | _, .top => pair 0 0
  | _, .bot => pair 1 0
  | _, .atom .eq ts => pair 2 (tuple (fun j => term (ts j)))
  | _, .atom .truth ts => pair 3 (tuple (fun j => term (ts j)))
  | _, .conj a b => pair 4 (pair (formula a) (formula b))
  | _, .disj a b => pair 5 (pair (formula a) (formula b))
  | _, .imp a b => pair 6 (pair (formula a) (formula b))
  | _, .all a => pair 7 (formula a)
  | _, .ex a => pair 8 (formula a)

theorem formula_inj {a b : Formula ArithmeticLanguage n} (h : formula a = formula b) : a = b := by
  induction a with
  | atom r ts =>
    cases r <;> cases b <;> (try cases ‹ArithmeticLanguage.Rel _›) <;> simp [formula] at h ⊢
    all_goals exact funext (fun i => term_inj (tuple_inj h i))
  | _ =>
    cases b <;> (try cases ‹ArithmeticLanguage.Rel _›) <;> simp [formula] at h ⊢
    all_goals first | exact ⟨by apply_assumption; exact h.1, by apply_assumption; exact h.2⟩ | apply_assumption; exact h

end Godel

def coding : Coding arithmetic := ⟨Godel.formula, Godel.formula_inj⟩

end BQL.Truth
