import Std

namespace BQL.Encoding
/-- Disjoint odd/even ranges distinguish the zero and successor cases. -/
def pair : Nat → Nat → Nat
  | 0,b => 2*b+1
  | a+1,b => 2*(pair a b)+2

@[simp] theorem pair_eq {a b c d : Nat} : pair a b = pair c d ↔ a = c ∧ b = d := by
  refine ⟨fun h => ?_,fun ⟨e,e'⟩ => e ▸ e' ▸ rfl⟩
  induction a generalizing c with
  | zero => cases c <;> simp only [pair] at h <;> omega
  | succ a ih =>
    cases c with
    | zero => simp only [pair] at h; omega
    | succ c =>
      simp only [pair] at h
      obtain ⟨rfl,rfl⟩ := ih (c := c) (by omega)
      exact ⟨rfl,rfl⟩

def tuple : {n : Nat} → (Fin n → Nat) → Nat
  | 0, _ => 0
  | _+1, xs => pair (xs 0) (tuple (fun i => xs i.succ))

theorem tuple_inj {xs ys : Fin n → Nat} (h : tuple xs = tuple ys) : ∀ i, xs i = ys i := by
  induction n with
  | zero => exact fun j => j.elim0
  | succ n ih =>
    obtain ⟨eq,rest⟩ := pair_eq.mp h
    exact Fin.cases eq (ih rest)

end BQL.Encoding
