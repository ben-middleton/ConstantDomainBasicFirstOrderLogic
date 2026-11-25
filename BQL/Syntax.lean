import Std

/-! First-order syntax. Constants are nullary function symbols. A formula at depth `V` has free variables in `Fin V`. Index zero names the newest binder. -/
namespace BQL

structure Language where
  Func : Nat → Type
  Rel : Nat → Type

inductive Term (L : Language) (V : Nat) where
  | var (x : Fin V)
  | app {n : Nat} (f : L.Func n) (args : Fin n → Term L V)

inductive Formula (L : Language) : Nat → Type where
  | top : Formula L V
  | bot : Formula L V
  | atom {n : Nat} (r : L.Rel n) (args : Fin n → Term L V) : Formula L V
  | conj (a b : Formula L V) : Formula L V
  | disj (a b : Formula L V) : Formula L V
  | imp (a b : Formula L V) : Formula L V
  | all (a : Formula L (V+1)) : Formula L V
  | ex (a : Formula L (V+1)) : Formula L V

abbrev Sentence (L : Language) := Formula L 0
abbrev Theory (L : Language) (V : Nat) := Formula L V → Prop

variable {L : Language} {V U : Nat} {D : Type}

def extend (ρ : Fin V → D) (d : D) : Fin (V+1) → D := Fin.cases d ρ

def Term.bind (s : Fin V → Term L U) : Term L V → Term L U
  | .var x => s x
  | .app f ts => .app f (fun i => (ts i).bind s)

def Term.lift (t : Term L V) : Term L (V+1) :=
  t.bind (fun x => .var x.succ)

def up (s : Fin V → Term L U) : Fin (V+1) → Term L (U+1) :=
  extend (fun x => (s x).lift) (.var 0)

def Formula.subst : {V U : Nat} → (Fin V → Term L U) → Formula L V → Formula L U
  | _, _, _, .top => .top
  | _, _, _, .bot => .bot
  | _, _, s, .atom r ts => .atom r (fun i => (ts i).bind s)
  | _, _, s, .conj a b => .conj (a.subst s) (b.subst s)
  | _, _, s, .disj a b => .disj (a.subst s) (b.subst s)
  | _, _, s, .imp a b => .imp (a.subst s) (b.subst s)
  | _, _, s, .all a => .all (a.subst (up s))
  | _, _, s, .ex a => .ex (a.subst (up s))

def Formula.lift (a : Formula L V) := a.subst (fun x => .var x.succ)

def Formula.inst (a : Formula L (V+1)) (t : Term L V) :=
  a.subst (extend Term.var t)

def Formula.box (a : Formula L V) := imp top a

def Formula.boxes (a : Formula L V) : Nat → Formula L V
  | 0 => a
  | n+1 => (a.boxes n).box

def insert (a : Formula L V) (Γ : Theory L V) : Theory L V :=
  fun b => b = a ∨ Γ b

def lifted (Γ : Theory L V) : Theory L (V+1) :=
  fun b => ∃ a, Γ a ∧ a.lift = b

def empty : Theory L V := fun _ => False

end BQL
