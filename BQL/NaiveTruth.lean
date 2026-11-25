import BQL.Arithmetic

namespace BQL.Truth
open Formula

abbrev ATerm := Term ArithmeticLanguage
abbrev AFml := Formula ArithmeticLanguage

def equal (t s : ATerm n) : AFml n := atom .eq (extend (fun _ => s) t)
def truthOf (t : ATerm n) : AFml n := atom .truth (fun _ => t)
def iffF (a b : AFml n) := conj (imp a b) (imp b a)

def close : {n : Nat} → AFml n → AFml 0
  | 0,a => a
  | _+1,a => close (all a)

def andTuple : {k : Nat} → (Fin k → AFml n) → AFml n
  | 0,_ => top
  | _+1,xs => conj (xs 0) (andTuple (fun i => xs i.succ))

def inductionAxiom (a : AFml (n+1)) : AFml n :=
  let next := a.subst (extend (fun i => .var i.succ) (successor (.var 0)))
  imp (all (imp a next)) (imp (a.inst zeroTerm) (all a))

/-- Defining equations for projection, composition and the two recursion cases. -/
inductive Equation : {n : Nat} → ATerm n → ATerm n → Prop where
  | proj (i : Fin n) : Equation (.app (.proj i) Term.var) (.var i)
  | comp (f : PR k) (g : Fin k → PR n) :
      Equation (.app (.comp f g) Term.var) (.app f (fun i => .app (g i) Term.var))
  | base (b : PR n) (s : PR (n+2)) :
      Equation (.app (.recu b s) (extend Term.var zeroTerm)) (.app b Term.var)
  | step (b : PR n) (s : PR (n+2)) :
      Equation (.app (.recu b s) (extend (fun i => .var i.succ) (successor (.var 0))))
        (.app s (extend Term.var (.app (.recu b s) Term.var)))

def functionCongruence (f : PR k) : AFml (k+k) :=
      let x := fun i : Fin k => Term.var (L := ArithmeticLanguage) (i.castAdd k)
      let y := fun i : Fin k => Term.var (L := ArithmeticLanguage) (i.natAdd k)
      imp (andTuple (fun i => equal (x i) (y i))) (equal (.app f x) (.app f y))

/-- A1–A6, function congruence, primitive recursive definitions, curried
induction, and every sentence instance of the Tarski biconditional. -/
inductive Schema : {n : Nat} → AFml n → Prop where
  | refl : @Schema 1 (equal (.var 0) (.var 0))
  | symm : @Schema 2 (imp (equal (.var 0) (.var 1)) (equal (.var 1) (.var 0)))
  | trans : @Schema 3 (imp (conj (equal (.var 0) (.var 1)) (equal (.var 1) (.var 2)))
      (equal (.var 0) (.var 2)))
  | congr (f : PR k) : Schema (functionCongruence f)
  | truthCongr : @Schema 2 (imp (conj (equal (.var 0) (.var 1)) (truthOf (.var 0))) (truthOf (.var 1)))
  | succNeZero : @Schema 1 (imp (equal (successor (.var 0)) zeroTerm) bot)
  | succInj : @Schema 2 (imp (equal (successor (.var 0)) (successor (.var 1))) (equal (.var 0) (.var 1)))
  | defining : Equation t s → Schema (equal t s)
  | inductionRule (a : AFml (n+1)) : Schema (inductionAxiom a)
  | tarski (a : AFml 0) : Schema (iffF (truthOf (numeral (coding.code a))) a)

inductive NT : Theory ArithmeticLanguage 0 where
  | ax (a : AFml n) : Schema a → NT (close a)

abbrev standard := model arithmetic coding
abbrev standardRoot := root arithmetic coding

theorem forces_equal (w : standard.W) (ρ : Fin n → Nat) (t s : ATerm n) :
    standard.Forces w ρ (equal t s) ↔ termVal arithmetic ρ t = termVal arithmetic ρ s := by
  change standard.eval ρ t = standard.eval ρ s ↔ _
  rw [eval_standard,eval_standard]

private theorem all_andTuple (w : standard.W) (ρ : Fin n → Nat) (xs : Fin k → AFml n)
    (h : standard.Forces w ρ (andTuple xs)) : ∀ i, standard.Forces w ρ (xs i) := by
  induction k with
  | zero => exact fun i => i.elim0
  | succ k ih => exact Fin.cases h.1 (ih _ h.2)

theorem equation_standard {t s : ATerm n} (h : Equation t s) (ρ : Fin n → Nat) :
    termVal arithmetic ρ t = termVal arithmetic ρ s := by
  cases h with
  | proj | comp | base => rfl
  | step b s =>
    apply congrArg (PR.run s)
    funext j
    refine Fin.cases rfl (fun i => ?_) j
    exact Fin.cases rfl (fun _ => rfl) i

theorem schema_standard {a : AFml n} (ha : Schema a) (w : standard.W) (ρ : Fin n → Nat) :
    standard.Forces w ρ a := by
  cases ha with
  | refl => rfl
  | symm => exact fun _ _ h => Eq.symm h
  | trans => exact fun _ _ h => Eq.trans h.1 h.2
  | congr f =>
    intro z _ h
    apply (forces_equal ..).2
    apply congrArg (PR.run f)
    exact funext (fun i => (forces_equal ..).1 (all_andTuple z ρ _ h i))
  | truthCongr =>
    intro z _ h
    change extension _ _ _ (ρ 1)
    exact (show ρ 0 = ρ 1 from h.1) ▸ h.2
  | succNeZero => exact fun _ _ h => Nat.noConfusion h
  | succInj => exact fun _ _ h => Nat.succ.inj h
  | defining h => exact (forces_equal ..).2 (equation_standard h ρ)
  | inductionRule a =>
    intro u _ step z uz hz d
    have h0 := (standard.forces_inst ..).1 hz
    induction d with
    | zero => exact h0
    | succ d ih =>
      have h := (standard.forces_subst ..).1 (step d z uz ih)
      exact (show (fun i => standard.eval (extend ρ d)
          (extend (fun j => Term.var j.succ) (successor (.var 0)) i)) = extend ρ (d+1) from
          funext (fun i => Fin.cases rfl (fun _ => rfl) i)) ▸ h
  | tarski a =>
    have e : ρ = closedEnv := funext (fun i => i.elim0)
    subst ρ
    have eq (u : standard.W) : standard.Forces u closedEnv (truthOf (numeral (coding.code a))) ↔
        standard.Forces u closedEnv a := by
      change extension _ _ _ (standard.eval _ _) ↔ _
      rw [eval_standard,value_numeral]
      exact transparency ..
    exact ⟨fun u _ => (eq u).1,fun u _ => (eq u).2⟩

private theorem close_standard (w : standard.W) (a : AFml n) (ha : ∀ ρ, standard.Forces w ρ a) :
    standard.Forces w closedEnv (close a) := by
  induction n with
  | zero => exact ha _
  | succ n ih => exact ih (all a) (fun ρ d => ha (extend ρ d))

theorem standardModel (w : standard.W) : standard.Satisfies w closedEnv NT := by
  intro a ha
  cases ha with
  | ax a h => exact close_standard w a (schema_standard h w)

theorem nonTriviality : ¬Proves NT bot := fun p =>
  soundness p standard standardRoot closedEnv (root_loop ..) (standardModel _)

private theorem consistent_extension {a : AFml 0} (ha : standard.Forces standardRoot closedEnv a) :
    ¬ Proves (insert a NT) bot :=
  fun p => soundness p standard standardRoot closedEnv (root_loop ..) (standard.sat_insert ha (standardModel _))

theorem omegaConsistency_all (a : AFml 1) (h : ∀ n, Proves NT (a.inst (numeral n))) :
    ¬ Proves (insert (all a) NT) bot := by
  apply consistent_extension
  intro n
  have hh := (standard.forces_inst ..).1 (soundness (h n) standard standardRoot closedEnv (root_loop ..) (standardModel _))
  rwa [eval_standard,value_numeral] at hh

theorem omegaConsistency_ex (a : AFml 1) (h : Proves NT (ex a)) :
    ∃ n, ¬ Proves (insert (a.inst (numeral n)) NT) bot := by
  obtain ⟨n,hn⟩ := soundness h standard standardRoot closedEnv (root_loop ..) (standardModel _)
  refine ⟨n,consistent_extension ((standard.forces_inst ..).2 ?_)⟩
  rwa [eval_standard,value_numeral]

end BQL.Truth
