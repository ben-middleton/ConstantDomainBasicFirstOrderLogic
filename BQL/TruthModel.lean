import BQL.Iteration
import BQL.Deduction
import BQL.Properties

/-! The appendix's two fixed points. The local least fixed point is the
intersection of all pre-fixed points. A global stage is a set of earlier
world valuations. The final stage contains its own valuation, giving the
reflexive root. -/
namespace BQL.Truth
open Formula Iteration

inductive Predicate : Nat → Type where
  | eq : Predicate 2
  | truth : Predicate 1

def language (F : Nat → Type) : Language := ⟨F,Predicate⟩

structure Arithmetic where
  Func : Nat → Type
  interpret : ∀ {n}, Func n → (Fin n → Nat) → Nat

abbrev Lang (A : Arithmetic) := language A.Func

variable (A : Arithmetic)

def termVal (ρ : Fin n → Nat) : Term (Lang A) n → Nat
  | .var x => ρ x
  | .app f ts => A.interpret f (fun j => termVal ρ (ts j))

structure Coding (A : Arithmetic) where
  code : Sentence (Lang A) → Nat
  injective : ∀ {a b}, code a = code b → a = b

structure Instance (A : Arithmetic) where
  {arity : Nat}
  formula : Formula (Lang A) arity
  env : Fin arity → Nat

abbrev Valuation := Instance A → Prop
abbrev Predecessors := Valuation A → Prop

def localTruth (S : Predecessors A) (X : Nat → Prop) :
    {n : Nat} → (Fin n → Nat) → Formula (Lang A) n → Prop
  | _, _, .top => True
  | _, _, .bot => False
  | _, ρ, .atom .eq ts => termVal A ρ (ts 0) = termVal A ρ (ts 1)
  | _, ρ, .atom .truth ts => X (termVal A ρ (ts 0))
  | _, ρ, .conj a b => localTruth S X ρ a ∧ localTruth S X ρ b
  | _, ρ, .disj a b => localTruth S X ρ a ∨ localTruth S X ρ b
  | _, ρ, .imp a b => ∀ v, S v → v ⟨a,ρ⟩ → v ⟨b,ρ⟩
  | _, ρ, .all a => ∀ d, localTruth S X (extend ρ d) a
  | _, ρ, .ex a => ∃ d, localTruth S X (extend ρ d) a

theorem localMono {S T : Predecessors A} {X Y : Nat → Prop}
    (ts : Subset T S) (xy : Subset X Y) (ρ : Fin n → Nat) (a : Formula (Lang A) n) :
    localTruth A S X ρ a → localTruth A T Y ρ a := by
  induction a with
  | top | bot => exact id
  | atom r => cases r with | eq => exact id | truth => exact fun h => xy h
  | conj _ _ ih ik => exact fun h => ⟨ih ρ h.1,ik ρ h.2⟩
  | disj _ _ ih ik => exact Or.imp (ih ρ) (ik ρ)
  | imp => exact fun h v hv => h v (ts hv)
  | all _ ih => exact fun h d => ih _ (h d)
  | ex _ ih => exact fun ⟨d,h⟩ => ⟨d,ih _ h⟩

variable (C : Coding A)

def operator (S : Predecessors A) (X : Nat → Prop) : Nat → Prop := fun n =>
  ∃ a, C.code a = n ∧ localTruth A S X closedEnv a

def extension (S : Predecessors A) : Nat → Prop :=
  fun n => ∀ X, Subset (operator A C S X) X → X n

theorem operatorMono {S T : Predecessors A} {X Y : Nat → Prop} (ts : Subset T S) (xy : Subset X Y) :
    Subset (operator A C S X) (operator A C T Y) :=
  fun _ ⟨a,e,h⟩ => ⟨a,e,localMono A ts xy _ a h⟩

theorem closure (S : Predecessors A) : operator A C S (extension A C S) = extension A C S := by
  let Φ := operator A C S
  let E := extension A C S
  have pre : Subset (Φ E) E := fun _ h X hx => hx
    (operatorMono A C (fun _ => id) (fun _ he => he X hx) h)
  exact antisymm pre (fun _ he => he (Φ E) (operatorMono A C (fun _ => id) pre))

theorem decreasing {S T : Predecessors A} (st : Subset S T) :
    Subset (extension A C T) (extension A C S) :=
  fun _ h X pre => h X (fun _ hx => pre (operatorMono A C st (fun _ => id) hx))

def point (S : Predecessors A) : Valuation A :=
  fun i => localTruth A S (extension A C S) i.env i.formula

def next (S : Predecessors A) : Predecessors A := fun v => S v ∨ v = point A C S

abbrev World := {S // Stage (next A C) S}

theorem origin {S : Predecessors A} (hs : Stage (next A C) S) {v} (hv : S v) :
    ∃ U : World A C, Subset U.val S ∧ point A C U.val = v := by
  induction hs with
  | step hu ih =>
    rcases hv with h | rfl
    · obtain ⟨u,us,rfl⟩ := ih h
      exact ⟨u,fun _ h => Or.inl (us h),rfl⟩
    · exact ⟨⟨_,hu⟩,fun _ => Or.inl,rfl⟩
  | limit s _ ih =>
    obtain ⟨t,ht,hv⟩ := hv
    obtain ⟨u,ut,rfl⟩ := ih t ht hv
    exact ⟨u,fun _ h => ⟨t,ht,ut h⟩,rfl⟩

def root : World A C := ⟨total (next A C),stage_total _⟩

def model : Model (Lang A) where
  W := World A C
  D := Nat
  worlds := ⟨root A C⟩
  domain := ⟨0⟩
  acc S U := Subset U.val S.val ∧ S.val (point A C U.val)
  trans h k := ⟨fun _ hx => h.1 (k.1 hx),h.1 k.2⟩
  func := A.interpret
  rel := fun {k} r w ts => match k, r, ts with
    | _, .eq, ts => ts 0 = ts 1
    | _, .truth, ts => extension A C w.val (ts 0)
  persist := by
    intro k r w u ts e
    cases r with
    | eq => exact id
    | truth => exact fun h => decreasing A C e.1 h

theorem root_loop : (model A C).acc (root A C) (root A C) := by
  refine ⟨fun _ => id,?_⟩
  have h : next A C (total (next A C)) (point A C (total (next A C))) := Or.inr rfl
  rwa [fixed (next A C) (fun _ _ => Or.inl)] at h

theorem reflexive_iff_root (w : World A C) : (model A C).acc w w ↔ w = root A C := by
  refine ⟨fun e => ?_,fun eq => eq ▸ root_loop A C⟩
  apply Subtype.ext
  exact fixedStage (next A C) (fun _ _ => Or.inl) w.property
    (antisymm (fun _ h => h.elim id (fun eq => eq ▸ e.2)) (fun _ => Or.inl))

theorem linearStages (u v : World A C) : u = v ∨ (model A C).acc u v ∨ (model A C).acc v u := by
  classical
  let f := next A C
  have inc s : Subset s (f s) := fun _ => Or.inl
  by_cases uv : Subset u.val v.val
  · by_cases vu : Subset v.val u.val
    · exact Or.inl (Subtype.ext (antisymm uv vu))
    · exact Or.inr (Or.inr ⟨uv,successor_below f inc u.property v.property vu (Or.inr rfl)⟩)
  · have sub := successor_below f inc v.property u.property uv
    exact Or.inr (Or.inl ⟨fun _ h => sub (Or.inl h), sub (Or.inr rfl)⟩)

theorem eval_standard (t : Term (Lang A) n) (ρ : Fin n → Nat) :
    (model A C).eval ρ t = termVal A ρ t := by
  induction t with
  | var => rfl
  | app f _ ih => exact congrArg (A.interpret f) (funext ih)

theorem truth (a : Formula (Lang A) n) (w : World A C) (ρ : Fin n → Nat) :
    (model A C).Forces w ρ a ↔ point A C w.val ⟨a,ρ⟩ := by
  induction a generalizing w with
  | top | bot => rfl
  | atom r ts =>
    cases r with
    | eq => change (_ = _) ↔ (_ = _); simp only [eval_standard]
    | truth => change extension A C _ _ ↔ extension A C _ _; simp only [eval_standard]
  | conj _ _ ih ik => exact and_congr (ih ..) (ik ..)
  | disj _ _ ih ik => exact or_congr (ih ..) (ik ..)
  | all _ ih => exact forall_congr' (fun _ => ih ..)
  | ex _ ih => exact exists_congr (fun _ => ih ..)
  | imp a b ih ik =>
    constructor
    · intro h v hv hA
      obtain ⟨u,sub,rfl⟩ := origin A C w.property hv
      exact (ik u ρ).1 (h u ⟨sub,hv⟩ ((ih u ρ).2 hA))
    · intro h u e ha
      exact (ik u ρ).2 (h _ e.2 ((ih u ρ).1 ha))

theorem transparency (w : World A C) (a : Sentence (Lang A)) :
    extension A C w.val (C.code a) ↔ (model A C).Forces w closedEnv a := by
  rw [truth, ← closure A C w.val]
  constructor
  · rintro ⟨b,e,h⟩
    exact C.injective e ▸ h
  · exact fun h => ⟨a,rfl,h⟩

end BQL.Truth
