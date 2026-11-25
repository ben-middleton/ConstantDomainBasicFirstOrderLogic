import BQL.Parameters

/-! Section 7. Equality can be a persistent world-dependent congruence or
actual identity. The latter semantics uses a quotient of the generated model
by the equivalence relation at its designated root. -/
namespace BQL.Identity
open Formula
variable {L : Language} (E : L.Rel 2)

def two (a b : D) : Fin 2 → D := Fin.cases a (fun _ => b)
theorem map_two (f : D → U) (a b : D) : (fun i => f (two a b i)) = two (f a) (f b) :=
  funext (fun i => Fin.cases rfl (fun _ => rfl) i)

def eqF (a b : Term L n) := atom E (two a b)

def EqAt (M : Model L) (w : M.W) (x y : M.D) := M.rel E w (two x y)

theorem forces_eq (M : Model L) (w : M.W) (ρ : Fin n → M.D) (a b : Term L n) :
    M.Forces w ρ (eqF E a b) ↔ EqAt E M w (M.eval ρ a) (M.eval ρ b) := by
  simp only [eqF,Model.Forces,EqAt,map_two]

def close : {n : Nat} → Formula L n → Sentence L
  | 0,a => a
  | _+1,a => close (all a)

theorem forces_close (M : Model L) (w : M.W) (η : Fin 0 → M.D) (a : Formula L n) :
    M.Forces w η (close a) ↔ ∀ ρ, M.Forces w ρ a := by
  induction n with
  | zero =>
    exact ⟨fun h ρ => (show η = ρ from funext (fun j => j.elim0)) ▸ h,fun h => h η⟩
  | succ n ih =>
    refine (ih (all a)).trans ⟨fun h ρ => ?_,fun h ρ d => h (extend ρ d)⟩
    have e : extend (fun j => ρ j.succ) (ρ 0) = ρ := funext (fun j => Fin.cases rfl (fun _ => rfl) j)
    exact e ▸ h _ (ρ 0)

def meetAll : {k : Nat} → (Fin k → Formula L n) → Formula L n
  | 0,_ => top
  | _+1,as => conj (as 0) (meetAll (fun i => as i.succ))

theorem forces_meet (M : Model L) (w : M.W) (ρ : Fin n → M.D) (as : Fin k → Formula L n) :
    M.Forces w ρ (meetAll as) ↔ ∀ i, M.Forces w ρ (as i) := by
  induction k with
  | zero => exact ⟨fun _ i => i.elim0,fun _ => trivial⟩
  | succ k ih => exact ⟨fun h => Fin.cases h.1 ((ih _).1 h.2),fun h => ⟨h 0,(ih _).2 (fun i => h i.succ)⟩⟩

def leftVar (i : Fin k) : Term L (k+k) := .var (i.castAdd k)
def rightVar (i : Fin k) : Term L (k+k) := .var (i.natAdd k)
def agree (k : Nat) : Formula L (k+k) := meetAll (fun i => eqF E (leftVar i) (rightVar i))

inductive Laws (E : L.Rel 2) (diagonal : Bool) : Theory L 0 where
  | refl : Laws E diagonal (close (n := 1) (eqF E (.var 0) (.var 0)))
  | symm : Laws E diagonal (close (n := 2) (imp (eqF E (.var 0) (.var 1)) (eqF E (.var 1) (.var 0))))
  | trans : Laws E diagonal (close (n := 3) (imp (conj (eqF E (.var 0) (.var 1)) (eqF E (.var 1) (.var 2)))
      (eqF E (.var 0) (.var 2))))
  | func (f : L.Func k) : Laws E diagonal (close (imp (agree E k) (eqF E (.app f leftVar) (.app f rightVar))))
  | rel (r : L.Rel k) : Laws E diagonal (close (imp (conj (agree E k) (atom r leftVar)) (atom r rightVar)))
  | em : diagonal = true → Laws E diagonal (close (n := 2) (disj (eqF E (.var 0) (.var 1))
      (imp (eqF E (.var 0) (.var 1)) bot)))

structure Congruent (M : Model L) (w : M.W) : Prop where
  equiv : Equivalence (EqAt E M w)
  func : ∀ {k} (f : L.Func k) (xs ys : Fin k → M.D), (∀ i, EqAt E M w (xs i) (ys i)) →
    EqAt E M w (M.func f xs) (M.func f ys)
  rel : ∀ {k} (r : L.Rel k) (xs ys : Fin k → M.D), (∀ i, EqAt E M w (xs i) (ys i)) → M.rel r w xs → M.rel r w ys

def Diagonal (M : Model L) := ∀ w x y, EqAt E M w x y ↔ x = y

theorem diagonalCongruent (M : Model L) (h : Diagonal E M) (w) : Congruent E M w where
  equiv := ⟨fun x => (h w x x).2 rfl,fun e => (h ..).2 ((h ..).1 e).symm,
    fun e e' => (h ..).2 (((h ..).1 e).trans ((h ..).1 e'))⟩
  func f _ _ he := (h ..).2 (congrArg (M.func f) (funext (fun i => (h ..).1 (he i))))
  rel _ xs ys he := (funext (fun i => (h ..).1 (he i)) : xs = ys) ▸ id

private theorem agrees (M : Model L) (w) (ρ : Fin (k+k) → M.D) :
    M.Forces w ρ (agree E k) ↔ ∀ i : Fin k, EqAt E M w (ρ (i.castAdd k)) (ρ (i.natAdd k)) :=
  (forces_meet ..).trans (forall_congr' (fun _ => forces_eq ..))

theorem laws_hold (M : Model L) (cg : ∀ w, Congruent E M w)
    (rigid : d = true → Diagonal E M) (w) (η) : M.Satisfies w η (Laws E d) := by
  intro a h
  cases h <;> apply (forces_close ..).2
  case refl => exact fun ρ => (forces_eq ..).2 ((cg w).equiv.refl _)
  case symm => exact fun ρ u _ h => (forces_eq ..).2 ((cg u).equiv.symm ((forces_eq ..).1 h))
  case trans => exact fun ρ u _ h => (forces_eq ..).2 ((cg u).equiv.trans ((forces_eq ..).1 h.1) ((forces_eq ..).1 h.2))
  case func f => exact fun ρ u _ h => (forces_eq ..).2 ((cg u).func f _ _ ((agrees ..).1 h))
  case rel r => exact fun ρ u _ h => (cg u).rel r _ _ ((agrees ..).1 h.1) h.2
  case em flag =>
    intro ρ
    by_cases e : ρ 0 = ρ 1
    · exact Or.inl ((forces_eq ..).2 ((rigid flag ..).2 e))
    · exact Or.inr (fun u _ h => e ((rigid flag ..).1 ((forces_eq ..).1 h)))

private def appendEnv (xs ys : Fin k → D) (i : Fin (k+k)) : D :=
  if h : i.val < k then xs ⟨i,h⟩ else ys ⟨i.val-k,by omega⟩

private theorem append_left (xs ys : Fin k → D) (i : Fin k) : appendEnv xs ys (i.castAdd k) = xs i := by
  simp [appendEnv,Fin.castAdd,i.isLt]
private theorem append_right (xs ys : Fin k → D) (i : Fin k) : appendEnv xs ys (i.natAdd k) = ys i := by
  simp only [appendEnv,Fin.natAdd,dif_neg (show ¬ k + i.val < k by omega)]
  exact congrArg ys (Fin.ext (show k + i.val - k = i.val by omega))

theorem laws_congruent (M : Model L) (w u : M.W) (edge : M.acc w u) {η} (h : M.Satisfies w η (Laws E d)) :
    Congruent E M u := by
  have ax {n} (a : Formula L n) (ha : Laws E d (close a)) := (forces_close M w η a).1 (h _ ha)
  refine ⟨⟨?_,?_,?_⟩,?_,?_⟩
  · intro x
    exact (forces_eq ..).1 (M.persistence edge _ _ (ax _ .refl (fun _ => x)))
  · intro x y e
    exact (forces_eq ..).1 (ax _ .symm (two x y) u edge ((forces_eq ..).2 e))
  · intro x y z e f
    exact (forces_eq ..).1 (ax _ .trans (extend (two y z) x) u edge ⟨(forces_eq ..).2 e,(forces_eq ..).2 f⟩)
  · intro k f xs ys eq
    let ρ := appendEnv xs ys
    have hh := (forces_eq ..).1 (ax _ (.func f) ρ u edge ((agrees ..).2 (by simpa only [ρ,append_left,append_right] using eq)))
    simpa only [Model.eval,leftVar,rightVar,ρ,append_left,append_right] using hh
  · intro k r xs ys eq hr
    let ρ := appendEnv xs ys
    have same := (agrees E M u ρ).2 (by simpa only [ρ,append_left,append_right] using eq)
    have hh := ax _ (.rel r) ρ u edge
    simp only [Model.Forces,Model.eval,leftVar,rightVar,ρ,append_left,append_right] at hh
    exact hh ⟨same,hr⟩

/-- The submodel generated by a reflexive root keeps each entire successor cone. -/
def generated (M : Model L) (w : M.W) (loop : M.acc w w) : Model L where
  W := {u // M.acc w u}
  D := M.D
  worlds := ⟨⟨w,loop⟩⟩
  domain := M.domain
  acc u v := M.acc u.val v.val
  trans := M.trans
  func := M.func
  rel r u := M.rel r u.val
  persist := M.persist

theorem generated_eval (M : Model L) (w loop) (ρ : Fin n → M.D) (t : Term L n) :
    (generated M w loop).eval ρ t = M.eval ρ t := by
  induction t with
  | var => rfl
  | app f _ ih => exact congrArg (M.func f) (funext ih)

theorem generated_forces (M : Model L) (w loop) (u : (generated M w loop).W) (ρ : Fin n → M.D) (a : Formula L n) :
    (generated M w loop).Forces u ρ a ↔ M.Forces u.val ρ a := by
  induction a generalizing u with
  | top | bot => rfl
  | atom => simp only [Model.Forces,generated_eval]; rfl
  | conj _ _ ih ik => exact and_congr (ih ..) (ik ..)
  | disj _ _ ih ik => exact or_congr (ih ..) (ik ..)
  | all _ ih => exact forall_congr' (fun _ => ih ..)
  | ex _ ih => exact exists_congr (fun _ => ih ..)
  | imp _ _ ih ik =>
    exact ⟨fun h z e ha => (ik ⟨z,M.trans u.property e⟩ ρ).1 (h _ e ((ih ..).2 ha)),
      fun h z e ha => (ik ..).2 (h z.val e ((ih ..).1 ha))⟩

end BQL.Identity
