import BQL.Saturation
import BQL.Compactness

namespace BQL
open Formula
namespace Canonical
variable {L : Language}
def single (a : Formula L n) : Theory L n := fun b => a = b

structure Point (L : Language) where
  mem : Sentence L → Prop
  top : mem top
  bot : ¬mem bot
  closed : ∀ {a b}, Basic (single a) b → mem a → mem b
  meet : ∀ {a b}, mem a → mem b → mem (conj a b)
  split : ∀ {a b}, mem (disj a b) → mem a ∨ mem b
  total : ∀ {a}, (∀ t, mem (a.inst t)) → mem (all a)
  witness : ∀ {a}, mem (ex a) → ∃ t, mem (a.inst t)

theorem impOfBasic {a b : Formula L n} (h : Basic (single a) b) : Basic empty (imp a b) :=
  .impI (h.cutBasic rfl (fun _ e => e ▸ Derivation.here) (fun _ h => h.elim))

def Prime.toPoint {O : Order L} (W : Prime O) (extend : ∀ {a b}, Basic (single a) b → O.le a b) : Point L :=
  ⟨W.mem,W.top,W.bot,fun h => W.up (extend h),W.meet,W.split,W.total,W.witness⟩

variable (W : Point L)
private theorem fact {a : F L} (p : Basic empty a) : W.mem a :=
  W.closed (p.weaken (fun _ h => h.elim) (fun _ => id)) W.top

private theorem unary {a b : F L} (p : Basic (single a) b) : W.mem a → W.mem b := W.closed p

private theorem binary {a b c : F L} (p : Basic (single (conj a b)) c) (ha : W.mem a) (hb : W.mem b) : W.mem c :=
  W.closed p (W.meet ha hb)

private theorem given {a : Formula L n} : Derivation L k (single a) Δ a := .global rfl

theorem lift_inst (a : Formula L n) (t : Term L n) : a.lift.inst t = a := by
  rw [lift,inst,subst_comp]
  exact a.subst_var

def relative : Order L where
  le a b := W.mem (imp a b)
  refl := fact W Derivation.identity
  trans := binary W (.trans (.andL given) (.andR given))
  top := fact W (Derivation.constant .topI)
  bot := fact W (.impI (.botE Derivation.here))
  left := fact W (.impI (.andL Derivation.here))
  right := fact W (.impI (.andR Derivation.here))
  meet := binary W (.meet (.andL given) (.andR given))
  inl := fact W (.impI (.orL Derivation.here))
  inr := fact W (.impI (.orR Derivation.here))
  join := binary W (.join (.andL given) (.andR given))
  dist := fact W Derivation.distribution
  allE t := fact W (.impI (.allE t Derivation.here))
  exI t := fact W (.impI (.exI t Derivation.here))
  allWitness := by
    intro x y a h
    apply unary W (a := all (imp x.lift (disj y.lift a)))
      (.trans (.internalAll given) (.impI (.cd Derivation.here)))
    apply W.total
    intro t
    change W.mem (imp (x.lift.inst t) (disj (y.lift.inst t) (a.inst t)))
    simpa only [lift_inst] using h t
  exWitness := by
    intro x y a h
    apply unary W (a := all (imp (conj x.lift a) y.lift))
      (.trans Derivation.infiniteDistribution (.internalEx given))
    apply W.total
    intro t
    change W.mem (imp (conj (x.lift.inst t) (a.inst t)) (y.lift.inst t))
    simpa only [lift_inst] using h t

def Access (W U : Point L) := ∀ ⦃a b⦄, W.mem (imp a b) → U.mem a → U.mem b

theorem persistMem {W U : Point L} (e : Access W U) {a} (ha : W.mem a) : U.mem a :=
  e (W.closed (Derivation.constant given) ha) U.top

theorem relativeExtension (enum : Nat → F L) (covers : ∀ a, ∃ i, enum i = a) {a b} (h : ¬W.mem (imp a b)) :
    ∃ U : Point L, Access W U ∧ U.mem a ∧ ¬ U.mem b := by
  let s : Pair (relative W) := ⟨a,b,h⟩
  obtain ⟨u,ha,hb⟩ := s.extend enum covers
  exact ⟨u.toPoint (fun p => fact W (impOfBasic p)),fun _ _ h => u.up h,ha,hb⟩

def model (point : Nonempty (Point L)) (term : Nonempty (Term L 0)) : Model L where
  W := Point L
  D := Term L 0
  worlds := point
  domain := term
  acc := Access
  trans e d := fun _ _ h => d (persistMem e h)
  func := Term.app
  rel r w ts := w.mem (atom r ts)
  persist := fun e => persistMem e

theorem evalTerm (pt : Nonempty (Point L)) (ht : Nonempty (Term L 0)) (ρ : Fin n → Term L 0) (t : Term L n) :
    (model pt ht).eval ρ t = t.bind ρ := by
  induction t with
  | var => rfl
  | app f _ ih => exact congrArg (Term.app f) (funext ih)

theorem inst_closed (ρ : Fin n → Term L 0) (t : Term L 0) (a : Formula L (n+1)) :
    (a.subst (up ρ)).inst t = a.subst (extend ρ t) := by
  rw [inst,subst_comp]
  apply congrArg (fun s => a.subst s)
  funext j
  refine Fin.cases rfl (fun i => ?_) j
  change ((ρ i).bind _).bind _ = ρ i
  rw [Term.bind_comp]
  exact (ρ i).bind_var

theorem truthLemma (enum : Nat → F L) (covers : ∀ a, ∃ i, enum i = a)
    (pt : Nonempty (Point L)) (ht : Nonempty (Term L 0)) (w : Point L) (ρ : Fin n → Term L 0) (a : Formula L n) :
    (model pt ht).Forces w ρ a ↔ w.mem (a.subst ρ) := by
  induction a generalizing w with
  | top => exact ⟨fun _ => w.top, fun _ => trivial⟩
  | bot => exact ⟨False.elim, w.bot⟩
  | atom r ts =>
    change w.mem (atom r _) ↔ w.mem (atom r _)
    simp only [evalTerm]
  | conj a b ih ik =>
    exact ⟨fun h => w.meet ((ih ..).1 h.1) ((ik ..).1 h.2),
      fun h => ⟨(ih ..).2 (w.closed (.andL given) h),(ik ..).2 (w.closed (.andR given) h)⟩⟩
  | disj a b ih ik =>
    exact ⟨fun h => h.elim (fun ha => w.closed (.orL given) ((ih ..).1 ha))
      (fun hb => w.closed (.orR given) ((ik ..).1 hb)),fun h => (w.split h).imp (ih ..).2 (ik ..).2⟩
  | imp a b ih ik =>
    refine ⟨fun h => Classical.byContradiction (fun hn => ?_),fun h u e ha => (ik ..).2 (e h ((ih ..).1 ha))⟩
    obtain ⟨u,e,ha,hb⟩ := relativeExtension w enum covers hn
    exact hb ((ik ..).1 (h u e ((ih ..).2 ha)))
  | all a ih =>
    refine ⟨fun h => w.total (fun t => ?_), fun h t => (ih ..).2 ?_⟩
    · rw [inst_closed]; exact (ih ..).1 (h t)
    · rw [← inst_closed]; exact w.closed (.allE t given) h
  | ex a ih =>
    constructor
    · rintro ⟨t,h⟩
      apply w.closed (.exI t given)
      rw [inst_closed]; exact (ih ..).1 h
    · intro h
      obtain ⟨t,ht⟩ := w.witness h
      rw [inst_closed] at ht
      exact ⟨t,(ih ..).2 ht⟩

end Canonical
end BQL
