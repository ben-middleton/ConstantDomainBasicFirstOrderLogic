import BQL.Parameters

namespace BQL
open Formula

namespace Model
variable {L : Language} (M : Model L)

/-- Adjoin a reflexive world below the entire frame. -/
def under : Model L where
  W := Option M.W
  D := M.D
  worlds := ⟨none⟩
  domain := M.domain
  acc w z := match w,z with
    | none,_ => True
    | some _,none => False
    | some u,some v => M.acc u v
  trans := by
    intro w z u
    cases w <;> cases z <;> cases u <;> first | exact fun _ _ => trivial | exact False.elim | exact fun _ => False.elim | exact M.trans
  func := M.func
  rel r w ts := match w with
    | none => False
    | some w => M.rel r w ts
  persist := by
    intro k r w z ts e h
    cases w <;> cases z <;> first | exact h.elim | exact e.elim | exact M.persist e h

theorem under_eval (t : Term L n) (ρ : Fin n → M.D) : M.under.eval ρ t = M.eval ρ t := by
  induction t with
  | var => rfl
  | app f _ ih => exact congrArg (M.func f) (funext ih)

theorem under_forces (w : M.W) (ρ : Fin n → M.D) (a : Formula L n) :
    M.under.Forces (some w) ρ a ↔ M.Forces w ρ a := by
  induction a generalizing w with
  | top | bot => rfl
  | atom => simp only [Forces,under_eval]; rfl
  | conj _ _ ih ik => exact and_congr (ih ..) (ik ..)
  | disj _ _ ih ik => exact or_congr (ih ..) (ik ..)
  | all _ ih => exact forall_congr' (fun _ => ih ..)
  | ex _ ih => exact exists_congr (fun _ => ih ..)
  | imp _ _ ih ik =>
    constructor
    · exact fun h z e ha => (ik ..).1 (h (some z) e ((ih ..).2 ha))
    · intro h z e ha
      cases z with
      | none => exact e.elim
      | some z => exact (ik ..).2 (h z e ((ih ..).1 ha))

end Model

def ValidEverywhere (a : Formula L n) := ∀ (M : Model L) w ρ, M.Forces w ρ a

theorem rootValidity {a : Formula L n} : Entails empty a ↔ ValidEverywhere a :=
  ⟨fun h M w ρ => (M.under_forces w ρ a).1
    (M.under.persistence (w := none) (u := some w) trivial ρ a (h M.under none ρ trivial (fun _ h => h.elim))),
    fun h M w ρ _ _ => h M w ρ⟩

namespace Canonical
variable {L : Language}
private abbrev B (x y : Sentence L) := Basic (single x) y
private theorem given {a : Formula L n} : Derivation L k (single a) Δ a := .global rfl
private theorem cutOne {a b : Formula L n} (p : Basic (single a) b) (ha : Derivation L k Γ Δ a) :
    Derivation L k Γ Δ b := p.cutBasic rfl (fun _ e => e ▸ ha) (fun _ h => h.elim)
private theorem basicAll (fresh : Fresh L) {x y : F L} {a : Formula L 1}
    (h : ∀ t, B x (disj y (a.inst t))) : B x (disj y (all a)) := by
  obtain ⟨c,hc⟩ := fresh (x.symbols ++ y.symbols ++ a.symbols)
  simp only [List.mem_append,not_or] at hc
  apply Derivation.cd
  apply Derivation.allI
  have hh := Translation.tree (h (constTerm c)) (Translation.openConst c)
    (G := lifted (single x)) (D := lifted empty)
    (fun _ e => e ▸ ⟨x,rfl,(Translation.open_independent hc.1.1).symm⟩) (fun _ h => h.elim)
  simpa only [Translation.form,Translation.open_instance hc.2,Translation.open_independent hc.1.2] using hh

private theorem basicEx (fresh : Fresh L) {x y : F L} {a : Formula L 1}
    (h : ∀ t, B (conj x (a.inst t)) y) : B (conj x (ex a)) y := by
  obtain ⟨c,hc⟩ := fresh (x.symbols ++ y.symbols ++ a.symbols)
  simp only [List.mem_append,not_or] at hc
  apply Derivation.exE (Derivation.andR given)
  let T := Translation.openConst (n := 0) c
  have eq : T.form (conj x (a.inst (constTerm c))) = conj x.lift a := by
    simp only [T,Translation.form,Translation.open_independent hc.1.1,Translation.open_instance hc.2]
  have hh := Translation.tree (h (constTerm c)) T (G := single (conj x.lift a)) (D := empty)
    (fun _ e => e ▸ eq.symm) (fun _ h => h.elim)
  rw [show T.form y = y.lift from Translation.open_independent hc.1.2] at hh
  exact cutOne hh (.andI (.andL (.global ⟨_,rfl,rfl⟩)) Derivation.here)

def basicOrder (fresh : Fresh L) : Order L where
  le := B
  refl := given
  trans h v := cutOne v h
  top := .topI
  bot := .botE given
  left := .andL given
  right := .andR given
  meet := .andI
  inl := .orL given
  inr := .orR given
  join h v := .orE given (cutOne h Derivation.here) (cutOne v Derivation.here)
  dist := .orE (.andR given) (.orL (.andI (.andL given) Derivation.here))
    (.orR (.andI (.andL given) Derivation.here))
  allE t := .allE t given
  exI t := .exI t given
  allWitness := basicAll fresh
  exWitness := basicEx fresh

theorem basicValid (H : HenkinLanguage L) {a : F L} (h : ValidEverywhere a) : Basic empty a := by
  apply Classical.byContradiction
  intro hn
  let s : Pair (basicOrder H.fresh) := ⟨top,a,fun h => hn (cutOne h .topI)⟩
  obtain ⟨p,_,ha⟩ := s.extend H.enum H.covers
  let w := p.toPoint (fun h => h)
  obtain ⟨c,_⟩ := H.fresh []
  let M := model (L := L) ⟨w⟩ ⟨constTerm c⟩
  have mem := (truthLemma H.enum H.covers _ _ w Term.var a).1 (h M w Term.var)
  change ¬w.mem a at ha
  exact ha (by simpa only [subst_var] using mem)

end Canonical

theorem sameTheorems {L : Language} (hc : Nonempty (L.Func 0)) (a : Sentence L) :
    Basic empty a ↔ Proves empty a := by
  refine ⟨fun h => h.raise trivial,fun p => ?_⟩
  obtain ⟨K,F,B,⟨H⟩,inv⟩ := Canonical.finiteRelabel L hc a.symbols
  have valid := rootValidity.mp (soundness p)
  have mapped : ValidEverywhere (F.form a) :=
    fun M w ρ => (F.forces M w ρ a).1 (valid (F.reduct M) w ρ)
  have back := B.tree (Canonical.basicValid H mapped) (G := empty) (D := empty)
    (fun _ h => h.elim) (fun _ h => h.elim)
  rwa [F.invertForm B a inv] at back

end BQL
