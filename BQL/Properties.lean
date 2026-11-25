import BQL.Intersection

namespace BQL
open Formula

variable {L : Language}
def closedEnv {D : Type} : Fin 0 → D := Fin.elim0

structure Countermodel (Γ : Theory L 0) (a : Sentence L) where
  model : Model L
  w : model.W
  loop : model.acc w w
  premises : model.Satisfies w closedEnv Γ
  fails : ¬model.Forces w closedEnv a

theorem countermodel {Γ : Theory L 0} {a : Sentence L} (h : ¬Entails Γ a) :
    Nonempty (Countermodel Γ a) := by
  apply Classical.byContradiction
  intro hc
  apply h
  intro M w ρ r g
  have he : ρ = closedEnv := funext (fun j => j.elim0)
  subst ρ
  exact Classical.byContradiction (fun hn => hc ⟨⟨M,w,r,g,hn⟩⟩)

private theorem env_unique {D : Type} (ρ : Fin 0 → D) : ρ = closedEnv := funext (fun j => j.elim0)

namespace Family
theorem root_premises {Γ : Theory L 0} {I} [Nonempty I] (F : Family L I)
    (fragment : ∀ a, Γ a → NegativeFragment a)
    (models : ∀ i, (F.model i).Satisfies (F.root i) closedEnv Γ) :
    F.glue.Satisfies none closedEnv Γ := by
  intro a ha
  apply (F.root_iff _ (fragment a ha)).2
  intro i
  rw [env_unique (F.proj i ∘ closedEnv)]
  exact models i a ha

theorem project_root {I} (F : Family L I) (i : I) {a : Formula L n} {ρ : Fin n → F.D}
    (h : F.glue.Forces none ρ a) : (F.model i).Forces (F.root i) (F.proj i ∘ ρ) a :=
  (F.branch i _ ρ a).1 (F.glue.persistence (.enter (F.loop i)) ρ a h)

noncomputable def product {I} (M : I → Model L) (r : (i : I) → (M i).W)
    (hr : ∀ i, (M i).acc (r i) (r i)) : Family L I where
  model := M
  root := r
  loop := hr
  D := (i : I) → (M i).D
  nonempty := ⟨fun i => Classical.choice (M i).domain⟩
  proj i x := x i
  onto := by
    classical
    intro i y
    exact ⟨fun j => if e : i = j then e ▸ y else Classical.choice (M j).domain, by simp⟩
  func f ts i := (M i).func f (fun j => ts j i)
  map_func := fun _ _ _ _ => rfl
end Family

/-- Glue two countermodels below a common reflexive root. -/
theorem disjunctionProperty (Γ : Theory L 0) (fragment : ∀ a, Γ a → NegativeFragment a)
    (a b : Sentence L) (h : Entails Γ (disj a b)) : Entails Γ a ∨ Entails Γ b := by
  classical
  apply Classical.byContradiction
  intro hn
  let side : Bool → Sentence L := fun i => if i then b else a
  have miss (i : Bool) : ¬Entails Γ (side i) := by
    cases i with
    | false => exact fun ha => hn (Or.inl ha)
    | true => exact fun hb => hn (Or.inr hb)
  let C := fun i => Classical.choice (countermodel (miss i))
  let F := Family.product (fun i => (C i).model) (fun i => (C i).w) (fun i => (C i).loop)
  have reject (i : Bool) (hi : F.glue.Forces none closedEnv (side i)) : False := by
    have hp := F.project_root i hi
    rw [env_unique (F.proj i ∘ closedEnv)] at hp
    exact (C i).fails hp
  exact (h F.glue none closedEnv .loop (F.root_premises fragment (fun i => (C i).premises))).elim
    (reject false) (reject true)

/-- Terms over arbitrary additional names, used as the single domain of a glued model. -/
private inductive NamedTerm (L : Language) (A : Type) where
  | name (x : A)
  | app {k} (f : L.Func k) (ts : Fin k → NamedTerm L A)

namespace NamedTerm
private def erase (c : Term L 0) : NamedTerm L A → Term L 0
  | .name _ => c
  | .app f ts => .app f (fun j => erase c (ts j))

private def value (M : Model L) (σ : A → M.D) : NamedTerm L A → M.D
  | .name x => σ x
  | .app f ts => M.func f (fun j => value M σ (ts j))

private theorem bound {P : Nat → Fin k → Prop}
    (mono : ∀ n m, n ≤ m → ∀ j, P n j → P m j) (h : ∀ j, ∃ n, P n j) : ∃ n, ∀ j, P n j := by
  induction k with
  | zero => exact ⟨0,fun j => j.elim0⟩
  | succ k ih =>
    obtain ⟨n,hn⟩ := h 0
    obtain ⟨m,hm⟩ := ih (P := fun n j => P n j.succ)
      (fun n m e j => mono n m e j.succ) (fun j => h j.succ)
    exact ⟨max n m, Fin.cases (mono _ _ (Nat.le_max_left ..) 0 hn)
      (fun j => mono _ _ (Nat.le_max_right ..) _ (hm j))⟩

/-- A finite term mentions only names below some numerical bound. -/
private theorem erase_value (t : NamedTerm L (Nat × A)) (c : Term L 0) :
    ∃ n, ∀ (M : Model L) (σ : Nat × A → M.D),
      (∀ x, x.1 < n → σ x = M.eval closedEnv c) →
      value M σ t = M.eval closedEnv (erase c t) := by
  induction t with
  | name x => exact ⟨x.1+1,fun _ _ h => h x (Nat.lt_succ_self _)⟩
  | app f ts ih =>
    let P := fun n j => ∀ (M : Model L) (σ : Nat × A → M.D),
      (∀ x, x.1 < n → σ x = M.eval closedEnv c) →
      value M σ (ts j) = M.eval closedEnv (erase c (ts j))
    obtain ⟨n,hn⟩ := bound (P := P)
      (fun _ _ e _ hp M σ h => hp M σ (fun x hx => h x (Nat.lt_of_lt_of_le hx e))) ih
    exact ⟨n,fun M σ h => congrArg (M.func f) (funext (fun j => hn j M σ h))⟩
end NamedTerm

/-- Each closed term has a countermodel if there is no uniform witness.
At coordinate (t,n), all extra names numbered below n denote c. The other
names still cover that countermodel's domain. Thus every term in the glued
domain agrees with its erasure in at least one countermodel for that erasure. -/
theorem existenceProperty (Γ : Theory L 0) (fragment : ∀ a, Γ a → NegativeFragment a)
    (c : Term L 0) (a : Formula L 1) (h : Entails Γ (ex a)) :
    ∃ t : Term L 0, Entails Γ (a.inst t) := by
  classical
  apply Classical.byContradiction
  intro hn
  let T := Term L 0
  let C := fun t : T => Classical.choice (countermodel (fun p => hn ⟨t,p⟩))
  let A := (t : T) → (C t).model.D
  let σ := fun (i : T × Nat) (x : Nat × A) =>
    if x.1 < i.2 then (C i.1).model.eval closedEnv c else x.2 i.1
  let F : Family L (T × Nat) := {
    model := fun i => (C i.1).model
    root := fun i => (C i.1).w
    loop := fun i => (C i.1).loop
    D := NamedTerm L (Nat × A)
    nonempty := ⟨.name (0, fun t => Classical.choice (C t).model.domain)⟩
    proj := fun i => NamedTerm.value _ (σ i)
    onto := by
      intro i y
      let v : A := fun j => if e : i.1 = j then e ▸ y else Classical.choice (C j).model.domain
      exact ⟨.name (i.2,v), by simp [NamedTerm.value, σ, v]⟩
    func := NamedTerm.app
    map_func := fun _ _ _ _ => rfl }
  letI : Nonempty (T × Nat) := ⟨(c,0)⟩
  obtain ⟨x,hx⟩ := h F.glue none closedEnv .loop (F.root_premises fragment (fun i => (C i.1).premises))
  let t := x.erase c
  obtain ⟨n,hval⟩ := x.erase_value c
  have eq : F.proj (t,n) x = (C t).model.eval closedEnv t :=
    hval _ (σ (t,n)) (fun y hy => if_pos hy)
  have hp := F.project_root (t,n) hx
  rw [F.proj_extend, env_unique (F.proj (t,n) ∘ closedEnv), eq] at hp
  exact (C t).fails (((C t).model.forces_inst ..).2 hp)

end BQL
