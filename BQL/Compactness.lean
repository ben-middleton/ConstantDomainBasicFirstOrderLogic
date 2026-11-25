import BQL.Semantics
import BQL.Iteration

namespace BQL
namespace Compactness
open Iteration
variable {X : Type}

private def FiniteCharacter (P : List X → Prop) (s : X → Prop) :=
  ∀ xs, (∀ x ∈ xs, s x) → P xs

private theorem finiteMax (P : List X → Prop) (base : X → Prop) (hb : FiniteCharacter P base) :
    ∃ s, Subset base s ∧ FiniteCharacter P s ∧
      ∀ t, Subset s t → FiniteCharacter P t → Subset t s := by
  classical
  let holds := fun a : X → Prop => FiniteCharacter P (fun x => base x ∨ a x)
  let bigger := fun a b : X → Prop => Subset a b ∧ ¬Subset b a ∧ holds b
  let f := fun a => if h : ∃ b, bigger a b then Classical.choose h else a
  have inc a : Subset a (f a) := by
    dsimp only [f]
    split <;> rename_i h
    · exact (Classical.choose_spec h).1
    · exact fun _ => id
  have bound {S : (X → Prop) → Prop} (hs : ∀ a, S a → Stage f a)
      {xs : List X} (hx : ∀ x ∈ xs, base x ∨ sup S x) :
      (∀ x ∈ xs, base x) ∨ ∃ a, S a ∧ ∀ x ∈ xs, base x ∨ a x := by
    induction xs with
    | nil => exact Or.inl (by simp)
    | cons x xs ih =>
      have tail := ih (fun z hz => hx z (List.mem_cons_of_mem _ hz))
      rcases hx x (.head _) with h | ⟨a,ha,hax⟩
      · rcases tail with t | ⟨b,hb,t⟩
        · exact Or.inl (List.forall_mem_cons.mpr ⟨h,t⟩)
        · exact Or.inr ⟨b,hb,List.forall_mem_cons.mpr ⟨Or.inl h,t⟩⟩
      · apply Or.inr
        rcases tail with t | ⟨b,hb,t⟩
        · exact ⟨a,ha,List.forall_mem_cons.mpr ⟨Or.inr hax,fun z hz => Or.inl (t z hz)⟩⟩
        · rcases comparable f inc (hs a ha) (hs b hb) with ba | ab
          · exact ⟨a,ha,List.forall_mem_cons.mpr ⟨Or.inr hax,fun z hz => (t z hz).imp_right (fun h => ba h)⟩⟩
          · exact ⟨b,hb,List.forall_mem_cons.mpr ⟨Or.inr (ab hax),t⟩⟩
  have ok {a} (stage : Stage f a) : holds a := by
    induction stage with
    | step _ ih =>
      dsimp only [f]
      split <;> rename_i h
      · exact (Classical.choose_spec h).2.2
      · exact ih
    | limit S hs ih =>
      intro xs hx
      rcases bound hs hx with h | ⟨a,ha,h⟩
      · exact hb xs h
      · exact ih a ha xs h
  let a := total f
  refine ⟨fun x => base x ∨ a x, fun _ => Or.inl, ok (stage_total f), ?_⟩
  intro t st ht x tx
  apply Classical.byContradiction
  intro hn
  have ex : ∃ b, bigger a b := ⟨t,fun _ h => st (Or.inr h),fun h => hn (Or.inr (h tx)),
    fun xs hh => ht xs (fun y hy => (hh y hy).elim (fun h => st (Or.inl h)) id)⟩
  have eq : Classical.choose ex = a := by
    calc
      _ = f a := (dif_pos ex).symm
      _ = a := fixed f inc
  exact (Classical.choose_spec ex).2.1 (fun _ h => eq ▸ h)

structure Ultra (I : Type) where
  large : (I → Prop) → Prop
  univ : large (fun _ => True)
  proper : ¬large (fun _ => False)
  inter : ∀ {p q}, large p → large q → large (fun i => p i ∧ q i)
  mono : ∀ {p q}, (∀ i, p i → q i) → large p → large q
  decide : ∀ p, large p ∨ large (fun i => ¬ p i)

private def Meets (ps : List (X → Prop)) := ∃ x, ∀ p ∈ ps, p x

private theorem extendUltra (base : (X → Prop) → Prop) (hb : FiniteCharacter Meets base) :
    ∃ U : Ultra X, Subset base U.large := by
  classical
  obtain ⟨s,bs,hs,maximal⟩ := finiteMax Meets base hb
  let Pos := fun (p : X → Prop) => ∀ ps : List (X → Prop), (∀ q ∈ ps, s q) → ∃ x, p x ∧ ∀ q ∈ ps, q x
  have add (p) (h : Pos p) : s p := by
    apply maximal (fun q => q = p ∨ s q) (fun _ => Or.inr) _ (Or.inl rfl)
    intro ps hps
    let qs := ps.filter (fun q => decide (s q))
    obtain ⟨x,hx,hqs⟩ := h qs (fun q hq => of_decide_eq_true (List.mem_filter.mp hq).2)
    refine ⟨x,fun q hq => ?_⟩
    rcases hps q hq with rfl | sq
    · exact hx
    · exact hqs q (List.mem_filter.mpr ⟨hq,decide_eq_true sq⟩)
  have pos {p} (hp : s p) : Pos p := by
    intro ps hh
    obtain ⟨x,h⟩ := hs (p::ps) (List.forall_mem_cons.mpr ⟨hp,hh⟩)
    exact ⟨x,List.forall_mem_cons.mp h⟩
  refine ⟨⟨s,?_,?_,?_,?_,?_⟩,bs⟩
  · exact add _ (fun ps hh => (hs ps hh).imp (fun _ h => ⟨trivial,h⟩))
  · intro h
    obtain ⟨_,hx,_⟩ := pos h [] (by simp)
    exact hx
  · intro p q hp hq
    apply add
    intro ps hh
    obtain ⟨x,hx,h⟩ := pos hp (q::ps) (List.forall_mem_cons.mpr ⟨hq,hh⟩)
    exact ⟨x,⟨hx,(List.forall_mem_cons.mp h).1⟩,(List.forall_mem_cons.mp h).2⟩
  · intro p q pq hp
    exact add _ (fun ps hh => (pos hp ps hh).imp (fun x h => ⟨pq x h.1,h.2⟩))
  · intro p
    by_cases sp : s p
    · exact Or.inl sp
    · apply Or.inr
      apply add
      have fail : ¬ Pos p := fun h => sp (add p h)
      simp only [Pos,Classical.not_forall,Classical.not_imp] at fail
      obtain ⟨qs,hqs,no⟩ := fail
      intro ps hh
      obtain ⟨x,h⟩ := hs (qs ++ ps) (List.forall_mem_append.mpr ⟨hqs,hh⟩)
      have both := List.forall_mem_append.mp h
      exact ⟨x, fun hx => no ⟨x,hx,both.1⟩,both.2⟩

namespace Ultra
variable {I : Type} (U : Ultra I)
theorem all {p : I → Prop} (h : ∀ i, p i) : U.large p := U.mono (fun i _ => h i) U.univ

theorem neg {p : I → Prop} : U.large (fun i => ¬p i) ↔ ¬U.large p := by
  refine ⟨fun hn hp => U.proper (U.mono (fun _ h => h.1 h.2) (U.inter hn hp)), ?_⟩
  exact fun h => (U.decide p).resolve_left h

theorem conj {p q : I → Prop} : U.large (fun i => p i ∧ q i) ↔ U.large p ∧ U.large q :=
  ⟨fun h => ⟨U.mono (fun _ => And.left) h,U.mono (fun _ => And.right) h⟩,fun h => U.inter h.1 h.2⟩

theorem disj {p q : I → Prop} : U.large (fun i => p i ∨ q i) ↔ U.large p ∨ U.large q := by
  refine ⟨fun h => ?_,fun h => h.elim (U.mono fun _ => Or.inl) (U.mono fun _ => Or.inr)⟩
  rcases U.decide p with hp | hn
  · exact Or.inl hp
  · exact Or.inr (U.mono (fun _ h => h.1.resolve_left h.2) (U.inter h hn))

theorem exists_iff {D : I → Type} (ne : ∀ i, Nonempty (D i)) (p : (i : I) → D i → Prop) :
    U.large (fun i => ∃ d, p i d) ↔ ∃ x : (i : I) → D i, U.large (fun i => p i (x i)) := by
  classical
  refine ⟨fun h => ?_,fun ⟨x,h⟩ => U.mono (fun i hp => ⟨x i,hp⟩) h⟩
  let x := fun i => if e : ∃ d, p i d then Classical.choose e else Classical.choice (ne i)
  exact ⟨x,U.mono (fun i e => by simpa [x,e] using Classical.choose_spec e) h⟩

theorem forall_iff {D : I → Type} (ne : ∀ i, Nonempty (D i)) (p : (i : I) → D i → Prop) :
    U.large (fun i => ∀ d, p i d) ↔ ∀ x : (i : I) → D i, U.large (fun i => p i (x i)) := by
  classical
  refine ⟨fun h x => U.mono (fun i hi => hi (x i)) h,fun h => ?_⟩
  apply Classical.byContradiction
  intro hn
  have bad := U.mono (fun i (hi : ¬∀ d, p i d) => Classical.not_forall.mp hi) (U.neg.mpr hn)
  obtain ⟨x,hx⟩ := (U.exists_iff ne _).1 bad
  exact U.neg.mp hx (h x)

theorem implies {p q : I → Prop} : U.large (fun i => p i → q i) ↔ (U.large p → U.large q) := by
  classical
  refine ⟨fun h hp => U.mono (fun _ h => h.1 h.2) (U.inter h hp),fun h => ?_⟩
  rcases U.decide p with hp | hn
  · exact U.mono (fun _ hq _ => hq) (h hp)
  · exact U.mono (fun _ hn hp => (hn hp).elim) hn


variable {L : Language} (M : I → Model L)

/-- In the equality-free language one may keep representatives in both
products. All atomic relations and accessibility are tested modulo U. -/
noncomputable def product : Model L where
  W := (i : I) → (M i).W
  D := (i : I) → (M i).D
  worlds := ⟨fun i => Classical.choice (M i).worlds⟩
  domain := ⟨fun i => Classical.choice (M i).domain⟩
  acc w z := U.large (fun i => (M i).acc (w i) (z i))
  trans h k := U.mono (fun i h => (M i).trans h.1 h.2) (U.inter h k)
  func f ts i := (M i).func f (fun j => ts j i)
  rel r w ts := U.large (fun i => (M i).rel r (w i) (fun j => ts j i))
  persist e h := U.mono (fun i h => (M i).persist h.1 h.2) (U.inter e h)

theorem eval_product (i : I) (ρ : Fin n → (U.product M).D) (t : Term L n) :
    (U.product M).eval ρ t i = (M i).eval (fun j => ρ j i) t := by
  induction t with
  | var => rfl
  | app f _ ih => exact congrArg ((M i).func f) (funext ih)

private theorem extend_apply (ρ : Fin n → (i : I) → (M i).D) (x : (i : I) → (M i).D) (i : I) :
    (fun j => extend ρ x j i) = extend (fun j => ρ j i) (x i) :=
  funext (fun j => Fin.cases rfl (fun _ => rfl) j)

theorem los (w : (U.product M).W) (ρ : Fin n → (U.product M).D) (a : Formula L n) :
    (U.product M).Forces w ρ a ↔ U.large (fun i => (M i).Forces (w i) (fun j => ρ j i) a) := by
  induction a generalizing w with
  | top => exact ⟨fun _ => U.univ,fun _ => trivial⟩
  | bot => exact ⟨False.elim,U.proper⟩
  | atom r ts =>
    change U.large _ ↔ U.large _
    simp only [Model.Forces,eval_product]
  | conj _ _ ih ik => exact (and_congr (ih ..) (ik ..)).trans U.conj.symm
  | disj _ _ ih ik => exact (or_congr (ih ..) (ik ..)).trans U.disj.symm
  | imp a b ih ik =>
    change (∀ z, U.large _ → _ → _) ↔ U.large (fun i => ∀ z, _ → _ → _)
    rw [U.forall_iff (fun i => (M i).worlds)]
    exact forall_congr' (fun z => by rw [U.implies, U.implies, ih, ik])
  | all a ih =>
    change (∀ x, _) ↔ U.large (fun i => ∀ x, (M i).Forces _ _ a)
    rw [U.forall_iff (fun i => (M i).domain)]
    exact forall_congr' (fun x => by rw [ih]; simp only [extend_apply])
  | ex a ih =>
    change (∃ x, _) ↔ U.large (fun i => ∃ x, (M i).Forces _ _ a)
    rw [U.exists_iff (fun i => (M i).domain)]
    exact exists_congr (fun x => by rw [ih]; simp only [extend_apply])

end Ultra

/-- The cones of lists containing a specified premise have the finite intersection property. -/
private theorem cones {A : Type} :
    ∃ U : Ultra (List A), ∀ a, U.large (fun xs => a ∈ xs) := by
  let base := fun p : List A → Prop => ∃ a, p = (fun xs => a ∈ xs)
  have fip : FiniteCharacter Meets base := by
    intro ps
    induction ps with
    | nil => exact fun _ => ⟨[],by simp⟩
    | cons p ps ih =>
      intro hh
      obtain ⟨a,rfl⟩ := hh _ (.head _)
      obtain ⟨xs,hxs⟩ := ih (fun q hq => hh q (.tail _ hq))
      refine ⟨a::xs,List.forall_mem_cons.mpr ⟨.head _,?_⟩⟩
      intro q hq
      obtain ⟨b,rfl⟩ := hh q (.tail _ hq)
      exact List.mem_cons_of_mem _ (hxs _ hq)
  obtain ⟨U,h⟩ := extendUltra base fip
  exact ⟨U,fun a => h ⟨a,rfl⟩⟩

end Compactness

theorem compactness {L : Language} {Γ : Theory L n} {a : Formula L n} (h : Entails Γ a) :
    ∃ xs : List (Formula L n), (∀ b ∈ xs, Γ b) ∧ Entails (fun b => b ∈ xs) a := by
  classical
  apply Classical.byContradiction
  intro hn
  let I := List {b // Γ b}
  let prem := fun (i : I) (b : Formula L n) => b ∈ i.map Subtype.val
  have bad (i : I) : ¬ Entails (prem i) a := by
    intro good
    exact hn ⟨_,fun _ hb => by obtain ⟨b,_,rfl⟩ := List.mem_map.mp hb; exact b.property,good⟩
  let models (i : I) := Classical.not_forall.mp (bad i)
  let M := fun i => Classical.choose (models i)
  have worlds (i) := Classical.not_forall.mp (Classical.choose_spec (models i))
  let w := fun i => Classical.choose (worlds i)
  have envs (i) := Classical.not_forall.mp (Classical.choose_spec (worlds i))
  let ρ := fun i => Classical.choose (envs i)
  have facts i : (M i).acc (w i) (w i) ∧ (M i).Satisfies (w i) (ρ i) (prem i) ∧
      ¬(M i).Forces (w i) (ρ i) a := by
    simpa only [M, w, ρ, Classical.not_imp] using Classical.choose_spec (envs i)
  obtain ⟨U,hu⟩ := Compactness.cones (A := {b // Γ b})
  let η := fun j i => ρ i j
  have root : (U.product M).acc w w := U.all (fun i => (facts i).1)
  have sat : (U.product M).Satisfies w η Γ := by
    intro b hb
    apply (U.los M w η b).2
    exact U.mono (fun i hi => (facts i).2.1 b (List.mem_map.mpr ⟨⟨b,hb⟩,hi,rfl⟩)) (hu ⟨b,hb⟩)
  exact U.neg.mp (U.all (fun i => (facts i).2.2)) ((U.los M w η a).1 (h _ _ _ root sat))

end BQL
