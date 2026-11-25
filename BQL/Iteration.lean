import Std

/-! Iteration of an inflationary operation on subsets. The generated stages
are closed under successors and suprema. Their union is a fixed point. This
gives a small index type for transfinite constructions without choosing ordinal
representatives. -/
namespace BQL.Iteration
variable {X : Type}

abbrev Subset (a b : X → Prop) := ∀ ⦃x⦄, a x → b x
local infix:50 " ⊆ " => Subset

def sup (S : (X → Prop) → Prop) : X → Prop := fun x => ∃ a, S a ∧ a x

theorem antisymm {a b : X → Prop} (ab : a ⊆ b) (ba : b ⊆ a) : a = b :=
  funext (fun _ => propext ⟨fun h => ab h,fun h => ba h⟩)

variable (f : (X → Prop) → X → Prop)

inductive Stage : (X → Prop) → Prop where
  | step : Stage a → Stage (f a)
  | limit (S) : (∀ a, S a → Stage a) → Stage (sup S)

def total := sup (Stage f)

theorem stage_total : Stage f (total f) := .limit _ (fun _ => id)

theorem contained {a} (ha : Stage f a) : a ⊆ total f := fun _ hx => ⟨a,ha,hx⟩

theorem fixed (inc : ∀ a, a ⊆ f a) : f (total f) = total f :=
  antisymm (contained f (.step (stage_total f))) (inc _)

private def Good (a : X → Prop) := ∀ b, Stage f b → b ⊆ a → ¬a ⊆ b → f b ⊆ a

private theorem split (inc : ∀ a, a ⊆ f a) {a} (good : Good f a)
    {b} (hb : Stage f b) : b ⊆ a ∨ f a ⊆ b := by
  classical
  induction hb with
  | step h ih =>
    rename_i b
    rcases ih with ba | ab
    · by_cases e : a ⊆ b
      · rw [antisymm e ba]
        exact Or.inr (fun _ h => h)
      · exact Or.inl (good b h ba e)
    · exact Or.inr (fun _ h => inc b (ab h))
  | limit S hs ih =>
    by_cases e : ∀ b, S b → b ⊆ a
    · exact Or.inl (fun _ ⟨b,hb,hx⟩ => e b hb hx)
    · apply Or.inr
      obtain ⟨b,hsb,hba⟩ : ∃ b, S b ∧ ¬ b ⊆ a := by
        apply Classical.byContradiction
        exact fun hn => e (fun b hb => Classical.byContradiction (fun h => hn ⟨b,hb,h⟩))
      exact fun _ h => ⟨b,hsb,((ih b hsb).resolve_left hba) h⟩

private theorem good_stage (inc : ∀ a, a ⊆ f a) {a} (ha : Stage f a) : Good f a := by
  classical
  induction ha with
  | step h ih =>
    rename_i a
    intro b hb _ hn
    have ba := (split f inc ih hb).resolve_right hn
    by_cases ab : a ⊆ b
    · rw [antisymm ba ab]
      exact fun _ h => h
    · exact fun _ hx => inc _ (ih _ hb ba ab hx)
  | limit S hs ih =>
    intro b hb _ hn
    obtain ⟨a,ha,nab⟩ : ∃ a, S a ∧ ¬ a ⊆ b := by
      apply Classical.byContradiction
      intro h
      exact hn (fun _ ⟨a,ha,hx⟩ => (Classical.byContradiction (fun h' => h ⟨a,ha,h'⟩) : a ⊆ b) hx)
    have ba := (split f inc (ih a ha) hb).resolve_right (fun fab => nab (fun _ hx => fab (inc a hx)))
    exact fun _ hx => ⟨a,ha,ih a ha b hb ba nab hx⟩

theorem comparable (inc : ∀ a, a ⊆ f a) {a b} (ha : Stage f a) (hb : Stage f b) :
    b ⊆ a ∨ a ⊆ b :=
  (split f inc (good_stage f inc ha) hb).imp_right (fun h _ hx => h (inc _ hx))

theorem successor_below (inc : ∀ a, a ⊆ f a) {a b} (ha : Stage f a) (hb : Stage f b)
    (strict : ¬ b ⊆ a) : f a ⊆ b :=
  (split f inc (good_stage f inc ha) hb).resolve_left strict

theorem fixedStage (inc : ∀ a, a ⊆ f a) {a} (ha : Stage f a) (stop : f a = a) : a = total f := by
  apply antisymm (contained f ha)
  rintro x ⟨b,hb,hx⟩
  have below {b} (hb : Stage f b) : b ⊆ a := by
    induction hb with
    | @step b h ih =>
      by_cases ab : a ⊆ b
      · rw [antisymm ih ab, stop]
        exact fun _ => id
      · exact successor_below f inc h ha ab
    | limit _ _ ih => exact fun _ ⟨_,hs,h⟩ => ih _ hs h
  exact below hb hx

/-- Proper inclusion well-orders the chain of generated stages. -/
def Earlier (a b : {s // Stage f s}) : Prop := a.val ⊆ b.val ∧ ¬ b.val ⊆ a.val

theorem wellFounded (inc : ∀ a, a ⊆ f a) : WellFounded (Earlier f) := by
  classical
  constructor
  rintro ⟨a,ha⟩
  induction ha with
  | @step a ha ih =>
    constructor
    rintro ⟨b,hb⟩ ⟨_,strict⟩
    have ba := (split f inc (good_stage f inc ha) hb).resolve_right strict
    by_cases ab : a ⊆ b
    · obtain rfl := antisymm ab ba
      exact ih
    · exact ih.inv ⟨ba,ab⟩
  | limit S hs ih =>
    constructor
    rintro ⟨b,hb⟩ ⟨_,strict⟩
    obtain ⟨c,hc,cb⟩ : ∃ c, S c ∧ ¬ c ⊆ b := by
      apply Classical.byContradiction
      intro hn
      exact strict (fun _ ⟨c,hc,hx⟩ => (Classical.byContradiction (fun h => hn ⟨c,hc,h⟩) : c ⊆ b) hx)
    exact (ih c hc).inv ⟨(comparable f inc (hs c hc) hb).resolve_right cb,cb⟩

end BQL.Iteration
