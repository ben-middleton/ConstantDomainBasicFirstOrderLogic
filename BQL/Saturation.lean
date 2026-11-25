import BQL.Elimination

/-! Countable prime saturation for a single-conclusion relation on sentences.
A state records the conjunction accepted so far and the disjunction rejected
so far. The two quantifier conditions pick witnesses while preserving separation. -/
namespace BQL
open Formula
namespace Canonical
variable {L : Language}
abbrev F (L : Language) := Sentence L

structure Order (L : Language) where
  le : F L → F L → Prop
  refl : ∀ {a}, le a a
  trans : ∀ {a b c}, le a b → le b c → le a c
  top : ∀ {a}, le a Formula.top
  bot : ∀ {a}, le Formula.bot a
  left : ∀ {a b}, le (conj a b) a
  right : ∀ {a b}, le (conj a b) b
  meet : ∀ {x a b}, le x a → le x b → le x (conj a b)
  inl : ∀ {a b}, le a (disj a b)
  inr : ∀ {a b}, le b (disj a b)
  join : ∀ {x a b}, le a x → le b x → le (disj a b) x
  dist : ∀ {x a b}, le (conj x (disj a b)) (disj (conj x a) (conj x b))
  allE : ∀ {a} t, le (all a) (a.inst t)
  exI : ∀ {a} t, le (a.inst t) (ex a)
  allWitness : ∀ {x y a}, (∀ t, le x (disj y (a.inst t))) → le x (disj y (all a))
  exWitness : ∀ {x y a}, (∀ t, le (conj x (a.inst t)) y) → le (conj x (ex a)) y

structure Prime (O : Order L) where
  mem : F L → Prop
  top : mem top
  bot : ¬mem bot
  up : ∀ {a b}, O.le a b → mem a → mem b
  meet : ∀ {a b}, mem a → mem b → mem (conj a b)
  split : ∀ {a b}, mem (disj a b) → mem a ∨ mem b
  total : ∀ {a}, (∀ t, mem (a.inst t)) → mem (all a)
  witness : ∀ {a}, mem (ex a) → ∃ t, mem (a.inst t)

structure Pair (O : Order L) where
  yes : F L
  no : F L
  sep : ¬ O.le yes no

namespace Pair
variable {O : Order L}

private def Refines (s t : Pair O) := O.le t.yes s.yes ∧ O.le s.no t.no
private def Decides (t : Pair O) (a : F L) :=
  (O.le t.yes a ∨ O.le a t.no) ∧
  (∀ b, a = ex b → O.le t.yes a → ∃ u, O.le t.yes (b.inst u)) ∧
  (∀ b, a = all b → O.le a t.no → ∃ u, O.le (b.inst u) t.no)

private theorem leftChoice (s : Pair O) (a : F L) (h : O.le (conj s.yes a) s.no) :
    ¬ O.le s.yes (disj s.no a) := fun bad => s.sep <|
  O.trans (O.trans (O.meet O.refl bad) O.dist) (O.join O.right h)

private theorem accept (s : Pair O) (a : F L) (h : ¬ O.le (conj s.yes a) s.no) :
    ∃ t : Pair O, s.Refines t ∧ O.le t.yes a ∧
      (∀ b, a = ex b → ∃ u, O.le t.yes (b.inst u)) := by
  classical
  by_cases he : ∃ b, a = ex b
  · obtain ⟨b,rfl⟩ := he
    obtain ⟨u,hu⟩ := Classical.not_forall.mp (fun ht => h (O.exWitness ht))
    exact ⟨⟨_,_,hu⟩,⟨O.left,O.refl⟩,O.trans O.right (O.exI u),
      fun c e => by cases e; exact ⟨u,O.right⟩⟩
  · exact ⟨⟨_,_,h⟩,⟨O.left,O.refl⟩,O.right,fun b e => (he ⟨b,e⟩).elim⟩

private theorem reject (s : Pair O) (a : F L) (h : ¬ O.le s.yes (disj s.no a)) :
    ∃ t : Pair O, s.Refines t ∧ O.le a t.no ∧
      (∀ b, a = all b → ∃ u, O.le (b.inst u) t.no) := by
  classical
  by_cases he : ∃ b, a = all b
  · obtain ⟨b,rfl⟩ := he
    obtain ⟨u,hu⟩ := Classical.not_forall.mp (fun ht => h (O.allWitness ht))
    exact ⟨⟨_,_,hu⟩,⟨O.refl,O.inl⟩,O.trans (O.allE u) O.inr,
      fun c e => by cases e; exact ⟨u,O.inr⟩⟩
  · exact ⟨⟨_,_,h⟩,⟨O.refl,O.inl⟩,O.inr,fun b e => (he ⟨b,e⟩).elim⟩

private theorem step_exists (s : Pair O) (a : F L) : ∃ t, s.Refines t ∧ t.Decides a := by
  classical
  by_cases h : O.le (conj s.yes a) s.no
  · obtain ⟨t,ref,neg,hall⟩ := s.reject a (s.leftChoice a h)
    exact ⟨t,ref,Or.inr neg,fun _ _ pos => (t.sep (O.trans pos neg)).elim,fun b e _ => hall b e⟩
  · obtain ⟨t,ref,pos,hex⟩ := s.accept a h
    exact ⟨t,ref,Or.inl pos,fun b e _ => hex b e,fun _ _ neg => (t.sep (O.trans pos neg)).elim⟩

noncomputable def chain (s : Pair O) (enum : Nat → F L) : Nat → Pair O
  | 0 => s
  | n+1 => Classical.choose ((chain s enum n).step_exists (enum n))

theorem extend (s : Pair O) (enum : Nat → F L) (covers : ∀ a, ∃ n, enum n = a) :
    ∃ W : Prime O, W.mem s.yes ∧ ¬W.mem s.no := by
  let S := s.chain enum
  have step n : (S n).Refines (S (n+1)) ∧ (S (n+1)).Decides (enum n) :=
    Classical.choose_spec ((S n).step_exists (enum n))
  have mono {i j : Nat} (h : i ≤ j) : (S i).Refines (S j) := by
    induction h with
    | refl => exact ⟨O.refl,O.refl⟩
    | step h ih => exact ⟨O.trans (step _).1.1 ih.1,O.trans ih.2 (step _).1.2⟩
  let pos := fun a => ∃ i, O.le (S i).yes a
  let neg := fun a => ∃ i, O.le a (S i).no
  have clash {a} : pos a → neg a → False := by
    rintro ⟨i,hi⟩ ⟨j,hj⟩
    exact (S (max i j)).sep (O.trans (O.trans (mono (Nat.le_max_left ..)).1 hi)
      (O.trans hj (mono (Nat.le_max_right ..)).2))
  have decision a : pos a ∨ neg a := by
    obtain ⟨i,rfl⟩ := covers a
    exact (step i).2.1.imp (fun h => ⟨_,h⟩) (fun h => ⟨_,h⟩)
  refine ⟨⟨pos,⟨0,O.top⟩,fun h => clash h ⟨0,O.bot⟩,fun h ⟨i,hi⟩ => ⟨i,O.trans hi h⟩,?_,?_,?_,?_⟩,
    ⟨0,O.refl⟩,fun h => clash h ⟨0,O.refl⟩⟩
  · rintro a b ⟨i,hi⟩ ⟨j,hj⟩
    exact ⟨max i j,O.meet (O.trans (mono (Nat.le_max_left ..)).1 hi) (O.trans (mono (Nat.le_max_right ..)).1 hj)⟩
  · intro a b hab
    rcases decision a with h | ⟨i,hi⟩
    · exact Or.inl h
    rcases decision b with h | ⟨j,hj⟩
    · exact Or.inr h
    exact (clash hab ⟨max i j,O.join (O.trans hi (mono (Nat.le_max_left ..)).2)
      (O.trans hj (mono (Nat.le_max_right ..)).2)⟩).elim
  · intro a ha
    obtain ⟨i,he⟩ := covers (all a)
    rcases (step i).2.1 with h | h
    · exact ⟨_,he ▸ h⟩
    obtain ⟨u,hu⟩ := (step i).2.2.2 a he h
    exact (clash (ha u) ⟨_,hu⟩).elim
  · intro a ha
    obtain ⟨i,he⟩ := covers (ex a)
    rcases (step i).2.1 with h | h
    · obtain ⟨u,hu⟩ := (step i).2.2.1 a he h
      exact ⟨u,_,hu⟩
    exact (clash ha ⟨_,he ▸ h⟩).elim
end Pair
end Canonical
end BQL
