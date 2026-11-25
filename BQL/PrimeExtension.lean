import BQL.Canonical
import BQL.Support

namespace BQL.Canonical
open Formula
variable {L : Language}

def Fresh (L : Language) := ∀ xs : List (Symbol L), ∃ c : L.Func 0, Symbol.fn c ∉ xs

structure HenkinLanguage (L : Language) where
  fresh : Fresh L
  enum : Nat → Sentence L
  covers : ∀ a, ∃ n, enum n = a

/-- Infinitely many parameters are still available outside the background
theory, expressed by avoidance of every additional finite list of symbols. -/
def FreshFor (Γ : Theory L 0) := ∀ xs : List (Symbol L), ∃ c : L.Func 0,
  Symbol.fn c ∉ xs ∧ ∀ a, Γ a → Symbol.fn c ∉ a.symbols

private abbrev Over (Γ : Theory L 0) (a b : F L) := TJK L true (insert a Γ) b
private theorem given {Γ : Theory L n} {x} : TJK L true (insert x Γ) x := .hyp (Or.inl rfl)
private theorem compose {Γ : Theory L 0} {a b c} (p : Over Γ a b) (q : Over Γ b c) : Over Γ a c :=
  q.cut (fun _ h => h.elim (fun e => e ▸ p) (fun hg => TJK.hyp (Or.inr hg)))

private theorem overAll {Γ : Theory L 0} (fresh : FreshFor Γ) {x y : F L} {a : Formula L 1}
    (h : ∀ t, Over Γ x (disj y (a.inst t))) : Over Γ x (disj y (all a)) := by
  obtain ⟨c,hc,hG⟩ := fresh (x.symbols ++ y.symbols ++ a.symbols)
  simp only [List.mem_append,not_or] at hc
  apply TJK.cd
  apply TJK.allI
  have independent b (hb : insert x Γ b) : Symbol.fn c ∉ b.symbols :=
    hb.elim (fun e => e ▸ hc.1.1) (hG b)
  have hh := Translation.proof (h (constTerm c)) (Translation.openConst c)
    (G := lifted (insert x Γ)) (fun b hb => ⟨b,hb,(Translation.open_independent (independent b hb)).symm⟩)
  simpa only [Translation.form,Translation.open_instance hc.2,Translation.open_independent hc.1.2] using hh

private theorem overEx {Γ : Theory L 0} (fresh : FreshFor Γ) {x y : F L} {a : Formula L 1}
    (h : ∀ t, Over Γ (conj x (a.inst t)) y) : Over Γ (conj x (ex a)) y := by
  obtain ⟨c,hc,hG⟩ := fresh (x.symbols ++ y.symbols ++ a.symbols)
  simp only [List.mem_append,not_or] at hc
  apply TJK.exE rfl (TJK.andR given)
  let T := Translation.openConst (n := 0) c
  have eq : T.form (conj x (a.inst (constTerm c))) = conj x.lift a := by
    simp only [T,Translation.form,Translation.open_independent hc.1.1,Translation.open_instance hc.2]
  have hh := Translation.proof (h (constTerm c)) T (G := insert (conj x.lift a) (lifted Γ))
    (fun b hb => hb.elim (fun e => Or.inl (e ▸ eq))
      (fun hg => Or.inr ⟨b,hg,(Translation.open_independent (hG b hg)).symm⟩))
  rw [show T.form y = y.lift from Translation.open_independent hc.1.2] at hh
  apply hh.cut
  rintro _ (rfl | ⟨b,hb,rfl⟩)
  · exact .andI (.andL (.hyp (Or.inr ⟨_,Or.inl rfl,rfl⟩))) (.hyp (Or.inl rfl))
  · exact .hyp (Or.inr ⟨b,Or.inr hb,rfl⟩)

private def overOrder {Γ : Theory L 0} (fresh : FreshFor Γ) : Order L where
  le := Over Γ
  refl := given
  trans := compose
  top := .topI
  bot := .botE given
  left := .andL given
  right := .andR given
  meet := .andI
  inl := .orL given
  inr := .orR given
  join p q := .orE given (p.weaken (fun _ h => h.imp_right Or.inr)) (q.weaken (fun _ h => h.imp_right Or.inr))
  dist := .mp given (.ax .dist)
  allE t := .allE t given
  exI t := .exI t given
  allWitness := overAll fresh
  exWitness := overEx fresh

theorem primeExtension {Γ : Theory L 0} (fresh : FreshFor Γ) (enum : Nat → F L)
    (covers : ∀ a, ∃ i, enum i = a) {a} (h : ¬Proves Γ a) :
    ∃ w : Point L, Access w w ∧ Incl Γ w.mem ∧ ¬w.mem a := by
  let s : Pair (overOrder fresh) := ⟨top,a,fun p => h (p.cut (fun _ hx =>
    hx.elim (fun e => e ▸ TJK.topI) TJK.hyp)).toRoot⟩
  obtain ⟨p,ht,ha⟩ := s.extend enum covers
  let w := p.toPoint (fun q => (TJK.ofRoot (q.raise (j := none) trivial)).weaken (fun _ e => Or.inl e.symm))
  have loop : Access w w := fun _ _ hi hx =>
    p.up (show Over Γ _ _ from TJK.mp (.andR given) (.andL given)) (p.meet hi hx)
  exact ⟨w,loop,fun _ hg => p.up (show Over Γ top _ from .hyp (Or.inr hg)) ht,ha⟩
end BQL.Canonical
