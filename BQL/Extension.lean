import BQL.PrimeExtension

namespace BQL.Canonical
open Formula
variable {L : Language}

theorem extension (H : HenkinLanguage L) {x y : F L} (h : ¬TJK L true (single x) y) :
    ∃ w : Point L, Access w w ∧ w.mem x ∧ ¬w.mem y := by
  have fresh : FreshFor (single x) := by
    intro xs
    obtain ⟨c,hc⟩ := H.fresh (xs ++ x.symbols)
    simp only [List.mem_append,not_or] at hc
    exact ⟨c,hc.1,fun _ e => e ▸ hc.2⟩
  obtain ⟨w,loop,g,hy⟩ := primeExtension fresh H.enum H.covers (fun p => h (TJK.ofRoot p))
  exact ⟨w,loop,g rfl,hy⟩

theorem singletonComplete (H : HenkinLanguage L) {x y : F L} (h : Entails (single x) y) : TJK L true (single x) y := by
  apply Classical.byContradiction
  intro hn
  obtain ⟨w,loop,hx,hy⟩ := extension H hn
  obtain ⟨c,_⟩ := H.fresh []
  let pt : Nonempty (Point L) := ⟨w⟩
  let ht : Nonempty (Term L 0) := ⟨constTerm c⟩
  have truth (a : F L) : (model pt ht).Forces w Term.var a ↔ w.mem a := by
    simpa only [subst_var] using truthLemma H.enum H.covers pt ht w Term.var a
  exact hy ((truth y).1 (h (model pt ht) w Term.var loop (fun _ e => e ▸ (truth x).2 hx)))

end BQL.Canonical
