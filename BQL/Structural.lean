import BQL.Deduction
import BQL.Substitution

namespace BQL
open Formula
abbrev Incl {α : Type} (A B : α → Prop) := ∀ ⦃x⦄, A x → B x

theorem incl_insert {Γ Δ : Theory L n} (h : Incl Γ Δ) (a) : Incl (insert a Γ) (insert a Δ) :=
  fun _ => Or.imp_right (fun h' => h h')

theorem incl_lifted {Γ Δ : Theory L n} (h : Incl Γ Δ) : Incl (lifted Γ) (lifted Δ) :=
  fun _ ⟨a,ha,e⟩ => ⟨a,h ha,e⟩

namespace Derivation
variable {L : Language} {a b c : Formula L n} {Γ Δ : Theory L n}

theorem weaken (p : Derivation L k Γ Δ a) {G D} (g : Incl Γ G) (d : Incl Δ D) : Derivation L k G D a := by
  induction p with
  | extra h => exact h.elim
  | global h => exact .global (g h)
  | hyp h => exact .hyp (d h)
  | orE _ _ _ h u v => exact .orE (h g d) (u g (incl_insert d _)) (v g (incl_insert d _))
  | impI _ h => exact .impI (h g (incl_insert d _))
  | impE e _ _ h v => exact .impE e (h g d) (v g (fun _ => id))
  | allI _ h => exact .allI (h (incl_lifted g) (incl_lifted d))
  | exE _ _ h v => exact .exE (h g d) (v (incl_lifted g) (incl_insert (incl_lifted d) _))
  | topI  => exact .topI
  | botE _ h => exact .botE (h g d)
  | andI _ _ h i => exact .andI (h g d) (i g d)
  | andL _ h => exact .andL (h g d)
  | andR _ h => exact .andR (h g d)
  | orL _ h => exact .orL (h g d)
  | orR _ h => exact .orR (h g d)
  | trans _ _ h i => exact .trans (h g d) (i g d)
  | meet _ _ h i => exact .meet (h g d) (i g d)
  | join _ _ h i => exact .join (h g d) (i g d)
  | allE t _ h => exact .allE t (h g d)
  | exI t _ h => exact .exI t (h g d)
  | cd _ h => exact .cd (h g d)
  | internalAll _ h => exact .internalAll (h g d)
  | internalEx _ h => exact .internalEx (h g d)

abbrev add (p : Derivation L k Γ Δ a) (b : Formula L n) : Derivation L k Γ (insert b Δ) a :=
  p.weaken (fun _ => id) (fun _ => Or.inr)

def MapInto (s : Fin n → Term L m) (Γ : Theory L n) (G : Theory L m) :=
  ∀ ⦃x⦄, Γ x → G (x.subst s)

theorem mapInsert {s : Fin n → Term L m} {Γ G} (h : MapInto s Γ G) (a) :
    MapInto s (insert a Γ) (insert (a.subst s) G) := by
  rintro _ (rfl | hx)
  · exact Or.inl rfl
  · exact Or.inr (h hx)

theorem mapLift {s : Fin n → Term L m} {Γ G} (h : MapInto s Γ G) :
    MapInto (up s) (lifted Γ) (lifted G) :=
  fun _ ⟨a,ha,e⟩ => e ▸ ⟨a.subst s,h ha,(a.subst_lift s).symm⟩

theorem substitute (p : Derivation L k Γ Δ a) (s : Fin n → Term L m)
    {G D} (g : MapInto s Γ G) (d : MapInto s Δ D) : Derivation L k G D (a.subst s) := by
  induction p generalizing m with
  | extra h => exact h.elim
  | global h => exact .global (g h)
  | hyp h => exact .hyp (d h)
  | orE _ _ _ h u v => exact .orE (h s g d) (u s g (mapInsert d _)) (v s g (mapInsert d _))
  | impI _ h => exact .impI (h s g (mapInsert d _))
  | impE e _ _ h v => exact .impE e (h s g d) (v s g (fun _ h => h.elim))
  | allI _ h => exact .allI (h _ (mapLift g) (mapLift d))
  | exE _ _ h v => exact .exE (h s g d) (by simpa only [subst_lift] using v _ (mapLift g) (mapInsert (mapLift d) _))
  | allE t _ h => rw [subst_inst]; exact .allE _ (h s g d)
  | exI t _ h => exact .exI _ (by simpa only [subst_inst] using h s g d)
  | cd _ h => exact .cd (by simpa only [subst,subst_lift] using h s g d)
  | internalAll _ h => exact .internalAll (by simpa only [subst,subst_lift] using h s g d)
  | internalEx _ h => exact .internalEx (by simpa only [subst,subst_lift] using h s g d)
  | andL _ h => exact .andL (h s g d)
  | andR _ h => exact .andR (h s g d)
  | botE _ h => exact .botE (h s g d)
  | topI  => exact .topI
  | andI _ _ h i => exact .andI (h s g d) (i s g d)
  | orL _ h => exact .orL (h s g d)
  | orR _ h => exact .orR (h s g d)
  | trans _ _ h i => exact .trans (h s g d) (i s g d)
  | meet _ _ h i => exact .meet (h s g d) (i s g d)
  | join _ _ h i => exact .join (h s g d) (i s g d)

theorem lift (p : Derivation L k Γ Δ a) : Derivation L k (lifted Γ) (lifted Δ) a.lift :=
  p.substitute _ (fun _ h => ⟨_,h,rfl⟩) (fun _ h => ⟨_,h,rfl⟩)

def DepthLE : Depth → Depth → Prop
  | _, none => True
  | none, some _ => False
  | some j, some k => j ≤ k

private theorem below_mono {i j k} (ij : Below i j) (jk : DepthLE j k) : Below i k := by
  cases k <;> cases j <;> cases i <;> simp_all [Below,DepthLE] <;> omega

theorem raise (p : Derivation L k Γ Δ a) (le : DepthLE k j) : Derivation L j Γ Δ a := by
  induction p with
  | impE e _ v h _ => exact .impE (below_mono e le) (h le) v
  | extra h => exact h.elim
  | global h => exact .global h
  | hyp h => exact .hyp h
  | topI  => exact .topI
  | botE _ h => exact .botE (h le)
  | andI _ _ h i => exact .andI (h le) (i le)
  | andL _ h => exact .andL (h le)
  | andR _ h => exact .andR (h le)
  | orL _ h => exact .orL (h le)
  | orR _ h => exact .orR (h le)
  | orE _ _ _ h i j => exact .orE (h le) (i le) (j le)
  | impI _ h => exact .impI (h le)
  | trans _ _ h i => exact .trans (h le) (i le)
  | meet _ _ h i => exact .meet (h le) (i le)
  | join _ _ h i => exact .join (h le) (i le)
  | allI _ h => exact .allI (h le)
  | allE t _ h => exact .allE t (h le)
  | exI t _ h => exact .exI t (h le)
  | exE _ _ h i => exact .exE (h le) (i le)
  | cd _ h => exact .cd (h le)
  | internalAll _ h => exact .internalAll (h le)
  | internalEx _ h => exact .internalEx (h le)

theorem bounded (p : Derivation L k Γ Δ a) : ∃ N : Nat, ∀ m ≥ N, Derivation L (some m) Γ Δ a := by
  induction p with
  | extra h => exact h.elim
  | global h => exact ⟨0,fun _ _ => .global h⟩
  | hyp h => exact ⟨0,fun _ _ => .hyp h⟩
  | topI => exact ⟨0,fun _ _ => .topI⟩
  | impE _ _ _ h v =>
    obtain ⟨i,hi⟩ := h
    obtain ⟨j,hj⟩ := v
    exact ⟨max i (j+1),fun m hm => .impE (j := some j) (show j < m by omega) (hi m (by omega)) (hj j (by omega))⟩
  | botE _ h =>
    obtain ⟨i,hi⟩ := h
    exact ⟨i,fun m hm => .botE (hi m (by omega))⟩
  | andI _ _ h p =>
    obtain ⟨i,hi⟩ := h
    obtain ⟨j,hj⟩ := p
    exact ⟨max i j,fun m hm => .andI (hi m (by omega)) (hj m (by omega))⟩
  | andL _ h =>
    obtain ⟨i,hi⟩ := h
    exact ⟨i,fun m hm => .andL (hi m (by omega))⟩
  | andR _ h =>
    obtain ⟨i,hi⟩ := h
    exact ⟨i,fun m hm => .andR (hi m (by omega))⟩
  | orL _ h =>
    obtain ⟨i,hi⟩ := h
    exact ⟨i,fun m hm => .orL (hi m (by omega))⟩
  | orR _ h =>
    obtain ⟨i,hi⟩ := h
    exact ⟨i,fun m hm => .orR (hi m (by omega))⟩
  | orE _ _ _ h p q =>
    obtain ⟨i,hi⟩ := h
    obtain ⟨j,hj⟩ := p
    obtain ⟨r,hr⟩ := q
    exact ⟨max i (max j r),fun m hm => .orE (hi m (by omega)) (hj m (by omega)) (hr m (by omega))⟩
  | impI _ h =>
    obtain ⟨i,hi⟩ := h
    exact ⟨i,fun m hm => .impI (hi m (by omega))⟩
  | trans _ _ h p =>
    obtain ⟨i,hi⟩ := h
    obtain ⟨j,hj⟩ := p
    exact ⟨max i j,fun m hm => .trans (hi m (by omega)) (hj m (by omega))⟩
  | meet _ _ h p =>
    obtain ⟨i,hi⟩ := h
    obtain ⟨j,hj⟩ := p
    exact ⟨max i j,fun m hm => .meet (hi m (by omega)) (hj m (by omega))⟩
  | join _ _ h p =>
    obtain ⟨i,hi⟩ := h
    obtain ⟨j,hj⟩ := p
    exact ⟨max i j,fun m hm => .join (hi m (by omega)) (hj m (by omega))⟩
  | allI _ h =>
    obtain ⟨i,hi⟩ := h
    exact ⟨i,fun m hm => .allI (hi m (by omega))⟩
  | allE t _ h =>
    obtain ⟨i,hi⟩ := h
    exact ⟨i,fun m hm => .allE t (hi m (by omega))⟩
  | exI t _ h =>
    obtain ⟨i,hi⟩ := h
    exact ⟨i,fun m hm => .exI t (hi m (by omega))⟩
  | exE _ _ h p =>
    obtain ⟨i,hi⟩ := h
    obtain ⟨j,hj⟩ := p
    exact ⟨max i j,fun m hm => .exE (hi m (by omega)) (hj m (by omega))⟩
  | cd _ h =>
    obtain ⟨i,hi⟩ := h
    exact ⟨i,fun m hm => .cd (hi m (by omega))⟩
  | internalAll _ h =>
    obtain ⟨i,hi⟩ := h
    exact ⟨i,fun m hm => .internalAll (hi m (by omega))⟩
  | internalEx _ h =>
    obtain ⟨i,hi⟩ := h
    exact ⟨i,fun m hm => .internalEx (hi m (by omega))⟩

end Derivation

namespace Tree
export Derivation (add raise weaken lift substitute bounded)
end Tree
end BQL
