import BQL.IdentityRules

/-! The rule presentation of §7. Equality elimination is substitution of one
equal term for another in an arbitrary formula, including under quantifiers. -/
namespace BQL.Identity
open Formula
variable {L : Language} {E : L.Rel 2}

inductive Rule (E : L.Rel 2) (d : Bool) : ExtraRules L where
  | intro (t : Term L n) : Rule E d [] (eqF E t t)
  | elim (a : Formula L (n+1)) (s t : Term L n) : Rule E d [eqF E s t,a.inst s] (a.inst t)
  | em (s t : Term L n) : d = true → Rule E d [] (disj (eqF E s t) (imp (eqF E s t) bot))

abbrev ND (E : L.Rel 2) (d : Bool) (Γ : Theory L n) (a : Formula L n) :=
  Tree L (Rule E d) none Γ empty a
private abbrev P {d : Bool} {n} (k : Depth) (Γ Δ : Theory L n) (a : Formula L n) := Tree L (Rule E d) k Γ Δ a

private theorem reflT (t : Term L n) : P (E := E) (d := d) k Γ Δ (eqF E t t) :=
  .extra (.intro t) (by simp)
private theorem elimT {s t : Term L n} (a : Formula L (n+1))
    (e : P (E := E) (d := d) k Γ Δ (eqF E s t)) (h : P (E := E) (d := d) k Γ Δ (a.inst s)) :
    P (E := E) (d := d) k Γ Δ (a.inst t) :=
  .extra (.elim a s t) (List.forall_mem_cons.mpr ⟨e,List.forall_mem_cons.mpr ⟨h,by simp⟩⟩)

private theorem ruleSound (M : Model L) (cg : ∀ w, Congruent E M w) (dg : d = true → Diagonal E M)
    {ps : List (Formula L n)} {a} (r : Rule E d ps a) (w) (ρ) (hs : ∀ b ∈ ps, M.Forces w ρ b) : M.Forces w ρ a := by
  cases r with
  | intro t => exact (forces_eq ..).2 ((cg w).equiv.refl (M.eval ρ t))
  | elim a s t =>
    have e := (forces_eq ..).1 (hs _ (.head _))
    have h := (M.forces_inst ..).1 (hs _ (.tail _ (.head _)))
    exact (M.forces_inst ..).2 ((forcing_congr M cg w (ρ := extend ρ (M.eval ρ s)) (σ := extend ρ (M.eval ρ t))
      (Fin.cases e (fun i => (cg w).equiv.refl (ρ i))) a).1 h)
  | em s t hd =>
    by_cases e : M.eval ρ s = M.eval ρ t
    · exact Or.inl ((forces_eq ..).2 ((dg hd ..).2 e))
    · exact Or.inr (fun u _ h => e ((dg hd ..).1 ((forces_eq ..).1 h)))

private theorem subst_eqF (s t : Term L n) (σ : Fin n → Term L m) :
    (eqF E s t).subst σ = eqF E (s.bind σ) (t.bind σ) := congrArg (atom E) (map_two ..)

private theorem drop (t : Term L n) (v : Term L n) : t.lift.bind (extend Term.var v) = t := by
  rw [Term.lift,Term.bind_comp]; exact t.bind_var

private theorem symmetry {s t : Term L n} (h : P (E := E) (d := d) k Γ Δ (eqF E s t)) :
    P (E := E) (d := d) k Γ Δ (eqF E t s) := by
  let a := eqF E (.var 0) s.lift
  have aux (v : Term L n) : a.inst v = eqF E v s := by simp only [a,inst,subst_eqF,drop]; rfl
  exact aux t ▸ elimT a h ((aux s).symm ▸ reflT s)

private theorem transitivity {s t u : Term L n} (h : P (E := E) (d := d) k Γ Δ (eqF E s t))
    (q : P (E := E) (d := d) k Γ Δ (eqF E t u)) : P (E := E) (d := d) k Γ Δ (eqF E s u) := by
  let a := eqF E s.lift (.var 0)
  have aux (v : Term L n) : a.inst v = eqF E s v := by simp only [a,inst,subst_eqF,drop]; rfl
  exact aux u ▸ elimT a q ((aux t).symm ▸ h)

private def hole (ts : Fin k → Term L n) (i j : Fin k) : Term L (n+1) :=
  if j = i then .var 0 else (ts j).lift

private def replace (ts : Fin k → Term L n) (i : Fin k) (v : Term L n) :=
  fun j => if j = i then v else ts j

private theorem fill (ts : Fin k → Term L n) (i) (v : Term L n) :
    (fun j => (hole ts i j).bind (extend Term.var v)) = replace ts i v := by
  funext j
  by_cases e : j = i
  · subst j; simp [hole,replace,Term.bind,extend]
  · simp [hole,replace,e,drop]

/-- Walk across a finite tuple, one coordinate at a time. -/
private theorem tupleTransport (xs ys : Fin k → Term L n) (H : (Fin k → Term L n) → Prop)
    (start : H xs) (step : ∀ ts i, ts i = xs i → H ts → H (replace ts i (ys i))) : H ys := by
  let mix := fun (m : Nat) (j : Fin k) => if j.val < m then ys j else xs j
  have walk (m) (hm : m ≤ k) : H (mix m) := by
    induction m with
    | zero => simpa only [mix,Nat.not_lt_zero,if_false] using start
    | succ m ih =>
      let i : Fin k := ⟨m,hm⟩
      have e : replace (mix m) i (ys i) = mix (m+1) := by
        funext j
        by_cases eq : j = i
        · subst j; simp [replace,mix,i]
        · have ne : j.val ≠ m := fun h => eq (Fin.ext h)
          have iff : j.val < m+1 ↔ j.val < m := by omega
          simp [replace,mix,eq,iff]
      exact e ▸ step (mix m) i (by simp [mix,i]) (ih (by omega))
  simpa only [mix,Fin.isLt,if_true] using walk k (Nat.le_refl _)

private theorem functions (f : L.Func j) (xs ys : Fin j → Term L n)
    (e : ∀ i, P (E := E) (d := d) k Γ Δ (eqF E (xs i) (ys i))) :
    P (E := E) (d := d) k Γ Δ (eqF E (.app f xs) (.app f ys)) := by
  apply tupleTransport xs ys (fun ts => P _ Γ Δ (eqF E (.app f xs) (.app f ts))) (reflT _)
  intro ts i hi h
  let a := eqF E (Term.app f xs).lift (.app f (hole ts i))
  have inst' (v : Term L n) : a.inst v = eqF E (.app f xs) (.app f (replace ts i v)) := by
    simp only [a,inst,subst_eqF,drop,Term.bind,fill]
  have self : replace ts i (xs i) = ts := by
    funext j; by_cases eq : j = i <;> simp [replace,eq,hi]
  exact inst' _ ▸ elimT a (e i) ((inst' _).symm ▸ (self.symm ▸ h))

private theorem relations (r : L.Rel j) (xs ys : Fin j → Term L n)
    (e : ∀ i, P (E := E) (d := d) k Γ Δ (eqF E (xs i) (ys i))) (start : P (E := E) (d := d) k Γ Δ (atom r xs)) :
    P (E := E) (d := d) k Γ Δ (atom r ys) := by
  apply tupleTransport xs ys (fun ts => P (E := E) (d := d) k Γ Δ (atom r ts)) start
  intro ts i hi h
  let a := atom r (hole ts i)
  have inst' (v : Term L n) : a.inst v = atom r (replace ts i v) := congrArg (atom r) (fill ..)
  have self : replace ts i (xs i) = ts := by
    funext j; by_cases eq : j = i <;> simp [replace,eq,hi]
  exact inst' _ ▸ elimT a (e i) ((inst' _).symm ▸ (self.symm ▸ h))

private def Logical (E : L.Rel 2) (d : Bool) (a : Formula L n) :=
  ∀ {m} (σ : Fin n → Term L m) {k} {G D}, Tree L (Rule E d) k G D (a.subst σ)

private theorem logicalLift {a : Formula L n} (h : Logical E d a) : Logical E d a.lift := by
  intro m σ k G D
  rw [lift,subst_comp]
  exact h _

private theorem logicalClose {a : Formula L n} (h : Logical E d a) : Logical E d (close a) := by
  induction n with
  | zero => exact h
  | succ n ih =>
    apply ih (a := all a)
    intro m σ k G D
    exact .allI (h (up σ))

private theorem members {as : Fin j → Formula L n} {σ : Fin n → Term L m}
    (h : Tree L (Rule E d) k Γ Δ ((meetAll as).subst σ)) :
    ∀ i, Tree L (Rule E d) k Γ Δ ((as i).subst σ) := by
  induction j with
  | zero => exact fun i => i.elim0
  | succ j ih => exact Fin.cases (.andL h) (ih (.andR h))

private theorem lawsLogical {a : Sentence L} (law : Laws E d a) : Logical E d a := by
  cases law <;> apply logicalClose <;> intro m σ k G D
  case refl => rw [subst_eqF]; exact reflT _
  case symm => simp only [subst,subst_eqF]; exact .impI (symmetry (.hyp (Or.inl rfl)))
  case trans => simp only [subst,subst_eqF]; exact .impI (transitivity (.andL (.hyp (Or.inl rfl))) (.andR (.hyp (Or.inl rfl))))
  case func f =>
    apply Tree.impI
    rw [subst_eqF]
    apply functions
    intro i
    exact subst_eqF .. ▸ members (as := fun j => eqF E (leftVar j) (rightVar j))
      (σ := σ) (Tree.hyp (Or.inl rfl)) i
  case rel r =>
    apply Tree.impI
    apply relations r _ _ _ (.andR (.hyp (Or.inl rfl)))
    intro i
    exact subst_eqF .. ▸ members (as := fun j => eqF E (leftVar j) (rightVar j))
      (σ := σ) (Tree.andL (.hyp (Or.inl rfl))) i
  case em en =>
    simp only [subst,subst_eqF]
    exact .extra (.em _ _ en) (by simp)

private theorem fromLaws {Γ Δ : Theory L n} {a} (p : Derivation L k Γ Δ a) {G D}
    (g : ∀ b, Γ b → G b ∨ Logical E d b) (inc : Incl Δ D) : Tree L (Rule E d) k G D a := by
  have liftedG {n} {Γ G : Theory L n} (g : ∀ b, Γ b → G b ∨ Logical E d b) :
      ∀ b, lifted Γ b → lifted G b ∨ Logical E d b := by
    rintro _ ⟨b,hb,rfl⟩
    exact (g b hb).imp (fun h => ⟨b,h,rfl⟩) logicalLift
  induction p with
  | extra h => exact h.elim
  | global h =>
    rcases g _ h with h | law
    · exact .global h
    · simpa only [subst_var] using law Term.var (k := _) (G := G) (D := D)
  | hyp h => exact .hyp (inc h)
  | topI => exact .topI
  | botE _ h => exact .botE (h g inc)
  | andI _ _ h v => exact .andI (h g inc) (v g inc)
  | andL _ h => exact .andL (h g inc)
  | andR _ h => exact .andR (h g inc)
  | orL _ h => exact .orL (h g inc)
  | orR _ h => exact .orR (h g inc)
  | orE _ _ _ h u v => exact .orE (h g inc) (u g (incl_insert inc _)) (v g (incl_insert inc _))
  | impI _ h => exact .impI (h g (incl_insert inc _))
  | impE e _ _ h v => exact .impE e (h g inc) (v g (fun _ => id))
  | trans _ _ h v => exact .trans (h g inc) (v g inc)
  | meet _ _ h v => exact .meet (h g inc) (v g inc)
  | join _ _ h v => exact .join (h g inc) (v g inc)
  | allI _ h => exact .allI (h (liftedG g) (incl_lifted inc))
  | allE t _ h => exact .allE t (h g inc)
  | exI t _ h => exact .exI t (h g inc)
  | exE _ _ h v => exact .exE (h g inc) (v (liftedG g) (incl_insert (incl_lifted inc) _))
  | internalAll _ h => exact .internalAll (h g inc)
  | internalEx _ h => exact .internalEx (h g inc)
  | cd _ h => exact .cd (h g inc)

theorem ruleAdequacy (hc : Nonempty (L.Func 0)) (d : Bool) (Γ : Theory L 0) (a : Sentence L) :
    ND E d Γ a ↔ restricted E d Γ a := by
  refine ⟨fun p M cg dg w η r h => p.soundAt M (ruleSound M cg dg) w w η r r h (fun _ h => h.elim),fun h => ?_⟩
  have p := completeWithConstant hc (adequate.mp ((adequateEquality ..).2 h))
  exact fromLaws p (fun _ hb => hb.imp_right lawsLogical) (fun _ => id)

/-- Equality-rule completeness in the parameter language of an arbitrary base signature. -/
theorem adequateRules (d : Bool) (Γ : Theory L 0) (a : Sentence L) :
    ND ((inclusion L).rel E) d (image (inclusion L) Γ) ((inclusion L).form a) ↔ restricted E d Γ a := by
  let F := inclusion L
  rw [ruleAdequacy (L := parameters L) ⟨Sum.inr 0⟩]
  constructor
  · intro h M cg dg w η loop g
    let value := Classical.choice M.domain
    let N := M.expand value
    have exCg (u : N.W) : Congruent (F.rel E) N u := by
      refine ⟨(cg u).equiv,?_,(cg u).rel⟩
      intro k f xs ys eq
      cases k with
      | zero =>
        cases f with
        | inl c => exact (cg u).func c xs ys eq
        | inr _ => exact (cg u).equiv.refl value
      | succ _ => exact (cg u).func f xs ys eq
    have transfer : ∀ u ρ, M.acc u u → M.Satisfies u ρ Γ → M.Forces u ρ a := by
      rw [← M.reduct_expand value]
      intro u ρ r hg
      exact (F.forces N u ρ a).2 (h N exCg dg u ρ r
        (fun _ ⟨b,hb,e⟩ => e ▸ (F.forces N u ρ b).1 (hg b hb)))
    exact transfer w η loop g
  · intro Nvalid N cg dg w η loop hg
    have redCg (u : N.W) : Congruent E (F.reduct N) u :=
      ⟨(cg u).equiv,fun f => (cg u).func (F.func f),fun r => (cg u).rel (F.rel r)⟩
    apply (F.forces N w η a).1
    exact Nvalid (F.reduct N) redCg dg w η loop (fun b hb => (F.forces N w η b).2 (hg _ ⟨b,hb,rfl⟩))

end BQL.Identity
