import BQL.Elimination

namespace BQL
open Formula

inductive Axiom {L : Language} : {n : Nat} → Formula L n → Type where
  | id : Axiom (imp a a)
  | top : Axiom (imp a Formula.top)
  | bot : Axiom (imp Formula.bot a)
  | meet : Axiom (imp (conj (imp x a) (imp x b)) (imp x (conj a b)))
  | left : Axiom (imp (conj a b) a)
  | right : Axiom (imp (conj a b) b)
  | inl : Axiom (imp a (disj a b))
  | inr : Axiom (imp b (disj a b))
  | join : Axiom (imp (conj (imp a x) (imp b x)) (imp (disj a b) x))
  | dist : Axiom (imp (conj x (disj a b)) (disj (conj x a) (conj x b)))
  | iAll : Axiom (imp (all (imp a.lift b)) (imp a (all b)))
  | allE (t) : Axiom (imp (all a) (a.inst t))
  | exI (t) : Axiom (imp (a.inst t) (ex a))
  | iEx : Axiom (imp (all (imp a b.lift)) (imp (ex a) b))
  | cd : Axiom (imp (all (disj a.lift b)) (disj a (all b)))
  | iDist : Axiom (imp (conj x (ex a)) (ex (conj x.lift a)))
  | trans : Axiom (imp (conj (imp a b) (imp b c)) (imp a c))
  | prefixing : Axiom (imp (imp a b) (imp (imp c a) (imp c b)))
  | suffixing : Axiom (imp (imp a b) (imp (imp b c) (imp a c)))
  | weakening : Axiom (imp a (imp b a))

inductive Level where
  | basic | dj | tj | tjk
  deriving DecidableEq

/-- The base system, then transitivity, prefixing/suffixing, and weakening. -/
def Axiom.Enabled {a : Formula L n} (level : Level) (ax : Axiom a) : Prop :=
  match ax with
  | .trans => level ≠ .basic
  | .prefixing | .suffixing => level = .tj ∨ level = .tjk
  | .weakening => level = .tjk
  | _ => True

def Scheme (level : Level) (a : Formula L n) : Type :=
  match level with
  | .tjk => Axiom a
  | l => {ax : Axiom a // ax.Enabled l}

/-- Original calculus of §2. The flag enables the external existential elimination. -/
inductive Relevant (L : Language) (level : Level) (withEx : Bool) : {n : Nat} → Theory L n → Formula L n → Prop where
  | hyp : Γ a → Relevant L level withEx Γ a
  | ax : Scheme level a → Relevant L level withEx Γ a
  | topI : Relevant L level withEx Γ top
  | botE : Relevant L level withEx Γ bot → Relevant L level withEx Γ a
  | andI : Relevant L level withEx Γ a → Relevant L level withEx Γ b → Relevant L level withEx Γ (conj a b)
  | andL : Relevant L level withEx Γ (conj a b) → Relevant L level withEx Γ a
  | andR : Relevant L level withEx Γ (conj a b) → Relevant L level withEx Γ b
  | orL : Relevant L level withEx Γ a → Relevant L level withEx Γ (disj a b)
  | orR : Relevant L level withEx Γ b → Relevant L level withEx Γ (disj a b)
  | orE : Relevant L level withEx Γ (disj a b) → Relevant L level withEx (insert a Γ) c → Relevant L level withEx (insert b Γ) c → Relevant L level withEx Γ c
  | mp : Relevant L level withEx Γ a → Relevant L level withEx Γ (imp a b) → Relevant L level withEx Γ b
  | rule : Relevant L level withEx Γ (imp a b) → Relevant L level withEx Γ (imp c d) → Relevant L level withEx Γ (imp (imp b c) (imp a d))
  | allI : Relevant L level withEx (lifted Γ) a → Relevant L level withEx Γ (all a)
  | allE (t) : Relevant L level withEx Γ (all a) → Relevant L level withEx Γ (a.inst t)
  | exI (t) : Relevant L level withEx Γ (a.inst t) → Relevant L level withEx Γ (ex a)
  | exE : withEx = true → Relevant L level withEx Γ (ex a) → Relevant L level withEx (insert a (lifted Γ)) b.lift → Relevant L level withEx Γ b
  | cd : Relevant L level withEx Γ (all (disj a.lift b)) → Relevant L level withEx Γ (disj a (all b))

abbrev TJK (L : Language) (withEx : Bool) {n} (Γ : Theory L n) (a : Formula L n) :=
  Relevant L .tjk withEx Γ a

namespace TJK
export Relevant (hyp ax topI botE andI andL andR orL orR orE mp rule allI allE exI exE cd)
end TJK

variable {L : Language} {a b c x : Formula L n} {Γ Δ : Theory L n}

theorem Axiom.basic (h : Axiom a) : Derivation L k Γ Δ a := by
  open Derivation in
    cases h with
    | id => exact identity
    | top => exact constant topI
    | bot => exact impI (botE here)
    | meet => exact impI (.meet (andL here) (andR here))
    | left => exact impI (andL here)
    | right => exact impI (andR here)
    | inl => exact impI (orL here)
    | inr => exact impI (orR here)
    | join => exact impI (.join (andL here) (andR here))
    | dist => exact distribution
    | iAll => exact impI (internalAll here)
    | allE t => exact impI (.allE t here)
    | exI t => exact impI (.exI t here)
    | iEx => exact impI (internalEx here)
    | cd => exact impI (.cd here)
    | iDist => exact infiniteDistribution
    | trans => exact impI (.trans (andL here) (andR here))
    | prefixing => exact impI (impI (.trans here (here.add _)))
    | suffixing => exact impI (impI (.trans (here.add _) here))
    | weakening => exact impI (constant here)

theorem TJK.toRoot (p : TJK L e Γ a) : Proves Γ a := by
  induction p with
  | hyp h => exact .global h
  | ax h => exact h.basic
  | topI => exact .topI
  | botE _ h => exact .botE h
  | andI _ _ h v => exact .andI h v
  | andL _ h => exact .andL h
  | andR _ h => exact .andR h
  | orL _ h => exact .orL h
  | orR _ h => exact .orR h
  | orE _ _ _ h u v => exact unrestrictedOr h u v
  | mp _ _ h v => exact .impE (j := none) trivial h v
  | rule _ _ h v => exact .impI (.trans (.trans (h.add _) Derivation.here) (v.add _))
  | allI _ h => exact .allI (h.weaken (fun _ => id) (fun _ h => h.elim))
  | allE t _ h => exact .allE t h
  | exI t _ h => exact .exI t h
  | exE _ _ _ h v => exact unrestrictedEx h v
  | cd _ h => exact .cd h

def Axiom.substitute (h : Axiom a) (s : Fin n → Term L m) : Axiom (a.subst s) := by
  cases h <;> simp only [subst,subst_lift,subst_inst] <;> first
    | exact .id | exact .top | exact .bot | exact .meet | exact .left | exact .right | exact .inl
    | exact .inr | exact .join | exact .dist | exact .iAll | exact .allE _ | exact .exI _
    | exact .iEx | exact .cd | exact .iDist | exact .trans | exact .prefixing | exact .suffixing | exact .weakening

namespace TJK
theorem substitute (p : TJK L e Γ a) (s : Fin n → Term L m) {G} (g : Derivation.MapInto s Γ G) :
    TJK L e G (a.subst s) := by
  induction p generalizing m with
  | hyp h => exact .hyp (g h)
  | ax h => exact .ax (h.substitute s)
  | topI => exact .topI
  | botE _ h => exact .botE (h s g)
  | andI _ _ h v => exact .andI (h s g) (v s g)
  | andL _ h => exact .andL (h s g)
  | andR _ h => exact .andR (h s g)
  | orL _ h => exact .orL (h s g)
  | orR _ h => exact .orR (h s g)
  | orE _ _ _ h u v => exact .orE (h s g) (u s (Derivation.mapInsert g _)) (v s (Derivation.mapInsert g _))
  | mp _ _ h v => exact .mp (h s g) (v s g)
  | rule _ _ h v => exact .rule (h s g) (v s g)
  | allI _ h => exact .allI (h _ (Derivation.mapLift g))
  | allE t _ h => rw [subst_inst]; exact .allE _ (h s g)
  | exI t _ h => exact .exI _ (by simpa only [subst_inst] using h s g)
  | exE en _ _ h v =>
    exact .exE en (h s g) (by simpa only [subst_lift] using v _ (Derivation.mapInsert (Derivation.mapLift g) _))
  | cd _ h => exact .cd (by simpa only [subst,subst_lift] using h s g)

theorem lift (p : TJK L e Γ a) : TJK L e (lifted Γ) a.lift := p.substitute _ (fun _ h => ⟨_,h,rfl⟩)

theorem trans (p : TJK L e Γ (imp a b)) (q : TJK L e Γ (imp b c)) : TJK L e Γ (imp a c) :=
  .mp (.andI p q) (.ax .trans)

theorem meet (p : TJK L e Γ (imp x a)) (q : TJK L e Γ (imp x b)) : TJK L e Γ (imp x (conj a b)) :=
  .mp (.andI p q) (.ax .meet)

theorem constant (p : TJK L e Γ a) : TJK L e Γ (imp x a) := .mp p (.ax .weakening)

theorem release (p : TJK L e Γ (imp (conj x a) b)) : TJK L e Γ (imp x (imp a b)) :=
  trans (trans (meet (.ax .weakening) (constant (.ax .id))) (.ax .meet)) (.mp p (.ax .prefixing))

private def Guards (e) (G Δ : Theory L n) (x : Formula L n) := ∀ ⦃d⦄, Δ d → TJK L e G (imp x d)
private theorem extendG (g : Guards e G Δ x) (a : Formula L n) :
    Guards e G (insert a Δ) (conj x a) := by
  rintro _ (rfl | h)
  · exact .ax .right
  · exact trans (.ax .left) (g h)
private theorem liftG (g : Guards e G Δ x) : Guards e (lifted G) (lifted Δ) x.lift :=
  fun _ ⟨_,h,eq⟩ => eq ▸ (g h).lift

theorem internalize (p : Derivation L k Γ Δ a) (base : k = some 0) (x : Formula L n)
    {G} (g : Guards e G Γ x) (d : Guards e G Δ x) : TJK L e G (imp x a) := by
  induction p with
  | extra h => exact h.elim
  | global h => exact g h
  | hyp h => exact d h
  | topI => exact .ax .top
  | botE _ h => exact trans (h base x g d) (.ax .bot)
  | andI _ _ h v => exact meet (h base x g d) (v base x g d)
  | andL _ h => exact trans (h base x g d) (.ax .left)
  | andR _ h => exact trans (h base x g d) (.ax .right)
  | orL _ h => exact trans (h base x g d) (.ax .inl)
  | orR _ h => exact trans (h base x g d) (.ax .inr)
  | impE ed => exact (Derivation.noBelowZero _ (base ▸ ed)).elim
  | impI _ h => exact release (h base _ (fun _ hg => trans (.ax .left) (g hg)) (extendG d _))
  | orE _ _ _ h u v =>
    exact trans (trans (meet (.ax .id) (h base x g d)) (.ax .dist)) (.mp
      (.andI (u base _ (fun _ hg => trans (.ax .left) (g hg)) (extendG d _))
        (v base _ (fun _ hg => trans (.ax .left) (g hg)) (extendG d _))) (.ax .join))
  | trans _ _ h v => exact trans (meet (h base x g d) (v base x g d)) (.ax .trans)
  | meet _ _ h v => exact trans (meet (h base x g d) (v base x g d)) (.ax .meet)
  | join _ _ h v => exact trans (meet (h base x g d) (v base x g d)) (.ax .join)
  | allI _ h => exact .mp (.allI (h base _ (liftG g) (liftG d))) (.ax .iAll)
  | allE t _ h => exact trans (h base x g d) (.ax (.allE t))
  | exI t _ h => exact trans (h base x g d) (.ax (.exI t))
  | exE _ _ h v =>
    exact trans (trans (meet (.ax .id) (h base x g d)) (.ax .iDist))
      (.mp (.allI (v base _ (fun _ hg => trans (.ax .left) (liftG g hg)) (extendG (liftG d) _))) (.ax .iEx))
  | cd _ h => exact trans (h base x g d) (.ax .cd)
  | internalAll _ h => exact trans (h base x g d) (.ax .iAll)
  | internalEx _ h => exact trans (h base x g d) (.ax .iEx)

theorem ofRoot (p : Proves Γ a) : TJK L e Γ a := by
  obtain ⟨k,h⟩ := reduction p
  have proof : TJK L e Γ (a.boxes k) := .mp .topI
    (internalize h rfl top (fun _ ha => constant (.hyp ha)) (fun _ h => h.elim))
  clear h
  induction k with
  | zero => exact proof
  | succ k ih => exact ih (.mp .topI proof)

end TJK

theorem equivalentTJK : Proves Γ a ↔ TJK L true Γ a := ⟨TJK.ofRoot,TJK.toRoot⟩
theorem redundantExistentialElim : TJK L true Γ a ↔ TJK L false Γ a :=
  ⟨fun h => TJK.ofRoot h.toRoot,fun h => TJK.ofRoot h.toRoot⟩

theorem TJK.weaken {Γ G : Theory L n} {a} (p : TJK L e Γ a) (h : Incl Γ G) : TJK L e G a := by
  simpa only [subst_var] using p.substitute Term.var (G := G) (fun a ha => a.subst_var.symm ▸ h ha)

namespace TJK
private def Supply (e) (G Γ : Theory L n) := ∀ ⦃a⦄, Γ a → TJK L e G a
private theorem more {G Γ : Theory L n} (h : Supply e G Γ) (a : Formula L n) : Supply e (insert a G) (insert a Γ) :=
  fun _ hx => hx.elim (fun e => e ▸ TJK.hyp (Or.inl rfl)) (fun hg => (h hg).weaken (fun _ => Or.inr))
private theorem fresh (h : Supply e G Γ) : Supply e (lifted G) (lifted Γ) :=
  fun _ ⟨_,hx,e⟩ => e ▸ (h hx).lift

theorem cut {Γ G : Theory L n} {a} (p : TJK L e Γ a) (d : Supply e G Γ) : TJK L e G a := by
  induction p with
  | hyp h => exact d h
  | ax h => exact .ax h
  | topI => exact .topI
  | botE _ h => exact .botE (h d)
  | andI _ _ h v => exact .andI (h d) (v d)
  | andL _ h => exact .andL (h d)
  | andR _ h => exact .andR (h d)
  | orL _ h => exact .orL (h d)
  | orR _ h => exact .orR (h d)
  | orE _ _ _ h u v => exact .orE (h d) (u (more d _)) (v (more d _))
  | mp _ _ h v => exact .mp (h d) (v d)
  | rule _ _ h v => exact .rule (h d) (v d)
  | allI _ h => exact .allI (h (fresh d))
  | allE t _ h => exact .allE t (h d)
  | exI t _ h => exact .exI t (h d)
  | exE en _ _ h v => exact .exE en (h d) (v (more (fresh d) _))
  | cd _ h => exact .cd (h d)
end TJK

end BQL
