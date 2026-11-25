import BQL.Structural

namespace BQL
namespace FiniteSupport

/-- A finite list suffices, and every enlargement also suffices. -/
private def Eventually (P : List α → Prop) :=
  ∃ xs : List α, ∀ ys : List α, (∀ x ∈ xs, x ∈ ys) → P ys

private theorem always {P : List α → Prop} (h : ∀ xs, P xs) : Eventually P :=
  ⟨[],fun ys _ => h ys⟩
private theorem map {P Q : List α → Prop} (p : Eventually P) (f : ∀ s, P s → Q s) : Eventually Q :=
  p.imp (fun _ h ys inc => f ys (h ys inc))
private theorem both {P Q R : List α → Prop} (p : Eventually P) (q : Eventually Q)
    (f : ∀ s, P s → Q s → R s) : Eventually R := by
  obtain ⟨xs,hx⟩ := p
  obtain ⟨ys,hy⟩ := q
  exact ⟨xs++ys,fun s inc => f s (hx s (fun x h => inc x (List.mem_append_left _ h)))
    (hy s (fun y h => inc y (List.mem_append_right _ h)))⟩
private theorem three {P Q R S : List α → Prop} (p : Eventually P) (q : Eventually Q)
    (r : Eventually R) (f : ∀ s, P s → Q s → R s → S s) : Eventually S :=
  both (both p q (fun _ a b => And.intro a b)) r (fun s h c => f s h.1 h.2 c)

private def Covered (Γ : Theory L n) (G : List α → Theory L n) :=
  ∀ ⦃a⦄, Γ a → Eventually (fun s => G s a)
private theorem liftCover {Γ : Theory L n} {G : List α → Theory L n} (h : Covered Γ G) :
    Covered (lifted Γ) (fun s => lifted (G s)) :=
  fun _ ⟨a,ha,e⟩ => map (h ha) (fun _ h => ⟨a,h,e⟩)
private theorem insertCover {Γ : Theory L n} {G : List α → Theory L n} (h : Covered Γ G) (a) :
    Covered (insert a Γ) (fun s => insert a (G s)) :=
  fun _ hx => hx.elim (fun e => always (fun _ => Or.inl e)) (fun hg => map (h hg) (fun _ => Or.inr))

private theorem continuity {Γ Δ : Theory L n} {G D : List α → Theory L n} {a}
    (p : Derivation L k Γ Δ a) (g : Covered Γ G) (d : Covered Δ D) :
    Eventually (fun s => Derivation L k (G s) (D s) a) := by
  induction p with
  | extra h => exact h.elim
  | global h => exact map (g h) (fun _ => Derivation.global)
  | hyp h => exact map (d h) (fun _ => Derivation.hyp)
  | topI => exact always (fun _ => .topI)
  | botE _ h => exact map (h g d) (fun _ => Derivation.botE)
  | andI _ _ h v => exact both (h g d) (v g d) (fun _ => Derivation.andI)
  | andL _ h => exact map (h g d) (fun _ => Derivation.andL)
  | andR _ h => exact map (h g d) (fun _ => Derivation.andR)
  | orL _ h => exact map (h g d) (fun _ => Derivation.orL)
  | orR _ h => exact map (h g d) (fun _ => Derivation.orR)
  | orE _ _ _ h u v => exact three (h g d) (u g (insertCover d _)) (v g (insertCover d _)) (fun _ => Derivation.orE)
  | impI _ h => exact map (h g (insertCover d _)) (fun _ => Derivation.impI)
  | impE e _ _ h v => exact both (h g d) (v g (D := fun _ => empty) (fun _ h => h.elim)) (fun _ => Derivation.impE e)
  | trans _ _ h v => exact both (h g d) (v g d) (fun _ => Derivation.trans)
  | meet _ _ h v => exact both (h g d) (v g d) (fun _ => Derivation.meet)
  | join _ _ h v => exact both (h g d) (v g d) (fun _ => Derivation.join)
  | allI _ h => exact map (h (liftCover g) (liftCover d)) (fun _ => Derivation.allI)
  | allE t _ h => exact map (h g d) (fun _ => Derivation.allE t)
  | exI t _ h => exact map (h g d) (fun _ => Derivation.exI t)
  | exE _ _ h v => exact both (h g d) (v (liftCover g) (insertCover (liftCover d) _)) (fun _ => Derivation.exE)
  | internalAll _ h => exact map (h g d) (fun _ => Derivation.internalAll)
  | internalEx _ h => exact map (h g d) (fun _ => Derivation.internalEx)
  | cd _ h => exact map (h g d) (fun _ => Derivation.cd)

theorem finitePremises {Γ : Theory L n} {a} (p : Derivation L k Γ empty a) :
    ∃ xs : List (Formula L n), (∀ b ∈ xs, Γ b) ∧ Derivation L k (fun b => b ∈ xs) empty a := by
  let G := fun (s : List {b // Γ b}) (a : Formula L n) => a ∈ s.map Subtype.val
  have g : Covered Γ G := fun b hb => ⟨[⟨b,hb⟩],fun _ inc => List.mem_map.mpr ⟨_,inc _ (.head _),rfl⟩⟩
  obtain ⟨s,hs⟩ := continuity p g (D := fun _ => empty) (fun _ h => h.elim)
  refine ⟨s.map Subtype.val,?_,hs s (fun _ => id)⟩
  intro b hb
  obtain ⟨x,_,rfl⟩ := List.mem_map.mp hb
  exact x.property

end FiniteSupport
end BQL
