import BQL.Completeness

namespace BQL

def parameters (L : Language) : Language where
  Func
    | 0 => L.Func 0 ⊕ Nat
    | n+1 => L.Func (n+1)
  Rel := L.Rel

def inclusion (L : Language) : Relabel L (parameters L) where
  func := fun {k} => match k with
    | 0 => Sum.inl
    | _+1 => id
  rel := id

variable {L : Language}

def image (F : Relabel L K) (Γ : Theory L n) : Theory K n := fun b => ∃ a, Γ a ∧ F.form a = b

/-- Consequence over the base language uses proofs in the parameter language.
This supplies closed eigenparameters even for a signature without constants. -/
def Derivable (Γ : Theory L 0) (a : Sentence L) :=
  Proves (image (inclusion L) Γ) ((inclusion L).form a)

theorem completeness {Γ : Theory L 0} {a} (h : Entails Γ a) : Derivable Γ a := by
  let F := inclusion L
  apply completeWithConstant (L := parameters L) ⟨Sum.inr 0⟩
  intro M w ρ r g
  apply (F.forces M w ρ a).1
  exact h (F.reduct M) w ρ r (fun b hb => (F.forces M w ρ b).2 (g _ ⟨b,hb,rfl⟩))

def Model.expand (M : Model L) (d : M.D) : Model (parameters L) where
  W := M.W
  D := M.D
  worlds := M.worlds
  domain := M.domain
  acc := M.acc
  trans := M.trans
  func := fun {k} f => match k, f with
    | 0, Sum.inl c => M.func c
    | 0, Sum.inr _ => fun _ => d
    | _+1, f => M.func f
  rel := M.rel
  persist := M.persist

theorem Model.reduct_expand (M : Model L) (d : M.D) : (inclusion L).reduct (M.expand d) = M := by
  cases M
  simp only [inclusion,Relabel.reduct,Model.expand]
  congr 1
  funext k f
  cases k <;> rfl

theorem adequate {Γ : Theory L 0} {a} : Derivable Γ a ↔ Entails Γ a := by
  refine ⟨fun p M => ?_,completeness⟩
  let d := Classical.choice M.domain
  let N := M.expand d
  rw [← M.reduct_expand d]
  intro w ρ r g
  apply ((inclusion L).forces N w ρ a).2
  exact soundness p N w ρ r (fun _ ⟨b,hb,e⟩ => e ▸ ((inclusion L).forces N w ρ b).1 (g b hb))

end BQL
