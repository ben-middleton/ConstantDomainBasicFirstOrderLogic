import BQL.Syntax

namespace BQL

structure Model (L : Language) where
  W : Type
  D : Type
  worlds : Nonempty W
  domain : Nonempty D
  acc : W → W → Prop
  trans : ∀ {w u z}, acc w u → acc u z → acc w z
  func : ∀ {n}, L.Func n → (Fin n → D) → D
  rel : ∀ {n}, L.Rel n → W → (Fin n → D) → Prop
  persist : ∀ {n} {r : L.Rel n} {w u ts}, acc w u → rel r w ts → rel r u ts

variable {L : Language} {V U : Nat}
namespace Model
variable (M : Model L)

def eval (ρ : Fin V → M.D) : Term L V → M.D
  | .var x => ρ x
  | .app f ts => M.func f (fun i => eval ρ (ts i))

def Forces : {V : Nat} → M.W → (Fin V → M.D) → Formula L V → Prop
  | _, _, _, .top => True
  | _, _, _, .bot => False
  | _, w, ρ, .atom r ts => M.rel r w (fun i => M.eval ρ (ts i))
  | _, w, ρ, .conj a b => Forces w ρ a ∧ Forces w ρ b
  | _, w, ρ, .disj a b => Forces w ρ a ∨ Forces w ρ b
  | _, w, ρ, .imp a b => ∀ u, M.acc w u → Forces u ρ a → Forces u ρ b
  | _, w, ρ, .all a => ∀ d, Forces w (extend ρ d) a
  | _, w, ρ, .ex a => ∃ d, Forces w (extend ρ d) a

theorem persistence {w u : M.W} (edge : M.acc w u) (ρ : Fin V → M.D)
    (a : Formula L V) : M.Forces w ρ a → M.Forces u ρ a := by
  induction a with
  | top | bot => exact id
  | atom => exact M.persist edge
  | conj _ _ ha hb => exact fun h => ⟨ha ρ h.1, hb ρ h.2⟩
  | disj _ _ ha hb => exact Or.imp (ha ρ) (hb ρ)
  | imp => exact fun h z e => h z (M.trans edge e)
  | all _ ih => exact fun h d => ih _ (h d)
  | ex _ ih => exact fun ⟨d,h⟩ => ⟨d,ih _ h⟩

theorem eval_bind (ρ : Fin U → M.D) (s : Fin V → Term L U) (t : Term L V) :
    M.eval ρ (t.bind s) = M.eval (fun x => M.eval ρ (s x)) t := by
  induction t with
  | var => rfl
  | app _ _ ih => exact congrArg (M.func _) (funext ih)

@[simp] theorem eval_lift (ρ : Fin V → M.D) (d : M.D) (t : Term L V) :
    M.eval (extend ρ d) t.lift = M.eval ρ t := M.eval_bind ..

theorem subst_assignment (ρ : Fin U → M.D) (s : Fin V → Term L U) (d : M.D) :
    (fun x => M.eval (extend ρ d) (up s x)) = extend (fun x => M.eval ρ (s x)) d := by
  funext x
  refine Fin.cases ?_ (fun i => ?_) x
  · rfl
  · exact M.eval_lift ..

theorem forces_subst (w : M.W) (ρ : Fin U → M.D) (s : Fin V → Term L U) (a : Formula L V) :
    M.Forces w ρ (a.subst s) ↔ M.Forces w (fun x => M.eval ρ (s x)) a := by
  induction a generalizing U w with
  | top | bot => rfl
  | atom => simp only [Formula.subst, Forces, eval_bind]
  | conj _ _ ha hb => exact and_congr (ha ..) (hb ..)
  | disj _ _ ha hb => exact or_congr (ha ..) (hb ..)
  | imp _ _ ha hb => simp only [Formula.subst, Forces, ha, hb]
  | all _ ih => simp only [Formula.subst, Forces, ih, subst_assignment]
  | ex _ ih => simp only [Formula.subst, Forces, ih, subst_assignment]

@[simp] theorem forces_lift (w : M.W) (ρ : Fin V → M.D) (d : M.D) (a : Formula L V) :
    M.Forces w (extend ρ d) a.lift ↔ M.Forces w ρ a := M.forces_subst ..

@[simp] theorem forces_inst (w : M.W) (ρ : Fin V → M.D) (a : Formula L (V+1)) (t : Term L V) :
    M.Forces w ρ (a.inst t) ↔ M.Forces w (extend ρ (M.eval ρ t)) a := by
  unfold Formula.inst
  rw [forces_subst]
  apply Iff.of_eq
  congr 1
  funext x
  exact Fin.cases rfl (fun _ => rfl) x

def Satisfies (w : M.W) (ρ : Fin V → M.D) (Γ : Theory L V) :=
  ∀ a, Γ a → M.Forces w ρ a

theorem sat_insert {w : M.W} {ρ : Fin V → M.D} {a : Formula L V} {Γ : Theory L V}
    (ha : M.Forces w ρ a) (hΓ : M.Satisfies w ρ Γ) : M.Satisfies w ρ (insert a Γ)
  | _, Or.inl rfl => ha
  | b, Or.inr h => hΓ b h

theorem sat_lifted {w : M.W} {ρ : Fin V → M.D} {Γ : Theory L V}
    (hΓ : M.Satisfies w ρ Γ) (d : M.D) : M.Satisfies w (extend ρ d) (lifted Γ)
  | _, ⟨a, ha, rfl⟩ => (M.forces_lift ..).2 (hΓ a ha)

theorem sat_persist {w u : M.W} {ρ : Fin V → M.D} {Γ : Theory L V}
    (edge : M.acc w u) (hΓ : M.Satisfies w ρ Γ) : M.Satisfies u ρ Γ :=
  fun a ha => M.persistence edge ρ a (hΓ a ha)
end Model

def Entails (Γ : Theory L V) (a : Formula L V) :=
  ∀ (M : Model L) w ρ, M.acc w w → M.Satisfies w ρ Γ → M.Forces w ρ a

def RelativeEntails (Γ Δ : Theory L V) (a : Formula L V) :=
  ∀ (M : Model L) w u ρ, M.acc w w → M.acc w u →
    M.Satisfies w ρ Γ → M.Satisfies u ρ Δ → M.Forces u ρ a

end BQL
