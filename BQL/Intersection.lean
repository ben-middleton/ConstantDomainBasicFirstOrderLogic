import BQL.Semantics

namespace BQL
open Formula

/-- The fragment used for premises in the disjunction and existence properties. -/
inductive NegativeFragment {L : Language} : {n : Nat} → Formula L n → Prop where
  | top : NegativeFragment top
  | bot : NegativeFragment bot
  | atom : NegativeFragment (atom r ts)
  | conj : NegativeFragment a → NegativeFragment b → NegativeFragment (conj a b)
  | imp : NegativeFragment a → NegativeFragment b → NegativeFragment (imp a b)
  | all : NegativeFragment a → NegativeFragment (all a)

theorem intersection {L : Language} (M : Model L) {I : Type} [Nonempty I]
    (w : M.W) (u : I → M.W)
    (atoms : ∀ {k} (r : L.Rel k) ts, M.rel r w ts ↔ ∀ i, M.rel r (u i) ts)
    (loops : ∀ i, M.acc (u i) (u i)) (edges : ∀ i, M.acc w (u i))
    (cover : ∀ z, M.acc w z → z ≠ w → ∃ i, M.acc (u i) z)
    {n} {a : Formula L n} (ha : NegativeFragment a) (ρ : Fin n → M.D) :
    M.Forces w ρ a ↔ ∀ i, M.Forces (u i) ρ a := by
  refine ⟨fun h i => M.persistence (edges i) ρ a h, ?_⟩
  induction ha with
  | top => exact fun _ => trivial
  | bot => exact fun h => h (Classical.choice ‹Nonempty I›)
  | atom => exact (atoms ..).2
  | conj _ _ ih ik => exact fun h => ⟨ih ρ (fun i => (h i).1), ik ρ (fun i => (h i).2)⟩
  | all _ ih => exact fun h x => ih _ (fun i => h i x)
  | imp _ _ _ ih =>
    intro h z wz hz
    by_cases eq : z = w
    · subst z
      exact ih ρ (fun i => h i _ (loops i) (M.persistence (edges i) ρ _ hz))
    · obtain ⟨i,iz⟩ := cover z wz eq
      exact h i z iz hz

/-- A family of pointed models together with a single domain projecting onto
each component domain. The projections preserve the functions of the language. -/
structure Family (L : Language) (I : Type) where
  model : I → Model L
  root : (i : I) → (model i).W
  loop : ∀ i, (model i).acc (root i) (root i)
  D : Type
  nonempty : Nonempty D
  proj : (i : I) → D → (model i).D
  onto : ∀ i y, ∃ x, proj i x = y
  func : ∀ {k}, L.Func k → (Fin k → D) → D
  map_func : ∀ i {k} (f : L.Func k) ts, proj i (func f ts) = (model i).func f (fun j => proj i (ts j))

namespace Family
variable {L : Language} {I : Type} (F : Family L I)

abbrev World := Option ((i : I) × (F.model i).W)

/-- Edges within a branch have both endpoints in the same component. -/
inductive Reach : F.World → F.World → Prop where
  | loop : Reach none none
  | enter : (F.model i).acc (F.root i) w → Reach none (some ⟨i,w⟩)
  | step : (F.model i).acc w z → Reach (some ⟨i,w⟩) (some ⟨i,z⟩)

def relation {k} (r : L.Rel k) : F.World → (Fin k → F.D) → Prop
  | none, ts => ∀ i, (F.model i).rel r (F.root i) (fun j => F.proj i (ts j))
  | some ⟨i,w⟩, ts => (F.model i).rel r w (fun j => F.proj i (ts j))

def glue : Model L where
  W := F.World
  D := F.D
  worlds := ⟨none⟩
  domain := F.nonempty
  acc := F.Reach
  trans := by
    intro w u z e d
    cases e with
    | loop => exact d
    | enter e => cases d with | step d => exact .enter ((F.model _).trans e d)
    | step e => cases d with | step d => exact .step ((F.model _).trans e d)
  func := F.func
  rel := F.relation
  persist := by
    intro k r w u ts e h
    cases e with
    | loop => exact h
    | enter e => exact (F.model _).persist e (h _)
    | step e => exact (F.model _).persist e h

theorem eval_proj (i : I) (ρ : Fin n → F.D) (t : Term L n) :
    F.proj i (F.glue.eval ρ t) = (F.model i).eval (F.proj i ∘ ρ) t := by
  induction t with
  | var => rfl
  | app f ts ih =>
    exact (F.map_func i f _).trans (congrArg ((F.model i).func f) (funext ih))

theorem proj_extend (i : I) (ρ : Fin n → F.D) (x : F.D) :
    F.proj i ∘ extend ρ x = extend (F.proj i ∘ ρ) (F.proj i x) :=
  funext (fun j => Fin.cases rfl (fun _ => rfl) j)

theorem branch (i : I) (w : (F.model i).W) (ρ : Fin n → F.D) (a : Formula L n) :
    F.glue.Forces (some ⟨i,w⟩) ρ a ↔ (F.model i).Forces w (F.proj i ∘ ρ) a := by
  induction a generalizing w with
  | top | bot => rfl
  | atom r ts =>
    change (F.model i).rel r w _ ↔ (F.model i).rel r w _
    simp only [eval_proj]
  | conj _ _ ih ik => exact and_congr (ih ..) (ik ..)
  | disj _ _ ih ik => exact or_congr (ih ..) (ik ..)
  | imp _ _ ih ik =>
    constructor
    · intro h z e ha
      exact (ik z ρ).1 (h _ (.step e) ((ih z ρ).2 ha))
    · intro h z e ha
      cases e with
      | step e => exact (ik _ ρ).2 (h _ e ((ih _ ρ).1 ha))
  | all a ih =>
    constructor
    · intro h y
      obtain ⟨x,rfl⟩ := F.onto i y
      exact F.proj_extend i ρ x ▸ (ih w _).1 (h x)
    · intro h x
      apply (ih w _).2
      rw [proj_extend]
      exact h _
  | ex a ih =>
    constructor
    · rintro ⟨x,h⟩
      exact ⟨_, F.proj_extend i ρ x ▸ (ih w _).1 h⟩
    · rintro ⟨y,h⟩
      obtain ⟨x,rfl⟩ := F.onto i y
      exact ⟨x, (ih w _).2 (by rw [proj_extend]; exact h)⟩

theorem root_iff [Nonempty I] (ρ : Fin n → F.D) {a : Formula L n} (ha : NegativeFragment a) :
    F.glue.Forces none ρ a ↔ ∀ i, (F.model i).Forces (F.root i) (F.proj i ∘ ρ) a := by
  apply Iff.trans (intersection F.glue none (fun i => some ⟨i,F.root i⟩)
    (fun _ _ => Iff.rfl) (fun i => .step (F.loop i)) (fun i => .enter (F.loop i)) ?_ ha ρ)
  · exact forall_congr' (fun i => F.branch i _ ρ a)
  · intro z e ne
    cases e with
    | loop => exact (ne rfl).elim
    | enter e => exact ⟨_, .step e⟩

end Family
end BQL
