import BQL.TJK

namespace BQL
open Formula

/-- Interpret parameters by terms and rename the remaining symbols. -/
structure Translation (L K : Language) (n m : Nat) where
  vars : Fin n → Term K m
  consts : L.Func 0 → Term K m
  funcs : ∀ {k}, L.Func (k+1) → K.Func (k+1)
  rels : ∀ {k}, L.Rel k → K.Rel k

namespace Translation
variable {L K : Language}

def bind (T : Translation L K n m) : Translation L K (n+1) (m+1) :=
  ⟨up T.vars,fun c => (T.consts c).lift,T.funcs,T.rels⟩

def term (T : Translation L K n m) : Term L n → Term K m
  | .var i => T.vars i
  | .app (n := 0) f _ => T.consts f
  | .app (n := _+1) f ts => .app (T.funcs f) (fun j => T.term (ts j))

def form : {n m : Nat} → Translation L K n m → Formula L n → Formula K m
  | _,_,_,.top => .top
  | _,_,_,.bot => .bot
  | _,_,T,.atom r ts => .atom (T.rels r) (fun j => T.term (ts j))
  | _,_,T,.conj a b => .conj (form T a) (form T b)
  | _,_,T,.disj a b => .disj (form T a) (form T b)
  | _,_,T,.imp a b => .imp (form T a) (form T b)
  | _,_,T,.all a => .all (form T.bind a)
  | _,_,T,.ex a => .ex (form T.bind a)

/-- A square commutes when translating then substituting and substituting
then translating agree on variables and on all language symbols. -/
structure Commutes (T : Translation L K n m) (U : Translation L K i j)
    (s : Fin n → Term L i) (r : Fin m → Term K j) : Prop where
  vars : ∀ x, U.term (s x) = (T.vars x).bind r
  consts : ∀ c, U.consts c = (T.consts c).bind r
  funcs : ∀ {k} (f : L.Func (k+1)), U.funcs f = T.funcs f
  rels : ∀ {k} (p : L.Rel k), U.rels p = T.rels p

theorem squareTerm {T : Translation L K n m} {U : Translation L K i j} {s r}
    (h : Commutes T U s r) (t : Term L n) : U.term (t.bind s) = (T.term t).bind r := by
  induction t with
  | var x => exact h.vars x
  | @app k f ts ih =>
    cases k with
    | zero => exact h.consts f
    | succ k => simp only [Term.bind,term,h.funcs,ih]

theorem liftTerm (T : Translation L K n m) (t : Term L n) : T.bind.term t.lift = (T.term t).lift :=
  squareTerm (T := T) (U := T.bind) (s := fun i => .var i.succ) (r := fun i => .var i.succ) ⟨fun _ => rfl,fun _ => rfl,fun _ => rfl,fun _ => rfl⟩ t

theorem Commutes.bind {T : Translation L K n m} {U : Translation L K i j} {s r}
    (h : Commutes T U s r) : Commutes T.bind U.bind (up s) (up r) := by
  refine ⟨?_,?_,h.funcs,h.rels⟩
  · intro x
    refine Fin.cases rfl (fun k => ?_) x
    exact (U.liftTerm (s k)).trans ((congrArg Term.lift (h.vars k)).trans ((T.vars k).bind_lift r).symm)
  · intro c
    exact (congrArg Term.lift (h.consts c)).trans ((T.consts c).bind_lift r).symm

theorem square {T : Translation L K n m} {U : Translation L K i j} {s r}
    (h : Commutes T U s r) (a : Formula L n) : U.form (a.subst s) = (T.form a).subst r := by
  induction a generalizing m i j with
  | top | bot => rfl
  | atom => simp only [subst,form,h.rels,squareTerm h]
  | conj _ _ ih ik | disj _ _ ih ik | imp _ _ ih ik => simp only [subst,form,ih h,ik h]
  | all _ ih | ex _ ih => simp only [subst,form,ih h.bind]

theorem liftForm (T : Translation L K n m) (a : Formula L n) : T.bind.form a.lift = (T.form a).lift :=
  square (T := T) (U := T.bind) (s := fun i => .var i.succ) (r := fun i => .var i.succ) ⟨fun _ => rfl,fun _ => rfl,fun _ => rfl,fun _ => rfl⟩ a

private theorem dropLift (t : Term K m) (v : Term K m) :
    t.lift.bind (extend Term.var v) = t := by rw [Term.lift,Term.bind_comp]; exact t.bind_var

theorem instForm (T : Translation L K n m) (a : Formula L (n+1)) (t : Term L n) :
    T.form (a.inst t) = (T.bind.form a).inst (T.term t) :=
  square (T := T.bind) (U := T) (s := extend Term.var t) (r := extend Term.var (T.term t)) ⟨fun x => Fin.cases rfl (fun i => (dropLift (T.vars i) _).symm) x,
    fun c => (dropLift (T.consts c) _).symm,fun _ => rfl,fun _ => rfl⟩ a

def axiomMap (T : Translation L K n m) {a} (h : Axiom a) : Axiom (T.form a) := by
  cases h <;> simp only [form,liftForm,instForm] <;> first
    | exact .id | exact .top | exact .bot | exact .meet | exact .left | exact .right | exact .inl
    | exact .inr | exact .join | exact .dist | exact .iAll | exact .allE _ | exact .exI _
    | exact .iEx | exact .cd | exact .iDist | exact .trans | exact .prefixing | exact .suffixing | exact .weakening

def Maps (T : Translation L K n m) (Γ : Theory L n) (G : Theory K m) := ∀ ⦃a⦄, Γ a → G (T.form a)
private theorem underInsert {T : Translation L K n m} {Γ G} (h : T.Maps Γ G) (a) :
    T.Maps (insert a Γ) (insert (T.form a) G) :=
  fun _ hx => hx.elim (fun e => Or.inl (congrArg T.form e)) (fun hg => Or.inr (h hg))
private theorem underLift {T : Translation L K n m} {Γ G} (h : T.Maps Γ G) :
    T.bind.Maps (lifted Γ) (lifted G) := fun _ ⟨a,ha,e⟩ => e ▸ ⟨_,h ha,(T.liftForm a).symm⟩

theorem proof {Γ : Theory L n} {a} (p : TJK L e Γ a) (T : Translation L K n m) {G}
    (g : T.Maps Γ G) : TJK K e G (T.form a) := by
  induction p generalizing m with
  | hyp h => exact .hyp (g h)
  | ax h => exact .ax (T.axiomMap h)
  | topI => exact .topI
  | botE _ h => exact .botE (h T g)
  | andI _ _ h v => exact .andI (h T g) (v T g)
  | andL _ h => exact .andL (h T g)
  | andR _ h => exact .andR (h T g)
  | orL _ h => exact .orL (h T g)
  | orR _ h => exact .orR (h T g)
  | orE _ _ _ h u v => exact .orE (h T g) (u T (underInsert g _)) (v T (underInsert g _))
  | mp _ _ h v => exact .mp (h T g) (v T g)
  | rule _ _ h v => exact .rule (h T g) (v T g)
  | allI _ h => exact .allI (h _ (underLift g))
  | allE t _ h => rw [instForm]; exact .allE _ (h T g)
  | exI t _ h => exact .exI _ (by simpa only [instForm] using h T g)
  | exE en _ _ h v =>
    exact .exE en (h T g) (by simpa only [liftForm] using v _ (underInsert (underLift g) _))
  | cd _ h => exact .cd (by simpa only [form,liftForm] using h T g)

theorem tree {Γ Δ : Theory L n} {a} (p : Derivation L k Γ Δ a) (T : Translation L K n m) {G D}
    (g : T.Maps Γ G) (d : T.Maps Δ D) : Derivation K k G D (T.form a) := by
  induction p generalizing m with
  | extra h => exact h.elim
  | global h => exact .global (g h)
  | hyp h => exact .hyp (d h)
  | orE _ _ _ h u v => exact .orE (h T g d) (u T g (underInsert d _)) (v T g (underInsert d _))
  | impI _ h => exact .impI (h T g (underInsert d _))
  | impE e _ _ h v => exact .impE e (h T g d) (v T g (fun _ h => h.elim))
  | allI _ h => exact .allI (h _ (underLift g) (underLift d))
  | exE _ _ h v => exact .exE (h T g d) (by simpa only [liftForm] using v _ (underLift g) (underInsert (underLift d) _))
  | allE t _ h => rw [instForm]; exact .allE _ (h T g d)
  | exI t _ h => exact .exI _ (by simpa only [instForm] using h T g d)
  | cd _ h => exact .cd (by simpa only [form,liftForm] using h T g d)
  | internalAll _ h => exact .internalAll (by simpa only [form,liftForm] using h T g d)
  | internalEx _ h => exact .internalEx (by simpa only [form,liftForm] using h T g d)
  | andL _ h => exact .andL (h T g d)
  | andR _ h => exact .andR (h T g d)
  | botE _ h => exact .botE (h T g d)
  | topI  => exact .topI
  | andI _ _ h i => exact .andI (h T g d) (i T g d)
  | orL _ h => exact .orL (h T g d)
  | orR _ h => exact .orR (h T g d)
  | trans _ _ h i => exact .trans (h T g d) (i T g d)
  | meet _ _ h i => exact .meet (h T g d) (i T g d)
  | join _ _ h i => exact .join (h T g d) (i T g d)

end Translation
end BQL
