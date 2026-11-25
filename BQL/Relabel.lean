import BQL.Support

namespace BQL
open Formula

structure Relabel (L K : Language) where
  func : ∀ {k}, L.Func k → K.Func k
  rel : ∀ {k}, L.Rel k → K.Rel k

namespace Relabel
variable {L K : Language} (F : Relabel L K)
def term : Term L n → Term K n
  | .var i => .var i
  | .app f ts => .app (F.func f) (fun j => term (ts j))

def form : Formula L n → Formula K n
  | .top => .top
  | .bot => .bot
  | .atom r ts => .atom (F.rel r) (fun j => F.term (ts j))
  | .conj a b => .conj (form a) (form b)
  | .disj a b => .disj (form a) (form b)
  | .imp a b => .imp (form a) (form b)
  | .all a => .all (form a)
  | .ex a => .ex (form a)

def reduct (M : Model K) : Model L where
  W := M.W
  D := M.D
  worlds := M.worlds
  domain := M.domain
  acc := M.acc
  trans := M.trans
  func f := M.func (F.func f)
  rel r := M.rel (F.rel r)
  persist := M.persist

theorem eval (M : Model K) (ρ : Fin n → M.D) (t : Term L n) :
    (F.reduct M).eval ρ t = M.eval ρ (F.term t) := by
  induction t with
  | var => rfl
  | app f _ ih => exact congrArg (M.func (F.func f)) (funext ih)

theorem forces (M : Model K) (w : M.W) (ρ : Fin n → M.D) (a : Formula L n) :
    (F.reduct M).Forces w ρ a ↔ M.Forces w ρ (F.form a) := by
  induction a generalizing w with
  | top | bot => rfl
  | atom => simp only [form,Model.Forces,eval]; rfl
  | conj _ _ ih ik => exact and_congr (ih ..) (ik ..)
  | disj _ _ ih ik => exact or_congr (ih ..) (ik ..)
  | imp _ _ ih ik => simp only [form,Model.Forces,ih,ik]; rfl
  | all _ ih => exact forall_congr' (fun _ => ih ..)
  | ex _ ih => exact exists_congr (fun _ => ih ..)

def asTranslation : Translation L K n n := ⟨Term.var,fun c => constTerm (F.func c), F.func,F.rel⟩

private theorem bind_as : (F.asTranslation (n := n)).bind = F.asTranslation := by
  have hv : up (L := K) (V := n) Term.var = Term.var := funext (fun i => Fin.cases rfl (fun _ => rfl) i)
  simp only [asTranslation,Translation.bind,hv,Term.lift,const_bind]

private theorem term_as (t : Term L n) : F.asTranslation.term t = F.term t := by
  induction t with
  | var => rfl
  | @app k f ts ih =>
    cases k with
    | zero => exact congrArg (Term.app _) (funext (fun i => i.elim0))
    | succ => exact congrArg (Term.app _) (funext ih)

private theorem form_as (a : Formula L n) : F.asTranslation.form a = F.form a := by
  induction a with
  | top | bot => rfl
  | atom => simp only [Translation.form,form,term_as]; rfl
  | conj _ _ ih ik | disj _ _ ih ik | imp _ _ ih ik => simp only [Translation.form,form,ih,ik]
  | all _ ih | ex _ ih => simp only [Translation.form,form,bind_as,ih]

theorem proof {Γ : Theory L n} {G : Theory K n} {a} (p : TJK L e Γ a)
    (g : ∀ b, Γ b → G (F.form b)) : TJK K e G (F.form a) := by
  simpa only [form_as] using Translation.proof p F.asTranslation (G := G)
    (fun b hb => by simpa only [form_as] using g b hb)

theorem tree {Γ Δ : Theory L n} {G D : Theory K n} {a} (p : Derivation L k Γ Δ a)
    (g : ∀ b, Γ b → G (F.form b)) (d : ∀ b, Δ b → D (F.form b)) : Derivation K k G D (F.form a) := by
  simpa only [form_as] using Translation.tree p F.asTranslation (G := G) (D := D)
    (fun b hb => by simpa only [form_as] using g b hb) (fun b hb => by simpa only [form_as] using d b hb)

variable (B : Relabel K L)
def Inverts : Symbol L → Prop
  | .fn f => B.func (F.func f) = f
  | .rel r => B.rel (F.rel r) = r

theorem invertTerm (t : Term L n) (h : ∀ s ∈ t.symbols, F.Inverts B s) :
    B.term (F.term t) = t := by
  induction t with
  | var => rfl
  | app f ts ih =>
    change Term.app _ _ = _
    rw [show B.func (F.func f) = f from h _ (.head _)]
    exact congrArg (Term.app f) (funext (fun i => ih i (fun s hs => h s (.tail _ (arg_mem hs)))))

theorem invertForm (a : Formula L n) (h : ∀ s ∈ a.symbols, F.Inverts B s) :
    B.form (F.form a) = a := by
  induction a with
  | top | bot => rfl
  | atom r ts =>
    change atom _ _ = _
    rw [show B.rel (F.rel r) = r from h _ (.head _)]
    exact congrArg (atom r) (funext (fun i => F.invertTerm B _ (fun s hs => h s (.tail _ (arg_mem hs)))))
  | conj _ _ ih ik | disj _ _ ih ik | imp _ _ ih ik =>
    simp only [form,ih (fun s hs => h s (List.mem_append_left _ hs)),ik (fun s hs => h s (List.mem_append_right _ hs))]
  | all _ ih | ex _ ih => simp only [form,ih h]

end Relabel
end BQL
