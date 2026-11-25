import BQL.Syntax

namespace BQL
variable {L : Language}
theorem Term.bind_comp (s : Fin n → Term L m) (r : Fin m → Term L k) (t : Term L n) :
    (t.bind s).bind r = t.bind (fun j => (s j).bind r) := by
  induction t with
  | var => rfl
  | app f ts ih => exact congrArg (Term.app f) (funext ih)

@[simp] theorem Term.bind_var (t : Term L n) : t.bind Term.var = t := by
  induction t with
  | var => rfl
  | app f _ ih => exact congrArg (Term.app f) (funext ih)

theorem Term.bind_lift (s : Fin n → Term L m) (t : Term L n) :
    t.lift.bind (up s) = (t.bind s).lift := by
  simp only [Term.lift,Term.bind_comp]
  rfl

theorem up_comp (s : Fin n → Term L m) (r : Fin m → Term L k) :
    (fun j => (up s j).bind (up r)) = up (fun j => (s j).bind r) :=
  funext (fun j => Fin.cases rfl (fun i => (s i).bind_lift r) j)

theorem Formula.subst_comp (a : Formula L n) (s : Fin n → Term L m) (r : Fin m → Term L k) :
    (a.subst s).subst r = a.subst (fun j => (s j).bind r) := by
  induction a generalizing m k with
  | top | bot => rfl
  | atom => simp only [subst,Term.bind_comp]
  | conj _ _ ih ik | disj _ _ ih ik | imp _ _ ih ik => simp only [subst,ih,ik]
  | all _ ih | ex _ ih => simp only [subst,ih,up_comp]

@[simp] theorem Formula.subst_var (a : Formula L n) : a.subst Term.var = a := by
  have e (k : Nat) : up (L := L) (V := k) Term.var = Term.var :=
    funext (fun j => Fin.cases rfl (fun _ => rfl) j)
  induction a with
  | top | bot => rfl
  | atom => simp only [subst,Term.bind_var]
  | conj _ _ ih ik | disj _ _ ih ik | imp _ _ ih ik => simp only [subst,ih,ik]
  | all _ ih | ex _ ih => simp only [subst,e,ih]

theorem Formula.subst_lift (a : Formula L n) (s : Fin n → Term L m) :
    a.lift.subst (up s) = (a.subst s).lift := by
  simp only [lift,subst_comp]
  rfl

theorem Formula.subst_inst (a : Formula L (n+1)) (t : Term L n) (s : Fin n → Term L m) :
    (a.inst t).subst s = (a.subst (up s)).inst (t.bind s) := by
  simp only [inst,subst_comp]
  apply congrArg (fun f => a.subst f)
  funext j
  refine Fin.cases rfl (fun i => ?_) j
  change s i = ((s i).bind _).bind _
  rw [Term.bind_comp]
  exact (s i).bind_var.symm

theorem Formula.open_lift_binder (a : Formula L (n+1)) :
    (a.subst (up (fun i : Fin n => .var i.succ))).inst (.var 0) = a := by
  rw [inst,subst_comp]
  apply Eq.trans _ a.subst_var
  exact congrArg (fun s => a.subst s) (funext (fun j => Fin.cases rfl (fun _ => rfl) j))

end BQL
