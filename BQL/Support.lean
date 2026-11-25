import BQL.Translation

namespace BQL
open Formula
inductive Symbol (L : Language) where
  | fn {k} (f : L.Func k)
  | rel {k} (r : L.Rel k)

def Term.symbols : Term L n → List (Symbol L)
  | .var _ => []
  | .app f ts => .fn f :: (List.ofFn (fun i => (ts i).symbols)).flatten

def Formula.symbols : Formula L n → List (Symbol L)
  | .top | .bot => []
  | .atom r ts => .rel r :: (List.ofFn (fun i => (ts i).symbols)).flatten
  | .conj a b | .disj a b | .imp a b => a.symbols ++ b.symbols
  | .all a | .ex a => a.symbols

theorem arg_mem {ts : Fin k → Term L n} {i} {s : Symbol L} (h : s ∈ (ts i).symbols) :
    s ∈ (List.ofFn (fun i => (ts i).symbols)).flatten :=
  List.mem_flatten.mpr ⟨_,List.mem_ofFn.mpr ⟨i,rfl⟩,h⟩

def constTerm (c : L.Func 0) : Term L n := .app c Fin.elim0

theorem const_bind (c : L.Func 0) (s : Fin n → Term L m) : (constTerm c).bind s = constTerm c :=
  congrArg (Term.app c) (funext (fun i => i.elim0))

variable {L : Language}

private theorem congrTwo (f : α → β → γ) {a b c d} (h : a = b) (e : c = d) : f a c = f b d := h ▸ e ▸ rfl

namespace Translation
def Fixes (T : Translation L L n m) : Symbol L → Prop
  | .fn (k := 0) c => T.consts c = constTerm c
  | .fn (k := _+1) f => T.funcs f = f
  | .rel r => T.rels r = r

theorem fixes_bind {T : Translation L L n m} {s} (h : T.Fixes s) : T.bind.Fixes s := by
  cases s with
  | rel => exact h
  | @fn k f =>
    cases k with
    | succ => exact h
    | zero => exact (congrArg Term.lift h).trans (const_bind ..)

theorem term_fixed (T : Translation L L n m) (t : Term L n) (fix : ∀ s ∈ t.symbols, T.Fixes s) :
    T.term t = t.bind T.vars := by
  induction t with
  | var => rfl
  | @app k f ts ih =>
    cases k with
    | zero => exact (fix _ (.head _)).trans (congrArg (Term.app f) (funext (fun i => i.elim0)))
    | succ k =>
      exact congrTwo (fun f ts => Term.app f ts) (fix _ (.head _))
        (funext (fun i => ih i (fun s h => fix s (.tail _ (arg_mem h)))))

theorem form_fixed (T : Translation L L n m) (a : Formula L n) (fix : ∀ s ∈ a.symbols, T.Fixes s) :
    T.form a = a.subst T.vars := by
  induction a generalizing m with
  | top | bot => rfl
  | atom r ts =>
    exact congrTwo (fun r ts => atom r ts) (fix _ (.head _))
      (funext (fun i => T.term_fixed _ (fun s h => fix s (.tail _ (arg_mem h)))))
  | conj _ _ ih ik | disj _ _ ih ik | imp _ _ ih ik =>
    simp only [form,subst,ih T (fun s h => fix s (List.mem_append_left _ h)),
      ik T (fun s h => fix s (List.mem_append_right _ h))]
  | all _ ih => exact congrArg all (ih T.bind (fun s h => fixes_bind (fix s h)))
  | ex _ ih => exact congrArg ex (ih T.bind (fun s h => fixes_bind (fix s h)))

noncomputable def openConst (c : L.Func 0) : Translation L L n (n+1) := by
  classical
  exact ⟨fun i => .var i.succ,fun f => if f = c then .var 0 else constTerm f,id,id⟩

theorem open_fixes {c : L.Func 0} {s} (ne : s ≠ .fn c) : (openConst (n := n) c).Fixes s := by
  cases s with
  | rel => rfl
  | @fn k f =>
    cases k with
    | succ => rfl
    | zero => exact if_neg (show f ≠ c from fun e => ne (congrArg Symbol.fn e))

theorem open_independent {a : Formula L n} {c : L.Func 0} (h : Symbol.fn c ∉ a.symbols) :
    (openConst c).form a = a.lift :=
  form_fixed _ _ (fun _ hs => open_fixes (fun e => h (e ▸ hs)))

theorem open_instance {a : Formula L (n+1)} {c : L.Func 0} (h : Symbol.fn c ∉ a.symbols) :
    (openConst c).form (a.inst (constTerm c)) = a := by
  rw [instForm,form_fixed _ a (fun _ hs => fixes_bind (open_fixes (fun e => h (e ▸ hs))))]
  have e : (openConst (n := n) c).term (constTerm c) = .var 0 := by
    simp [term,constTerm,openConst]
  rw [e]
  exact a.open_lift_binder

end Translation
end BQL
