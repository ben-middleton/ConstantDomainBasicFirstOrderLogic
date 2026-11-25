import BQL.Extension
import BQL.Relabel
import BQL.Encoding

namespace BQL
open Formula
namespace Canonical
variable (L : Language)

private def Numbered (α : Type) := {_i : Nat // Nonempty α}
private def counted : Language := ⟨fun k => Numbered (L.Func k),fun k => Numbered (L.Rel k)⟩

open Encoding
private def termCode : Term (counted L) n → Nat
  | .var i => pair 0 i
  | .app (n := k) f ts => pair 1 (pair k (pair f.val (tuple (fun i => termCode (ts i)))))

private theorem termCode_inj {a b : Term (counted L) n} (h : termCode L a = termCode L b) : a = b := by
  induction a generalizing b with
  | var i => cases b <;> simp_all [termCode,Fin.ext_iff]
  | app f ts ih =>
    cases b <;> simp only [termCode,pair_eq,Nat.reduceEqDiff,false_and,true_and] at h
    obtain ⟨rfl,ef,et⟩ := h
    rw [show f = _ from Subtype.ext ef]
    exact congrArg _ (funext (fun j => ih j (tuple_inj et j)))

private def code : Formula (counted L) n → Nat
  | .top => pair 0 0
  | .bot => pair 1 0
  | .atom (n := k) r ts => pair 2 (pair k (pair r.val (tuple (fun i => termCode L (ts i)))))
  | .conj a b => pair 3 (pair (code a) (code b))
  | .disj a b => pair 4 (pair (code a) (code b))
  | .imp a b => pair 5 (pair (code a) (code b))
  | .all a => pair 6 (code a)
  | .ex a => pair 7 (code a)

private theorem code_inj {a b : Formula (counted L) n} (h : code L a = code L b) : a = b := by
  induction a with
  | atom r ts =>
    cases b <;> simp only [code,pair_eq,Nat.reduceEqDiff,false_and,true_and] at h
    obtain ⟨rfl,er,et⟩ := h
    rw [show r = _ from Subtype.ext er]
    exact congrArg _ (funext (fun j => termCode_inj L (tuple_inj et j)))
  | _ =>
    cases b <;> simp [code] at h ⊢
    all_goals first | exact ⟨by apply_assumption; exact h.1, by apply_assumption; exact h.2⟩ | apply_assumption; exact h

private def maxSymbol : List (Symbol (counted L)) → Nat
  | [] => 0
  | .fn f :: xs => max (f.val+1) (maxSymbol xs)
  | .rel _ :: xs => maxSymbol xs

private theorem ltMax {f : (counted L).Func n} {xs} (h : Symbol.fn f ∈ xs) : f.val < maxSymbol L xs := by
  induction xs with
  | nil => contradiction
  | cons s xs ih =>
    rcases List.mem_cons.mp h with e | hm
    · subst s; exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_left ..)
    · have lt := ih hm
      cases s <;> simp only [maxSymbol] <;> omega

private noncomputable def henkin (hc : Nonempty (L.Func 0)) : HenkinLanguage (counted L) := by
  classical
  let enum := fun n => if e : ∃ a : Sentence (counted L), code L a = n then Classical.choose e else top
  refine ⟨fun xs => ⟨⟨maxSymbol L xs,hc⟩,fun h => (Nat.lt_irrefl _) (ltMax L h)⟩,enum,?_⟩
  intro a
  have ex : ∃ b : Sentence (counted L), code L b = code L a := ⟨a,rfl⟩
  exact ⟨code L a,by simpa [enum,ex] using code_inj L (Classical.choose_spec ex)⟩

private noncomputable def index {α : Type} (xs : List α) (x : α) : Nat := by
  classical
  exact if ex : ∃ i : Fin xs.length, xs.get i = x then (Classical.choose ex).val else xs.length

private theorem index_inj {α : Type} {xs : List α} {a b : α} (ha : a ∈ xs) (hb : b ∈ xs)
    (e : index xs a = index xs b) : a = b := by
  classical
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp ha
  obtain ⟨j,hj⟩ := List.mem_iff_get.mp hb
  have ea : ∃ i, xs.get i = a := ⟨i,hi⟩
  have eb : ∃ i, xs.get i = b := ⟨j,hj⟩
  simp only [index,dif_pos ea,dif_pos eb] at e
  exact (Classical.choose_spec ea).symm.trans ((congrArg xs.get (Fin.ext e)).trans (Classical.choose_spec eb))

private noncomputable def lookup {α β : Type} (xs : List β) (tag : α → β) (i : Numbered α) : α := by
  classical
  exact if h : ∃ x, tag x ∈ xs ∧ index xs (tag x) = i.val then Classical.choose h else Classical.choice i.property

private theorem lookup_index {α β : Type} (xs : List β) (tag : α → β) (a : α)
    (inj : ∀ {a b}, tag a = tag b → a = b) (ha : tag a ∈ xs) :
    lookup xs tag ⟨index xs (tag a),⟨a⟩⟩ = a := by
  classical
  have ex : ∃ b, tag b ∈ xs ∧ index xs (tag b) = index xs (tag a) := ⟨a,ha,rfl⟩
  exact (dif_pos ex).trans (inj (index_inj (Classical.choose_spec ex).1 ha (Classical.choose_spec ex).2))

private noncomputable def number (xs : List (Symbol L)) : Relabel L (counted L) where
  func f := ⟨index xs (.fn f),⟨f⟩⟩
  rel r := ⟨index xs (.rel r),⟨r⟩⟩
private noncomputable def unnumber (xs : List (Symbol L)) : Relabel (counted L) L where
  func := lookup xs Symbol.fn
  rel := lookup xs Symbol.rel

private theorem number_inverse {xs : List (Symbol L)} {s} (hs : s ∈ xs) :
    (number L xs).Inverts (unnumber L xs) s := by
  cases s with
  | fn f => exact lookup_index xs Symbol.fn f (fun h => by cases h; rfl) hs
  | rel r => exact lookup_index xs Symbol.rel r (fun h => by cases h; rfl) hs

theorem finiteRelabel (hc : Nonempty (L.Func 0)) (xs : List (Symbol L)) :
    ∃ (K : Language) (F : Relabel L K) (B : Relabel K L), Nonempty (HenkinLanguage K) ∧
      ∀ s ∈ xs, F.Inverts B s :=
  ⟨_,number L xs,unnumber L xs,⟨henkin L hc⟩,fun _ => number_inverse L⟩

theorem singletonCompleteGeneral (hc : Nonempty (L.Func 0)) {x y : F L} (h : Entails (single x) y) :
    TJK L true (single x) y := by
  let xs := x.symbols ++ y.symbols
  let F := number L xs
  let B := unnumber L xs
  have sem : Entails (single (F.form x)) (F.form y) := by
    intro M w ρ r g
    apply (F.forces M w ρ y).1
    exact h (F.reduct M) w ρ r (fun _ e => e ▸ (F.forces M w ρ x).2 (g _ rfl))
  have px : B.form (F.form x) = x := F.invertForm B x (fun _ hs => number_inverse L (List.mem_append_left _ hs))
  have py : B.form (F.form y) = y := F.invertForm B y (fun _ hs => number_inverse L (List.mem_append_right _ hs))
  exact py ▸ B.proof (singletonComplete (henkin L hc) sem) (fun _ e => e ▸ px.symm)

end Canonical

def conjunction : List (Formula L n) → Formula L n
  | [] => top
  | a::xs => conj a (conjunction xs)

theorem conjunction_forces (M : Model L) (w : M.W) (ρ : Fin n → M.D) (xs : List (Formula L n)) :
    M.Forces w ρ (conjunction xs) ↔ ∀ a ∈ xs, M.Forces w ρ a := by
  induction xs with
  | nil => simp [conjunction,Model.Forces]
  | cons a xs ih => exact (and_congr Iff.rfl ih).trans List.forall_mem_cons.symm

/-- Strong completeness over any signature with a constant, including the
paper's extended language with eigenconstants. -/
theorem completeWithConstant {L : Language} (hc : Nonempty (L.Func 0)) {Γ : Theory L 0} {a}
    (h : Entails Γ a) : Proves Γ a := by
  obtain ⟨xs,hx,hs⟩ := compactness h
  have hx' : TJK L true Γ (conjunction xs) := by
    clear hs
    induction xs with
    | nil => exact .topI
    | cons b xs ih => exact .andI (.hyp (hx _ (.head _))) (ih (fun z hz => hx z (.tail _ hz)))
  have single : Entails (Canonical.single (conjunction xs)) a := fun M w ρ r g =>
    hs M w ρ r ((conjunction_forces ..).1 (g _ rfl))
  exact ((Canonical.singletonCompleteGeneral L hc single).cut (fun _ eq => eq ▸ hx')).toRoot

end BQL
