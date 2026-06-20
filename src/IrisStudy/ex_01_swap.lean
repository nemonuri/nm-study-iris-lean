-- original: https://gitlab.mpi-sws.org/iris/tutorial-popl21/-/blob/master/exercises/ex_01_swap.v?ref_type=heads

/-
This exercise introduces the basic Iris Proof Mode tactics by proving a simple
example: a function that swaps the contents of two pointers. We will use this
function to implement two other functions.
-/

module

public import Iris.HeapLang.PrimitiveLaws
public import Iris.HeapLang.ProofMode
public import Iris.Std


public section


namespace IrisStudy

open Iris.HeapLang

/-
The swap function, defined as a heap-lang value. This looks like an ordinary
Coq function, but it is not: heap-lang is a deeply embedded language in Coq. It
uses strings for name binding and notations close to Coq's (but typically
augmented with a colon to avoid ambiguity) to make it easy to read and write
programs.
-/
def swap : Val := hl_val% λ x y,
  let tmp := !x;
  x ← !y;
  y ← tmp



/-
Using swap, we can define functions that rotate three pointers in left and
right direction.
-/
def rotate_r : Val := hl_val% λ x y z,
  &swap y z; &swap x y


def rotate_l : Val := hl_val% λ x y z,
  &swap x y; &swap y z


section print_s

set_option pp.notation false
--set_option pp.explicit true

#print swap
#print rotate_r
#print rotate_l

open Iris ProgramLogic

#print COFE.OFunctorPre
#print GType
#print GFunctor
#print RFunctorContractive
#print BundledGFunctors

end print_s


section proof_s

open Iris.BI Iris ProgramLogic HeapLang

set_option trace.Meta.synthInstance true in
#synth OFE (LeibnizO (Option Val))

set_option trace.Meta.synthInstance true in
#synth CMRA <| Agree (LeibnizO (Option Val))

variable {GF : BundledGFunctors} [hlgs: HeapLangGS hlc GF]

set_option trace.Meta.synthInstance true in
#synth Std.LawfulPartialMap HeapF Loc

set_option trace.Meta.synthInstance true in
#synth UCMRA (IResUR GF)

set_option trace.Meta.synthInstance true in
#synth CMRA DFrac

set_option trace.Meta.synthInstance true in
#synth ProgramLogic.ToVal Exp Val

set_option trace.Meta.synthInstance true in
#synth Wp (IProp GF) Exp Val Stuckness


#print wp.def

#print HeapLangS

#check UPred.instBIBaseUPred

#print instUCMRAIResUR

#print instEctxItemLanguageExp

--set_option pp.explicit true in
/-
set_option trace.Meta.synthInstance true in
set_option pp.notation false in
open Iris.Std in
theorem pointsTo_entails_eq_get? (x: Loc) (v: Option Val)
  : x ↦ v ⊢ ∀(hp: HeapF Val), ⌜get? hp x = v ⌝ := by
  refine (fun n0 valid_at pts_to => ?_)
-/
  --rcases valid_at with ⟨res, res_p⟩
  --have lm1 := valid_at.property
  --have := pointsTo_persist
  --unfold pointsTo
  --unfold ghost_map_elem
  --have bi : BI (IProp GF) := inferInstance
  --sorry


/-
set_option trace.Meta.synthInstance true in
--set_option pp.notation false in
theorem pointsTo_none_eq_empty x
  : iprop( x ↦ .none ) = iprop( ⌜False⌝ ) := by --(Φ : Val → IProp GF)
  have lfm : Std.LawfulFiniteMap HeapF Loc := inferInstance
  have lm1 := lfm.toList_get?_none
-/

set_option trace.Meta.synthInstance true in
theorem swap_spec x y (v1 v2: Val) (Φ : Val → IProp GF) :
  ⊢@{IProp GF}
  ( x ↦ some v1 ∗ y ↦ some v2 ) -∗
  (( x ↦ some v2 ∗ y ↦ some v1 ) -∗ Φ hl_val(#()) ) -∗
  WP hl(&swap #x #y) {{ Φ }}
  := by
  istart
  iintro ⟨h1, h2⟩ h3
  wp_rec; wp_pures

  wp_bind !_
  iapply wp_load $$ h1
  iintro !> h1
  wp_pures

  wp_bind !_
  iapply wp_load $$ h2
  iintro !> h2

  wp_bind _ ← _
  iapply wp_store $$ h1
  iintro !> h1
  wp_pures

  wp_bind _ ← _
  iapply wp_store $$ h2
  iintro !> h2

  iapply h3
  isplitl [h1]
  · iexact h1
  · iexact h2








end proof_s



end IrisStudy

end
