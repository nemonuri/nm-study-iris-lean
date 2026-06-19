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

--#synth IProp

--set_option trace.Meta.synthInstance true in
--#synth Std.Heap HeapF Loc


set_option trace.Meta.synthInstance true in
set_option pp.notation false in
open Iris.Std in
theorem pointsTo_eq_get? (x: Loc) (v: Option Val)
  : iprop( x ↦ v ) = iprop( ⌜∀(k: HeapF Val), get? k x = v ⌝ ) := by
  have bi : BI (IProp GF) := inferInstance
  sorry


/-
set_option trace.Meta.synthInstance true in
--set_option pp.notation false in
theorem pointsTo_none_eq_empty x
  : iprop( x ↦ .none ) = iprop( ⌜False⌝ ) := by --(Φ : Val → IProp GF)
  have lfm : Std.LawfulFiniteMap HeapF Loc := inferInstance
  have lm1 := lfm.toList_get?_none
-/

/-
theorem swap_spec x y v1 v2 (Φ : Val → IProp GF) :
  ⊢@{IProp GF}
  ( x ↦ v1 ∗ y ↦ v2 ) -∗
  (( x ↦ v2 ∗ y ↦ v1 ) -∗ Φ hl_val(#()) ) -∗
  WP hl(&swap #x #y) {{ v, Φ v }}
  := by
  istart
  iintro ⟨h1, h2⟩ h3
  iloeb as ih4
  wp_rec; wp_pures
  cases v1 with
  | none =>
-/
  --cases v1 with
  --| none => wp_expr_simp
  --iloeb as lm1
  --iapply wp_load
  --ihave _ := wp_load $$ %Φ h1
  --irevert h1 h2 h3
  --inext
  --ihave %lm1 := wp_load Φ && *h1
   --h1 h2
  --icases h1 with ⟨h1_1, h1_2⟩

  --wp_rec
  --icases h1 with ⟨h2, h3⟩
  --unfold swap




end proof_s



end IrisStudy

end
