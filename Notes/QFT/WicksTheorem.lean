/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import VersoBlog
import VersoManual
import PhysLean.QFT.PerturbationTheory.WickAlgebra.WicksTheoremNormal
import PhysLean.QFT.PerturbationTheory.WickAlgebra.Grading
import PhysLean.QFT.PerturbationTheory.WickContraction.Card
open Verso.Genre
open Verso.Genre Manual

open Verso.Genre
set_option verso.docstring.allowMissing true

set_option maxHeartbeats 0

#doc (Manual) "Wicks theorem" =>


By Joseph Tooby-Smith

# Introduction
%%%
tag := "Introduction"
%%%

Wicks theorem

In this note we walk through the important parts of the proof of the three versions of
      Wick's theorem for field operators containing carrying both fermionic and bosonic statistics,
      as it appears in PhysLean. Not every lemma or definition is covered here.
      The aim is to give just enough that the story can be understood.


Before proceeding with the steps in the proof, we review some basic terminology
     related to Lean and type theory. The most important notion is that of a type.
     We don't give any formal definition here, except to say that a type `T`, like a set, has
     elements `x` which we say are of type `T` and write `x : T`. Examples of types include,
     the type of natural numbers `ℕ`, the type of real numbers `ℝ`, the type of numbers
     `0, …, n-1` denoted `Fin n`. Given two types `T` and `S`, we can form the product type `T × S`,
     and the function type `T → S`.

Types form the foundation of Lean and the theory behind them will be used both explicitly and
      implicitly throughout this note.


# Field operators

## Field statistics

{docstring FieldStatistic}

{docstring FieldStatistic.instCommGroup}

{docstring FieldStatistic.exchangeSign}

## Field specifications

{docstring FieldSpecification}

## Field operators

{docstring FieldSpecification.FieldOp}

{docstring FieldSpecification.fieldOpStatistic}

{docstring CreateAnnihilate}

{docstring FieldSpecification.CrAnFieldOp}

{docstring FieldSpecification.crAnFieldOpToCreateAnnihilate}

{docstring FieldSpecification.crAnStatistics}

Insert `FieldSpecification.notation_remark` here

## Field-operator free algebra

{docstring FieldSpecification.FieldOpFreeAlgebra}

Insert `FieldSpecification.FieldOpFreeAlgebra.naming_convention` here

{docstring FieldSpecification.FieldOpFreeAlgebra.ofCrAnOpF}

{docstring FieldSpecification.FieldOpFreeAlgebra.universality}

{docstring FieldSpecification.FieldOpFreeAlgebra.ofCrAnListF}

{docstring FieldSpecification.FieldOpFreeAlgebra.ofFieldOpF}

{docstring FieldSpecification.FieldOpFreeAlgebra.ofFieldOpListF}

Insert `FieldSpecification.FieldOpFreeAlgebra.notation_drop` here

{docstring FieldSpecification.FieldOpFreeAlgebra.fieldOpFreeAlgebraGrade}

{docstring FieldSpecification.FieldOpFreeAlgebra.superCommuteF}

{docstring FieldSpecification.FieldOpFreeAlgebra.superCommuteF_ofCrAnListF_ofCrAnListF_eq_sum}

## Field-operator algebra


{docstring FieldSpecification.WickAlgebra}

{docstring FieldSpecification.WickAlgebra.ι}

{docstring FieldSpecification.WickAlgebra.ofCrAnOp}

{docstring FieldSpecification.WickAlgebra.ofCrAnList}

{docstring FieldSpecification.WickAlgebra.ofFieldOp}

{docstring FieldSpecification.WickAlgebra.ofFieldOpList}

{docstring FieldSpecification.WickAlgebra.anPart}

{docstring FieldSpecification.WickAlgebra.crPart}

{docstring FieldSpecification.WickAlgebra.ofFieldOp_eq_crPart_add_anPart}

{docstring FieldSpecification.WickAlgebra.WickAlgebraGrade}

{docstring FieldSpecification.WickAlgebra.superCommute}

# Time ordering

{docstring FieldSpecification.crAnTimeOrderRel}

{docstring FieldSpecification.crAnTimeOrderList}

{docstring FieldSpecification.crAnTimeOrderSign}

{docstring FieldSpecification.FieldOpFreeAlgebra.timeOrderF}

{docstring FieldSpecification.WickAlgebra.timeOrder}

{docstring FieldSpecification.WickAlgebra.timeOrder_eq_maxTimeField_mul_finset}

{docstring FieldSpecification.WickAlgebra.timeOrder_timeOrder_mid}

# Normal ordering

{docstring FieldSpecification.normalOrderRel}

{docstring FieldSpecification.normalOrderList}

{docstring FieldSpecification.normalOrderSign}

{docstring FieldSpecification.normalOrderSign_eraseIdx}

{docstring FieldSpecification.FieldOpFreeAlgebra.normalOrderF}

{docstring FieldSpecification.WickAlgebra.normalOrder}

{docstring FieldSpecification.WickAlgebra.normalOrder_superCommute_eq_zero}

{docstring FieldSpecification.WickAlgebra.ofCrAnOp_superCommute_normalOrder_ofCrAnList_sum}

{docstring FieldSpecification.WickAlgebra.ofFieldOp_mul_normalOrder_ofFieldOpList_eq_sum}

# Wick Contractions

## Definition

{docstring WickContraction}

{docstring WickContraction.mem_three}

{docstring WickContraction.mem_four}

Insert `WickContraction.contraction_notation` here

{docstring WickContraction.GradingCompliant}


## Aside: Cardinality

{docstring WickContraction.card_eq_cardFun}

## Uncontracted elements

{docstring WickContraction.uncontracted}

{docstring WickContraction.uncontractedListGet}

## Constructors

{docstring WickContraction.insertAndContract}

{docstring WickContraction.insertLift_sum}

{docstring WickContraction.join}

## Sign

{docstring WickContraction.sign}

{docstring WickContraction.join_sign}

{docstring WickContraction.sign_insert_none}

{docstring WickContraction.sign_insert_none_zero}

{docstring WickContraction.sign_insert_some_of_not_lt}

{docstring WickContraction.sign_insert_some_of_lt}

{docstring WickContraction.sign_insert_some_zero}

## Normal order

{docstring FieldSpecification.WickAlgebra.normalOrder_uncontracted_none}

{docstring FieldSpecification.WickAlgebra.normalOrder_uncontracted_some}

# Static Wick's theorem

## Static contractions

{docstring WickContraction.staticContract}

{docstring WickContraction.staticContract_insert_none}

{docstring WickContraction.staticContract_insert_some}

## Static Wick terms

{docstring WickContraction.staticWickTerm}

{docstring WickContraction.staticWickTerm_empty_nil}

{docstring WickContraction.staticWickTerm_insert_zero_none}

{docstring WickContraction.staticWickTerm_insert_zero_some}

{docstring WickContraction.mul_staticWickTerm_eq_sum}

## The Static Wick's theorem

{docstring FieldSpecification.WickAlgebra.static_wick_theorem}

# Wick's theorem

## Time contractions

{docstring FieldSpecification.WickAlgebra.timeContract}

{docstring FieldSpecification.WickAlgebra.timeContract_of_timeOrderRel}

{docstring FieldSpecification.WickAlgebra.timeContract_of_not_timeOrderRel_expand}

{docstring FieldSpecification.WickAlgebra.timeContract_mem_center}

{docstring WickContraction.timeContract}

{docstring WickContraction.timeContract_insert_none}

{docstring WickContraction.timeContract_insert_some_of_not_lt}

{docstring WickContraction.timeContract_insert_some_of_lt}

{docstring WickContraction.join_sign_timeContract}

## Wick terms

{docstring WickContraction.wickTerm}

{docstring WickContraction.wickTerm_empty_nil}

{docstring WickContraction.wickTerm_insert_none}

{docstring WickContraction.wickTerm_insert_some}

{docstring WickContraction.mul_wickTerm_eq_sum}

## Wick's theorem

{docstring FieldSpecification.wicks_theorem}

# Normal-ordered Wick's theorem

{docstring WickContraction.EqTimeOnly.timeOrder_staticContract_of_not_mem}

{docstring WickContraction.EqTimeOnly.staticContract_eq_timeContract_of_eqTimeOnly}

{docstring WickContraction.EqTimeOnly.timeOrder_timeContract_mul_of_eqTimeOnly_left}

{docstring FieldSpecification.WickAlgebra.timeOrder_ofFieldOpList_eqTimeOnly}

{docstring FieldSpecification.WickAlgebra.normalOrder_timeOrder_ofFieldOpList_eq_eqTimeOnly_empty}

{docstring FieldSpecification.WickAlgebra.timeOrder_haveEqTime_split}

{docstring FieldSpecification.WickAlgebra.wicks_theorem_normal_order}
