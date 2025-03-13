/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import VersoBlog
import Notes.Genre.Declaration
import VersoManual
import PhysLean.QFT.PerturbationTheory.FieldOpAlgebra.WicksTheoremNormal
import PhysLean.QFT.PerturbationTheory.FieldOpAlgebra.Grading
import PhysLean.QFT.PerturbationTheory.WickContraction.Card
open Verso.Genre
open Verso.Genre Manual

open Verso.Genre
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

{declaration FieldStatistic}

{declaration FieldStatistic.instCommGroup}

{declaration FieldStatistic.exchangeSign}

## Field specifications

{declaration FieldSpecification}

## Field operators

{declaration FieldSpecification.FieldOp}

{declaration FieldSpecification.fieldOpStatistic}

{declaration CreateAnnihilate}

{declaration FieldSpecification.CrAnFieldOp}

{declaration FieldSpecification.crAnFieldOpToCreateAnnihilate}

{declaration FieldSpecification.crAnStatistics}

Insert `FieldSpecification.notation_remark` here

## Field-operator free algebra

{declaration FieldSpecification.FieldOpFreeAlgebra}

Insert `FieldSpecification.FieldOpFreeAlgebra.naming_convention` here

{declaration FieldSpecification.FieldOpFreeAlgebra.ofCrAnOpF}

{declaration FieldSpecification.FieldOpFreeAlgebra.universality}

{declaration FieldSpecification.FieldOpFreeAlgebra.ofCrAnListF}

{declaration FieldSpecification.FieldOpFreeAlgebra.ofFieldOpF}

{declaration FieldSpecification.FieldOpFreeAlgebra.ofFieldOpListF}

Insert `FieldSpecification.FieldOpFreeAlgebra.notation_drop` here

{declaration FieldSpecification.FieldOpFreeAlgebra.fieldOpFreeAlgebraGrade}

{declaration FieldSpecification.FieldOpFreeAlgebra.superCommuteF}

{declaration FieldSpecification.FieldOpFreeAlgebra.superCommuteF_ofCrAnListF_ofCrAnListF_eq_sum}

## Field-operator algebra


{declaration FieldSpecification.FieldOpAlgebra}

{declaration FieldSpecification.FieldOpAlgebra.ι}

{declaration FieldSpecification.FieldOpAlgebra.ofCrAnOp}

{declaration FieldSpecification.FieldOpAlgebra.ofCrAnList}

{declaration FieldSpecification.FieldOpAlgebra.ofFieldOp}

{declaration FieldSpecification.FieldOpAlgebra.ofFieldOpList}

Insert `FieldSpecification.FieldOpAlgebra.notation_drop` here

{declaration FieldSpecification.FieldOpAlgebra.anPart}

{declaration FieldSpecification.FieldOpAlgebra.crPart}

{declaration FieldSpecification.FieldOpAlgebra.ofFieldOp_eq_crPart_add_anPart}

{declaration FieldSpecification.FieldOpAlgebra.fieldOpAlgebraGrade}

{declaration FieldSpecification.FieldOpAlgebra.superCommute}

# Time ordering

{declaration FieldSpecification.crAnTimeOrderRel}

{declaration FieldSpecification.crAnTimeOrderList}

{declaration FieldSpecification.crAnTimeOrderSign}

{declaration FieldSpecification.FieldOpFreeAlgebra.timeOrderF}

{declaration FieldSpecification.FieldOpAlgebra.timeOrder}

{declaration FieldSpecification.FieldOpAlgebra.timeOrder_eq_maxTimeField_mul_finset}

{declaration FieldSpecification.FieldOpAlgebra.timeOrder_timeOrder_mid}

# Normal ordering

{declaration FieldSpecification.normalOrderRel}

{declaration FieldSpecification.normalOrderList}

{declaration FieldSpecification.normalOrderSign}

{declaration FieldSpecification.normalOrderSign_eraseIdx}

{declaration FieldSpecification.FieldOpFreeAlgebra.normalOrderF}

{declaration FieldSpecification.FieldOpAlgebra.normalOrder}

{declaration FieldSpecification.FieldOpAlgebra.normalOrder_superCommute_eq_zero}

{declaration FieldSpecification.FieldOpAlgebra.ofCrAnOp_superCommute_normalOrder_ofCrAnList_sum}

{declaration FieldSpecification.FieldOpAlgebra.ofFieldOp_mul_normalOrder_ofFieldOpList_eq_sum}

# Wick Contractions

## Definition

{declaration WickContraction}

{declaration WickContraction.mem_three}

{declaration WickContraction.mem_four}

Insert `WickContraction.contraction_notation` here

{declaration WickContraction.GradingCompliant}


## Aside: Cardinality

{declaration WickContraction.card_eq_cardFun}

## Uncontracted elements

{declaration WickContraction.uncontracted}

{declaration WickContraction.uncontractedListGet}

## Constructors

{declaration WickContraction.insertAndContract}

{declaration WickContraction.insertLift_sum}

{declaration WickContraction.join}

## Sign

{declaration WickContraction.sign}

{declaration WickContraction.join_sign}

{declaration WickContraction.sign_insert_none}

{declaration WickContraction.sign_insert_none_zero}

{declaration WickContraction.sign_insert_some_of_not_lt}

{declaration WickContraction.sign_insert_some_of_lt}

{declaration WickContraction.sign_insert_some_zero}

## Normal order

{declaration FieldSpecification.FieldOpAlgebra.normalOrder_uncontracted_none}

{declaration FieldSpecification.FieldOpAlgebra.normalOrder_uncontracted_some}

# Static Wick's theorem

## Static contractions

{declaration WickContraction.staticContract}

{declaration WickContraction.staticContract_insert_none}

{declaration WickContraction.staticContract_insert_some}

## Static Wick terms

{declaration WickContraction.staticWickTerm}

{declaration WickContraction.staticWickTerm_empty_nil}

{declaration WickContraction.staticWickTerm_insert_zero_none}

{declaration WickContraction.staticWickTerm_insert_zero_some}

{declaration WickContraction.mul_staticWickTerm_eq_sum}

## The Static Wick's theorem

{declaration FieldSpecification.FieldOpAlgebra.static_wick_theorem}

# Wick's theorem

## Time contractions

{declaration FieldSpecification.FieldOpAlgebra.timeContract}

{declaration FieldSpecification.FieldOpAlgebra.timeContract_of_timeOrderRel}

{declaration FieldSpecification.FieldOpAlgebra.timeContract_of_not_timeOrderRel_expand}

{declaration FieldSpecification.FieldOpAlgebra.timeContract_mem_center}

{declaration WickContraction.timeContract}

{declaration WickContraction.timeContract_insert_none}

{declaration WickContraction.timeContract_insert_some_of_not_lt}

{declaration WickContraction.timeContract_insert_some_of_lt}

{declaration WickContraction.join_sign_timeContract}

## Wick terms

{declaration WickContraction.wickTerm}

{declaration WickContraction.wickTerm_empty_nil}

{declaration WickContraction.wickTerm_insert_none}

{declaration WickContraction.wickTerm_insert_some}

{declaration WickContraction.mul_wickTerm_eq_sum}

## Wick's theorem

{declaration FieldSpecification.wicks_theorem}

# Normal-ordered Wick's theorem

{declaration WickContraction.EqTimeOnly.timeOrder_staticContract_of_not_mem}

{declaration WickContraction.EqTimeOnly.staticContract_eq_timeContract_of_eqTimeOnly}

{declaration WickContraction.EqTimeOnly.timeOrder_timeContract_mul_of_eqTimeOnly_left}

{declaration FieldSpecification.FieldOpAlgebra.timeOrder_ofFieldOpList_eqTimeOnly}

{declaration FieldSpecification.FieldOpAlgebra.normalOrder_timeOrder_ofFieldOpList_eq_eqTimeOnly_empty}

{declaration FieldSpecification.FieldOpAlgebra.timeOrder_haveEqTime_split}

{declaration FieldSpecification.FieldOpAlgebra.wicks_theorem_normal_order}
