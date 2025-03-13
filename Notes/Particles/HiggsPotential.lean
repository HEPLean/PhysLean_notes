/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Particles.StandardModel.HiggsBoson.Potential
import VersoBlog
import Notes.Genre.Declaration
import VersoManual
open Verso.Genre Manual

open Verso.Genre
open StandardModel
open StandardModel.HiggsField

set_option maxHeartbeats 0
#doc (Manual) "Higgs potential" =>
%%%
tag := "higgs-potential"
authors := ["Joseph Tooby-Smith"]
%%%

# Introduction

The Higgs potential is a key part of the Standard Model of particle physics.
      It is a scalar potential which is used to give mass to the elementary particles.
      The Higgs potential is a polynomial of degree four in the Higgs field.

# The Higgs field

{declaration StandardModel.HiggsVec}

{declaration StandardModel.HiggsBundle}

{declaration StandardModel.HiggsField}

# The Higgs potential

{declaration StandardModel.HiggsField.Potential}

{declaration StandardModel.HiggsField.normSq}

{declaration StandardModel.HiggsField.Potential.toFun}

## Properties of the Higgs potential

{declaration StandardModel.HiggsField.Potential.neg_𝓵_quadDiscrim_zero_bound}

{declaration StandardModel.HiggsField.Potential.pos_𝓵_quadDiscrim_zero_bound}

{declaration StandardModel.HiggsField.Potential.neg_𝓵_sol_exists_iff}

{declaration StandardModel.HiggsField.Potential.pos_𝓵_sol_exists_iff}

## Boundedness of the Higgs potential

{declaration StandardModel.HiggsField.Potential.IsBounded}

{declaration StandardModel.HiggsField.Potential.isBounded_𝓵_nonneg}

{declaration StandardModel.HiggsField.Potential.isBounded_of_𝓵_pos}

## Maximum and minimum of the Higgs potential

{declaration StandardModel.HiggsField.Potential.isMaxOn_iff_field_of_𝓵_neg}

{declaration StandardModel.HiggsField.Potential.isMinOn_iff_field_of_𝓵_pos}
