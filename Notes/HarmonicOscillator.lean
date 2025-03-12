/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.QuantumMechanics.OneDimension.HarmonicOscillator.Basic
import VersoBlog
import Notes.Genre.Basic

open Verso.Genre
open QuantumMechanics.OneDimension
open PhysLeanNote
#doc (PhysLeanNote) "Quantum Harmonic Oscillator" =>


# Introduction
%%%
tag := "intro"
%%%

The quantum harmonic oscillator is a fundamental example of a one-dimensional
quantum mechanical system. It is often one of the first models encountered by undergraduate
students studying quantum mechanics.

This note presents the formalization of the quantum harmonic oscillator in the theorem prover
Lean 4, as part of the larger project PhysLean.
What this means is that every definition and theorem in this note has been formally checked
for mathematical correctness for by a computer. There are a number of
motivations for doing this which are dicussed  physlean.com


Note that we do not give every definition and theorem which is part of the formalization.
Our goal is give key aspects, in such a way that we hope this note will be useful
to newcomers to Lean or those intrested in simply intrested in learning about the
quantum harmonic oscillator.

{docString "test"}
