/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.QuantumMechanics.OneDimension.HarmonicOscillator.TISE
import PhysLean.QuantumMechanics.OneDimension.HarmonicOscillator.Completeness
import VersoBlog
import Notes.Genre.Declaration
import VersoManual
open Verso.Genre Manual

open Verso.Genre
open QuantumMechanics.OneDimension.HilbertSpace
open QuantumMechanics.OneDimension.HarmonicOscillator

set_option maxHeartbeats 0
#doc (Manual) "Quantum Harmonic Oscillator" =>
%%%
tag := "QHO"
authors := ["Joseph Tooby-Smith"]
%%%

# Introduction
%%%
tag := "intro"
authors := ["Joseph Tooby-Smith"]
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

# Hilbert space

{declaration QuantumMechanics.OneDimension.HilbertSpace}

{declaration MemHS}

{declaration memHS_iff}

{declaration QuantumMechanics.OneDimension.HilbertSpace.mk}

{declaration parity}

{declaration memHS_of_parity}

# The Schrodinger Operator

{declaration QuantumMechanics.OneDimension.HarmonicOscillator}

{declaration ξ}

{declaration schrodingerOperator}

{declaration schrodingerOperator_parity}

# The eigenfunctions of the Schrodinger Operator

{declaration PhysLean.physHermite}

{declaration eigenfunction}

#  Properties of the eigenfunctions

{declaration eigenfunction_integrable}

{declaration eigenfunction_conj}

{declaration eigenfunction_aeStronglyMeasurable}

{declaration eigenfunction_square_integrable}

{declaration eigenfunction_memHS}

{declaration eigenfunction_differentiableAt}

{declaration eigenfunction_orthonormal}

{declaration eigenfunction_parity}

# The time-independent Schrodinger Equation

{declaration eigenValue}

{declaration schrodingerOperator_eigenfunction}

# Completeness

{declaration orthogonal_power_of_mem_orthogonal}

{declaration orthogonal_exp_of_mem_orthogonal}

{declaration fourierIntegral_zero_of_mem_orthogonal}

{declaration eigenfunction_completeness}
