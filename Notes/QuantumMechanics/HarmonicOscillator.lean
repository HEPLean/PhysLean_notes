/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.QuantumMechanics.OneDimension.HarmonicOscillator.TISE
import PhysLean.QuantumMechanics.OneDimension.HarmonicOscillator.Completeness
import VersoBlog
import VersoManual
open Verso.Genre Manual

open Verso.Genre
open QuantumMechanics.OneDimension.HilbertSpace
open QuantumMechanics.OneDimension.HarmonicOscillator
set_option verso.docstring.allowMissing true

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

{docstring QuantumMechanics.OneDimension.HilbertSpace}

{docstring MemHS}

{docstring memHS_iff}

{docstring QuantumMechanics.OneDimension.HilbertSpace.mk}

{docstring parity}

{docstring memHS_of_parity}

# The Schrodinger Operator

{docstring QuantumMechanics.OneDimension.HarmonicOscillator}

{docstring ξ}

{docstring schrodingerOperator}

{docstring schrodingerOperator_parity}

# The eigenfunctions of the Schrodinger Operator

{docstring PhysLean.physHermite}

{docstring eigenfunction}

#  Properties of the eigenfunctions

{docstring eigenfunction_integrable}

{docstring eigenfunction_conj}

{docstring eigenfunction_aeStronglyMeasurable}

{docstring eigenfunction_square_integrable}

{docstring eigenfunction_memHS}

{docstring eigenfunction_differentiableAt}

{docstring eigenfunction_orthonormal}

{docstring eigenfunction_parity}

# The time-independent Schrodinger Equation

{docstring eigenValue}

{docstring schrodingerOperator_eigenfunction}

# Completeness

{docstring orthogonal_power_of_mem_orthogonal}

{docstring orthogonal_exp_of_mem_orthogonal}

{docstring fourierIntegral_zero_of_mem_orthogonal}

{docstring eigenfunction_completeness}
