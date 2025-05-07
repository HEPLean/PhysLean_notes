/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.QuantumMechanics.OneDimension.HarmonicOscillator.TISE
import PhysLean.CondensedMatter.TightBindingChain.Basic
import VersoBlog
import VersoManual
open Verso.Genre Manual
open CondensedMatter
open Verso.Genre
open QuantumMechanics.OneDimension.HilbertSpace
open QuantumMechanics.OneDimension.HarmonicOscillator
set_option verso.docstring.allowMissing true

set_option maxHeartbeats 0
#doc (Manual) "The tight binding chain" =>
%%%
tag := "TightBindingChain"
authors := ["Joseph Tooby-Smith"]
%%%

# Introduction
%%%
tag := "TBC-intro"
authors := ["Joseph Tooby-Smith"]
%%%

The tight binding chain is corresponds to a
finite dimensional quantum mechanical system.

It consists of a chain of `N` sites seperated by a distance `a`, and a particle,
often described as an electron,
which can occupy each site. The energy of the electron sitting
at a given site is `E_0`, and
a paramter `p` describes the tunneling of the electron between neighbouring sites.

These parameters are defined within the `TightBindingChain` structure.

{docstring TightBindingChain}


The hilbert space is the finite dimensional space of `N`-dimensional vectors.

{docstring TightBindingChain.HilbertSpace}


The state corresponding to the electron being at site `n` is defined as

{docstring TightBindingChain.localizedState}

The notation `|n⟩` is used to denote this state.

These localized states are orthonormal:

{docstring TightBindingChain.localizedState_orthonormal}


The linear map `|m⟩⟨n|`  is given by

{docstring TightBindingChain.localizedComp}

The hamiltonian is then given by

{docstring TightBindingChain.hamiltonian}


The energy of the localized state `|n⟩` is given in the following theorem:

{docstring TightBindingChain.energy_localizedState}

The energy eigenfunctions are parameterized by a wavefunction sitting in the following set

{docstring TightBindingChain.QuantaWaveNumber}

The energy eigenfunctions are given by

{docstring TightBindingChain.energyEigenstate}

The energy eigenvalues are given by

{docstring TightBindingChain.energyEigenvalue}

They satisfy the time independent schrodinger equation

{docstring TightBindingChain.hamiltonian_energyEigenstate}
