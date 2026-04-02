/- 
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Euclidean Plane Backgrounds

This file introduces a first genuine background layer for the continuum
side of the project. Rather than hard-coding `ℝ^d`, Schwartz test
functions, tempered distributions, and Euclidean motions separately in
downstream files, we package the ambient Euclidean background and derive
the standard objects from it.

The first instance is the Euclidean plane background used by the current
`P(Φ)₂` formalization. Future torus/cylinder backgrounds can grow beside
this layer rather than being introduced only through route-local APIs.
-/

import GaussianField.Construction
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

noncomputable section

open GaussianField

namespace Pphi2

/-- A Euclidean continuum background determined by its dimension.

This is intentionally small: the point space, real/complex Schwartz test
spaces, tempered distributions, and Euclidean motions are all derived from
the ambient Euclidean space `ℝ^d`. -/
structure EuclideanPlaneBackground where
  dim : ℕ

namespace EuclideanPlaneBackground

/-- The underlying Euclidean spacetime `ℝ^d`. -/
abbrev SpaceTime (B : EuclideanPlaneBackground) :=
  EuclideanSpace ℝ (Fin B.dim)

/-- Real Schwartz test functions on the background. -/
abbrev RealTestFunction (B : EuclideanPlaneBackground) :=
  SchwartzMap (SpaceTime B) ℝ

/-- Complex Schwartz test functions on the background. -/
abbrev ComplexTestFunction (B : EuclideanPlaneBackground) :=
  SchwartzMap (SpaceTime B) ℂ

/-- Tempered distributions on the background. -/
abbrev Distribution (B : EuclideanPlaneBackground) :=
  Configuration (RealTestFunction B)

/-- Orthogonal linear isometry equivalences of the background. -/
abbrev OrthogonalGroup (B : EuclideanPlaneBackground) :=
  SpaceTime B ≃ₗᵢ[ℝ] SpaceTime B

/-- A Euclidean motion: orthogonal part plus translation. -/
structure Motion (B : EuclideanPlaneBackground) where
  R : OrthogonalGroup B
  t : SpaceTime B

/-- The inverse affine action of a Euclidean motion on spacetime points. -/
def inversePointAction {B : EuclideanPlaneBackground}
    (g : Motion B) (x : SpaceTime B) : SpaceTime B :=
  g.R.symm (x - g.t)

private lemma inversePointAction_hasTemperateGrowth
    {B : EuclideanPlaneBackground} (g : Motion B) :
    (inversePointAction g).HasTemperateGrowth := by
  have hR := g.R.symm.toContinuousLinearEquiv.hasTemperateGrowth
  have hSub : (fun x : SpaceTime B => x - g.t).HasTemperateGrowth :=
    ((ContinuousLinearMap.id ℝ (SpaceTime B)).hasTemperateGrowth).sub
      (Function.HasTemperateGrowth.const g.t)
  convert hR.comp hSub

private lemma inversePointAction_antilipschitz
    {B : EuclideanPlaneBackground} (g : Motion B) :
    AntilipschitzWith 1 (inversePointAction g) :=
  fun x y => by
    simp only [inversePointAction, ENNReal.coe_one, one_mul]
    calc edist x y
        = edist (x - g.t) (y - g.t) := by rw [edist_sub_right]
      _ = edist (g.R.symm (x - g.t)) (g.R.symm (y - g.t)) :=
          (g.R.symm.isometry.edist_eq _ _).symm
      _ ≤ edist (g.R.symm (x - g.t)) (g.R.symm (y - g.t)) := le_refl _

/-- Pull back a real Schwartz function along a Euclidean motion. -/
noncomputable def action {B : EuclideanPlaneBackground}
    (g : Motion B) : RealTestFunction B →L[ℝ] RealTestFunction B :=
  SchwartzMap.compCLMOfAntilipschitz ℝ
    (inversePointAction_hasTemperateGrowth g)
    (inversePointAction_antilipschitz g)

/-- Pull back a complex Schwartz function along a Euclidean motion. -/
noncomputable def actionComplex {B : EuclideanPlaneBackground}
    (g : Motion B) : ComplexTestFunction B →L[ℝ] ComplexTestFunction B :=
  SchwartzMap.compCLMOfAntilipschitz ℝ
    (inversePointAction_hasTemperateGrowth g)
    (inversePointAction_antilipschitz g)

/-- The pure translation motion with identity orthogonal part. -/
def translationMotion (B : EuclideanPlaneBackground) (t : SpaceTime B) : Motion B where
  R := LinearIsometryEquiv.refl ℝ (SpaceTime B)
  t := t

/-- Translation of a real Schwartz function by a spacetime vector. -/
noncomputable def translate (B : EuclideanPlaneBackground) (v : SpaceTime B) :
    RealTestFunction B →L[ℝ] RealTestFunction B :=
  action (translationMotion B v)

/-- Translation of a complex Schwartz function by a spacetime vector. -/
noncomputable def translateComplex (B : EuclideanPlaneBackground) (v : SpaceTime B) :
    ComplexTestFunction B →L[ℝ] ComplexTestFunction B :=
  actionComplex (translationMotion B v)

/-- `translate` acts by precomposition with `x ↦ x - v`. -/
theorem translate_apply (B : EuclideanPlaneBackground) (v : SpaceTime B)
    (f : RealTestFunction B) (x : SpaceTime B) :
    translate B v f x = f (x - v) := by
  simp only [translate, action, SchwartzMap.compCLMOfAntilipschitz_apply,
    Function.comp_apply, inversePointAction, translationMotion]
  congr 1

/-- `translateComplex` acts by precomposition with `x ↦ x - v`. -/
theorem translateComplex_apply (B : EuclideanPlaneBackground) (v : SpaceTime B)
    (f : ComplexTestFunction B) (x : SpaceTime B) :
    translateComplex B v f x = f (x - v) := by
  simp only [translateComplex, actionComplex, SchwartzMap.compCLMOfAntilipschitz_apply,
    Function.comp_apply, inversePointAction, translationMotion]
  congr 1

end EuclideanPlaneBackground

/-- The canonical Euclidean plane background of dimension `d`. -/
abbrev planeBackground (d : ℕ) : EuclideanPlaneBackground where
  dim := d

/-- Euclidean spacetime `ℝ^d` used by continuum test functions. -/
abbrev ContinuumSpaceTime (d : ℕ) :=
  EuclideanPlaneBackground.SpaceTime (planeBackground d)

/-- Continuum real Schwartz test functions on `ℝ^d`. -/
abbrev ContinuumTestFunction (d : ℕ) :=
  EuclideanPlaneBackground.RealTestFunction (planeBackground d)

/-- Continuum complex Schwartz test functions on `ℝ^d`. -/
abbrev ContinuumComplexTestFunction (d : ℕ) :=
  EuclideanPlaneBackground.ComplexTestFunction (planeBackground d)

/-- Tempered distributions on `ℝ^d`. -/
abbrev ContinuumFieldConfig (d : ℕ) :=
  EuclideanPlaneBackground.Distribution (planeBackground d)

/-- Orthogonal group of `ℝ^d`. -/
abbrev ContinuumOrthogonalGroup (d : ℕ) :=
  EuclideanPlaneBackground.OrthogonalGroup (planeBackground d)

/-- Euclidean motions of `ℝ^d`. -/
abbrev ContinuumMotion (d : ℕ) :=
  EuclideanPlaneBackground.Motion (planeBackground d)

/-- Pull back a real Schwartz function on `ℝ^d` along a Euclidean motion. -/
noncomputable def continuumEuclideanAction {d : ℕ}
    (g : ContinuumMotion d) :
    ContinuumTestFunction d →L[ℝ] ContinuumTestFunction d :=
  EuclideanPlaneBackground.action g

/-- Pull back a complex Schwartz function on `ℝ^d` along a Euclidean motion. -/
noncomputable def continuumEuclideanActionComplex {d : ℕ}
    (g : ContinuumMotion d) :
    ContinuumComplexTestFunction d →L[ℝ] ContinuumComplexTestFunction d :=
  EuclideanPlaneBackground.actionComplex g

/-- Translation of a real Schwartz function by `v ∈ ℝ^d`. -/
noncomputable def schwartzTranslate (d : ℕ) (v : ContinuumSpaceTime d) :
    ContinuumTestFunction d →L[ℝ] ContinuumTestFunction d :=
  EuclideanPlaneBackground.translate (planeBackground d) v

/-- `schwartzTranslate` acts by precomposition with `x ↦ x - v`. -/
theorem schwartzTranslate_apply {d : ℕ} (v : ContinuumSpaceTime d)
    (f : ContinuumTestFunction d) (x : ContinuumSpaceTime d) :
    schwartzTranslate d v f x = f (x - v) :=
  EuclideanPlaneBackground.translate_apply (planeBackground d) v f x

end Pphi2
