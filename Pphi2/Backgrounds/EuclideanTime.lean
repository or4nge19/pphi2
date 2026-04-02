/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Michael R. Douglas

# Euclidean Time Structures

This file adds a second foundational layer above
`Pphi2.Backgrounds.EuclideanPlane`: a Euclidean background together with a
distinguished time-reflection structure and a positive-time region.

The idea is that reflection positivity should depend on a genuine
geometric object, not on route-local ad hoc definitions sitting inside the
OS axiom file.
-/

import Pphi2.Backgrounds.EuclideanPlane

noncomputable section

namespace Pphi2

/-- A Euclidean background equipped with time reflection and a positive-time
region. -/
structure EuclideanTimeStructure (B : EuclideanPlaneBackground) where
  reflect : EuclideanPlaneBackground.SpaceTime B →ₗ[ℝ]
    EuclideanPlaneBackground.SpaceTime B
  reflect_involutive : Function.Involutive reflect
  timeAxis : ℝ →ₗ[ℝ] EuclideanPlaneBackground.SpaceTime B
  positiveTimeSet : Set (EuclideanPlaneBackground.SpaceTime B)

namespace EuclideanTimeStructure

/-- The time reflection as a continuous linear equivalence. -/
noncomputable def reflectCLE {B : EuclideanPlaneBackground}
    (T : EuclideanTimeStructure B) :
    EuclideanPlaneBackground.SpaceTime B ≃L[ℝ]
      EuclideanPlaneBackground.SpaceTime B :=
  (LinearEquiv.ofInvolutive T.reflect T.reflect_involutive).toContinuousLinearEquiv

/-- Pull back real test functions along time reflection. -/
noncomputable def reflectOnRealTestFunctions {B : EuclideanPlaneBackground}
    (T : EuclideanTimeStructure B) :
    EuclideanPlaneBackground.RealTestFunction B →L[ℝ]
      EuclideanPlaneBackground.RealTestFunction B :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℝ T.reflectCLE

/-- Pull back complex test functions along time reflection. -/
noncomputable def reflectOnComplexTestFunctions {B : EuclideanPlaneBackground}
    (T : EuclideanTimeStructure B) :
    EuclideanPlaneBackground.ComplexTestFunction B →L[ℝ]
      EuclideanPlaneBackground.ComplexTestFunction B :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℝ T.reflectCLE

/-- The distinguished time-translation vector at parameter `t`. -/
def timeTranslation {B : EuclideanPlaneBackground}
    (T : EuclideanTimeStructure B) (t : ℝ) :
    EuclideanPlaneBackground.SpaceTime B :=
  T.timeAxis t

/-- Shift a spacetime point by the distinguished time-translation vector. -/
def timeShift {B : EuclideanPlaneBackground}
    (T : EuclideanTimeStructure B) (t : ℝ) :
    EuclideanPlaneBackground.SpaceTime B → EuclideanPlaneBackground.SpaceTime B :=
  fun x => x + T.timeTranslation t

@[simp] theorem timeShift_apply {B : EuclideanPlaneBackground}
    (T : EuclideanTimeStructure B) (t : ℝ)
    (x : EuclideanPlaneBackground.SpaceTime B) :
    T.timeShift t x = x + T.timeTranslation t :=
  rfl

@[simp] theorem timeShift_zero {B : EuclideanPlaneBackground}
    (T : EuclideanTimeStructure B)
    (x : EuclideanPlaneBackground.SpaceTime B) :
    T.timeShift 0 x = x := by
  simp [timeShift, timeTranslation]

theorem timeShift_add {B : EuclideanPlaneBackground}
    (T : EuclideanTimeStructure B) (s t : ℝ)
    (x : EuclideanPlaneBackground.SpaceTime B) :
    T.timeShift (s + t) x = T.timeShift s (T.timeShift t x) := by
  simp [timeShift, timeTranslation, add_left_comm, add_comm]

/-- Pull back real test functions along time translation. -/
noncomputable def timeTranslateOnRealTestFunctions {B : EuclideanPlaneBackground}
    (T : EuclideanTimeStructure B) (t : ℝ) :
    EuclideanPlaneBackground.RealTestFunction B →L[ℝ]
      EuclideanPlaneBackground.RealTestFunction B :=
  EuclideanPlaneBackground.translate B (-T.timeTranslation t)

@[simp] theorem timeTranslateOnRealTestFunctions_apply {B : EuclideanPlaneBackground}
    (T : EuclideanTimeStructure B) (t : ℝ)
    (f : EuclideanPlaneBackground.RealTestFunction B)
    (x : EuclideanPlaneBackground.SpaceTime B) :
    T.timeTranslateOnRealTestFunctions t f x = f (T.timeShift t x) := by
  simp [timeTranslateOnRealTestFunctions, timeShift, EuclideanPlaneBackground.translate_apply,
    sub_eq_add_neg]

/-- Pull back complex test functions along time translation. -/
noncomputable def timeTranslateOnComplexTestFunctions {B : EuclideanPlaneBackground}
    (T : EuclideanTimeStructure B) (t : ℝ) :
    EuclideanPlaneBackground.ComplexTestFunction B →L[ℝ]
      EuclideanPlaneBackground.ComplexTestFunction B :=
  EuclideanPlaneBackground.translateComplex B (-T.timeTranslation t)

@[simp] theorem timeTranslateOnComplexTestFunctions_apply {B : EuclideanPlaneBackground}
    (T : EuclideanTimeStructure B) (t : ℝ)
    (f : EuclideanPlaneBackground.ComplexTestFunction B)
    (x : EuclideanPlaneBackground.SpaceTime B) :
    T.timeTranslateOnComplexTestFunctions t f x = f (T.timeShift t x) := by
  simp [timeTranslateOnComplexTestFunctions, timeShift,
    EuclideanPlaneBackground.translateComplex_apply, sub_eq_add_neg]

/-- The submodule of real test functions supported in the positive-time
region. -/
def positiveTimeSubmodule {B : EuclideanPlaneBackground}
    (T : EuclideanTimeStructure B) :
    Submodule ℝ (EuclideanPlaneBackground.RealTestFunction B) where
  carrier := {f | tsupport f ⊆ T.positiveTimeSet}
  zero_mem' := by
    simp only [Set.mem_setOf_eq, tsupport]
    exact
      (closure_minimal Function.support_zero.subset isClosed_empty).trans
        (Set.empty_subset _)
  add_mem' := fun {f g} hf hg =>
    (tsupport_add f g).trans (Set.union_subset hf hg)
  smul_mem' := fun c f hf =>
    (tsupport_smul_subset_right (fun _ : EuclideanPlaneBackground.SpaceTime B => c) f).trans hf

end EuclideanTimeStructure

end Pphi2
