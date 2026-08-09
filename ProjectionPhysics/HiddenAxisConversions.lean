-- ProjectionPhysics — reversible orthogonal conversions of the H/R/I axes
--
-- A scalar projection is not an inverse conversion: it forgets the other two
-- coordinates. This module formalizes the safer standard: convert the full
-- three-axis state by a bijective orthogonal map, with both inverse laws.

import ProjectionPhysics.HiddenSpacePhysics

namespace ProjectionPhysics

structure AxisCoordinates where
  hidden : Int
  real : Int
  imag : Int

def coordinatesOf (x : HiddenTriAxis) : AxisCoordinates :=
  ⟨x.hidden, x.real, x.imag⟩

def hiddenTriAxisOf (c : AxisCoordinates) : HiddenTriAxis :=
  ⟨c.hidden, c.real, c.imag⟩

theorem coordinates_roundtrip (x : HiddenTriAxis) :
    hiddenTriAxisOf (coordinatesOf x) = x := by
  rfl

theorem coordinates_roundtrip_back (c : AxisCoordinates) :
    coordinatesOf (hiddenTriAxisOf c) = c := by
  rfl

def swapHiddenReal (x : HiddenTriAxis) : HiddenTriAxis :=
  ⟨x.real, x.hidden, x.imag⟩

def swapRealImag (x : HiddenTriAxis) : HiddenTriAxis :=
  ⟨x.hidden, x.imag, x.real⟩

def swapImagHidden (x : HiddenTriAxis) : HiddenTriAxis :=
  ⟨x.imag, x.real, x.hidden⟩

theorem swapHiddenReal_involutive (x : HiddenTriAxis) :
    swapHiddenReal (swapHiddenReal x) = x := by
  rfl

theorem swapRealImag_involutive (x : HiddenTriAxis) :
    swapRealImag (swapRealImag x) = x := by
  rfl

theorem swapImagHidden_involutive (x : HiddenTriAxis) :
    swapImagHidden (swapImagHidden x) = x := by
  rfl

theorem swapHiddenReal_preserves_dot (x y : HiddenTriAxis) :
    triAxisDot (swapHiddenReal x) (swapHiddenReal y) = triAxisDot x y := by
  simp [swapHiddenReal, triAxisDot, Int.mul_comm, Int.add_comm,
    Int.add_left_comm] <;> omega

theorem swapRealImag_preserves_dot (x y : HiddenTriAxis) :
    triAxisDot (swapRealImag x) (swapRealImag y) = triAxisDot x y := by
  simp [swapRealImag, triAxisDot, Int.mul_comm, Int.add_comm,
    Int.add_left_comm] <;> omega

theorem swapImagHidden_preserves_dot (x y : HiddenTriAxis) :
    triAxisDot (swapImagHidden x) (swapImagHidden y) = triAxisDot x y := by
  simp [swapImagHidden, triAxisDot, Int.mul_comm, Int.add_comm,
    Int.add_left_comm] <;> omega

structure OrthogonalAxisConversion where
  forward : HiddenTriAxis → HiddenTriAxis
  backward : HiddenTriAxis → HiddenTriAxis
  left_inverse : ∀ x, backward (forward x) = x
  right_inverse : ∀ x, forward (backward x) = x
  preserves_dot : ∀ x y, triAxisDot (forward x) (forward y) = triAxisDot x y

def hiddenRealOrthogonalConversion : OrthogonalAxisConversion :=
  { forward := swapHiddenReal
    backward := swapHiddenReal
    left_inverse := swapHiddenReal_involutive
    right_inverse := swapHiddenReal_involutive
    preserves_dot := swapHiddenReal_preserves_dot }

def realImagOrthogonalConversion : OrthogonalAxisConversion :=
  { forward := swapRealImag
    backward := swapRealImag
    left_inverse := swapRealImag_involutive
    right_inverse := swapRealImag_involutive
    preserves_dot := swapRealImag_preserves_dot }

def imagHiddenOrthogonalConversion : OrthogonalAxisConversion :=
  { forward := swapImagHidden
    backward := swapImagHidden
    left_inverse := swapImagHidden_involutive
    right_inverse := swapImagHidden_involutive
    preserves_dot := swapImagHidden_preserves_dot }

theorem scalar_projection_has_no_inverse_without_axis_restriction :
    ∃ x y : HiddenTriAxis,
      x ≠ y ∧ realProjection x = realProjection y := by
  refine ⟨⟨0, 0, 0⟩, ⟨1, 0, 0⟩, ?_, ?_⟩
  · intro h
    have hh := congrArg HiddenTriAxis.hidden h
    simp at hh
  · rfl

theorem full_axis_conversion_has_inverse :
    ∀ x : HiddenTriAxis,
      hiddenRealOrthogonalConversion.backward
        (hiddenRealOrthogonalConversion.forward x) = x := by
  exact hiddenRealOrthogonalConversion.left_inverse

end ProjectionPhysics
