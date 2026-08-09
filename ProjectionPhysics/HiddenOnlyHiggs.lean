-- ProjectionPhysics — a time-free, hidden-only Higgs model
--
-- This module deliberately uses only HIBS hidden-tagged values and a hidden
-- spatial coordinate. It does not introduce real/imaginary axes, time,
-- derivatives, velocities, a metric, or a spacetime signature.
--
-- The construction is a static algebraic Higgs analogue:
--   hidden vacuum value -> hidden-only static field -> hidden potential
--   hidden coupling × hidden vacuum value -> nonnegative mass index.
-- These are explicit model definitions, not consequences of HIBS A1-A3.

import ProjectionPhysics.HIBSPhysicalBridges
import ProjectionPhysics.ProjectionAlgebra

namespace ProjectionPhysics

structure PureHiddenNumber where
  value : Int

/-! ### HOH1. The hidden scalar as a kernel direction -/

def hiddenKernelEmbedding (h : PureHiddenNumber) : KernelOf reProj :=
  ⟨⟨0, h.value⟩, by rfl⟩

theorem hiddenKernelEmbedding_is_kernel (h : PureHiddenNumber) :
    (hiddenKernelEmbedding h).val.re = 0 := by
  rfl

def hiddenKernelPairing
    (x y : PureHiddenNumber) : Int :=
  cKernelBiForm.B (hiddenKernelEmbedding x).val (hiddenKernelEmbedding y).val

theorem hiddenKernelPairing_formula
    (x y : PureHiddenNumber) :
    hiddenKernelPairing x y = x.value * y.value := by
  simp [hiddenKernelPairing, hiddenKernelEmbedding, cKernelBiForm]

def hiddenKernelQuadratic (h : PureHiddenNumber) : Int :=
  hiddenKernelPairing h h

theorem hiddenKernelQuadratic_formula (h : PureHiddenNumber) :
    hiddenKernelQuadratic h = h.value * h.value := by
  simp [hiddenKernelQuadratic, hiddenKernelPairing_formula]

def hiddenTagged (h : PureHiddenNumber) : HibsState :=
  ⟨h.value, HibsTag.hidden⟩

theorem hiddenTagged_is_hidden (h : PureHiddenNumber) :
    (hiddenTagged h).tag = HibsTag.hidden := by
  rfl

structure HiddenPoint where
  coordinate : PureHiddenNumber

abbrev StaticHiddenField := HiddenPoint → PureHiddenNumber

def hiddenVacuumField (vacuum : PureHiddenNumber) : StaticHiddenField :=
  fun _ => vacuum

def hiddenPotential (vacuum fieldValue : PureHiddenNumber) : Nat :=
  Int.natAbs
    (fieldValue.value * fieldValue.value - vacuum.value * vacuum.value)

theorem hidden_potential_nonnegative
    (vacuum fieldValue : PureHiddenNumber) :
    0 ≤ hiddenPotential vacuum fieldValue := by
  exact Nat.zero_le _

theorem hidden_vacuum_potential_zero
    (vacuum : PureHiddenNumber) (point : HiddenPoint) :
    hiddenPotential vacuum (hiddenVacuumField vacuum point) = 0 := by
  simp [hiddenPotential, hiddenVacuumField]

def hiddenSpatialVariation
    (field : StaticHiddenField) (x y : HiddenPoint) : Nat :=
  Int.natAbs ((field x).value - (field y).value)

theorem hidden_vacuum_has_zero_spatial_variation
    (vacuum : PureHiddenNumber) (x y : HiddenPoint) :
    hiddenSpatialVariation (hiddenVacuumField vacuum) x y = 0 := by
  simp [hiddenSpatialVariation, hiddenVacuumField]

structure StaticHiddenHiggsModel where
  vacuum : PureHiddenNumber
  field : StaticHiddenField
  is_vacuum_field : field = hiddenVacuumField vacuum

def staticHiddenHiggs (vacuum : PureHiddenNumber) : StaticHiddenHiggsModel :=
  { vacuum := vacuum
    field := hiddenVacuumField vacuum
    is_vacuum_field := rfl }

def hiddenPotentialAt
    (model : StaticHiddenHiggsModel) (point : HiddenPoint) : Nat :=
  hiddenPotential model.vacuum (model.field point)

theorem static_hidden_higgs_is_at_zero_potential
    (model : StaticHiddenHiggsModel) (point : HiddenPoint) :
    hiddenPotentialAt model point = 0 := by
  rw [hiddenPotentialAt, model.is_vacuum_field]
  exact hidden_vacuum_potential_zero model.vacuum point

def hiddenYukawaMass
    (coupling vacuum : PureHiddenNumber) : Nat :=
  Int.natAbs (coupling.value * vacuum.value)

def hiddenYukawaMassSquared
    (coupling vacuum : PureHiddenNumber) : Int :=
  hiddenKernelQuadratic ⟨coupling.value * vacuum.value⟩

theorem hidden_yukawa_mass_squared_formula
    (coupling vacuum : PureHiddenNumber) :
    hiddenYukawaMassSquared coupling vacuum =
      (coupling.value * vacuum.value) *
        (coupling.value * vacuum.value) := by
  simp [hiddenYukawaMassSquared, hiddenKernelQuadratic_formula]

theorem hidden_yukawa_mass_squared_is_kernel_form
    (coupling vacuum : PureHiddenNumber) :
    hiddenYukawaMassSquared coupling vacuum =
      hiddenKernelPairing ⟨coupling.value * vacuum.value⟩
        ⟨coupling.value * vacuum.value⟩ := by
  rfl

theorem hidden_yukawa_mass_index_is_kernel_magnitude
    (coupling vacuum : PureHiddenNumber) :
    Int.natAbs (hiddenYukawaMassSquared coupling vacuum) =
      hiddenYukawaMass coupling vacuum * hiddenYukawaMass coupling vacuum := by
  simp [hiddenYukawaMassSquared, hiddenKernelQuadratic,
    hiddenKernelPairing_formula, hiddenYukawaMass, Int.natAbs_mul]

theorem hidden_yukawa_mass_squared_zero_of_zero_coupling
    (vacuum : PureHiddenNumber) :
    hiddenYukawaMassSquared ⟨0⟩ vacuum = 0 := by
  simp [hiddenYukawaMassSquared, hiddenKernelQuadratic_formula]

theorem hidden_yukawa_mass_squared_nonzero
    (coupling vacuum : PureHiddenNumber)
    (hc : coupling.value ≠ 0) (hv : vacuum.value ≠ 0) :
    hiddenYukawaMassSquared coupling vacuum ≠ 0 := by
  rw [hidden_yukawa_mass_squared_formula]
  exact Int.mul_ne_zero (Int.mul_ne_zero hc hv) (Int.mul_ne_zero hc hv)

theorem hidden_yukawa_mass_formula (coupling vacuum : PureHiddenNumber) :
    hiddenYukawaMass coupling vacuum =
      Int.natAbs (coupling.value * vacuum.value) := by
  rfl

theorem hidden_yukawa_mass_zero_of_zero_coupling
    (vacuum : PureHiddenNumber) :
    hiddenYukawaMass ⟨0⟩ vacuum = 0 := by
  simp [hiddenYukawaMass]

theorem hidden_yukawa_mass_zero_of_zero_vacuum
    (coupling : PureHiddenNumber) :
    hiddenYukawaMass coupling ⟨0⟩ = 0 := by
  simp [hiddenYukawaMass]

theorem hidden_yukawa_mass_nonzero
    (coupling vacuum : PureHiddenNumber)
    (hc : coupling.value ≠ 0) (hv : vacuum.value ≠ 0) :
    hiddenYukawaMass coupling vacuum ≠ 0 := by
  intro h
  have hproduct : coupling.value * vacuum.value = 0 := by
    exact Int.natAbs_eq_zero.mp h
  rcases Int.mul_eq_zero.mp hproduct with hc' | hv'
  · exact hc hc'
  · exact hv hv'

theorem hidden_higgs_mass_bridge
    (coupling vacuum : PureHiddenNumber)
    (hc : coupling.value ≠ 0) (hv : vacuum.value ≠ 0) :
    (hiddenTagged vacuum).tag = HibsTag.hidden ∧
    hiddenPotential vacuum vacuum = 0 ∧
    hiddenYukawaMass coupling vacuum ≠ 0 := by
  refine ⟨hiddenTagged_is_hidden vacuum, ?_, ?_⟩
  · simp [hiddenPotential]
  · exact hidden_yukawa_mass_nonzero coupling vacuum hc hv

theorem static_hidden_model_has_no_time_coordinate :
    ∃ (model : StaticHiddenHiggsModel),
      ∀ (point : HiddenPoint), hiddenPotentialAt model point = 0 := by
  refine ⟨staticHiddenHiggs ⟨1⟩, ?_⟩
  intro point
  exact static_hidden_higgs_is_at_zero_potential (staticHiddenHiggs ⟨1⟩) point

/-! ### HOH2. Static defects, boundaries, and vacuum degeneracy -/

def hiddenOrigin : HiddenPoint :=
  ⟨⟨0⟩⟩

def hiddenUnitPoint : HiddenPoint :=
  ⟨⟨1⟩⟩

def hiddenDefectField
    (vacuum defect : PureHiddenNumber) : StaticHiddenField :=
  fun point => if point.coordinate.value = 0 then defect else vacuum

def hiddenBoundary
    (field : StaticHiddenField) (x y : HiddenPoint) : Prop :=
  hiddenSpatialVariation field x y ≠ 0

theorem hidden_defect_is_boundary
    (vacuum defect : PureHiddenNumber)
    (hd : defect.value ≠ vacuum.value) :
    hiddenBoundary (hiddenDefectField vacuum defect)
      hiddenOrigin hiddenUnitPoint := by
  unfold hiddenBoundary hiddenSpatialVariation
  apply Int.natAbs_ne_zero.mpr
  simp [hiddenDefectField, hiddenOrigin, hiddenUnitPoint]
  omega

theorem hidden_defect_is_vacuum_away_from_origin
    (vacuum defect : PureHiddenNumber) (point : HiddenPoint)
    (hp : point.coordinate.value ≠ 0) :
    hiddenDefectField vacuum defect point = vacuum := by
  simp [hiddenDefectField, hp]

def hiddenVacuumPartner (vacuum : PureHiddenNumber) : PureHiddenNumber :=
  ⟨-vacuum.value⟩

theorem hidden_vacuum_partner_has_zero_potential
    (vacuum : PureHiddenNumber) (point : HiddenPoint) :
    hiddenPotential vacuum (hiddenVacuumPartner vacuum) = 0 := by
  simp [hiddenPotential, hiddenVacuumPartner, Int.neg_mul_neg]

theorem hidden_vacua_are_distinct
    (vacuum : PureHiddenNumber) (hv : vacuum.value ≠ 0) :
    vacuum ≠ hiddenVacuumPartner vacuum := by
  intro h
  have hvalue := congrArg PureHiddenNumber.value h
  simp [hiddenVacuumPartner] at hvalue
  omega

end ProjectionPhysics
