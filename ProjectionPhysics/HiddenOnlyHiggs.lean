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
  deriving DecidableEq

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

def hiddenProduct (x y : PureHiddenNumber) : PureHiddenNumber :=
  ⟨x.value * y.value⟩

def hiddenKernelInteraction
    (a b c : PureHiddenNumber) : Int :=
  hiddenKernelPairing (hiddenProduct a b) c

theorem hiddenKernelInteraction_formula
    (a b c : PureHiddenNumber) :
    hiddenKernelInteraction a b c = a.value * b.value * c.value := by
  simp [hiddenKernelInteraction, hiddenProduct, hiddenKernelPairing_formula,
    Int.mul_assoc]

structure HiddenCoupling where
  linear : PureHiddenNumber
  quadratic : PureHiddenNumber
  cubic : PureHiddenNumber

def hiddenCouplingResponse
    (coupling : HiddenCoupling) (fieldValue : PureHiddenNumber) : Int :=
  hiddenKernelPairing coupling.linear fieldValue +
    hiddenKernelPairing coupling.quadratic (hiddenProduct fieldValue fieldValue) +
    hiddenKernelPairing coupling.cubic
      (hiddenProduct (hiddenProduct fieldValue fieldValue) fieldValue)

theorem hiddenCouplingResponse_formula
    (coupling : HiddenCoupling) (fieldValue : PureHiddenNumber) :
    hiddenCouplingResponse coupling fieldValue =
      coupling.linear.value * fieldValue.value +
      coupling.quadratic.value * fieldValue.value * fieldValue.value +
      coupling.cubic.value * fieldValue.value * fieldValue.value * fieldValue.value := by
  simp [hiddenCouplingResponse, hiddenProduct, hiddenKernelPairing_formula,
    Int.mul_assoc, Int.add_assoc]

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

def hiddenMultiVacuumPotential
    (vacua : List PureHiddenNumber) (fieldValue : PureHiddenNumber) : Nat :=
  match vacua with
  | [] => 1
  | vacuum :: rest =>
      hiddenPotential vacuum fieldValue *
        hiddenMultiVacuumPotential rest fieldValue

theorem hidden_multi_vacuum_potential_nonnegative
    (vacua : List PureHiddenNumber) (fieldValue : PureHiddenNumber) :
    0 ≤ hiddenMultiVacuumPotential vacua fieldValue := by
  exact Nat.zero_le _

theorem hidden_multi_vacuum_potential_zero_of_mem
    (vacua : List PureHiddenNumber) (vacuum : PureHiddenNumber)
    (hv : vacuum ∈ vacua) :
    hiddenMultiVacuumPotential vacua vacuum = 0 := by
  induction vacua with
  | nil => cases hv
  | cons head tail ih =>
      simp only [List.mem_cons] at hv
      cases hv with
      | inl h =>
          cases h
          simp [hiddenMultiVacuumPotential, hiddenPotential]
      | inr h =>
          simp [hiddenMultiVacuumPotential, ih h]

theorem hidden_pm_vacua_are_multi_vacua
    (vacuum : PureHiddenNumber) :
    hiddenMultiVacuumPotential
        [vacuum, hiddenVacuumPartner vacuum] vacuum = 0 ∧
    hiddenMultiVacuumPotential
        [vacuum, hiddenVacuumPartner vacuum]
        (hiddenVacuumPartner vacuum) = 0 := by
  constructor
  · apply hidden_multi_vacuum_potential_zero_of_mem
    simp
  · apply hidden_multi_vacuum_potential_zero_of_mem
    simp

structure FiniteHiddenInterval where
  left : Int
  right : Int
  left_le_right : left ≤ right

def hiddenIntervalPoint (coordinate : Int) : HiddenPoint :=
  ⟨⟨coordinate⟩⟩

def inFiniteHiddenInterval
    (interval : FiniteHiddenInterval) (point : HiddenPoint) : Prop :=
  interval.left ≤ point.coordinate.value ∧
    point.coordinate.value ≤ interval.right

theorem hidden_interval_left_mem
    (interval : FiniteHiddenInterval) :
    inFiniteHiddenInterval interval (hiddenIntervalPoint interval.left) := by
  simp [inFiniteHiddenInterval, hiddenIntervalPoint]
  exact interval.left_le_right

theorem hidden_interval_right_mem
    (interval : FiniteHiddenInterval) :
    inFiniteHiddenInterval interval (hiddenIntervalPoint interval.right) := by
  simp [inFiniteHiddenInterval, hiddenIntervalPoint]
  exact interval.left_le_right

structure HiddenDirichletBoundary where
  interval : FiniteHiddenInterval
  field : StaticHiddenField
  leftValue : PureHiddenNumber
  rightValue : PureHiddenNumber
  left_condition :
    field (hiddenIntervalPoint interval.left) = leftValue
  right_condition :
    field (hiddenIntervalPoint interval.right) = rightValue

def constantHiddenBoundary
    (interval : FiniteHiddenInterval) (value : PureHiddenNumber) :
    HiddenDirichletBoundary :=
  { interval := interval
    field := hiddenVacuumField value
    leftValue := value
    rightValue := value
    left_condition := rfl
    right_condition := rfl }

theorem hidden_dirichlet_boundary_conditions_hold
    (boundary : HiddenDirichletBoundary) :
    boundary.field (hiddenIntervalPoint boundary.interval.left) =
        boundary.leftValue ∧
      boundary.field (hiddenIntervalPoint boundary.interval.right) =
        boundary.rightValue := by
  exact ⟨boundary.left_condition, boundary.right_condition⟩

end ProjectionPhysics
