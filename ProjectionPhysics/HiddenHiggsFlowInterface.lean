-- ProjectionPhysics — an optional flow interface for the hidden Higgs model
--
-- This file is intentionally separate from HiddenOnlyHiggs.lean.
-- `HiddenFlowParameter` is an external algebraic index, not time. The static
-- model remains unchanged when this optional interface is not imported.

import ProjectionPhysics.HiddenOnlyHiggs

namespace ProjectionPhysics

/-! ### HOH3. An optional flow parameter, explicitly not identified with time -/

structure HiddenFlowParameter where
  step : Nat

abbrev FlowIndexedHiddenField :=
  HiddenPoint → HiddenFlowParameter → PureHiddenNumber

structure HiddenFlowInterface where
  baseField : StaticHiddenField
  fieldAt : FlowIndexedHiddenField
  at_zero : ∀ point : HiddenPoint,
    fieldAt point ⟨0⟩ = baseField point

def frozenHiddenFlow (field : StaticHiddenField) : FlowIndexedHiddenField :=
  fun point _ => field point

def frozenHiddenFlowInterface
    (field : StaticHiddenField) : HiddenFlowInterface :=
  { baseField := field
    fieldAt := frozenHiddenFlow field
    at_zero := by intro point; rfl }

theorem frozen_hidden_flow_is_static
    (field : StaticHiddenField) (point : HiddenPoint)
    (parameter : HiddenFlowParameter) :
    frozenHiddenFlow field point parameter = field point := by
  rfl

def hiddenFlowDisplacement
    (flow : FlowIndexedHiddenField) (point : HiddenPoint)
    (a b : HiddenFlowParameter) : Nat :=
  Int.natAbs ((flow point a).value - (flow point b).value)

theorem frozen_hidden_flow_has_zero_displacement
    (field : StaticHiddenField) (point : HiddenPoint)
    (a b : HiddenFlowParameter) :
    hiddenFlowDisplacement (frozenHiddenFlow field) point a b = 0 := by
  simp [hiddenFlowDisplacement, frozenHiddenFlow]

theorem hidden_flow_interface_preserves_static_base
    (extension : HiddenFlowInterface) (point : HiddenPoint) :
    extension.fieldAt point ⟨0⟩ = extension.baseField point := by
  exact extension.at_zero point

/-! ### HOH3. A testable discrete relaxation law -/

def hiddenRelaxationStep
    (vacuum : PureHiddenNumber) (field : StaticHiddenField) :
    StaticHiddenField :=
  fun point => if field point = vacuum then field point else vacuum

def hiddenRelaxationFlow
    (vacuum : PureHiddenNumber) (field : StaticHiddenField) :
    FlowIndexedHiddenField :=
  fun point parameter =>
    if parameter.step = 0 then field point else vacuum

def hiddenRelaxationInterface
    (vacuum : PureHiddenNumber) (field : StaticHiddenField) :
    HiddenFlowInterface :=
  { baseField := field
    fieldAt := hiddenRelaxationFlow vacuum field
    at_zero := by intro point; simp [hiddenRelaxationFlow] }

theorem hidden_relaxation_zero_step
    (vacuum : PureHiddenNumber) (field : StaticHiddenField)
    (point : HiddenPoint) :
    hiddenRelaxationFlow vacuum field point ⟨0⟩ = field point := by
  simp [hiddenRelaxationFlow]

theorem hidden_relaxation_positive_step
    (vacuum : PureHiddenNumber) (field : StaticHiddenField)
    (point : HiddenPoint) (step : Nat) :
    hiddenRelaxationFlow vacuum field point ⟨step + 1⟩ = vacuum := by
  simp [hiddenRelaxationFlow]

theorem hidden_relaxation_step_is_idempotent
    (vacuum : PureHiddenNumber) (field : StaticHiddenField)
    (point : HiddenPoint) :
    hiddenRelaxationStep vacuum
        (hiddenRelaxationStep vacuum field) point =
      hiddenRelaxationStep vacuum field point := by
  by_cases h : field point = vacuum
  · simp [hiddenRelaxationStep, h]
  · simp [hiddenRelaxationStep, h]

/-! ### HOH4. Evolution along the hidden spatial coordinate -/

def hiddenShiftPoint
    (displacement : PureHiddenNumber) (point : HiddenPoint) : HiddenPoint :=
  ⟨⟨point.coordinate.value + displacement.value⟩⟩

def hiddenSpatialShiftField
    (field : StaticHiddenField) (displacement : PureHiddenNumber) :
    StaticHiddenField :=
  fun point => field (hiddenShiftPoint displacement point)

theorem hidden_shift_point_composes_additively
    (a b : PureHiddenNumber) (point : HiddenPoint) :
    hiddenShiftPoint b (hiddenShiftPoint a point) =
      hiddenShiftPoint ⟨a.value + b.value⟩ point := by
  cases point with
  | mk coordinate =>
      cases coordinate with
      | mk p =>
          cases a with
          | mk av =>
              cases b with
              | mk bv =>
                  simp [hiddenShiftPoint]
                  omega

theorem hidden_shift_zero_is_identity
    (field : StaticHiddenField) (point : HiddenPoint) :
    hiddenSpatialShiftField field ⟨0⟩ point = field point := by
  simp [hiddenSpatialShiftField, hiddenShiftPoint]

theorem hidden_shift_composes_additively
    (field : StaticHiddenField)
    (a b : PureHiddenNumber) (point : HiddenPoint) :
    hiddenSpatialShiftField
        (hiddenSpatialShiftField field a) b point =
      hiddenSpatialShiftField field
        ⟨a.value + b.value⟩ point := by
  unfold hiddenSpatialShiftField
  rw [hidden_shift_point_composes_additively]
  simp [hiddenShiftPoint, Int.add_comm]

def hiddenSpatialEvolutionMassSquared
    (coupling : PureHiddenNumber) (field : StaticHiddenField)
    (displacement : PureHiddenNumber) (point : HiddenPoint) : Int :=
  hiddenFieldFlowMassSquared coupling field point
    (hiddenShiftPoint displacement point)

theorem hidden_spatial_evolution_of_vacuum_has_zero_mass
    (coupling vacuum displacement : PureHiddenNumber)
    (point : HiddenPoint) :
    hiddenSpatialEvolutionMassSquared coupling
      (hiddenVacuumField vacuum) displacement point = 0 := by
  simp [hiddenSpatialEvolutionMassSquared, hiddenFieldFlowMassSquared,
    hiddenFieldFlow, hiddenVacuumField, hiddenProduct,
    hiddenKernelQuadratic, hiddenKernelPairing_formula]

end ProjectionPhysics
