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

end ProjectionPhysics
