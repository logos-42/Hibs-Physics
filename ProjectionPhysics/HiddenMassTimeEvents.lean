-- ProjectionPhysics — mass-generation events and emergent discrete time
--
-- No event stores a time coordinate. A mass-generation history is a list of
-- spatial/kernel events, and its length is the emergent event time. The main
-- theorem proves synchronization: appending one mass event adds one unit.

import ProjectionPhysics.HiddenOnlyHiggs

namespace ProjectionPhysics

structure HiddenMassGenerationEvent where
  coupling : PureHiddenNumber
  fromState : PureHiddenNumber
  toState : PureHiddenNumber
  massSquared : Int
  mass_formula :
    massSquared = hiddenFlowMassSquared coupling fromState toState
  mass_nonzero : massSquared ≠ 0

def hiddenMassGenerationEvent
    (coupling fromState toState : PureHiddenNumber)
    (hm : hiddenFlowMassSquared coupling fromState toState ≠ 0) :
    HiddenMassGenerationEvent :=
  { coupling := coupling
    fromState := fromState
    toState := toState
    massSquared := hiddenFlowMassSquared coupling fromState toState
    mass_formula := rfl
    mass_nonzero := hm }

theorem hidden_mass_generation_event_has_mass_formula
    (event : HiddenMassGenerationEvent) :
    event.massSquared =
      hiddenFlowMassSquared event.coupling event.fromState event.toState := by
  exact event.mass_formula

abbrev HiddenMassHistory := List HiddenMassGenerationEvent

def emergentMassTime (history : HiddenMassHistory) : Nat :=
  history.length

theorem mass_generation_synchronizes_time
    (history : HiddenMassHistory) (event : HiddenMassGenerationEvent) :
    emergentMassTime (history ++ [event]) = emergentMassTime history + 1 := by
  simp [emergentMassTime]

theorem one_mass_generation_has_one_emergent_time_unit
    (event : HiddenMassGenerationEvent) :
    emergentMassTime [event] = 1 := by
  rfl

theorem mass_generation_time_is_additive
    (left right : HiddenMassHistory) :
    emergentMassTime (left ++ right) =
      emergentMassTime left + emergentMassTime right := by
  simp [emergentMassTime]

theorem mass_generation_synchronizes_nonzero_mass
    (event : HiddenMassGenerationEvent) :
    event.massSquared ≠ 0 ∧ emergentMassTime [event] = 1 := by
  exact ⟨event.mass_nonzero, one_mass_generation_has_one_emergent_time_unit event⟩

end ProjectionPhysics
