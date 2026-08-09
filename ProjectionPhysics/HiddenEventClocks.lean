-- ProjectionPhysics — event order, mass-event filtering, and local clocks
--
-- A spatial event has no time field. It carries a mass outcome and a local
-- clock weight. The history order is primary; mass is a predicate on events,
-- while weighted clock accumulation models position/state-dependent discrete
-- proper-time increments without introducing a continuous time coordinate.

import ProjectionPhysics.HiddenOnlyHiggs

namespace ProjectionPhysics

structure HiddenSpatialEvent where
  location : HiddenPoint
  coupling : PureHiddenNumber
  fromState : PureHiddenNumber
  toState : PureHiddenNumber
  massSquared : Int
  mass_formula :
    massSquared = hiddenFlowMassSquared coupling fromState toState
  clockWeight : Nat

def isMassEvent (event : HiddenSpatialEvent) : Prop :=
  event.massSquared ≠ 0

abbrev HiddenEventHistory := List HiddenSpatialEvent

def eventCount (history : HiddenEventHistory) : Nat :=
  history.length

def massEventCount : HiddenEventHistory → Nat
  | [] => 0
  | event :: rest =>
      if event.massSquared = 0 then
        massEventCount rest
      else
        massEventCount rest + 1

def weightedClock : HiddenEventHistory → Nat
  | [] => 0
  | event :: rest => event.clockWeight + weightedClock rest

def eventDisplacement (event : HiddenSpatialEvent) : Int :=
  event.toState.value - event.fromState.value

def pathDisplacement : HiddenEventHistory → Int
  | [] => 0
  | event :: rest => eventDisplacement event + pathDisplacement rest

def hiddenPathSummary (history : HiddenEventHistory) : Int × Nat :=
  (pathDisplacement history, weightedClock history)

theorem event_count_append
    (left right : HiddenEventHistory) :
    eventCount (left ++ right) = eventCount left + eventCount right := by
  simp [eventCount]

theorem mass_event_count_append
    (left right : HiddenEventHistory) :
    massEventCount (left ++ right) =
      massEventCount left + massEventCount right := by
  induction left with
  | nil => simp [massEventCount]
  | cons head tail ih =>
      by_cases h : head.massSquared = 0
      · simp [massEventCount, h, ih]
      · simp [massEventCount, h, ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem mass_event_count_append_nonzero
    (history : HiddenEventHistory) (event : HiddenSpatialEvent)
    (hm : isMassEvent event) :
    massEventCount (history ++ [event]) = massEventCount history + 1 := by
  change event.massSquared ≠ 0 at hm
  rw [mass_event_count_append]
  simp [massEventCount, hm]

theorem mass_event_count_append_zero
    (history : HiddenEventHistory) (event : HiddenSpatialEvent)
    (hm : event.massSquared = 0) :
    massEventCount (history ++ [event]) = massEventCount history := by
  rw [mass_event_count_append]
  simp [massEventCount, hm]

theorem weighted_clock_append
    (left right : HiddenEventHistory) :
    weightedClock (left ++ right) =
      weightedClock left + weightedClock right := by
  induction left with
  | nil => simp [weightedClock]
  | cons head tail ih =>
      simp [weightedClock, ih, Nat.add_assoc]

theorem weighted_clock_append_event
    (history : HiddenEventHistory) (event : HiddenSpatialEvent) :
    weightedClock (history ++ [event]) =
      weightedClock history + event.clockWeight := by
  rw [weighted_clock_append]
  rfl

theorem path_displacement_append
    (left right : HiddenEventHistory) :
    pathDisplacement (left ++ right) =
      pathDisplacement left + pathDisplacement right := by
  induction left with
  | nil => simp [pathDisplacement]
  | cons head tail ih =>
      simp [pathDisplacement, ih, Int.add_assoc]

theorem hidden_path_summary_append
    (left right : HiddenEventHistory) :
    hiddenPathSummary (left ++ right) =
      (pathDisplacement left + pathDisplacement right,
        weightedClock left + weightedClock right) := by
  apply Prod.ext
  · exact path_displacement_append left right
  · exact weighted_clock_append left right

def withClockWeight
    (event : HiddenSpatialEvent) (weight : Nat) : HiddenSpatialEvent :=
  { event with clockWeight := weight }

theorem event_order_is_independent_of_mass_value
    (history : HiddenEventHistory) (event : HiddenSpatialEvent) :
    eventCount (history ++ [event]) = eventCount history + 1 := by
  simp [eventCount]

theorem mass_is_an_event_property
    (event : HiddenSpatialEvent) :
    isMassEvent event ↔ event.massSquared ≠ 0 := by
  rfl

theorem local_clock_weight_changes_clock_not_event_order
    (event : HiddenSpatialEvent) (a b : Nat) (h : a ≠ b) :
    eventCount [withClockWeight event a] = eventCount [withClockWeight event b] ∧
    weightedClock [withClockWeight event a] ≠
      weightedClock [withClockWeight event b] := by
  constructor
  · rfl
  · simpa [weightedClock, withClockWeight] using h

end ProjectionPhysics
