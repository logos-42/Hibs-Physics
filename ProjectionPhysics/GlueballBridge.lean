-- ProjectionPhysics — pure-glue composite and Higgs portal bridge
--
-- This module formalizes the first honest glueball layer:
--   pure gluon modes -> color-singlet proxy + gauge-invariant contract
--   -> pure-glue mass candidate -> 0++ Higgs portal -> mass matrix.
--
-- It deliberately does not claim a concrete SU(3) Yang-Mills construction.
-- `GaugeAction` is an explicit interface, and `colorBalance = 0` is a
-- minimal abelian proxy for a color-singlet condition. The purpose is to
-- prove the dependency structure before adding a richer color algebra.

import ProjectionPhysics.HiddenOnlyHiggs

namespace ProjectionPhysics

/-! ### G1. Gauge-invariant pure-glue composites -/

structure GaugeAction (State : Type) where
  symmetry : Type
  one : symmetry
  combine : symmetry → symmetry → symmetry
  act : symmetry → State → State
  act_one : ∀ x : State, act one x = x
  act_combine : ∀ (g h : symmetry) (x : State),
    act (combine g h) x = act g (act h x)

def GaugeInvariant {State : Type} (action : GaugeAction State) (x : State) : Prop :=
  ∀ g : action.symmetry, action.act g x = x

def identityGaugeAction (State : Type) : GaugeAction State :=
  { symmetry := Unit
    one := ()
    combine := fun _ _ => ()
    act := fun _ x => x
    act_one := by intro x; rfl
    act_combine := by intro g h x; rfl }

structure GluonMode where
  hidden : PureHiddenNumber
  colorCharge : Int

def colorBalance : List GluonMode → Int
  | [] => 0
  | mode :: rest => mode.colorCharge + colorBalance rest

/- A first color-singlet proxy: total abelianized color charge is zero. -/
structure GluonConfiguration where
  modes : List GluonMode
  color_singlet : colorBalance modes = 0

inductive GlueballChannel : Type where
  | scalar0pp
  | tensor2pp
  | pseudoscalar0mp
  deriving DecidableEq

structure Glueball where
  configuration : GluonConfiguration
  gaugeAction : GaugeAction GluonConfiguration
  gauge_invariant : GaugeInvariant gaugeAction configuration
  channel : GlueballChannel

theorem glueball_is_color_singlet (g : Glueball) :
    colorBalance g.configuration.modes = 0 := by
  exact g.configuration.color_singlet

theorem glueball_is_gauge_invariant (g : Glueball) :
    GaugeInvariant g.gaugeAction g.configuration := by
  exact g.gauge_invariant

def pairedScalarGlueball (a b : PureHiddenNumber) : Glueball :=
  { configuration :=
      { modes := [⟨a, 1⟩, ⟨b, -1⟩]
        color_singlet := by simp [colorBalance] }
    gaugeAction := identityGaugeAction GluonConfiguration
    gauge_invariant := by intro g; rfl
    channel := GlueballChannel.scalar0pp }

theorem paired_scalar_glueball_is_singlet
    (a b : PureHiddenNumber) :
    colorBalance (pairedScalarGlueball a b).configuration.modes = 0 := by
  exact glueball_is_color_singlet (pairedScalarGlueball a b)

/-! ### G2. Pure-glue field energy and mass candidate -/

def gluonModeEnergy (mode : GluonMode) : Nat :=
  Int.natAbs mode.hidden.value * Int.natAbs mode.hidden.value

def configurationFieldEnergy : List GluonMode → Nat
  | [] => 0
  | mode :: rest => gluonModeEnergy mode + configurationFieldEnergy rest

/- The kernel quadratic form supplies the scalar hidden-field energy proxy. -/
def pureGlueMassSquared (g : Glueball) : Int :=
  Int.ofNat (configurationFieldEnergy g.configuration.modes)

theorem gluon_mode_energy_positive
    (mode : GluonMode) (h : mode.hidden.value ≠ 0) :
    0 < gluonModeEnergy mode := by
  have hn0 : Int.natAbs mode.hidden.value ≠ 0 :=
    Int.natAbs_ne_zero.mpr h
  have hn : 0 < Int.natAbs mode.hidden.value := Nat.pos_of_ne_zero hn0
  exact Nat.mul_pos hn hn

theorem configuration_field_energy_positive_of_nonzero_mode
    (modes : List GluonMode) (mode : GluonMode)
    (hm : mode ∈ modes) (h : mode.hidden.value ≠ 0) :
    0 < configurationFieldEnergy modes := by
  induction modes with
  | nil => cases hm
  | cons head tail ih =>
      simp only [List.mem_cons] at hm
      cases hm with
      | inl heq =>
          cases heq
          have hp := gluon_mode_energy_positive mode h
          simp [configurationFieldEnergy]
          omega
      | inr htail =>
          have hp := ih htail
          simp [configurationFieldEnergy]
          omega

theorem pure_glue_mass_squared_nonzero_of_nonzero_mode
    (g : Glueball) (mode : GluonMode)
    (hm : mode ∈ g.configuration.modes) (h : mode.hidden.value ≠ 0) :
    pureGlueMassSquared g ≠ 0 := by
  have hp := configuration_field_energy_positive_of_nonzero_mode
    g.configuration.modes mode hm h
  simp [pureGlueMassSquared, Nat.ne_of_gt hp]

theorem pure_glue_mass_squared_is_nonnegative (g : Glueball) :
    0 ≤ pureGlueMassSquared g := by
  simp [pureGlueMassSquared]

/-! ### G3. The scalar Higgs portal -/

def portalMixing
    (portal vacuum overlap : PureHiddenNumber) : Int :=
  portal.value * vacuum.value * overlap.value

def glueballHiggsPortal
    (g : Glueball) (portal vacuum overlap : PureHiddenNumber) : Int :=
  if g.channel = GlueballChannel.scalar0pp then
    portalMixing portal vacuum overlap
  else
    0

theorem non_scalar_glueball_has_no_higgs_portal
    (g : Glueball) (hchannel : g.channel ≠ GlueballChannel.scalar0pp)
    (portal vacuum overlap : PureHiddenNumber) :
    glueballHiggsPortal g portal vacuum overlap = 0 := by
  simp [glueballHiggsPortal, hchannel]

theorem glueball_higgs_portal_zero_of_zero_coupling
    (g : Glueball) (vacuum overlap : PureHiddenNumber) :
    glueballHiggsPortal g ⟨0⟩ vacuum overlap = 0 := by
  by_cases hchannel : g.channel = GlueballChannel.scalar0pp
  · simp [glueballHiggsPortal, hchannel, portalMixing]
  · simp [glueballHiggsPortal, hchannel]

/-! ### G4. Glueball-Higgs mass matrix and decoupling -/

structure MassSquaredMatrix where
  glueball : Int
  mixing : Int
  higgs : Int

def glueballHiggsMassMatrix
    (g : Glueball) (portal vacuum overlap : PureHiddenNumber) :
    MassSquaredMatrix :=
  { glueball := pureGlueMassSquared g
    mixing := glueballHiggsPortal g portal vacuum overlap
    higgs := hiddenYukawaMassSquared portal vacuum }

def massMatrixAction
    (matrix : MassSquaredMatrix) (vector : Int × Int) : Int × Int :=
  (matrix.glueball * vector.1 + matrix.mixing * vector.2,
   matrix.mixing * vector.1 + matrix.higgs * vector.2)

def IsMassEigenpair
    (matrix : MassSquaredMatrix) (vector : Int × Int) (eigenvalue : Int) : Prop :=
  massMatrixAction matrix vector =
    (eigenvalue * vector.1, eigenvalue * vector.2)

theorem pure_glue_basis_is_eigenpair_when_decoupled
    (matrix : MassSquaredMatrix) (hmix : matrix.mixing = 0) :
    IsMassEigenpair matrix (1, 0) matrix.glueball := by
  unfold IsMassEigenpair massMatrixAction
  simp [hmix]

theorem higgs_basis_is_eigenpair_when_decoupled
    (matrix : MassSquaredMatrix) (hmix : matrix.mixing = 0) :
    IsMassEigenpair matrix (0, 1) matrix.higgs := by
  unfold IsMassEigenpair massMatrixAction
  simp [hmix]

theorem glueball_higgs_mass_matrix_decouples_when_higgs_off
    (g : Glueball) (vacuum overlap : PureHiddenNumber) :
    (glueballHiggsMassMatrix g ⟨0⟩ vacuum overlap).mixing = 0 := by
  simp [glueballHiggsMassMatrix, glueball_higgs_portal_zero_of_zero_coupling]

theorem pure_glue_survives_when_higgs_off
    (g : Glueball) (vacuum overlap : PureHiddenNumber) :
    (glueballHiggsMassMatrix g ⟨0⟩ vacuum overlap).glueball =
      pureGlueMassSquared g := by
  rfl

theorem pure_glue_is_mass_eigenstate_when_higgs_off
    (g : Glueball) (vacuum overlap : PureHiddenNumber) :
    IsMassEigenpair (glueballHiggsMassMatrix g ⟨0⟩ vacuum overlap)
      (1, 0) (pureGlueMassSquared g) := by
  apply pure_glue_basis_is_eigenpair_when_decoupled
  exact glueball_higgs_mass_matrix_decouples_when_higgs_off g vacuum overlap

theorem excited_glueball_stays_massive_when_higgs_off
    (g : Glueball) (mode : GluonMode)
    (hm : mode ∈ g.configuration.modes) (h : mode.hidden.value ≠ 0)
    (vacuum overlap : PureHiddenNumber) :
    (glueballHiggsMassMatrix g ⟨0⟩ vacuum overlap).glueball ≠ 0 := by
  rw [pure_glue_survives_when_higgs_off]
  exact pure_glue_mass_squared_nonzero_of_nonzero_mode g mode hm h

end ProjectionPhysics
