import TorusEuler.InductiveUniformStageEstimates
import TorusEuler.InductiveLaterActivationJetBounds
import TorusEuler.LaterWavePrimaryPressureBound

/-! The frozen torus Euler theorem. -/

namespace TorusEuler

/-- The fixed leading pressure and activation costs of the actual later wave. -/
theorem nonempty_laterPrimaryCosts : Nonempty LaterPrimaryCosts := by
  obtain ⟨Apressure, Cpressure, _, hCpressure, hPressure⟩ :=
    InductiveEulerTip.SelectedLaterInput.exists_leading_pressure_hessian_bound
  obtain ⟨Aactivation, Cactivation, _, hCactivation, hActivation⟩ :=
    InductiveEulerTip.SelectedLaterInput.exists_activationPrimary_phaseJetBound
  exact ⟨
    { radiusFloor := max Apressure Aactivation
      pressureCost := Cpressure
      pressurePower := fun a => 2 * a + 74
      activationCost := Cactivation
      pressure_nonneg := hCpressure
      activation_nonneg := hCactivation
      pressure := fun d ha => hPressure d ((le_max_left _ _).trans ha)
      activation := fun d ha => hActivation d ((le_max_right _ _).trans ha) }⟩

/-- Theorem 1.1 of the frozen torus manuscript. -/
theorem theorem11 : Theorem11 :=
  theorem11_of_laterPrimaryCosts (Classical.choice nonempty_laterPrimaryCosts)

end TorusEuler
