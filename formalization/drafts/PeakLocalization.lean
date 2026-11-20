import TorusEuler.ReferenceAmplitude
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Location of the actual transverse amplitude peak -/

open Set MeasureTheory

namespace TorusEuler.PeakLocalization

open ReferenceRiccati (x x_nonneg s s_pos s_sq_mul s_le_one hasDerivAt_s x_mul_s_lt_one
  rhs damping deviation referenceY referenceY_deviation hasDerivWithinAt_deviation
  riccati_deviation_bounds)
open ReferencePropagator (decay growingFactor growingFactor_pos)
open ReferenceAmplitude (kernel kernelIntegral kernel_bounds selectedV selectedV_pos
  peak_mem_window_of_signs)

noncomputable section

/-- The logarithmic rate of the selected seed. -/
def selectedRate (ε : ℝ) (Y : ℝ → ℝ) (t : ℝ) : ℝ :=
  Y t - kernel ε Y t / (1 - kernelIntegral ε Y t)

private theorem clock_square_identity (ε t : ℝ) :
    ε * x ε t = (ε * t) ^ 2 / 2 := by
  unfold x
  ring

private theorem referenceY_formula (ε t : ℝ) (Y : ℝ → ℝ) :
    Y t = s ε t * (1 + deviation ε Y t - (ε * t) * (x ε t * s ε t) / 2) := by
  calc
    Y t = referenceY ε (deviation ε Y) t := (congrFun (referenceY_deviation ε Y) t).symm
    _ = _ := by unfold referenceY damping; ring

private theorem referenceY_lower_of_clock {ε t z : ℝ} {Y : ℝ → ℝ}
    (hε : 0 ≤ ε) (ht : 0 ≤ t) (hz : ε * t ≤ z) (he : 0 ≤ deviation ε Y t) :
    (1 - z / 2) * s ε t ≤ Y t := by
  have hs := s_pos ε t
  have hxs := (x_mul_s_lt_one ε t).le
  have hprod : (ε * t) * (x ε t * s ε t) ≤ z :=
    (mul_le_of_le_one_right (mul_nonneg hε ht) hxs).trans hz
  rw [referenceY_formula]
  exact (mul_comm _ _).le.trans (mul_le_mul_of_nonneg_left (by linarith) hs.le)

private theorem s_ge_inv_one_add_x {ε t : ℝ} (hε : 0 ≤ ε) : (1 + x ε t)⁻¹ ≤ s ε t := by
  have hx := x_nonneg hε t
  have hroot : Real.sqrt (1 + x ε t ^ 2) ≤ 1 + x ε t :=
    (Real.sqrt_le_left (by positivity)).2 (by nlinarith)
  unfold s
  exact inv_anti₀ (Real.sqrt_pos.2 (by positivity)) hroot

private theorem s_le_inv_x {ε t : ℝ} (hx : 0 < x ε t) : s ε t ≤ (x ε t)⁻¹ := by
  have hroot : x ε t ≤ Real.sqrt (1 + x ε t ^ 2) := by
    apply (Real.le_sqrt (le_of_lt hx) (by positivity)).2
    linarith
  unfold s
  exact inv_anti₀ hx hroot

private theorem continuous_s (ε : ℝ) : Continuous (s ε) :=
  continuous_iff_continuousAt.2 (fun t => (hasDerivAt_s ε t).continuousAt)

private theorem integral_mono_right_of_nonneg {f : ℝ → ℝ} {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (hf : ContinuousOn f (Icc a c)) (hf₀ : ∀ t ∈ Icc a c, 0 ≤ f t) :
    (∫ r in a..b, f r) ≤ ∫ r in a..c, f r :=
  intervalIntegral.integral_mono_interval le_rfl hab hbc
    (ae_restrict_of_forall_mem measurableSet_Ioc (fun r hr => hf₀ r (Ioc_subset_Icc_self hr)))
    (hf.intervalIntegrable_of_Icc (hab.trans hbc))

private theorem decay_le_inv_thirtytwo {ε T t : ℝ} {Y : ℝ → ℝ}
    (hε : 0 < ε) (hε₁ : ε ≤ 1 / 20) (hY₀ : Y 0 = 1)
    (hY : ∀ r ∈ Icc 0 T, HasDerivWithinAt Y (rhs ε r (Y r)) (Icc 0 T) r)
    (ht : t ∈ Icc 0 T) (ht₃ : 3 ≤ t) :
    decay (s ε) (deviation ε Y) 0 t ≤ 1 / 32 := by
  let F (r : ℝ) := 2 * s ε r * (1 + deviation ε Y r)
  have hsub : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc_right ht.2
  have hsub₃ : Icc 0 3 ⊆ Icc 0 t := Icc_subset_Icc_right ht₃
  have heC : ContinuousOn (deviation ε Y) (Icc 0 T) :=
    HasDerivWithinAt.continuousOn (fun r hr => hasDerivWithinAt_deviation (hY r hr))
  have hC : ContinuousOn F (Icc 0 t) :=
    (continuousOn_const.mul (continuous_s ε).continuousOn).mul (continuousOn_const.add (heC.mono hsub))
  have he₀ (r : ℝ) (hr : r ∈ Icc 0 t) : 0 ≤ deviation ε Y r :=
    (riccati_deviation_bounds hε hY₀ hY r (hsub hr)).1
  have hF₀ (r : ℝ) (hr : r ∈ Icc 0 t) : 0 ≤ F r := by
    have := he₀ r hr
    have := s_pos ε r
    unfold F
    positivity
  have hF (r : ℝ) (hr : r ∈ Icc 0 3) : 5 / 3 ≤ F r := by
    have hx₀ := x_nonneg hε.le r
    have hr² := pow_le_pow_left₀ hr.1 hr.2 2
    have hx : x ε r ≤ 9 / 40 := by
      unfold x
      linarith [mul_le_mul hε₁ hr² (sq_nonneg r) (by norm_num : (0 : ℝ) ≤ 1 / 20)]
    have hroot : Real.sqrt (1 + x ε r ^ 2) ≤ 6 / 5 := by
      apply (Real.sqrt_le_left (by norm_num)).2
      nlinarith [pow_le_pow_left₀ hx₀ hx 2]
    have hs : 5 / 6 ≤ s ε r := by
      have h := inv_anti₀ (Real.sqrt_pos.2 (show (0 : ℝ) < 1 + x ε r ^ 2 by positivity)) hroot
      simpa [s] using h
    have hsd := s_pos ε r
    have he := he₀ r (hsub₃ hr)
    unfold F
    nlinarith [mul_nonneg hsd.le he]
  have hint := intervalIntegral.integral_mono_on (show (0 : ℝ) ≤ 3 by norm_num)
    (intervalIntegrable_const (μ := volume) (c := (5 / 3 : ℝ)))
    ((hC.mono hsub₃).intervalIntegrable_of_Icc (by norm_num)) hF
  have hrun : (5 : ℝ) ≤ ∫ r in 0..t, F r := by
    have h := hint.trans (integral_mono_right_of_nonneg (by norm_num) ht₃ hC hF₀)
    simpa [intervalIntegral.integral_const] using h
  have hexp : (32 : ℝ) ≤ Real.exp 5 := by
    have h := pow_le_pow_left₀ (show (0 : ℝ) ≤ 2 by norm_num) Real.exp_one_gt_two.le 5
    rw [← Real.exp_nat_mul] at h
    norm_num at h ⊢
    exact h
  have hsmall : Real.exp (-5) ≤ (1 : ℝ) / 32 := by
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ (by norm_num) hexp
  unfold decay
  exact (Real.exp_le_exp.mpr (neg_le_neg hrun)).trans hsmall

/-- The Riccati derivative is at least `s/10` on the left of the peak window. -/
theorem reference_left_margin {ε T t : ℝ} {Y : ℝ → ℝ}
    (hε : 0 < ε) (hY₀ : Y 0 = 1)
    (hY : ∀ r ∈ Icc 0 T, HasDerivWithinAt Y (rhs ε r (Y r)) (Icc 0 T) r)
    (ht : t ∈ Icc 0 T) (hleft : t ≤ 9 / (5 * ε)) : s ε t / 10 ≤ Y t := by
  have hz : ε * t ≤ 9 / 5 := by
    have h := (le_div_iff₀ (show 0 < (5 : ℝ) * ε by positivity)).1 hleft
    nlinarith
  have he := (riccati_deviation_bounds hε hY₀ hY t ht).1
  have h := referenceY_lower_of_clock hε.le ht.1 hz he
  linarith

/-- The selected seed grows at a uniform positive rate after the early cutoff
and before the left edge of the peak window. -/
theorem selected_left_margin {ε T t : ℝ} {Y : ℝ → ℝ}
    (hε : 0 < ε) (hε₁ : ε ≤ 1 / 20) (hY₀ : Y 0 = 1)
    (hY : ∀ r ∈ Icc 0 T, HasDerivWithinAt Y (rhs ε r (Y r)) (Icc 0 T) r)
    (ht : t ∈ Icc 0 T) (hleft : t ∈ Icc (1 / (4 * ε)) (9 / (5 * ε))) :
    ε / 100 ≤ selectedRate ε Y t := by
  have hs := s_pos ε t
  have ht₃ : 3 ≤ t := by
    apply le_trans ?_ hleft.1
    exact (le_div_iff₀ (by positivity)).2 (by linarith)
  have hD := decay_le_inv_thirtytwo hε hε₁ hY₀ hY ht ht₃
  have hK := kernel_bounds hε hY₀ hY ht
  have hh : 1 / 2 ≤ 1 - kernelIntegral ε Y t := by linarith [hK.2.2]
  have hh₀ : 0 < 1 - kernelIntegral ε Y t := by linarith
  have hsmall : kernel ε Y t / (1 - kernelIntegral ε Y t) ≤ s ε t / 16 := by
    apply (div_le_iff₀ hh₀).2
    unfold kernel
    have h₁ := mul_le_mul_of_nonneg_left hD hs.le
    have h₂ := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ s ε t / 16)
    linarith
  have hClock : ε * t ≤ 9 / 5 := by
    have h := (le_div_iff₀ (show 0 < (5 : ℝ) * ε by positivity)).1 hleft.2
    nlinarith
  have hx : ε * x ε t ≤ 81 / 50 := by
    rw [clock_square_identity]
    nlinarith [pow_le_pow_left₀ (mul_nonneg hε.le ht.1) hClock 2]
  have hscale : ε / 2 ≤ s ε t := by
    refine le_trans ?_ (s_ge_inv_one_add_x hε.le)
    rw [← one_div]
    apply (le_div_iff₀ (show 0 < 1 + x ε t by linarith [x_nonneg hε.le t])).2
    nlinarith
  unfold selectedRate
  linarith [reference_left_margin hε hY₀ hY ht hleft.2]

/-- The Riccati rate has a uniform inverse-age negative margin past the right
edge of the peak window. -/
theorem reference_right_margin {ε T t : ℝ} {Y : ℝ → ℝ}
    (hε : 0 < ε) (hε₁ : ε ≤ 1 / 20) (hY₀ : Y 0 = 1)
    (hY : ∀ r ∈ Icc 0 T, HasDerivWithinAt Y (rhs ε r (Y r)) (Icc 0 T) r)
    (ht : t ∈ Icc 0 T) (hright : 11 / (5 * ε) ≤ t) : t * Y t ≤ -(1 / 20) := by
  have hClock : 11 / 5 ≤ ε * t := by
    have h := (div_le_iff₀ (show 0 < (5 : ℝ) * ε by positivity)).1 hright
    nlinarith
  have hxs := x_nonneg hε.le t
  have hs := s_pos ε t
  have hx : 1 ≤ ε * x ε t := by
    rw [clock_square_identity]
    nlinarith [pow_le_pow_left₀ (show (0 : ℝ) ≤ 11 / 5 by norm_num) hClock 2]
  have hxpos : 0 < x ε t := by
    by_contra! h
    have := mul_nonpos_of_nonneg_of_nonpos hε.le h
    linarith
  have hscale : s ε t ≤ ε := (s_le_inv_x hxpos).trans (by rwa [inv_le_iff₀ hxpos, mul_comm])
  have htc : Real.sqrt (1 + x ε t ^ 2) = (s ε t)⁻¹ := by rw [s, inv_inv]
  have htBound : t * s ε t ≤ 10 / 11 := by
    have hprod : (11 / 5) * (t * s ε t) ≤ 2 := by
      calc
        _ ≤ (ε * t) * (t * s ε t) := mul_le_mul_of_nonneg_right hClock (mul_nonneg ht.1 hs.le)
        _ = 2 * (x ε t * s ε t) := by unfold x; ring
        _ ≤ 2 := by linarith [x_mul_s_lt_one ε t]
    linarith
  have he := riccati_deviation_bounds hε hY₀ hY t ht
  have hfirst : t * s ε t * (1 + deviation ε Y t) ≤ (10 / 11) * (161 / 160) :=
    mul_le_mul htBound (by linarith [he.2]) (by linarith [he.1]) (by norm_num)
  have hlast : 399 / 400 ≤ (x ε t * s ε t) ^ 2 := by
    have hsq := pow_le_pow_left₀ hs.le (hscale.trans hε₁) 2
    have hid : (x ε t * s ε t) ^ 2 = 1 - s ε t ^ 2 := by
      linear_combination s_sq_mul ε t
    linarith
  have hidentity : t * Y t = t * s ε t * (1 + deviation ε Y t) - (x ε t * s ε t) ^ 2 := by
    rw [referenceY_formula]
    unfold x
    ring
  rw [hidentity]
  linarith

/-- The selected seed inherits the negative margin, since its kernel term
only decreases the logarithmic rate. -/
theorem selected_right_margin {ε T t : ℝ} {Y : ℝ → ℝ}
    (hε : 0 < ε) (hε₁ : ε ≤ 1 / 20) (hY₀ : Y 0 = 1)
    (hY : ∀ r ∈ Icc 0 T, HasDerivWithinAt Y (rhs ε r (Y r)) (Icc 0 T) r)
    (ht : t ∈ Icc 0 T) (hright : 11 / (5 * ε) ≤ t) :
    selectedRate ε Y t ≤ -(1 / (20 * t)) := by
  have ht₀ : 0 < t := (by positivity : 0 < 11 / (5 * ε)).trans_le hright
  have hYle := (le_div_iff₀ ht₀).2 (by
    simpa only [mul_comm (Y t) t] using reference_right_margin hε hε₁ hY₀ hY ht hright)
  have hK := kernel_bounds hε hY₀ hY ht
  have hq : 0 ≤ kernel ε Y t / (1 - kernelIntegral ε Y t) :=
    div_nonneg hK.1.1.le (by linarith [hK.2.2])
  have hEq : -(1 / 20 : ℝ) / t = -(1 / (20 * t)) := by ring
  rw [← hEq]
  exact (sub_le_self _ hq).trans hYle

private theorem s_ge_div_x {ε t : ℝ} (hx : 4 ≤ x ε t) : (15 / 16) / x ε t ≤ s ε t := by
  have hx₀ : 0 < x ε t := by linarith
  have hroot : Real.sqrt (1 + x ε t ^ 2) ≤ (16 / 15) * x ε t := by
    apply (Real.sqrt_le_left (by positivity)).2
    nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4) hx 2]
  calc
    _ = ((16 / 15) * x ε t)⁻¹ := by field_simp
    _ ≤ _ := inv_anti₀ (Real.sqrt_pos.2 (by positivity)) hroot

private theorem intervalIntegrable_inv_sq {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun r : ℝ => (r ^ 2)⁻¹) volume a b :=
  ((continuousOn_id.pow 2).inv₀ (fun r hr => pow_ne_zero 2 (ha.trans_le hr.1).ne'))
    |>.intervalIntegrable_of_Icc hab

private theorem integral_inv_sq {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ r in a..b, (r ^ 2)⁻¹) = a⁻¹ - b⁻¹ := by
  have hd (r : ℝ) (hr : r ∈ Icc a b) : HasDerivAt (fun u : ℝ => -u⁻¹) ((r ^ 2)⁻¹) r := by
    simpa using (hasDerivAt_inv (ha.trans_le hr.1).ne').neg
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
    (fun r hr => (hd r hr).continuousAt.continuousWithinAt)
    (fun r hr => hd r (Ioo_subset_Icc_self hr)) (intervalIntegrable_inv_sq ha hab)
  simpa only [neg_sub_neg] using hFTC

/-- At normalized age `2/ε` the growing factor exceeds every early value
by at least `exp(15/4)`. -/
theorem early_reference_gap {ε T t : ℝ} {Y : ℝ → ℝ}
    (hε : 0 < ε) (hε₁ : ε ≤ 1 / 128) (hY₀ : Y 0 = 1)
    (hY : ∀ r ∈ Icc 0 T, HasDerivWithinAt Y (rhs ε r (Y r)) (Icc 0 T) r)
    (hT : 2 / ε ≤ T) (ht : t ∈ Icc 0 (1 / (4 * ε))) :
    Real.exp (15 / 4) * growingFactor Y t ≤ growingFactor Y (2 / ε) := by
  let a := 1 / (4 * ε)
  let b := 1 / (2 * ε)
  let c := 1 / ε
  let p := 2 / ε
  have ha : 0 < a := by dsimp [a]; positivity
  have hab : a ≤ b := div_le_div_of_nonneg_left zero_le_one (by positivity) (by linarith)
  have hbc : b ≤ c := div_le_div_of_nonneg_left zero_le_one hε (by linarith)
  have hcp : c ≤ p := div_le_div_of_nonneg_right (by norm_num) hε.le
  have hta : t ≤ a := ht.2
  have hb := ha.trans_le hab
  have hYc := HasDerivWithinAt.continuousOn hY
  have hI (u v : ℝ) (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ p) :
      IntervalIntegrable Y volume u v :=
    (hYc.mono (Icc_subset_Icc hu (hv.trans hT))).intervalIntegrable_of_Icc huv
  have hpos (r : ℝ) (hr : r ∈ Icc 0 p) : 0 ≤ Y r := by
    have hr' : r ∈ Icc 0 T := ⟨hr.1, hr.2.trans hT⟩
    have hz : ε * r ≤ 2 := by
      rw [mul_comm]
      exact (le_div_iff₀ hε).1 hr.2
    have hy := referenceY_lower_of_clock hε.le hr.1 hz
      (riccati_deviation_bounds hε hY₀ hY r hr').1
    norm_num at hy
    exact hy
  have hslow (r : ℝ) (hr : r ∈ Icc a p) : (15 / (8 * ε)) * (r ^ 2)⁻¹ ≤ s ε r := by
    have hr₀ := ha.trans_le hr.1
    have hz : 1 / 4 ≤ ε * r := by
      have h := (div_le_iff₀ (show 0 < (4 : ℝ) * ε by positivity)).1 hr.1
      nlinarith
    have hX : 4 ≤ x ε r := by
      have hh : 1 / 32 ≤ ε * x ε r := by
        rw [clock_square_identity]
        nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 4) hz 2]
      apply le_of_mul_le_mul_left _ hε
      linarith
    calc
      _ = (15 / 16) / x ε r := by
        unfold x
        field_simp [hε.ne', hr₀.ne']
        <;> ring
      _ ≤ _ := s_ge_div_x hX
  have hpoint (r z : ℝ) (hr : r ∈ Icc a p) (hz : ε * r ≤ z) (hz₂ : z ≤ 2) :
      (1 - z / 2) * (15 / (8 * ε)) * (r ^ 2)⁻¹ ≤ Y r := by
    have hr' : r ∈ Icc 0 T := ⟨ha.le.trans hr.1, hr.2.trans hT⟩
    have hslow' := mul_le_mul_of_nonneg_left (hslow r hr) (show 0 ≤ 1 - z / 2 by linarith)
    rw [← mul_assoc] at hslow'
    exact hslow'.trans (referenceY_lower_of_clock hε.le hr'.1 hz
      (riccati_deviation_bounds hε hY₀ hY r hr').1)
  have habBound (r : ℝ) (hr : r ∈ Icc a b) : (45 / (32 * ε)) * (r ^ 2)⁻¹ ≤ Y r := by
    have hz : ε * r ≤ 1 / 2 := by
      have h := (le_div_iff₀ (show 0 < (2 : ℝ) * ε by positivity)).1 hr.2
      nlinarith
    convert hpoint r (1 / 2) ⟨hr.1, hr.2.trans (hbc.trans hcp)⟩ hz (by norm_num) using 1
    norm_num
    ring
  have hbcBound (r : ℝ) (hr : r ∈ Icc b c) : (15 / (16 * ε)) * (r ^ 2)⁻¹ ≤ Y r := by
    have hz : ε * r ≤ 1 := by
      rw [mul_comm]
      exact (le_div_iff₀ hε).1 hr.2
    convert hpoint r 1 ⟨hab.trans hr.1, hr.2.trans hcp⟩ hz (by norm_num) using 1
    norm_num
    ring
  have hInt₁ : (45 / 16 : ℝ) ≤ ∫ r in a..b, Y r := by
    have h := intervalIntegral.integral_mono_on hab
      ((intervalIntegrable_inv_sq ha hab).const_mul (45 / (32 * ε)))
      (hI a b ha.le hab (hbc.trans hcp)) habBound
    rw [intervalIntegral.integral_const_mul, integral_inv_sq ha hab] at h
    have hEval : (45 / (32 * ε)) * (a⁻¹ - b⁻¹) = (45 / 16 : ℝ) := by
      dsimp [a, b]
      field_simp
    rwa [hEval] at h
  have hInt₂ : (15 / 16 : ℝ) ≤ ∫ r in b..c, Y r := by
    have h := intervalIntegral.integral_mono_on hbc
      ((intervalIntegrable_inv_sq hb hbc).const_mul (15 / (16 * ε)))
      (hI b c hb.le hbc hcp) hbcBound
    rw [intervalIntegral.integral_const_mul, integral_inv_sq hb hbc] at h
    have hEval : (15 / (16 * ε)) * (b⁻¹ - c⁻¹) = (15 / 16 : ℝ) := by
      dsimp [b, c]
      field_simp
    rwa [hEval] at h
  have hInt₃ : 0 ≤ ∫ r in c..p, Y r :=
    intervalIntegral.integral_nonneg hcp
      (fun r hr => hpos r ⟨(hb.le.trans hbc).trans hr.1, hr.2⟩)
  have hInt₀ : 0 ≤ ∫ r in t..a, Y r :=
    intervalIntegral.integral_nonneg hta
      (fun r hr => hpos r ⟨ht.1.trans hr.1, hr.2.trans (hab.trans (hbc.trans hcp))⟩)
  have hcat₀ := intervalIntegral.integral_add_adjacent_intervals
    (hI 0 t le_rfl ht.1 (hta.trans (hab.trans (hbc.trans hcp))))
    (hI t a ht.1 hta (hab.trans (hbc.trans hcp)))
  have hcat₁ := intervalIntegral.integral_add_adjacent_intervals
    (hI 0 a le_rfl ha.le (hab.trans (hbc.trans hcp))) (hI a b ha.le hab (hbc.trans hcp))
  have hcat₂ := intervalIntegral.integral_add_adjacent_intervals
    (hI 0 b le_rfl hb.le (hbc.trans hcp)) (hI b c hb.le hbc hcp)
  have hcat₃ := intervalIntegral.integral_add_adjacent_intervals
    (hI 0 c le_rfl (hb.le.trans hbc) hcp) (hI c p (hb.le.trans hbc) hcp le_rfl)
  change Real.exp (15 / 4) * growingFactor Y t ≤ growingFactor Y p
  unfold growingFactor
  rw [← Real.exp_add]
  exact Real.exp_le_exp.mpr (by linarith)

end

end TorusEuler.PeakLocalization
