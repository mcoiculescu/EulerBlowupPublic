import TorusEuler.LinearFlowExistence
import TorusEuler.TorusLabelFlow

open Asymptotics Filter Set
open scoped NNReal Topology

namespace TorusEuler

/-- The periodic velocity perturbed in a real parameter has a family of
pointwise flows on the same closed slab. -/
theorem exists_perturbedLabelFlows {U b : Velocity} {l r : ℝ} (hlr : l < r)
    (hU : ContDiffOn ℝ 1 (Function.uncurry U) (Icc l r ×ˢ (univ : Set Vec3)))
    (hb : ContDiffOn ℝ 1 (Function.uncurry b) (Icc l r ×ˢ (univ : Set Vec3)))
    (hUper : ∀ t ∈ Icc l r, SpatiallyPeriodic (U t))
    (hbper : ∀ t ∈ Icc l r, SpatiallyPeriodic (b t)) :
    ∃ X : ℝ → ℝ → Velocity,
      ∀ ε : ℝ, IsLabelFlowOn (fun t x => U t x + ε • b t x) (X ε) (Icc l r) := by
  have hExists (ε : ℝ) :
      ∃ Y : ℝ → Velocity, IsLabelFlowOn (fun t x => U t x + ε • b t x) Y (Icc l r) := by
    obtain ⟨_, Y, _, hY⟩ := exists_labelFlow_on_Icc_of_contDiffOn_periodic hlr
      (U := fun t x => U t x + ε • b t x) (hU.add (hb.const_smul ε))
      (fun t ht n x => by simp only [hUper t ht n x, hbper t ht n x])
    exact ⟨Y, hY⟩
  choose X hX using hExists
  exact ⟨X, hX⟩

private theorem gronwall_zero_start_uniform {f d : ℝ → Vec3} {l r K D : ℝ}
    (hK : 0 ≤ K) (hD : 0 ≤ D)
    (hf : ∀ t ∈ Icc l r, HasDerivWithinAt f (d t) (Icc l r) t) (h₀ : f l = 0)
    (hd : ∀ t ∈ Icc l r, ‖d t‖ ≤ K * ‖f t‖ + D) {t : ℝ} (ht : t ∈ Icc l r) :
    ‖f t‖ ≤ gronwallBound 0 K D (r - l) := by
  have h := norm_le_gronwallBound_of_norm_deriv_right_le (HasDerivWithinAt.continuousOn hf)
    (fun u hu => (hf u (Ico_subset_Icc_self hu)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem hu)) (show ‖f l‖ ≤ 0 by simp [h₀])
    (fun u hu => hd u (Ico_subset_Icc_self hu)) t ht
  exact h.trans (gronwallBound_mono le_rfl hD hK (sub_le_sub_right ht.2 l))

private theorem gronwall_zero_start_mul (K D c d : ℝ) :
    gronwallBound 0 K (D * c) d = gronwallBound 0 K D d * c := by
  by_cases hK : K = 0 <;> simp only [gronwallBound, hK, ↓reduceIte, zero_mul, zero_add] <;> ring

private theorem gronwall_zero_start_nonneg {K D d : ℝ} (hK : 0 ≤ K) (hD : 0 ≤ D) (hd : 0 ≤ d) :
    0 ≤ gronwallBound 0 K D d := by
  simpa only [gronwallBound_x0] using gronwallBound_mono (δ := 0) le_rfl hD hK hd

private theorem norm_velocityTaylor_le {f : Vec3 → Vec3} (hf : Differentiable ℝ f)
    {L : ℝ≥0} (hLip : LipschitzWith L (fderiv ℝ f)) (x y : Vec3) :
    ‖f y - f x - fderiv ℝ f x (y - x)‖ ≤ (L : ℝ) * ‖y - x‖ ^ 2 := by
  rw [pow_two, ← mul_assoc]
  refine (convex_closedBall x ‖y - x‖).norm_image_sub_le_of_norm_fderiv_le'
    (fun z _ => hf z) (fun z hz => ?_) (Metric.mem_closedBall_self (norm_nonneg _))
    (by simp only [Metric.mem_closedBall, dist_eq_norm, le_refl])
  exact (by simpa only [dist_eq_norm] using hLip.dist_le_mul z x :
      ‖fderiv ℝ f z - fderiv ℝ f x‖ ≤ (L : ℝ) * ‖z - x‖).trans
    (mul_le_mul_of_nonneg_left (by simpa only [Metric.mem_closedBall, dist_eq_norm] using hz)
      L.coe_nonneg)

/-- First variation in the velocity, with the initial label held fixed. The
parameter derivative solves the forced variational equation on the entire slab. -/
theorem labelFlow_firstVariation {U b : Velocity} {X : ℝ → ℝ → Velocity} {l r : ℝ}
    {K L J C : ℝ≥0} (hlr : l ≤ r)
    (hX : ∀ ε : ℝ, IsLabelFlowOn (fun t x => U t x + ε • b t x) (X ε) (Icc l r))
    (hUlip : ∀ t ∈ Icc l r, LipschitzWith K (U t))
    (hUdiff : ∀ t ∈ Icc l r, Differentiable ℝ (U t))
    (hDlip : ∀ t ∈ Icc l r, LipschitzWith L (fderiv ℝ (U t)))
    (hblip : ∀ t ∈ Icc l r, LipschitzWith J (b t))
    (hbnd : ∀ t ∈ Icc l r, ∀ x, ‖b t x‖ ≤ C)
    (hbc : ContinuousOn (Function.uncurry b) (Icc l r ×ˢ (univ : Set Vec3))) (a : Vec3)
    (hD : ContinuousOn (fun t => fderiv ℝ (U t) (X 0 l t a)) (Icc l r)) :
    ∃ ξ : ℝ → Vec3, ξ l = 0 ∧
      (∀ t ∈ Icc l r, HasDerivWithinAt ξ
        (fderiv ℝ (U t) (X 0 l t a) (ξ t) + b t (X 0 l t a)) (Icc l r) t) ∧
      ∀ t ∈ Icc l r, HasDerivAt (fun ε : ℝ => X ε l t a) (ξ t) 0 := by
  let A (t : ℝ) := fderiv ℝ (U t) (X 0 l t a)
  let hl : l ∈ Icc l r := left_mem_Icc.2 hlr
  have hBc : ContinuousOn (fun t => b t (X 0 l t a)) (Icc l r) :=
    hbc.comp (continuousOn_id.prodMk (HasDerivWithinAt.continuousOn ((hX 0).trajectory l hl a)))
      (fun _ ht => ⟨ht, mem_univ _⟩)
  obtain ⟨ξ, hξ₀, hξ⟩ := linearODE_inhom_exists_Icc hl hD hBc (0 : Vec3)
  refine ⟨ξ, hξ₀, hξ, fun t ht => ?_⟩
  let B := gronwallBound 0 K C (r - l)
  let D := (L : ℝ) * B ^ 2 + (J : ℝ) * B
  let P := gronwallBound 0 K D (r - l)
  have hB₀ : 0 ≤ B := gronwall_zero_start_nonneg K.coe_nonneg C.coe_nonneg (sub_nonneg.mpr hlr)
  have hD₀ : 0 ≤ D := add_nonneg (mul_nonneg L.coe_nonneg (sq_nonneg _))
    (mul_nonneg J.coe_nonneg hB₀)
  have hErr (ε : ℝ) : ‖X ε l t a - X 0 l t a - ε • ξ t‖ ≤ P * ‖ε‖ ^ 2 := by
    let Δ (u : ℝ) := X ε l u a - X 0 l u a
    let dΔ (u : ℝ) := U u (X ε l u a) - U u (X 0 l u a) + ε • b u (X ε l u a)
    have hΔ₀ : Δ l = 0 := by simp [Δ, (hX _).initial l hl]
    have hΔ (u : ℝ) (hu : u ∈ Icc l r) : HasDerivWithinAt Δ (dΔ u) (Icc l r) u := by
      refine (((hX ε).trajectory l hl a u hu).sub ((hX 0).trajectory l hl a u hu)).congr_deriv ?_
      simp only [dΔ, zero_smul, add_zero]
      abel
    have hΔrate (u : ℝ) (hu : u ∈ Icc l r) : ‖dΔ u‖ ≤ (K : ℝ) * ‖Δ u‖ + (C : ℝ) * ‖ε‖ := by
      have h := (hUlip u hu).dist_le_mul (X ε l u a) (X 0 l u a)
      have hU : ‖U u (X ε l u a) - U u (X 0 l u a)‖ ≤ (K : ℝ) * ‖Δ u‖ := by
        simpa only [dist_eq_norm, Δ] using h
      calc
        ‖dΔ u‖ ≤ ‖U u (X ε l u a) - U u (X 0 l u a)‖ + ‖ε • b u (X ε l u a)‖ :=
          norm_add_le _ _
        _ ≤ _ := by
          rw [norm_smul, mul_comm (C : ℝ)]
          exact add_le_add hU (mul_le_mul_of_nonneg_left (hbnd u hu _) (norm_nonneg _))
    have hΔbound (u : ℝ) (hu : u ∈ Icc l r) : ‖Δ u‖ ≤ B * ‖ε‖ := by
      have h := gronwall_zero_start_uniform K.coe_nonneg (mul_nonneg C.coe_nonneg (norm_nonneg ε))
        hΔ hΔ₀ hΔrate hu
      rwa [gronwall_zero_start_mul] at h
    let err (u : ℝ) := Δ u - ε • ξ u
    let dErr (u : ℝ) := A u (err u) +
      (U u (X ε l u a) - U u (X 0 l u a) - A u (Δ u)) +
      ε • (b u (X ε l u a) - b u (X 0 l u a))
    have herr₀ : err l = 0 := by simp only [err, hΔ₀, hξ₀, smul_zero, sub_zero]
    have herr (u : ℝ) (hu : u ∈ Icc l r) : HasDerivWithinAt err (dErr u) (Icc l r) u := by
      have hscaled : HasDerivWithinAt (fun v => ε • ξ v)
          (ε • (A u (ξ u) + b u (X 0 l u a))) (Icc l r) u :=
        (hξ u hu).const_smul ε
      refine ((hΔ u hu).sub hscaled).congr_deriv ?_
      simp only [err, dErr, dΔ, map_sub, map_smul, smul_sub, smul_add]
      abel
    have hrate (u : ℝ) (hu : u ∈ Icc l r) : ‖dErr u‖ ≤ (K : ℝ) * ‖err u‖ + D * ‖ε‖ ^ 2 := by
      have hA : ‖A u‖ ≤ (K : ℝ) := norm_fderiv_le_of_lipschitz ℝ (hUlip u hu)
      have hTaylor := norm_velocityTaylor_le (hUdiff u hu) (hDlip u hu) (X 0 l u a) (X ε l u a)
      have hbDiff : ‖b u (X ε l u a) - b u (X 0 l u a)‖ ≤ (J : ℝ) * (B * ‖ε‖) := by
        have h := (hblip u hu).dist_le_mul (X ε l u a) (X 0 l u a)
        rw [dist_eq_norm, dist_eq_norm] at h
        exact h.trans (mul_le_mul_of_nonneg_left (hΔbound u hu) J.coe_nonneg)
      calc
        ‖dErr u‖ ≤
            ‖A u (err u)‖ + (L : ℝ) * ‖Δ u‖ ^ 2 + ‖ε‖ * ‖b u (X ε l u a) - b u (X 0 l u a)‖ :=
          (norm_add_le _ _).trans (add_le_add
            ((norm_add_le _ _).trans (add_le_add le_rfl hTaylor)) (by rw [norm_smul]))
        _ ≤ (K : ℝ) * ‖err u‖ + (L : ℝ) * (B * ‖ε‖) ^ 2 + ‖ε‖ * ((J : ℝ) * (B * ‖ε‖)) :=
          add_le_add (add_le_add (((A u).le_opNorm _).trans
            (mul_le_mul_of_nonneg_right hA (norm_nonneg _)))
            (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hΔbound u hu) 2) L.coe_nonneg))
            (mul_le_mul_of_nonneg_left hbDiff (norm_nonneg _))
        _ = _ := by dsimp only [D]; ring
    have h := gronwall_zero_start_uniform K.coe_nonneg (mul_nonneg hD₀ (sq_nonneg ‖ε‖))
      herr herr₀ hrate ht
    rwa [gronwall_zero_start_mul] at h
  rw [hasDerivAt_iff_isLittleO, isLittleO_iff]
  intro c hc
  have hcont : Continuous (fun ε : ℝ => P * ‖ε‖) := by fun_prop
  have hlim : Tendsto (fun ε : ℝ => P * ‖ε‖) (𝓝 0) (𝓝 0) := by
    simpa only [norm_zero, mul_zero] using (hcont.continuousAt (x := (0 : ℝ))).tendsto
  filter_upwards [hlim (Iio_mem_nhds hc)] with ε hε
  simp only [sub_zero]
  exact (hErr ε).trans <| calc
    P * ‖ε‖ ^ 2 = (P * ‖ε‖) * ‖ε‖ := by ring
    _ ≤ c * ‖ε‖ := mul_le_mul_of_nonneg_right (mem_Iio.mp hε).le (norm_nonneg _)

end TorusEuler
