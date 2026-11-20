import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Algebra.Module.ClosedSubmodule
import Mathlib.Topology.ContinuousMap.Bounded.Normed

open Set
open BoundedContinuousFunction ContinuousLinearMap

namespace TorusEuler

variable {X E : Type*} [MetricSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]

abbrev DistinctPairs (X : Type*) := {q : X × X // q.1 ≠ q.2}

abbrev HalfHolderData (X E : Type*) [TopologicalSpace X] [PseudoMetricSpace E] :=
  (X →ᵇ E) × (DistinctPairs X →ᵇ E)

private noncomputable def holderConstraint (q : DistinctPairs X) : HalfHolderData X E →L[ℝ] E :=
  (evalCLM ℝ q).comp (snd ℝ (X →ᵇ E) (DistinctPairs X →ᵇ E)) -
    (Real.sqrt (dist q.val.1 q.val.2))⁻¹ •
      (ContinuousLinearMap.comp (evalCLM ℝ q.val.1 - evalCLM ℝ q.val.2)
        (fst ℝ (X →ᵇ E) (DistinctPairs X →ᵇ E)))

/-- The graph of the half-Hölder difference quotient in bounded continuous functions. -/
noncomputable def halfHolderSubspace (X E : Type*) [MetricSpace X] [NormedAddCommGroup E]
    [NormedSpace ℝ E] : ClosedSubmodule ℝ (HalfHolderData X E) := by
  let s : Submodule ℝ (HalfHolderData X E) := ⨅ q : DistinctPairs X, (holderConstraint (E := E) q).ker
  refine { toSubmodule := s, isClosed' := ?_ }
  have h : (s : Set (HalfHolderData X E)) =
      ⋂ q : DistinctPairs X, (holderConstraint (E := E) q) ⁻¹' {0} := by
    ext f
    simp [s, Submodule.mem_iInf]
  rw [h]
  exact isClosed_iInter fun q => isClosed_singleton.preimage (holderConstraint q).continuous

/-- Bounded half-Hölder fields with the maximum of the supremum norm and seminorm.
It is a Banach space whenever the codomain is Banach. -/
abbrev HalfHolder (X E : Type*) [MetricSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  ↥(halfHolderSubspace X E).toSubmodule

instance [CompleteSpace E] : CompleteSpace (HalfHolder X E) :=
  (halfHolderSubspace X E).isClosed'.isComplete.completeSpace_coe

theorem halfHolder_quotient (f : HalfHolder X E) (q : DistinctPairs X) :
    f.val.2 q = (Real.sqrt (dist q.val.1 q.val.2))⁻¹ • (f.val.1 q.val.1 - f.val.1 q.val.2) := by
  have h : holderConstraint q f.val = 0 :=
    ((Submodule.mem_iInf _).mp f.property q : f.val ∈ (holderConstraint q).ker)
  exact sub_eq_zero.mp h

/-- Point evaluation of the half-Hölder field. -/
noncomputable def HalfHolder.eval (x : X) : HalfHolder X E →L[ℝ] E :=
  ((evalCLM ℝ x).comp (fst ℝ (X →ᵇ E) (DistinctPairs X →ᵇ E))).comp
    (halfHolderSubspace X E).toSubmodule.subtypeL

@[simp] theorem HalfHolder.eval_apply (x : X) (f : HalfHolder X E) : HalfHolder.eval x f = f.val.1 x :=
  rfl

theorem HalfHolder.norm_le_iff {f : HalfHolder X E} {M : ℝ} (hM : 0 ≤ M) :
    ‖f‖ ≤ M ↔ (∀ x, ‖f.val.1 x‖ ≤ M) ∧
      ∀ x y, ‖f.val.1 x - f.val.1 y‖ ≤ M * Real.sqrt (dist x y) := by
  change max ‖f.val.1‖ ‖f.val.2‖ ≤ M ↔ _
  rw [max_le_iff, BoundedContinuousFunction.norm_le hM, BoundedContinuousFunction.norm_le hM]
  constructor
  · rintro ⟨hvalue, hquot⟩
    refine ⟨hvalue, fun x y => ?_⟩
    by_cases hxy : x = y
    · simp [hxy]
    · have hd : 0 < Real.sqrt (dist x y) := Real.sqrt_pos.2 (dist_pos.mpr hxy)
      let q : DistinctPairs X := ⟨(x, y), hxy⟩
      have h := hquot q
      rw [halfHolder_quotient, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hd),
        ← div_eq_inv_mul, div_le_iff₀ hd] at h
      exact h
  · rintro ⟨hvalue, hquot⟩
    refine ⟨hvalue, fun q => ?_⟩
    have hd : 0 < Real.sqrt (dist q.val.1 q.val.2) := Real.sqrt_pos.2 (dist_pos.mpr q.property)
    rw [halfHolder_quotient, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hd),
      ← div_eq_inv_mul, div_le_iff₀ hd]
    exact hquot _ _

/-- A continuous field with both bounds is a member of the half-Hölder Banach space. -/
noncomputable def HalfHolder.ofBound (f : C(X, E)) {M : ℝ}
    (hvalue : ∀ x, ‖f x‖ ≤ M)
    (hquot : ∀ x y, ‖f x - f y‖ ≤ M * Real.sqrt (dist x y)) : HalfHolder X E := by
  let g : DistinctPairs X → E := fun q =>
    (Real.sqrt (dist q.val.1 q.val.2))⁻¹ • (f q.val.1 - f q.val.2)
  have hgcont : Continuous g := by
    have hd : Continuous (fun q : DistinctPairs X => Real.sqrt (dist q.val.1 q.val.2)) :=
      Real.continuous_sqrt.comp (continuous_subtype_val.fst.dist continuous_subtype_val.snd)
    have hne (q : DistinctPairs X) : Real.sqrt (dist q.val.1 q.val.2) ≠ 0 :=
      (Real.sqrt_pos.2 (dist_pos.mpr q.property)).ne'
    exact (hd.inv₀ hne).smul ((f.continuous.comp continuous_subtype_val.fst).sub
      (f.continuous.comp continuous_subtype_val.snd))
  have hgbound (q : DistinctPairs X) : ‖g q‖ ≤ M := by
    have hd : 0 < Real.sqrt (dist q.val.1 q.val.2) := Real.sqrt_pos.2 (dist_pos.mpr q.property)
    dsimp only [g]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hd), ← div_eq_inv_mul, div_le_iff₀ hd]
    exact hquot _ _
  let fBounded : X →ᵇ E := ofNormedAddCommGroup f f.continuous M hvalue
  let gBounded : DistinctPairs X →ᵇ E :=
    ofNormedAddCommGroup g hgcont M hgbound
  refine ⟨(fBounded, gBounded), (Submodule.mem_iInf _).mpr fun q => ?_⟩
  change holderConstraint q (fBounded, gBounded) = 0
  change g q - g q = 0
  exact sub_self _

@[simp] theorem HalfHolder.eval_ofBound (f : C(X, E)) {M : ℝ}
    (hvalue : ∀ x, ‖f x‖ ≤ M)
    (hquot : ∀ x y, ‖f x - f y‖ ≤ M * Real.sqrt (dist x y)) (x : X) :
    HalfHolder.eval x (HalfHolder.ofBound f hvalue hquot) = f x := rfl

end TorusEuler
