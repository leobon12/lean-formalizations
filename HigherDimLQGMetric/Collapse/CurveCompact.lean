import HigherDimLQGMetric.Collapse.Tube
import HigherDimLQGMetric.Coord.Compactness

/-!
# Compactness of curves of uniformly bounded ambient speed

This is the specialization of the existing coordinate Arzelà–Ascoli theorem to one fixed
metric. The limit keeps the compact confinement and length is lower semicontinuous.
-/

set_option autoImplicit false

open Set Filter Topology BoundedContinuousFunction
open scoped ENNReal

namespace HigherDimLQGMetric

open LQGMetric.MetricGeometry

/-- Replace a rectifiable curve by a Lipschitz path with the same length and endpoints,
whose image lies in the original image. -/
theorem collapse_exists_lipschitz_path {X : Type*} [MetricSpace X] {Y : Set X}
    {P : ℝ → X} {x y : X} {C : ℝ} (hC : 0 ≤ C)
    (hP : ContinuousOn P (Icc 0 1)) (h0 : P 0 = x) (h1 : P 1 = y)
    (hPY : MapsTo P (Icc 0 1) Y)
    (hlen : curveLength P 0 1 ≤ ENNReal.ofReal C) :
    ∃ Q : Icc (0 : ℝ) 1 →ᵇ X, Q 0 = x ∧ Q 1 = y ∧
      (∀ t, Q t ∈ Y) ∧
      (∀ t, ∃ s ∈ Icc (0 : ℝ) 1, Q t = P s) ∧
      curveLength (Set.IccExtend (by norm_num : (0 : ℝ) ≤ 1) Q) 0 1 =
        curveLength P 0 1 ∧
      ∀ s t, dist (Q s) (Q t) ≤ C * dist s t := by
  obtain ⟨γ, hγlen, hγimg⟩ := exists_path_of_curve zero_le_one hP
  have hlen' : pathLength γ ≠ ⊤ := by
    rw [hγlen]
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hlen
  obtain ⟨γ', hγ'len, hγ'img, hγ'lip⟩ := exists_lipschitz_path γ hlen'
  have hγ'Y : ∀ t, γ' t ∈ Y := by
    intro t
    obtain ⟨s, hgs⟩ := hγ'img ⟨t, rfl⟩
    obtain ⟨r, hr, hrs⟩ := hγimg ⟨s, rfl⟩
    exact (hgs.symm.trans hrs.symm) ▸ hPY hr
  let Q : Icc (0 : ℝ) 1 →ᵇ X := BoundedContinuousFunction.mkOfCompact γ'.toContinuousMap
  refine ⟨Q, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact γ'.source.trans h0
  · exact γ'.target.trans h1
  · exact hγ'Y
  · intro t
    obtain ⟨s, hgs⟩ := hγ'img ⟨t, rfl⟩
    obtain ⟨r, hr, hrs⟩ := hγimg ⟨s, rfl⟩
    exact ⟨r, hr, hgs.symm.trans hrs.symm⟩
  · change pathLength γ' = curveLength P 0 1
    exact hγ'len.trans hγlen
  · intro s t
    have hbound : (pathLength γ).toReal ≤ C := by
      apply ENNReal.toReal_le_of_le_ofReal hC
      exact hγlen.symm ▸ hlen
    calc
      dist (Q s) (Q t) ≤ (pathLength γ).toNNReal * dist s t :=
        hγ'lip.dist_le_mul s t
      _ ≤ C * dist s t := by
        apply mul_le_mul_of_nonneg_right _ dist_nonneg
        simpa only [ENNReal.coe_toNNReal_eq_toReal] using hbound

/-- Arzelà–Ascoli plus lower semicontinuity of ambient length on `[0,1]`. -/
theorem collapse_curve_subseq {X : Type*} [MetricSpace X] {Y : Set X} (hY : IsCompact Y)
    {a b : ℝ} (hab : a ≤ b) (A : ℝ) (F : ℕ → Icc a b →ᵇ X)
    (hFY : ∀ n t, F n t ∈ Y)
    (hspeed : ∀ n (s t : Icc a b), dist (F n s) (F n t) ≤ A * dist s t) :
    ∃ Q : Icc a b →ᵇ X, (∀ t, Q t ∈ Y) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        TendstoUniformly (fun n t => F (φ n) t) Q atTop ∧
        curveLength (Set.IccExtend hab Q) a b ≤
          liminf (fun n => curveLength
            (Set.IccExtend hab (F (φ n))) a b) atTop := by
  have hmod : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ n : ℕ, ∀ x ∈ Y, ∀ y ∈ Y, dist x y < δ → dist x y < ε := by
    intro ε hε
    exact ⟨ε, hε, fun _ _ _ _ _ h => h⟩
  obtain ⟨Q, hQY, φ, hφ, hlim⟩ :=
    exists_curve_subseq_of_uniform_lower_modulus hY
      (fun _ x y => dist x y) A F hFY hmod hspeed
  refine ⟨Q, hQY, φ, hφ, hlim, ?_⟩
  apply curveLength_le_liminf
  intro t ht
  have htend := hlim.tendsto_at (⟨t, ht⟩ : Icc a b)
  simpa only [Set.IccExtend_of_mem hab _ ht] using htend

end HigherDimLQGMetric
