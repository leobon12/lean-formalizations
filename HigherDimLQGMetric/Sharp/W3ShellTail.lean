import HigherDimLQGMetric.Sharp.W2Upper
import HigherDimLQGMetric.Sharp.W2Around
import HigherDimLQGMetric.Sharp.ShellScaling
import HigherDimLQGMetric.Config.Geometry
import HigherDimLQGMetric.ShellDec.Tail

/-! Upper tails for the two shell costs used by multiscale chaining. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Set Metric MeasureTheory
open HigherDimLFPP (Rd)
open scoped ENNReal

variable {d : ℕ}

private theorem w3_sphere_nontrivial (hd : 3 ≤ d) {r : ℝ} (hr : 0 < r) :
    (Metric.sphere (0 : Rd d) r).Nontrivial := by
  let i : Fin d := ⟨0, by omega⟩
  let u : Rd d := EuclideanSpace.single i (1 : ℝ)
  let x : Rd d := r • u
  have hu : ‖u‖ = 1 := by simp [u, PiLp.norm_single]
  have hnorm : ‖x‖ = r := by
    dsimp [x]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, hu, mul_one]
  have hx : x ∈ Metric.sphere (0 : Rd d) r := by
    simpa only [Metric.mem_sphere, dist_zero_right] using hnorm
  have hneg : -x ∈ Metric.sphere (0 : Rd d) r := by
    simpa only [Metric.mem_sphere, dist_zero_right, norm_neg] using hnorm
  refine ⟨x, hx, -x, hneg, ?_⟩
  intro he
  have h2 : (2 : ℝ) • x = 0 := by
    calc
      (2 : ℝ) • x = x + x := by norm_num [two_smul]
      _ = 0 := (congrArg (fun y : Rd d => x + y) he).trans (add_neg_cancel x)
  have hn : 2 * ‖x‖ = 0 := by
    have heq := congrArg norm h2
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2),
      norm_zero] using heq
  linarith

/-- The crossing cost in the geometric multiscale lemma has a tail of every
polynomial order, uniformly over centers and scales. -/
theorem w3_across_upper_superpoly (hd : 3 ≤ d) {ξ Q : ℝ}
    (hξ : 0 < ξ) (hQ : 0 ≤ Q)
    {D : DistRd d → ContMetric d} (hD : IsSharpWeakExpMetric d ξ Q D)
    {p : ℝ} (hp : 0 < p) :
    ∃ C : ℝ, ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (h : Ω → DistRd d), IsWholeSpaceLGF h P →
      ∀ r : ℝ, 0 < r → ∀ z : Rd d, ∀ A : ℝ, 1 ≤ A →
      P {ω | ENNReal.ofReal (A * r ^ (ξ * Q) *
        Real.exp (ξ * sphereAvg (h ω) r z)) <
        setDistIn (D (h ω)) (ann z (r / 16) (2 * r))
          (Metric.sphere z (r / 8)) (Metric.sphere z r)} ≤
        ENNReal.ofReal (C * A ^ (-p)) := by
  let V : Set (Rd d) := ann 0 (1 / 16) 2
  let S₁ : Set (Rd d) := Metric.sphere 0 (1 / 8)
  let S₂ : Set (Rd d) := Metric.sphere 0 1
  have hrank : 1 < Module.rank ℝ (Rd d) := by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
    exact_mod_cast (show 1 < d by omega)
  have hS₁V : S₁ ⊆ V := by
    intro x hx
    have he : ‖x‖ = (1 : ℝ) / 8 := by
      simpa only [S₁, Metric.mem_sphere, dist_zero_right] using hx
    change x ∈ V
    dsimp [V, ann]
    simp only [sub_zero]
    rw [he]
    norm_num
  have hS₂V : S₂ ⊆ V := by
    intro x hx
    have he : ‖x‖ = (1 : ℝ) := by
      simpa only [S₂, Metric.mem_sphere, dist_zero_right] using hx
    change x ∈ V
    dsimp [V, ann]
    simp only [sub_zero]
    rw [he]
    norm_num
  obtain ⟨C, hC⟩ := setDist_upper_superpoly (lemmaA1 (by omega : 1 ≤ d)) hd hξ hQ hD
    (show IsOpen V from isOpen_ann _ _ _)
    (config_isConnected_ann (by omega : 2 ≤ d) 0 (by norm_num) (by norm_num))
    (isCompact_sphere _ _) (isConnected_sphere hrank 0 (by norm_num))
    (w3_sphere_nontrivial hd (by norm_num))
    (isCompact_sphere _ _) (isConnected_sphere hrank 0 (by norm_num))
    (w3_sphere_nontrivial hd (by norm_num)) hS₁V hS₂V hp
  refine ⟨C, ?_⟩
  intro Ω _ P _ h hh r hr z A hA
  have hV : affineSet r z V = ann z (r / 16) (2 * r) := by
    unfold V affineSet
    rw [show (fun x : Rd d => z + r • x) = (fun x => r • x + z) by funext x; abel]
    rw [image_ann_affine hr z]
    rw [show r * ((1 : ℝ) / 16) = r / 16 by ring, mul_comm r 2]
  have hS₁ : affineSet r z S₁ = Metric.sphere z (r / 8) := by
    unfold S₁ affineSet
    rw [show (fun x : Rd d => z + r • x) = (fun x => r • x + z) by funext x; abel]
    rw [image_sphere_affine hr z]
    rw [show r * ((1 : ℝ) / 8) = r / 8 by ring]
  have hS₂ : affineSet r z S₂ = Metric.sphere z r := by
    unfold S₂ affineSet
    rw [show (fun x : Rd d => z + r • x) = (fun x => r • x + z) by funext x; abel]
    simpa only [mul_one] using image_sphere_affine hr z 1
  dsimp only [S₁, S₂] at hS₁ hS₂
  simpa only [hV, hS₁, hS₂] using hC P h hh r hr z A hA

/-- The around-annulus linking cost has a tail of every polynomial order. -/
theorem w3_around_upper_superpoly (hd : 3 ≤ d) {ξ Q : ℝ}
    (hξ : 0 < ξ) (hQ : 0 ≤ Q)
    {D : DistRd d → ContMetric d} (hD : IsSharpWeakExpMetric d ξ Q D)
    {p : ℝ} (hp : 0 < p) :
    ∃ C : ℝ, ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (h : Ω → DistRd d), IsWholeSpaceLGF h P →
      ∀ r : ℝ, 0 < r → ∀ z : Rd d, ∀ A : ℝ, 1 ≤ A →
      P {ω | ENNReal.ofReal (A * r ^ (ξ * Q) *
        Real.exp (ξ * sphereAvg (h ω) r z)) <
        aroundDist (D (h ω)) z (3 * r / 16) (3 * r / 8)} ≤
        ENNReal.ofReal (C * A ^ (-p)) := by
  obtain ⟨C, hC⟩ := around_upper_superpoly (lemmaA1 (by omega : 1 ≤ d)) hd
    hξ hQ hD (show (0 : ℝ) < 3 / 16 by norm_num)
    (show (3 : ℝ) / 16 < 3 / 8 by norm_num) hp
  refine ⟨C, ?_⟩
  intro Ω _ P _ h hh r hr z A hA
  convert hC P h hh r hr z A hA using 1; ring_nf

end HigherDimLQGMetric
