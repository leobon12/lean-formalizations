import QuantumZipper.Proofs.Thm18.ASep2Conj1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ASEP2 (D1, locality): regularized values only see the field near the measure

Deterministic locality of the regularization used to pass from a continuous cutoff of the
wedge profile to the profile itself (which is continuous only off `0`). If two fields `x`, `y` have
the same raw values on all dyadic folded circles within distance `ε` of a set `Z₀`
(`hloc`), then

* their regularized averages agree near `Z₀` at small scales (`avgReg_eq_of_loc`);
* their regularized values agree at every folded circle near `Z₀` (`evalReg_fc_eq_of_loc`),
  at every measure carried by `Z₀` (`evalReg_map_eq_of_loc`), and after a rescaling
  (`evalReg_rescale_map_eq_of_loc`).

Own elementary bookkeeping (the regularization is a local limit of circle averages).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology

namespace QuantumZipper
namespace ASep

theorem evalReg_congr_of_eventually {x y : FieldSample} {ν : Measure ℂ}
    (h : ∀ᶠ k in atTop, ∫ v, avgReg x k v ∂ν = ∫ v, avgReg y k v ∂ν) :
    evalReg x ν = evalReg y ν := by
  unfold evalReg limUnder
  rw [Filter.map_congr h]

theorem avgReg_congr_of_eventually {x y : FieldSample} {k : ℕ} {z : ℂ}
    (h : ∀ᶠ n in atTop, x (foldedCircle (dyadicRoundC n z) (radius k)) =
      y (foldedCircle (dyadicRoundC n z) (radius k))) :
    avgReg x k z = avgReg y k z := by
  unfold avgReg limUnder
  rw [Filter.map_congr h]

theorem eventually_radius_lt {ε : ℝ} (hε : 0 < ε) : ∀ᶠ k in atTop, radius k < ε :=
  (RegClosure.tendsto_radius_nhdsGT.mono_right nhdsWithin_le_nhds).eventually (gt_mem_nhds hε)

variable {x y : FieldSample} {Z₀ : Set ℂ} {ε : ℝ}

/-- Regularized averages agree near `Z₀`. -/
theorem avgReg_eq_of_loc
    (hloc : ∀ c ∈ RegUnif.Dy, ∀ k : ℕ, (∃ z₀ ∈ Z₀, ‖c - z₀‖ + radius k ≤ ε) →
      x (foldedCircle c (radius k)) = y (foldedCircle c (radius k)))
    {v : ℂ} (hv : v ∈ Hbar) {k : ℕ} (hk : ∃ z₀ ∈ Z₀, ‖v - z₀‖ + radius k < ε) :
    avgReg x k v = avgReg y k v := by
  obtain ⟨z₀, hz₀, hlt⟩ := hk
  refine avgReg_congr_of_eventually ?_
  have hf : Tendsto (fun n => foldH (dyadicRoundC n v)) atTop (𝓝 v) := by
    have := (CircleFubini.continuous_foldH'.tendsto v).comp (RegClosure.tendsto_dyadicRoundC v)
    rwa [CircleFubini.foldH_of_mem' hv] at this
  have hs : 0 < ε - (‖v - z₀‖ + radius k) := by linarith
  filter_upwards [hf.eventually (ball_mem_nhds v hs)] with n hn
  rw [RegUnif.raw_eq_foldH x n k v, RegUnif.raw_eq_foldH y n k v]
  refine hloc _ (RegUnif.foldH_dyadicRoundC_mem_Dy n v) k ⟨z₀, hz₀, ?_⟩
  rw [dist_eq_norm] at hn
  have := norm_sub_le_norm_sub_add_norm_sub (foldH (dyadicRoundC n v)) v z₀
  linarith

/-- Regularized values agree at folded circles near `Z₀`. -/
theorem evalReg_fc_eq_of_loc
    (hloc : ∀ c ∈ RegUnif.Dy, ∀ k : ℕ, (∃ z₀ ∈ Z₀, ‖c - z₀‖ + radius k ≤ ε) →
      x (foldedCircle c (radius k)) = y (foldedCircle c (radius k)))
    {c : ℂ} (hc : c ∈ Hbar) {ρ : ℝ} (hρ : 0 ≤ ρ) (h : ∃ z₀ ∈ Z₀, ‖c - z₀‖ + ρ < ε) :
    evalReg x (foldedCircle c ρ) = evalReg y (foldedCircle c ρ) := by
  obtain ⟨z₀, hz₀, hlt⟩ := h
  refine evalReg_congr_of_eventually ?_
  filter_upwards [eventually_radius_lt (show 0 < ε - (‖c - z₀‖ + ρ) by linarith)] with k hk
  refine integral_congr_ae ?_
  filter_upwards [FrostmanReg.foldedCircle_ae_near_frostman (c := c) hc hρ] with v hv
  refine avgReg_eq_of_loc hloc hv.1 ⟨z₀, hz₀, ?_⟩
  have h1 : ‖v - c‖ ≤ ρ := by simpa using hv.2
  have := norm_sub_le_norm_sub_add_norm_sub v c z₀
  linarith

/-- Regularized values agree at a push-forward carried by `Z₀`. -/
theorem evalReg_map_eq_of_loc (hε : 0 < ε)
    (hloc : ∀ c ∈ RegUnif.Dy, ∀ k : ℕ, (∃ z₀ ∈ Z₀, ‖c - z₀‖ + radius k ≤ ε) →
      x (foldedCircle c (radius k)) = y (foldedCircle c (radius k)))
    {σ : Measure ℂ} {φ : ℂ → ℂ} (hφ : AEMeasurable φ σ)
    (hσ : ∀ᵐ w ∂σ, φ w ∈ Hbar ∧ φ w ∈ Z₀) :
    evalReg x (σ.map φ) = evalReg y (σ.map φ) := by
  refine evalReg_congr_of_eventually ?_
  filter_upwards [eventually_radius_lt hε] with k hk
  rw [integral_map hφ (RegClosure.measurable_avgReg_slice x k).aestronglyMeasurable,
    integral_map hφ (RegClosure.measurable_avgReg_slice y k).aestronglyMeasurable]
  refine integral_congr_ae ?_
  filter_upwards [hσ] with w hw
  exact avgReg_eq_of_loc hloc hw.1 ⟨φ w, hw.2, by simpa using hk⟩

/-- Regularized values of the rescaled fields agree at a push-forward whose `a`-dilate is
carried by `Z₀`. -/
theorem evalReg_rescale_map_eq_of_loc (hε : 0 < ε)
    (hloc : ∀ c ∈ RegUnif.Dy, ∀ k : ℕ, (∃ z₀ ∈ Z₀, ‖c - z₀‖ + radius k ≤ ε) →
      x (foldedCircle c (radius k)) = y (foldedCircle c (radius k)))
    (Q : ℝ) {a : ℝ} (ha : 0 < a)
    {σ : Measure ℂ} {φ : ℂ → ℂ} (hφ : AEMeasurable φ σ)
    (hσ : ∀ᵐ w ∂σ, φ w ∈ Hbar ∧ (a : ℂ) * φ w ∈ Z₀) :
    evalReg (rescale x Q a) (σ.map φ) = evalReg (rescale y Q a) (σ.map φ) := by
  refine evalReg_congr_of_eventually ?_
  have ha2 : 0 < ε / (2 * a) := by positivity
  filter_upwards [eventually_radius_lt ha2] with j hj
  rw [integral_map hφ (RegClosure.measurable_avgReg_slice _ j).aestronglyMeasurable,
    integral_map hφ (RegClosure.measurable_avgReg_slice _ j).aestronglyMeasurable]
  refine integral_congr_ae ?_
  filter_upwards [hσ] with w hw
  set z := φ w with hzdef
  have hz : z ∈ Hbar := hw.1
  refine avgReg_congr_of_eventually ?_
  have hs : 0 < ε / 2 / a := by positivity
  filter_upwards [(RegClosure.tendsto_dyadicRoundC z).eventually (ball_mem_nhds z hs)]
    with n hn
  have hcn : dyadicRoundC n z ∈ Hbar := CircleCont.dyadicRoundC_mem_Hbar hz n
  show evalReg x ((foldedCircle (dyadicRoundC n z) (radius j)).map fun u => (a : ℂ) * u) +
      Q * ∫ u, Real.log ‖deriv (fun u : ℂ => (a : ℂ) * u) u‖ ∂foldedCircle _ _ =
    evalReg y ((foldedCircle (dyadicRoundC n z) (radius j)).map fun u => (a : ℂ) * u) +
      Q * ∫ u, Real.log ‖deriv (fun u : ℂ => (a : ℂ) * u) u‖ ∂foldedCircle _ _
  congr 1
  rw [Thm18Asm.foldedCircle_map_mul ha]
  have hacn : (a : ℂ) * dyadicRoundC n z ∈ Hbar := by
    show 0 ≤ ((a : ℂ) * dyadicRoundC n z).im
    have : 0 ≤ (dyadicRoundC n z).im := hcn
    simpa using mul_nonneg ha.le this
  refine evalReg_fc_eq_of_loc hloc hacn (mul_pos ha (radius_pos j)).le ⟨_, hw.2, ?_⟩
  rw [dist_eq_norm] at hn
  have e : (a : ℂ) * dyadicRoundC n z - (a : ℂ) * z = (a : ℂ) * (dyadicRoundC n z - z) := by
    ring
  rw [e, norm_mul, Complex.norm_real, Real.norm_of_nonneg ha.le]
  have h1 : a * ‖dyadicRoundC n z - z‖ < ε / 2 := by
    rw [lt_div_iff₀ ha] at hn; linarith
  have h2 : a * radius j < ε / 2 := by
    rw [lt_div_iff₀ (by positivity)] at hj; linarith
  linarith

end ASep
end QuantumZipper
