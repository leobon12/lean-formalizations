import QuantumZipper.Proofs.Zipper.SWCoreN2Main
import QuantumZipper.Proofs.Zipper.SWCoreVClass

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-N2 (3): moduli for the round comparison semicircles and for derivatives over a family

Deterministic inputs of the family version of the boundary distortion core:

* `swcn2_round_modulus`: the Neumann energy of `(fc(s,ρ), fc(s',ρ'))` (real centres) is
  `≤ 2 holderK 25 2 · ((|s−s'| + |ρ−ρ'|)/ρ)^{1/6}` when `|s−s'| + |ρ−ρ'| ≤ ρ/2`
  (rescaling by `u ↦ s + ρ u`, `RegUnif.kernelCov2_map_affine`, and `swcv_kernelCov2_two`);
* `swcn2_deriv_sub_le`: for `ψ₁, ψ₂` in a boundary class with `‖ψ₁ − ψ₂‖ ≤ δ` on the
  `ρ`-thickening and `t, t' ∈ [a,b]` with `|t − t'| < ρ/4`,
  `‖ψ₁'(t) − ψ₂'(t')‖ ≤ K |t − t'| + 2δ/ρ` (Cauchy estimates, `swcv_deriv2_bound`).

Own elementary arguments (Cauchy's estimates: Ahlfors, *Complex Analysis*, Ch. 4, §2.3).
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology ENNReal Real

namespace QuantumZipper
namespace SWCore

open RegUnif TwoPoint

/-- The composite of two real affine maps. -/
theorem swcn2_swhAff_comp (s ρ s'' ρ'' : ℝ) :
    swhAff s ρ ∘ swhAff s'' ρ'' = swhAff (s + ρ * s'') (ρ * ρ'') := by
  funext u; simp only [Function.comp_apply, swhAff]; push_cast; ring

/-- **Energy modulus of round semicircles with real centres.** -/
theorem swcn2_round_modulus {s s' ρ ρ' : ℝ} (hρ : 0 < ρ)
    (hsmall : |s - s'| + |ρ - ρ'| ≤ ρ / 2) :
    |kernelCov2 neumannH (foldedCircle (s : ℂ) ρ, foldedCircle (s' : ℂ) ρ')
        (foldedCircle (s : ℂ) ρ, foldedCircle (s' : ℂ) ρ')| ≤
      2 * (holderK (12 / (1 / 2) + 1) 2 * ((|s - s'| + |ρ - ρ'|) / ρ) ^ ((1 / 3 : ℝ) / 2)) := by
  have hρ' : ρ / 2 ≤ ρ' := by
    have := le_abs_self (ρ - ρ'); linarith [abs_nonneg (s - s')]
  have hρ'0 : 0 < ρ' := by linarith
  set s'' := (s' - s) / ρ with hs''
  set ρ'' := ρ' / ρ with hρ''
  have hρ''0 : 0 < ρ'' := div_pos hρ'0 hρ
  set μ₀ : Measure ℂ := foldedCircle 0 1 with hμ₀
  have e1 : foldedCircle (s : ℂ) ρ = μ₀.map (swhAff s ρ) := swcv_fc_eq_map s hρ
  have e2 : foldedCircle (s' : ℂ) ρ' = (μ₀.map (swhAff s'' ρ'')).map (swhAff s ρ) := by
    rw [Measure.map_map (measurable_swhAff s ρ) (measurable_swhAff s'' ρ''),
      swcn2_swhAff_comp, ← swcv_fc_eq_map _ (mul_pos hρ hρ''0)]
    congr 2
    · rw [hs'']; field_simp; push_cast; ring
    · rw [hρ'']; field_simp
  have hid : μ₀ = μ₀.map (swhAff 0 1) := by
    rw [← swcv_fc_eq_map 0 one_pos]; simp [hμ₀]
  have hadm0 : IsAdmissibleH μ₀ := D3Plus.isAdmissibleH_foldedCircle' 0 one_pos
  have hadm1 : IsAdmissibleH (μ₀.map (swhAff s'' ρ'')) := by
    rw [← swcv_fc_eq_map s'' hρ''0]; exact D3Plus.isAdmissibleH_foldedCircle' _ hρ''0
  have hmass : μ₀ univ = (μ₀.map (swhAff s'' ρ'')) univ := by
    rw [Measure.map_apply (measurable_swhAff s'' ρ'') MeasurableSet.univ, preimage_univ]
  have hinv := kernelCov2_map_affine s hρ ⟨(μ₀, μ₀.map (swhAff s'' ρ'')), hadm0, hadm1, hmass⟩
  simp only at hinv
  rw [e1, e2, hinv]
  set Δ := (|s - s'| + |ρ - ρ'|) / ρ with hΔ
  have hΔ0 : 0 ≤ Δ := by positivity
  have hΔ1 : Δ ≤ 1 / 2 := by rw [hΔ, div_le_iff₀ hρ]; linarith
  have hB : ∀ u ∈ closedBall (0 : ℂ) 1, ‖u‖ ≤ 1 := fun u hu => by simpa using hu
  have hdisp : ∀ u ∈ closedBall (0 : ℂ) 1, ‖swhAff 0 1 u - swhAff s'' ρ'' u‖ ≤ Δ := by
    intro u hu
    have hu1 := hB u hu
    simp only [swhAff, Complex.ofReal_zero, zero_add, Complex.ofReal_one, one_mul]
    have e : u - ((s'' : ℂ) + (ρ'' : ℂ) * u) = -(s'' : ℂ) + ((1 - ρ'' : ℝ) : ℂ) * u := by
      push_cast; ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_neg, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs]
    have h1 : |s''| = |s - s'| / ρ := by
      rw [hs'', abs_div, abs_of_pos hρ, abs_sub_comm]
    have h2 : |1 - ρ''| = |ρ - ρ'| / ρ := by
      rw [hρ'', show (1 : ℝ) - ρ' / ρ = (ρ - ρ') / ρ by field_simp, abs_div, abs_of_pos hρ]
    rw [h1, h2, hΔ, add_div]
    have := mul_le_mul_of_nonneg_left hu1 (div_nonneg (abs_nonneg (ρ - ρ')) hρ.le)
    linarith
  have hco1 : ∀ u ∈ closedBall (0 : ℂ) 1, ∀ v ∈ closedBall (0 : ℂ) 1,
      1 / 2 * ‖u - v‖ ≤ ‖swhAff 0 1 u - swhAff 0 1 v‖ := fun u _ v _ => by
    simp only [swhAff, Complex.ofReal_zero, zero_add, Complex.ofReal_one, one_mul]
    linarith [norm_nonneg (u - v)]
  have hρ''h : 1 / 2 ≤ ρ'' := by rw [hρ'', le_div_iff₀ hρ]; linarith
  have hco2 : ∀ u ∈ closedBall (0 : ℂ) 1, ∀ v ∈ closedBall (0 : ℂ) 1,
      1 / 2 * ‖u - v‖ ≤ ‖swhAff s'' ρ'' u - swhAff s'' ρ'' v‖ := fun u _ v _ => by
    have e : swhAff s'' ρ'' u - swhAff s'' ρ'' v = (ρ'' : ℂ) * (u - v) := by
      simp only [swhAff]; ring
    rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ''0]
    exact mul_le_mul_of_nonneg_right hρ''h (norm_nonneg _)
  have hb1 : ∀ u ∈ closedBall (0 : ℂ) 1, ‖swhAff 0 1 u‖ ≤ 2 := fun u hu => by
    simp only [swhAff, Complex.ofReal_zero, zero_add, Complex.ofReal_one, one_mul]
    linarith [hB u hu]
  have hb2 : ∀ u ∈ closedBall (0 : ℂ) 1, ‖swhAff s'' ρ'' u‖ ≤ 2 := fun u hu => by
    have h1 := hdisp u hu
    have h2 := hb1 u hu
    calc ‖swhAff s'' ρ'' u‖ = ‖swhAff 0 1 u - (swhAff 0 1 u - swhAff s'' ρ'' u)‖ := by
          rw [sub_sub_cancel]
      _ ≤ ‖swhAff 0 1 u‖ + ‖swhAff 0 1 u - swhAff s'' ρ'' u‖ := norm_sub_le _ _
      _ ≤ 2 := by
          have : ‖swhAff 0 1 u‖ ≤ 1 := by
            simp only [swhAff, Complex.ofReal_zero, zero_add, Complex.ofReal_one, one_mul]
            exact hB u hu
          linarith
  have h := swcv_kernelCov2_two (measurable_swhAff 0 1) (measurable_swhAff s'' ρ'') hΔ0
    (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) < 1 / 2) hdisp hb1 hb2 hco1 hco2
  rw [← hid] at h
  exact h

/-- **Derivatives over a family** (Cauchy estimates). -/
theorem swcn2_deriv_sub_le {a b ρ M m : ℝ} (hρ : 0 < ρ) {ψ₁ ψ₂ : ℂ → ℂ}
    (h₁ : ψ₁ ∈ BdryClass a b ρ M m) (h₂ : ψ₂ ∈ BdryClass a b ρ M m) {δ : ℝ}
    (hδ : ∀ z ∈ thickening ρ (segC a b), ‖ψ₁ z - ψ₂ z‖ ≤ δ) {t t' : ℝ} (ht : t ∈ Icc a b)
    (ht' : t' ∈ Icc a b) (htt : |t - t'| < ρ / 4) :
    ‖deriv ψ₁ t - deriv ψ₂ t'‖ ≤
      (|M| + 1) / (ρ / 4) / (ρ / 4) * |t - t'| + δ / (ρ / 2) := by
  have hδ0 : 0 ≤ δ := by
    have hmem : (t : ℂ) ∈ thickening ρ (segC a b) := swcv_ball_sub ht (mem_ball_self hρ)
    exact (norm_nonneg _).trans (hδ _ hmem)
  -- same map, two points
  have hA : ‖deriv ψ₁ t - deriv ψ₁ t'‖ ≤ (|M| + 1) / (ρ / 4) / (ρ / 4) * |t - t'| := by
    have hconv : Convex ℝ (ball (t : ℂ) (ρ / 4)) := convex_ball _ _
    have hdiff : ∀ z ∈ ball (t : ℂ) (ρ / 4), DifferentiableAt ℂ (deriv ψ₁) z := fun z hz =>
      ((h₁.1.deriv isOpen_thickening).differentiableAt
        (isOpen_thickening.mem_nhds (swcv_ball_sub ht (ball_subset_ball (by linarith) hz))))
    have hbd : ∀ z ∈ ball (t : ℂ) (ρ / 4), ‖deriv (deriv ψ₁) z‖ ≤
        (|M| + 1) / (ρ / 4) / (ρ / 4) := fun z hz => swcv_deriv2_bound h₁ hρ ht hz
    have hmt : (t : ℂ) ∈ ball (t : ℂ) (ρ / 4) := mem_ball_self (by positivity)
    have hmt' : (t' : ℂ) ∈ ball (t : ℂ) (ρ / 4) := by
      rw [mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
        abs_sub_comm]; exact htt
    have := hconv.norm_image_sub_le_of_norm_deriv_le hdiff hbd hmt' hmt
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at this
    exact this
  -- two maps, same point
  have hB : ‖deriv ψ₁ t' - deriv ψ₂ t'‖ ≤ δ / (ρ / 2) := by
    set f := fun z => ψ₁ z - ψ₂ z with hf
    have hsub : closedBall (t' : ℂ) (ρ / 2) ⊆ thickening ρ (segC a b) := fun z hz =>
      swcv_ball_sub ht' (by rw [mem_ball]; rw [mem_closedBall] at hz; linarith)
    have hfd : DifferentiableOn ℂ f (thickening ρ (segC a b)) := h₁.1.sub h₂.1
    have hmem : (t' : ℂ) ∈ thickening ρ (segC a b) := swcv_ball_sub ht' (mem_ball_self hρ)
    have hderiv : deriv f t' = deriv ψ₁ t' - deriv ψ₂ t' := by
      have d1 := (h₁.1.differentiableAt (isOpen_thickening.mem_nhds hmem))
      have d2 := (h₂.1.differentiableAt (isOpen_thickening.mem_nhds hmem))
      exact deriv_sub d1 d2
    rw [← hderiv]
    apply Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by positivity)
    · refine DifferentiableOn.diffContOnCl ?_
      rw [closure_ball _ (by positivity)]
      exact hfd.mono hsub
    · intro z hz
      exact hδ z (hsub (sphere_subset_closedBall hz))
  calc ‖deriv ψ₁ t - deriv ψ₂ t'‖ = ‖(deriv ψ₁ t - deriv ψ₁ t') + (deriv ψ₁ t' - deriv ψ₂ t')‖ := by
        ring_nf
    _ ≤ _ := (norm_add_le _ _).trans (add_le_add hA hB)

end SWCore
end QuantumZipper
