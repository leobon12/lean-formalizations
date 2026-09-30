import QuantumZipper.Proofs.Thm18.G1Side3Mu

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-SIDE3 (14): the area limit of the pulled-back canonical field, per sample

With the inputs of `G1Side.tendsto_area_rect` on the rectangles `R_n = [-n, n] × [1/n, n]` (and the
continuum limits on the larger rectangles `U_n`), the pulled-back canonical field
`coordChange (rescale w Q s) ψ Q` has the area limit `pullMu μ_w (s ψ)` along all radii
(`hasAreaLimit_sample`): every compact subset of `ℍ` lies inside some `R_n`, and the limit
functional of Sheffield–Wang's transport is the pullback (`G1Side.integral_pullMu`).
Own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Metric Function
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace G1Side

open SWCore

theorem areaClass_mono {ψ : ℂ → ℂ} {a b c d ρ M m ρ' M' m' : ℝ} (hψ : ψ ∈ AreaClass a b c d ρ M m)
    (hρ : ρ' ≤ ρ) (hM : M ≤ M') (hm : m' ≤ m) : ψ ∈ AreaClass a b c d ρ' M' m' := by
  have hth : thickening ρ' (rectC a b c d) ⊆ thickening ρ (rectC a b c d) := thickening_mono hρ _
  refine ⟨hψ.1.mono hth, hψ.2.1.mono hth, fun z hz => ?_, fun z hz => hm.trans (hψ.2.2.2 z hz)⟩
  obtain ⟨h1, h2⟩ := hψ.2.2.1 z (hth hz)
  exact ⟨h1.trans hM, hρ.trans h2⟩

/-- A radius below `2^{-k₁}` is `α 2^{-k}` with `α ∈ [1,2]` and `k ≥ k₁`. -/
theorem exists_offset {k₁ : ℕ} {ρ : ℝ} (hρ : 0 < ρ) (hρk : ρ < radius k₁) :
    ∃ k ≥ k₁, ∃ α ∈ Icc (1 : ℝ) 2, ρ = α * radius k := by
  have hex : ∃ k : ℕ, radius k ≤ ρ := by
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hρ (by norm_num : (2 : ℝ)⁻¹ < 1)
    exact ⟨k, hk.le⟩
  classical
  let k := Nat.find hex
  have hk : radius k ≤ ρ := Nat.find_spec hex
  have hkk : k₁ < k := by
    by_contra hle
    push_neg at hle
    have : radius k₁ ≤ radius k := by
      unfold radius; exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hle
    linarith
  obtain ⟨j, hj⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hj' : ρ < radius j := not_le.1 (Nat.find_min hex (by omega : j < k))
  have hr : radius k = radius j / 2 := by
    rw [hj]; unfold radius; rw [pow_succ]; ring
  refine ⟨k, hkk.le, ρ / radius k, ⟨?_, ?_⟩, (div_mul_cancel₀ ρ (radius_pos k).ne').symm⟩
  · rw [le_div_iff₀ (radius_pos k)]; linarith
  · rw [div_le_iff₀ (radius_pos k)]; rw [hr] at hk ⊢; linarith

/-- The rectangles `R_n`. -/
def recR (n : ℕ) : Set ℂ := rectC (-n) n (1 / (n + 1 : ℝ)) n

theorem recR_subset_H (n : ℕ) : recR n ⊆ H := fun z hz =>
  show 0 < z.im from lt_of_lt_of_le (by positivity) hz.2.1

/-- Every compact subset of `ℍ` lies in the interior of some `R_n`. -/
theorem exists_recR {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ H) :
    ∃ n : ℕ, K ⊆ interior (recR n) := by
  rcases K.eq_empty_or_nonempty with he | hne
  · exact ⟨0, by simp [he]⟩
  obtain ⟨B, hB⟩ := hK.isBounded.exists_norm_le
  obtain ⟨z₀, hz₀, hmin⟩ := hK.exists_isMinOn hne Complex.continuous_im.continuousOn
  have hc : 0 < z₀.im := hKH hz₀
  obtain ⟨n, hn⟩ := exists_nat_gt (B + 1 / z₀.im)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB z₀ hz₀)
  refine ⟨n, fun z hz => ?_⟩
  have hzB := hB z hz
  have hre := Complex.abs_re_le_norm z
  have him := Complex.abs_im_le_norm z
  have hzim : z₀.im ≤ z.im := hmin hz
  have hn' : (1 : ℝ) / (n + 1) < z₀.im := by
    rw [div_lt_iff₀ (by positivity)]
    have : 1 / z₀.im < n + 1 := by linarith
    rw [div_lt_iff₀ hc] at this; linarith
  have hsub : Metric.ball z (min (z.im - 1 / (n + 1)) (n - B)) ⊆ recR n := by
    intro u hu
    have hd := mem_ball.1 hu
    have h1 := Complex.abs_re_le_norm (u - z)
    have h2 := Complex.abs_im_le_norm (u - z)
    rw [← dist_eq_norm, Complex.sub_re] at h1
    rw [← dist_eq_norm, Complex.sub_im] at h2
    obtain ⟨h1a, h1b⟩ := abs_le.1 h1
    obtain ⟨h2a, h2b⟩ := abs_le.1 h2
    have hm1 := min_le_left (z.im - 1 / (n + 1)) (n - B)
    have hm2 := min_le_right (z.im - 1 / (n + 1)) (n - B)
    obtain ⟨hre1, hre2⟩ := abs_le.1 hre
    obtain ⟨him1, him2⟩ := abs_le.1 him
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  refine interior_maximal hsub isOpen_ball ?_
  have hpos : 0 < 1 / z₀.im := by positivity
  exact mem_ball_self (lt_min (by linarith) (by linarith))

end G1Side
end QuantumZipper
