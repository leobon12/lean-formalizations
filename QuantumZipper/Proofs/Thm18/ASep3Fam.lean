import QuantumZipper.Proofs.Thm18.ASep3Frost

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ASEP3 (step 4): `GenFam` for the dilated A-sep family

**`genFam_muA0_dil`**: on a box of good parameters, for a small dyadic radius cap `ρ₀ = 2^{-m₀}`,
the family `((p, s), ρ) ↦ (muA0 p (ρ₀ ρ)).map (s ·)`, `s ∈ [s₀, s₁]`, `s₀ > 0`, satisfies the
hypotheses `GenFam` of the GENERIC-UC Kolmogorov step. These are the X-measures read by the
regularization of the rescaled field `rescale (ofFun g + X) Q s` at the conclusion measures
(ASEP3 route). Ingredients: `genFam_muA0` (ASepModJ), `genFam_reparam` (radius cap),
`frostman_muA0_small` (ASep3Frost), `genFam_dil` (ASep3Dil).

Own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal

namespace QuantumZipper
namespace ASep

/-- Restricting the radius to `[0, ε]` keeps `GenFam`. -/
theorem genFam_reparam {n : ℕ} {S : Set (Fin n → ℝ)} {μ : (Fin n → ℝ) → ℝ → Measure ℂ}
    {M : ℝ≥0∞} {K c : ℝ} (hF : GenUC.GenFam S μ M K c) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    GenUC.GenFam S (fun p ρ => μ p (ε * ρ)) M K c := by
  have hI : ∀ ρ ∈ Icc (0 : ℝ) 1, ε * ρ ∈ Icc (0 : ℝ) 1 := fun ρ hρ =>
    ⟨mul_nonneg hε.le hρ.1, by nlinarith [hρ.1, hρ.2]⟩
  refine ⟨fun p hp ρ hρ => hF.adm p hp _ (hI ρ hρ), fun p hp ρ hρ => hF.mass p hp _ (hI ρ hρ),
    hF.K_nonneg, hF.c_pos, fun p hp p' hp' ρ hρ ρ' hρ' => ?_⟩
  refine (hF.energy p hp p' hp' _ (hI ρ hρ) _ (hI ρ' hρ')).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ hF.K_nonneg
  refine Real.rpow_le_rpow (by positivity) ?_ hF.c_pos.le
  have : |ε * ρ - ε * ρ'| ≤ |ρ - ρ'| := by
    rw [← mul_sub, abs_mul, abs_of_pos hε]
    exact mul_le_of_le_one_left (abs_nonneg _) hε1
  linarith

/-- **`GenFam` for the dilated A-sep family.** -/
theorem genFam_muA0_dil {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {T α CH : ℝ}
    (hT : 0 < T) (hα : 0 < α) (hα1 : α ≤ 1) (hCH : 0 ≤ CH)
    (hH : ∀ t ∈ Icc (0 : ℝ) T, ∀ t' ∈ Icc (0 : ℝ) T, |t - t'| ≤ 1 / 2 →
      |W t - W t'| ≤ CH * |t - t'| ^ α)
    {d : ℂ} {r : ℝ} (hd : 0 ≤ d.im) (hr : 0 < r) {a₀ a₁ : ℝ} (ha₀ : 0 < a₀)
    {S : Set (Fin 2 → ℝ)} (hS : IsCompact S)
    (hSb : ∀ p ∈ S, p 0 ∈ Icc (0 : ℝ) T ∧ p 1 ∈ Icc a₀ a₁)
    {δ : ℝ} (hδ : 0 < δ)
    (hgood : ∀ a ∈ Icc a₀ a₁,
      ∀ w ∈ Metric.cthickening δ (foldH '' Metric.sphere d r) ∩ {w : ℂ | 0 ≤ w.im},
      ∃ u, IsForwardSol W ((a : ℂ) * w) T u) :
    ∃ m₀ : ℕ, ∀ s₀ s₁ : ℝ, 0 < s₀ → ∃ K c : ℝ,
      GenUC.GenFam (dilSet S s₀ s₁) (dilFam fun p ρ => muA0 W d r p (radius m₀ * ρ)) 1 K c := by
  obtain ⟨M, K, c, hF⟩ := genFam_muA0 hW hW0 hT hα hα1 hCH hH hd hr ha₀ hS hSb hδ hgood
  have hgood0 : ∀ a ∈ Icc a₀ a₁, ∀ w ∈ foldSph d r, ∃ u, IsForwardSol W ((a : ℂ) * w) T u := by
    intro a ha w hw
    refine hgood a ha w ⟨self_subset_cthickening _ hw, ?_⟩
    obtain ⟨y, -, rfl⟩ := hw
    show 0 ≤ (foldH y).im
    rw [TwoPoint.im_foldH]; exact abs_nonneg _
  have hsol : ∀ z ∈ scaledSph d r a₀ a₁, ∃ u, IsForwardSol W z T u := by
    rintro _ ⟨q, hq, rfl⟩; exact hgood0 q.1 hq.1 q.2 hq.2
  obtain ⟨m, hm, hlow⟩ := exists_fwdMap_lower hW hW0 hT.le (isCompact_scaledSph d r a₀ a₁) hsol
  obtain ⟨ρ₁, C, B, hρ₁, hC, hB, hFB⟩ := frostman_muA0_small hW hW0 hr ha₀ hm hgood0 hlow
  obtain ⟨m₀, hm₀⟩ := exists_pow_lt_of_lt_one (lt_min hρ₁ one_pos)
    (show (2 : ℝ)⁻¹ < 1 by norm_num)
  set ρ₀ : ℝ := radius m₀ with hρ₀
  have hρ₀p : 0 < ρ₀ := radius_pos m₀
  have hρ₀m : ρ₀ ≤ min ρ₁ 1 := hm₀.le
  refine ⟨m₀, fun s₀ s₁ hs₀ => ?_⟩
  -- the masses are `1`
  have hmass : ∀ p ∈ S, ∀ ρ ∈ Icc (0 : ℝ) 1, muA0 W d r p ρ univ = 1 := by
    intro p hp ρ _
    have hm' := RTBeur.measurable_fwdMapInv_rt hW hW0 (hSb p hp).1.1
    have hgm := measurable_gA hW hW0 hm hgood0 hlow (hSb p hp).1 (hSb p hp).2
    have hνeq : (foldedCircle d r).map (fun w => fwdMap W (p 0) ((p 1 : ℂ) * w)) =
        (foldedCircle d r).map (gA W d r (p 0) (p 1)) :=
      Measure.map_congr (by
        filter_upwards [ae_mem_foldSph d hr.le] with w hw
        exact (gA_of_mem hw).symm)
    unfold muA0
    rw [hνeq, Measure.map_apply hm' MeasurableSet.univ, preimage_univ]
    show (Measure.bind _ fun y => foldedCircle y ρ) univ = 1
    rw [CircleFubini.bind_circle_univ, Measure.map_apply hgm MeasurableSet.univ, preimage_univ,
      measure_univ]
  have hF1 : GenUC.GenFam S (muA0 W d r) 1 K c :=
    ⟨hF.adm, hmass, hF.K_nonneg, hF.c_pos, hF.energy⟩
  have hF2 := genFam_reparam hF1 hρ₀p (hρ₀m.trans (min_le_right _ _))
  have hdiam : ∀ p ∈ S, ∀ p' ∈ S, dist p p' ≤ T + |a₁ - a₀| := by
    intro p hp p' hp'
    refine (dist_pi_le_iff (by positivity)).2 fun i => ?_
    rw [Real.dist_eq]
    have h0 := (hSb p hp).1; have h0' := (hSb p' hp').1
    have h1 := (hSb p hp).2; have h1' := (hSb p' hp').2
    fin_cases i
    · have : |p 0 - p' 0| ≤ T := abs_sub_le_iff.2 ⟨by linarith [h0.1, h0.2, h0'.1, h0'.2],
        by linarith [h0.1, h0.2, h0'.1, h0'.2]⟩
      simp only [Fin.zero_eta]
      linarith [abs_nonneg (a₁ - a₀)]
    · have : |p 1 - p' 1| ≤ a₁ - a₀ := abs_sub_le_iff.2 ⟨by linarith [h1.1, h1.2, h1'.1, h1'.2],
        by linarith [h1.1, h1.2, h1'.1, h1'.2]⟩
      simp only [Fin.mk_one]
      linarith [le_abs_self (a₁ - a₀)]
  have hρI : ∀ ρ ∈ Icc (0 : ℝ) 1, ρ₀ * ρ ∈ Icc (0 : ℝ) ρ₁ := fun ρ hρ =>
    ⟨mul_nonneg hρ₀p.le hρ.1, (mul_le_of_le_one_right hρ₀p.le hρ.2).trans (hρ₀m.trans (min_le_left _ _))⟩
  exact genFam_dil hF2 hs₀ (by norm_num : (0 : ℝ) < 1 / 3) (by norm_num) hC hB
    (by positivity : (0 : ℝ) ≤ T + |a₁ - a₀|)
    (fun p hp ρ hρ => (hFB p (hSb p hp).1 (hSb p hp).2 _ (hρI ρ hρ)).1)
    (fun p hp ρ hρ => (hFB p (hSb p hp).1 (hSb p hp).2 _ (hρI ρ hρ)).2) hdiam

end ASep
end QuantumZipper
