import QuantumZipper.Proofs.Thm18.ASepModF

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ASEP (mod G): admissibility of `muA0` and the small-radius triangle bound

* `adm_muA0`: `muA0 p ρ` is an admissible probability measure for `ρ ∈ [0,1]` (radius `0`: the
  folded circle `fc(a d, a r)`; radius `ρ > 0`: `RegUnif.goodM_map_bindFc` with the pushed circles
  `goodM_pushed_circle`, as in `F1.flowAdmStmt_holds`);
* `energy_muA0_small`: the triangle inequality for the Neumann energy through `muA0 p 0` and
  `muA0 p' 0` with PUSH0 (`push0_muA0`) and the radius-`0` modulus (`energy_muA0_zero_le`).

Own bookkeeping (as XFLOW-E1, D33).
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace QuantumZipper
namespace ASep

open RegCont RegUnif B2

/-- **Admissibility and mass of `muA0`.** -/
theorem adm_muA0 {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {d : ℂ}
    {r a₀ a₁ T m M : ℝ} (hr : 0 < r) (ha₀ : 0 < a₀) (hm : 0 < m)
    (hgood0 : ∀ a ∈ Icc a₀ a₁, ∀ w ∈ foldSph d r, ∃ u, IsForwardSol W ((a : ℂ) * w) T u)
    (hlow : ∀ z ∈ scaledSph d r a₀ a₁, ∀ s ∈ Icc (0 : ℝ) T, m ≤ ‖fwdMap W s z‖)
    (hM : ∀ t ∈ Icc (0 : ℝ) T, |W t| ≤ M)
    {p : Fin 2 → ℝ} (hp0 : p 0 ∈ Icc (0 : ℝ) T) (hp1 : p 1 ∈ Icc a₀ a₁)
    {ρ : ℝ} (hρ : ρ ∈ Icc (0 : ℝ) 1) :
    IsAdmissibleH (muA0 W d r p ρ) ∧ muA0 W d r p ρ univ = 1 := by
  have ha : 0 < p 1 := ha₀.trans_le hp1.1
  rcases hρ.1.eq_or_lt with h | h
  · rw [← h, muA0_zero hW hW0 hr ha₀ hm hgood0 hlow hp0 hp1]
    exact ⟨D3Plus.isAdmissibleH_foldedCircle' _ (mul_pos ha hr), measure_univ⟩
  · set R : ℝ := a₁ * (‖d‖ + r) + M + 2 * T / m + 1 with hRdef
    set g := gA W d r (p 0) (p 1) with hgdef
    have hgm : Measurable g := measurable_gA hW hW0 hm hgood0 hlow hp0 hp1
    set α := (foldedCircle d r).map g with hαdef
    have hαP : IsProbabilityMeasure α := inferInstance
    have hfacts := alphaA_facts hW hW0 hr ha₀ hm hgood0 hlow hM hp0 hp1
    have hαR : ∀ᵐ z ∂α, ‖z‖ ≤ R :=
      (ae_map_iff hgm.aemeasurable (measurableSet_le measurable_norm measurable_const)).2
        (hfacts.mono fun x hx => hx.2.2)
    have hVu : Continuous (vrev W (p 0)) := continuous_vrev hW (p 0)
    have hψm := TwoPoint.measurable_revMap hVu hp0.1
    have hmuα : ((foldedCircle d r).map fun w => fwdMap W (p 0) ((p 1 : ℂ) * w)) = α :=
      Measure.map_congr ((ae_mem_foldSph d hr.le).mono fun x hx => (gA_of_mem hx).symm)
    have e : muA0 W d r p ρ = (bindFc α ρ).map (revMap (vrev W (p 0)) (p 0)) := by
      unfold muA0
      rw [hmuα]
      refine Measure.map_congr ?_
      filter_upwards [CoordReg.bind_fc_mem_H_norm α h hαR] with x hx
      exact fwdMapInv_eq_revMap_vrev hW hW0 hp0.1 hx.1
    rw [e]
    have hG := goodM_map_bindFc hψm (A := α) (ρ := ρ) (α := 1 / 3)
      (C := frostC T ρ (R + 1)) (B := revBound (2 * M) T (R + 1))
      (by unfold frostC; positivity)
      (hαR.mono fun z hz =>
        (goodM_pushed_circle hW hW0 hM hp0 h le_rfl (by linarith [hρ.2])).2)
    exact ⟨hG.admissible (by norm_num), hG.prob.measure_univ⟩

/-- **Small-radius (triangle) bound.** -/
theorem energy_muA0_small {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {d : ℂ}
    {r a₀ a₁ T m M : ℝ} (hr : 0 < r) (ha₀ : 0 < a₀) (hm : 0 < m)
    (hgood0 : ∀ a ∈ Icc a₀ a₁, ∀ w ∈ foldSph d r, ∃ u, IsForwardSol W ((a : ℂ) * w) T u)
    (hlow : ∀ z ∈ scaledSph d r a₀ a₁, ∀ s ∈ Icc (0 : ℝ) T, m ≤ ‖fwdMap W s z‖)
    (hM : ∀ t ∈ Icc (0 : ℝ) T, |W t| ≤ M) {M₀ C₀ b : ℝ} (hM₀ : 0 ≤ M₀)
    (h0 : ∀ p : Fin 2 → ℝ, p 0 ∈ Icc (0 : ℝ) T → p 1 ∈ Icc a₀ a₁ →
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
      |kernelCov2 neumannH (muA0 W d r p ρ, muA0 W d r p 0) (muA0 W d r p ρ, muA0 W d r p 0)| ≤
        M₀ * ρ ^ (1 / 4 : ℝ))
    (hz : ∀ p p' : Fin 2 → ℝ, p 0 ∈ Icc (0 : ℝ) T → p 1 ∈ Icc a₀ a₁ →
      p' 0 ∈ Icc (0 : ℝ) T → p' 1 ∈ Icc a₀ a₁ →
      |kernelCov2 neumannH (muA0 W d r p 0, muA0 W d r p' 0) (muA0 W d r p 0, muA0 W d r p' 0)| ≤
        C₀ * (|p 1 - p' 1| * (‖d‖ + r)) ^ b)
    {p p' : Fin 2 → ℝ} (hp0 : p 0 ∈ Icc (0 : ℝ) T) (hp1 : p 1 ∈ Icc a₀ a₁)
    (hp0' : p' 0 ∈ Icc (0 : ℝ) T) (hp1' : p' 1 ∈ Icc a₀ a₁)
    {ρ ρ' : ℝ} (hρ : ρ ∈ Icc (0 : ℝ) 1) (hρ' : ρ' ∈ Icc (0 : ℝ) 1) :
    |kernelCov2 neumannH (muA0 W d r p ρ, muA0 W d r p' ρ') (muA0 W d r p ρ, muA0 W d r p' ρ')| ≤
      2 * (M₀ * ρ ^ (1 / 4 : ℝ)) + 4 * (C₀ * (|p 1 - p' 1| * (‖d‖ + r)) ^ b) +
        4 * (M₀ * ρ' ^ (1 / 4 : ℝ)) := by
  have z01 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have A1 := adm_muA0 hW hW0 hr ha₀ hm hgood0 hlow hM hp0 hp1 hρ
  have A2 := adm_muA0 hW hW0 hr ha₀ hm hgood0 hlow hM hp0 hp1 z01
  have A3 := adm_muA0 hW hW0 hr ha₀ hm hgood0 hlow hM hp0' hp1' z01
  have A4 := adm_muA0 hW hW0 hr ha₀ hm hgood0 hlow hM hp0' hp1' hρ'
  -- PUSH0 extended to `ρ = 0`
  have h0' : ∀ q : Fin 2 → ℝ, q 0 ∈ Icc (0 : ℝ) T → q 1 ∈ Icc a₀ a₁ → ∀ s ∈ Icc (0 : ℝ) 1,
      kernelCov2 neumannH (muA0 W d r q s, muA0 W d r q 0) (muA0 W d r q s, muA0 W d r q 0) ≤
        M₀ * s ^ (1 / 4 : ℝ) := by
    intro q hq0 hq1 s hs
    rcases hs.1.eq_or_lt with hs0 | hs0
    · rw [← hs0]
      have : kernelCov2 neumannH (muA0 W d r q 0, muA0 W d r q 0)
          (muA0 W d r q 0, muA0 W d r q 0) = 0 := by unfold kernelCov2; ring
      rw [this]; positivity
    · exact (le_abs_self _).trans (h0 q hq0 hq1 s hs0 hs.2)
  have t1 := kernelCov2_self_triangle A1.1 A2.1 A4.1 (A1.2.trans A2.2.symm) (A2.2.trans A4.2.symm)
  have t2 := kernelCov2_self_triangle A2.1 A3.1 A4.1 (A2.2.trans A3.2.symm) (A3.2.trans A4.2.symm)
  have e12 := h0' p hp0 hp1 ρ hρ
  have e23 := (le_abs_self _).trans (hz p p' hp0 hp1 hp0' hp1')
  have e34 := h0' p' hp0' hp1' ρ' hρ'
  rw [kernelCov2_swap] at e34
  rw [abs_of_nonneg (kernelCov2_self_nonneg A1.1 A4.1 (A1.2.trans A4.2.symm))]
  linarith

end ASep
end QuantumZipper
