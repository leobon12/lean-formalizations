import QuantumZipper.Proofs.Zipper.UnifUC1RadBasic

/-!
# UNIF-RC3-E1 (decision D33): `EnergyRadStmt T` holds

**Main result** `energyRadStmt_holds : EnergyRadStmt T` (all `T`): for a continuous driver `W`,
`W 0 = 0`, and a dyadic folded circle `fc(d, 2^{-k})`, the Neumann energy of
`muUS p ρ − muUS p ρ'` is `≤ C |ρ − ρ'|^{1/192}` on `tri T × [0,1]²`.

Proof (interpolation, as planned in D33). Let `ρ' ≤ ρ`, `Δ = ρ − ρ' > 0`, `r₀ = Δ^{1/48}`.

* If `ρ' ≥ r₀`: the radius modulus at radii `≥ r₀` (`abs_kernelCov2_muUS_rad_le`, built on MIX and
  the JointMod space modulus) gives `spaceK(r₀)·Δ^{1/12}`, and `spaceK(r₀)·r₀² ≤ spaceKs`
  (`spaceK_mul_sq_le`), so the bound is `spaceKs·Δ^{1/12 − 1/24}`.
* If `ρ' < r₀`: then `ρ < 2 r₀`, and the triangle inequality for the energy through
  `muUS p 0` (`kernelCov2_self_triangle`) with PUSH0 (`push0_unif`: `E(σ, 0) ≤ M σ^{1/4}`)
  gives `≤ 8 M (r₀)^{1/4} = 8 M Δ^{1/192}`.

Sources: Hu–Miller–Peres, Ann. Probab. 38 (2010), Prop. 2.1; Duplantier–Sheffield, Invent. Math.
185 (2011), Prop. 3.1. The interpolation `min(A, B)` over the two regimes is an own elementary
argument.
-/

noncomputable section

open MeasureTheory Filter Metric Set
open scoped ENNReal Real Topology

namespace QuantumZipper
namespace RegUnif

open RegCont B2

variable {W : ℝ → ℝ}

/-- Every `muUS p σ`, `σ ∈ [0,1]`, is an admissible probability measure. -/
theorem admissible_muUS (hW : Continuous W) (hW0 : W 0 = 0) {T Mw : ℝ}
    (hMw : ∀ t ∈ Icc (0 : ℝ) T, |W t| ≤ Mw) (d : ℂ) (k : ℕ) {p : ℝ × ℝ} (hp : p ∈ tri T)
    {σ : ℝ} (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    IsAdmissibleH (muUS W d k p σ) ∧ muUS W d k p σ univ = 1 := by
  rcases hσ.eq_or_lt with h | h
  · subst h; exact admissible_muUS_zero hW hW0 hMw d k hp
  have hT : 0 ≤ T := hp.1.trans (by linarith [hp.2.1, hp.2.2])
  have hu : p.1 ∈ Icc (0 : ℝ) T := ⟨hp.1, by linarith [hp.2.1, hp.2.2]⟩
  have := isProbabilityMeasure_alphaUS hW d k hp
  have hψm := TwoPoint.measurable_revMap (continuous_vrev hW p.1) hp.1
  have hα := alphaUS_ae_H_norm hW hMw d k hp
  rw [muUS_eq_map hW hW0 hMw d k hp h]
  have hG := goodM_map_bindFc hψm (ρ := σ) (α := 1 / 3)
    (C := frostC T σ (revBound (2 * Mw) T (‖d‖ + radius k) + 1))
    (B := revBound (2 * Mw) T (revBound (2 * Mw) T (‖d‖ + radius k) + 1))
    (by unfold frostC; positivity)
    (hα.mono fun z hz => (goodM_pushed_circle hW hW0 hMw hu h le_rfl (by linarith [hz.2])).2)
  exact ⟨hG.admissible (by norm_num), hG.prob.measure_univ⟩

/-- **UNIF-RC3-E1: `EnergyRadStmt T` holds.** -/
theorem energyRadStmt_holds (T : ℝ) : EnergyRadStmt T := by
  intro W hW hW0 d k
  by_cases hT : 0 ≤ T
  swap
  · refine ⟨0, 1, le_rfl, one_pos, fun p hp => ?_⟩
    exact absurd (add_nonneg hp.1 hp.2.1 |>.trans hp.2.2) hT
  obtain ⟨Mw, hMw'⟩ := isCompact_Icc.exists_bound_of_continuousOn (hW.continuousOn (s := Icc 0 T))
  have hMw : ∀ t ∈ Icc (0 : ℝ) T, |W t| ≤ Mw := fun t ht => by
    simpa [Real.norm_eq_abs] using hMw' t ht
  have hMw0 : 0 ≤ Mw := (abs_nonneg _).trans (hMw 0 ⟨le_rfl, hT⟩)
  set R1 := revBound (2 * Mw) T (‖d‖ + radius k) + 1 with hR1
  set Ks := spaceKs Mw T R1 with hKs
  obtain ⟨M0, hM00, hM0⟩ := push0_unif hW hW0 hT d k
  refine ⟨|Ks| + 8 * M0, 1 / 192, by positivity, by norm_num, fun p hp ρ hρ ρ' hρ' => ?_⟩
  wlog hle : ρ' ≤ ρ generalizing ρ ρ'
  · rw [kernelCov2_swap, abs_sub_comm]
    exact this ρ' hρ' ρ hρ (le_of_not_ge hle)
  set E : ℝ → ℝ → ℝ := fun x y =>
    kernelCov2 neumannH (muUS W d k p x, muUS W d k p y) (muUS W d k p x, muUS W d k p y) with hE
  change |E ρ ρ'| ≤ _
  set Δ := ρ - ρ' with hΔ
  have hΔ0 : 0 ≤ Δ := by linarith
  have hΔ1 : Δ ≤ 1 := by linarith [hρ.2, hρ'.1]
  rw [abs_of_nonneg hΔ0]
  have hC0 : 0 ≤ |Ks| + 8 * M0 := by positivity
  rcases hΔ0.eq_or_lt with hΔz | hΔpos
  · have e : ρ' = ρ := by linarith
    have : E ρ ρ' = 0 := by rw [hE, e]; unfold kernelCov2; ring
    rw [this, abs_zero]; positivity
  set r₀ := Δ ^ (1 / 48 : ℝ) with hr₀def
  have hr₀ : 0 < r₀ := Real.rpow_pos_of_pos hΔpos _
  have hr₀1 : r₀ ≤ 1 := Real.rpow_le_one hΔ0 hΔ1 (by norm_num)
  have hΔr : Δ ≤ r₀ := by
    have := Real.rpow_le_rpow_of_exponent_ge' hΔ0 hΔ1 (by norm_num) (show (1 / 48 : ℝ) ≤ 1 by
      norm_num)
    rwa [Real.rpow_one] at this
  have hp192 : 0 ≤ Δ ^ (1 / 192 : ℝ) := Real.rpow_nonneg hΔ0 _
  by_cases hcase : r₀ ≤ ρ'
  · -- both radii `≥ r₀`
    have h := abs_kernelCov2_muUS_rad_le hW hW0 hMw d k hp hr₀ (hcase.trans hle) hcase hρ.2 hρ'.2
    rw [← hR1, ← hΔ, abs_of_nonneg hΔ0] at h
    have hK := spaceK_mul_sq_le (R := R1) hMw0 hT hr₀ hr₀1
    have hr2 : r₀ ^ 2 = Δ ^ (1 / 24 : ℝ) := by
      rw [hr₀def, ← Real.rpow_natCast, ← Real.rpow_mul hΔ0]; norm_num
    have h12 : Δ ^ (1 / 12 : ℝ) = r₀ ^ 2 * Δ ^ (1 / 24 : ℝ) := by
      rw [hr2, ← Real.rpow_add hΔpos]; norm_num
    have h24 : Δ ^ (1 / 24 : ℝ) ≤ Δ ^ (1 / 192 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge' hΔ0 hΔ1 (by norm_num) (by norm_num)
    have hp24 : 0 ≤ Δ ^ (1 / 24 : ℝ) := Real.rpow_nonneg hΔ0 _
    calc |E ρ ρ'| ≤ spaceK Mw T r₀ R1 * Δ ^ (1 / 12 : ℝ) := h
      _ = (spaceK Mw T r₀ R1 * r₀ ^ 2) * Δ ^ (1 / 24 : ℝ) := by rw [h12]; ring
      _ ≤ |Ks| * Δ ^ (1 / 24 : ℝ) :=
          mul_le_mul_of_nonneg_right (hK.trans (le_abs_self _)) hp24
      _ ≤ |Ks| * Δ ^ (1 / 192 : ℝ) := mul_le_mul_of_nonneg_left h24 (abs_nonneg _)
      _ ≤ (|Ks| + 8 * M0) * Δ ^ (1 / 192 : ℝ) := by nlinarith
  · -- small radius: go through `muUS p 0`
    push Not at hcase
    have hρ2 : ρ ≤ 2 * r₀ := by linarith
    have h2 : (2 : ℝ) ^ (1 / 4 : ℝ) ≤ 2 := by
      have := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num)
        (show (1 / 4 : ℝ) ≤ 1 by norm_num)
      rwa [Real.rpow_one] at this
    have hr4 : r₀ ^ (1 / 4 : ℝ) = Δ ^ (1 / 192 : ℝ) := by
      rw [hr₀def, ← Real.rpow_mul hΔ0]; norm_num
    have hE0 : ∀ σ : ℝ, 0 ≤ σ → σ ≤ 1 → σ ≤ 2 * r₀ → E σ 0 ≤ 2 * M0 * Δ ^ (1 / 192 : ℝ) := by
      intro σ hσ hσ1 hσr
      rcases hσ.eq_or_lt with h0 | h0
      · have : E σ 0 = 0 := by rw [hE, ← h0]; unfold kernelCov2; ring
        rw [this]; positivity
      have h := hM0 p hp σ h0 hσ1
      have hpow : σ ^ (1 / 4 : ℝ) ≤ (2 * r₀) ^ (1 / 4 : ℝ) :=
        Real.rpow_le_rpow h0.le hσr (by norm_num)
      rw [Real.mul_rpow (by norm_num) hr₀.le, hr4] at hpow
      calc E σ 0 ≤ |E σ 0| := le_abs_self _
        _ ≤ M0 * σ ^ (1 / 4 : ℝ) := h
        _ ≤ M0 * ((2 : ℝ) ^ (1 / 4 : ℝ) * Δ ^ (1 / 192 : ℝ)) :=
            mul_le_mul_of_nonneg_left hpow hM00
        _ ≤ 2 * M0 * Δ ^ (1 / 192 : ℝ) := by
            have := mul_le_mul_of_nonneg_right h2 hp192
            nlinarith [mul_le_mul_of_nonneg_left this hM00]
    obtain ⟨ha, hma⟩ := admissible_muUS hW hW0 hMw d k hp hρ.1 hρ.2
    obtain ⟨hb, hmb⟩ := admissible_muUS hW hW0 hMw d k hp le_rfl zero_le_one
    obtain ⟨hc, hmc⟩ := admissible_muUS hW hW0 hMw d k hp hρ'.1 hρ'.2
    have htri := kernelCov2_self_triangle ha hb hc (hma.trans hmb.symm) (hmb.trans hmc.symm)
    have hswap : kernelCov2 neumannH (muUS W d k p 0, muUS W d k p ρ')
        (muUS W d k p 0, muUS W d k p ρ') = E ρ' 0 := by rw [hE, kernelCov2_swap]
    rw [hswap] at htri
    have hnn : 0 ≤ E ρ ρ' := kernelCov2_self_nonneg ha hc (hma.trans hmc.symm)
    have e1 := hE0 ρ hρ.1 hρ.2 hρ2
    have e2 := hE0 ρ' hρ'.1 hρ'.2 (by linarith)
    rw [abs_of_nonneg hnn]
    change E ρ ρ' ≤ 2 * E ρ 0 + 2 * E ρ' 0 at htri
    nlinarith [abs_nonneg Ks]

end RegUnif
end QuantumZipper
