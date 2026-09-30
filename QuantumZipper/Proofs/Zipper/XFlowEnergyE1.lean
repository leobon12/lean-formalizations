import QuantumZipper.Proofs.Zipper.XFlowEnergyE1Push

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# XFLOW-E1: the radius modulus `FlowE1Stmt`, uniform over `flowBox m`

**Main result** `flowE1Stmt_holds : FlowE1Stmt`: for a continuous driver `W`, `W 0 = 0`, the
Neumann energy of `flowMu W p ρ − flowMu W p ρ'` is `≤ C |ρ − ρ'|^{1/192}` for all
`p ∈ flowBox m`, `ρ, ρ' ∈ [0,1]`.

This is the D33 proof `RegUnif.energyRadStmt_holds` (`UnifUC1Rad.lean`) with the dyadic circle
`fc(d, 2^{-k})` replaced by the circle `fc(d, r)` of `p = (u, s, d, r) ∈ flowBox m`; all constants
are taken uniform over the box via `T = 2m + 2`, `rl = 1/(m+2) ≤ r`, `‖d‖ + r ≤ R₀ = 3(m+2)`
(`fBox_of_mem_flowBox`). The interpolation (`Δ = ρ − ρ'`, `r₀ = Δ^{1/48}`):

* if `ρ' ≥ r₀`: the radius modulus `abs_kernelCov2_flowMu_rad_le` and
  `RegUnif.spaceK_mul_sq_le` give `spaceKs · Δ^{1/24}`;
* if `ρ' < r₀`: the energy triangle inequality `RegUnif.kernelCov2_self_triangle` through
  `flowMu p 0` and PUSH0 `push0_flow` give `8 M Δ^{1/192}`.

Sources: Hu–Miller–Peres, Ann. Probab. 38 (2010), Prop. 2.1; Duplantier–Sheffield, Invent. Math.
185 (2011), Prop. 3.1 (through the D33 lemmas); the interpolation is own elementary argument
(as in D33).
-/

noncomputable section

open MeasureTheory Filter Metric Set
open scoped ENNReal Real Topology

namespace QuantumZipper
namespace F1

open RegCont B2 RegUnif

/-- **XFLOW-E1: `FlowE1Stmt` holds.** -/
theorem flowE1Stmt_holds : FlowE1Stmt := by
  intro m W hW hW0
  set T : ℝ := 2 * (m : ℝ) + 2 with hTdef
  set rl : ℝ := 1 / ((m : ℝ) + 2) with hrldef
  set R₀ : ℝ := 3 * ((m : ℝ) + 2) with hR₀def
  have hT : 0 ≤ T := by positivity
  have hrl : 0 < rl := by positivity
  obtain ⟨Mw, hMw'⟩ := isCompact_Icc.exists_bound_of_continuousOn (hW.continuousOn (s := Icc 0 T))
  have hMw : ∀ t ∈ Icc (0 : ℝ) T, |W t| ≤ Mw := fun t ht => by
    simpa [Real.norm_eq_abs] using hMw' t ht
  have hMw0 : 0 ≤ Mw := (abs_nonneg _).trans (hMw 0 ⟨le_rfl, hT⟩)
  set R1 := revBound (2 * Mw) T R₀ + 1 with hR1
  set Ks := spaceKs Mw T R1 with hKs
  obtain ⟨M0, hM00, hM0⟩ := push0_flow hW hW0 hT hrl (R₀ := R₀)
  refine ⟨|Ks| + 8 * M0, 1 / 192, by positivity, by norm_num, fun p hp ρ hρ ρ' hρ' => ?_⟩
  have hp' : FBox T rl R₀ p := fBox_of_mem_flowBox hp
  wlog hle : ρ' ≤ ρ generalizing ρ ρ'
  · rw [kernelCov2_swap, abs_sub_comm]
    exact this ρ' hρ' ρ hρ (le_of_not_ge hle)
  set E : ℝ → ℝ → ℝ := fun x y =>
    kernelCov2 neumannH (flowMu W p x, flowMu W p y) (flowMu W p x, flowMu W p y) with hE
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
    have h := abs_kernelCov2_flowMu_rad_le hW hW0 hMw hrl hp' hr₀ (hcase.trans hle) hcase
      hρ.2 hρ'.2
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
  · -- small radius: go through `flowMu p 0`
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
      have h := hM0 p hp' σ h0 hσ1
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
    obtain ⟨ha, hma⟩ := admissible_flowMu hW hW0 hMw hrl hp' hρ.1 hρ.2
    obtain ⟨hb, hmb⟩ := admissible_flowMu hW hW0 hMw hrl hp' le_rfl zero_le_one
    obtain ⟨hc, hmc⟩ := admissible_flowMu hW hW0 hMw hrl hp' hρ'.1 hρ'.2
    have htri := kernelCov2_self_triangle ha hb hc (hma.trans hmb.symm) (hmb.trans hmc.symm)
    have hswap : kernelCov2 neumannH (flowMu W p 0, flowMu W p ρ')
        (flowMu W p 0, flowMu W p ρ') = E ρ' 0 := by rw [hE, kernelCov2_swap]
    rw [hswap] at htri
    have hnn : 0 ≤ E ρ ρ' := kernelCov2_self_nonneg ha hc (hma.trans hmc.symm)
    have e1 := hE0 ρ hρ.1 hρ.2 hρ2
    have e2 := hE0 ρ' hρ'.1 hρ'.2 (by linarith)
    rw [abs_of_nonneg hnn]
    change E ρ ρ' ≤ 2 * E ρ 0 + 2 * E ρ' 0 at htri
    nlinarith [abs_nonneg Ks]

end F1
end QuantumZipper
