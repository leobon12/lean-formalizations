import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.Bochner.Set

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# A1R (cut): smoothing limits with a radius-dependent cut-off near the boundary

Deterministic lemma for the D90 route of the last G1 A1b node (`R18.G1A1b2SideTendstoStmt`).
The smoothed integrals `∫ F(z, ρ) dμ(z)` converge to `L` as `ρ ↓ 0` as soon as

* on a cut-off set `N ρ` (in the application: the points within `√ρ` of the real line, where
  the smoothing circles may meet the unzipped segment) the integrand has logarithmic growth,
  `|F(z, ρ)| ≤ C (1 + |log ρ|)`,
* `μ (N ρ) ≤ C_m ρ^β` for some `β > 0`, and
* the integrals over the complement converge to `L`.

This is the "junk times small mass" pattern of Berestycki–Powell, arXiv:2404.16642, Thm 8.16 and
Rem 8.10 (p. 283), with the log growth of circle averages of Hu–Miller–Peres, Ann. Probab. 38
(2010), Prop. 2.1, already used for `R18.maskPullCoreStmt_of_growth_mass` (R18RTCore.lean).
Own elementary proof.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology

namespace QuantumZipper
namespace R18
namespace A1R

/-- `C · C_m · (1 + |log ρ|) · ρ^β → 0` as `ρ ↓ 0`. -/
theorem tendsto_logGrowth_mul_rpow {C Cm β : ℝ} (hβ : 0 < β) :
    Tendsto (fun ρ : ℝ => C * Cm * (ρ ^ β - Real.log ρ * ρ ^ β)) (𝓝[>] 0) (𝓝 0) := by
  have h1 : Tendsto (fun ρ : ℝ => ρ ^ β) (𝓝[>] 0) (𝓝 0) := by
    have := (Real.continuousAt_rpow_const 0 β (Or.inr hβ.le)).tendsto
    rw [Real.zero_rpow hβ.ne'] at this
    exact this.mono_left nhdsWithin_le_nhds
  have h2 := tendsto_log_mul_rpow_nhdsGT_zero hβ
  have := (h1.sub h2).const_mul (C * Cm)
  simpa using this

/-- **Smoothing limit with a radius-dependent cut-off.** -/
theorem tendsto_integral_of_cutoff {μ : Measure ℂ} [IsFiniteMeasure μ] {F : ℂ × ℝ → ℝ}
    {L C Cm β : ℝ} (hβ : 0 < β) (hC : 0 ≤ C) (N : ℝ → Set ℂ)
    (hNm : ∀ ρ, MeasurableSet (N ρ))
    (hint : ∀ ρ : ℝ, 0 < ρ → Integrable (fun z => F (z, ρ)) μ)
    (hgr : ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ᵐ z ∂μ, z ∈ N ρ → |F (z, ρ)| ≤ C * (1 + |Real.log ρ|))
    (hmass : ∀ ρ : ℝ, 0 < ρ → ρ < 1 → μ.real (N ρ) ≤ Cm * ρ ^ β)
    (hfar : Tendsto (fun ρ => ∫ z in (N ρ)ᶜ, F (z, ρ) ∂μ) (𝓝[>] 0) (𝓝 L)) :
    Tendsto (fun ρ => ∫ z, F (z, ρ) ∂μ) (𝓝[>] 0) (𝓝 L) := by
  have hev : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), 0 < ρ ∧ ρ < 1 :=
    Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)
  -- the near part tends to `0`
  have hnear : Tendsto (fun ρ => ∫ z in N ρ, F (z, ρ) ∂μ) (𝓝[>] 0) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (tendsto_logGrowth_mul_rpow (C := C) (Cm := Cm) hβ)
    filter_upwards [hev] with ρ ⟨h0, h1⟩
    have hlog : |Real.log ρ| = -Real.log ρ :=
      abs_of_nonpos (Real.log_nonpos h0.le h1.le)
    have hb := norm_setIntegral_le_of_norm_le_const_ae' (f := fun z => F (z, ρ))
      (measure_lt_top μ (N ρ))
      ((hgr ρ h0 h1).mono fun z hz hzN => by
        rw [Real.norm_eq_abs]; exact hz hzN)
    have hK : 0 ≤ C * (1 + |Real.log ρ|) := mul_nonneg hC (by positivity)
    calc ‖∫ z in N ρ, F (z, ρ) ∂μ‖ ≤ C * (1 + |Real.log ρ|) * μ.real (N ρ) := hb
      _ ≤ C * (1 + |Real.log ρ|) * (Cm * ρ ^ β) :=
          mul_le_mul_of_nonneg_left (hmass ρ h0 h1) hK
      _ = C * Cm * (ρ ^ β - Real.log ρ * ρ ^ β) := by rw [hlog]; ring
  have hsum := hfar.add hnear
  rw [add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [hev] with ρ ⟨h0, _⟩
  rw [add_comm]
  exact integral_add_compl (hNm ρ) (hint ρ h0)

end A1R
end R18
end QuantumZipper
