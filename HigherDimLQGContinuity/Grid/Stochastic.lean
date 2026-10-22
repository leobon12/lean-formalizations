import HigherDimLQGContinuity.Grid.Profile
import HigherDimLQGContinuity.Param.Interval
import HigherDimLQGContinuity.Endpoint.Profile

/-!
# Stochastic continuity of logarithmic profiles

This is Part C `c:lem-stoch`.  The depth in `Prop37Shape` is real, so a fixed arbitrarily
large depth suffices for each requested probability bound; no floor or division by the
parameter gap is needed here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric

/-- For every fixed profile threshold, comparison of a convergent deterministic sequence with
an arbitrary strong metric at its limit has probability tending to zero. -/
theorem tendstoInMeasure_profile_of_tendsto {d : ℕ} (hd : 3 ≤ d) (hP : Prop37Shape d)
    {lo hi ξ : ℝ} (hlo : 0 < lo) (hlohi : lo < hi)
    (hhi : 0 < hi ∧ Real.sqrt (2 * d) < distExp d hi)
    (hξ : ξ ∈ Icc lo hi) {t : ℕ → ℝ} (ht : ∀ k, t k ∈ Icc lo hi)
    (htend : Tendsto t atTop (𝓝 ξ))
    (D : DistRd d → ContMetric d) (hD : IsStrongExpMetric d ξ (distExp d ξ) D)
    {R δ : ℝ} (hR : 1 ≤ R) (hδ : 0 < δ) (hδ8 : δ < 1 / 8) :
    ∀ η : ℝ, 0 < η → ∀ᶠ k : ℕ in atTop,
      normLGFLaw d {g | ENNReal.ofReal δ <
        supDistLU d R (gridProfile d (t k) g) (logProfile (rho D g).1)} ≤ ENNReal.ofReal η := by
  obtain ⟨ps, c', _hps, _hps1, _hc', hshape⟩ := hP hi hhi.1 hhi.2
  obtain ⟨B, M, C, c, hB, hM, hc, _hc1, hC, hcmp⟩ := hshape R hR
  have hhiS : hi ∈ subcritSet d := ⟨hhi.1, hhi.2⟩
  obtain ⟨μ, _hμ, _hμ1, _hμ2, hsub, _⟩ := gap24 (by omega : 2 ≤ d) hhiS
  have hloI : lo ∈ Ioc (0 : ℝ) hi := ⟨hlo, hlohi.le⟩
  have hnode (k : ℕ) : t k ∈ subcritSet d :=
    hsub ⟨hlo.trans_le (ht k).1, (ht k).2⟩
  have hcoeff : 0 < c * δ ^ M := mul_pos hc (Real.rpow_pos_of_pos hδ _)
  have hfac : 0 ≤ C * δ ^ (-M) := by positivity
  have hdecay : Tendsto (fun n : ℝ => C * δ ^ (-M) * Real.exp (-(c * δ ^ M * n)))
      atTop (𝓝 0) := by
    have hneg : -(c * δ ^ M) < 0 := neg_neg_iff_pos.mpr hcoeff
    have hexp := Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg hneg)
    have h := hexp.const_mul (C * δ ^ (-M))
    simpa only [Function.comp_def, id_eq, neg_mul, mul_zero] using h
  intro η hη
  have hsmall : ∀ᶠ n : ℝ in atTop,
      C * δ ^ (-M) * Real.exp (-(c * δ ^ M * n)) < η :=
    hdecay.eventually (Iio_mem_nhds hη)
  have hlarge : ∀ᶠ n : ℝ in atTop,
      C * δ ^ (-M) * Real.log (C / δ) ≤ n := eventually_ge_atTop _
  obtain ⟨n, hnsmall, hnlarge⟩ := (hsmall.and hlarge).exists
  have hNpos : 0 < n := by
    have hlog : 0 < Real.log (C / δ) := Real.log_pos (by
      have : (1 : ℝ) < C / δ := (lt_div_iff₀ hδ).2 (by linarith [hC, hδ8])
      exact this)
    have : 0 < C * δ ^ (-M) * Real.log (C / δ) := by positivity
    linarith
  have htgap : Tendsto (fun k => |t k - ξ|) atTop (𝓝 0) := by
    convert (htend.sub tendsto_const_nhds).abs using 1; simp
  have hbound : 0 < min (Real.exp (-(C * lo ^ (-B) * δ ^ (-B)))) (c * δ / n) := by
    apply lt_min
    · exact Real.exp_pos _
    · exact div_pos (mul_pos hc hδ) hNpos
  have hev : ∀ᶠ k : ℕ in atTop,
      |t k - ξ| ≤ min (Real.exp (-(C * lo ^ (-B) * δ ^ (-B)))) (c * δ / n) :=
    htgap.eventually_le_const hbound
  filter_upwards [hev] with k hk
  have hnodeI := ht k
  have hstrong := strongAt_spec hd (hnode k)
  have hgap1 : |t k - ξ| ≤ Real.exp (-(C * lo ^ (-B) * δ ^ (-B))) := hk.trans (min_le_left _ _)
  have hgap2 : |t k - ξ| * n ≤ c * δ := by
    have hn := hk.trans (min_le_right _ _)
    have := mul_le_mul_of_nonneg_right hn hNpos.le
    rwa [div_mul_cancel₀ _ hNpos.ne'] at this
  have hcmp' := hcmp lo hloI (t k) hnodeI ξ hξ (strongAt d (t k)) D
    hstrong hD δ hδ hδ8 n hnlarge hgap2 (Or.inl hgap1)
  change normLGFLaw d {g | ENNReal.ofReal δ <
      supDistLU d R (gridProfile d (t k) g) (logProfile (rho D g).1)} ≤ _ at hcmp'
  exact hcmp'.trans (ENNReal.ofReal_le_ofReal hnsmall.le)

end HigherDimLQGContinuity
