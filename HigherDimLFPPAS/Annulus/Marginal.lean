import HigherDimLFPPAS.Annulus.MarginalPinned

/-!
# Lemma 3.2, marginal part, for the Borel good event `E′` (packet L32p)

`lemma32Marginal_holds` proves the interface `Core.Lemma32Marginal` (paper Lemma 3.2, (3.6), in the corrected form of
`planning/audits/MA1-sections-1-3.md` Details A9–A10: the Borel event `E′ = Core.GoodAnnulus` and the uniform statement
"`∃ ε₀, ∀ ε < ε₀, ∀ z, ∀ r ∈ 𝒩_ε(u)`" that Lemma 3.3 consumes) from the standing hypotheses `Core.Setting` and the
interfaces `LocFieldScaling`, `CoordScaling`, `AffineInternalScaling` (packet SC), `PairLaw`, `RescaledConv`.

For `p < 1` the constant `A ≥ 1` is chosen from the law of `D_h` only (`l32p_choose_A`), before `η, u, q₀`. Then, for
`ε` small, `z` arbitrary and `r ∈ 𝒩_ε(u)` (so `ε ≤ r ≤ 1` and `8 ε^{q₀} ≤ r · 8 ε^{q₀ − u}`):
`P[E′_ε(z, r)] ≥ P[Ẽ(D_g, 𝔐_{ε,ε/r}(g); 8 ε^{q₀−u})]` (Step 1, `l32p_ae_goodAnnulus_of_unit`, `g = recentAff r z h`)
`= P[Ẽ(D_h, 𝔐_{ε,ε/r}(h); 8 ε^{q₀−u})]` (Step 2, `l32p_prob_unit_eq`) `≥ p` (Step 3, `l32p_pinned`).
Probabilities are outer measures throughout.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace HigherDimLFPPAS.Annulus

open HigherDimLFPPAS.Core HigherDimLQGMetric
open HigherDimLFPP (Rd)

/-- **Lemma 3.2, marginal part, for `E′`** (MA1 A10): for every `p < 1` there is `A ≥ 1`, independent of `η, u, q₀`,
such that for every `η > 0`, `0 < u < q₀ < 1` there is `ε₀ > 0` with `P[E′_ε(z, r)] ≥ p` for all `ε ∈ (0, ε₀)`, all
centres `z` and all `r ∈ 𝒩_ε(u)`. -/
theorem lemma32Marginal_holds {d : ℕ} {ξ Q : ℝ} {κ : Rd d → ℝ} {D : DistRd d → ContMetric d}
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistRd d}
    (hS : Core.Setting d ξ Q κ D P h) (hsc : Core.LocFieldScaling κ)
    (hcs : Core.CoordScaling ξ Q D P h) (hai : Core.AffineInternalScaling d)
    (hpl : Core.PairLaw κ ξ D P h) (hrc : Core.RescaledConv κ ξ D P h) :
    Core.Lemma32Marginal κ ξ Q D P h := by
  intro p hp
  obtain ⟨A, hA1, hA⟩ := l32p_choose_A hS hp
  refine ⟨A, hA1, fun η u q₀ hη hu huq hq1 => ?_⟩
  obtain ⟨ε₀, hε₀, hpin⟩ := l32p_pinned hS hpl hrc (by linarith) hη hA hu huq hq1
  have hqu : 0 < q₀ - u := sub_pos.2 huq
  -- the smallness conditions on `ε`: `Z_ε ≥ 1/2` and `8 ε^{q₀ − u} ≤ 1/4`
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      1 / 2 ≤ locMass κ ε (locRad ε) ∧ 8 * ε ^ (q₀ - u) ≤ 1 / 4 := by
    have hT : Tendsto (fun ε : ℝ => 8 * ε ^ (q₀ - u)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have hc : ContinuousAt (fun x : ℝ => x ^ (q₀ - u)) 0 :=
        Real.continuousAt_rpow_const 0 _ (Or.inr hqu.le)
      have h8 : Tendsto (fun ε : ℝ => 8 * ε ^ (q₀ - u)) (𝓝[>] (0 : ℝ))
          (𝓝 (8 * (0 : ℝ) ^ (q₀ - u))) :=
        (hc.tendsto.mono_left nhdsWithin_le_nhds).const_mul 8
      simpa only [Real.zero_rpow hqu.ne', mul_zero] using h8
    filter_upwards [hS.seed.locHyp, hT.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))]
      with ε h1 h2
    exact ⟨h1.2.2.2.2, h2⟩
  obtain ⟨ε₁, hε₁, hsmall⟩ := (nhdsGT_basis (0 : ℝ)).eventually_iff.1 hev
  refine ⟨min (min ε₀ ε₁) 1, lt_min (lt_min hε₀ hε₁) one_pos, fun ε hε z r hr => ?_⟩
  have hε0 : 0 < ε := hε.1
  have hεε₀ : ε < ε₀ := hε.2.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hεε₁ : ε < ε₁ := hε.2.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hε1 : ε < 1 := hε.2.trans_le (min_le_right _ _)
  obtain ⟨hZ2, hb4⟩ := hsmall ⟨hε0, hεε₁⟩
  have hZ : locMass κ ε (locRad ε) ≠ 0 := by
    intro h0
    rw [h0] at hZ2
    norm_num at hZ2
  obtain ⟨hεu, hεr, hr1, hr0⟩ := l32p_window_facts hε0 hε1 hu (huq.trans hq1) hr
  have hbb : 8 * ε ^ q₀ ≤ r * (8 * ε ^ (q₀ - u)) := by
    have hsplit : ε ^ q₀ = ε ^ u * ε ^ (q₀ - u) := by
      rw [← Real.rpow_add hε0]
      congr 1
      ring
    have hpos : 0 ≤ ε ^ (q₀ - u) := (Real.rpow_pos_of_pos hε0 _).le
    rw [hsplit]
    nlinarith [mul_le_mul_of_nonneg_right hεu hpos]
  have h1 := l32p_ae_goodAnnulus_of_unit hS hsc hcs hai hε0 hε1 hr0 hZ z (A := A) hη.le hbb
  have h2 := l32p_prob_unit_eq hS hpl hε0 hε1 hεr hr1 z A η
    (by positivity : (0 : ℝ) < 8 * ε ^ (q₀ - u)) hb4
  calc ENNReal.ofReal p
      ≤ P {ω | l32pUnitGood (D (h ω)) (MepsR κ ξ ε r (h ω)) A η (8 * ε ^ (q₀ - u))} :=
        hpin ε ⟨hε0, hεε₀⟩ r hr
    _ = P {ω | l32pUnitGood (D (recentAff r z (h ω))) (MepsR κ ξ ε r (recentAff r z (h ω))) A η
          (8 * ε ^ (q₀ - u))} := h2.symm
    _ ≤ P {ω | GoodAnnulus (D (h ω)) (Meps κ ξ ε (h ω)) A η (cRatio κ ξ Q ε r) (8 * ε ^ q₀) z r} :=
        measure_mono_ae h1

end HigherDimLFPPAS.Annulus
