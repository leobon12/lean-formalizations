import HigherDimLQGContinuity.Fatou.Basic

/-!
# Fatou passage for fixed annulus crossings

The cutoff inverse moment bound passes to a canonical metric by compactness of the two
boundary spheres and Fatou's lemma.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

/-- The convolution inverse-crossing input passes to every continuous-metric assignment
obtained as a local-uniform probability limit of the median-normalized LFPP metrics. -/
theorem fatou_invCross_of_conv {d : ℕ} (hd : 3 ≤ d) {κ : Rd d → ℝ}
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (hC2 : ConvInvCrossShape d κ)
    {b μ : ℝ} (hb : 0 < b) (hμ : 0 < μ) (z : Rd d)
    {a c q : ℝ} (ha : 0 < a) (hac : a < c) (hq : 0 < q) :
    ∃ C : ℝ, ∀ ξ : ℝ, UHyp d κ b μ ξ → ∀ D : DistRd d → ContMetric d,
      TendstoInProbLU (normLGFLaw d)
        (fun ε g => (aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε g) (𝓝[>] 0)
        (fun g => (D g).1) →
      ∫⁻ g, (acrossDist (D g) z a c)⁻¹ ^ q ∂(normLGFLaw d) ≤ ENNReal.ofReal C := by
  let _ : IsProbabilityMeasure (normLGFLaw d) :=
    (normLGFLaw_spec_holds d (by omega : 2 ≤ d)).1
  have hn : IsNormalizedLGF id (normLGFLaw d) :=
    (normLGFLaw_spec_holds d (by omega : 2 ≤ d)).2.1
  obtain ⟨C, hC⟩ := hC2 b μ hb hμ z a c ha hac q hq
  refine ⟨C, fun ξ hξ D hconv => ?_⟩
  obtain ⟨ns, _, hae⟩ := fatou_exists_subseq hd hκ D hconv
  let X : ℕ → DistRd d → C(Rd d × Rd d, ℝ) := fun k g =>
    toCMapRd ((aEps κ ξ (fatouEps (ns k)))⁻¹ •
      lfppDist κ ξ (fatouEps (ns k)) g)
  let F : C(Rd d × Rd d, ℝ) → ℝ≥0∞ := fun E =>
    (infPairs E (sphere z a) (sphere z c))⁻¹ ^ q
  have hF : Continuous F := by
    exact (ENNReal.continuous_rpow_const.comp
      (continuous_inv.comp (fatou_continuous_across z a c)))
  have hpt : ∀ᵐ g ∂(normLGFLaw d),
      Tendsto (fun k => F (X k g)) atTop (𝓝 (F (D g).1)) := by
    filter_upwards [hae] with g hg
    exact (hF.tendsto (D g).1).comp hg
  have hmeas (k : ℕ) : AEMeasurable (fun g => F (X k g)) (normLGFLaw d) := by
    have hm : AEMeasurable (X k) (normLGFLaw d) :=
      l6a_aemeasurable_normalized_lfpp (by omega : 2 ≤ d) κ hκ ξ
        (fatouEps_pos (ns k)) (normLGFLaw d) id hn.1.isLGFPlusBddCont
    exact hF.measurable.comp_aemeasurable hm
  have hbound (k : ℕ) :
      ∫⁻ g, F (X k g) ∂(normLGFLaw d) ≤ ENNReal.ofReal C := by
    have heq := fatou_prelimit_infPairs_ae (by omega : 2 ≤ d) hκ ξ
      (fatouEps_pos (ns k)) (sphere z a) (sphere z c)
    have heqint : (∫⁻ g, F (X k g) ∂(normLGFLaw d)) =
        ∫⁻ g, (ENNReal.ofReal (aEps κ ξ (fatouEps (ns k)))⁻¹ *
          infPairs (lfppDist κ ξ (fatouEps (ns k)) g) (sphere z a) (sphere z c))⁻¹ ^ q
          ∂(normLGFLaw d) := by
      apply lintegral_congr_ae
      filter_upwards [heq] with g hg
      change (infPairs (toCMapRd ((aEps κ ξ (fatouEps (ns k)))⁻¹ •
        lfppDist κ ξ (fatouEps (ns k)) g)) (sphere z a) (sphere z c))⁻¹ ^ q = _
      rw [hg, ENNReal.ofReal_inv_of_pos
        (l6a_aEps_pos (by omega : 2 ≤ d) κ hκ ξ (fatouEps_pos (ns k)))]
    rw [heqint]
    exact hC ξ hξ (fatouEps (ns k)) ⟨fatouEps_pos _, fatouEps_lt_one _⟩
      (normLGFLaw d) id hn
  have hlim : ∫⁻ g, F (D g).1 ∂(normLGFLaw d) ≤
      liminf (fun k => ∫⁻ g, F (X k g) ∂(normLGFLaw d)) atTop := by
    calc
      _ = ∫⁻ g, liminf (fun k => F (X k g)) atTop ∂(normLGFLaw d) := by
        apply lintegral_congr_ae
        filter_upwards [hpt] with g hg
        exact (hg.liminf_eq).symm
      _ ≤ _ := lintegral_liminf_le' hmeas
  have hfinal : ∫⁻ g, F (D g).1 ∂(normLGFLaw d) ≤ ENNReal.ofReal C :=
    hlim.trans (liminf_le_of_frequently_le' (Frequently.of_forall hbound))
  simpa only [F, acrossDist, infPairs] using hfinal

end HigherDimLQGContinuity
