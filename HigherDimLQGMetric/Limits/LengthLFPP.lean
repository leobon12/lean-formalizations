import HigherDimLQGMetric.Limits.LengthLaw
import HigherDimLQGMetric.Weak.DetLFPPMetric
import HigherDimLQGMetric.Sharp.ScaledMetric
import HigherDimLQGMetric.Main.LFPPMedian
import HigherDimLQGMetric.Field.LGFPlusCont

/-!
# The LFPP laws are carried by length metrics

This supplies the prelimit length condition for the portmanteau argument of
`Limits.LengthLaw`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- Each normalized LFPP metric of a continuous convolution field is a length metric. -/
theorem l6c_scaled_lfpp_isContLengthFn {d : ℕ} (κ : Rd d → ℝ) (ξ ε a : ℝ)
    (g : DistRd d) (hc : Continuous (convMollify κ ε g)) (ha : 0 < a) :
    IsContLengthFn (toCMapRd (a⁻¹ • lfppDist κ ξ ε g)) := by
  let φ : C(Rd d, ℝ) := ⟨convMollify κ ε g, hc⟩
  have hfun : lfppDist κ ξ ε g = fieldLfpp ξ (convMollify κ ε g) := by
    funext p
    exact (fieldLfpp_eq_lfppDistOn hc p).symm
  have hcont : Continuous (a⁻¹ • lfppDist κ ξ ε g) := by
    rw [hfun]
    exact (continuous_fieldLfpp hc).const_smul _
  have heq : toCMapRd (a⁻¹ • lfppDist κ ξ ε g) =
      ((fieldLfppMetric ξ φ).smul a⁻¹ (inv_pos.mpr ha)).1 := by
    ext p
    rw [toCMapRd_apply_of_continuous hcont, ContMetric.smul_apply]
    simp only [Pi.smul_apply, smul_eq_mul, fieldLfppMetric_apply, hfun]
    rfl
  rw [heq]
  exact ⟨((fieldLfppMetric ξ φ).smul a⁻¹ (inv_pos.mpr ha)).2,
    ContMetric.isLength_smul (inv_pos.mpr ha) (fieldLfppMetric_isLength ξ φ)⟩

/-- At each positive cutoff, the normalized LFPP law is carried by length metrics. -/
theorem l6c_ae_lfpp_length {d : ℕ} (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (ξ ε : ℝ) (hε : 0 < ε) (ha : 0 < aEps κ ξ ε)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P) :
    ∀ᵐ ω ∂P, IsContLengthFn
      (toCMapRd ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω))) := by
  filter_upwards [l10a_ae_continuous_convMollify hd κ hκ P h hh hε] with ω hω
  exact l6c_scaled_lfpp_isContLengthFn κ ξ ε (aEps κ ξ ε) (h ω) hω ha

/-- [1] Lemma 3.1(1): every limit law of the normalized LFPP metrics is
carried by proper continuous length metrics. -/
theorem l6c_lemma31_lengthLimit
    (hL6a : ∀ d ξ κ, L6a_tight d ξ κ)
    {d : ℕ} (ξ : ℝ) (κ : Rd d → ℝ)
    (hB2 : ∃ Q : ℝ, DGZ.DGZHyp d κ ξ Q ∧ DGZ.RealEpsAdapterShape d κ ξ Q)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P)
    (μ : ProbabilityMeasure C(Rd d × Rd d, ℝ))
    (hμ : μ ∈ closure {ν : ProbabilityMeasure C(Rd d × Rd d, ℝ) |
      ∃ ε ∈ Ioo (0 : ℝ) 1,
        (ν : Measure C(Rd d × Rd d, ℝ)) =
          P.map (fun ω => toCMapRd ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω)))}) :
    ∀ᵐ D ∂(μ : Measure C(Rd d × Rd d, ℝ)), IsContLengthFn D := by
  have hA := (hL6a d ξ κ) hB2 P h hh.1.isLGFPlusBddCont
  obtain ⟨Q, hQ, _⟩ := hB2
  exact l6c_lemma31_lengthLaw P
    (fun ε ω => toCMapRd ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω))) (Ioo 0 1)
    hA.2 (fun ε hε => l6c_ae_lfpp_length hQ.dim κ hQ.kernel ξ ε hε.1
      (hA.1 ε hε) P h hh) μ hμ

end HigherDimLQGMetric
