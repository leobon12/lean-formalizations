import HigherDimLQGMetric.LfppTight.PureFamily
import HigherDimLQGMetric.LfppTight.NormalizeMetric
import HigherDimLQGMetric.LfppTight.RandomPerturbCompare
import HigherDimLQGMetric.LfppTight.LawInput
import HigherDimLQGMetric.Limits.CompareFamily

/-! Transfer of tightness from a normalized LGF through an additive constant
and a bounded continuous perturbation. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Set

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

private theorem norm_lfpp_apply {d : ℕ} (κ : Rd d → ℝ) (ξ ε a : ℝ)
    (h : DistRd d) (hc : Continuous fun z => convMollify κ ε h z)
    (p : Rd d × Rd d) :
    toCMapRd (a⁻¹ • lfppDist κ ξ ε h) p =
      a⁻¹ * lfppDist κ ξ ε h p := by
  change DGZ.normMetricC ξ (convMollify κ ε h) a p = _
  rw [DGZ.normMetricC_apply hc]
  rfl

theorem l6a_ae_raw_mem_alg_bdd {d : ℕ} (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsLGFPlusBddCont h P)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂P, toCMapRd ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω)) ∈
      metricAlgSet_select := by
  have hae : 0 < aEps κ ξ ε := l6a_aEps_pos hd κ hκ ξ hε
  filter_upwards [l6a_ae_continuous_convMollify hd κ hκ P h hh hε]
    with ω hc
  change DGZ.normMetricC ξ (convMollify κ ε (h ω)) (aEps κ ξ ε) ∈
    metricAlgSet_select
  exact l6a_normMetric_mem_alg ξ (aEps κ ξ ε) hae _ hc

private theorem exp_abs_compare (X Y t : ℝ) (hX : 0 ≤ X)
    (hY : Y = Real.exp t * X) :
    Real.exp (-|t|) * X ≤ Y ∧ Y ≤ Real.exp |t| * X := by
  rw [hY]
  exact ⟨mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_abs_le t)) hX,
    mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (le_abs_self t)) hX⟩

private theorem symmetric_exp_compare (X Y M : ℝ)
    (hYX : Y ≤ Real.exp M * X) (hXY : X ≤ Real.exp M * Y) :
    Real.exp (-M) * X ≤ Y ∧ Y ≤ Real.exp M * X := by
  constructor
  · rw [Real.exp_neg]
    exact (inv_mul_le_iff₀ (Real.exp_pos M)).2 hXY
  · exact hYX

theorem l6a_tightFamily_addConst (hL1e : L1e_law)
    {d : ℕ} {κ : Rd d → ℝ} {ξ Q : ℝ}
    (hDGZ : DGZ.DGZHyp d κ ξ Q)
    (hAdapter : DGZ.RealEpsAdapterShape d κ ξ Q)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (g b : Ω → DistRd d) (hg : IsNormalizedLGF g P)
    (hb : IsWholeSpaceLGF b P) (c : Ω → ℝ) (hc : Measurable c)
    (hbc : ∀ ω, b ω = addConst (g ω) (c ω)) :
    TightFamily P (fun ε ω => toCMapRd
      ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (b ω))) (Ioo (0 : ℝ) 1) := by
  let A : ℝ → Ω → C(Rd d × Rd d, ℝ) := fun ε ω => toCMapRd
    ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (g ω))
  let B : ℝ → Ω → C(Rd d × Rd d, ℝ) := fun ε ω => toCMapRd
    ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (b ω))
  let M : Ω → ℝ := fun ω => |ξ * c ω|
  have hMm : Measurable M := by
    simpa only [M, Function.comp_def, Pi.mul_apply, Real.norm_eq_abs] using
      (measurable_norm.comp (measurable_const.mul hc))
  have hPure : TightFamily P A (Ioo (0 : ℝ) 1) :=
    l6a_pure_tightFamily hL1e hDGZ hAdapter P g hg
  have hBm : ∀ ε ∈ Ioo (0 : ℝ) 1, AEMeasurable (B ε) P := by
    intro ε hε
    exact l6a_aemeasurable_normalized_lfpp hDGZ.dim κ hDGZ.kernel ξ
      hε.1 P b hb.isLGFPlusBddCont
  have hAalg : ∀ ε ∈ Ioo (0 : ℝ) 1,
      ∀ᵐ ω ∂P, A ε ω ∈ metricAlgSet_select := by
    intro ε hε
    exact l6a_ae_raw_mem_alg hDGZ.dim κ hDGZ.kernel ξ P g hg hε.1
  have hBalg : ∀ ε ∈ Ioo (0 : ℝ) 1,
      ∀ᵐ ω ∂P, B ε ω ∈ metricAlgSet_select := by
    intro ε hε
    exact l6a_ae_raw_mem_alg_bdd hDGZ.dim κ hDGZ.kernel ξ P b
      hb.isLGFPlusBddCont hε.1
  have hcmp : ∀ ε ∈ Ioo (0 : ℝ) 1, ∀ᵐ ω ∂P,
      ∀ p : Rd d × Rd d,
      Real.exp (-M ω) * A ε ω p ≤ B ε ω p ∧
      B ε ω p ≤ Real.exp (M ω) * A ε ω p := by
    intro ε hε
    filter_upwards [l6a_ae_lfppDist_addConst_normalized hDGZ.dim κ
        hDGZ.kernel ξ P g hg b c hbc,
      l6a_ae_continuous_convMollify hDGZ.dim κ hDGZ.kernel P g
        hg.1.isLGFPlusBddCont hε.1,
      l6a_ae_continuous_convMollify hDGZ.dim κ hDGZ.kernel P b
        hb.isLGFPlusBddCont hε.1] with ω heq hcg hcb p
    have hA : A ε ω p = (aEps κ ξ ε)⁻¹ * lfppDist κ ξ ε (g ω) p :=
      norm_lfpp_apply κ ξ ε (aEps κ ξ ε) (g ω) hcg p
    have hB : B ε ω p = (aEps κ ξ ε)⁻¹ * lfppDist κ ξ ε (b ω) p :=
      norm_lfpp_apply κ ξ ε (aEps κ ξ ε) (b ω) hcb p
    have hEq : B ε ω p = Real.exp (ξ * c ω) * A ε ω p := by
      rw [hA, hB, heq ε hε.1 p]
      ring
    have hX : 0 ≤ A ε ω p := by
      rw [hA]
      exact mul_nonneg (inv_pos.mpr (l6a_aEps_pos hDGZ.dim κ hDGZ.kernel ξ hε.1)).le
        (DGZ.lfppMetric_nonneg ξ _ p.1 p.2)
    exact exp_abs_compare _ _ _ hX hEq
  exact l6c_tightFamily_of_randomCompare P A B (Ioo (0 : ℝ) 1)
    hPure hBm hAalg hBalg M hMm hcmp

theorem l6a_tightFamily_addBddCont
    {d : ℕ} {κ : Rd d → ℝ} {ξ Q : ℝ}
    (hDGZ : DGZ.DGZHyp d κ ξ Q)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (b h : Ω → DistRd d) (hb : IsWholeSpaceLGF b P)
    (hh : IsLGFPlusBddCont h P)
    (f : Ω → C(Rd d, ℝ)) (hf : Measurable f)
    (hfb : ∀ ω, ∃ M : ℝ, ∀ z, |f ω z| ≤ M)
    (hhb : ∀ ω, h ω = addFun (b ω) (f ω))
    (hT : TightFamily P (fun ε ω => toCMapRd
      ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (b ω))) (Ioo (0 : ℝ) 1)) :
    TightFamily P (fun ε ω => toCMapRd
      ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω))) (Ioo (0 : ℝ) 1) := by
  let A : ℝ → Ω → C(Rd d × Rd d, ℝ) := fun ε ω => toCMapRd
    ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (b ω))
  let B : ℝ → Ω → C(Rd d × Rd d, ℝ) := fun ε ω => toCMapRd
    ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω))
  let L : ℝ := ∫ z : Rd d, |convKernel κ z|
  let M : Ω → ℝ := fun ω => |ξ| * (s8a_supAbs (f ω) * L)
  have hMm : Measurable M := by
    exact measurable_const.mul ((s8a_measurable_supAbs hf).mul measurable_const)
  have hBm : ∀ ε ∈ Ioo (0 : ℝ) 1, AEMeasurable (B ε) P := by
    intro ε hε
    exact l6a_aemeasurable_normalized_lfpp hDGZ.dim κ hDGZ.kernel ξ
      hε.1 P h hh
  have hAalg : ∀ ε ∈ Ioo (0 : ℝ) 1,
      ∀ᵐ ω ∂P, A ε ω ∈ metricAlgSet_select := by
    intro ε hε
    exact l6a_ae_raw_mem_alg_bdd hDGZ.dim κ hDGZ.kernel ξ P b
      hb.isLGFPlusBddCont hε.1
  have hBalg : ∀ ε ∈ Ioo (0 : ℝ) 1,
      ∀ᵐ ω ∂P, B ε ω ∈ metricAlgSet_select := by
    intro ε hε
    exact l6a_ae_raw_mem_alg_bdd hDGZ.dim κ hDGZ.kernel ξ P h hh hε.1
  have hcmp : ∀ ε ∈ Ioo (0 : ℝ) 1, ∀ᵐ ω ∂P,
      ∀ p : Rd d × Rd d,
      Real.exp (-M ω) * A ε ω p ≤ B ε ω p ∧
      B ε ω p ≤ Real.exp (M ω) * A ε ω p := by
    intro ε hε
    have hae : 0 < aEps κ ξ ε :=
      l6a_aEps_pos hDGZ.dim κ hDGZ.kernel ξ hε.1
    filter_upwards [l6a_ae_lfppDist_addFun_compare_random hDGZ.dim κ
        hDGZ.kernel ξ P b hb f hfb hε.1,
      l6a_ae_continuous_convMollify hDGZ.dim κ hDGZ.kernel P b
        hb.isLGFPlusBddCont hε.1,
      l6a_ae_continuous_convMollify hDGZ.dim κ hDGZ.kernel P h
        hh hε.1] with ω hraw hcb hch p
    have hA : A ε ω p = (aEps κ ξ ε)⁻¹ * lfppDist κ ξ ε (b ω) p :=
      norm_lfpp_apply κ ξ ε (aEps κ ξ ε) (b ω) hcb p
    have hB : B ε ω p = (aEps κ ξ ε)⁻¹ * lfppDist κ ξ ε (h ω) p :=
      norm_lfpp_apply κ ξ ε (aEps κ ξ ε) (h ω) hch p
    have hraw1 := (hraw p).1
    have hraw2 := (hraw p).2
    rw [← hhb ω] at hraw1 hraw2
    have hYX : B ε ω p ≤ Real.exp (M ω) * A ε ω p := by
      calc
        B ε ω p = (aEps κ ξ ε)⁻¹ * lfppDist κ ξ ε (h ω) p := hB
        _ ≤ (aEps κ ξ ε)⁻¹ *
            (Real.exp (M ω) * lfppDist κ ξ ε (b ω) p) :=
          mul_le_mul_of_nonneg_left hraw1 (inv_pos.mpr hae).le
        _ = Real.exp (M ω) * A ε ω p := by rw [hA]; ring
    have hXY : A ε ω p ≤ Real.exp (M ω) * B ε ω p := by
      calc
        A ε ω p = (aEps κ ξ ε)⁻¹ * lfppDist κ ξ ε (b ω) p := hA
        _ ≤ (aEps κ ξ ε)⁻¹ *
            (Real.exp (M ω) * lfppDist κ ξ ε (h ω) p) :=
          mul_le_mul_of_nonneg_left hraw2 (inv_pos.mpr hae).le
        _ = Real.exp (M ω) * B ε ω p := by rw [hB]; ring
    exact symmetric_exp_compare _ _ _ hYX hXY
  exact l6c_tightFamily_of_randomCompare P A B (Ioo (0 : ℝ) 1)
    hT hBm hAalg hBalg M hMm hcmp

end HigherDimLQGMetric
