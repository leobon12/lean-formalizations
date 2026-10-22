import HigherDimLQGMetric.Config.Measurable
import HigherDimLQGMetric.Weak.DetLFPPMetric
import HigherDimLQGMetric.Main.LFPPMedian
import HigherDimLQGMetric.LfppTight.LawInput

/-! Measurability of internal LFPP metric coordinates. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- The length metric determined by a continuous field is a Borel map. -/
theorem l6c_measurable_fieldLfppMetric {d : ℕ} (ξ : ℝ) :
    Measurable (fieldLfppMetric (d := d) ξ) := by
  have hval : Measurable (fun φ : C(Rd d, ℝ) =>
      (fieldLfppMetric ξ φ).1) := by
    refine ContinuousMap.measurable_iff_eval.mpr fun p => ?_
    convert HigherDimLFPP.measurable_lfppDistOn_continuousMap
      (V := univ) isOpen_univ ξ p.1 p.2 using 1
    funext φ
    exact fieldLfpp_eq_lfppDistOn φ.continuous p
  have hEmb : MeasurableEmbedding
      ((↑) : ContMetric d → C(Rd d × Rd d, ℝ)) :=
    MeasurableEmbedding.subtype_coe (measurableSet_isContinuousMetric_select d)
  exact (hEmb.measurable_comp_iff).mp hval

/-- Internal distance on an open connected domain is Borel as a function of
the underlying continuous LFPP field. -/
theorem l6c_measurable_fieldLfpp_internalC {d : ℕ} (ξ : ℝ)
    {U : Set (Rd d)} (hU : IsOpen U) (hUc : IsPreconnected U) :
    Measurable (fun φ : C(Rd d, ℝ) =>
      internalC (fieldLfppMetric ξ φ)
        (fieldLfppMetric_isLength ξ φ) hU hUc) := by
  let _ := hU.locallyCompactSpace
  exact measurable_internalC_of_measurable
    (fieldLfppMetric ξ) (l6c_measurable_fieldLfppMetric ξ)
    (fun φ => fieldLfppMetric_isLength ξ φ) hU hUc

/-- Internal distance commutes with a positive global normalization. -/
theorem l6c_internalC_smul {d : ℕ} (D : ContMetric d) (hD : D.IsLength)
    {s : ℝ} (hs : 0 < s) {U : Set (Rd d)}
    (hU : IsOpen U) (hUc : IsPreconnected U) :
    internalC (D.smul s hs) (ContMetric.isLength_smul hs hD) hU hUc =
      s • internalC D hD hU hUc := by
  apply ContinuousMap.ext
  rintro ⟨u, v⟩
  change ((D.smul s hs).internal U u.1 v.1).toReal =
    s * (D.internal U u.1 v.1).toReal
  rw [ContMetric.internal_smul hs, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hs.le]

/-- For a measurable random continuous field, every normalized internal LFPP
coordinate is a measurable continuous map on the domain. -/
theorem l6c_measurable_scaledFieldLfpp_internalC {d : ℕ} (ξ : ℝ)
    {U : Set (Rd d)} (hU : IsOpen U) (hUc : IsPreconnected U)
    {Ω : Type*} [MeasurableSpace Ω] (φ : Ω → C(Rd d, ℝ))
    (hφ : Measurable φ) {s : ℝ} (hs : 0 < s) :
    Measurable (fun ω => internalC ((fieldLfppMetric ξ (φ ω)).smul s hs)
      (ContMetric.isLength_smul hs (fieldLfppMetric_isLength ξ (φ ω))) hU hUc) := by
  have hbase := (l6c_measurable_fieldLfpp_internalC ξ hU hUc).comp hφ
  have hscaled : Measurable (fun ω =>
      s • internalC (fieldLfppMetric ξ (φ ω))
        (fieldLfppMetric_isLength ξ (φ ω)) hU hUc) :=
    (show Continuous (fun E : C(U × U, ℝ) => s • E) from by fun_prop).measurable.comp hbase
  convert hscaled using 1
  funext ω
  exact l6c_internalC_smul (fieldLfppMetric ξ (φ ω))
    (fieldLfppMetric_isLength ξ (φ ω)) hs hU hUc

/-- The same coordinate is a.e.-measurable when the field is only given by an
a.e.-measurable continuous-map version. -/
theorem l6c_aemeasurable_scaledFieldLfpp_internalC {d : ℕ} (ξ : ℝ)
    {U : Set (Rd d)} (hU : IsOpen U) (hUc : IsPreconnected U)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (φ : Ω → C(Rd d, ℝ)) (hφ : AEMeasurable φ P)
    {s : ℝ} (hs : 0 < s) :
    AEMeasurable (fun ω => internalC ((fieldLfppMetric ξ (φ ω)).smul s hs)
      (ContMetric.isLength_smul hs (fieldLfppMetric_isLength ξ (φ ω))) hU hUc) P := by
  have hF := l6c_measurable_scaledFieldLfpp_internalC ξ hU hUc
    (id : C(Rd d, ℝ) → C(Rd d, ℝ)) measurable_id hs
  exact hF.comp_aemeasurable hφ

/-- Every positive-cutoff LFPP metric has an a.e.-measurable internal metric
coordinate on an open connected domain. The witness metric is its actual
median-normalized LFPP metric almost surely. -/
theorem l6c_exists_internalLfpp_sample {d : ℕ} (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ)
    {ε : ℝ} (hε : 0 < ε)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P)
    {U : Set (Rd d)} (hU : IsOpen U) (hUc : IsPreconnected U) :
    ∃ J : Ω → C(U × U, ℝ), AEMeasurable J P ∧
      ∀ᵐ ω ∂P, ∃ D : ContMetric d, ∃ hD : D.IsLength,
        (D.1 : C(Rd d × Rd d, ℝ)) =
          toCMapRd ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω)) ∧
        J ω = internalC D hD hU hUc := by
  classical
  let H : Rd d → Ω → ℝ := fun z ω => convMollify κ ε (h ω) z
  have hc : ∀ᵐ ω ∂P, Continuous fun z => H z ω :=
    l10a_ae_continuous_convMollify hd κ hκ P h hh hε
  let Y : Rd d → Ω → ℝ := fun z ω =>
    if hcont : Continuous (fun w => H w ω) then H z ω else 0
  have hYc (ω : Ω) : Continuous fun z => Y z ω := by
    by_cases hcont : Continuous (fun z => H z ω)
    · have heq : (fun z => Y z ω) = fun z => H z ω := by
        funext z
        simp [Y, hcont]
      rwa [heq]
    · have heq : (fun z => Y z ω) = fun _ => 0 := by
        funext z
        simp [Y, hcont]
      rw [heq]
      exact continuous_const
  have hYm (z : Rd d) : AEMeasurable (Y z) P := by
    have hH : Measurable (H z) :=
      (l10a_measurable_convMollify_apply κ ε z).comp hh.1.measurable
    have heq : Y z =ᵐ[P] H z := by
      filter_upwards [hc] with ω hω
      simp [Y, hω]
    exact (aemeasurable_congr heq.symm).1 hH.aemeasurable
  let φ : Ω → C(Rd d, ℝ) := fun ω => ⟨fun z => Y z ω, hYc ω⟩
  have hφ : AEMeasurable φ P := l10a_aemeasurable_toContMap Y hYm hYc
  have ha : 0 < aEps κ ξ ε := l6a_aEps_pos hd κ hκ ξ hε
  let s : ℝ := (aEps κ ξ ε)⁻¹
  have hs : 0 < s := inv_pos.mpr ha
  let D : Ω → ContMetric d := fun ω =>
    (fieldLfppMetric ξ (φ ω)).smul s hs
  have hD (ω : Ω) : (D ω).IsLength :=
    ContMetric.isLength_smul hs (fieldLfppMetric_isLength ξ (φ ω))
  let J : Ω → C(U × U, ℝ) := fun ω => internalC (D ω) (hD ω) hU hUc
  refine ⟨J, ?_, ?_⟩
  · exact l6c_aemeasurable_scaledFieldLfpp_internalC ξ hU hUc P φ hφ hs
  · filter_upwards [hc] with ω hω
    refine ⟨D ω, hD ω, ?_, rfl⟩
    have hYeq : (fun z => Y z ω) = fun z => H z ω := by
      funext z
      simp [Y, hω]
    have hlf : lfppDist κ ξ ε (h ω) = fieldLfpp ξ (fun z => H z ω) := by
      funext p
      exact (fieldLfpp_eq_lfppDistOn hω p).symm
    have hscaled : Continuous (s • lfppDist κ ξ ε (h ω)) := by
      rw [hlf]
      exact (continuous_fieldLfpp hω).const_smul s
    apply ContinuousMap.ext
    intro p
    change s * fieldLfpp ξ (φ ω) p =
      toCMapRd (s • lfppDist κ ξ ε (h ω)) p
    rw [toCMapRd_apply_of_continuous hscaled]
    change s * fieldLfpp ξ (fun z => Y z ω) p =
      s * lfppDist κ ξ ε (h ω) p
    rw [hYeq, hlf]

end HigherDimLQGMetric
