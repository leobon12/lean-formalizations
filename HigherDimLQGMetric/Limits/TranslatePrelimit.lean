import HigherDimLQGMetric.Limits.ScaleIdentity
import HigherDimLQGMetric.Weak.DetLFPPMetric
import HigherDimLQGMetric.Main.LFPPMedian
import HigherDimLQGMetric.ConvField.Shifts
import HigherDimLQGMetric.LfppTight.LawInput

/-! Exact translation covariance of normalized convolution LFPP. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- Recentering a normalized LGF at any deterministic point preserves its law. -/
theorem l6c_map_normalizedTranslate_eq {d : ℕ} (hd : 2 ≤ d)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P) (z : Rd d) :
    P.map (fun ω => addConst (affineComp 1 z (h ω))
      (-sphereAvg (affineComp 1 z (h ω)) 1 0)) = P.map h := by
  calc
    P.map (fun ω => addConst (affineComp 1 z (h ω))
        (-sphereAvg (affineComp 1 z (h ω)) 1 0)) =
      P.map (fun ω => addConst (affineComp 1 z (h ω))
        (-sphereAvg (h ω) 1 z)) := by
      apply Measure.map_congr
      filter_upwards [hh.1.ae_sphereAvg_affineComp hd one_pos z one_pos 0]
        with ω hs
      rw [hs]
      simp
    _ = P.map h := hh.map_affineComp_sub_sphereAvg hd one_pos z

/-- At a fixed cutoff the recentered field produces the original LFPP law. -/
theorem l6c_map_lfppMetric_normalizedTranslate {d : ℕ} (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P)
    (δ : ℝ) (hδ : 0 < δ) (z : Rd d) :
    P.map (fun ω => lfppSeq κ ξ (fun _ => δ)
      (addConst (affineComp 1 z (h ω))
        (-sphereAvg (affineComp 1 z (h ω)) 1 0)) 0) =
    P.map (fun ω => lfppSeq κ ξ (fun _ => δ) (h ω) 0) := by
  let g : Ω → DistRd d := fun ω =>
    addConst (affineComp 1 z (h ω))
      (-sphereAvg (affineComp 1 z (h ω)) 1 0)
  let F : DistRd d → C(Rd d × Rd d, ℝ) := fun x =>
    toCMapRd ((aEps κ ξ δ)⁻¹ • lfppDist κ ξ δ x)
  have hmap : P.map g = P.map h := l6c_map_normalizedTranslate_eq hd P h hh z
  have hgm : Measurable g :=
    measurable_addConst.comp
      (((measurable_affineComp 1 z).comp hh.1.measurable).prodMk
        ((measurable_sphereAvg_left 1 0).comp
          ((measurable_affineComp 1 z).comp hh.1.measurable)).neg)
  have hnorm : IsNormalizedLGF id (P.map h) := hh.map_id
  have hFm : AEMeasurable F (P.map h) :=
    l6a_aemeasurable_normalized_lfpp hd κ hκ ξ hδ (P.map h) id
      hnorm.1.isLGFPlusBddCont
  have hFg : AEMeasurable F (P.map g) := by rw [hmap]; exact hFm
  change P.map (F ∘ g) = P.map (F ∘ h)
  calc
    P.map (F ∘ g) = (P.map g).map F :=
      (AEMeasurable.map_map_of_aemeasurable hFg hgm.aemeasurable).symm
    _ = (P.map h).map F := by rw [hmap]
    _ = P.map (F ∘ h) :=
      AEMeasurable.map_map_of_aemeasurable hFm hh.1.measurable.aemeasurable

/-- At every cutoff, translating and recentering the field exactly translates
the LFPP metric with the Weyl factor from the sphere average. -/
theorem l6c_ae_lfppDist_translate {d : ℕ} (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P) (z : Rd d) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε → ∀ u v : Rd d,
      lfppDist κ ξ ε (h ω) (z + u, z + v) =
        Real.exp (ξ * sphereAvg (h ω) 1 z) *
          lfppDist κ ξ ε
            (addConst (affineComp 1 z (h ω))
              (-sphereAvg (affineComp 1 z (h ω)) 1 0)) (u, v) := by
  let k : Ω → DistRd d := fun ω => affineComp 1 z (h ω)
  have hk : IsWholeSpaceLGF k P := hh.1.affineComp one_pos z
  have hconv : ∀ᵐ ω ∂P, k ω ∈ convSet d :=
    hk.ae_exists_tendsto_sphereAvgSeq hd one_pos 0
  let g : Ω → DistRd d := fun ω => addConst (k ω) (-sphereAvg (k ω) 1 0)
  have hg : IsNormalizedLGF g P := hk.isNormalizedLGF_normalize (by omega) hconv
  filter_upwards [l2b_ae_convMollify_tendsto d hd κ hκ P g hg,
    hh.1.ae_sphereAvg_affineComp hd one_pos z one_pos 0]
    with ω hlim hsph
  intro ε hε u v
  have heq (w : Rd d) :
      convMollify κ ε (h ω) (z + w) =
        convMollify κ ε (g ω) w + sphereAvg (h ω) 1 z := by
    have hsh := l2b_convMollify_addConst_of_tendsto hd hκ hε
      (c := sphereAvg (k ω) 1 0) (hlim ε hε w)
    have hk_eq : addConst (g ω) (sphereAvg (k ω) 1 0) = k ω := by
      dsimp [g]
      rw [addConst_addConst, neg_add_cancel, addConst_zero]
    rw [hk_eq] at hsh
    calc
      _ = convMollify κ ε (k ω) w :=
        (by simpa only [add_comm w z] using
          (l2b_convMollify_translate d hd κ hκ ε (h ω) z w).symm)
      _ = convMollify κ ε (g ω) w + sphereAvg (k ω) 1 0 := hsh
      _ = _ := by
        congr 1
        simpa only [k, one_mul, one_smul, zero_add] using hsph
  have ht := l6a_lfppDist_scale_of_conv_eq κ ξ ε 1
    (sphereAvg (h ω) 1 z) one_pos (h ω) (g ω) z u v
    (by simpa only [div_one, one_smul] using heq)
  simpa only [div_one, one_smul, one_mul] using ht

/-- Translation covariance as an identity of the normalized LFPP continuous maps.
The event is independent of the sequence index and of the endpoints. -/
theorem l6c_ae_lfppSeq_translate {d : ℕ} (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ)
    (εs : ℕ → ℝ) (hεs : ∀ n, 0 < εs n)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P) (z : Rd d) :
    ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ u v : Rd d,
      lfppSeq κ ξ εs (h ω) n (z + u, z + v) =
        Real.exp (ξ * sphereAvg (h ω) 1 z) *
          lfppSeq κ ξ εs
            (addConst (affineComp 1 z (h ω))
              (-sphereAvg (affineComp 1 z (h ω)) 1 0)) n (u, v) := by
  let k : Ω → DistRd d := fun ω => affineComp 1 z (h ω)
  have hk : IsWholeSpaceLGF k P := hh.1.affineComp one_pos z
  have hconv : ∀ᵐ ω ∂P, k ω ∈ convSet d :=
    hk.ae_exists_tendsto_sphereAvgSeq hd one_pos 0
  let g : Ω → DistRd d := fun ω => addConst (k ω) (-sphereAvg (k ω) 1 0)
  have hg : IsNormalizedLGF g P := hk.isNormalizedLGF_normalize (by omega) hconv
  have hch : ∀ᵐ ω ∂P, ∀ n : ℕ,
      Continuous (convMollify κ (εs n) (h ω)) := by
    exact ae_all_iff.mpr fun n =>
      l10a_ae_continuous_convMollify hd κ hκ P h hh (hεs n)
  have hcg : ∀ᵐ ω ∂P, ∀ n : ℕ,
      Continuous (convMollify κ (εs n) (g ω)) := by
    exact ae_all_iff.mpr fun n =>
      l10a_ae_continuous_convMollify hd κ hκ P g hg (hεs n)
  filter_upwards [l6c_ae_lfppDist_translate hd κ hκ ξ P h hh z, hch, hcg]
    with ω ht hc hdg
  intro n u v
  have hcontH : Continuous (fun p : Rd d × Rd d =>
      (aEps κ ξ (εs n))⁻¹ * lfppDist κ ξ (εs n) (h ω) p) := by
    have heq : lfppDist κ ξ (εs n) (h ω) =
        fieldLfpp ξ (convMollify κ (εs n) (h ω)) := by
      funext p
      exact (fieldLfpp_eq_lfppDistOn (hc n) p).symm
    rw [heq]
    exact (continuous_fieldLfpp (hc n)).const_mul _
  have hcontG : Continuous (fun p : Rd d × Rd d =>
      (aEps κ ξ (εs n))⁻¹ * lfppDist κ ξ (εs n) (g ω) p) := by
    have heq : lfppDist κ ξ (εs n) (g ω) =
        fieldLfpp ξ (convMollify κ (εs n) (g ω)) := by
      funext p
      exact (fieldLfpp_eq_lfppDistOn (hdg n) p).symm
    rw [heq]
    exact (continuous_fieldLfpp (hdg n)).const_mul _
  change toCMapRd ((aEps κ ξ (εs n))⁻¹ • lfppDist κ ξ (εs n) (h ω))
      (z + u, z + v) =
    Real.exp (ξ * sphereAvg (h ω) 1 z) *
      toCMapRd ((aEps κ ξ (εs n))⁻¹ • lfppDist κ ξ (εs n) (g ω)) (u, v)
  have hcontH' : Continuous ((aEps κ ξ (εs n))⁻¹ •
      lfppDist κ ξ (εs n) (h ω)) := by
    convert hcontH using 1
    funext p
    simp only [Pi.smul_apply, smul_eq_mul]
  have hcontG' : Continuous ((aEps κ ξ (εs n))⁻¹ •
      lfppDist κ ξ (εs n) (g ω)) := by
    convert hcontG using 1
    funext p
    simp only [Pi.smul_apply, smul_eq_mul]
  rw [toCMapRd_apply_of_continuous hcontH',
    toCMapRd_apply_of_continuous hcontG']
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [ht (εs n) (hεs n) u v]
  ring

end HigherDimLQGMetric
