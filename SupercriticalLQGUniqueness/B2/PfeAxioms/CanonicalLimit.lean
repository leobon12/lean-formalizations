import SupercriticalLQGUniqueness.B2.PfeAxioms.NormalizedLaw
import SupercriticalLQGUniqueness.B2.PfeAxioms.HeatVersionMeasurable
import SupercriticalLQGUniqueness.B2.PfeAxioms.ContinuousLFPPMeasurable
import SupercriticalLQGUniqueness.B2.LscTop.Limits

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology LQGMetric
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

private theorem exists_canonical_heat_version (δ : Set.Ioi (0 : ℝ)) :
    ∃ H : DistC → C(ℂ, ℝ), Measurable H ∧
      ∀ᵐ g ∂normGFFLaw, (H g : ℂ → ℝ) = heatMollify (δ : ℝ) g := by
  have hm : Measurable (fun g : DistC => heatMollify (δ : ℝ) g) :=
    measurable_pi_iff.mpr fun z => measurable_heatMollify_left (δ : ℝ) z
  exact exists_measurable_continuous_real_version normGFFLaw _ hm
    (LQGMetric.LFPP.ae_continuous_heatMollify_normGFFLaw δ.property.ne')

private def canonicalHeatVersion (δ : Set.Ioi (0 : ℝ)) : DistC → C(ℂ, ℝ) :=
  (exists_canonical_heat_version δ).choose

private theorem canonicalHeatVersion_measurable (δ : Set.Ioi (0 : ℝ)) :
    Measurable (canonicalHeatVersion δ) :=
  (exists_canonical_heat_version δ).choose_spec.1

private theorem canonicalHeatVersion_ae (δ : Set.Ioi (0 : ℝ)) :
    ∀ᵐ g ∂normGFFLaw,
      (canonicalHeatVersion δ g : ℂ → ℝ) = heatMollify (δ : ℝ) g :=
  (exists_canonical_heat_version δ).choose_spec.2

 

def canonicalLSCLimit [MeasurableSpace LSCFun] [BorelSpace LSCFun]
    (ξ : Set.Ioi (0 : ℝ))
    (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (ε : ℕ → Set.Ioi (0 : ℝ)) : DistC → LSCFun :=
  fun g => limUnder atTop fun n =>
    B2.LscTop.ofContinuousMap
      (B2.LscTop.rescaledLFPPMap (ξ : ℝ) (m (ε n)) (canonicalHeatVersion (ε n) g))

theorem measurable_canonicalLSCLimit [MeasurableSpace LSCFun] [BorelSpace LSCFun]
    (ξ : Set.Ioi (0 : ℝ))
    (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (ε : ℕ → Set.Ioi (0 : ℝ)) :
    Measurable (canonicalLSCLimit ξ m ε) := by
  apply B2.LscTop.measurable_limUnder
  intro n
  exact B2.LscTop.continuous_ofContinuousMap.measurable.comp
    ((measurable_rescaledLFPPMap (ξ : ℝ) (m (ε n))).comp
      (canonicalHeatVersion_measurable (ε n)))

 

theorem ae_canonicalLSCLimit_eq
    [MeasurableSpace LSCFun] [BorelSpace LSCFun]
    (ξ : Set.Ioi (0 : ℝ))
    (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (ε : ℕ → Set.Ioi (0 : ℝ)) (D : DistC → LSCMetric)
    (hD : SubseqLimit ξ m ε D)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P)
    (X : Set.Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ δ, IsHeatSmoothing P h δ (X δ)) :
    ∀ᵐ ω ∂P, canonicalLSCLimit ξ m ε (h ω) = (D (h ω)).toLSCFun := by
  have hH : ∀ᵐ ω ∂P, ∀ n,
      (canonicalHeatVersion (ε n) (h ω) : ℂ → ℝ) =
        heatMollify (ε n : ℝ) (h ω) := by
    apply ae_all_iff.mpr
    intro n
    have hcanon := canonicalHeatVersion_ae (ε n)
    rw [normGFFLaw_eq_of_normalized P h hh] at hcanon
    exact ae_of_ae_map hh.1.measurable.aemeasurable hcanon
  have hXeq : ∀ᵐ ω ∂P, ∀ n,
      (X (ε n) ω : ℂ → ℝ) = heatMollify (ε n : ℝ) (h ω) := by
    apply ae_all_iff.mpr
    intro n
    exact (DG20Pt.dg20_heat_smoothing_ae_heatMollify P h hh
      (ε n) (X (ε n)) (hX (ε n))).mono fun _ hω => funext hω
  have hLim := (hD P h (LQGMetric.DFGPS.isGFFPlusBddCont_of_wp hh.1) X hX).1
  filter_upwards [hH, hXeq, hLim] with ω hHω hXω hLω
  have hEq : ∀ n, canonicalHeatVersion (ε n) (h ω) = X (ε n) ω := by
    intro n
    apply ContinuousMap.ext
    intro z
    exact (congrFun (hHω n) z).trans (congrFun (hXω n) z).symm
  have hConv : Tendsto (fun n =>
      B2.LscTop.ofContinuousMap
        (B2.LscTop.rescaledLFPPMap (ξ : ℝ) (m (ε n))
          (canonicalHeatVersion (ε n) (h ω)))) atTop
      (𝓝 (D (h ω)).toLSCFun) := by
    apply LSCFun.tendsto_of_lscTendsto
    convert hLω using 1
    funext n
    simp only [hEq n]
    rfl
  have hConvCanon : Tendsto (fun n =>
      B2.LscTop.ofContinuousMap
        (B2.LscTop.rescaledLFPPMap (ξ : ℝ) (m (ε n))
          (canonicalHeatVersion (ε n) (h ω)))) atTop
      (𝓝 (canonicalLSCLimit ξ m ε (h ω))) :=
    tendsto_nhds_limUnder ⟨_, hConv⟩
  exact tendsto_nhds_unique hConvCanon hConv

end SupercriticalLQGUniqueness.B2.PfeAxioms
