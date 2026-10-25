import SupercriticalLQGUniqueness.B2.PfeAxioms.S2Locality
import SupercriticalLQGUniqueness.B2.PfeAxioms.A4DG20Inputs
import SupercriticalLQGUniqueness.B2.PfeWeyl.S3Assembly

 

















set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal
open LQGMetric (DistC normGFFLaw heatMollify)
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

 

theorem ae_mem_patchLocus_of_gffPlusCont
    (ξ : Ioi (0 : ℝ)) (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (ε : ℕ → Ioi (0 : ℝ)) (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (Φ : DistC → LSCMetric)
    (hlsc : PfeWeyl.NormalizedLscLimit ξ m ε Φ)
    (hgeo : PfeWeyl.NormalizedLimitGeometry Φ)
    (htail : PfeWeyl.NormalizedAcrossTails Φ)
    (hsmall : PfeWeyl.NormalizedSmallAnnuli ξ m ε Φ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (hh : LQGMetric.IsGFFPlusCont h P) :
    ∀ᵐ ω ∂P, h ω ∈ patchLocus ξ m ε := by
  obtain ⟨h₀, g, hh₀, -, hdec⟩ := LQGMetric.DFGPS.T12.isGFFPlusCont_decomp hh
  have hh₀' : IsNormalizedWholePlaneGFF h₀ P := isNormalizedWholePlaneGFF_iff_old.mpr hh₀
  filter_upwards [ae_patchWitness_weyl_of_normalized ξ m ε hε Φ hlsc hgeo htail hsmall P h₀ hh₀']
    with ω hω
  rw [hdec ω]
  exact (hω (g ω)).1

 
theorem isPfeWeakMetric_patchWitness
    [MeasurableSpace LSCFun] [BorelSpace LSCFun]
    (hSkC : B2.DG20Lim.DG20LimitSkC)
    (hS : DG20Section4) (hPerc : DG20PercEstimate')
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (hm : ∀ δ, IsLFPPNormalizer ξ δ (m δ))
    (ε : ℕ → Ioi (0 : ℝ)) (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (Φ : DistC → LSCMetric)
    (hlsc : PfeWeyl.NormalizedLscLimit ξ m ε Φ)
    (hgeo : PfeWeyl.NormalizedLimitGeometry Φ)
    (htail : PfeWeyl.NormalizedAcrossTails Φ)
    (hsmall : PfeWeyl.NormalizedSmallAnnuli ξ m ε Φ)
    (hpts : PfeWeyl.NormalizedPointCircles ξ m ε Φ)
    (c : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (hc : ∀ r : ℚ, ∀ hr : 0 < r,
      Tendsto (fun n => (r : ℝ) *
        (m ⟨(ε n : ℝ) / (r : ℝ),
          Set.mem_Ioi.mpr (div_pos (ε n).property (Rat.cast_pos.mpr hr))⟩ : ℝ) /
        (m (ε n) : ℝ)) atTop
        (𝓝 (c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ)))
    (Λ : ℝ) (hΛ : 1 < Λ)
    (hV : ∀ δ : Ioo (0 : ℝ) 1, ∀ r : ℚ, ∀ hr : 0 < r,
      Λ⁻¹ * (δ : ℝ) ^ Λ ≤
        (c ⟨(δ : ℝ) * (r : ℝ), Set.mem_Ioi.mpr
          (mul_pos δ.property.1 (Rat.cast_pos.mpr hr))⟩ : ℝ) /
          (c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ) ∧
      (c ⟨(δ : ℝ) * (r : ℝ), Set.mem_Ioi.mpr
          (mul_pos δ.property.1 (Rat.cast_pos.mpr hr))⟩ : ℝ) /
          (c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ) ≤
        Λ * (δ : ℝ) ^ (-Λ)) :
    IsPfeWeakMetric ξ (patchWitness ξ m ε) c := by
  refine ⟨measurable_patchWitness ξ m ε, ?_, ?_, ?_, ?_, ⟨Λ, hΛ, hV⟩, ?_⟩
  · intro Ω _ P _ h hh
    exact ae_isLengthSpace_patchWitness_of_gffPlusCont ξ m ε hε Φ hlsc hgeo htail hsmall P h hh
  · intro Ω _ P _ h hh U
    exact patchWitness_locality_of_gffPlusCont ξ m ε hε Φ hlsc hgeo htail hsmall P h hh U
  · intro Ω _ P _ h hh
    exact ae_weyl_patchWitness_of_gffPlusCont ξ m ε hε Φ hlsc hgeo htail hsmall P h hh
  · intro Ω _ P _ h hh z
    exact ae_translate_patchWitness_of_gffPlusCont ξ m ε hε Φ hlsc hgeo htail hsmall hSkC Q hQ
      hm hpts P h hh z
  · exact pfeAxiomV_patchWitness hSkC hS hPerc ξ Q hQ m hm ε hε Φ hlsc hgeo htail hsmall hpts
      c hc Λ hΛ hV

 



theorem pfeThm17_conclusion_of_coupling_patch
    [MeasurableSpace LSCFun] [BorelSpace LSCFun]
    (hSkC : B2.DG20Lim.DG20LimitSkC)
    (hS : DG20Section4) (hPerc : DG20PercEstimate')
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (hm : ∀ δ, IsLFPPNormalizer ξ δ (m δ))
    (ε : ℕ → Ioi (0 : ℝ)) (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (φ₁ : ℕ → ℕ) (hφ₁ : StrictMono φ₁) (c : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (hratio : ∀ r : ℚ, ∀ hr : 0 < r,
      Tendsto (fun n => (r : ℝ) *
        (m ⟨(ε (φ₁ n) : ℝ) / (r : ℝ),
          Set.mem_Ioi.mpr (div_pos (ε (φ₁ n)).property (Rat.cast_pos.mpr hr))⟩ : ℝ) /
        (m (ε (φ₁ n)) : ℝ)) atTop
        (𝓝 (c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ)))
    (Λ : ℝ) (hΛ : 1 < Λ)
    (hV17 : ∀ δ : Ioo (0 : ℝ) 1, ∀ r : ℚ, ∀ hr : 0 < r,
      Λ⁻¹ * (δ : ℝ) ^ Λ ≤
        (c ⟨(δ : ℝ) * (r : ℝ), Set.mem_Ioi.mpr
          (mul_pos δ.property.1 (Rat.cast_pos.mpr hr))⟩ : ℝ) /
          (c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ) ∧
      (c ⟨(δ : ℝ) * (r : ℝ), Set.mem_Ioi.mpr
          (mul_pos δ.property.1 (Rat.cast_pos.mpr hr))⟩ : ℝ) /
          (c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ) ≤
        Λ * (δ : ℝ) ^ (-Λ))
    (V : Ioi (0 : ℝ) → DistC → C(ℂ, ℝ)) (hVm : ∀ δ, Measurable (V δ))
    (hV : ∀ δ : Ioi (0 : ℝ), ∀ᵐ g ∂normGFFLaw, ∀ z, V δ g z = heatMollify (δ : ℝ) g z)
    (Φ : DistC → LSCMetric) (hΦ : Measurable Φ)
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (hN : ℕ → Ω' → DistC) (h' : Ω' → DistC) (hNm : ∀ n, Measurable (hN n))
    (h'm : Measurable h') (hNlaw : ∀ n, P'.map (hN n) = normGFFLaw)
    (h'law : P'.map h' = normGFFLaw)
    (hconv : ∀ᵐ ω ∂P', Tendsto (fun n =>
      PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m (ε (φ₁ n))) (V (ε (φ₁ n)) (hN n ω))) atTop
        (𝓝 (Φ (h' ω))))
    (happrox : ∀ κ : ℝ≥0∞, 0 < κ → ∃ Ψ : DistC → LSCMetric, Measurable Ψ ∧
      normGFFLaw {g | Φ g ≠ Ψ g} < κ ∧
      ∀ᵐ ω ∂P', Tendsto (fun n => Ψ (hN n ω)) atTop (𝓝 (Ψ (h' ω))))
    (hgeo : PfeWeyl.NormalizedLimitGeometry Φ) (htail : PfeWeyl.NormalizedAcrossTails Φ)
    (hsmall : PfeWeyl.NormalizedSmallAnnuli ξ m (ε ∘ φ₁) Φ)
    (hpts : PfeWeyl.NormalizedPointCircles ξ m (ε ∘ φ₁) Φ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ D : DistC → LSCMetric, ∃ c : Ioi (0 : ℝ) → Ioi (0 : ℝ),
        IsPfeWeakMetric ξ D c ∧ SubseqLimit ξ m (ε ∘ φ) D ∧
          (∀ r : ℚ, ∀ hr : 0 < r,
            Tendsto (fun n => (r : ℝ) *
              (m ⟨(ε (φ n) : ℝ) / (r : ℝ),
                Set.mem_Ioi.mpr (div_pos (ε (φ n)).property (Rat.cast_pos.mpr hr))⟩ : ℝ) /
              (m (ε (φ n)) : ℝ)) atTop
              (𝓝 (c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ))) := by
  obtain ⟨ns, hns, hlscΦ⟩ := PfeWeyl.normalizedLscLimit_of_coupling ξ m (ε ∘ φ₁) V hVm hV Φ
    hΦ P' hN h' hNm h'm hNlaw h'law hconv happrox
  have hε' : Tendsto (fun n => (((ε ∘ φ₁) ∘ ns) n : ℝ)) atTop (𝓝 0) :=
    hε.comp (hφ₁.comp hns).tendsto_atTop
  have hsmall' : PfeWeyl.NormalizedSmallAnnuli ξ m ((ε ∘ φ₁) ∘ ns) Φ :=
    PfeWeyl.normalizedSmallAnnuli_comp hsmall hns
  have hpts' : PfeWeyl.NormalizedPointCircles ξ m ((ε ∘ φ₁) ∘ ns) Φ :=
    PfeWeyl.normalizedPointCircles_comp hpts hns
  have hc' : ∀ r : ℚ, ∀ hr : 0 < r,
      Tendsto (fun n => (r : ℝ) *
        (m ⟨((((ε ∘ φ₁) ∘ ns) n : Ioi (0 : ℝ)) : ℝ) / (r : ℝ),
          Set.mem_Ioi.mpr (div_pos (((ε ∘ φ₁) ∘ ns) n).property (Rat.cast_pos.mpr hr))⟩ : ℝ) /
        (m (((ε ∘ φ₁) ∘ ns) n) : ℝ)) atTop
        (𝓝 (c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ)) :=
    fun r hr => (hratio r hr).comp hns.tendsto_atTop
  refine ⟨φ₁ ∘ ns, hφ₁.comp hns, patchWitness ξ m ((ε ∘ φ₁) ∘ ns), c, ?_, ?_, hc'⟩
  · exact isPfeWeakMetric_patchWitness hSkC hS hPerc ξ Q hQ m hm ((ε ∘ φ₁) ∘ ns) hε' Φ hlscΦ
      hgeo htail hsmall' hpts' c hc' Λ hΛ hV17
  · exact subseqLimit_patchWitness ξ m ((ε ∘ φ₁) ∘ ns) hε' Φ hlscΦ hgeo htail hsmall' hpts'

 

theorem pfeThm17_conclusion_of_coupling_patch_dg20Inputs
    (hS : DG20Section4) (hPerc : DG20PercEstimate')
    (hRatio : DG20QuantileRatio) (hRel : DG20ExponentRelation)
    (hPos : DG20ExponentPositive)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (hm : ∀ δ, IsLFPPNormalizer ξ δ (m δ))
    (ε : ℕ → Ioi (0 : ℝ)) (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (φ₁ : ℕ → ℕ) (hφ₁ : StrictMono φ₁) (c : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (hratio : ∀ r : ℚ, ∀ hr : 0 < r,
      Tendsto (fun n => (r : ℝ) *
        (m ⟨(ε (φ₁ n) : ℝ) / (r : ℝ),
          Set.mem_Ioi.mpr (div_pos (ε (φ₁ n)).property (Rat.cast_pos.mpr hr))⟩ : ℝ) /
        (m (ε (φ₁ n)) : ℝ)) atTop
        (𝓝 (c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ)))
    (Λ : ℝ) (hΛ : 1 < Λ)
    (hV17 : ∀ δ : Ioo (0 : ℝ) 1, ∀ r : ℚ, ∀ hr : 0 < r,
      Λ⁻¹ * (δ : ℝ) ^ Λ ≤
        (c ⟨(δ : ℝ) * (r : ℝ), Set.mem_Ioi.mpr
          (mul_pos δ.property.1 (Rat.cast_pos.mpr hr))⟩ : ℝ) /
          (c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ) ∧
      (c ⟨(δ : ℝ) * (r : ℝ), Set.mem_Ioi.mpr
          (mul_pos δ.property.1 (Rat.cast_pos.mpr hr))⟩ : ℝ) /
          (c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ) ≤
        Λ * (δ : ℝ) ^ (-Λ))
    (V : Ioi (0 : ℝ) → DistC → C(ℂ, ℝ)) (hVm : ∀ δ, Measurable (V δ))
    (hV : ∀ δ : Ioi (0 : ℝ), ∀ᵐ g ∂normGFFLaw, ∀ z, V δ g z = heatMollify (δ : ℝ) g z)
    (Φ : DistC → LSCMetric) (hΦ : Measurable Φ)
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (hN : ℕ → Ω' → DistC) (h' : Ω' → DistC) (hNm : ∀ n, Measurable (hN n))
    (h'm : Measurable h') (hNlaw : ∀ n, P'.map (hN n) = normGFFLaw)
    (h'law : P'.map h' = normGFFLaw)
    (hconv : ∀ᵐ ω ∂P', Tendsto (fun n =>
      PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m (ε (φ₁ n))) (V (ε (φ₁ n)) (hN n ω))) atTop
        (𝓝 (Φ (h' ω))))
    (happrox : ∀ κ : ℝ≥0∞, 0 < κ → ∃ Ψ : DistC → LSCMetric, Measurable Ψ ∧
      normGFFLaw {g | Φ g ≠ Ψ g} < κ ∧
      ∀ᵐ ω ∂P', Tendsto (fun n => Ψ (hN n ω)) atTop (𝓝 (Ψ (h' ω))))
    (hgeo : PfeWeyl.NormalizedLimitGeometry Φ) (htail : PfeWeyl.NormalizedAcrossTails Φ)
    (hsmall : PfeWeyl.NormalizedSmallAnnuli ξ m (ε ∘ φ₁) Φ)
    (hpts : PfeWeyl.NormalizedPointCircles ξ m (ε ∘ φ₁) Φ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ D : DistC → LSCMetric, ∃ c : Ioi (0 : ℝ) → Ioi (0 : ℝ),
        IsPfeWeakMetric ξ D c ∧ SubseqLimit ξ m (ε ∘ φ) D ∧
          (∀ r : ℚ, ∀ hr : 0 < r,
            Tendsto (fun n => (r : ℝ) *
              (m ⟨(ε (φ n) : ℝ) / (r : ℝ),
                Set.mem_Ioi.mpr (div_pos (ε (φ n)).property (Rat.cast_pos.mpr hr))⟩ : ℝ) /
              (m (ε (φ n)) : ℝ)) atTop
              (𝓝 (c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ))) := by
  let _ : MeasurableSpace LSCFun := borel LSCFun
  have _ : BorelSpace LSCFun := ⟨rfl⟩
  exact pfeThm17_conclusion_of_coupling_patch
    (dg20LimitSkC_of_dg20Inputs hS hPerc hRatio hRel hPos) hS hPerc ξ Q hQ m hm ε hε φ₁ hφ₁ c
    hratio Λ hΛ hV17 V hVm hV Φ hΦ P' hN h' hNm h'm hNlaw h'law hconv happrox hgeo htail hsmall
    hpts

end SupercriticalLQGUniqueness.B2.PfeAxioms
