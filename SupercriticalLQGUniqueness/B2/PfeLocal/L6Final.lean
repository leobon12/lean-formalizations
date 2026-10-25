import SupercriticalLQGUniqueness.B2.PfeLocal.L6Locality
import SupercriticalLQGUniqueness.B2.PfeLocal.L5S3

 















set_option autoImplicit false
noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeLocal

open LQGMetric

 

theorem l6_axiomII (hS4 : Iface.DG20Section4) (hPerc : Iface.DG20PercEstimate')
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)) (hm : ∀ ε, IsLFPPNormalizer ξ ε (m ε))
    (V : Set.Ioi (0 : ℝ) → DistC → C(ℂ, ℝ)) (hVm : ∀ δ, Measurable (V δ))
    (hV : ∀ δ : Set.Ioi (0 : ℝ), ∀ᵐ g ∂normGFFLaw, ∀ z, V δ g z = heatMollify (δ : ℝ) g z)
    (e : ℕ → Set.Ioi (0 : ℝ)) (he : Tendsto (fun n => (e n : ℝ)) atTop (𝓝 0))
    (c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (hc : ∀ r : ℚ, ∀ hr : 0 < r,
      Tendsto (fun n => (r : ℝ) *
        (m ⟨(e n : ℝ) / (r : ℝ), Set.mem_Ioi.mpr (div_pos (e n).2 (Rat.cast_pos.mpr hr))⟩ : ℝ) /
        (m (e n) : ℝ)) atTop (𝓝 (c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ)))
    {Ω' : Type} [MeasurableSpace Ω'] [StandardBorelSpace Ω'] [Nonempty Ω']
    (P' : Measure Ω') [IsProbabilityMeasure P']
    (h' : Ω' → DistC) (hh' : IsNormalizedWholePlaneGFF h' P')
    (hN : ℕ → Ω' → DistC) (hNm : ∀ n, Measurable (hN n))
    (hNlaw : ∀ n, P'.map (hN n) = normGFFLaw)
    (hpair : ∀ φ : TestC, ∀ᵐ ω ∂P', Tendsto (fun n => hN n ω φ) atTop (𝓝 (h' ω φ)))
    (L : Ω' → LSCMetric) (hL : Measurable L)
    (hconv : ∀ᵐ ω ∂P', Tendsto (fun n =>
      PfeWeyl.normalizedLFPPMetric ξ (m (e n)) (V (e n) (hN n ω))) atTop (𝓝 (L ω)))
    (hgeo : ∀ᵐ ω ∂P', L5Geo (L ω))
    (hsmall : Inputs.L6SmallAnnuli ξ m V e P' hN L) :
    ∃ Φ : DistC → LSCMetric, Measurable Φ ∧ ∀ᵐ ω ∂P', L ω = Φ (h' ω) :=
  l5_axiomII_of_obsLocality hS4 hPerc ξ Q hQ m hm V hVm hV e he c hc P' h' hh' hN hNm hNlaw
    hpair L hL hconv hgeo
    (l6_obsLocality ξ m V hVm hV e he P' h' hh' hN hNm hNlaw hpair L hL hconv hsmall)

 
theorem l6_hconv (hS4 : Iface.DG20Section4) (hPerc : Iface.DG20PercEstimate')
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)) (hm : ∀ ε, IsLFPPNormalizer ξ ε (m ε))
    (V : Set.Ioi (0 : ℝ) → DistC → C(ℂ, ℝ)) (hVm : ∀ δ, Measurable (V δ))
    (hV : ∀ δ : Set.Ioi (0 : ℝ), ∀ᵐ g ∂normGFFLaw, ∀ z, V δ g z = heatMollify (δ : ℝ) g z)
    (e : ℕ → Set.Ioi (0 : ℝ)) (he : Tendsto (fun n => (e n : ℝ)) atTop (𝓝 0))
    (c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (hc : ∀ r : ℚ, ∀ hr : 0 < r,
      Tendsto (fun n => (r : ℝ) *
        (m ⟨(e n : ℝ) / (r : ℝ), Set.mem_Ioi.mpr (div_pos (e n).2 (Rat.cast_pos.mpr hr))⟩ : ℝ) /
        (m (e n) : ℝ)) atTop (𝓝 (c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ)))
    {Ω' : Type} [MeasurableSpace Ω'] [StandardBorelSpace Ω'] [Nonempty Ω']
    (P' : Measure Ω') [IsProbabilityMeasure P']
    (h' : Ω' → DistC) (hh' : IsNormalizedWholePlaneGFF h' P')
    (hN : ℕ → Ω' → DistC) (hNm : ∀ n, Measurable (hN n))
    (hNlaw : ∀ n, P'.map (hN n) = normGFFLaw)
    (hpair : ∀ φ : TestC, ∀ᵐ ω ∂P', Tendsto (fun n => hN n ω φ) atTop (𝓝 (h' ω φ)))
    (L : Ω' → LSCMetric) (hL : Measurable L)
    (hconv : ∀ᵐ ω ∂P', Tendsto (fun n =>
      PfeWeyl.normalizedLFPPMetric ξ (m (e n)) (V (e n) (hN n ω))) atTop (𝓝 (L ω)))
    (hgeo : ∀ᵐ ω ∂P', L5Geo (L ω))
    (hsmall : Inputs.L6SmallAnnuli ξ m V e P' hN L) :
    ∃ Φ : DistC → LSCMetric, Measurable Φ ∧ (∀ᵐ ω ∂P', L ω = Φ (h' ω)) ∧
      ∀ᵐ ω ∂P', Tendsto (fun n =>
        PfeWeyl.normalizedLFPPMetric ξ (m (e n)) (V (e n) (hN n ω))) atTop (𝓝 (Φ (h' ω))) :=
  l5_hconv_of_obsLocality hS4 hPerc ξ Q hQ m hm V hVm hV e he c hc P' h' hh' hN hNm hNlaw
    hpair L hL hconv hgeo
    (l6_obsLocality ξ m V hVm hV e he P' h' hh' hN hNm hNlaw hpair L hL hconv hsmall)

 
theorem l6_pfeThm17_conclusion
    (hS4 : Iface.DG20Section4) (hPerc : Iface.DG20PercEstimate')
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)) (hm : ∀ ε, IsLFPPNormalizer ξ ε (m ε))
    (ε : ℕ → Set.Ioi (0 : ℝ)) (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (φ₁ : ℕ → ℕ) (hφ₁ : StrictMono φ₁) (c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (hratio : ∀ r : ℚ, ∀ hr : 0 < r,
      Tendsto (fun n => (r : ℝ) *
        (m ⟨(ε (φ₁ n) : ℝ) / (r : ℝ),
          Set.mem_Ioi.mpr (div_pos (ε (φ₁ n)).property (Rat.cast_pos.mpr hr))⟩ : ℝ) /
        (m (ε (φ₁ n)) : ℝ)) atTop
        (𝓝 (c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ)))
    (V : Set.Ioi (0 : ℝ) → DistC → C(ℂ, ℝ)) (hVm : ∀ δ, Measurable (V δ))
    (hV : ∀ δ : Set.Ioi (0 : ℝ), ∀ᵐ g ∂normGFFLaw, ∀ z, V δ g z = heatMollify (δ : ℝ) g z)
    {Ω' : Type} [MeasurableSpace Ω'] [StandardBorelSpace Ω'] [Nonempty Ω']
    (P' : Measure Ω') [IsProbabilityMeasure P']
    (h' : Ω' → DistC) (hh' : IsNormalizedWholePlaneGFF h' P')
    (hN : ℕ → Ω' → DistC) (hNm : ∀ n, Measurable (hN n))
    (hNlaw : ∀ n, P'.map (hN n) = normGFFLaw)
    (hpair : ∀ φ : TestC, ∀ᵐ ω ∂P', Tendsto (fun n => hN n ω φ) atTop (𝓝 (h' ω φ)))
    (L : Ω' → LSCMetric) (hL : Measurable L)
    (hconv : ∀ᵐ ω ∂P', Tendsto (fun n =>
      PfeWeyl.normalizedLFPPMetric ξ (m (ε (φ₁ n))) (V (ε (φ₁ n)) (hN n ω))) atTop (𝓝 (L ω)))
    (hgeo : ∀ᵐ ω ∂P', L5Geo (L ω))
    (hsmall : Inputs.L6SmallAnnuli ξ m V (fun n => ε (φ₁ n)) P' hN L)
    (happrox : ∀ Φ : DistC → LSCMetric, Measurable Φ → (∀ᵐ ω ∂P', L ω = Φ (h' ω)) →
      ∀ κ : ℝ≥0∞, 0 < κ → ∃ Ψ : DistC → LSCMetric, Measurable Ψ ∧
        normGFFLaw {g | Φ g ≠ Ψ g} < κ ∧
        ∀ᵐ ω ∂P', Tendsto (fun n => Ψ (hN n ω)) atTop (𝓝 (Ψ (h' ω))))
    (hS2 : ∀ Φ : DistC → LSCMetric, Measurable Φ → (∀ᵐ ω ∂P', L ω = Φ (h' ω)) →
      ∃ D : DistC → LSCMetric, Iface.IsPfeWeakMetric ξ D c ∧
        (∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (hf : Ω → DistC), IsNormalizedWholePlaneGFF hf P → ∀ᵐ ω ∂P, D (hf ω) = Φ (hf ω)) ∧
        PfeWeyl.NormalizedLimitGeometry D ∧ PfeWeyl.NormalizedAcrossTails D ∧
        PfeWeyl.NormalizedSmallAnnuli ξ m (ε ∘ φ₁) D ∧
        PfeWeyl.NormalizedPointCircles ξ m (ε ∘ φ₁) D) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ D : DistC → LSCMetric, ∃ c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ),
        Iface.IsPfeWeakMetric ξ D c ∧ Iface.SubseqLimit ξ m (ε ∘ φ) D ∧
          (∀ r : ℚ, ∀ hr : 0 < r,
            Tendsto (fun n => (r : ℝ) *
              (m ⟨(ε (φ n) : ℝ) / (r : ℝ),
                Set.mem_Ioi.mpr (div_pos (ε (φ n)).property (Rat.cast_pos.mpr hr))⟩ : ℝ) /
              (m (ε (φ n)) : ℝ)) atTop
              (𝓝 (c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ))) :=
  l5_pfeThm17_conclusion_of_obsLocality hS4 hPerc ξ Q hQ m hm ε hε φ₁ hφ₁ c hratio V hVm hV P'
    h' hh' hN hNm hNlaw hpair L hL hconv hgeo
    (l6_obsLocality ξ m V hVm hV (fun n => ε (φ₁ n)) (hε.comp hφ₁.tendsto_atTop) P' h' hh' hN
      hNm hNlaw hpair L hL hconv hsmall)
    happrox hS2

end SupercriticalLQGUniqueness.B2.PfeLocal
