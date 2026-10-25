import SupercriticalLQGUniqueness.B2.PfeLocal.L5Main
import SupercriticalLQGUniqueness.B2.PfeWeyl.S3Assembly
import SupercriticalLQGUniqueness.B2.PfeWeyl.S3Bridge
import SupercriticalLQGUniqueness.B2.PfeAxioms.NormalizedLaw

 





















set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal
open LQGMetric (DistC normGFFLaw heatMollify TestC)
open LQGMetric LQGMetric.DDDF

namespace SupercriticalLQGUniqueness.B2.PfeLocal

 
theorem l5_identification_ae_unique {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω')
    [IsProbabilityMeasure P'] (h' : Ω' → DistC) (hh' : IsNormalizedWholePlaneGFF h' P')
    (L : Ω' → LSCMetric) {Φ Φ' : DistC → LSCMetric} (hΦ : Measurable Φ) (hΦ' : Measurable Φ')
    (h1 : ∀ᵐ ω ∂P', L ω = Φ (h' ω)) (h2 : ∀ᵐ ω ∂P', L ω = Φ' (h' ω)) :
    ∀ᵐ g ∂normGFFLaw, Φ g = Φ' g := by
  have hm : Measurable h' := hh'.1.measurable
  have hS : MeasurableSet {g : DistC | Φ g = Φ' g} :=
    isClosed_diagonal.measurableSet.preimage (hΦ.prodMk hΦ')
  rw [PfeAxioms.normGFFLaw_eq_of_normalized P' h' hh',
    ae_map_iff (p := fun g => Φ g = Φ' g) hm.aemeasurable hS]
  filter_upwards [h1, h2] with ω hω hω'
  rw [← hω, ← hω']

 

theorem l5_happrox_of_lusin {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω')
    (hN : ℕ → Ω' → DistC) (h' : Ω' → DistC)
    (hNconv : ∀ᵐ ω ∂P', Tendsto (fun n => hN n ω) atTop (𝓝 (h' ω)))
    (hlusin : ∀ Φ : DistC → LSCMetric, Measurable Φ → ∀ κ : ℝ≥0∞, 0 < κ →
      ∃ Ψ : DistC → LSCMetric, Measurable Ψ ∧ Continuous Ψ ∧ normGFFLaw {g | Φ g ≠ Ψ g} < κ)
    (Φ : DistC → LSCMetric) (hΦ : Measurable Φ) :
    ∀ κ : ℝ≥0∞, 0 < κ → ∃ Ψ : DistC → LSCMetric, Measurable Ψ ∧
      normGFFLaw {g | Φ g ≠ Ψ g} < κ ∧
      ∀ᵐ ω ∂P', Tendsto (fun n => Ψ (hN n ω)) atTop (𝓝 (Ψ (h' ω))) :=
  PfeWeyl.happrox_of_continuous_approx Φ P' hN h' hNconv (hlusin Φ hΦ)

 

theorem l5_pfeThm17_conclusion_of_obsLocality
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
    (hloc : Inputs.L5ObsLocality P' h' L)
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
              (𝓝 (c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ))) := by
  have he : Tendsto (fun n => (ε (φ₁ n) : ℝ)) atTop (𝓝 0) :=
    hε.comp hφ₁.tendsto_atTop
  obtain ⟨Φ, hΦ, hII, hconvΦ⟩ := l5_hconv_of_obsLocality hS4 hPerc ξ Q hQ m hm V hVm hV
    (fun n => ε (φ₁ n)) he c hratio P' h' hh' hN hNm hNlaw hpair L hL hconv hgeo hloc
  obtain ⟨D, hPfe, hDΦ, hgeoD, htail, hsmall, hpts⟩ := hS2 Φ hΦ hII
  exact PfeWeyl.pfeThm17_conclusion_of_coupling ξ m ε hε φ₁ hφ₁ c hratio V hVm hV Φ hΦ P' hN h'
    hNm hh'.1.measurable hNlaw (PfeAxioms.normGFFLaw_eq_of_normalized P' h' hh').symm hconvΦ
    (happrox Φ hΦ hII) D hPfe hDΦ hgeoD htail hsmall hpts

end SupercriticalLQGUniqueness.B2.PfeLocal
