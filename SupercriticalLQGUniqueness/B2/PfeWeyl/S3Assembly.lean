import SupercriticalLQGUniqueness.B2.PfeWeyl.S3Reference
import SupercriticalLQGUniqueness.B2.PfeWeyl.S1Circles

 





















set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal
open LQGMetric (DistC normGFFLaw heatMollify)
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.PfeWeyl

 
theorem normalizedLscLimit_comp {ξ : Set.Ioi (0 : ℝ)} {m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)}
    {ε : ℕ → Set.Ioi (0 : ℝ)} {D : DistC → LSCMetric} (h : NormalizedLscLimit ξ m ε D)
    {ns : ℕ → ℕ} (hns : StrictMono ns) : NormalizedLscLimit ξ m (ε ∘ ns) D := by
  intro Ω _ P _ hf hh X hX
  filter_upwards [h P hf hh X hX] with ω hω
  exact hω.comp_strictMono hns

 
theorem normalizedLscLimit_congr {ξ : Set.Ioi (0 : ℝ)} {m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)}
    {ε : ℕ → Set.Ioi (0 : ℝ)} {Φ D : DistC → LSCMetric} (h : NormalizedLscLimit ξ m ε Φ)
    (hDΦ : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (hf : Ω → DistC), IsNormalizedWholePlaneGFF hf P → ∀ᵐ ω ∂P, D (hf ω) = Φ (hf ω)) :
    NormalizedLscLimit ξ m ε D := by
  intro Ω _ P _ hf hh X hX
  filter_upwards [h P hf hh X hX, hDΦ P hf hh] with ω hω hD
  rw [hD]
  exact hω

 
theorem normalizedSmallAnnuli_comp {ξ : Set.Ioi (0 : ℝ)} {m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)}
    {ε : ℕ → Set.Ioi (0 : ℝ)} {D : DistC → LSCMetric} (h : NormalizedSmallAnnuli ξ m ε D)
    {ns : ℕ → ℕ} (hns : StrictMono ns) : NormalizedSmallAnnuli ξ m (ε ∘ ns) D := by
  intro Ω _ P _ hf hh X hX k
  filter_upwards [h P hf hh X hX k] with ω hω
  intro z hz hns' δ hδ ρ hρ
  obtain ⟨A, h1, h2, h3, h4, h5⟩ := hω z hz hns' δ hδ ρ hρ
  exact ⟨A, h1, h2, h3, h4, hns.tendsto_atTop.eventually h5⟩

 
theorem normalizedPointCircles_comp {ξ : Set.Ioi (0 : ℝ)} {m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)}
    {ε : ℕ → Set.Ioi (0 : ℝ)} {D : DistC → LSCMetric} (h : NormalizedPointCircles ξ m ε D)
    {ns : ℕ → ℕ} (hns : StrictMono ns) : NormalizedPointCircles ξ m (ε ∘ ns) D := by
  intro Ω _ P _ hf hh X hX x y r x' y' r' hr hr' h0
  filter_upwards [h P hf hh X hX x y r x' y' r' hr hr' h0] with ω hω
  exact hω.comp hns.tendsto_atTop

 
theorem pfeThm17_conclusion_of_coupling
    (ξ : Set.Ioi (0 : ℝ)) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
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
    (Φ : DistC → LSCMetric) (hΦ : Measurable Φ)
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (hN : ℕ → Ω' → DistC) (h' : Ω' → DistC) (hNm : ∀ n, Measurable (hN n))
    (h'm : Measurable h') (hNlaw : ∀ n, P'.map (hN n) = normGFFLaw)
    (h'law : P'.map h' = normGFFLaw)
    (hconv : ∀ᵐ ω ∂P', Tendsto (fun n =>
      normalizedLFPPMetric (ξ : ℝ) (m (ε (φ₁ n))) (V (ε (φ₁ n)) (hN n ω))) atTop
        (𝓝 (Φ (h' ω))))
    (happrox : ∀ κ : ℝ≥0∞, 0 < κ → ∃ Ψ : DistC → LSCMetric, Measurable Ψ ∧
      normGFFLaw {g | Φ g ≠ Ψ g} < κ ∧
      ∀ᵐ ω ∂P', Tendsto (fun n => Ψ (hN n ω)) atTop (𝓝 (Ψ (h' ω))))
    (D : DistC → LSCMetric) (hPfe : IsPfeWeakMetric ξ D c)
    (hDΦ : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (hf : Ω → DistC), IsNormalizedWholePlaneGFF hf P → ∀ᵐ ω ∂P, D (hf ω) = Φ (hf ω))
    (hgeo : NormalizedLimitGeometry D) (htail : NormalizedAcrossTails D)
    (hsmall : NormalizedSmallAnnuli ξ m (ε ∘ φ₁) D)
    (hpts : NormalizedPointCircles ξ m (ε ∘ φ₁) D) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ D : DistC → LSCMetric, ∃ c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ),
        IsPfeWeakMetric ξ D c ∧ SubseqLimit ξ m (ε ∘ φ) D ∧
          (∀ r : ℚ, ∀ hr : 0 < r,
            Tendsto (fun n => (r : ℝ) *
              (m ⟨(ε (φ n) : ℝ) / (r : ℝ),
                Set.mem_Ioi.mpr (div_pos (ε (φ n)).property (Rat.cast_pos.mpr hr))⟩ : ℝ) /
              (m (ε (φ n)) : ℝ)) atTop
              (𝓝 (c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ))) := by
  obtain ⟨ns, hns, hlscΦ⟩ := normalizedLscLimit_of_coupling ξ m (ε ∘ φ₁) V hVm hV Φ hΦ P'
    hN h' hNm h'm hNlaw h'law hconv happrox
  have hlscD : NormalizedLscLimit ξ m ((ε ∘ φ₁) ∘ ns) D := normalizedLscLimit_congr hlscΦ hDΦ
  have hε' : Tendsto (fun n => (((ε ∘ φ₁) ∘ ns) n : ℝ)) atTop (𝓝 0) :=
    hε.comp (hφ₁.comp hns).tendsto_atTop
  refine ⟨φ₁ ∘ ns, hφ₁.comp hns, D, c, hPfe, ?_, fun r hr => ?_⟩
  · exact subseqLimit_of_normalizedLsc_of_pfeWeak ξ m ((ε ∘ φ₁) ∘ ns) hε' D c hPfe hlscD hgeo
      htail (normalizedSmallAnnuli_comp hsmall hns) (normalizedPointCircles_comp hpts hns)
  · exact (hratio r hr).comp hns.tendsto_atTop

end SupercriticalLQGUniqueness.B2.PfeWeyl
