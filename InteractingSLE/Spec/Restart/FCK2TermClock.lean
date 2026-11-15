/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FCK2TermChart

/-! # Simplicity of the actual canonical chart paths, through finite lifetimes -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn)

namespace InteractingSLE.Restart.FCPlumb
universe u

/-- An increasing clock reading of a simple physical path is simple. The
chart inverse need not be injective for this implication. -/
theorem injOn_of_increasing_clock_reading {η γ : ℝ≥0 → ℂ} {ψ : ℂ → ℂ}
    {c : ℝ≥0 → ℝ≥0} {U ζ : ℝ≥0∞}
    (hc : StrictMonoOn c {r | (r : ℝ≥0∞) ≤ U})
    (hl : ∀ r : ℝ≥0, (r : ℝ≥0∞) ≤ U → (c r : ℝ≥0∞) ≤ ζ)
    (hr : ∀ r : ℝ≥0, (r : ℝ≥0∞) ≤ U → η (c r) = ψ (γ r))
    (hi : InjOn η {s | (s : ℝ≥0∞) ≤ ζ}) :
    InjOn γ {r | (r : ℝ≥0∞) ≤ U} := by
  intro a ha b hb hab
  apply hc.injOn ha hb
  apply hi (hl a ha) (hl b hb)
  rw [hr a ha, hr b hb, hab]

/-- Both supplied canonical paths are injective on their closed lifetimes,
almost surely on the available first-contact branch. -/
theorem ae_canon_injOn_closed_life
    {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (h77 : Supp10.Lemma77Statement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {b : ℝ → ℝ} {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J)
    {x₁ x₂ θ₁ θ₂ : ℝ} (hx : x₂ < x₁) (hθ : θ₁ < θ₂ + Real.pi)
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b J)
    {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
    (hη₁ : IsFlowLine κ b J x₁ θ₁ P h η₁ ζ₁)
    (hη₂ : IsFlowLine κ b J x₂ θ₂ P h η₂ ζ₂)
    {d : PairData Ω} (hd : d.IsMeasGood) (hζ₁ : d.ζ₁ = ζ₁) (hζ₂ : d.ζ₂ = ζ₂)
    (hae : ∀ᵐ ω ∂P, ω ∈ d.G ∧
      (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → d.η₁ ω s = η₁ ω s) ∧
      ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₂ ω → d.η₂ ω s = η₂ ω s)
    {γ₁ γ₂ : Ω → ℝ≥0 → ℂ} {U₁ U₂ : Ω → ℝ≥0∞}
    (hcanon : d.IsCanonClock P γ₁ γ₂ U₁ U₂) :
    ∀ᵐ ω ∂P, ω ∈ meetSet d →
      InjOn (γ₁ ω) {r | (r : ℝ≥0∞) ≤ U₁ ω} ∧
        InjOn (γ₂ ω) {r | (r : ℝ≥0∞) ≤ U₂ ω} := by
  obtain ⟨γc₁, γc₂, Uc₁, Uc₂, -, -, -, -, -, -, hcan, hdata⟩ :=
    exists_canonClock Theorem15.aux25Statement h77 hκ hκ4 hb hx hθ hh hη₁ hη₂
      hd hζ₁ hζ₂ hae
  have hp₁ := ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₁
  have hp₂ := ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₂
  filter_upwards [ae_canonClock_eq hcanon hcan, hdata, hae, hp₁, hp₂]
    with ω he hdω ha hp₁ω hp₂ω hm
  obtain ⟨hE, hs, ht⟩ := mem_meetSet_iff.1 hm
  have ha₁ : ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ d.ζ₁ ω → d.η₁ ω s = η₁ ω s := by
    simpa only [hζ₁] using ha.2.1
  have ha₂ : ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ d.ζ₂ ω → d.η₂ ω s = η₂ ω s := by
    simpa only [hζ₂] using ha.2.2
  have hf := (isFirstContact_congr ha₁ ha₂).1 (hd.isFirstContact hE)
  simp only [hζ₁, hζ₂] at hf hs ht
  obtain ⟨c₁, c₂, hc₁, hi₁, hc₂, hi₂, -, -, hr₁, hr₂⟩ := hdω _ _ hf hs ht
  obtain ⟨e₁, e₂, hγ₁, hγ₂⟩ := he hm
  have hiγ₁ := injOn_of_increasing_clock_reading hc₁
    (fun r hr => (hi₁ ▸ mem_image_of_mem c₁ hr).2) hr₁ hp₁ω.1
  have hiγ₂ := injOn_of_increasing_clock_reading hc₂
    (fun r hr => (hi₂ ▸ mem_image_of_mem c₂ hr).2) hr₂ hp₂ω.1
  rw [← e₁] at hiγ₁
  rw [← e₂] at hiγ₂
  exact ⟨hiγ₁.congr (fun r hr => (hγ₁ r hr).symm),
    hiγ₂.congr (fun r hr => (hγ₂ r hr).symm)⟩

end InteractingSLE.Restart.FCPlumb
