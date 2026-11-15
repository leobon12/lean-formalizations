/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FCK2Cap

/-!
# Finite source endpoints are read at the original terminal time

The closed, onto clock data suffice. A finite capacity endpoint cannot
correspond to an infinite physical lifetime. This avoids an extra terminal
clock hypothesis in the source collision argument.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn)

namespace InteractingSLE.Restart.FCPlumb
universe u

/-- The largest point of a finite clock interval maps to the physical
terminal time; its smallest point maps to the physical start. -/
theorem endpoints_of_finite_clock_image {c : ℝ≥0 → ℝ≥0} {σ T : ℝ≥0} {ζ U : ℝ≥0∞}
    (hc : StrictMonoOn c {r | (r : ℝ≥0∞) ≤ U})
    (hi : c '' {r | (r : ℝ≥0∞) ≤ U} = {s | σ ≤ s ∧ (s : ℝ≥0∞) ≤ ζ})
    (hT : (T : ℝ≥0∞) = U) : ζ = (c T : ℝ≥0∞) ∧ c 0 = σ := by
  have hTU : (T : ℝ≥0∞) ≤ U := hT.le
  have hmax : IsGreatest {s : ℝ≥0 | σ ≤ s ∧ (s : ℝ≥0∞) ≤ ζ} (c T) := by
    rw [← hi]
    refine ⟨⟨T, hTU, rfl⟩, ?_⟩
    rintro s ⟨r, hr, rfl⟩
    exact hc.monotoneOn hr hTU (ENNReal.coe_le_coe.1 (hr.trans_eq hT.symm))
  have hfin : ζ ≠ ⊤ := by
    intro he
    have h := hmax.2 (show c T + 1 ∈ {s : ℝ≥0 | σ ≤ s ∧ (s : ℝ≥0∞) ≤ ζ} from
      ⟨hmax.1.1.trans le_self_add, by rw [he]; exact le_top⟩)
    exact (not_le_of_gt (lt_add_one (c T))) h
  have hco : c T ≤ ζ.toNNReal :=
    ENNReal.coe_le_coe.1 ((hmax.1.2).trans_eq (ENNReal.coe_toNNReal hfin).symm)
  have hζmem : ζ.toNNReal ∈ {s : ℝ≥0 | σ ≤ s ∧ (s : ℝ≥0∞) ≤ ζ} :=
    ⟨hmax.1.1.trans hco, (ENNReal.coe_toNNReal hfin).le⟩
  have he : c T = ζ.toNNReal := le_antisymm hco (hmax.2 hζmem)
  refine ⟨by rw [he, ENNReal.coe_toNNReal hfin], ?_⟩
  have hzero : (0 : ℝ≥0∞) ≤ U := zero_le
  have hc0 : σ ≤ c 0 := (hi ▸ mem_image_of_mem c hzero).1
  obtain ⟨r, hr, hcr⟩ := hi.symm ▸
    (show σ ∈ {s : ℝ≥0 | σ ≤ s ∧ (s : ℝ≥0∞) ≤ ζ} from
      ⟨le_rfl, (ENNReal.coe_le_coe.2 hmax.1.1).trans hmax.1.2⟩)
  exact le_antisymm ((hc.monotoneOn hzero hr zero_le).trans_eq hcr) hc0

/-- Reading a nonempty continuation at a finite canonical endpoint reads
the original finite endpoint, and that capacity endpoint is positive. -/
theorem terminal_reading_of_clock_image {ψ : ℂ → ℂ} {η γ : ℝ≥0 → ℂ}
    {c : ℝ≥0 → ℝ≥0} {σ T : ℝ≥0} {ζ U : ℝ≥0∞}
    (hc : StrictMonoOn c {r | (r : ℝ≥0∞) ≤ U})
    (hi : c '' {r | (r : ℝ≥0∞) ≤ U} = {s | σ ≤ s ∧ (s : ℝ≥0∞) ≤ ζ})
    (hr : ∀ r : ℝ≥0, (r : ℝ≥0∞) ≤ U → η (c r) = ψ (γ r))
    (hσ : (σ : ℝ≥0∞) < ζ) (hT : (T : ℝ≥0∞) = U) :
    0 < T ∧ ζ ≠ ⊤ ∧ ψ (γ T) = η ζ.toNNReal := by
  obtain ⟨he, hz⟩ := endpoints_of_finite_clock_image hc hi hT
  have hfin : ζ ≠ ⊤ := he ▸ ENNReal.coe_ne_top
  have ht : 0 < T := pos_iff_ne_zero.2 fun ht => by
    rw [he, ht, hz] at hσ
    exact lt_irrefl _ hσ
  refine ⟨ht, hfin, ?_⟩
  rw [← hr T hT.le, he, ENNReal.toNNReal_coe]

/-- On the original source coupling both actual canonical chart paths read
their finite endpoints at the original terminal physical time. No safe law,
source forward kernel, endpoint access, or stopped extension is used. -/
theorem ae_canon_terminal_physical_readings
    {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (h77 : Supp10.Lemma77Statement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    {x₁ x₂ θ₁ θ₂ : ℝ} (hx : x₂ < x₁) (hθ : θ₁ < θ₂ + Real.pi)
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁)
    (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    {d : PairData Ω} (hd : d.IsMeasGood) (hζ₁ : d.ζ₁ = ζ₁) (hζ₂ : d.ζ₂ = ζ₂)
    (hae : ∀ᵐ ω ∂P, ω ∈ d.G ∧
      (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → d.η₁ ω s = η₁ ω s) ∧
      ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₂ ω → d.η₂ ω s = η₂ ω s)
    {γ₁ γ₂ : Ω → ℝ≥0 → ℂ} {U₁ U₂ : Ω → ℝ≥0∞}
    (hcanon : d.IsCanonClock P γ₁ γ₂ U₁ U₂) :
    ∀ᵐ ω ∂P, ω ∈ meetSet d →
      (∀ T : ℝ≥0, (T : ℝ≥0∞) = U₁ ω →
        0 < T ∧ ζ₁ ω ≠ ⊤ ∧ d.inv ω (γ₁ ω T) = η₁ ω (ζ₁ ω).toNNReal) ∧
      (∀ T : ℝ≥0, (T : ℝ≥0∞) = U₂ ω →
        0 < T ∧ ζ₂ ω ≠ ⊤ ∧ d.inv ω (γ₂ ω T) = η₂ ω (ζ₂ ω).toNNReal) := by
  obtain ⟨γc₁, γc₂, Uc₁, Uc₂, -, -, -, -, -, -, hcan, hdata⟩ :=
    exists_canonClock Theorem15.aux25Statement h77 hκ hκ4 hb hx hθ hh hη₁ hη₂
      hd hζ₁ hζ₂ hae
  filter_upwards [ae_canonClock_eq hcanon hcan, hdata, hae] with ω he hdω ha hm
  obtain ⟨hE, hs, ht⟩ := mem_meetSet_iff.1 hm
  have ha₁ : ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ d.ζ₁ ω → d.η₁ ω s = η₁ ω s := by
    simpa only [hζ₁] using ha.2.1
  have ha₂ : ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ d.ζ₂ ω → d.η₂ ω s = η₂ ω s := by
    simpa only [hζ₂] using ha.2.2
  have hf := (isFirstContact_congr ha₁ ha₂).1 (hd.isFirstContact hE)
  simp only [hζ₁, hζ₂] at hf hs ht
  obtain ⟨c₁, c₂, hc₁, hi₁, hc₂, hi₂, -, -, hr₁, hr₂⟩ := hdω _ _ hf hs ht
  obtain ⟨e₁, e₂, hγ₁, hγ₂⟩ := he hm
  constructor
  · intro T hT
    have hread := terminal_reading_of_clock_image hc₁ hi₁ hr₁ hs (hT.trans e₁)
    rw [hγ₁ T hT.le]
    exact hread
  · intro T hT
    have hread := terminal_reading_of_clock_image hc₂ hi₂ hr₂ ht (hT.trans e₂)
    rw [hγ₂ T hT.le]
    exact hread

end InteractingSLE.Restart.FCPlumb
