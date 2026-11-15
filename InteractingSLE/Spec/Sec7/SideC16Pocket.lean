/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC16Angles
import InteractingSLE.Spec.Sec7.SideC14Marked
import InteractingSLE.Spec.Sec7.StripWallMeanFull
import InteractingSLE.Spec.Sec7.Aux119Heights

/-! # R98: the general filled-pocket mean for constant-angle outer arms

PROVE-SIDE-COLLAR2. Canonical all-angle flow couplings supply the own
heights. The labelled-wall marked comparison and generic Aux. 119
then give the filled-pocket mean. No angle-range or counterflow-range
containment premise is imposed, and the source constant is zero.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Bornology
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.SideC16
open LocalSets WholeField Aux119Nested Aux119Bdry Aux119Heights Aux2728Pocket
  PocketCoord PocketMarks StripGeom Lemma71N Lemma71I

/-- The original filled-pocket flow formula for canonical constant-angle
walls, including outer angles. The field-determined local histories,
canonical flow couplings and selected component geometry are explicit.
The boundary heights and the filled/union mean comparison are proved. -/
theorem ae_eqOn_filledPocket_allAngles
    {Ω : Type*} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {κ : ℝ} (hκ : 0 < κ)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {β α : Ω → ℝ≥0 → ℂ} {θL θR : ℝ}
    (hβ : IsFlowLine κ b jumps 0 θL P h β (fun _ => ⊤))
    (hα : IsFlowLine κ b jumps 0 θR P h α (fun _ => ⊤))
    (hβc : ∀ ω, Continuous (β ω)) (hβ0 : ∀ ω, β ω 0 = 0)
    (hβm : ∀ t, Measurable fun ω => β ω t)
    (hβdet : ∀ t : ℝ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => β ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hβloc : Sec6.IsEntranceHistoryLocal β (centredField h u₀) P)
    (hαc : ∀ ω, Continuous (α ω)) (hα0 : ∀ ω, α ω 0 = 0)
    (hαm : ∀ t, Measurable fun ω => α ω t)
    (hαdet : ∀ t : ℝ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => α ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hαloc : Sec6.IsEntranceHistoryLocal α (centredField h u₀) P)
    (hβsp : ∀ᵐ ω ∂P, IsSimpleProper (β ω))
    (hαsp : ∀ᵐ ω ∂P, IsSimpleProper (α ω))
    {WL WR : Ω → ℝ≥0 → ℝ}
    (hβtr : ∀ᵐ ω ∂P, IsGeneratingTrace (WL ω) ⊤ (β ω) ∧ Continuous (WL ω) ∧ WL ω 0 = 0)
    (hαtr : ∀ᵐ ω ∂P, IsGeneratingTrace (WR ω) ⊤ (α ω) ∧ Continuous (WR ω) ∧ WR ω 0 = 0)
    {C : Ω → Set ℂ}
    (hCm : Measurable[PocketWordPerQ.wallsSigma P α β, hittingSigma] (fun ω => H \ C ω))
    (hCo : ∀ ω, IsOpen (C ω)) (hCs : ∀ ω, C ω ⊆ H \ wallUnion β α ω)
    (hCc : ∀ᵐ ω ∂P, ∀ z ∈ C ω, connectedComponentIn (H \ wallUnion β α ω) z ⊆ C ω)
    {gC : Ω → DistOn upperHalfPlaneOpens}
    (hgC : IsLocalSetMean (fun ω => H \ C ω) (centredField h u₀) P gC) :
    ∀ᵐ ω ∂P, ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (C ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ C ω → gC ω φ = ∫ z, v z * φ z) →
      ∀ (r : ℝ≥0) (Ψ : ℂ → ℂ) (c : Chart) (ℓ : ℂ → ℂ) (n : ℤ) (G : ℂ → ℝ),
      C ω = changePocket (α ω) (β ω) r → IsFlowChart (α ω) (β ω) r Ψ c →
      changePocket (α ω) (β ω) r ⊆ leftSideOf (range (α ω)) →
      IsDerivLog c.1 ℓ (changePocket (α ω) (β ω) r) →
      (∀ z ∈ changePocket (α ω) (β ω) r, c.2.2 z = (ℓ z).im) → IsPocketBranch (β ω) (α ω) c n →
      IsBoundedHarmonicExtension
        (chartData (β ω) (α ω) (fun _ => sleLambda κ - θL * chiC κ)
          (fun _ => -sleLambda κ - θR * chiC κ) c)
        (exSet (β ω) (α ω) {0} {0} c) G →
      ∀ z ∈ C ω, v z + u₀ z = G (c.1 z) - chiC κ * (c.2.2 z + 2 * π * n) := by
  have hX := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀
  have htr : ∀ᵐ ω ∂P, Tendsto (β ω) atTop (cobounded ℂ) ∧ Tendsto (α ω) atTop (cobounded ℂ) := by
    filter_upwards [hβsp, hαsp] with ω hB hA
    exact ⟨tendsto_norm_atTop_iff_cobounded.mp hB.2.2.2.2,
      tendsto_norm_atTop_iff_cobounded.mp hA.2.2.2.2⟩
  have hβim : ∀ᵐ ω ∂P, ∀ t, 0 ≤ (β ω t).im := by
    filter_upwards [hβsp] with ω hB t
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with ht | ht
    · rw [← ht, hβ0]; exact le_rfl
    · exact (hB.2.2.2.1 t ht).le
  have hαim : ∀ᵐ ω ∂P, ∀ t, 0 ≤ (α ω t).im := by
    filter_upwards [hαsp] with ω hA t
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with ht | ht
    · rw [← ht, hα0]; exact le_rfl
    · exact (hA.2.2.2.1 t ht).le
  obtain ⟨gL, hgL⟩ := StripWall.exists_isLocalSetMean_prefix hX hβc hβ0 hβm hβdet hβloc
  obtain ⟨gR, hgR⟩ := StripWall.exists_isLocalSetMean_prefix hX hαc hα0 hαm hαdet hαloc
  obtain ⟨hUm, hUloc, _⟩ := isLocalSet_wallUnion hX hβc hβ0 hβm hβdet hβloc
    hαc hα0 hαm hαdet hαloc htr
  obtain ⟨gU, hgU⟩ := IsLocalSet.exists_isLocalSetMean hX hUm hUloc
  have hsideL := ae_rational_ownHeights_allAngles hκ hb hh hβ
    (W := fun t ω => WL ω t) (by simpa only [Complex.ofReal_zero, sub_zero] using hβtr.mono (fun _ h => h.1))
    (ae_of_all _ fun _ => rfl) hu₀ hβc hβ0 hβm hβdet hβloc hgL
  have hsideR := ae_rational_ownHeights_allAngles hκ hb hh hα
    (W := fun t ω => WR ω t) (by simpa only [Complex.ofReal_zero, sub_zero] using hαtr.mono (fun _ h => h.1))
    (ae_of_all _ fun _ => rfl) hu₀ hαc hα0 hαm hαdet hαloc hgR
  have hsideL' : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, β ω s ∉ range (α ω) → s ∉ ({0} : Set ℝ≥0) →
      ∃ q : ℚ≥0, s < q ∧ ∀ v : ℂ → ℝ,
        InnerProductSpace.HarmonicOnNhd v (H \ (β ω '' Icc 0 (q : ℝ≥0) ∩ H)) →
        (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (β ω '' Icc 0 (q : ℝ≥0) ∩ H) →
          gL q ω φ = ∫ z, v z * φ z) → HasSideHeights κ θL (β ω) 0 (WL ω) q (β ω s) v u₀ := by
    filter_upwards [hsideL, hβsp] with ω hs hB s _ hs0
    have hp : 0 < s := pos_of_ne_zero (by simpa only [mem_singleton_iff] using hs0)
    exact hs s hp (hB.2.2.2.1 s hp)
  have hsideR' : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, α ω s ∉ range (β ω) → s ∉ ({0} : Set ℝ≥0) →
      ∃ q : ℚ≥0, s < q ∧ ∀ v : ℂ → ℝ,
        InnerProductSpace.HarmonicOnNhd v (H \ (α ω '' Icc 0 (q : ℝ≥0) ∩ H)) →
        (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (α ω '' Icc 0 (q : ℝ≥0) ∩ H) →
          gR q ω φ = ∫ z, v z * φ z) → HasSideHeights κ θR (α ω) 0 (WR ω) q (α ω s) v u₀ := by
    filter_upwards [hsideR, hαsp] with ω hs hA s _ hs0
    have hp : 0 < s := pos_of_ne_zero (by simpa only [mem_singleton_iff] using hs0)
    exact hs s hp (hA.2.2.2.1 s hp)
  have hSource := ae_eqOn_changePocket_of_sideHeights hX hβc hβ0 hβm hβdet hβloc hβim
    hαc hα0 hαm hαdet hαloc hαim htr hgU hgL hgR hu₀.1 hu₀.2.1
    (finite_singleton 0) (finite_singleton 0) hsideL' hsideR'
  have hEq := SideC14.ae_representatives_filled_eq_wallMean hX
    hβc hβ0 hβm hβdet hβloc hαc hα0 hαm hαdet hαloc htr hCm hCo hCs hCc hgU hgC
  filter_upwards [hSource, hEq, hgU.2.1, hβtr, hαtr] with ω hSrc hEqω hGU hBT hAT
    v hv hrep r Ψ c ℓ n G hC hF hleft hℓ hlift hn hG z hz
  obtain ⟨vU, hrepU⟩ := harmRep_spec hGU
  rw [hEqω v _ hv hrep vU hrepU hz]
  exact hSrc _ vU hrepU r Ψ c ℓ n G hF hleft hℓ hlift hn
    hBT.1 hBT.2.1 hBT.2.2 hAT.1 hAT.2.1 hAT.2.2 hG z (hC ▸ hz)

end InteractingSLE.Sec7.SideC16
