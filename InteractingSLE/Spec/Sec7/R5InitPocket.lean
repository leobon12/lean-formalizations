/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC16Pocket
import InteractingSLE.Spec.Sec7.SideC14Select
import InteractingSLE.Spec.Sec7.R7LeavesExtremal

/-!
# R.5's initial heights, part 1: the original filled-pocket mean of the R.7 walls

Packet PROVE-R5-INIT (Astra's pocket-mean note, ruling R98, Theorem 9 and Remark 10). PROVE-SIDE-COLLAR2's general
filled-pocket theorem `SideC16.ae_eqOn_filledPocket_allAngles` asks for flow lines whose lifetime is the constant `⊤`;
the R.7 arms of `R7Outer.IsR7OuterConfig` have lifetimes that are `⊤` only almost surely. Its proof uses the lifetime
only through `SideC16.ae_rational_ownHeights_allAngles`, which already allows an almost surely infinite lifetime, so
the same proof gives the statement for such lifetimes (`ae_eqOn_filledPocket_allAngles_ae`). Its R.7 instance (the
constant-angle arms `θ_R`, `θ_L`, no angle bound, on a walls-measurable selection of change pockets; the first
original-frame fact of the note: the pocket-exterior mean equals the wall-union mean, which is the flow word) is
`R5Init.ae_eqOn_selectedChangePocket_r7` in `R5InitTest.lean`. An explicit two-valued source extension `r7FlowMean`
of the two wall heights is provided here (`isBoundedHarmonicExtension_r7FlowMean`).

Conditional helpers with distinct names; no source theorem is replaced. Ruling R48: nothing here uses
Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any result taking them as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Bornology
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec7.R5Init

open LocalSets WholeField Aux119Nested Aux119Bdry Aux119Heights Aux2728Pocket PocketCoord PocketMarks StripGeom
  Lemma71N Lemma71I

/-! ### The filled-pocket mean for almost surely infinite lifetimes -/

/-- **`SideC16.ae_eqOn_filledPocket_allAngles` for flow lines with almost surely infinite lifetimes** (same proof; the
lifetimes enter only through `SideC16.ae_rational_ownHeights_allAngles`, which allows them). -/
theorem ae_eqOn_filledPocket_allAngles_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {κ : ℝ} (hκ : 0 < κ)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {β α : Ω → ℝ≥0 → ℂ} {θL θR : ℝ} {ζL ζR : Ω → ℝ≥0∞}
    (hβ : IsFlowLine κ b jumps 0 θL P h β ζL) (hζL : ∀ᵐ ω ∂P, ζL ω = ⊤)
    (hα : IsFlowLine κ b jumps 0 θR P h α ζR) (hζR : ∀ᵐ ω ∂P, ζR ω = ⊤)
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
  have hβtrζ : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => WL ω t) (ζL ω) (fun t => β ω t - ((0 : ℝ) : ℂ)) := by
    filter_upwards [hβtr, hζL] with ω hB hz
    rw [hz]
    simpa only [Complex.ofReal_zero, sub_zero] using hB.1
  have hαtrζ : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => WR ω t) (ζR ω) (fun t => α ω t - ((0 : ℝ) : ℂ)) := by
    filter_upwards [hαtr, hζR] with ω hA hz
    rw [hz]
    simpa only [Complex.ofReal_zero, sub_zero] using hA.1
  obtain ⟨gL, hgL⟩ := StripWall.exists_isLocalSetMean_prefix hX hβc hβ0 hβm hβdet hβloc
  obtain ⟨gR, hgR⟩ := StripWall.exists_isLocalSetMean_prefix hX hαc hα0 hαm hαdet hαloc
  obtain ⟨hUm, hUloc, _⟩ := isLocalSet_wallUnion hX hβc hβ0 hβm hβdet hβloc
    hαc hα0 hαm hαdet hαloc htr
  obtain ⟨gU, hgU⟩ := IsLocalSet.exists_isLocalSetMean hX hUm hUloc
  have hsideL := SideC16.ae_rational_ownHeights_allAngles hκ hb hh hβ (W := fun t ω => WL ω t) hβtrζ hζL
    hu₀ hβc hβ0 hβm hβdet hβloc hgL
  have hsideR := SideC16.ae_rational_ownHeights_allAngles hκ hb hh hα (W := fun t ω => WR ω t) hαtrζ hζR
    hu₀ hαc hα0 hαm hαdet hαloc hgR
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

/-! ### An explicit source extension of the two constant wall heights -/

/-- **The two-valued flow-coordinate mean**: `λ − θ_L χ` on `ℝ₋`, `−λ − θ_R χ` on `ℝ₊` (the left side of the right
wall and the right side of the left wall, in a flow chart sending the left wall to `ℝ₋`). -/
def r7FlowMean (κ θR θL : ℝ) (y : ℂ) : ℝ :=
  (sleLambda κ - θL * chiC κ) +
    ((-sleLambda κ - θR * chiC κ) - (sleLambda κ - θL * chiC κ)) * Impl.jumpExt 0 y

theorem r7FlowMean_harmonic (κ θR θL : ℝ) : InnerProductSpace.HarmonicOnNhd (r7FlowMean κ θR θL) H := by
  have h := (InnerProductSpace.harmonicOnNhd_const (sleLambda κ - θL * chiC κ)).add
    (Impl.harmonicOnNhd_const_mul ((-sleLambda κ - θR * chiC κ) - (sleLambda κ - θL * chiC κ))
      (Impl.harmonicOnNhd_jumpExt 0))
  exact h

theorem abs_r7FlowMean_le (κ θR θL : ℝ) :
    ∃ M : ℝ, ∀ z ∈ H, |r7FlowMean κ θR θL z| ≤ M := by
  refine ⟨|sleLambda κ - θL * chiC κ| + |(-sleLambda κ - θR * chiC κ) - (sleLambda κ - θL * chiC κ)|,
    fun z hz => ?_⟩
  unfold r7FlowMean
  have h1 := abs_add_le (sleLambda κ - θL * chiC κ)
    (((-sleLambda κ - θR * chiC κ) - (sleLambda κ - θL * chiC κ)) * Impl.jumpExt 0 z)
  have h2 := mul_le_of_le_one_right
    (abs_nonneg ((-sleLambda κ - θR * chiC κ) - (sleLambda κ - θL * chiC κ))) (Impl.abs_jumpExt_le 0 hz)
  rw [abs_mul] at h1
  linarith

/-- The boundary values of `r7FlowMean` at every nonzero real point. -/
theorem tendsto_r7FlowMean (κ θR θL : ℝ) {t : ℝ} (ht : t ≠ 0) :
    Tendsto (r7FlowMean κ θR θL) (𝓝[H] (t : ℂ))
      (𝓝 (if t < 0 then sleLambda κ - θL * chiC κ else -sleLambda κ - θR * chiC κ)) := by
  have hj := Impl.tendsto_jumpExt (b := 0) (t := t) (Ne.symm ht)
  have hlim := (hj.const_mul ((-sleLambda κ - θR * chiC κ) - (sleLambda κ - θL * chiC κ))).const_add
    (sleLambda κ - θL * chiC κ)
  have e : (if t < 0 then sleLambda κ - θL * chiC κ else -sleLambda κ - θR * chiC κ) =
      (sleLambda κ - θL * chiC κ) + ((-sleLambda κ - θR * chiC κ) - (sleLambda κ - θL * chiC κ)) *
        (if (0 : ℝ) ≤ t then 1 else 0) := by
    rcases lt_or_gt_of_ne ht with hneg | hpos
    · simp only [hneg, ↓reduceIte, not_le.2 hneg, mul_zero, add_zero]
    · simp only [not_lt.2 hpos.le, ↓reduceIte, hpos.le, mul_one]
      ring
  rw [e]
  exact hlim

/-- **`r7FlowMean` is a bounded source extension** of the two constant wall heights in every chart. -/
theorem isBoundedHarmonicExtension_r7FlowMean (κ θR θL : ℝ) (L R : ℝ≥0 → ℂ) (c : Chart) (SL SR : Set ℝ≥0) :
    IsBoundedHarmonicExtension
      (chartData L R (fun _ => sleLambda κ - θL * chiC κ) (fun _ => -sleLambda κ - θR * chiC κ) c)
      (exSet L R SL SR c) (r7FlowMean κ θR θL) := by
  refine ⟨r7FlowMean_harmonic κ θR θL, abs_r7FlowMean_le κ θR θL, fun ξ hξ => ?_⟩
  have hξ0 : ξ ≠ 0 := fun he => hξ (he ▸ Set.mem_insert 0 _)
  have hlim := tendsto_r7FlowMean κ θR θL hξ0
  rcases lt_or_gt_of_ne hξ0 with hneg | hpos
  · simpa only [chartData, hneg, ↓reduceIte] using hlim
  · simpa only [chartData, not_lt.2 hpos.le, hpos, ↓reduceIte] using hlim

end InteractingSLE.Sec7.R5Init
