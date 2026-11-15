/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.StripWallLocal
import InteractingSLE.Spec.Supplement.StagedRegularize
import InteractingSLE.Spec.Sec7.StripHeights44

/-!
# Aux. lemma 119's change-pocket mean for the strip walls with the walls' Lemma 6.2 inputs discharged

Packet PROVE-STRIPSYS29. Specification §7.4, Aux. lemma 119 and its proof (`source/spec/p385-432.md` L3–L54,
pp. 385–387) for the walls `L = β^{(q)} = η^{q,∞}_{π/2,θ₂}` and `R = α = η^{1,∞}_{−π/2,θ₁}` of (RS13.1), with Aux. lemma
130's height choice (pp. 408–410) and its rational change time `q > 0` (p. 411).

PROVE-STRIPSYS28's `StripWall.ae_eqOn_changePocket_strip_of_trace` assumed the walls' entrance-history locality,
the local-set means of their prefixes and the regularity of the drivers at every sample. Here:

* **`lemma62_walls`**: Lemma 6.2's inputs for every version of either wall — field determination (PROVE-STRIPSYS21/27),
  entrance-history locality (`StripWall.isEntranceHistoryLocal_alpha`, `…_beta`, `Spec/Sec7/StripWallLocal`) and
  transience (PROVE-STRIPSYS28);
* **`exists_isLocalSetMean_prefix`**: the prefix local-set means exist (Lemma 6.2's local set
  `StripMark.isLocalSet_range`, then Lemma 3.6's mean `IsLocalSet.exists_isLocalSetMean`);
  **`exists_isLocalSetMean_wallUnion_strip`**: the mean of the walls' union exists
  (`Aux119Nested.isLocalSet_wallUnion`);
* **`ae_eqOn_changePocket_strip_loc`**: the change-pocket mean for any versions `β`, `α` of the walls and any version
  `gU` of the local-set mean of their union; the remaining hypotheses are the source's (strip system, heights, angles,
  rational change time) and the regularity of the two staged histories' drivers at every sample;
* **`ae_eqOn_changePocket_strip_reg`**: the same with that regularity replaced by the frozen almost-sure regularity
  `StagedPiecesRegular` of the two programs (ruling R51: the source's pieces are continuous curves; pathwise
  regularity at every sample cannot be read off the conditional laws). The staged histories are regularized
  (`Theorem14.StagedReg.regHist`, family `regStrip`), which changes neither the strip system (`isStripSystem_regStrip`)
  nor, almost surely, the concatenated drivers (`ae_catPath_regHist_eq`), so the walls' versions are unchanged
  (`regStrip_walls`); `exists_isLocalSetMean_wallUnion_strip_reg` likewise;
* **`ae_eqOn_changePocket_strip_aux130`**: the same with the cumulative height bounds supplied by Aux. lemma 130's
  chosen four-height half-plane word (`StripHeights44.IsAux130HalfPlaneWord`, ruling R56; `cum_of_aux130`).

No Theorem 1.2/1.3 (R43, R48); the only named input is `AdmCode.Theorem12ParamCond44Statement`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Function
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE

namespace Sec7

namespace StripWall

open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)
open StripSideHeightProb
open Exist.Staged (IsRegularDriver)
open Lemma71N (IsPocketBranch)
open PocketCoord PocketMarks Aux119Bdry LocalSets StripGeom Aux119Nested Aux2728Pocket

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}

omit [StandardBorelSpace Ω] in
/-- **The prefix local-set means of a field-determined, entrance-history local path exist** (Lemma 6.2's local set at
every deterministic time, then Lemma 3.6's conditional mean). -/
theorem exists_isLocalSetMean_prefix {X : Ω → DistOn upperHalfPlaneOpens}
    (hX : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens X P) {γ : Ω → ℝ≥0 → ℂ} (hγc : ∀ ω, Continuous (γ ω))
    (hγ0 : ∀ ω, γ ω 0 = 0) (hγm : ∀ t, Measurable fun ω => γ ω t)
    (hdet : ∀ t : ℝ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => γ ω t) =ᵐ[P] fun ω => f (X ω))
    (hloc : Sec6.IsEntranceHistoryLocal γ X P) :
    ∃ g : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens, ∀ q : ℝ≥0,
      IsLocalSetMean (fun ω => γ ω '' Icc 0 q ∩ H) X P (g q) := by
  have hex : ∀ q : ℝ≥0, ∃ g, IsLocalSetMean (fun ω => γ ω '' Icc 0 q ∩ H) X P g := fun q =>
    IsLocalSet.exists_isLocalSetMean hX (StripMark.measurable_range hγc hγm q)
      (StripMark.isLocalSet_range hX hγc hγ0 hγm hdet hloc q)
  choose g hg using hex
  exact ⟨g, hg⟩

/-- **Lemma 6.2's inputs for both strip walls** (spec pp. 410–411): every version `β` of the wall `β^{(q)}` (rational
`q > 0`) and every version `α` of the wall `α` is field determined at fixed times (PROVE-STRIPSYS21/27) and
entrance-history local (`isEntranceHistoryLocal_beta`, `isEntranceHistoryLocal_alpha`) for the centred field, and both
are almost surely transient (PROVE-STRIPSYS28). -/
theorem lemma62_walls (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hS : StripSys.IsStripSystem κ b jumps P h W' ζ' E)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ₁ θ₂ : ℝ} (hθ₁ : θ₁ ∈ Icc (-(π / 2)) (π / 2)) (hθ₂ : θ₂ ∈ Icc (-(π / 2)) (π / 2)) {q : ℚ≥0} (hq : 0 < q)
    (hregα : ∀ j ω, IsRegularDriver (E (StripSys.alphaSpec θ₁) j ω))
    (hregβ : ∀ j ω, IsRegularDriver (E (StripSys.betaSpec (q : ℝ≥0) θ₂) j ω))
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {β α : Ω → ℝ≥0 → ℂ} (hβc : ∀ ω, Continuous (β ω)) (hβ0 : ∀ ω, β ω 0 = 0)
    (hβm : ∀ t, Measurable fun ω => β ω t)
    (hβtr : ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (E (StripSys.betaSpec (q : ℝ≥0) θ₂) 0 ω).1 (q : ℝ≥0)
      (E (StripSys.betaSpec (q : ℝ≥0) θ₂) 1 ω).1) ⊤ (β ω))
    (hαc : ∀ ω, Continuous (α ω)) (hα0 : ∀ ω, α ω 0 = 0) (hαm : ∀ t, Measurable fun ω => α ω t)
    (hαtr : ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (E (StripSys.alphaSpec θ₁) 0 ω).1 1
      (E (StripSys.alphaSpec θ₁) 1 ω).1) ⊤ (α ω)) :
    (∀ t : ℝ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => β ω t) =ᵐ[P] fun ω => f (WholeField.centredField h u₀ ω)) ∧
    Sec6.IsEntranceHistoryLocal β (WholeField.centredField h u₀) P ∧
    (∀ t : ℝ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => α ω t) =ᵐ[P] fun ω => f (WholeField.centredField h u₀ ω)) ∧
    Sec6.IsEntranceHistoryLocal α (WholeField.centredField h u₀) P ∧
    ∀ᵐ ω ∂P, Tendsto (β ω) atTop (Bornology.cobounded ℂ) ∧ Tendsto (α ω) atTop (Bornology.cobounded ℂ) := by
  have hκ := hS.kappa_pos
  have hκ4 := hS.kappa_lt_four
  have hb := hS.boundaryData
  have hh := hS.gff
  have hπχ : 0 ≤ π * chiC κ := mul_nonneg Real.pi_pos.le (Sec4.chiC_pos hκ hκ4).le
  have hL44 : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps →
      b y + a * chiC κ ≤ -sleLambda κ + π * chiC κ := fun a ha y hy hyJ => by
    have := hcumL a ha y hy hyJ
    linarith
  have hm := StripSys.neg_pi_div_two_mem_Icc
  have hp := StripSys.pi_div_two_mem_Icc
  have hDα : IsDetTwoPiece P h (E (StripSys.alphaSpec θ₁)) :=
    isDetTwoPiece_of_heights h44 hκ hκ4 hb hh (hS.isStagedHistory_alpha hθ₁) hregα (hL44 _ hm) (hcumR _ hm)
      (hL44 _ hθ₁) (hcumR _ hθ₁) hθ₁.1 (by linarith [hθ₁.2])
  have hDβ : IsDetTwoPiece P h (E (StripSys.betaSpec (q : ℝ≥0) θ₂)) :=
    isDetTwoPiece_of_heights_refl h44 hκ hκ4 hb hh (hS.isStagedHistory_beta hθ₂ (q : ℝ≥0)) hregβ (hL44 _ hp)
      (hcumR _ hp) (hcumL _ hθ₂) (fun y hy hyJ => by have := hcumR _ hθ₂ y hy hyJ; linarith) hθ₂.2
      (by linarith [hθ₂.1])
  have htrβ := (isWallVersion_beta hS hcumL hcumR hθ₂ (q : ℝ≥0) hregβ hβc hβ0 hβm hβtr).ae_trace
  have htrα := (isWallVersion_alpha hS hcumL hcumR hθ₁ hregα hαc hα0 hαm hαtr).ae_trace
  refine ⟨hDβ.hdet hregβ u₀ hβtr, isEntranceHistoryLocal_beta h44 hS hcumL hcumR hθ₂ hq hregβ hu₀ hβc hβ0 hβm hβtr,
    hDα.hdet hregα u₀ hαtr, isEntranceHistoryLocal_alpha h44 hS hcumL hcumR hθ₁ hregα hu₀ hαc hα0 hαm hαtr, ?_⟩
  filter_upwards [htrβ, htrα] with ω h1 h2
  exact ⟨h1.2.2.2, h2.2.2.2⟩

/-- **The local-set mean of the strip walls' union exists** (Lemma 6.2 for the complete union,
`Aux119Nested.isLocalSet_wallUnion`, then Lemma 3.6's mean). -/
theorem exists_isLocalSetMean_wallUnion_strip (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hS : StripSys.IsStripSystem κ b jumps P h W' ζ' E)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ₁ θ₂ : ℝ} (hθ₁ : θ₁ ∈ Icc (-(π / 2)) (π / 2)) (hθ₂ : θ₂ ∈ Icc (-(π / 2)) (π / 2)) {q : ℚ≥0} (hq : 0 < q)
    (hregα : ∀ j ω, IsRegularDriver (E (StripSys.alphaSpec θ₁) j ω))
    (hregβ : ∀ j ω, IsRegularDriver (E (StripSys.betaSpec (q : ℝ≥0) θ₂) j ω))
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {β α : Ω → ℝ≥0 → ℂ} (hβc : ∀ ω, Continuous (β ω)) (hβ0 : ∀ ω, β ω 0 = 0)
    (hβm : ∀ t, Measurable fun ω => β ω t)
    (hβtr : ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (E (StripSys.betaSpec (q : ℝ≥0) θ₂) 0 ω).1 (q : ℝ≥0)
      (E (StripSys.betaSpec (q : ℝ≥0) θ₂) 1 ω).1) ⊤ (β ω))
    (hαc : ∀ ω, Continuous (α ω)) (hα0 : ∀ ω, α ω 0 = 0) (hαm : ∀ t, Measurable fun ω => α ω t)
    (hαtr : ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (E (StripSys.alphaSpec θ₁) 0 ω).1 1
      (E (StripSys.alphaSpec θ₁) 1 ω).1) ⊤ (α ω)) :
    ∃ gU : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean (wallUnion β α) (WholeField.centredField h u₀) P gU := by
  have hX := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hS.gff hu₀
  obtain ⟨hdβ, hlβ, hdα, hlα, htr⟩ := lemma62_walls h44 hS hcumL hcumR hθ₁ hθ₂ hq hregα hregβ hu₀ hβc hβ0 hβm hβtr
    hαc hα0 hαm hαtr
  obtain ⟨hUm, hUloc, -⟩ := isLocalSet_wallUnion hX hβc hβ0 hβm hdβ hlβ hαc hα0 hαm hdα hlα htr
  exact IsLocalSet.exists_isLocalSetMean hX hUm hUloc

/-- **Aux. lemma 119's conditional mean in the change pocket of the strip walls, with the walls' locality and prefix
means discharged** (spec pp. 385–387, 408–411). For a strip system with Aux. lemma 130's heights, angles
`θ₁, θ₂ ∈ [−π/2, π/2]`, a rational change time `q > 0`, versions `β`, `α` of the traces of the walls
`β^{(q)} = η^{q,∞}_{π/2,θ₂}` and `α = η^{1,∞}_{−π/2,θ₁}` (continuous, starting at `0`, measurable at fixed times, almost
surely generating the concatenated chain on `[0, ∞)`) and any version `gU` of the local-set mean of their union:
almost surely, for every harmonic representative `v` of `gU` and every flow chart `c` of a change pocket on the left of
`α` with the common lift's integer `n`, on the pocket `v + u₀` is the bounded Poisson extension `G` of the two-angle
heights pulled back by `c`, minus `χ (arg c′ + 2πn)`. The drivers of the two staged histories are assumed regular at
every sample (as in PROVE-STRIPSYS21–28). -/
theorem ae_eqOn_changePocket_strip_loc (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hS : StripSys.IsStripSystem κ b jumps P h W' ζ' E)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ₁ θ₂ : ℝ} (hθ₁ : θ₁ ∈ Icc (-(π / 2)) (π / 2)) (hθ₂ : θ₂ ∈ Icc (-(π / 2)) (π / 2)) {q : ℚ≥0} (hq : 0 < q)
    (hregα : ∀ j ω, IsRegularDriver (E (StripSys.alphaSpec θ₁) j ω))
    (hregβ : ∀ j ω, IsRegularDriver (E (StripSys.betaSpec (q : ℝ≥0) θ₂) j ω))
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {β α : Ω → ℝ≥0 → ℂ} (hβc : ∀ ω, Continuous (β ω)) (hβ0 : ∀ ω, β ω 0 = 0)
    (hβm : ∀ t, Measurable fun ω => β ω t)
    (hβtr : ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (E (StripSys.betaSpec (q : ℝ≥0) θ₂) 0 ω).1 (q : ℝ≥0)
      (E (StripSys.betaSpec (q : ℝ≥0) θ₂) 1 ω).1) ⊤ (β ω))
    (hαc : ∀ ω, Continuous (α ω)) (hα0 : ∀ ω, α ω 0 = 0) (hαm : ∀ t, Measurable fun ω => α ω t)
    (hαtr : ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (E (StripSys.alphaSpec θ₁) 0 ω).1 1
      (E (StripSys.alphaSpec θ₁) 1 ω).1) ⊤ (α ω))
    {gU : Ω → DistOn upperHalfPlaneOpens}
    (hgU : IsLocalSetMean (wallUnion β α) (WholeField.centredField h u₀) P gU) :
    ∀ᵐ ω ∂P, ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ wallUnion β α ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ wallUnion β α ω → gU ω φ = ∫ z, v z * φ z) →
      ∀ (r' : ℝ≥0) (Ψ : ℂ → ℂ) (c : Chart) (ℓ : ℂ → ℂ) (n : ℤ) (G : ℂ → ℝ),
      IsFlowChart (α ω) (β ω) r' Ψ c → changePocket (α ω) (β ω) r' ⊆ leftSideOf (range (α ω)) →
      IsDerivLog c.1 ℓ (changePocket (α ω) (β ω) r') →
      (∀ z ∈ changePocket (α ω) (β ω) r', c.2.2 z = (ℓ z).im) → IsPocketBranch (β ω) (α ω) c n →
      IsBoundedHarmonicExtension
        (chartData (β ω) (α ω) (fun s => sleLambda κ - (if s < (q : ℝ≥0) then π / 2 else θ₂) * chiC κ)
          (fun s => -sleLambda κ - (if s < 1 then -(π / 2) else θ₁) * chiC κ) c)
        (exSet (β ω) (α ω) {(q : ℝ≥0)} {1} c) G →
      ∀ z ∈ changePocket (α ω) (β ω) r', v z + u₀ z = G (c.1 z) - chiC κ * (c.2.2 z + 2 * π * n) := by
  have hX := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hS.gff hu₀
  obtain ⟨hdβ, hlocβ, hdα, hlocα, -⟩ := lemma62_walls h44 hS hcumL hcumR hθ₁ hθ₂ hq hregα hregβ hu₀ hβc hβ0 hβm
    hβtr hαc hα0 hαm hαtr
  obtain ⟨gL, hgL⟩ := exists_isLocalSetMean_prefix hX hβc hβ0 hβm hdβ hlocβ
  obtain ⟨gR, hgR⟩ := exists_isLocalSetMean_prefix hX hαc hα0 hαm hdα hlocα
  exact ae_eqOn_changePocket_strip_of_trace h44 hS hcumL hcumR hθ₁ hθ₂ (q : ℝ≥0) hregα hregβ hu₀ hβc hβ0 hβm hβtr
    hlocβ hαc hα0 hαm hαtr hlocα hgU hgL hgR

/-! ### Regularization of the two staged histories (ruling R51) -/

section Reg

open Theorem14.StagedReg

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
/-- **The regularized two-angle history has, almost surely, the same concatenated driver** when the pieces are almost
surely regular (`StagedPiecesRegular`) and live forever: the first piece is regularized for its own time `t₀` and agrees
with the driver on `[0, t₀]`; the continuation is regularized for `∞` and agrees everywhere. -/
theorem ae_catPath_regHist_eq {θ₀ θ : ℝ} {t₀ : ℝ≥0} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hR : StagedPiecesRegular κ b jumps P (StripSys.twoAngleSpec θ₀ t₀ θ) E)
    (hζ : ∀ᵐ ω ∂P, (E 0 ω).2 = ⊤ ∧ (E 1 ω).2 = ⊤) :
    ∀ᵐ ω ∂P, catPath (regHist (StripSys.twoAngleSpec θ₀ t₀ θ) E 0 ω).1 t₀
      (regHist (StripSys.twoAngleSpec θ₀ t₀ θ) E 1 ω).1 = catPath (E 0 ω).1 t₀ (E 1 ω).1 := by
  unfold StagedPiecesRegular at hR
  filter_upwards [hR, hζ] with ω hω hz
  have h0 : (t₀ : ℝ≥0∞) < (E 0 ω).2 := by rw [hz.1]; exact ENNReal.coe_lt_top
  obtain ⟨⟨c₀, θa⟩, hl0⟩ := Option.ne_none_iff_exists'.1
    (StripDet.launch_zero (κ := κ) (b := b) (jumps := jumps) (θ₀ := θ₀) (t₀ := t₀) (θ := θ) (fun j => E j ω))
  have hθa : θa = θ₀ := Exist.Staged.angle_of_launch _ _ hl0
  obtain ⟨⟨c₁, θb⟩, hl1⟩ := Option.ne_none_iff_exists'.1
    (StripDet.launch_one_of_lt (κ := κ) (b := b) (jumps := jumps) (θ₀ := θ₀) (θ := θ) (D := fun j => E j ω) h0)
  have hθb : θb = θ := Exist.Staged.angle_of_launch _ _ hl1
  subst hθa hθb
  obtain ⟨hz0, hc0, -⟩ := hω 0 _ (t₀ : ℝ≥0∞) c₀ rfl hl0
  obtain ⟨hz1, hc1, -⟩ := hω 1 _ ⊤ c₁ rfl hl1
  have e0 : ∀ x : ℝ≥0, x ≤ t₀ → (regHist (StripSys.twoAngleSpec θa t₀ θb) E 0 ω).1 x = (E 0 ω).1 x :=
    fun x hx => regularize_eq_of_le (t := (t₀ : ℝ≥0∞)) hz0 hc0
      (by rw [hz.1, min_eq_left le_top]; exact ENNReal.coe_le_coe.2 hx)
  have e1 : ∀ x : ℝ≥0, (regHist (StripSys.twoAngleSpec θa t₀ θb) E 1 ω).1 x = (E 1 ω).1 x :=
    fun x => regularize_eq_of_le (t := ⊤) hz1 hc1 (by rw [hz.2, min_self]; exact le_top)
  funext s
  unfold catPath
  split_ifs with hs
  · exact e0 s hs
  · rw [e0 t₀ le_rfl, e1]

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
open Classical in
/-- **The regularized family**: every staged history that is `StagedPiecesRegular` is replaced by its regularization
(`Theorem14.StagedReg.regHist`), the others are kept. -/
def regStrip (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (P : Measure Ω) (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) :
    ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞ :=
  fun spec => if StagedPiecesRegular κ b jumps P spec (E spec) then regHist spec (E spec) else E spec

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
theorem regStrip_of {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {spec : ExplSpec}
    (hR : StagedPiecesRegular κ b jumps P spec (E spec)) : regStrip κ b jumps P E spec = regHist spec (E spec) := by
  classical
  simp only [regStrip, hR, ↓reduceIte]

/-- **The regularized family is again a strip system.** -/
theorem isStripSystem_regStrip {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hS : StripSys.IsStripSystem κ b jumps P h W' ζ' E) :
    StripSys.IsStripSystem κ b jumps P h W' ζ' (regStrip κ b jumps P E) := by
  classical
  refine ⟨hS.kappa_pos, hS.kappa_lt_four, hS.boundaryData, hS.gff, hS.counterflow, hS.lifetime, fun spec hs => ?_⟩
  by_cases hR : StagedPiecesRegular κ b jumps P spec (E spec)
  · rw [regStrip_of hR]
    exact isStagedHistory_regHist hS.boundaryData (hS.staged spec hs) hR
  · simp only [regStrip, hR, ↓reduceIte]
    exact hS.staged spec hs

/-- **The regularized strip family keeps the walls** (ruling R51): under `StagedPiecesRegular` for the two programs,
`regStrip` is a strip system whose two staged histories are regular at every sample, and every version of a wall of
the original family is a version of the corresponding wall of the regularized family. -/
theorem regStrip_walls
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hS : StripSys.IsStripSystem κ b jumps P h W' ζ' E)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ₁ θ₂ : ℝ} (hθ₁ : θ₁ ∈ Icc (-(π / 2)) (π / 2)) (hθ₂ : θ₂ ∈ Icc (-(π / 2)) (π / 2)) (q : ℝ≥0)
    (hRα : StagedPiecesRegular κ b jumps P (StripSys.alphaSpec θ₁) (E (StripSys.alphaSpec θ₁)))
    (hRβ : StagedPiecesRegular κ b jumps P (StripSys.betaSpec q θ₂) (E (StripSys.betaSpec q θ₂)))
    {β α : Ω → ℝ≥0 → ℂ}
    (hβtr : ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (E (StripSys.betaSpec q θ₂) 0 ω).1 q
      (E (StripSys.betaSpec q θ₂) 1 ω).1) ⊤ (β ω))
    (hαtr : ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (E (StripSys.alphaSpec θ₁) 0 ω).1 1
      (E (StripSys.alphaSpec θ₁) 1 ω).1) ⊤ (α ω)) :
    StripSys.IsStripSystem κ b jumps P h W' ζ' (regStrip κ b jumps P E) ∧
      (∀ j ω, IsRegularDriver (regStrip κ b jumps P E (StripSys.alphaSpec θ₁) j ω)) ∧
      (∀ j ω, IsRegularDriver (regStrip κ b jumps P E (StripSys.betaSpec q θ₂) j ω)) ∧
      (∀ᵐ ω ∂P, IsGeneratingTrace (catPath (regStrip κ b jumps P E (StripSys.betaSpec q θ₂) 0 ω).1 q
        (regStrip κ b jumps P E (StripSys.betaSpec q θ₂) 1 ω).1) ⊤ (β ω)) ∧
      ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (regStrip κ b jumps P E (StripSys.alphaSpec θ₁) 0 ω).1 1
        (regStrip κ b jumps P E (StripSys.alphaSpec θ₁) 1 ω).1) ⊤ (α ω) := by
  have hS' := isStripSystem_regStrip hS
  have eα := regStrip_of hRα
  have eβ := regStrip_of hRβ
  have hregα : ∀ j ω, IsRegularDriver (regStrip κ b jumps P E (StripSys.alphaSpec θ₁) j ω) := fun j ω => by
    rw [eα]; exact isRegularDriver_regHist j ω
  have hregβ : ∀ j ω, IsRegularDriver (regStrip κ b jumps P E (StripSys.betaSpec q θ₂) j ω) := fun j ω => by
    rw [eβ]; exact isRegularDriver_regHist j ω
  have hζα : ∀ᵐ ω ∂P, (E (StripSys.alphaSpec θ₁) 0 ω).2 = ⊤ ∧ (E (StripSys.alphaSpec θ₁) 1 ω).2 = ⊤ := by
    filter_upwards [ae_simple_trace_alpha hS' hcumL hcumR hθ₁ hregα] with ω hω
    rw [eα, regHist_snd, regHist_snd] at hω
    exact hω.1
  have hζβ : ∀ᵐ ω ∂P, (E (StripSys.betaSpec q θ₂) 0 ω).2 = ⊤ ∧ (E (StripSys.betaSpec q θ₂) 1 ω).2 = ⊤ := by
    filter_upwards [ae_simple_trace_beta hS' hcumL hcumR hθ₂ q hregβ] with ω hω
    rw [eβ, regHist_snd, regHist_snd] at hω
    exact hω.1
  refine ⟨hS', hregα, hregβ, ?_, ?_⟩
  · rw [eβ]
    filter_upwards [hβtr, ae_catPath_regHist_eq (θ₀ := π / 2) (t₀ := q) (θ := θ₂) hRβ hζβ] with ω h1 h2
    rw [StripSys.betaSpec] at h2 ⊢
    rw [h2]
    exact h1
  · rw [eα]
    filter_upwards [hαtr, ae_catPath_regHist_eq (θ₀ := -(π / 2)) (t₀ := 1) (θ := θ₁) hRα hζα] with ω h1 h2
    rw [StripSys.alphaSpec] at h2 ⊢
    rw [h2]
    exact h1

/-- **The local-set mean of the strip walls' union exists** under the almost-sure regularity of the pieces (R51). -/
theorem exists_isLocalSetMean_wallUnion_strip_reg (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hS : StripSys.IsStripSystem κ b jumps P h W' ζ' E)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ₁ θ₂ : ℝ} (hθ₁ : θ₁ ∈ Icc (-(π / 2)) (π / 2)) (hθ₂ : θ₂ ∈ Icc (-(π / 2)) (π / 2)) {q : ℚ≥0} (hq : 0 < q)
    (hRα : StagedPiecesRegular κ b jumps P (StripSys.alphaSpec θ₁) (E (StripSys.alphaSpec θ₁)))
    (hRβ : StagedPiecesRegular κ b jumps P (StripSys.betaSpec (q : ℝ≥0) θ₂) (E (StripSys.betaSpec (q : ℝ≥0) θ₂)))
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {β α : Ω → ℝ≥0 → ℂ} (hβc : ∀ ω, Continuous (β ω)) (hβ0 : ∀ ω, β ω 0 = 0)
    (hβm : ∀ t, Measurable fun ω => β ω t)
    (hβtr : ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (E (StripSys.betaSpec (q : ℝ≥0) θ₂) 0 ω).1 (q : ℝ≥0)
      (E (StripSys.betaSpec (q : ℝ≥0) θ₂) 1 ω).1) ⊤ (β ω))
    (hαc : ∀ ω, Continuous (α ω)) (hα0 : ∀ ω, α ω 0 = 0) (hαm : ∀ t, Measurable fun ω => α ω t)
    (hαtr : ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (E (StripSys.alphaSpec θ₁) 0 ω).1 1
      (E (StripSys.alphaSpec θ₁) 1 ω).1) ⊤ (α ω)) :
    ∃ gU : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean (wallUnion β α) (WholeField.centredField h u₀) P gU := by
  obtain ⟨hS', hregα, hregβ, hβtr', hαtr'⟩ := regStrip_walls hS hcumL hcumR hθ₁ hθ₂ (q : ℝ≥0) hRα hRβ hβtr hαtr
  exact exists_isLocalSetMean_wallUnion_strip h44 hS' hcumL hcumR hθ₁ hθ₂ hq hregα hregβ hu₀ hβc hβ0 hβm hβtr' hαc
    hα0 hαm hαtr'

/-- **Aux. lemma 119's conditional mean in the change pocket of the strip walls under the almost-sure regularity of the
pieces** (spec pp. 385–387, 408–411; ruling R51). `ae_eqOn_changePocket_strip_loc` with the regularity of the drivers at
every sample replaced by the frozen `StagedPiecesRegular` of the two programs `α = η^{1,∞}_{−π/2,θ₁}` and
`β^{(q)} = η^{q,∞}_{π/2,θ₂}`: the remaining hypotheses are the source's (strip system, Aux. lemma 130's heights, angles,
rational change time `q > 0`), the versions `β`, `α` of the walls and a version `gU` of the local-set mean of their
union. -/
theorem ae_eqOn_changePocket_strip_reg (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hS : StripSys.IsStripSystem κ b jumps P h W' ζ' E)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ₁ θ₂ : ℝ} (hθ₁ : θ₁ ∈ Icc (-(π / 2)) (π / 2)) (hθ₂ : θ₂ ∈ Icc (-(π / 2)) (π / 2)) {q : ℚ≥0} (hq : 0 < q)
    (hRα : StagedPiecesRegular κ b jumps P (StripSys.alphaSpec θ₁) (E (StripSys.alphaSpec θ₁)))
    (hRβ : StagedPiecesRegular κ b jumps P (StripSys.betaSpec (q : ℝ≥0) θ₂) (E (StripSys.betaSpec (q : ℝ≥0) θ₂)))
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {β α : Ω → ℝ≥0 → ℂ} (hβc : ∀ ω, Continuous (β ω)) (hβ0 : ∀ ω, β ω 0 = 0)
    (hβm : ∀ t, Measurable fun ω => β ω t)
    (hβtr : ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (E (StripSys.betaSpec (q : ℝ≥0) θ₂) 0 ω).1 (q : ℝ≥0)
      (E (StripSys.betaSpec (q : ℝ≥0) θ₂) 1 ω).1) ⊤ (β ω))
    (hαc : ∀ ω, Continuous (α ω)) (hα0 : ∀ ω, α ω 0 = 0) (hαm : ∀ t, Measurable fun ω => α ω t)
    (hαtr : ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (E (StripSys.alphaSpec θ₁) 0 ω).1 1
      (E (StripSys.alphaSpec θ₁) 1 ω).1) ⊤ (α ω))
    {gU : Ω → DistOn upperHalfPlaneOpens}
    (hgU : IsLocalSetMean (wallUnion β α) (WholeField.centredField h u₀) P gU) :
    ∀ᵐ ω ∂P, ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ wallUnion β α ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ wallUnion β α ω → gU ω φ = ∫ z, v z * φ z) →
      ∀ (r' : ℝ≥0) (Ψ : ℂ → ℂ) (c : Chart) (ℓ : ℂ → ℂ) (n : ℤ) (G : ℂ → ℝ),
      IsFlowChart (α ω) (β ω) r' Ψ c → changePocket (α ω) (β ω) r' ⊆ leftSideOf (range (α ω)) →
      IsDerivLog c.1 ℓ (changePocket (α ω) (β ω) r') →
      (∀ z ∈ changePocket (α ω) (β ω) r', c.2.2 z = (ℓ z).im) → IsPocketBranch (β ω) (α ω) c n →
      IsBoundedHarmonicExtension
        (chartData (β ω) (α ω) (fun s => sleLambda κ - (if s < (q : ℝ≥0) then π / 2 else θ₂) * chiC κ)
          (fun s => -sleLambda κ - (if s < 1 then -(π / 2) else θ₁) * chiC κ) c)
        (exSet (β ω) (α ω) {(q : ℝ≥0)} {1} c) G →
      ∀ z ∈ changePocket (α ω) (β ω) r', v z + u₀ z = G (c.1 z) - chiC κ * (c.2.2 z + 2 * π * n) := by
  obtain ⟨hS', hregα, hregβ, hβtr', hαtr'⟩ := regStrip_walls hS hcumL hcumR hθ₁ hθ₂ (q : ℝ≥0) hRα hRβ hβtr hαtr
  exact ae_eqOn_changePocket_strip_loc h44 hS' hcumL hcumR hθ₁ hθ₂ hq hregα hregβ hu₀ hβc hβ0 hβm hβtr' hαc hα0 hαm
    hαtr' hgU

end Reg

/-! ### Aux. lemma 130's chosen heights (ruling R56) -/

section Aux130

open StripHeights44

omit [StandardBorelSpace Ω] in
/-- **Aux. lemma 130's chosen heights give the cumulative bounds at every angle** (p. 410: the four heights
`a, b ≥ λ + πχ/2`, `a', b' ≥ λ + 3πχ/2`): for the half-plane word with values `−a, −a'` left and `b, b'` right of `0`,
`B + θχ ≤ −λ` left and `B + θχ ≥ λ` right for every `θ ∈ [−π/2, π/2]` (the forms `hcumL`, `hcumR`). -/
theorem cum_of_aux130 {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (Hs : Aux130SourceHeights κ) {B : ℝ → ℝ}
    {jumps : Finset ℝ} (hword : IsAux130HalfPlaneWord Hs B jumps) :
    (∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → B y + a * chiC κ ≤ -sleLambda κ) ∧
      ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ B y + a * chiC κ := by
  have hχ := Sec4.chiC_pos hκ hκ4
  have hπχ : 0 ≤ π * chiC κ := mul_nonneg Real.pi_pos.le hχ.le
  refine ⟨fun a ha y hy hyJ => ?_, fun a ha y hy hyJ => ?_⟩
  · have hhi : a * chiC κ ≤ (π / 2) * chiC κ := mul_le_mul_of_nonneg_right ha.2 hχ.le
    rcases hword.1 y hy hyJ with e | e
    · rw [e]; linarith [Hs.a_lower]
    · rw [e]; linarith [Hs.aUpper_lower]
  · have hlo : -(π / 2) * chiC κ ≤ a * chiC κ := mul_le_mul_of_nonneg_right ha.1 hχ.le
    rcases hword.2 y hy hyJ with e | e
    · rw [e]; linarith [Hs.b_lower]
    · rw [e]; linarith [Hs.bUpper_lower]

/-- **Aux. lemma 119's change-pocket mean for the strip walls with Aux. lemma 130's chosen heights** (spec pp. 385–387,
408–411; rulings R51, R56): `ae_eqOn_changePocket_strip_reg` with the cumulative bounds supplied by the source's
four-height half-plane word. The hypotheses are the strip system, the source heights, the angles, the rational change
time `q > 0`, the almost-sure regularity of the two programs' pieces, the versions of the walls and a version `gU` of
the local-set mean of their union (one exists: `exists_isLocalSetMean_wallUnion_strip_reg`). -/
theorem ae_eqOn_changePocket_strip_aux130 (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hS : StripSys.IsStripSystem κ b jumps P h W' ζ' E) (Hs : Aux130SourceHeights κ)
    (hword : IsAux130HalfPlaneWord Hs b jumps)
    {θ₁ θ₂ : ℝ} (hθ₁ : θ₁ ∈ Icc (-(π / 2)) (π / 2)) (hθ₂ : θ₂ ∈ Icc (-(π / 2)) (π / 2)) {q : ℚ≥0} (hq : 0 < q)
    (hRα : StagedPiecesRegular κ b jumps P (StripSys.alphaSpec θ₁) (E (StripSys.alphaSpec θ₁)))
    (hRβ : StagedPiecesRegular κ b jumps P (StripSys.betaSpec (q : ℝ≥0) θ₂) (E (StripSys.betaSpec (q : ℝ≥0) θ₂)))
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {β α : Ω → ℝ≥0 → ℂ} (hβc : ∀ ω, Continuous (β ω)) (hβ0 : ∀ ω, β ω 0 = 0)
    (hβm : ∀ t, Measurable fun ω => β ω t)
    (hβtr : ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (E (StripSys.betaSpec (q : ℝ≥0) θ₂) 0 ω).1 (q : ℝ≥0)
      (E (StripSys.betaSpec (q : ℝ≥0) θ₂) 1 ω).1) ⊤ (β ω))
    (hαc : ∀ ω, Continuous (α ω)) (hα0 : ∀ ω, α ω 0 = 0) (hαm : ∀ t, Measurable fun ω => α ω t)
    (hαtr : ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (E (StripSys.alphaSpec θ₁) 0 ω).1 1
      (E (StripSys.alphaSpec θ₁) 1 ω).1) ⊤ (α ω))
    {gU : Ω → DistOn upperHalfPlaneOpens}
    (hgU : IsLocalSetMean (wallUnion β α) (WholeField.centredField h u₀) P gU) :
    ∀ᵐ ω ∂P, ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ wallUnion β α ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ wallUnion β α ω → gU ω φ = ∫ z, v z * φ z) →
      ∀ (r' : ℝ≥0) (Ψ : ℂ → ℂ) (c : Chart) (ℓ : ℂ → ℂ) (n : ℤ) (G : ℂ → ℝ),
      IsFlowChart (α ω) (β ω) r' Ψ c → changePocket (α ω) (β ω) r' ⊆ leftSideOf (range (α ω)) →
      IsDerivLog c.1 ℓ (changePocket (α ω) (β ω) r') →
      (∀ z ∈ changePocket (α ω) (β ω) r', c.2.2 z = (ℓ z).im) → IsPocketBranch (β ω) (α ω) c n →
      IsBoundedHarmonicExtension
        (chartData (β ω) (α ω) (fun s => sleLambda κ - (if s < (q : ℝ≥0) then π / 2 else θ₂) * chiC κ)
          (fun s => -sleLambda κ - (if s < 1 then -(π / 2) else θ₁) * chiC κ) c)
        (exSet (β ω) (α ω) {(q : ℝ≥0)} {1} c) G →
      ∀ z ∈ changePocket (α ω) (β ω) r', v z + u₀ z = G (c.1 z) - chiC κ * (c.2.2 z + 2 * π * n) := by
  obtain ⟨hcumL, hcumR⟩ := cum_of_aux130 hS.kappa_pos hS.kappa_lt_four Hs hword
  exact ae_eqOn_changePocket_strip_reg h44 hS hcumL hcumR hθ₁ hθ₂ hq hRα hRβ hu₀ hβc hβ0 hβm hβtr hαc hα0 hαm hαtr
    hgU

end Aux130

end StripWall

end Sec7

end InteractingSLE
