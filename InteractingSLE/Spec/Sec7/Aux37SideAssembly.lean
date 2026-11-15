/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Aux37SideGerm

/-!
# Aux. lemma 37 in the bounded change pocket: the side germ statement proved, `hwit` from the flat clock alone

Packet PROVE-STRIPSYS42. Specification §6.2, Aux. lemma 37's proof (`source/spec/p193-240.md` L104–L136,
pp. 198–200).

* **`pocketSideGermStatement_of_traces`**: `Aux37Frame.PocketSideGermStatement` (the named analytic input of
  `Aux37Frame.hwit_of_sideGerm`, PROVE-STRIPSYS40) holds for the strip system, from the counterflow's trace, the walls'
  reverse visits and the walls' own Loewner traces (`isRightSideGerm_of_witness`, `isLeftSideGerm_of_witness`,
  with the counterflow's force positions bounded by the images of `0^±`).
* `ae_ownTrace_alpha`, `ae_ownTrace_beta`: the walls' own traces, from their versions and the field determination of
  their drivers (`StripWall.isDetTwoPiece_of_heights`, `_refl`: infinite lifetimes).
* **`hwit_of_flatClock`**: `hwit` of `StripPocketPath.pocketWordEvolution_of_stripSystem`, exactly in its type, from
  the flat clock (FC) and the consumer's realization data only (the binders of `hwit_of_sideGerm` without
  `PocketSideGermStatement`). Angles `θ₁ ∈ (−π/2, π/2)`, `θ₂ ∈ (−π/2, π/2]`.

No Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement`, `*_of_param` (R43, R48); `h44` is the walls'
determination input, as in G1.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology Function
open LQGMetric (DistOn TestOn)
open QuantumZipper (H Hbar chiC fwdHull)
open InteractingSLE.WangWu (negInv)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec7.Aux37Side

open WangWu Lemma71I PocketCoord PocketJordan PocketMarks Aux119Bdry Aux119Nested Aux37Germ StripWall
  StripSideHeightProb StripPocketPath Aux37Assembly Aux37Frame LocalSets
open Exist.Staged (IsRegularDriver)

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}

omit mΩ [StandardBorelSpace Ω] in
/-- The counterflow's right force positions are right of the image of `0⁺`. -/
theorem cfPosR_ge {w : ℝ≥0 → ℝ} (hw : Continuous fun s : ℝ => w s.toNNReal) {s : ℝ} (hs : 0 ≤ s) (i) :
    MartChar.RealFlow.rightImg (fun t : ℝ => w t.toNNReal) 0 s - w s.toNNReal ≤
      Sec5.GlueCond.cfPosR κ b jumps w s.toNNReal i := by
  unfold Sec5.GlueCond.cfPosR
  rw [Real.coe_toNNReal _ hs]
  have := rightImg_mono hw (Theorem14.GW3Word.flowLineXR_nonneg _ _ i) hs
  exact sub_le_sub_right this _

omit mΩ [StandardBorelSpace Ω] in
/-- The counterflow's left force positions are left of the image of `0⁻`. -/
theorem cfPosL_le {w : ℝ≥0 → ℝ} (hw : Continuous fun s : ℝ => w s.toNNReal) {s : ℝ} (hs : 0 ≤ s) (i) :
    Sec5.GlueCond.cfPosL κ b jumps w s.toNNReal i ≤
      -MartChar.RealFlow.rightImg (fun t : ℝ => -w t.toNNReal) 0 s - w s.toNNReal := by
  unfold Sec5.GlueCond.cfPosL
  rw [Real.coe_toNNReal _ hs]
  have := rightImg_mono (w := fun t : ℝ => -w t.toNNReal) hw.neg
    (neg_nonneg.2 (Theorem14.GW3Word.flowLineXL_nonpos _ _ i)) hs
  have e : (fun s => -Ito.rpath w s) = fun t : ℝ => -w t.toNNReal := rfl
  rw [e]
  linarith

/-- **The side germ statement for the strip system** (`Aux37Frame.PocketSideGermStatement`), from the counterflow's
trace, the walls' reverse visits and the walls' own Loewner traces. -/
theorem pocketSideGermStatement_of_traces
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hS : StripSys.IsStripSystem κ b jumps P h W' ζ' E)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ₁ θ₂ : ℝ} {α : Ω → ℝ≥0 → ℂ} {Lr : ℚ → Ω → ℝ≥0 → ℂ} {η : Ω → ℝ → ℂ}
    (hηtr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (fun t : ℝ≥0 => η ω t))
    (hwalls : ∀ᵐ ω ∂P, IsWallReverseVisit (α ω) (η ω) ∧ IsWallVisited (α ω) (η ω))
    (hwallsL : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, IsWallReverseVisit (Lr q ω) (η ω))
    (hownα : ∀ᵐ ω ∂P, IsLoewnerTrace (alphaDrv E θ₁ ω) (realPath (α ω)) ∧ Continuous (alphaDrv E θ₁ ω) ∧
      alphaDrv E θ₁ ω 0 = 0)
    (hownL : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, IsLoewnerTrace (betaDrv E (StripSys.rt q) θ₂ ω) (realPath (Lr q ω)) ∧
      Continuous (betaDrv E (StripSys.rt q) θ₂ ω) ∧ betaDrv E (StripSys.rt q) θ₂ ω 0 = 0) :
    PocketSideGermStatement κ b jumps P W' E θ₁ θ₂ α Lr η := by
  intro q hq s₁ s₂ v v₁ v₂
  filter_upwards [ae_isLoewnerTrace_counterflow hS hcumL hcumR hηtr, hwalls, hwallsL q hq, hownα, hownL q hq]
    with ω htr hw hwL hα hL hconf hpos Ψ c hF _ _
  have h0 := zero_notMem_closure_of_rightLo_pos hconf hpos
  have hW0 : (fun s : ℝ => W' s.toNNReal ω) 0 = 0 := by simpa using htr.2.2
  have hs₂ : ∀ {A : ℝ → ℂ}, Aux37Attach.IsAttachWitness (η ω) (cfPocket (α ω) (Lr q ω) (StripSys.rt q)) A
      (firstHit (η ω) (cfArcR (α ω) (Lr q ω) (StripSys.rt q) 1))
      (firstHit (η ω) (cfArcR (α ω) (Lr q ω) (StripSys.rt q) 0)) s₁ s₂ v v₁ v₂ → (0 : ℝ) ≤ s₂ := fun hwit =>
    ((Real.sInf_nonneg fun _ hx => hx.1).trans hwit.1).trans hwit.2.1.le
  refine ⟨fun hwit => ?_, fun hwit => ?_⟩
  · exact isRightSideGerm_of_witness hconf h0 htr.1 htr.2.1 hW0 hw.1 hwL hw.2 hF hwit hα.1 hα.2.1 hα.2.2
      (fun i => cfPosR_ge (κ := κ) (b := b) (jumps := jumps) (w := fun t => W' t ω) htr.2.1 (hs₂ hwit) i)
      (fun i => cfPosL_le (κ := κ) (b := b) (jumps := jumps) (w := fun t => W' t ω) htr.2.1 (hs₂ hwit) i)
      (Real.coe_toNNReal _ (hs₂ hwit))
  · exact isLeftSideGerm_of_witness hconf h0 htr.1 htr.2.1 hW0 hw.1 hwL hw.2 hF hwit hL.1 hL.2.1 hL.2.2
      (fun i => cfPosR_ge (κ := κ) (b := b) (jumps := jumps) (w := fun t => W' t ω) htr.2.1 (hs₂ hwit) i)
      (fun i => cfPosL_le (κ := κ) (b := b) (jumps := jumps) (w := fun t => W' t ω) htr.2.1 (hs₂ hwit) i)
      (Real.coe_toNNReal _ (hs₂ hwit))

/-! ### The walls' own Loewner traces -/

section Own

variable {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- **The right wall's own trace**: almost surely `α` is a continuous Loewner trace of its own continuous driver (from
the version and the infinite lifetimes of the field-determined pieces). -/
theorem ae_ownTrace_alpha (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    (hS : StripSys.IsStripSystem κ b jumps P h W' ζ' E)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ₁ : ℝ} (hθ₁ : θ₁ ∈ Ioo (-(π / 2)) (π / 2)) (hregα : ∀ j ω, IsRegularDriver (E (StripSys.alphaSpec θ₁) j ω))
    {α : Ω → ℝ≥0 → ℂ} (hvα : IsWallVersion P (E (StripSys.alphaSpec θ₁)) 1 α) :
    ∀ᵐ ω ∂P, IsLoewnerTrace (alphaDrv E θ₁ ω) (realPath (α ω)) ∧ Continuous (alphaDrv E θ₁ ω) ∧
      alphaDrv E θ₁ ω 0 = 0 := by
  have hκ := hS.kappa_pos
  have hκ4 := hS.kappa_lt_four
  have hb := hS.boundaryData
  have hh := hS.gff
  have hθ₁c : θ₁ ∈ Icc (-(π / 2)) (π / 2) := Ioo_subset_Icc_self hθ₁
  have hπχ : 0 ≤ π * chiC κ := mul_nonneg Real.pi_pos.le (Sec4.chiC_pos hκ hκ4).le
  have hL44 : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps →
      b y + a * chiC κ ≤ -sleLambda κ + π * chiC κ := fun a ha y hy hyJ => by
    have := hcumL a ha y hy hyJ
    linarith
  have hEα := hS.isStagedHistory_alpha hθ₁c
  have hm := StripSys.neg_pi_div_two_mem_Icc
  have hDα : IsDetTwoPiece P h (E (StripSys.alphaSpec θ₁)) :=
    isDetTwoPiece_of_heights h44 hκ hκ4 hb hh hEα hregα (hL44 _ hm) (hcumR _ hm) (hL44 _ hθ₁c) (hcumR _ hθ₁c)
      hθ₁c.1 (by linarith [hθ₁c.2])
  filter_upwards [hvα.ae_trace, hDα.ae_lifetimes] with ω htr hl
  obtain ⟨hc, hc0⟩ := continuous_catPath_of_isRegularDriver (hregα 0 ω) (hregα 1 ω) hl.1 hl.2 1
  refine ⟨isLoewnerTrace_of_isGeneratingTrace htr.1, hc.comp continuous_real_toNNReal, ?_⟩
  show catPath _ 1 _ (0 : ℝ).toNNReal = 0
  rw [Real.toNNReal_zero]
  exact hc0

/-- **The left wall's own trace** (as `ae_ownTrace_alpha`, for `β^{(q)}`). -/
theorem ae_ownTrace_beta (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    (hS : StripSys.IsStripSystem κ b jumps P h W' ζ' E)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ₂ : ℝ} (hθ₂ : θ₂ ∈ Ioc (-(π / 2)) (π / 2)) (r : ℝ≥0)
    (hregβ : ∀ j ω, IsRegularDriver (E (StripSys.betaSpec r θ₂) j ω))
    {β : Ω → ℝ≥0 → ℂ} (hvβ : IsWallVersion P (E (StripSys.betaSpec r θ₂)) r β) :
    ∀ᵐ ω ∂P, IsLoewnerTrace (betaDrv E r θ₂ ω) (realPath (β ω)) ∧ Continuous (betaDrv E r θ₂ ω) ∧
      betaDrv E r θ₂ ω 0 = 0 := by
  have hκ := hS.kappa_pos
  have hκ4 := hS.kappa_lt_four
  have hb := hS.boundaryData
  have hh := hS.gff
  have hθ₂c : θ₂ ∈ Icc (-(π / 2)) (π / 2) := Ioc_subset_Icc_self hθ₂
  have hπχ : 0 ≤ π * chiC κ := mul_nonneg Real.pi_pos.le (Sec4.chiC_pos hκ hκ4).le
  have hL44 : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps →
      b y + a * chiC κ ≤ -sleLambda κ + π * chiC κ := fun a ha y hy hyJ => by
    have := hcumL a ha y hy hyJ
    linarith
  have hEβ := hS.isStagedHistory_beta hθ₂c r
  have hp := StripSys.pi_div_two_mem_Icc
  have hDβ : IsDetTwoPiece P h (E (StripSys.betaSpec r θ₂)) :=
    isDetTwoPiece_of_heights_refl h44 hκ hκ4 hb hh hEβ hregβ (hL44 _ hp) (hcumR _ hp) (hcumL _ hθ₂c)
      (fun y hy hyJ => by have := hcumR _ hθ₂c y hy hyJ; linarith) hθ₂c.2 (by linarith [hθ₂c.1])
  filter_upwards [hvβ.ae_trace, hDβ.ae_lifetimes] with ω htr hl
  obtain ⟨hc, hc0⟩ := continuous_catPath_of_isRegularDriver (hregβ 0 ω) (hregβ 1 ω) hl.1 hl.2 r
  refine ⟨isLoewnerTrace_of_isGeneratingTrace htr.1, hc.comp continuous_real_toNNReal, ?_⟩
  show catPath _ r _ (0 : ℝ).toNNReal = 0
  rw [Real.toNNReal_zero]
  exact hc0

end Own

/-! ### `hwit` from the flat clock -/

open StripPocketPath in
/-- **`hwit` of `StripPocketPath.pocketWordEvolution_of_stripSystem`** (Aux. lemma 37's exclusion of every rational
witness in the bounded change pocket), exactly in its type, from the flat clock (FC) and the consumer's realization
data: the binders of `Aux37Frame.hwit_of_sideGerm` without `PocketSideGermStatement`, which is proved
(`pocketSideGermStatement_of_traces`). Angles: `θ₁ ∈ (−π/2, π/2)`, `θ₂ ∈ (−π/2, π/2]`. -/
theorem hwit_of_flatClock (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hS : StripSys.IsStripSystem κ b jumps P h W' ζ' E)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ₁ θ₂ : ℝ} (hθ₁ : θ₁ ∈ Ioo (-(π / 2)) (π / 2)) (hθ₂ : θ₂ ∈ Ioc (-(π / 2)) (π / 2))
    (hregα : ∀ j ω, IsRegularDriver (E (StripSys.alphaSpec θ₁) j ω))
    (hregβ : ∀ q : ℚ, 0 < q → ∀ j ω, IsRegularDriver (E (StripSys.betaSpec (StripSys.rt q) θ₂) j ω))
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {α β : Ω → ℝ≥0 → ℂ} {Lr : ℚ → Ω → ℝ≥0 → ℂ} {η : Ω → ℝ → ℂ}
    (hvα : IsWallVersion P (E (StripSys.alphaSpec θ₁)) 1 α)
    (hlocα : Sec6.IsEntranceHistoryLocal α (WholeField.centredField h u₀) P)
    (hvL : ∀ q : ℚ, 0 < q → IsWallVersion P (E (StripSys.betaSpec (StripSys.rt q) θ₂)) (StripSys.rt q) (Lr q))
    (hlocL : ∀ q : ℚ, 0 < q → Sec6.IsEntranceHistoryLocal (Lr q) (WholeField.centredField h u₀) P)
    {gU : ℚ → Ω → DistOn upperHalfPlaneOpens}
    (hgU : ∀ q : ℚ, 0 < q → IsLocalSetMean (wallUnion (Lr q) α) (WholeField.centredField h u₀) P (gU q))
    {gL : ℚ → ℝ≥0 → Ω → DistOn upperHalfPlaneOpens}
    (hgL : ∀ q : ℚ, 0 < q → ∀ t : ℝ≥0,
      IsLocalSetMean (fun ω => Lr q ω '' Icc 0 t ∩ H) (WholeField.centredField h u₀) P (gL q t))
    {gR : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens}
    (hgR : ∀ t : ℝ≥0, IsLocalSetMean (fun ω => α ω '' Icc 0 t ∩ H) (WholeField.centredField h u₀) P (gR t))
    {g : ℚ → ℝ≥0 → Ω → DistOn upperHalfPlaneOpens}
    (hg : ∀ q : ℚ, 0 < q → ∀ t : ℝ≥0,
      IsLocalSetMean (stripExpl W' ζ' (Lr q) α t) (WholeField.centredField h u₀) P (g q t))
    (hFC : ∀ q : ℚ, 0 < q → FlatClockStatement P univ (stripExpl W' ζ' (Lr q) α) (g q))
    (hηc : ∀ ω, ContinuousOn (η ω) (Ici 0))
    (hηtr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (fun t : ℝ≥0 => η ω t))
    (hwalls : ∀ᵐ ω ∂P, IsWallReverseVisit (α ω) (η ω) ∧ IsWallVisited (α ω) (η ω))
    (hwallsL : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, IsWallReverseVisit (Lr q ω) (η ω))
    (hβ : ∀ᵐ ω ∂P, IsSimpleProper (β ω))
    (hLβ : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, Lr q ω (StripSys.rt q) = β ω (StripSys.rt q))
    (hav : ∀ᵐ ω ∂P, ∀ q : ℚ, 0 ≤ (q : ℝ) → negInv (η ω q) ∉ leftSideOf (range (β ω))) :
    ∀ q : ℚ, 0 < q → ∀ s₁ s₂ v v₁ v₂ : ℚ, ∀ᵐ ω ∂P, IsChangeConfigInc (α ω) (Lr q ω) (StripSys.rt q) →
      0 < rightLo (α ω) (Lr q ω) (StripSys.rt q) →
        ¬ IsPocketWitness (α ω) (Lr q ω) (StripSys.rt q) (η ω) s₁ s₂ v v₁ v₂ :=
  hwit_of_sideGerm h44 hS hcumL hcumR hθ₁ hθ₂ hregα hregβ hu₀ hvα hlocα hvL hlocL hgU hgL hgR hg hFC hηc hηtr hwalls
    hwallsL hβ hLβ hav (pocketSideGermStatement_of_traces hS hcumL hcumR hηtr hwalls hwallsL
      (ae_ownTrace_alpha h44 hS hcumL hcumR hθ₁ hregα hvα)
      fun q hq => ae_ownTrace_beta h44 hS hcumL hcumR hθ₂ (StripSys.rt q) (hregβ q hq) (hvL q hq))

end InteractingSLE.Sec7.Aux37Side
