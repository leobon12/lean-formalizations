/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Aux37WallsConst
import InteractingSLE.Spec.Sec7.R7Aux131Strip

/-!
# Aux. lemma 37's witness exclusions for R.7's pockets (two constant-angle walls)

Packet PROVE-AUX37-WALLS. Specification §6.2, Aux. lemma 37's proof (`source/spec/p193-240.md` L104–L136,
pp. 198–200), for the pocket of Aux. lemma 131 (`source/spec/p385-432.md` L527–L548, pp. 414–416): the right wall `R`
and the left wall `L` are versions of the strip system's constant-angle incoming paths `η_{θR}`, `η_{θL}`
(`R7Aux131.constSpec`), `−π/2 ≤ θR < θL ≤ π/2` ((CS13.1), p. 415), and the pocket is the change pocket of
`(R, L, rt q)` as in `R7Aux131.r7PocketStopStatement_of_stripSystem`.

The argument is PROVE-STRIPSYS39–42's and PROVE-FLATCLOCK's for the two-angle walls of Aux. lemma 130, with the
walls' inputs from `Aux37WallsConst` (determination, locality, side heights and G1 for constant angles):

* `false_of_rightFrame_const`, `false_of_leftFrame_const`: (PFI4) at one sample, for constant wall angles
  (`θR ∈ [−π/2, π/2)` on the right, `θL ∈ (−π/2, π/2]` on the left);
* `exists_isFlowChart_of_order`: the flow chart of the change pocket, with the pocket on the left of `R`, from the
  walls' order `range R ∩ leftSide(range L) = ∅` (R.7's `hord`; `L` is its own left frontier);
* **`ae_noFrame_const`**: almost surely no witness frame (G1 `ae_ownHeights_union_const`, G2
  `Aux37Assembly.ae_cfGerm_union_strip`, the flat clock);
* **`hwit_r7`**, **`hwitI_r7`**: the witness exclusions `hwit`/`hwitI` of
  `R7Aux131.r7PocketStopStatement_of_stripSystem`, exactly in their types, from the strip system, the walls' versions,
  the counterflow's version, Lemma 5.7's reverse visits (`hwalls`) and the walls' order (`hord`); the walls' means
  and the flat clock are proved here;
* **`r7PocketStopStatement_of_stripSystem_aux37`**: `R7Aux131.r7PocketStopStatement_of_stripSystem` without
  `hwit`, `hwitI` (with `h44`, the walls' determination input).

No Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement`, `*_of_param` (R43, R48); `h44` is the walls'
determination input.
-/

set_option autoImplicit false

noncomputable section

universe u

open MeasureTheory Set Metric Filter Topology Function Bornology
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open QuantumZipper (H Hbar chiC fwdHull fwdMap logDerivFwd)
open InteractingSLE.WangWu (negInv)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.Aux37Walls

open WangWu Lemma71I PocketCoord PocketJordan PocketMarks Aux119Bdry Aux119Nested Aux37Germ StripWall
  StripSideHeightProb StripPocketPath Aux37Assembly Aux37Frame LocalSets R7Aux131
open Exist.Staged (IsRegularDriver)

/-! ### (PFI4) for constant wall angles -/

section Exclusion

variable {κ : ℝ} {nL nR : ℕ} {R L : ℝ≥0 → ℂ} {r : ℝ≥0} {Ar As Wu Er Es : Set ℂ} {w d : ℝ → ℝ} {s₀ : ℝ≥0}
  {posL : Fin nL → ℝ} {posR : Fin nR → ℝ} {vr vs u₀ : ℂ → ℝ}

/-- **No witness frame on a constant-angle right wall** (`Aux37Assembly.false_of_rightFrame` with the right wall's
angle `θR ∈ [−π/2, π/2)` at every own time). -/
theorem false_of_rightFrame_const (hκ : 0 < κ) (hκ4 : κ < 4) {θR : ℝ} (hθR : θR ∈ Ico (-(π / 2)) (π / 2))
    (hG1 : ∀ t₀ : ℝ≥0, R t₀ ∉ range L → (∃ ε > 0, Ar ∩ ball (R t₀) ε = ∅) → ∃ q' : ℝ≥0, t₀ < q' ∧
      Tendsto (fun z => vr z + u₀ z + chiC κ * (logDerivFwd d q' z).im) (𝓝[changePocket R L r] (R t₀))
        (𝓝 (-sleLambda κ - θR * chiC κ)))
    (hG2 : ∀ z₀ ∈ As, (∃ ε > 0, Wu ∩ ball z₀ ε ⊆ As) → ∀ F : Filter ℂ, F ≤ 𝓝[H \ Es] z₀ → ∀ y : ℝ,
      Tendsto (fun z => fwdMap w s₀ (negInv z)) F (𝓝 (y : ℂ)) → y ∉ forceJumpSet posL posR → 0 < y →
        (∀ i, y ≤ posR i) → Tendsto (fun z => vs z + u₀ z + chiC κ * (Sec5.GlueImg.logDerivPsi w s₀ z).im) F
          (𝓝 (-sleLambda (16 / κ) + π * chiC κ)))
    (hFC : ∀ z ∈ H \ Es, connectedComponentIn (H \ Es) z = connectedComponentIn (H \ Er) z →
      ∀ x ∈ connectedComponentIn (H \ Es) z, vr x = vs x)
    (hfr : IsRightWitnessFrame R L r Ar As Wu Er Es w d s₀ posL posR) : False := by
  obtain ⟨t₀, hoff, -, hAr, hAs, hWu, F, hFne, hF1, hFE, ⟨z, hz, hcomp, hFcomp⟩, ⟨y, hy, hyJ, hy0, hyR⟩,
    hBR⟩ := hfr
  obtain ⟨q', hq', hlim⟩ := hG1 t₀ hoff hAr
  obtain ⟨k, hk⟩ := hBR q' hq'
  have hG2' := hG2 _ hAs hWu F hFE y hy hyJ hy0 hyR
  have hFCeq : vr =ᶠ[F] vs := Aux37Germ.eventuallyEq_of_flatClock (hFC z hz hcomp) hFcomp
  have hside : ((-1 : ℝ) = 1 ∧ θR ∈ Ioc (-(π / 2)) (π / 2)) ∨ ((-1 : ℝ) = -1 ∧ θR ∈ Ico (-(π / 2)) (π / 2)) :=
    Or.inr ⟨rfl, hθR⟩
  refine false_of_flat_germs_shift (u₀ := u₀) hκ hκ4 hside hFCeq ?_ 1 ?_ k hk
  · rw [neg_one_mul]
    exact hlim.mono_left hF1
  · convert hG2' using 2
    push_cast
    ring

/-- **No witness frame on a constant-angle left wall** (`Aux37Assembly.false_of_leftFrame` with the left wall's angle
`θL ∈ (−π/2, π/2]` at every own time). -/
theorem false_of_leftFrame_const (hκ : 0 < κ) (hκ4 : κ < 4) {θL : ℝ} (hθL : θL ∈ Ioc (-(π / 2)) (π / 2))
    (hG1 : ∀ t₀ : ℝ≥0, L t₀ ∉ range R → (∃ ε > 0, Ar ∩ ball (L t₀) ε = ∅) → ∃ q' : ℝ≥0, t₀ < q' ∧
      Tendsto (fun z => vr z + u₀ z + chiC κ * (logDerivFwd d q' z).im) (𝓝[changePocket R L r] (L t₀))
        (𝓝 (sleLambda κ - θL * chiC κ)))
    (hG2 : ∀ z₀ ∈ As, (∃ ε > 0, Wu ∩ ball z₀ ε ⊆ As) → ∀ F : Filter ℂ, F ≤ 𝓝[H \ Es] z₀ → ∀ y : ℝ,
      Tendsto (fun z => fwdMap w s₀ (negInv z)) F (𝓝 (y : ℂ)) → y ∉ forceJumpSet posL posR → y < 0 →
        (∀ i, posL i ≤ y) → Tendsto (fun z => vs z + u₀ z + chiC κ * (Sec5.GlueImg.logDerivPsi w s₀ z).im) F
          (𝓝 (sleLambda (16 / κ) - π * chiC κ)))
    (hFC : ∀ z ∈ H \ Es, connectedComponentIn (H \ Es) z = connectedComponentIn (H \ Er) z →
      ∀ x ∈ connectedComponentIn (H \ Es) z, vr x = vs x)
    (hfr : IsLeftWitnessFrame R L r Ar As Wu Er Es w d s₀ posL posR) : False := by
  obtain ⟨t₀, hoff, -, hAr, hAs, hWu, F, hFne, hF1, hFE, ⟨z, hz, hcomp, hFcomp⟩, ⟨y, hy, hyJ, hy0, hyL⟩,
    hBR⟩ := hfr
  obtain ⟨q', hq', hlim⟩ := hG1 t₀ hoff hAr
  obtain ⟨k, hk⟩ := hBR q' hq'
  have hG2' := hG2 _ hAs hWu F hFE y hy hyJ hy0 hyL
  have hFCeq : vr =ᶠ[F] vs := Aux37Germ.eventuallyEq_of_flatClock (hFC z hz hcomp) hFcomp
  have hside : ((1 : ℝ) = 1 ∧ θL ∈ Ioc (-(π / 2)) (π / 2)) ∨ ((1 : ℝ) = -1 ∧ θL ∈ Ico (-(π / 2)) (π / 2)) :=
    Or.inl ⟨rfl, hθL⟩
  refine false_of_flat_germs_shift (u₀ := u₀) hκ hκ4 hside hFCeq ?_ 0 ?_ k hk
  · rw [one_mul]
    exact hlim.mono_left hF1
  · convert hG2' using 2
    push_cast
    ring

end Exclusion

/-! ### The flow chart from the walls' order -/

/-- **(F0) from the walls' order**: a flow chart of the change pocket of `(R, L, r)` with the pocket on the left of
`R`, when `R` avoids the open left side of `L` (`L` is then its own left frontier through the change point). -/
theorem exists_isFlowChart_of_order {R L : ℝ≥0 → ℂ} {r : ℝ≥0} (h : IsChangeConfigInc R L r)
    (hord : Disjoint (range R) (leftSideOf (range L))) :
    (∃ (Ψ : ℂ → ℂ) (c : Chart), IsFlowChart R L r Ψ c) ∧ changePocket R L r ⊆ leftSideOf (range R) := by
  have hor := h.isFlowChartOriented_of_leftFrontier h.left rfl hord
  refine ⟨?_, h.changePocket_subset_leftSideOf (h.mem_leftSideOf_of_leftFrontier h.left rfl hord)⟩
  obtain ⟨-, c, -, -, -, -, -, -, -, -, hflow, -⟩ :=
    Aux119Lift.exists_measurable_flowChart_branch (Ω := Unit) (R := fun _ => R) (L := fun _ => L) (r := r)
      (G := univ) (fun _ => measurable_const) (fun _ => measurable_const) MeasurableSet.univ (fun _ _ => h)
      (fun _ _ => hor)
  obtain ⟨Ψ, hΨ⟩ := hflow () trivial
  exact ⟨Ψ, c (), hΨ⟩

/-! ### No witness frame, almost surely -/

section Strip

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ}
  {ζ' : Ω → ℝ≥0∞} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- **No witness frame, almost surely, for two constant-angle walls** (`Aux37Assembly.ae_noFrame_strip` for the walls
`L = η_{θL}`, `R = η_{θR}`): at deterministic times `r₀ ≤ s₀`, almost surely, for every flow chart of the change
pocket of `(R, L, r)` on the left of `R`, neither witness frame exists. Inputs: the walls' versions and means, the
exploration's means `g t` and the flat clock (FC). -/
theorem ae_noFrame_const (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    (hS : StripSys.IsStripSystem κ b jumps P h W' ζ' E)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θR θL : ℝ} (hθR : θR ∈ Ico (-(π / 2)) (π / 2)) (hθL : θL ∈ Ioc (-(π / 2)) (π / 2)) (r : ℝ≥0)
    (hregR : ∀ ω, IsRegularDriver (E (constSpec θR) 0 ω)) (hregL : ∀ ω, IsRegularDriver (E (constSpec θL) 0 ω))
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {R L : Ω → ℝ≥0 → ℂ} (hRc : ∀ ω, Continuous (R ω)) (hR0 : ∀ ω, R ω 0 = 0)
    (hRm : ∀ t, Measurable fun ω => R ω t)
    (hRtr : ∀ᵐ ω ∂P, IsGeneratingTrace (E (constSpec θR) 0 ω).1 ⊤ (R ω))
    (hLc : ∀ ω, Continuous (L ω)) (hL0 : ∀ ω, L ω 0 = 0) (hLm : ∀ t, Measurable fun ω => L ω t)
    (hLtr : ∀ᵐ ω ∂P, IsGeneratingTrace (E (constSpec θL) 0 ω).1 ⊤ (L ω))
    {gU : Ω → DistOn upperHalfPlaneOpens}
    (hgU : IsLocalSetMean (wallUnion L R) (WholeField.centredField h u₀) P gU)
    {gL gR : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens}
    (hgL : ∀ t : ℝ≥0, IsLocalSetMean (fun ω => L ω '' Icc 0 t ∩ H) (WholeField.centredField h u₀) P (gL t))
    (hgR : ∀ t : ℝ≥0, IsLocalSetMean (fun ω => R ω '' Icc 0 t ∩ H) (WholeField.centredField h u₀) P (gR t))
    {g : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens}
    (hg : ∀ t : ℝ≥0, IsLocalSetMean (stripExpl W' ζ' L R t) (WholeField.centredField h u₀) P (g t))
    (hFC : FlatClockStatement P univ (stripExpl W' ζ' L R) g) {r₀ s₀ : ℝ≥0} (hrs : r₀ ≤ s₀) :
    ∀ᵐ ω ∂P, ∀ (Ψ : ℂ → ℂ) (c : Chart), IsFlowChart (R ω) (L ω) r Ψ c →
      changePocket (R ω) (L ω) r ⊆ leftSideOf (range (R ω)) →
      ¬ IsRightWitnessFrame (R ω) (L ω) r (cfHull W' ζ' r₀ ω) (cfHull W' ζ' s₀ ω) (wallUnion L R ω)
          (stripExpl W' ζ' L R r₀ ω) (stripExpl W' ζ' L R s₀ ω) (fun t : ℝ => W' t.toNNReal ω)
          (constDrv E θR ω) s₀ (Sec5.GlueCond.cfPosL κ b jumps (W' · ω) s₀)
          (Sec5.GlueCond.cfPosR κ b jumps (W' · ω) s₀) ∧
        ¬ IsLeftWitnessFrame (R ω) (L ω) r (cfHull W' ζ' r₀ ω) (cfHull W' ζ' s₀ ω) (wallUnion L R ω)
          (stripExpl W' ζ' L R r₀ ω) (stripExpl W' ζ' L R s₀ ω) (fun t : ℝ => W' t.toNNReal ω)
          (constDrv E θL ω) s₀ (Sec5.GlueCond.cfPosL κ b jumps (W' · ω) s₀)
          (Sec5.GlueCond.cfPosR κ b jumps (W' · ω) s₀) := by
  have hκ := hS.kappa_pos
  have hκ4 := hS.kappa_lt_four
  have hθRc : θR ∈ Icc (-(π / 2)) (π / 2) := Ico_subset_Icc_self hθR
  have hθLc : θL ∈ Icc (-(π / 2)) (π / 2) := Ioc_subset_Icc_self hθL
  have hLdet := hdet_const h44 hS hcumL hcumR hθLc hregL u₀ hLtr
  have hRdet := hdet_const h44 hS hcumL hcumR hθRc hregR u₀ hRtr
  have hLloc := isEntranceHistoryLocal_const hS hcumL hcumR hθLc hregL hu₀ hLc hL0 hLm hLtr
  have hRloc := isEntranceHistoryLocal_const hS hcumL hcumR hθRc hregR hu₀ hRc hR0 hRm hRtr
  have htr : ∀ᵐ ω ∂P, Tendsto (L ω) atTop (cobounded ℂ) ∧ Tendsto (R ω) atTop (cobounded ℂ) := by
    filter_upwards [ae_trace_const hS hcumL hcumR hθLc hregL hLc hL0 hLtr,
      ae_trace_const hS hcumL hcumR hθRc hregR hRc hR0 hRtr] with ω h1 h2
    exact ⟨h1.2.2.2.2, h2.2.2.2.2⟩
  have G1 := ae_ownHeights_union_const h44 hS hcumL hcumR hθLc hθRc hregL hregR hu₀ hLc hL0 hLm hLtr hRc hR0 hRm
    hRtr (measurable_cfHull hS.counterflow r₀) (isLocalSet_cfHull hS hcumL hcumR u₀ hu₀.1 r₀) (hg r₀) hgU hgL hgR
  have G2 := ae_cfGerm_union_strip hS hcumL hcumR hu₀ hLc hL0 hLm hLdet hLloc hRc hR0 hRm hRdet hRloc htr s₀
    (hg s₀)
  have FC := hFC r₀ trivial s₀ trivial hrs
  filter_upwards [G1, G2, FC, (hg r₀).2.1, (hg s₀).2.1] with ω h1 h2 h3 ⟨vr, hvr, hvrr⟩ ⟨vs, hvs, hvsr⟩ Ψ c hF hCl
  obtain ⟨g1L, g1R⟩ := h1 vr hvr hvrr r Ψ c hF hCl
  have g2 := h2 vs hvs hvsr
  have fc := fun z hz hcomp => h3 vr vs hvr hvrr hvs hvsr z hz hcomp
  refine ⟨fun hfr => ?_, fun hfr => ?_⟩
  · exact false_of_rightFrame_const (u₀ := u₀) hκ hκ4 hθR g1R
      (fun z₀ hz₀ hε F hF y hy hyJ hy0 hyR => (g2 z₀ hz₀ hε F hF y hy hyJ).2 hy0 hyR) fc hfr
  · exact false_of_leftFrame_const (u₀ := u₀) hκ hκ4 hθL g1L
      (fun z₀ hz₀ hε F hF y hy hyJ hy0 hyL => (g2 z₀ hz₀ hε F hF y hy hyJ).1 hy0 hyL) fc hfr

end Strip

/-! ### The walls' field inputs -/

section Inputs

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ}
  {ζ' : Ω → ℝ≥0∞} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- **The field inputs of Aux. lemma 37 for two constant-angle walls**: the means `gU` of the walls' union, `gL`, `gR`
of their prefixes, versions `g t` of the means of the strip exploration `stripExpl W′ ζ′ L R t`, and the flat clock
for that exploration (Lemma 6.2 for the walls, `isLocalSet_wallUnion`, `StripWall.exists_isLocalSetMean_prefix`,
`FlatClockProof.exists_isLocalSetMean_stripExpl_of_walls`, `FlatClockProof.flatClockStatement_stripExpl_of_walls`). -/
theorem exists_fieldInputs_const (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    (hS : StripSys.IsStripSystem κ b jumps P h W' ζ' E)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θR θL : ℝ} (hθR : θR ∈ Icc (-(π / 2)) (π / 2)) (hθL : θL ∈ Icc (-(π / 2)) (π / 2))
    (hregR : ∀ ω, IsRegularDriver (E (constSpec θR) 0 ω)) (hregL : ∀ ω, IsRegularDriver (E (constSpec θL) 0 ω))
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {R L : Ω → ℝ≥0 → ℂ} (hRc : ∀ ω, Continuous (R ω)) (hR0 : ∀ ω, R ω 0 = 0)
    (hRm : ∀ t, Measurable fun ω => R ω t)
    (hRtr : ∀ᵐ ω ∂P, IsGeneratingTrace (E (constSpec θR) 0 ω).1 ⊤ (R ω))
    (hLc : ∀ ω, Continuous (L ω)) (hL0 : ∀ ω, L ω 0 = 0) (hLm : ∀ t, Measurable fun ω => L ω t)
    (hLtr : ∀ᵐ ω ∂P, IsGeneratingTrace (E (constSpec θL) 0 ω).1 ⊤ (L ω)) :
    (∃ gU : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean (wallUnion L R) (WholeField.centredField h u₀) P gU) ∧
    (∃ gL : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens, ∀ t : ℝ≥0,
      IsLocalSetMean (fun ω => L ω '' Icc 0 t ∩ H) (WholeField.centredField h u₀) P (gL t)) ∧
    (∃ gR : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens, ∀ t : ℝ≥0,
      IsLocalSetMean (fun ω => R ω '' Icc 0 t ∩ H) (WholeField.centredField h u₀) P (gR t)) ∧
    ∃ g : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens,
      (∀ t : ℝ≥0, IsLocalSetMean (stripExpl W' ζ' L R t) (WholeField.centredField h u₀) P (g t)) ∧
      FlatClockStatement P univ (stripExpl W' ζ' L R) g := by
  have hX := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hS.gff hu₀
  have hLdet := hdet_const h44 hS hcumL hcumR hθL hregL u₀ hLtr
  have hRdet := hdet_const h44 hS hcumL hcumR hθR hregR u₀ hRtr
  have hLloc := isEntranceHistoryLocal_const hS hcumL hcumR hθL hregL hu₀ hLc hL0 hLm hLtr
  have hRloc := isEntranceHistoryLocal_const hS hcumL hcumR hθR hregR hu₀ hRc hR0 hRm hRtr
  have htr : ∀ᵐ ω ∂P, Tendsto (L ω) atTop (cobounded ℂ) ∧ Tendsto (R ω) atTop (cobounded ℂ) := by
    filter_upwards [ae_trace_const hS hcumL hcumR hθL hregL hLc hL0 hLtr,
      ae_trace_const hS hcumL hcumR hθR hregR hRc hR0 hRtr] with ω h1 h2
    exact ⟨h1.2.2.2.2, h2.2.2.2.2⟩
  obtain ⟨hUm, hUloc, -⟩ := isLocalSet_wallUnion hX hLc hL0 hLm hLdet hLloc hRc hR0 hRm hRdet hRloc htr
  obtain ⟨-, g, hg⟩ := FlatClockProof.exists_isLocalSetMean_stripExpl_of_walls hS hcumL hcumR hu₀ hLc hL0 hLm hLdet
    hLloc hRc hR0 hRm hRdet hRloc htr
  exact ⟨IsLocalSet.exists_isLocalSetMean hX hUm hUloc, exists_isLocalSetMean_prefix hX hLc hL0 hLm hLdet hLloc,
    exists_isLocalSetMean_prefix hX hRc hR0 hRm hRdet hRloc, g, hg,
    FlatClockProof.flatClockStatement_stripExpl_of_walls hS hcumL hcumR hu₀ hLc hL0 hLm hLdet hLloc hRc hR0 hRm hRdet
      hRloc htr hg⟩

end Inputs

/-! ### `hwit` and `hwitI` for R.7's pockets -/

section Hwit

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ}
  {ζ' : Ω → ℝ≥0∞} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- **Aux. lemma 37's witness exclusion in the bounded change pocket of two constant-angle walls** (`hwit` of
`R7Aux131.r7PocketStopStatement_of_stripSystem`, exactly in its type): from the strip system, versions of the walls
`R = η_{θR}`, `L = η_{θL}` (`θR ∈ [−π/2, π/2)`, `θL ∈ (−π/2, π/2]`) and of the counterflow's trace `η`, Lemma 5.7's
reverse visits (`hwalls`) and the walls' order (`hord`). -/
theorem hwit_r7 (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    (hS : StripSys.IsStripSystem κ b jumps P h W' ζ' E)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θR θL : ℝ} (hθR : θR ∈ Ico (-(π / 2)) (π / 2)) (hθL : θL ∈ Ioc (-(π / 2)) (π / 2))
    (hregR : ∀ ω, IsRegularDriver (E (constSpec θR) 0 ω)) (hregL : ∀ ω, IsRegularDriver (E (constSpec θL) 0 ω))
    {R L : Ω → ℝ≥0 → ℂ} {η : Ω → ℝ → ℂ}
    (hRc : ∀ ω, Continuous (R ω)) (hR0 : ∀ ω, R ω 0 = 0) (hRm : ∀ t, Measurable fun ω => R ω t)
    (hRtr : ∀ᵐ ω ∂P, IsGeneratingTrace (E (constSpec θR) 0 ω).1 ⊤ (R ω))
    (hLc : ∀ ω, Continuous (L ω)) (hL0 : ∀ ω, L ω 0 = 0) (hLm : ∀ t, Measurable fun ω => L ω t)
    (hLtr : ∀ᵐ ω ∂P, IsGeneratingTrace (E (constSpec θL) 0 ω).1 ⊤ (L ω))
    (hηtr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (fun t : ℝ≥0 => η ω t))
    (hwalls : ∀ᵐ ω ∂P, IsWallReverseVisit (R ω) (η ω) ∧ IsWallVisited (R ω) (η ω) ∧
      IsWallReverseVisit (L ω) (η ω) ∧ IsWallVisited (L ω) (η ω))
    (hord : ∀ᵐ ω ∂P, Disjoint (range (R ω)) (leftSideOf (range (L ω)))) :
    ∀ q : ℚ, 0 < q → ∀ s₁ s₂ v v₁ v₂ : ℚ, ∀ᵐ ω ∂P, IsChangeConfigInc (R ω) (L ω) (StripSys.rt q) →
      0 < rightLo (R ω) (L ω) (StripSys.rt q) →
        ¬ IsPocketWitness (R ω) (L ω) (StripSys.rt q) (η ω) s₁ s₂ v v₁ v₂ := by
  obtain ⟨u₀, hu₀, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hS.boundaryData
  have hθRc : θR ∈ Icc (-(π / 2)) (π / 2) := Ico_subset_Icc_self hθR
  have hθLc : θL ∈ Icc (-(π / 2)) (π / 2) := Ioc_subset_Icc_self hθL
  obtain ⟨⟨gU, hgU⟩, ⟨gL, hgL⟩, ⟨gR, hgR⟩, g, hg, hFC⟩ := exists_fieldInputs_const h44 hS hcumL hcumR hθRc hθLc
    hregR hregL hu₀ hRc hR0 hRm hRtr hLc hL0 hLm hLtr
  intro q hq s₁ s₂ v v₁ v₂
  by_cases hlt : (s₁ : ℝ) < s₂
  swap
  · refine Eventually.of_forall fun ω _ _ hw => hlt ?_
    rcases hw.1 with h1 | h1
    · exact h1.2.1
    · exact h1.2.1
  have hrs : (s₁ : ℝ).toNNReal ≤ (s₂ : ℝ).toNNReal := Real.toNNReal_le_toNNReal hlt.le
  have hreg : ∀ᵐ ω ∂P, ζ' ω = ⊤ ∧ W' 0 ω = 0 ∧ Continuous fun t => W' t ω := by
    filter_upwards [StripPocketPath.ae_counterflow_trace hS hcumL hcumR] with ω hω
    exact ⟨hω.1, hω.2.2.1, hω.2.1⟩
  filter_upwards [ae_noFrame_const h44 hS hcumL hcumR hθR hθL (StripSys.rt q) hregR hregL hu₀ hRc hR0 hRm hRtr hLc
    hL0 hLm hLtr hgU hgL hgR hg hFC hrs, ae_isLoewnerTrace_counterflow hS hcumL hcumR hηtr, hreg, hwalls, hord,
    ae_ownTrace_const hS hcumL hcumR hθRc hregR hRc hR0 hRtr, ae_ownTrace_const hS hcumL hcumR hθLc hregL hLc hL0 hLtr]
    with ω hno htrω hregω hwω hordω hRo hLo hconf hpos hwit
  have h0 := zero_notMem_closure_of_rightLo_pos hconf hpos
  obtain ⟨⟨Ψ, c, hF⟩, hCl⟩ := exists_isFlowChart_of_order hconf hordω
  obtain ⟨hnoR, hnoL⟩ := hno Ψ c hF hCl
  have hW0 : (fun s : ℝ => W' s.toNNReal ω) 0 = 0 := by simpa using htrω.2.2
  have he : ∀ t : ℝ≥0, cfHull W' ζ' t ω = negInv '' fwdHull (fun s : ℝ => W' s.toNNReal ω) t :=
    cfHull_eq hregω.1 hregω.2.1 hregω.2.2
  have hs₁0 : (0 : ℝ) ≤ s₁ := by
    rcases hwit.1 with h1 | h1
    · exact (Real.sInf_nonneg fun _ hx => hx.1).trans h1.1
    · exact (Real.sInf_nonneg fun _ hx => hx.1).trans h1.1
  have hs₂0 : (0 : ℝ) ≤ s₂ := hs₁0.trans hlt.le
  have hs₁ : (((s₁ : ℝ).toNNReal : ℝ≥0) : ℝ) = s₁ := Real.coe_toNNReal _ hs₁0
  have hs₂ : (((s₂ : ℝ).toNNReal : ℝ≥0) : ℝ) = s₂ := Real.coe_toNNReal _ hs₂0
  have hposR := fun i => Aux37Side.cfPosR_ge (κ := κ) (b := b) (jumps := jumps) (w := fun t => W' t ω) htrω.2.1
    hs₂0 i
  have hposL := fun i => Aux37Side.cfPosL_le (κ := κ) (b := b) (jumps := jumps) (w := fun t => W' t ω) htrω.2.1
    hs₂0 i
  rcases hwit.1 with hwR | hwL
  · obtain ⟨x, hx, F, hFne, hFG, hgm⟩ := Aux37Side.isRightSideGerm_of_witness hconf h0 htrω.1 htrω.2.1 hW0 hwω.1
      hwω.2.2.1 hwω.2.1 hF hwR hRo.1 hRo.2.1 hRo.2.2 hposR hposL hs₂
    have hwR' : Aux37Attach.IsAttachWitness (η ω) (cfPocket (R ω) (L ω) (StripSys.rt q))
        (cfArcR (R ω) (L ω) (StripSys.rt q)) (firstHit (η ω) (cfArcR (R ω) (L ω) (StripSys.rt q) 1))
        (firstHit (η ω) (cfArcR (R ω) (L ω) (StripSys.rt q) 0)) ((s₁ : ℝ).toNNReal : ℝ) ((s₂ : ℝ).toNNReal : ℝ)
        v v₁ v₂ := by rw [hs₁, hs₂]; exact hwR
    have hfr := isRightWitnessFrame_of_germ (hFne := hFne) hconf h0 htrω.1 htrω.2.1 hW0 hwω.1 hwω.2.2.1 hwω.2.1 hF
      hwR' hwit.2 hx hFG hgm
    refine hnoR ?_
    simp only [stripExpl, wallUnion, he]
    exact hfr
  · obtain ⟨x, hx, F, hFne, hFG, hgm⟩ := Aux37Side.isLeftSideGerm_of_witness hconf h0 htrω.1 htrω.2.1 hW0 hwω.1
      hwω.2.2.1 hwω.2.1 hF hwL hLo.1 hLo.2.1 hLo.2.2 hposR hposL hs₂
    have hwL' : Aux37Attach.IsAttachWitness (η ω) (cfPocket (R ω) (L ω) (StripSys.rt q))
        (cfArcL (R ω) (L ω) (StripSys.rt q)) (firstHit (η ω) (cfArcR (R ω) (L ω) (StripSys.rt q) 1))
        (firstHit (η ω) (cfArcR (R ω) (L ω) (StripSys.rt q) 0)) ((s₁ : ℝ).toNNReal : ℝ) ((s₂ : ℝ).toNNReal : ℝ)
        v v₁ v₂ := by rw [hs₁, hs₂]; exact hwL
    have hfr := isLeftWitnessFrame_of_germ (hFne := hFne) hconf h0 htrω.1 htrω.2.1 hW0 hwω.1 hwω.2.2.1 hwω.2.1 hF
      hwL' hwit.2 hx hFG hgm
    refine hnoL ?_
    simp only [stripExpl, wallUnion, he]
    exact hfr

/-- **Aux. lemma 37's witness exclusion in the change pocket at the flow seed of two constant-angle walls** (`hwitI`
of `R7Aux131.r7PocketStopStatement_of_stripSystem`, exactly in its type; as `hwit_r7`). -/
theorem hwitI_r7 (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    (hS : StripSys.IsStripSystem κ b jumps P h W' ζ' E)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θR θL : ℝ} (hθR : θR ∈ Ico (-(π / 2)) (π / 2)) (hθL : θL ∈ Ioc (-(π / 2)) (π / 2))
    (hregR : ∀ ω, IsRegularDriver (E (constSpec θR) 0 ω)) (hregL : ∀ ω, IsRegularDriver (E (constSpec θL) 0 ω))
    {R L : Ω → ℝ≥0 → ℂ} {η : Ω → ℝ → ℂ}
    (hRc : ∀ ω, Continuous (R ω)) (hR0 : ∀ ω, R ω 0 = 0) (hRm : ∀ t, Measurable fun ω => R ω t)
    (hRtr : ∀ᵐ ω ∂P, IsGeneratingTrace (E (constSpec θR) 0 ω).1 ⊤ (R ω))
    (hLc : ∀ ω, Continuous (L ω)) (hL0 : ∀ ω, L ω 0 = 0) (hLm : ∀ t, Measurable fun ω => L ω t)
    (hLtr : ∀ᵐ ω ∂P, IsGeneratingTrace (E (constSpec θL) 0 ω).1 ⊤ (L ω))
    (hηtr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (fun t : ℝ≥0 => η ω t))
    (hwalls : ∀ᵐ ω ∂P, IsWallReverseVisit (R ω) (η ω) ∧ IsWallVisited (R ω) (η ω) ∧
      IsWallReverseVisit (L ω) (η ω) ∧ IsWallVisited (L ω) (η ω))
    (hord : ∀ᵐ ω ∂P, Disjoint (range (R ω)) (leftSideOf (range (L ω)))) :
    ∀ q : ℚ, 0 < q → ∀ s₁ s₂ v v₁ v₂ : ℚ, ∀ᵐ ω ∂P, IsChangeConfigInc (R ω) (L ω) (StripSys.rt q) →
      rightLo (R ω) (L ω) (StripSys.rt q) = 0 →
        ¬ IsPocketWitnessInf (R ω) (L ω) (StripSys.rt q) (η ω) s₁ s₂ v v₁ v₂ := by
  obtain ⟨u₀, hu₀, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hS.boundaryData
  have hθRc : θR ∈ Icc (-(π / 2)) (π / 2) := Ico_subset_Icc_self hθR
  have hθLc : θL ∈ Icc (-(π / 2)) (π / 2) := Ioc_subset_Icc_self hθL
  obtain ⟨⟨gU, hgU⟩, ⟨gL, hgL⟩, ⟨gR, hgR⟩, g, hg, hFC⟩ := exists_fieldInputs_const h44 hS hcumL hcumR hθRc hθLc
    hregR hregL hu₀ hRc hR0 hRm hRtr hLc hL0 hLm hLtr
  intro q hq s₁ s₂ v v₁ v₂
  by_cases hlt : (s₁ : ℝ) < s₂
  swap
  · refine Eventually.of_forall fun ω _ _ hw => hlt ?_
    rcases hw.1 with h1 | h1
    · exact h1.2.1
    · exact h1.2.1
  have hrs : (s₁ : ℝ).toNNReal ≤ (s₂ : ℝ).toNNReal := Real.toNNReal_le_toNNReal hlt.le
  have hreg : ∀ᵐ ω ∂P, ζ' ω = ⊤ ∧ W' 0 ω = 0 ∧ Continuous fun t => W' t ω := by
    filter_upwards [StripPocketPath.ae_counterflow_trace hS hcumL hcumR] with ω hω
    exact ⟨hω.1, hω.2.2.1, hω.2.1⟩
  filter_upwards [ae_noFrame_const h44 hS hcumL hcumR hθR hθL (StripSys.rt q) hregR hregL hu₀ hRc hR0 hRm hRtr hLc
    hL0 hLm hLtr hgU hgL hgR hg hFC hrs, ae_isLoewnerTrace_counterflow hS hcumL hcumR hηtr, hreg, hwalls, hord,
    ae_ownTrace_const hS hcumL hcumR hθRc hregR hRc hR0 hRtr, ae_ownTrace_const hS hcumL hcumR hθLc hregL hLc hL0 hLtr]
    with ω hno htrω hregω hwω hordω hRo hLo hconf hpos hwit
  obtain ⟨⟨Ψ, c, hF⟩, hCl⟩ := exists_isFlowChart_of_order hconf hordω
  obtain ⟨hnoR, hnoL⟩ := hno Ψ c hF hCl
  have hW0 : (fun s : ℝ => W' s.toNNReal ω) 0 = 0 := by simpa using htrω.2.2
  have he : ∀ t : ℝ≥0, cfHull W' ζ' t ω = negInv '' fwdHull (fun s : ℝ => W' s.toNNReal ω) t :=
    cfHull_eq hregω.1 hregω.2.1 hregω.2.2
  have hs₁0 : (0 : ℝ) ≤ s₁ := by
    rcases hwit.1 with h1 | h1
    · exact (Real.sInf_nonneg fun _ hx => hx.1).trans h1.1
    · exact (Real.sInf_nonneg fun _ hx => hx.1).trans h1.1
  have hs₁ : (((s₁ : ℝ).toNNReal : ℝ≥0) : ℝ) = s₁ := Real.coe_toNNReal _ hs₁0
  have hs₂ : (((s₂ : ℝ).toNNReal : ℝ≥0) : ℝ) = s₂ := Real.coe_toNNReal _ (hs₁0.trans hlt.le)
  rcases hwit.1 with hwR | hwL
  · have hfr := Aux37Side.isRightWitnessFrame_of_inf hconf hpos htrω.1 htrω.2.1 hW0 hwω.1 hwω.2.2.1 hwω.2.1
      hwω.2.2.2 hF hwR hwit.2 hRo.1 hRo.2.1 hRo.2.2
      (fun i => Aux37Side.cfPosR_ge (κ := κ) (b := b) (jumps := jumps) (w := fun t => W' t ω) htrω.2.1
        (hs₁0.trans hlt.le) i)
      (fun i => Aux37Side.cfPosL_le (κ := κ) (b := b) (jumps := jumps) (w := fun t => W' t ω) htrω.2.1
        (hs₁0.trans hlt.le) i) hs₁ hs₂
    refine hnoR ?_
    simp only [stripExpl, wallUnion, he]
    exact hfr
  · have hfr := Aux37Side.isLeftWitnessFrame_of_inf hconf hpos htrω.1 htrω.2.1 hW0 hwω.1 hwω.2.2.1 hwω.2.1
      hwω.2.2.2 hF hwL hwit.2 hLo.1 hLo.2.1 hLo.2.2
      (fun i => Aux37Side.cfPosR_ge (κ := κ) (b := b) (jumps := jumps) (w := fun t => W' t ω) htrω.2.1
        (hs₁0.trans hlt.le) i)
      (fun i => Aux37Side.cfPosL_le (κ := κ) (b := b) (jumps := jumps) (w := fun t => W' t ω) htrω.2.1
        (hs₁0.trans hlt.le) i) hs₁ hs₂
    refine hnoL ?_
    simp only [stripExpl, wallUnion, he]
    exact hfr

end Hwit

/-! ### R.7's pocket stop statement without the witness exclusions -/

open R7Pocket PocketWordAssembly PocketSeedOpen PocketStopField PocketStopWallsFin StripPocketConfig in
open SupercriticalConformalCovariance.GM24 (smoothDist) in
/-- **`R7PocketStopStatement κ′ r_L r_R GoodR7` from the strip system's two constant-angle flow lines, with Aux.
lemma 37's witness exclusions proved** (`hwit_r7`, `hwitI_r7`): `R7Aux131.r7PocketStopStatement_of_stripSystem`
without its inputs `hwit`, `hwitI`, with the walls' determination input `h44`. The angles
`θR = R7.thetaR (16/κ) r_L ∈ [−π/2, π/2)` and `θL = R7.thetaL (16/κ) r_R ∈ (−π/2, π/2]` come from (CS13.1)
(`R7Aux131.aux131_angles_of_max_eq`). All other binders are the consumer's, verbatim. -/
theorem r7PocketStopStatement_of_stripSystem_aux37 {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u}
    {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    {Es : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    (haux7 : Sec4.Aux7Statement.{u} (16 / κ)) (hS : StripSys.IsStripSystem κ b jumps P h W' ζ' Es)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {rL rR : ℝ} (hL : -2 < rL) (hR : -2 < rR) (hmax : max rL rR = 16 / κ / 2 - 4)
    (hregR : ∀ ω, IsRegularDriver (Es (constSpec (R7.thetaR (16 / κ) rL)) 0 ω))
    (hregL : ∀ ω, IsRegularDriver (Es (constSpec (R7.thetaL (16 / κ) rR)) 0 ω)) (h𝓦 : 𝓦 ≤ mΩ)
    {R L : Ω → ℝ≥0 → ℂ} {η : Ω → ℝ → ℂ}
    (hRc : ∀ ω, Continuous (R ω)) (hR0 : ∀ ω, R ω 0 = 0) (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t)
    (hRtr : ∀ᵐ ω ∂P, IsGeneratingTrace (Es (constSpec (R7.thetaR (16 / κ) rL)) 0 ω).1 ⊤ (R ω))
    (hLc : ∀ ω, Continuous (L ω)) (hL0 : ∀ ω, L ω 0 = 0) (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t)
    (hLtr : ∀ᵐ ω ∂P, IsGeneratingTrace (Es (constSpec (R7.thetaL (16 / κ) rR)) 0 ω).1 ⊤ (L ω))
    (hηc : ∀ ω, ContinuousOn (η ω) (Ici 0)) (hη0 : ∀ ω, η ω 0 = 0)
    (hηm : ∀ t : ℝ, 0 ≤ t → Measurable fun ω => η ω t)
    (hηtr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (fun t : ℝ≥0 => η ω t))
    (hwalls : ∀ᵐ ω ∂P, IsWallReverseVisit (R ω) (η ω) ∧ IsWallVisited (R ω) (η ω) ∧
      IsWallReverseVisit (L ω) (η ω) ∧ IsWallVisited (L ω) (η ω))
    (hne : ∀ᵐ ω ∂P, range (L ω) ≠ range (R ω))
    (hord : ∀ᵐ ω ∂P, Disjoint (range (R ω)) (leftSideOf (range (L ω))))
    {h₀ : Ω → DistOn upperHalfPlaneOpens} (hh₀ : IsZeroBoundaryGFF upperHalfPlaneOpens h₀ P)
    {u : ℂ → ℝ} (hu : InnerProductSpace.HarmonicOnNhd u H) (hub : ∃ M : ℝ, ∀ z ∈ H, |u z| ≤ M)
    (hin : ∀ q : ℚ, 0 < q → ∀ G : Set Ω, MeasurableSet[𝓦 ⊔ Ito.nullSets P] G → 0 < P G →
      (∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) (StripSys.rt q)) →
      TwoSeedWallsInput (16 / κ) rL rR (𝓦 ⊔ Ito.nullSets P) P R L (StripSys.rt q)
          (fun ω (s : ℝ) => W' s.toNNReal ω) η {ω | ω ∈ G ∧ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} h₀ u ∧
        TwoSeedWallsInputInf (16 / κ) rL rR (𝓦 ⊔ Ito.nullSets P) P R L (StripSys.rt q)
          (fun ω (s : ℝ) => W' s.toNNReal ω) η {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} h₀ u)
    (h513 : ∃ Γ' : Ω → ℝ≥0 → ℂ, (∀ t, StronglyMeasurable[MeasurableSpace.comap
      (fun ω => h₀ ω + smoothDist upperHalfPlaneOpens u) inferInstance] fun ω => Γ' ω t) ∧
      ∀ᵐ ω ∂P, Γ' ω = fun t : ℝ≥0 => η ω t)
    {ε₀ : Type u} [MeasurableSpace ε₀] [StandardBorelSpace ε₀] {E₀ : Ω → ε₀} (hE₀ : Measurable[𝓦] E₀)
    (hgen : 𝓦 ≤ MeasurableSpace.comap E₀ inferInstance ⊔ Ito.nullSets P) :
    R7PocketStopStatement.{u} (16 / κ) rL rR GoodR7 := by
  have hκ := hS.kappa_pos
  have hκ' : 4 < 16 / κ := by rw [lt_div_iff₀ hκ]; linarith [hS.kappa_lt_four]
  obtain ⟨-, hθ1, hθ2, hθ3⟩ := aux131_angles_of_max_eq hκ' hL hR hmax
  have hθR : R7.thetaR (16 / κ) rL ∈ Ico (-(π / 2)) (π / 2) := ⟨hθ1, hθ2.trans_le hθ3⟩
  have hθL : R7.thetaL (16 / κ) rR ∈ Ioc (-(π / 2)) (π / 2) := ⟨hθ1.trans_lt hθ2, hθ3⟩
  have hRm' : ∀ t, Measurable fun ω => R ω t := fun t => (hRm t).mono h𝓦 le_rfl
  have hLm' : ∀ t, Measurable fun ω => L ω t := fun t => (hLm t).mono h𝓦 le_rfl
  exact r7PocketStopStatement_of_stripSystem haux7 hS hcumL hcumR hL hR hmax hregR hregL h𝓦 hRc hR0 hRm hRtr hLc
    hL0 hLm hLtr hηc hη0 hηm hηtr hwalls hne hord
    (hwit_r7 h44 hS hcumL hcumR hθR hθL hregR hregL hRc hR0 hRm' hRtr hLc hL0 hLm' hLtr hηtr hwalls hord)
    (hwitI_r7 h44 hS hcumL hcumR hθR hθL hregR hregL hRc hR0 hRm' hRtr hLc hL0 hLm' hLtr hηtr hwalls hord)
    hh₀ hu hub hin h513 hE₀ hgen

end InteractingSLE.Sec7.Aux37Walls
