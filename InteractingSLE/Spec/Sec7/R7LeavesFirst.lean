/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7LeavesStrip
import InteractingSLE.Spec.Sec5.RestartGenReflect

/-!
# Theorem R.7's extremal pockets: the wall first exits from Lemma 4.7

Packet PROVE-R7-LEAVES. The rational first exits `firstR`, `firstL` of `R7Leaves.R7ExtremalCore` (Lemma 5.7 in the
inversion chart for the two constant-angle walls; PROVE-WALLS-PATH's `hfirstR`, `hfirstL`) are proved here for the R.7
field from Lemma 4.7 in chart `Q`, through PROVE-RESTART-GEN's one-angle restart laws
(`Sec5.RestartGen.ae_isFirstHitQ_of_isFlowLine_heights` at an interior relative angle,
`…_pi_div_two` at `π/2`, `…_neg_pi_div_two` at `−π/2` by reflection). For extremal pairs both wall angles lie in
`[−π/2, π/2]`, so no other input is needed.

* `firstHit_r7`: the rational first exit of a version of any angle-`θ` flow line (`θ ∈ [−π/2, π/2]`) of the R.7 field;
* `R7ExtremalSideDet`, `R7ExtremalSideDetRemaining`, `r7ExtremalCoreRemaining_of_sideDet`: the extremal remaining
  inputs reduced to the two-seed side limits and Proposition 5.13 for the counterflow.

R48: the only named inputs are Proposition 4.11 in chart `Q` and Lemma 4.7 (at relative angles `π/2` and interior
`θ`), both inputs of Theorem 1.2's chain proved from Zhan's Part A; nothing uses Theorem 1.2/1.3 or any `*_of_param`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric Function
open LQGMetric (DistOn IsZeroBoundaryGFF)
open QuantumZipper (H Hbar chiC)
open SupercriticalConformalCovariance.GM24 (smoothDist)
open InteractingSLE.WangWu (negInv)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec7.R7Leaves

open R7Outer Sec5.Prop55Half WangWu WholeField Lemma71C Lemma71I PocketCoord PocketJordan PocketMarks
  PocketWordAssembly PocketSeedOpen PocketStopField PocketStopWallsFin PocketStopWalls PocketCoupling
  StripPocketConfig PocketWordPerQ PocketStop R7Aux131 R7Pocket RefWire

/-! ### The first exits -/

section First

variable {k rL rR c c' : ℝ} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}

/-- **Lemma 5.7's rational first exit for a flow line of the R.7 field** (angle `θ ∈ [−π/2, π/2]`): almost surely the
centred counterflow (any version `η` of its trace, `η 0 = 0`) first hits the inverted prefix `m(γ((0, q]))` of an
almost surely simple flow line `γ` at its tip `m(γ(q))`. From Lemma 4.7 at the relative angle `θ`
(`Sec5.Prop411Q.Lemma47QHitStatement` at `π/2`, by reflection at `−π/2`, `h47T` in between). -/
theorem firstHit_r7 (h411 : Sec5.Cond44Ref.Prop411QStatement.{u}) (h47 : Sec5.Prop411Q.Lemma47QHitStatement.{u})
    (h47T : ∀ θ : ℝ, -(π / 2) < θ → θ < π / 2 → Sec5.RestartGen.Lemma47QHitTStatement.{u} θ)
    (hk4 : 4 < k) (hc : 0 ≤ c) (hc' : 0 ≤ c')
    (hh : IsGFFWithBoundaryData P h (prop74Data (r7A k rR + c) (r7B k rL + c')) ((({0} : Finset ℝ)) : Set ℝ))
    (hcf : IsCenteredCounterflowDriver (16 / k) P h W' ζ') {θ : ℝ} (hθ : θ ∈ Icc (-(π / 2)) (π / 2))
    {γ : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (hfl : IsFlowLine (16 / k) (prop74Data (r7A k rR + c) (r7B k rL + c')) {0} 0 θ P h γ ζ)
    (hγs : ∀ᵐ ω ∂P, IsSimpleProper (γ ω)) {η : Ω → ℝ → ℂ} (hη0 : ∀ ω, η ω 0 = 0)
    (hηtr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (fun t : ℝ≥0 => η ω t)) :
    ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, ∃ T : ℝ,
      Sec4.IsFirstHitPoint (η ω) T (negInv '' (γ ω '' Ioc 0 (StripSys.rt q))) (negInv (γ ω (StripSys.rt q))) := by
  intro q hq
  have hκ : 0 < 16 / k := R7.sixteen_div_pos (by linarith)
  have hκ4 : 16 / k < 4 := R7.sixteen_div_lt_four hk4
  have hχ := Sec4.chiC_pos hκ hκ4
  have hb := isPiecewiseConstant_prop74Data (r7A k rR + c) (r7B k rL + c')
  have href := Sec5.Cond44Ref.cond44ReferenceStatement_of_prop411Q h411
  have hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤ := (ae_counterflow_trace_r7 hk4 hc hc' hh hcf).mono fun ω hω => hω.1
  have hπ := isHeightBounded44_r7 (c := c) (c' := c') hk4 hc hc' (pi_div_two_mem_r7 k rL rR)
  have hQ : ∀ᵐ ω ∂P, Sec5.Prop411Q.IsFirstHitQ (Lemma71I.realPath (γ ω))
      (fun s : ℝ => (fun t : ℝ≥0 => η ω t) s.toNNReal) q := by
    rcases eq_or_lt_of_le hθ.1 with hθm | hθm
    · subst hθm
      have hhi : π / 2 * chiC (16 / k) ≤ r7ThetaHi k rR * chiC (16 / k) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) hχ.le
      have hlo : r7ThetaLo k rL * chiC (16 / k) ≤ -(π / 2) * chiC (16 / k) :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) hχ.le
      have hpχ : 0 ≤ π * chiC (16 / k) := mul_nonneg Real.pi_pos.le hχ.le
      have hA : sleLambda (16 / k) - π / 2 * chiC (16 / k) ≤ r7A k rR + c := by simp only [r7A]; linarith
      have hB : sleLambda (16 / k) - π / 2 * chiC (16 / k) ≤ r7B k rL + c' := by simp only [r7B]; linarith
      exact Sec5.RestartGen.ae_isFirstHitQ_of_isFlowLine_neg_pi_div_two h47 href hκ hκ4 hb
        (isHeightBounded44_refl_prop74Data hA hB) hh hcf hζ' hηtr hfl q hq
    · rcases eq_or_lt_of_le hθ.2 with hθp | hθp
      · subst hθp
        exact Sec5.RestartGen.ae_isFirstHitQ_of_isFlowLine_pi_div_two h47 href hκ hκ4 hb hπ hh hcf hζ' hηtr hfl q hq
      · exact Sec5.RestartGen.ae_isFirstHitQ_of_isFlowLine_heights (h47T θ hθm hθp) href hκ hκ4 hb
          (isHeightBounded44_r7 hk4 hc hc' ⟨(min_le_right _ _).trans hθ.1, hθ.2.trans (le_max_right _ _)⟩) hπ
          hh hcf hζ' hηtr hfl q hq
  filter_upwards [hQ, hγs] with ω hω hsω
  exact Sec5.RestartGen.isFirstHitPoint_rt hq (Sec5.RestartGen.ne_zero_of_isSimpleProper hsω) (hη0 ω)
    (Sec5.RestartGen.isFirstHitQ_real_of_toNNReal (by exact_mod_cast hq) hω)

end First

/-! ### The extremal remaining inputs reduced to the side limits and Proposition 5.13 -/

section SideDet

/-- **The side and determination inputs** (the `R7ExtremalCore` other than the first exits) on versions `R`, `L`,
`η`: the two-seed side limits and Proposition 5.13 for the counterflow. -/
structure R7ExtremalSideDet (k rL rR : ℝ) {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (W' : ℝ≥0 → Ω → ℝ)
    (ζ' : Ω → ℝ≥0∞) (h'' : Ω → DistOn upperHalfPlaneOpens) (u₀' : ℂ → ℝ) (R L : Ω → ℝ≥0 → ℂ)
    (η : Ω → ℝ → ℂ) : Prop where
  side : ∀ q : ℚ, 0 < q → ∀ G : Set Ω, MeasurableSet[wallsSigma P R L] G → 0 < P G →
    (∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) (StripSys.rt q)) →
    (∀ ω ∈ G, ζ' ω = ⊤) →
    (∀ ω ∈ G, 0 < rightLo (R ω) (L ω) (StripSys.rt q) →
      IsCfPocketConfig (R ω) (L ω) (StripSys.rt q) (fun s : ℝ => W' s.toNNReal ω) (η ω)) →
    (∀ ω ∈ G, rightLo (R ω) (L ω) (StripSys.rt q) = 0 →
      IsCfPocketConfigInf (R ω) (L ω) (StripSys.rt q) (fun s : ℝ => W' s.toNNReal ω) (η ω)) →
    TwoSeedSideInput k rL rR (wallsSigma P R L) P R L (StripSys.rt q) η
        {ω | ω ∈ G ∧ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} (centredField h'' u₀') u₀' ∧
      TwoSeedSideInputInf k rL rR (wallsSigma P R L) P R L (StripSys.rt q) η
        {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} (centredField h'' u₀') u₀'
  det : ∃ Γ' : Ω → ℝ≥0 → ℂ, (∀ t, StronglyMeasurable[MeasurableSpace.comap h'' inferInstance]
    fun ω => Γ' ω t) ∧ ∀ᵐ ω ∂P, Γ' ω = fun t : ℝ≥0 => η ω t

/-- **The side and determination inputs on every configuration** (heights `c`, `c′`), as in `R7ExtremalRemaining`. -/
def R7ExtremalSideDetRemaining (k rL rR c c' : ℝ) : Prop :=
  ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞)
    (αR βR βL αL : Ω → ℝ≥0 → ℂ) (ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞),
    IsR7OuterConfig k rL rR c c' P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL →
    ∀ (b' : ℝ → ℝ) (J' : Finset ℝ) (h' h'' : Ω → DistOn upperHalfPlaneOpens) (𝓕 : Filtration ℝ≥0 mΩ)
      (VL : Fin (flowLineNL b' J' 0) → ℝ≥0 → Ω → ℝ) (VR : Fin (flowLineNR b' J' 0) → ℝ≥0 → Ω → ℝ)
      (B : ℝ≥0 → Ω → ℝ), IsCfDecomp k P h W' ζ' b' J' h' h'' 𝓕 VL VR B →
    ∀ u₀' : ℂ → ℝ, IsBoundedHarmonicExtension (forceBoundaryData k (flowLineRhoL k b' J' 0 0)
      (flowLineRhoR k b' J' 0 0) (flowLineXL b' J' 0) (flowLineXR b' J' 0))
      (forceJumpSet (flowLineXL b' J' 0) (flowLineXR b' J' 0)) u₀' →
    ∀ (R L : Ω → ℝ≥0 → ℂ) (η : Ω → ℝ → ℂ), IsR7Versions P W' αR αL R L η →
      R7ExtremalSideDet k rL rR P W' ζ' h'' u₀' R L η

/-- **The core extremal inputs from the side limits and Proposition 5.13**: the first exits are `firstHit_r7` for the
two walls (both angles in `[−π/2, π/2]` for extremal pairs, `R7Aux131.aux131_angles_of_max_eq`). -/
theorem r7ExtremalCoreRemaining_of_sideDet (h411 : Sec5.Cond44Ref.Prop411QStatement.{u})
    (h47 : Sec5.Prop411Q.Lemma47QHitStatement.{u})
    (h47T : ∀ θ : ℝ, -(π / 2) < θ → θ < π / 2 → Sec5.RestartGen.Lemma47QHitTStatement.{u} θ)
    {k rL rR c c' : ℝ} (hk4 : 4 < k) (hL : -2 < rL) (hR : -2 < rR) (hmax : max rL rR = k / 2 - 4)
    (hc : 0 ≤ c) (hc' : 0 ≤ c') (hsd : R7ExtremalSideDetRemaining.{u} k rL rR c c') :
    R7ExtremalCoreRemaining.{u} k rL rR c c' := by
  intro Ω mΩ hSB P hP h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg b' J' h' h'' 𝓕 VL VR B hD u₀' hu₀' R L η hV
  have hsdω := hsd P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg b' J' h' h'' 𝓕 VL VR B hD u₀' hu₀' R L η hV
  obtain ⟨-, hθ1, hθ2, hθ3⟩ := aux131_angles_of_max_eq hk4 hL hR hmax
  have hreg := hcfg.regular
  have hRs : ∀ᵐ ω ∂P, IsSimpleProper (R ω) := by
    filter_upwards [hreg, hV.R_ae] with ω hω he
    rw [he]; exact R7Outer.IsSeedProper.isSimpleProper hω.1
  have hLs : ∀ᵐ ω ∂P, IsSimpleProper (L ω) := by
    filter_upwards [hreg, hV.L_ae] with ω hω he
    rw [he]; exact R7Outer.IsSeedProper.isSimpleProper hω.2.2.2.1
  have hflR := IsFlowLine.congr_path (η' := R) hcfg.flow_αR (hV.R_ae.mono fun ω hω t _ => by rw [hω])
  have hflL := IsFlowLine.congr_path (η' := L) hcfg.flow_αL (hV.L_ae.mono fun ω hω t _ => by rw [hω])
  exact ⟨firstHit_r7 h411 h47 h47T hk4 hc hc' hcfg.gff hcfg.counterflow ⟨hθ1, hθ2.le.trans hθ3⟩ hflR hRs
      hV.η_zero hV.η_trace,
    firstHit_r7 h411 h47 h47T hk4 hc hc' hcfg.gff hcfg.counterflow ⟨hθ1.trans hθ2.le, hθ3⟩ hflL hLs
      hV.η_zero hV.η_trace,
    hsdω.side, hsdω.det⟩

end SideDet

end InteractingSLE.Sec7.R7Leaves
