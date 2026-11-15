/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1RestartPair

/-!
# GW1: the next piece is simple from the current launch clock alone

This localizes the landed per-piece argument. It needs no launch clock at any
later instruction and hence is available before constructing the next pair.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW1RestartPair

open Exist.Staged Exist.StagedLaw GW1Z

/-- The first-visit proof for one launch, using only that launch's complete pair.
GB6 is the only additional conditional counterflow-kernel input. -/
theorem ae_isSimplePiece_of_isLaunchClock
    (hGB6 : Supp8.GB6.GB6RestartStatement.{u})
    (hT13 : Exist.Theorem13Statement.{u}) (hT13₀ : Exist.Theorem13Statement.{0})
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {right : Bool}
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    {W' V : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {ℓ : Ω → ℝ≥0 → ℝ≥0}
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hS : IsStagedHistory κ b jumps P h (walkSpec b jumps right) E)
    (hreg : ∀ j ω, IsRegularDriver (E j ω))
    (hRs : StagedPiecesRegular κ b jumps P (walkSpec b jumps right) E) {k : ℕ}
    (hD : IsLaunchClock κ b jumps P h W' (walkSpec b jumps right) E k V ζ ℓ) :
    ∀ᵐ ω ∂P, ∀ c θ,
      (ExplState.run κ b jumps (walkSpec b jumps right) (fun j => E j ω) (k + 1)).2.2.2.1 k =
        some (c, θ) →
      IsSimplePiece c (E k ω).1 (min (instrTime (walkSpec b jumps right) k) (E k ω).2)
        (SB.prefixPhysSet κ b jumps (walkSpec b jumps right) (fun j => E j ω) k) := by
  have hGW0 : GW0.GW0ForwardStatement.{u} := BR3Ref.gw0ForwardStatement_of_theorem13 hT13₀
  obtain ⟨hWm, hD1, hD2⟩ := hD
  let spec := walkSpec b jumps right
  let L : Set Ω := {ω | (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none}
  have hL : MeasurableSet[pastSigma κ b jumps spec E k] L :=
    GW1W.measurableSet_pastSigma_launch hb spec hS.1 hreg k
  let M := PieceVisitEvent (E k) (fun ω => min (instrTime spec k) (E k ω).2) V
  have hM : MeasurableSet M := measurableSet_pieceVisitEvent (hS.1 k)
    (measurable_const.min (measurable_snd.comp (hS.1 k))) hWm
  have hker : ∀ᵐ ω₀ ∂P, ω₀ ∈ L →
      ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E k) ω₀), ω ∈ M := by
    filter_upwards [hS.2.2.2 k, hD1] with ω₀ hst hd1 hω₀
    obtain ⟨⟨c, θ⟩, hl⟩ := Option.ne_none_iff_exists'.1 hω₀
    obtain ⟨b', jumps', h', hb', htr, hfl⟩ := hst c θ hl
    obtain ⟨hV, hζ⟩ := hd1 c θ hl h' htr
    have hθ : θ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) :=
      angle_walkSpec_mem (eq_launch_of_launches spec _ hl).1
    exact ae_mem_pieceVisitEvent hGB6 hGW0 hT13 hκ hκ4 hθ hb' hfl
      (Eventually.of_forall fun ω => (hreg k ω).2.2.2) hV hζ (instrTime spec k)
  have hP := GW2Later.ae_of_ae_condExpKernel_on' (hS.2.1 k) hL hM hker
  filter_upwards [hP, hRs, hD2] with ω hPω hRω hDω c θ hl
  have hωM : ω ∈ M := hPω (by
    change (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none
    rw [hl]; exact Option.some_ne_none _)
  have hk := (eq_launch_of_launches spec _ hl).1
  obtain ⟨hw0, hwc, η, hη, hηtr⟩ := hRω k θ (instrTime spec k) c hk hl
  obtain ⟨-, hVc, hV0, ⟨γ, hγ, hγtr⟩, -, -, hrange, hiff⟩ := hDω c θ hl
  have hregω : ∀ j c' θ',
      (ExplState.run κ b jumps spec (fun j => E j ω) (j + 1)).2.2.2.1 j = some (c', θ') →
      GW1P.PieceRegular (E j ω).1 (min (instrTime spec j) (E j ω).2) := by
    intro j c' θ' hl'
    exact hRω j θ' (instrTime spec j) c' (eq_launch_of_launches spec _ hl').1 hl'
  obtain ⟨f, C, hf, hC, hfib⟩ := chartFiberStatement κ b jumps spec (fun j => E j ω) hregω k c θ hl
  have hwlt : ContinuousOn (E k ω).1 {s | (s : ℝ≥0∞) < min (instrTime spec k) (E k ω).2} :=
    hwc.mono fun _ (hs : (_ : ℝ≥0∞) < _) => (le_of_lt hs : (_ : ℝ≥0∞) ≤ _)
  have hA : ∀ q : ℚ, (rt q : ℝ≥0∞) < min (instrTime spec k) (E k ω).2 →
      LP.traceAt (rt q) (E k ω).1 = η (rt q) := fun _ hq =>
    LP.traceAt_eq_of_isGeneratingTrace hη hwlt hw0 hq
  have hγc : Continuous γ := by
    have hc := hγ.2.1
    simp only [le_top, ofPred_true] at hc
    exact continuousOn_univ.1 hc
  have hG : ∀ r : ℚ, LP.traceAt (rt r) (fun s => V s ω) = γ (rt r) := fun _ =>
    LP.traceAt_eq_of_isGeneratingTrace hγ hVc.continuousOn hV0 ENNReal.coe_lt_top
  have hinj := injOn_of_sepAt hη.2.1 hA hωM.1
  have hvis := visit_of_visAt hη.2.1 hη.1 hinj hγc hγtr hA hG hωM.2
  obtain ⟨hinj', havoid⟩ :=
    piece_simple_of_visit hf hfib hη hwc hw0 hγ hVc hV0 hvis hinj (notMem_of_clock hrange hiff)
  exact ⟨f, η, C, hf, hC, hw0, hwc, hη, hηtr, hinj', havoid⟩

end InteractingSLE.Theorem14.GW1RestartPair
