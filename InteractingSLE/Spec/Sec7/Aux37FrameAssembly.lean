/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Aux37FrameBounded

/-!
# Aux. lemma 37 in the bounded change pocket: `hwit` from the flat clock and the side germ

Packet PROVE-STRIPSYS40. Specification §6.2, Aux. lemma 37's proof (`source/spec/p193-240.md` L104–L136,
pp. 198–200).

`Aux37Assembly.hwit_hwitI_of_frame` (PROVE-STRIPSYS39) derived `hwit`/`hwitI` from the flat clock and the named
pathwise `Aux37Assembly.WitnessFrameStatement`. In the bounded pocket (`0 < rightLo`, the case of `hwit`) every field of
the witness frame except the two analytic ones is now proved (`Aux37Frame.isRightWitnessFrame_of_germ`,
`isLeftWitnessFrame_of_germ`). What remains is the named statement

* **`PocketSideGermStatement`**: almost surely, at every rational witness on the right (left) arc of the bounded change
  pocket and for every flow chart, some witness point `x ∈ [v, v₂)` has an approach `F ≠ ⊥` below the flow chart's
  approach at `x` with the side germ `IsRightSideGerm` (`IsLeftSideGerm`): the counterflow chart's real limit on the
  traversal side, left of the first right force position (right of the last left one), and the branch relation.

* **`hwit_of_sideGerm`**: `hwit` of `StripPocketPath.pocketWordEvolution_of_stripSystem`, in its exact type, from the
  flat clock (FC), the hypotheses of the proved germs G1/G2 (as in `hwit_hwitI_of_frame`), the realization data the
  consumer already has (the counterflow's trace, the walls' reverse visits, the left frontier `β` through the change
  point, the avoidance `hav`), and `PocketSideGermStatement`. No `WitnessFrameStatement` is used.

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

namespace InteractingSLE.Sec7.Aux37Frame

open WangWu Lemma71I PocketCoord PocketJordan PocketMarks Aux119Bdry Aux119Nested Aux37Germ StripWall
  StripSideHeightProb StripPocketPath Aux37Assembly LocalSets
open Exist.Staged (IsRegularDriver)

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}

/-- **The side germ statement** (Aux. lemma 37's traversal-side claim (PFI3) and branch relation (BR) in the bounded
change pocket; the named analytic input of `hwit_of_sideGerm`): almost surely, for every rational witness on the right
arc (resp. left arc) of the bounded change pocket of `α` and `β^{(q)} = Lr q`, and every flow chart with the pocket on
the left of `α`, some witness point `x ∈ [v, v₂)` has an approach `F ≠ ⊥` below the chart approach at `x` along which
the counterflow chart at `s₂` has a real limit on the traversal side and the branch relation holds
(`IsRightSideGerm` with `α`'s own driver, resp. `IsLeftSideGerm` with `β^{(q)}`'s). -/
def PocketSideGermStatement (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (P : Measure Ω) (W' : ℝ≥0 → Ω → ℝ)
    (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (θ₁ θ₂ : ℝ) (α : Ω → ℝ≥0 → ℂ) (Lr : ℚ → Ω → ℝ≥0 → ℂ)
    (η : Ω → ℝ → ℂ) : Prop :=
  ∀ q : ℚ, 0 < q → ∀ s₁ s₂ v v₁ v₂ : ℚ, ∀ᵐ ω ∂P, IsChangeConfigInc (α ω) (Lr q ω) (StripSys.rt q) →
    0 < rightLo (α ω) (Lr q ω) (StripSys.rt q) → ∀ (Ψ : ℂ → ℂ) (c : Chart),
    IsFlowChart (α ω) (Lr q ω) (StripSys.rt q) Ψ c →
    changePocket (α ω) (Lr q ω) (StripSys.rt q) ⊆ leftSideOf (range (α ω)) →
    (∀ b ∈ chgPts (α ω) (Lr q ω) (StripSys.rt q), b ∉ Icc (v : ℝ) v₂) →
    (Aux37Attach.IsAttachWitness (η ω) (cfPocket (α ω) (Lr q ω) (StripSys.rt q))
        (cfArcR (α ω) (Lr q ω) (StripSys.rt q)) (firstHit (η ω) (cfArcR (α ω) (Lr q ω) (StripSys.rt q) 1))
        (firstHit (η ω) (cfArcR (α ω) (Lr q ω) (StripSys.rt q) 0)) s₁ s₂ v v₁ v₂ →
      ∃ x ∈ Ico (v : ℝ) v₂, ∃ F : Filter ℂ, F.NeBot ∧
        F ≤ map c.2.1 (𝓝[H] ((Ψ (toDisc (realPath (α ω)) (rightPar (α ω) (Lr q ω) (StripSys.rt q) x))).re : ℂ)) ∧
        IsRightSideGerm (fun t : ℝ => W' t.toNNReal ω) (alphaDrv E θ₁ ω) (s₂ : ℝ).toNNReal
          (Sec5.GlueCond.cfPosL κ b jumps (W' · ω) (s₂ : ℝ).toNNReal)
          (Sec5.GlueCond.cfPosR κ b jumps (W' · ω) (s₂ : ℝ).toNNReal)
          (arcTime (rightPar (α ω) (Lr q ω) (StripSys.rt q) x)).toNNReal F) ∧
    (Aux37Attach.IsAttachWitness (η ω) (cfPocket (α ω) (Lr q ω) (StripSys.rt q))
        (cfArcL (α ω) (Lr q ω) (StripSys.rt q)) (firstHit (η ω) (cfArcR (α ω) (Lr q ω) (StripSys.rt q) 1))
        (firstHit (η ω) (cfArcR (α ω) (Lr q ω) (StripSys.rt q) 0)) s₁ s₂ v v₁ v₂ →
      ∃ x ∈ Ico (v : ℝ) v₂, ∃ F : Filter ℂ, F.NeBot ∧
        F ≤ map c.2.1 (𝓝[H] ((Ψ (toDisc (realPath (Lr q ω)) (leftPar (α ω) (Lr q ω) (StripSys.rt q) x))).re : ℂ)) ∧
        IsLeftSideGerm (fun t : ℝ => W' t.toNNReal ω) (betaDrv E (StripSys.rt q) θ₂ ω) (s₂ : ℝ).toNNReal
          (Sec5.GlueCond.cfPosL κ b jumps (W' · ω) (s₂ : ℝ).toNNReal)
          (Sec5.GlueCond.cfPosR κ b jumps (W' · ω) (s₂ : ℝ).toNNReal)
          (arcTime (leftPar (α ω) (Lr q ω) (StripSys.rt q) x)).toNNReal F)

omit mΩ [StandardBorelSpace Ω] in
/-- The counterflow hull of the strip system read from the history is the Loewner hull of its driver, on the regular
paths. -/
theorem cfHull_eq {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {ω : Ω} (hζ : ζ' ω = ⊤) (hw0 : W' 0 ω = 0)
    (hw : Continuous fun t => W' t ω) (t : ℝ≥0) :
    cfHull W' ζ' t ω = negInv '' fwdHull (fun s : ℝ => W' s.toNNReal ω) t := by
  show negInv '' Sec5.GlueCond.hullAt t (Sec5.Cond44Ref.cfHistory W' ζ' ω) = _
  rw [Sec5.GlueCond.hullAt_cfHistory hζ hw0 hw]

open StripPocketPath in
/-- **`hwit` of `StripPocketPath.pocketWordEvolution_of_stripSystem`** (Aux. lemma 37's exclusion of every rational
witness in the bounded change pocket), exactly in its type, from the flat clock (FC) for each pocket's exploration,
the hypotheses of the proved germs (as in `Aux37Assembly.hwit_hwitI_of_frame`), the consumer's realization data
(the counterflow version `η` and its trace, the walls' reverse visits, the left frontier `β` through the change point,
the avoidance `hav`) and the named analytic input `PocketSideGermStatement`. Angles: `θ₁ ∈ (−π/2, π/2)`,
`θ₂ ∈ (−π/2, π/2]`. -/
theorem hwit_of_sideGerm (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
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
    (hav : ∀ᵐ ω ∂P, ∀ q : ℚ, 0 ≤ (q : ℝ) → negInv (η ω q) ∉ leftSideOf (range (β ω)))
    (hgerm : PocketSideGermStatement κ b jumps P W' E θ₁ θ₂ α Lr η) :
    ∀ q : ℚ, 0 < q → ∀ s₁ s₂ v v₁ v₂ : ℚ, ∀ᵐ ω ∂P, IsChangeConfigInc (α ω) (Lr q ω) (StripSys.rt q) →
      0 < rightLo (α ω) (Lr q ω) (StripSys.rt q) →
        ¬ IsPocketWitness (α ω) (Lr q ω) (StripSys.rt q) (η ω) s₁ s₂ v v₁ v₂ := by
  intro q hq s₁ s₂ v v₁ v₂
  by_cases hlt : (s₁ : ℝ) < s₂
  swap
  · refine Eventually.of_forall fun ω _ _ hw => hlt ?_
    rcases hw.1 with h1 | h1
    · exact h1.2.1
    · exact h1.2.1
  have hrs : (s₁ : ℝ).toNNReal ≤ (s₂ : ℝ).toNNReal := Real.toNNReal_le_toNNReal hlt.le
  have htrace := ae_isLoewnerTrace_counterflow hS hcumL hcumR hηtr
  have hreg : ∀ᵐ ω ∂P, ζ' ω = ⊤ ∧ W' 0 ω = 0 ∧ Continuous fun t => W' t ω := by
    filter_upwards [StripPocketPath.ae_counterflow_trace hS hcumL hcumR] with ω hω
    exact ⟨hω.1, hω.2.2.1, hω.2.1⟩
  filter_upwards [ae_noFrame_strip h44 hS hcumL hcumR hθ₁ hθ₂ (StripSys.rt q) hregα (hregβ q hq) hu₀ (hvL q hq)
    (hlocL q hq) hvα hlocα (hgU q hq) (hgL q hq) hgR (hg q hq) (hFC q hq) hrs,
    hgerm q hq s₁ s₂ v v₁ v₂, htrace, hreg, hwalls, hwallsL q hq, hβ, hLβ q hq, hav]
    with ω hno hgω htrω hregω hwω hwLω hβω hLβω havω hconf hpos hwit
  have h0 := zero_notMem_closure_of_rightLo_pos hconf hpos
  obtain ⟨⟨Ψ, c, hF⟩, hCl⟩ := exists_isFlowChart_of_cfAvoid hconf hβω hLβω hwω.2 (hηc ω) havω
  obtain ⟨hnoR, hnoL⟩ := hno Ψ c hF hCl
  obtain ⟨hgR', hgL'⟩ := hgω hconf hpos Ψ c hF hCl hwit.2
  have hW0 : (fun s : ℝ => W' s.toNNReal ω) 0 = 0 := by simpa using htrω.2.2
  have hP := hconf.isReversePocket_of_counterflow h0 htrω.1 htrω.2.1 hW0 hwω.1 hwLω hwω.2
  have he : ∀ t : ℝ≥0, cfHull W' ζ' t ω = negInv '' fwdHull (fun s : ℝ => W' s.toNNReal ω) t :=
    cfHull_eq hregω.1 hregω.2.1 hregω.2.2
  have hs₁ : (((s₁ : ℝ).toNNReal : ℝ≥0) : ℝ) = s₁ := by
    refine Real.coe_toNNReal _ (hP.nonneg.trans ?_)
    rcases hwit.1 with h1 | h1
    · exact h1.1
    · exact h1.1
  have hs₂ : (((s₂ : ℝ).toNNReal : ℝ≥0) : ℝ) = s₂ := Real.coe_toNNReal _ ((hs₁ ▸ NNReal.coe_nonneg _).trans hlt.le)
  rcases hwit.1 with hwR | hwL
  · obtain ⟨x, hx, F, hFne, hFG, hgm⟩ := hgR' hwR
    have hwR' : Aux37Attach.IsAttachWitness (η ω) (cfPocket (α ω) (Lr q ω) (StripSys.rt q))
        (cfArcR (α ω) (Lr q ω) (StripSys.rt q)) (firstHit (η ω) (cfArcR (α ω) (Lr q ω) (StripSys.rt q) 1))
        (firstHit (η ω) (cfArcR (α ω) (Lr q ω) (StripSys.rt q) 0)) ((s₁ : ℝ).toNNReal : ℝ) ((s₂ : ℝ).toNNReal : ℝ)
        v v₁ v₂ := by rw [hs₁, hs₂]; exact hwR
    have hfr := isRightWitnessFrame_of_germ (hFne := hFne) hconf h0 htrω.1 htrω.2.1 hW0 hwω.1 hwLω hwω.2 hF hwR'
      hwit.2 hx hFG hgm
    refine hnoR ?_
    simp only [stripExpl, wallUnion, he]
    exact hfr
  · obtain ⟨x, hx, F, hFne, hFG, hgm⟩ := hgL' hwL
    have hwL' : Aux37Attach.IsAttachWitness (η ω) (cfPocket (α ω) (Lr q ω) (StripSys.rt q))
        (cfArcL (α ω) (Lr q ω) (StripSys.rt q)) (firstHit (η ω) (cfArcR (α ω) (Lr q ω) (StripSys.rt q) 1))
        (firstHit (η ω) (cfArcR (α ω) (Lr q ω) (StripSys.rt q) 0)) ((s₁ : ℝ).toNNReal : ℝ) ((s₂ : ℝ).toNNReal : ℝ)
        v v₁ v₂ := by rw [hs₁, hs₂]; exact hwL
    have hfr := isLeftWitnessFrame_of_germ (hFne := hFne) hconf h0 htrω.1 htrω.2.1 hW0 hwω.1 hwLω hwω.2 hF hwL'
      hwit.2 hx hFG hgm
    refine hnoL ?_
    simp only [stripExpl, wallUnion, he]
    exact hfr

end InteractingSLE.Sec7.Aux37Frame
