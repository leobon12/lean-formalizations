/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.AStopPathCore
import InteractingSLE.Spec.Supplement.OrdModelLeaf

/-!
# Item 6 of `AStopSourceInputs` for the A-stopped second continuation

Packet PROVE-T15-ASTOP-PATH. In the setting of `RLC.OrdModel.RetOrdAStopSourceSndStatement`, on an event `M` of
ordinary pairs (almost surely) carrying one force type of the word `β.1` (angle `θ₂`), for any continuous driver `W`
from `0`, stop set `J ω`, stop `V'` and trace `γ'` with `V' = V`, `γ' = γ` on `[0, V]` (the canonical A-stopped
life and path), the generation `W ↦ γ'` and `J ω = I_A` almost surely on `M` (`J = aStopSet ∘ E` for the outputs of
PROVE-T15-ASTOP-PROC's `AStopProc.exists_sndProcInputs`), **`ae_aStopPath_snd`** proves almost surely on `M`:

* `0 < V'`;
* `V' ≤ thr` (the frozen-threshold time of `W` for the typed word: no threshold before the A-stop, Lemma G7);
* `γ' t ∉ J ω` for `0 < t < V'`;
* at a finite `V'`: either `γ' V' ∈ J ω` (an A-contact), or the continuation ran to the flow line's own
  lifetime `ζ₂` with an end point off `A` (the terminal case, `aStopTerminalSndStatement` in `AStopPathTermWire`).

Inputs used: Aux. 25 (`Theorem15.aux25Statement`, good paths), the live incident bounds of a flow line
(`FCPlumb.ae_live_real_incident_bounds`), its jump avoidance (`RLC.jumpVisitStatement`). No Theorem 1.2/1.3.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory Complex
open scoped NNReal ENNReal

open QuantumZipper (H Hbar chiC)
open LQGMetric (DistOn)

namespace InteractingSLE.RLC.AStopPath

open Supp7 Restart PiecewiseConstantBoundaryData MartChar.RealFlow OrdModel

universe u

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x₁ x₂ θ₁ θ₂ : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {η₁ η₂ : Ω → ℝ≥0 → ℂ}
  {ζ₁ ζ₂ : Ω → ℝ≥0∞} {d : RetData Ω}

/-- **Item 6 of `AStopSourceInputs` for the second continuation, up to the terminal case** (see the module
docstring). -/
theorem ae_aStopPath_snd (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hx : x₂ ≤ x₁) (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    (hd : d.IsMeasGood)
    (hag : ∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
      (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t)
    {β : Ω → BoundaryWord × ℝ}
    (hword : ∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r →
      (β ω).1.IsSorted ∧ (β ω).2 = tipPos d η₁ ω ∧ 0 < (β ω).2 ∧
      IsRetainedWord κ θ₁ θ₂ (η₁ ω) d.u (η₂ ω) d.r (d.inv ω) (β ω).1 ∧
      IsUntouchedWord b jumps (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) (d.inv ω) (β ω).1)
    {M : Set Ω} (hMord : ∀ᵐ ω ∂P, ω ∈ M → IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r)
    {a : RetAux79.ForceWordType}
    (htype : ∀ᵐ ω ∂P, ω ∈ M → (β ω).1 ∈ FCDet.typeSet κ θ₂ a.nL a.nR a.rhoL a.rhoR)
    {W : ℝ≥0 → Ω → ℝ} (hWc : ∀ ω, Continuous (W · ω)) (hW0 : ∀ ω, W 0 ω = 0)
    {J : Ω → Set ℂ} {V' : Ω → ℝ≥0∞} {γ' : Ω → ℝ≥0 → ℂ}
    (hcan : ∀ᵐ ω ∂P, ω ∈ M →
      V' ω = canonRetLife (d.D ω) (d.fwd ω) (η₂ ω) (ζ₂ ω) d.r (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) 0 ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ canonRetLife (d.D ω) (d.fwd ω) (η₂ ω) (ζ₂ ω) d.r
        (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) 0 →
        γ' ω t = canonRetPath (d.D ω) (d.fwd ω) (η₂ ω) (ζ₂ ω) d.r (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) 0 t)
    (hgen : ∀ᵐ ω ∂P, ω ∈ M → IsGeneratingTrace (W · ω) (V' ω) (γ' ω))
    (hE : ∀ᵐ ω ∂P, ω ∈ M →
      J ω = {z : ℂ | z.im = 0 ∧ d.inv ω z ∈ η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r}) :
    (∀ᵐ ω ∂P, ω ∈ M → 0 < V' ω) ∧
    (∀ᵐ ω ∂P, ω ∈ M → V' ω ≤ FCDet.thr a.rhoL a.rhoR W
      (fun ω => FCDet.typeXL κ θ₂ a.nL a.nR a.rhoL a.rhoR (β ω).1)
      (fun ω => FCDet.typeXR κ θ₂ a.nL a.nR a.rhoL a.rhoR (β ω).1) ω) ∧
    (∀ᵐ ω ∂P, ω ∈ M → ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < V' ω → γ' ω t ∉ J ω) ∧
    (∀ᵐ ω ∂P, ω ∈ M → V' ω ≠ ⊤ →
      (contStop (η₂ ω) (ζ₂ ω) d.r (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) = ζ₂ ω ∧
        η₂ ω (ζ₂ ω).toNNReal ∉ η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) ∨
      γ' ω (V' ω).toNNReal ∈ J ω) := by
  have hp₁ := ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₁
  have hp₂ := ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₂
  have hv := FCPlumb.ae_live_real_incident_bounds hκ hκ4 hb hh hη₂
  have hj := RLC.jumpVisitStatement κ hκ hκ4 b jumps hb x₂ θ₂ P h hh η₂ ζ₂ hη₂
  have hF : ∀ᵐ ω ∂P, ω ∈ M → 0 < V' ω ∧
      ¬ ForceWord.ThresholdCondition a.rhoL a.rhoR 0
        (FCDet.typeXL κ θ₂ a.nL a.nR a.rhoL a.rhoR (β ω).1) (FCDet.typeXR κ θ₂ a.nL a.nR a.rhoL a.rhoR (β ω).1) ∧
      (∀ q : ℝ≥0, 0 < q → (q : ℝ≥0∞) < V' ω →
        ¬ ForceWord.ThresholdCondition a.rhoL a.rhoR (W q ω)
          (fun i => Sec7.PocketTraversal.geomLW W
            (fun ω => FCDet.typeXL κ θ₂ a.nL a.nR a.rhoL a.rhoR (β ω).1) i q ω)
          (fun j => Sec7.PocketTraversal.geomRW W
            (fun ω => FCDet.typeXR κ θ₂ a.nL a.nR a.rhoL a.rhoR (β ω).1) j q ω)) ∧
      (∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < V' ω → γ' ω t ∉ J ω) ∧
      (V' ω ≠ ⊤ →
        (contStop (η₂ ω) (ζ₂ ω) d.r (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) = ζ₂ ω ∧
          η₂ ω (ζ₂ ω).toNNReal ∉ η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) ∨
        γ' ω (V' ω).toNNReal ∈ J ω) := by
    filter_upwards [hp₁, hp₂, hv, hj, hag, hword, hMord, htype, hcan, hgen, hE] with ω hp₁ω hp₂ω hvω hjω hagω hwω
      hMω htω hcω hgω hEω hω
    have hord := hMω hω
    obtain ⟨hG, ha₁, ha₂⟩ := hagω hord.1 hord.2.1
    have hS : IsOrdSample d η₁ η₂ ζ₁ ζ₂ x₁ x₂ ω := ⟨hG, hp₁ω, hp₂ω, hx, ha₁, ha₂, hord⟩
    obtain ⟨-, -, -, hret, hunt⟩ := hwω hord
    have hR := hS.isRetCont_snd hd
    have hA := hS.isAChart_snd hd
    obtain ⟨hV, hγ⟩ := hcω hω
    have hg := hgω hω
    have hEq := hEω hω
    have hD := hS.D_eq hd
    rw [hD] at hV hγ
    rw [hV] at hg ⊢
    have hg' := isGeneratingTrace_congr_le hg fun t ht => (hγ t ht).symm
    have hside : ∀ y : ℝ, y ≠ 0 → d.inv ω y ∈ H → d.inv ω y ∉ η₁ ω '' Icc 0 d.u →
        d.inv ω y ∈ η₂ ω '' Icc 0 d.r → (y < 0 → (β ω).1.fn y = -sleLambda κ - θ₂ * chiC κ) ∧
          (0 < y → (β ω).1.fn y = sleLambda κ - θ₂ * chiC κ) := by
      intro y hy0 hyH hyO hyη
      have hne₂ : d.inv ω y ≠ η₂ ω d.r := fun he =>
        hy0 (ofReal_eq_zero.1 (hR.tipUniq _ (by show (0 : ℝ) ≤ (y : ℂ).im; rw [ofReal_im]) he))
      have hne₁ : d.inv ω y ≠ η₁ ω d.u := fun he => hyO (by rw [he]; exact ⟨d.u, ⟨zero_le, le_rfl⟩, rfl⟩)
      exact (hret y hyH hne₂ hne₁ fun hI => hyO hI.1).2.2.1 hyη
    obtain ⟨hpos, hseed, hthr, havoid, hterm⟩ :=
      aStop_facts hR hA hκ hb hunt hvω hjω hside (htω hω) (hWc ω) (hW0 ω) hg'
    refine ⟨hpos, hseed, fun q hq0 hq => hthr q hq0 hq, fun t ht0 ht => ?_, fun hfin => ?_⟩
    · rw [hγ t ht.le, hEq]
      exact havoid t ht0 ht
    · rcases hterm hfin with h1 | h2
      · exact Or.inl h1
      · right
        rw [hγ _ (ENNReal.coe_toNNReal_le_self), hEq]
        exact h2
  refine ⟨hF.mono fun ω h hω => (h hω).1, ?_, hF.mono fun ω h hω => (h hω).2.2.2.1,
    hF.mono fun ω h hω => (h hω).2.2.2.2⟩
  apply RetAux79.life_le_thr_of_retPrelifeNonThreshold hWc
  exact FCPlumb.prelifeNonThreshold_of_boundary_checks hWc hW0
    (fun ω => (FCDet.isOrderedForceWord_typeXL (β ω).1).2.1)
    (fun ω => (FCDet.isOrderedForceWord_typeXL (β ω).1).2.2.2) hgen
    (hF.mono fun ω h hω => (h hω).2.1) (hF.mono fun ω h hω q hq0 hq _ => (h hω).2.2.1 q hq0 hq)

end InteractingSLE.RLC.AStopPath
