/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.AStopSafeFstLaw
import InteractingSLE.Spec.Supplement.AStopSafeSnd
import InteractingSLE.Spec.Supplement.OrdModelSeed

/-!
# `RetOrdAStopSourceFstSeedStatement` from the pathwise A-stop facts

Packet PROVE-T15-ASTOP-SAFE. Items 1–5 of `RLC.OrdModel.AStopSourceInputs` for the A-stopped first continuation at its
seed `(β ω).2` are proved: item 1 (PROVE-T15-ASTOP-PART's `exists_ordTypePartition_fst`), items 2–3
(PROVE-T15-ASTOP-PROC's `exists_subset_isFstGood`, `exists_fstProc`, `exists_retEnds_seed`), item 4
(`AStopSafe.integrable_pairing_ord_fst`), item 5 (`AStopSafe.hasSafe_aStop_fst`). Item 6 (PROVE-T15-ASTOP-PATH) is
stated in source terms:

* `AStopPathFstStatement` (**not proved here**): for the canonical retained lifetime `V` (chart translated by the first
  tip's position) and path `γ = canonRetPath … − (β ω).2` of the first flow line, on an event of ordinary pairs on which
  the seeded stop word `shiftW (β ω).2 (β ω).1` has one force type for `θ₁`, for every continuous driver from `0`
  generating `γ` up to `V`: `0 < V`, `V ≤ thr`, the path avoids the translated chart reals over `A` strictly between `0`
  and `V`, and at a finite `V` either `V = thr` or `γ V` is such a point;
* **`exists_aStopSourceInputs_fst`**, **`retOrdAStopSourceFstSeedStatement_of_path`**;
* **`retOrdDetStatement_of_lemma75_path`**: Theorem 1.5's leaf 3 (`RLC.RetOrdDetStatement`) from Lemma 7.5, Theorem 1.3
  and the two pathwise statements (ASTOP2's `retOrdDetStatement_of_source`).

Uses Lemma 7.5 (and Theorem 1.3 only in the last theorem, for Theorem 1.5; R48).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.RLC.AStopSafe

open Restart Restart.RetAux79 Supp7 Sec7 Sec7.Lemma76F AStopProc OrdModel FCDet
open Exist.StagedLaw.BoundaryWord

universe u

/-- **Item 6 of `AStopSourceInputs` for the A-stopped first continuation at its seed, in source terms**
(PROVE-T15-ASTOP-PATH's target; see the module docstring). **Not proved in this file.** -/
def AStopPathFstStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ ≤ x₁ → θ₁ < θ₂ →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
    ∀ (d : RetData Ω) (hd : d.IsMeasGood),
      (∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
        (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t) →
    ∀ u₀ : ℂ → ℝ, IsBoundedHarmonicExtension b jumps u₀ →
    ∀ β : Ω → BoundaryWord × ℝ, Measurable[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r] β →
      IsRetMeanIdentOn κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd
        {ω | IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r} (fun ω => (β ω).1) →
      (∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r →
        (β ω).1.IsSorted ∧ (β ω).2 = tipPos d η₁ ω ∧ 0 < (β ω).2 ∧
        IsRetainedWord κ θ₁ θ₂ (η₁ ω) d.u (η₂ ω) d.r (d.inv ω) (β ω).1 ∧
        IsUntouchedWord b jumps (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) (d.inv ω) (β ω).1) →
    ∀ (a : ForceWordType) (M : Set Ω),
      (∀ᵐ ω ∂P, ω ∈ M → IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r) →
      (∀ ω ∈ M, shiftW (β ω).2 (β ω).1 ∈ typeSet κ θ₁ a.nL a.nR a.rhoL a.rhoR) →
    ∀ W : ℝ≥0 → Ω → ℝ, (∀ ω, Continuous (W · ω)) → (∀ ω, W 0 ω = 0) →
      (∀ᵐ ω ∂P, ω ∈ M → IsGeneratingTrace (W · ω)
        (canonRetLife (d.D ω) (d.fwd ω) (η₁ ω) (ζ₁ ω) d.u (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) (tipPos d η₁ ω))
        (fun t => canonRetPath (d.D ω) (d.fwd ω) (η₁ ω) (ζ₁ ω) d.u (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r)
          (tipPos d η₁ ω) t - (β ω).2)) →
      (∀ᵐ ω ∂P, ω ∈ M → 0 < canonRetLife (d.D ω) (d.fwd ω) (η₁ ω) (ζ₁ ω) d.u
        (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) (tipPos d η₁ ω)) ∧
      (∀ᵐ ω ∂P, ω ∈ M → canonRetLife (d.D ω) (d.fwd ω) (η₁ ω) (ζ₁ ω) d.u
          (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) (tipPos d η₁ ω) ≤
        thr a.rhoL a.rhoR W (fun ω => typeXL κ θ₁ a.nL a.nR a.rhoL a.rhoR (shiftW (β ω).2 (β ω).1))
          (fun ω => typeXR κ θ₁ a.nL a.nR a.rhoL a.rhoR (shiftW (β ω).2 (β ω).1)) ω) ∧
      (∀ᵐ ω ∂P, ω ∈ M → ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < canonRetLife (d.D ω) (d.fwd ω) (η₁ ω) (ζ₁ ω) d.u
          (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) (tipPos d η₁ ω) →
        canonRetPath (d.D ω) (d.fwd ω) (η₁ ω) (ζ₁ ω) d.u (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r)
            (tipPos d η₁ ω) t - (β ω).2 ∉
          {z : ℂ | z.im = 0 ∧ d.inv ω (z + (β ω).2) ∈ η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r}) ∧
      (∀ᵐ ω ∂P, ω ∈ M → canonRetLife (d.D ω) (d.fwd ω) (η₁ ω) (ζ₁ ω) d.u
          (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) (tipPos d η₁ ω) ≠ ⊤ →
        canonRetLife (d.D ω) (d.fwd ω) (η₁ ω) (ζ₁ ω) d.u (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r)
            (tipPos d η₁ ω) =
          thr a.rhoL a.rhoR W (fun ω => typeXL κ θ₁ a.nL a.nR a.rhoL a.rhoR (shiftW (β ω).2 (β ω).1))
            (fun ω => typeXR κ θ₁ a.nL a.nR a.rhoL a.rhoR (shiftW (β ω).2 (β ω).1)) ω ∨
        canonRetPath (d.D ω) (d.fwd ω) (η₁ ω) (ζ₁ ω) d.u (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) (tipPos d η₁ ω)
            (canonRetLife (d.D ω) (d.fwd ω) (η₁ ω) (ζ₁ ω) d.u (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r)
              (tipPos d η₁ ω)).toNNReal - (β ω).2 ∈
          {z : ℂ | z.im = 0 ∧ d.inv ω (z + (β ω).2) ∈ η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r})

section Assembly

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x₁ x₂ θ₁ θ₂ : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {η₁ η₂ : Ω → ℝ≥0 → ℂ}
  {ζ₁ ζ₂ : Ω → ℝ≥0∞}

/-- **All of `AStopSourceInputs` for the A-stopped first continuation at its seed on a part of the type partition**
(up to a null set), from Lemma 7.5 and the pathwise A-stop facts `AStopPathFstStatement`. -/
theorem exists_aStopSourceInputs_fst (hL75 : Theorem15.Lemma75Statement.{u})
    (hpath : AStopPathFstStatement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hx : x₂ ≤ x₁) (hθ : θ₁ < θ₂)
    (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    {d : RetData Ω} (hd : d.IsMeasGood)
    (hag : ∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
      (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) {β : Ω → BoundaryWord × ℝ}
    (hβ : Measurable[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r] β)
    (hmean : IsRetMeanIdentOn κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd
      {ω | IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r} (fun ω => (β ω).1))
    (hword : ∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r →
      (β ω).1.IsSorted ∧ (β ω).2 = tipPos d η₁ ω ∧ 0 < (β ω).2 ∧
      IsRetainedWord κ θ₁ θ₂ (η₁ ω) d.u (η₂ ω) d.r (d.inv ω) (β ω).1 ∧
      IsUntouchedWord b jumps (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) (d.inv ω) (β ω).1)
    {M : Set Ω} (hM : MeasurableSet[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r] M)
    (hMord : ∀ᵐ ω ∂P, ω ∈ M → IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r)
    (a : ForceWordType) (htype : ∀ ω ∈ M, shiftW (β ω).2 (β ω).1 ∈ typeSet κ θ₁ a.nL a.nR a.rhoL a.rhoR) :
    ∃ M' ⊆ M, MeasurableSet[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r] M' ∧ (∀ᵐ ω ∂P, ω ∈ M → ω ∈ M') ∧
      AStopSourceInputs κ θ₁ P M' (fun ω => (β ω).2) (fun ω => shiftW (β ω).2 (β ω).1)
        (fun ω => Exist.flowField (β ω).2 0 (hd.chartField κ h ω))
        (fun ω => canonRetLife (d.D ω) (d.fwd ω) (η₁ ω) (ζ₁ ω) d.u (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r)
          (tipPos d η₁ ω))
        (fun ω t => canonRetPath (d.D ω) (d.fwd ω) (η₁ ω) (ζ₁ ω) d.u (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r)
          (tipPos d η₁ ω) t - (β ω).2) := by
  have hτm : Measurable[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r] fun ω => (β ω).2 := hβ.snd
  have hτ : ∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r → (β ω).2 = tipPos d η₁ ω := by
    filter_upwards [hword] with ω hw hord using (hw hord).2.1
  obtain ⟨η₁', hm₁, ha₁⟩ := exists_measurable_version_of_isFlowLine hη₁
  obtain ⟨M', hM'M, hM', hMM', hMg⟩ := exists_subset_isFstGood hκ hκ4 hη₁ hd hag ha₁ (x₁ := x₁)
    (τ := fun ω => (β ω).2) hτ hM hMord
  obtain ⟨E, hEm, hE⟩ := exists_retEnds_seed hL75 hκ hκ4 hb hx hh hη₁ hη₂ hd hag hτm
  obtain ⟨𝓗, W, V', γ', h0, hWc, hW0, hWa, hV, hγm, hγc, hγ0, hcan, hgen, ⟨hQa, h𝓗⟩, hV', hγ', -⟩ :=
    exists_fstProc hL75 hκ hκ4 hb hh hη₁ hη₂ hd hag hm₁ ha₁ hτm hM' hMg
  have hMord' : ∀ᵐ ω ∂P, ω ∈ M' → IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r := by
    filter_upwards [hMord] with ω hω hω' using hω (hM'M hω')
  have htype' : ∀ ω ∈ M', shiftW (β ω).2 (β ω).1 ∈ typeSet κ θ₁ a.nL a.nR a.rhoL a.rhoR := fun ω hω =>
    htype ω (hM'M hω)
  have hsort : ∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r → (β ω).1.IsSorted := by
    filter_upwards [hword] with ω hw hord using (hw hord).1
  have hgen' : ∀ ω ∈ M', IsGeneratingTrace (W · ω)
      (aLife (fstChart d (fun ω => (β ω).2) η₁' ζ₁) (fstLifeP d η₁' ζ₁) ω)
      (aPath (fstChart d (fun ω => (β ω).2) η₁' ζ₁) (fstLifeP d η₁' ζ₁) ω) := by
    intro ω hω
    have hg := hgen ω hω
    rw [hV', hγ', indicator_of_mem hω, aTrace_of_mem hω] at hg
    exact hg
  obtain ⟨hS, hL⟩ := hasSafe_aStop_fst hL75 hκ hκ4 hb hx hθ hh hη₁ hη₂ hd hag hu₀ hmean hsort hτm hm₁ ha₁ hM'
    hMg hMord' a htype' hWc hW0 hgen' hQa
  have hcan' := Eventually.of_forall (f := ae P) hcan
  have hgenc : ∀ᵐ ω ∂P, ω ∈ M' → IsGeneratingTrace (W · ω)
      (canonRetLife (d.D ω) (d.fwd ω) (η₁ ω) (ζ₁ ω) d.u (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) (tipPos d η₁ ω))
      (fun t => canonRetPath (d.D ω) (d.fwd ω) (η₁ ω) (ζ₁ ω) d.u (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r)
        (tipPos d η₁ ω) t - (β ω).2) := by
    filter_upwards [hcan'] with ω hc hω
    obtain ⟨hl, hp⟩ := hc hω
    have hg := hgen ω hω
    rw [hl] at hg
    exact Restart.isGeneratingTrace_congr_le hg fun t ht => (hp t ht).symm
  obtain ⟨hpos, hthr, hoff, hend⟩ := hpath κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd
    hag u₀ hu₀ β hβ hmean hword a M' hMord' htype' W hWc hW0 hgenc
  have hR := retSigma76_le P η₁ η₂ ζ₁ ζ₂ d.u d.r
  have hcm : Measurable[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r] fun ω => shiftW (β ω).2 (β ω).1 := by
    have hp : Measurable[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r] fun ω => ((β ω).2, (β ω).1) := hβ.snd.prodMk hβ.fst
    have h2 := @Measurable.comp Ω (ℝ × BoundaryWord) BoundaryWord (retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r) _ _ _ _
      measurable_shiftW hp
    exact h2
  have hHc : Measurable fun ω => Exist.flowField (β ω).2 0 (hd.chartField κ h ω) := by
    have hp : Measurable fun ω => ((β ω).2, hd.chartField κ h ω) :=
      (hτm.mono hR le_rfl).prodMk (hd.measurable_chartField κ hh.1)
    have h2 := Exist.StagedLaw.measurable_flowField_uncurry.comp hp
    exact h2
  subst h𝓗 hV'
  refine ⟨M', hM'M, hM', hMM', a, _, W, E, _, γ', h0 _ hM', hcm.mono h0 le_rfl, hHc, hWc, hW0, hWa, hV, hγm,
    hγc, hγ0, hEm.mono h0 le_rfl, hτm.mono h0 le_rfl, Eventually.of_forall hcan,
    Eventually.of_forall fun ω hω => htype' ω hω,
    fun φ => integrable_pairing_ord_fst hL75 hκ hκ4 hb hh hη₁ hη₂ hd hag hu₀ hβ hmean hsort hM' hMord' a htype' φ,
    hS, hL, Eventually.of_forall hgen, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hcan', hpos] with ω hc hp hω
    rw [(hc hω).1]
    exact hp hω
  · filter_upwards [hcan', hthr] with ω hc hp hω
    rw [(hc hω).1]
    exact hp hω
  · filter_upwards [hcan', hoff, hE, hMord'] with ω hc hp hEω hordω hω t ht0 ht
    obtain ⟨hl, hγe⟩ := hc hω
    rw [hl] at ht
    rw [hγe t ht.le, hEω (hordω hω)]
    exact hp hω t ht0 ht
  · filter_upwards [hcan', hend, hE, hMord'] with ω hc hp hEω hordω hω htop
    obtain ⟨hl, hγe⟩ := hc hω
    rw [hl] at htop ⊢
    rw [hγe _ (ENNReal.coe_toNNReal_le_self), hEω (hordω hω)]
    exact hp hω htop

/-- **`RetOrdAStopSourceFstSeedStatement` from Lemma 7.5 and the pathwise A-stop facts** (items 1–5 proved; item 6
is `AStopPathFstStatement`). The parts are the good sub-events of PROVE-T15-ASTOP-PART's type partition. -/
theorem retOrdAStopSourceFstSeedStatement_of_path (hL75 : Theorem15.Lemma75Statement.{u})
    (hpath : AStopPathFstStatement.{u}) : RetOrdAStopSourceFstSeedStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hag u₀ hu₀ β hβ hmean hword
  obtain ⟨n, a, M, hMσ, -, hcover, hord, htype, -⟩ :=
    AStopPart.exists_ordTypePartition_fst hL75 hκ hκ4 hb hx hθ hh hη₁ hη₂ hd hag hu₀ hβ hmean hword
  choose M' hM'M hM' hMM' hin using fun i => exists_aStopSourceInputs_fst hL75 hpath hκ hκ4 hb hx hθ hh hη₁ hη₂
    hd hag hu₀ hβ hmean hword (hMσ i) (hord i) (a i) (htype i)
  refine ⟨n, M', fun i => retSigma76_le P η₁ η₂ ζ₁ ζ₂ d.u d.r _ (hM' i), ?_, fun i _ => hin i⟩
  have hall : ∀ᵐ ω ∂P, ∀ i, ω ∈ M i → ω ∈ M' i := ae_all_iff.2 hMM'
  filter_upwards [hcover, hall] with ω hc ha hordω
  obtain ⟨i, hi⟩ := hc hordω
  exact ⟨i, ha i hi⟩

/-- **Theorem 1.5's leaf 3 (`RLC.RetOrdDetStatement`) from Lemma 7.5, Theorem 1.3 and the two pathwise A-stop
statements** (PROVE-T15-ASTOP2's `retOrdDetStatement_of_source` with both source statements reduced). -/
theorem retOrdDetStatement_of_lemma75_path (hL75 : Theorem15.Lemma75Statement.{u})
    (h13 : Exist.Theorem13Statement.{0}) (hfst : AStopPathFstStatement.{u}) (hsnd : AStopPathSndStatement.{u}) :
    RetOrdDetStatement.{u} :=
  retOrdDetStatement_of_source h13 (retOrdAStopSourceFstSeedStatement_of_path hL75 hfst)
    (retOrdAStopSourceSndStatement_of_path hL75 hsnd)

end Assembly

end InteractingSLE.RLC.AStopSafe
