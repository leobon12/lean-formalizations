/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBS3AsmChart
import InteractingSLE.Spec.Supplement.GW2aPiece
import InteractingSLE.Spec.Supplement.W5CommonSeedShift
import InteractingSLE.Spec.Supplement.SBLwShift

/-!
# Lemma S3: a second history launched from a real seed

Worker PROVE-R6-CORNER (Theorem 1.4, Lemma S3 in SB2(1)'s configuration). The flow line `η` from the seed `x` is,
recentred, the first piece of every staged program from the root `x` starting with its angle
(`ae_flowLine_eq_firstPiece_root`, via `Supp9.IsFlowLine.recenter` and `isFlowLineDriver_first_root`);
`ae_firstDriver_eq_root` compares two such programs. `shiftChart_recenter_loewner`: the Loewner chart launched from
`x`, shifted by `x`, is the one launched from `0`; hence **`second_sample_facts_root`** reduces the second side of
the comparison at a seed `x` to `second_sample_facts` (same driver family, program re-rooted at `0`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Complex Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar chiC)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.S3.Asm

open Exist Exist.Staged Exist.StagedLaw Restart

/-- The Loewner chart launched from the real root `u`, read in coordinates shifted by `u`, is the one launched from
`0`. -/
theorem shiftChart_recenter_loewner (u : ℝ) (W : ℝ → ℝ) (t : ℝ) :
    Lw.shiftChart ((Chart.id.recenter u).loewner W t) u 0 = (Chart.id.recenter 0).loewner W t := by
  refine Prod.ext (funext fun z => ?_) (Prod.ext (funext fun w => ?_) (funext fun z => ?_))
  · simp [Lw.shiftChart, Chart.loewner, Chart.recenter, Chart.id]
  · simp [Lw.shiftChart, Chart.loewner, Chart.recenter, Chart.id]
  · simp [Lw.shiftChart, Chart.loewner, Chart.recenter, Chart.id]

/-- **The recentred flow line from the root of a staged program is its first piece** (as
`ae_flowLine_eq_firstPiece`, for any real root: `η − x` is the first piece's trace). -/
theorem ae_flowLine_eq_firstPiece_root (h12p : Theorem12ParamStatement.{u}) (h13 : Theorem13Statement.{u})
    (h12p₀ : Theorem12ParamStatement.{0}) (h13₀ : Theorem13Statement.{0}) {κ ψ : ℝ} (hκ : 0 < κ)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {spec : ExplSpec} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hE : IsStagedHistory κ b jumps P h spec E)
    (hR : StagedPiecesRegular κ b jumps P spec E) {τ : ℝ≥0∞} {rest : List Instr}
    (hp : spec.2.2 = Sum.inl (ψ, τ) :: rest)
    {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞} (hη : IsFlowLine κ b jumps spec.1 ψ P h η ζ) :
    ∀ᵐ ω ∂P, ζ ω = (E 0 ω).2 ∧ (E 0 ω).1 0 = 0 ∧ ContinuousOn (E 0 ω).1 {s | (s : ℝ≥0∞) ≤ min τ (E 0 ω).2} ∧
      ∀ η' : ℝ≥0 → ℂ, IsGeneratingTrace (E 0 ω).1 (min τ (E 0 ω).2) η' →
        ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ min τ (E 0 ω).2 → η ω t - spec.1 = η' t := by
  obtain ⟨h', 𝓕, W, VL, VR, B, htr, hcoup, htrace⟩ := Supp9.IsFlowLine.recenter (κ := κ) hη
  have hFL : IsFlowLineDriver κ (fun y => b (y + spec.1)) (jumps.image (· - spec.1)) ψ P
      (fun ω => Exist.flowField spec.1 0 (h ω)) W ζ := ⟨h', 𝓕, VL, VR, B, htr, hcoup⟩
  have hFL₂ := hE.isFlowLineDriver_first_root hκ hb hh hp
  have hb' := Exist.isPiecewiseConstant_comp_add hb spec.1
  have huniq := SB.Lk.ae_eq_of_isFlowLineDriver h12p h13 h12p₀ h13₀ hκ hb' hb' hFL hFL₂
  have hl := GW1.launches_run_one_of_cons κ b jumps spec hp
  filter_upwards [huniq, htrace, hR] with ω hu htω hr
  obtain ⟨hζ, hW⟩ := hu
  have hk : spec.2.2[0]? = some (Sum.inl (ψ, τ)) := by rw [hp]; rfl
  obtain ⟨h0, hc, -⟩ := hr 0 ψ τ (Chart.id.recenter spec.1) hk (hl (fun j => E j ω))
  refine ⟨hζ, h0, hc, fun η' hη' t ht => ?_⟩
  have hβg : IsGeneratingTrace (E 0 ω).1 (E 0 ω).2 (fun t => η ω t - spec.1) := by
    have h1 : IsGeneratingTrace (fun t => W t ω) (ζ ω) (fun t => η ω t - spec.1) := by
      simpa only [Complex.ofReal_zero, sub_zero] using htω
    rw [hζ] at h1
    exact Restart.StoppedK2.isGeneratingTrace_congr (fun s hs => hW s (hζ ▸ hs)) h1
  have hβg' := BRLeaf.isGeneratingTrace_of_le hβg (min_le_right τ _)
  have hc' : ContinuousOn (E 0 ω).1 {s : ℝ≥0 | (s : ℝ≥0∞) < min τ (E 0 ω).2} :=
    hc.mono fun s (hs : (s : ℝ≥0∞) < min τ (E 0 ω).2) => show (s : ℝ≥0∞) ≤ min τ (E 0 ω).2 from le_of_lt hs
  exact (GW4Leaf.eqOn_of_isGeneratingTrace hη' hβg' hc' h0 t ht)

/-- The first pieces of two staged programs from the same real root with the same first angle have the same driver
on their common lifetime. -/
theorem ae_firstDriver_eq_root (h12p : Theorem12ParamStatement.{u}) (h13 : Theorem13Statement.{u})
    (h12p₀ : Theorem12ParamStatement.{0}) (h13₀ : Theorem13Statement.{0}) {κ ψ : ℝ} (hκ : 0 < κ)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {spec spec' : ExplSpec} {E E' : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : IsStagedHistory κ b jumps P h spec E) (hE' : IsStagedHistory κ b jumps P h spec' E')
    (hroot : spec'.1 = spec.1) {τ τ' : ℝ≥0∞} {rest rest' : List Instr}
    (hp : spec.2.2 = Sum.inl (ψ, τ) :: rest) (hp' : spec'.2.2 = Sum.inl (ψ, τ') :: rest') :
    ∀ᵐ ω ∂P, (E 0 ω).2 = (E' 0 ω).2 ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) < (E 0 ω).2 → (E 0 ω).1 t = (E' 0 ω).1 t := by
  have h1 := hE.isFlowLineDriver_first_root hκ hb hh hp
  have h2 := hE'.isFlowLineDriver_first_root hκ hb hh hp'
  rw [hroot] at h2
  have hb' := Exist.isPiecewiseConstant_comp_add hb spec.1
  exact SB.Lk.ae_eq_of_isFlowLineDriver h12p h13 h12p₀ h13₀ hκ hb' hb' h1 h2

/-- **The second side at one sample, for a piece launched from a real root `u`**, in coordinates shifted by `u`
(deterministic). As `second_sample_facts`, for the program `(u, true, [(ψ, q)])`: the means are read through
`z ↦ z + u` and the chart identity is the root-`u` one. -/
theorem second_sample_facts_root {κ ψ x : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {q : ℝ≥0}
    {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hreg : ∀ k c θ', (ExplState.run κ b jumps (x, true, [Sum.inl (ψ, (q : ℝ≥0∞))]) D (k + 1)).2.2.2.1 k =
      some (c, θ') → GW1P.PieceRegular (D k).1
        (min (instrTime (x, true, [Sum.inl (ψ, (q : ℝ≥0∞))]) k) (D k).2))
    {W : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {β : ℝ≥0 → ℂ} (hβ : IsGeneratingTrace W ζ β)
    (hW : ContinuousOn W {s | (s : ℝ≥0∞) < ζ}) (hW0 : W 0 = 0) (hinj : InjOn β {t | (t : ℝ≥0∞) ≤ ζ})
    (hq : (q : ℝ≥0∞) < ζ) (hq0 : 0 < q) (hDq : (q : ℝ≥0∞) < (D 0).2)
    (hDW : ∀ t : ℝ≥0, t ≤ q → (D 0).1 t = W t)
    (hDc : ContinuousOn (D 0).1 {s | (s : ℝ≥0∞) ≤ min (q : ℝ≥0∞) (D 0).2})
    {β₂ w : BoundaryWord} {r : RecData} {v₂ u₀ : ℂ → ℝ}
    (hmean : EqOn (fun z => v₂ z + u₀ z + chiC κ *
        (ExplState.run κ b jumps (x, true, [Sum.inl (ψ, (q : ℝ≥0∞))]) D 1).2.2.2.2.1.2.2 z)
      (fun z => β₂.mean ((ExplState.run κ b jumps (x, true, [Sum.inl (ψ, (q : ℝ≥0∞))]) D 1).2.2.2.2.1.1 z))
      (ExplState.run κ b jumps (x, true, [Sum.inl (ψ, (q : ℝ≥0∞))]) D 1).2.2.2.2.1.dom)
    (hid : ∀ y : ℝ, y ∉ β₂.jumps → y ∉ (stopWord κ (w, ψ, r)).jumps → β₂.fn y = (stopWord κ (w, ψ, r)).fn y)
    (hcid : (ExplState.run κ b jumps (x, true, [Sum.inl (ψ, (q : ℝ≥0∞))]) D 1).2.2.2.2.1 =
      (Chart.id.recenter x).loewner (rdrv r) (rtime r)) :
    ∃ (f Φ : ℂ → ℂ) (e₂ : ℝ) (Jx : Finset ℝ),
      Geo.IsChartCore β q f Φ ∧ DifferentiableOn ℂ f (H \ fillH (β '' Icc 0 q)) ∧
      (∀ z, (Φ ⁻¹' {z} ∩ {v | 0 ≤ v.im}).Finite) ∧ IsOpen (H \ fillH (β '' Icc 0 q)) ∧
      IsMapOut (fillH (β '' Icc 0 q)) (fun z => f z + (e₂ : ℂ)) ∧
      EqOn (fun z => v₂ (z + x) + u₀ (z + x) + chiC κ * (canonDerivLog (fillH (β '' Icc 0 q)) z).im)
        (fun z => β₂.mean (f z)) (H \ fillH (β '' Icc 0 q)) ∧
      ∀ y : ℝ, y < 0 → y ∉ β₂.jumps → y ∉ Jx → Φ y ∈ H → β₂.fn y = -sleLambda κ - ψ * chiC κ := by
  set sx : ExplSpec := (x, true, [Sum.inl (ψ, (q : ℝ≥0∞))]) with hsx
  set s0 : ExplSpec := ((0 : ℝ), true, [Sum.inl (ψ, (q : ℝ≥0∞))]) with hs0
  have hlx := GW1.launches_run_one_of_cons κ b jumps sx (θ := ψ) (t := (q : ℝ≥0∞)) (rest := []) rfl D
  have hl0 := GW1.launches_run_one_of_cons κ b jumps s0 (θ := ψ) (t := (q : ℝ≥0∞)) (rest := []) rfl D
  obtain ⟨-, hex, -⟩ := eq_launch_of_launches sx D hlx
  obtain ⟨-, he0, -⟩ := eq_launch_of_launches s0 D hl0
  have hfin : min (instrTime sx 0) (D 0).2 ≠ ⊤ := by
    have : instrTime sx 0 = (q : ℝ≥0∞) := rfl
    rw [this]
    exact ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_left _ _)
  -- the two stage-1 charts
  set cx := (ExplState.run κ b jumps sx D 1).2.2.2.2.1 with hcx
  set c0 := (ExplState.run κ b jumps s0 D 1).2.2.2.2.1 with hc0
  have hcx' : cx = (Chart.id.recenter x).loewner
      (fun y : ℝ => (D 0).1 (min ((y.toNNReal : ℝ≥0) : ℝ≥0∞) (min (q : ℝ≥0∞) (D 0).2)).toNNReal)
      ((min (q : ℝ≥0∞) (D 0).2).toNNReal : ℝ) := by
    rw [hcx, hex, chart_launch _ _ _ _ _ hfin]
    rfl
  have hc0' : c0 = (Chart.id.recenter 0).loewner
      (fun y : ℝ => (D 0).1 (min ((y.toNNReal : ℝ≥0) : ℝ≥0∞) (min (q : ℝ≥0∞) (D 0).2)).toNNReal)
      ((min (q : ℝ≥0∞) (D 0).2).toNNReal : ℝ) := by
    have hfin0 : min (instrTime s0 0) (D 0).2 ≠ ⊤ := hfin
    rw [hc0, he0, chart_launch _ _ _ _ _ hfin0]
    rfl
  have hshift : c0 = Lw.shiftChart cx x 0 := by rw [hc0', hcx', shiftChart_recenter_loewner]
  -- regularity of the root-0 program
  have hreg0 : ∀ k c θ', (ExplState.run κ b jumps s0 D (k + 1)).2.2.2.1 k = some (c, θ') →
      GW1P.PieceRegular (D k).1 (min (instrTime s0 k) (D k).2) := by
    intro k c θ' hl
    obtain ⟨hk, -, -⟩ := eq_launch_of_launches s0 D hl
    rcases k with _ | k
    · exact hreg 0 _ _ hlx
    · exact absurd hk (by simp [hs0])
  -- conformality and domains
  have hccx : cx.IsConformal :=
    (GW2aCont.isConformal_runChart (κ := κ) (b := b) (jumps := jumps) sx D 1 fun j _ c θ h => hreg j c θ h).1
  have hcc0 : c0.IsConformal :=
    (GW2aCont.isConformal_runChart (κ := κ) (b := b) (jumps := jumps) s0 D 1 fun j _ c θ h => hreg0 j c θ h).1
  have hdom : ∀ z, z ∈ (c0.dom : Set ℂ) → z + (x : ℂ) ∈ (cx.dom : Set ℂ) := by
    intro z hz
    rw [hcc0.coe_dom] at hz
    rw [hccx.coe_dom]
    obtain ⟨w, hw, hwz⟩ := hz
    refine ⟨w, hw, ?_⟩
    have : c0.2.1 w = cx.2.1 w - x := by rw [hshift]; simp [Lw.shiftChart]
    rw [← hwz, this, sub_add_cancel]
  have hmean0 : EqOn (fun z => v₂ (z + x) + u₀ (z + x) + chiC κ * c0.2.2 z) (fun z => β₂.mean (c0.1 z))
      (c0.dom : Set ℂ) := by
    intro z hz
    have he := hmean (hdom z hz)
    have h1 : c0.2.2 z = cx.2.2 (z + x) := by rw [hshift]; rfl
    have h2 : c0.1 z = cx.1 (z + x) := by rw [hshift]; simp [Lw.shiftChart]
    simp only at he ⊢
    rw [h1, h2]
    exact he
  have hcid0 : c0 = (Chart.id.recenter 0).loewner (rdrv r) (rtime r) := by
    rw [hshift, hcid, shiftChart_recenter_loewner]
  exact second_sample_facts (D := D) hreg0 hβ hW hW0 hinj hq hq0 hDq hDW hDc hmean0 hid hcid0

end InteractingSLE.Theorem14.SB.S3.Asm
