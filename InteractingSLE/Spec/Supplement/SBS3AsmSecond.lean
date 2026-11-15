/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2LkUnique
import InteractingSLE.Spec.Supplement.GW1Base
import InteractingSLE.Spec.Supplement.GW4LeafPiece
import InteractingSLE.Spec.Supplement.BRLeafGB6Aux
import InteractingSLE.Spec.Restart.StoppedK2Wire
import InteractingSLE.Spec.Supplement.SBS3GeoSecond

/-!
# Lemma S3: the second path as the first piece of a staged program

Worker PROVE-R6-CORNER (Theorem 1.4, Lemma S3, specification pp. 579–580). The second history of S3 is the given
angle-`ϑ` flow line `β` up to a rational time; the actual means, words and union comparisons of PROVE-T14-S3 are
stated for staged histories. This file identifies the two:

* **`ae_flowLine_eq_firstPiece`**: for a staged history of a program from the root `0` starting with an ordinary piece
  of angle `ϑ` and own time `τ`, almost surely the flow line has the piece's lifetime, the piece's driver vanishes at
  `0` and is continuous up to `min τ ζ`, and the flow line agrees with **every** generating trace of the piece's
  driver up to `min τ ζ` (Theorem 1.2's determination `Lk.ae_eq_of_isFlowLineDriver` through
  `IsStagedHistory.isFlowLineDriver_first`; trace uniqueness `GW4Leaf.eqOn_of_isGeneratingTrace`);
* `Geo.IsChartCore.congr`: a core chart only depends on the curve through its image up to `q` and its tip.

R48: Theorems 1.2–1.3 appear only as hypotheses (these results serve Theorem 1.4).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar chiC)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.S3.Asm

open Exist Exist.Staged Exist.StagedLaw

/-- **The given flow line is the first piece of a staged program** (Theorem 1.2's determination,
`Lk.ae_eq_of_isFlowLineDriver`; trace uniqueness, `GW4Leaf.eqOn_of_isGeneratingTrace`). For a staged history of a
program from the root `0` whose first instruction is an ordinary piece of angle `ϑ` and own time `τ`, almost surely
the flow line `β` of angle `ϑ` from `0` has the piece's lifetime, and agrees up to `min τ ζ` with every generating
trace of the piece's driver. -/
theorem ae_flowLine_eq_firstPiece (h12p : Theorem12ParamStatement.{u}) (h13 : Theorem13Statement.{u})
    (h12p₀ : Theorem12ParamStatement.{0}) (h13₀ : Theorem13Statement.{0}) {κ ϑ : ℝ} (hκ : 0 < κ)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {spec : ExplSpec} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hE : IsStagedHistory κ b jumps P h spec E)
    (hR : StagedPiecesRegular κ b jumps P spec E) (hroot : spec.1 = 0) {τ : ℝ≥0∞} {rest : List Instr}
    (hp : spec.2.2 = Sum.inl (ϑ, τ) :: rest)
    {β : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞} (hβ : IsFlowLine κ b jumps 0 ϑ P h β ζ) :
    ∀ᵐ ω ∂P, ζ ω = (E 0 ω).2 ∧ (E 0 ω).1 0 = 0 ∧ ContinuousOn (E 0 ω).1 {s | (s : ℝ≥0∞) ≤ min τ (E 0 ω).2} ∧
      ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (E 0 ω).1 (min τ (E 0 ω).2) η →
        ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ min τ (E 0 ω).2 → β ω t = η t := by
  obtain ⟨h', 𝓕, W, VL, VR, B, htr, hcoup, htrace⟩ := hβ
  have hFL : IsFlowLineDriver κ b jumps ϑ P h W ζ := ⟨h', 𝓕, VL, VR, B, htr, hcoup⟩
  have hFL₂ := hE.isFlowLineDriver_first hκ hb hh hroot hp
  have huniq := SB.Lk.ae_eq_of_isFlowLineDriver h12p h13 h12p₀ h13₀ hκ hb hb hFL hFL₂
  have hl := GW1.launches_run_one_of_cons κ b jumps spec hp
  filter_upwards [huniq, htrace, hR] with ω hu htω hr
  obtain ⟨hζ, hW⟩ := hu
  have hk : spec.2.2[0]? = some (Sum.inl (ϑ, τ)) := by rw [hp]; rfl
  obtain ⟨h0, hc, -⟩ := hr 0 ϑ τ (Chart.id.recenter spec.1) hk (hl (fun j => E j ω))
  refine ⟨hζ, h0, hc, fun η hη t ht => ?_⟩
  have hβg : IsGeneratingTrace (E 0 ω).1 (E 0 ω).2 (β ω) := by
    have h1 : IsGeneratingTrace (fun t => W t ω) (ζ ω) (β ω) := by
      simpa only [Complex.ofReal_zero, sub_zero] using htω
    rw [hζ] at h1
    exact Restart.StoppedK2.isGeneratingTrace_congr (fun s hs => hW s (hζ ▸ hs)) h1
  have hβg' := BRLeaf.isGeneratingTrace_of_le hβg (min_le_right τ _)
  have hc' : ContinuousOn (E 0 ω).1 {s : ℝ≥0 | (s : ℝ≥0∞) < min τ (E 0 ω).2} :=
    hc.mono fun s (hs : (s : ℝ≥0∞) < min τ (E 0 ω).2) => show (s : ℝ≥0∞) ≤ min τ (E 0 ω).2 from le_of_lt hs
  exact (GW4Leaf.eqOn_of_isGeneratingTrace hη hβg' hc' h0 t ht)

/-- A core chart only depends on the curve through its image up to `q` and its tip. -/
theorem _root_.InteractingSLE.Theorem14.SB.S3.Geo.IsChartCore.congr {η η' : ℝ≥0 → ℂ} {q : ℝ≥0} {f Φ : ℂ → ℂ}
    (h : Geo.IsChartCore η q f Φ) (hag : ∀ s ≤ q, η' s = η s) : Geo.IsChartCore η' q f Φ := by
  have himg : η' '' Icc 0 q = η '' Icc 0 q := image_congr fun s hs => hag s hs.2
  have htip : η' q = η q := hag q le_rfl
  refine ⟨?_, ?_, ?_, ?_, h.inv_cont, ?_, h.f_inv, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [himg, htip]
  · exact h.maps
  · exact h.injOn
  · exact h.cont
  · exact h.bdd
  · exact h.inv_mem
  · exact h.inv_f
  · exact h.cluster
  · exact h.tip
  · exact h.tip_fibre
  · exact h.bdry

end InteractingSLE.Theorem14.SB.S3.Asm
