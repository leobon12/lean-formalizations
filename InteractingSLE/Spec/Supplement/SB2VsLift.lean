/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2VsThr

/-!
# The continuous extension of the launch chart's inverse (D19, step 4)

Packet PROVE-AUX61-NOJUMP. **`ae_lift_inv'`**: `Vn.ae_lift_inv` with the clause, already established in its proof,
that the continuous extension agrees with the shifted launch chart's inverse on `ℍ` (so the record, read from the
chart's inverse on `ℍ`, decodes to the gauge of this extension).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Vs

open Lv Exist.Staged Exist.StagedLaw Sec7.PocketTraversal Sec7.Lemma71C Vn

section

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u ψ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}

/-- **One extension of the chart's inverse reads the flow from the whole lift**, and agrees with the shifted chart's
inverse on `ℍ` (`Vn.ae_lift_inv` with that clause kept). -/
theorem ae_lift_inv' (h13 : Exist.Theorem13Statement.{u}) (hS3 : Tc.SB2EntranceNoCommonArcStatement.{u})
    (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ) :
    ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) → Ve.entT κ b jumps E k u η ζ ω < ζ ω →
      ∃ g : ℂ → ℂ, ContinuousOn g {z | 0 ≤ z.im} ∧
        EqOn g (Lw.shiftChart (Lv.launchChart κ b jumps E (k + 1) ω) u (launchEntry κ b jumps E (k + 1) u ω)).2.1 H ∧
        ∀ r : ℝ≥0,
        (((Ve.entT κ b jumps E k u η ζ ω).toNNReal + r : ℝ≥0) : ℝ≥0∞) < ζ ω →
        0 ≤ (Ve.flowLift κ b jumps E k u η ζ ω r).im ∧
        g (Ve.flowLift κ b jumps E k u η ζ ω r) = η ω ((Ve.entT κ b jumps E k u η ζ ω).toNNReal + r) - u := by
  filter_upwards [Vc.ae_lineGeom_liftOf h13 hS3 HP] with ω hrec hl hT
  have hTL : Ve.entT κ b jumps E k u η ζ ω ≠ ⊤ := ne_top_of_lt hT
  set t₀ : ℝ≥0 := (Ve.entT κ b jumps E k u η ζ ω).toNNReal with ht₀
  have hcoe : ((t₀ : ℝ≥0) : ℝ≥0∞) = Ve.entT κ b jumps E k u η ζ ω := ENNReal.coe_toNNReal hTL
  have e2 : (Ve.entT κ b jumps E k u η ζ ω).toReal = (t₀ : ℝ) := rfl
  -- a record with a horizon beyond any given relative time `r` before the life
  have hrecAt : ∀ r : ℝ≥0, ((t₀ + r : ℝ≥0) : ℝ≥0∞) < ζ ω → ∃ (T : ℝ≥0) (S₁ : ℝ), (T : ℝ≥0∞) ≤ ζ ω ∧
      Ve.entT κ b jumps E k u η ζ ω < T ∧ 0 < S₁ ∧ (Ve.entT κ b jumps E k u η ζ ω).toReal + S₁ < T ∧
      (r : ℝ) < S₁ := by
    intro r hr
    by_cases hζ : ζ ω = ⊤
    · refine ⟨t₀ + r + 2, r + 1, by rw [hζ]; exact le_top, ?_, by positivity, ?_, by linarith⟩
      · rw [← hcoe, ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe]; push_cast; linarith [r.2]
      · rw [e2]; push_cast; linarith
    · set Zt : ℝ≥0 := (ζ ω).toNNReal with hZt
      have hZc : ((Zt : ℝ≥0) : ℝ≥0∞) = ζ ω := ENNReal.coe_toNNReal hζ
      have hr' : (t₀ : ℝ) + r < Zt := by
        rw [← hZc, ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, NNReal.coe_add] at hr; exact hr
      refine ⟨Zt, ((r : ℝ) + (Zt - t₀)) / 2, hZc.le, ?_, ?_, ?_, ?_⟩
      · rw [← hcoe, ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe]; linarith [r.2]
      · linarith [r.2]
      · rw [e2]; linarith
      · linarith
  -- the facts of one record at a relative time below its horizon
  have hread : ∀ r : ℝ≥0, ((t₀ + r : ℝ≥0) : ℝ≥0∞) < ζ ω → ∃ g : ℂ → ℂ, ContinuousOn g {z | 0 ≤ z.im} ∧
      EqOn g (Lw.shiftChart (Lv.launchChart κ b jumps E (k + 1) ω) u (launchEntry κ b jumps E (k + 1) u ω)).2.1 H ∧
      0 ≤ (Ve.flowLift κ b jumps E k u η ζ ω r).im ∧
      g (Ve.flowLift κ b jumps E k u η ζ ω r) = η ω (t₀ + r) - u := by
    intro r hr
    obtain ⟨T, S₁, hTζ, hvis, hS₁, hS₁T, hrS⟩ := hrecAt r hr
    obtain ⟨p, g, β', γ, tL, Wr, ηr, -, ⟨-, hgc, hgi, -, -⟩, ⟨-, -, -, -, htL, hγp, -, hlift⟩, hag, -, hlo⟩ :=
      hrec hl T hTζ hvis S₁ hS₁ hS₁T
    have htL' : t₀ = tL := by
      have := congrArg ENNReal.toNNReal htL
      rw [ENNReal.toNNReal_coe] at this
      exact this.symm
    have hγr : Ve.flowLift κ b jumps E k u η ζ ω r = γ r := by
      rw [hlo r hrS, ← htL']
      rfl
    refine ⟨g, hgc, hgi, by rw [hγr]; exact hγp.2.2.1 r, ?_⟩
    rw [hγr, hlift r, htL', hag (tL + r) (by push_cast; linarith)]
  -- one extension for all times
  obtain ⟨g₀, hg₀c, hg₀i⟩ : ∃ g₀ : ℂ → ℂ, ContinuousOn g₀ {z | 0 ≤ z.im} ∧
      EqOn g₀ (Lw.shiftChart (Lv.launchChart κ b jumps E (k + 1) ω) u (launchEntry κ b jumps E (k + 1) u ω)).2.1 H := by
    have h0 : ((t₀ + 0 : ℝ≥0) : ℝ≥0∞) < ζ ω := by rw [add_zero, hcoe]; exact hT
    obtain ⟨g, hgc, hgi, -, -⟩ := hread 0 h0
    exact ⟨g, hgc, hgi⟩
  refine ⟨g₀, hg₀c, hg₀i, fun r hr => ?_⟩
  obtain ⟨g, hgc, hgi, him, hval⟩ := hread r hr
  refine ⟨him, ?_⟩
  rw [eqOn_closedH_of_eqOn_H hg₀c hgc (hg₀i.trans hgi.symm) him]
  exact hval

end

end InteractingSLE.Theorem14.SB.Vs
