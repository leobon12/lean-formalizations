/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2VfGlue
import InteractingSLE.Spec.Supplement.SB2VeIn

/-!
# SB2(1)'s version half: the readings are the flow's lift

Packet PROVE-AUX61-NOJUMP (Theorem 1.4, SB2(1)'s version half, ruling R108). Almost surely at a launch on the entrance
event, for every rational time `q` before the lifetime:

* **`ae_reading`**: (i) a reading in the chart domain comes after the entrance (`T_L < q`): before the entrance the
  shifted flow lies in `hullK A'` (`SB.s2HullStatement`), which misses `ℍ \ fill A'`; (ii) after the entrance a
  reading in the domain is the flow's lift: `Vh.relRead … q = Ve.flowLift … (q − T_L)`
  (`Vf.relRead_eq`, `Vh.lift_eq_fwd`, `Vc.ae_lineGeom_liftOf`).
* `isConformal_of_shift`: a chart whose shift is conformal is conformal (deterministic).

These turn the line-mark readings `Vh.relRead` into readings of the version's lift. Theorem 1.3 and the named S3
input as before (R48); serves Theorem 1.4 only.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Vf

open Lv Exist.Staged Exist.StagedLaw

/-- **A chart whose shift is conformal is conformal.** -/
theorem isConformal_of_shift {c : Chart} {u m : ℝ} (h : (Lw.shiftChart c u m).IsConformal) : c.IsConformal := by
  obtain ⟨hd, hmaps, hinv⟩ := h
  have hsh : ∀ w : ℂ, c.2.1 w = (Lw.shiftChart c u m).2.1 (w - m) + u := fun w => by
    simp [Lw.shiftChart_inv]
  have hHm : ∀ w : ℂ, w ∈ H → w - m ∈ H := fun w hw => by
    have := (Lw.add_real_mem_H_iff (w := w - (m : ℂ)) m).1 (by simpa using hw)
    exact this
  refine ⟨fun w hw => ?_, fun w hw => ?_, fun w hw => ?_⟩
  · have h1 : DifferentiableWithinAt ℂ (fun w => (Lw.shiftChart c u m).2.1 (w - m) + u) H w :=
      ((hd (w - m) (hHm w hw)).comp w ((differentiableWithinAt_id).sub_const _) fun x hx => hHm x hx).add_const _
    exact h1.congr (fun x _ => hsh x) (hsh w)
  · rw [hsh]
    exact (Lw.add_real_mem_H_iff u).2 (hmaps (hHm w hw))
  · have h1 := hinv (w - m) (hHm w hw)
    simp only [Lw.shiftChart_fwd, Lw.shiftChart_inv, sub_add_cancel] at h1
    linear_combination h1

/-- **The readings are the flow's lift**, almost surely at a launch on the entrance event. -/
theorem ae_reading (h13 : Exist.Theorem13Statement.{u}) (hS3 : Tc.SB2EntranceNoCommonArcStatement.{u})
    {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u ψ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ) (I : K2LaunchInputs κ b jumps P h E k u ψ) {u₀ : ℂ → ℝ}
    (D : EntranceUnion κ b jumps P h E k u η ζ u₀) :
    ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) → Ve.entT κ b jumps E k u η ζ ω < ζ ω →
      ∀ q : ℚ≥0, ((q : ℝ≥0) : ℝ≥0∞) < ζ ω →
        (Vh.etaRead D q ω ∈ (I.chart ω).dom → Ve.entT κ b jumps E k u η ζ ω < ((q : ℝ≥0) : ℝ≥0∞)) ∧
        (Vh.etaRead D q ω ∈ (I.chart ω).dom →
          Vh.relRead D I q ω =
            Ve.flowLift κ b jumps E k u η ζ ω ((q : ℝ≥0) - (Ve.entT κ b jumps E k u η ζ ω).toNNReal)) := by
  filter_upwards [I.chart_eq, Vh.ae_etaRead_eq D, Vc.ae_lineGeom_liftOf h13 hS3 HP] with ω hch hη hrec hF hT q hqζ
  set TL := Ve.entT κ b jumps E k u η ζ ω with hTLdef
  have hTLtop : TL ≠ ⊤ := ne_top_of_lt hT
  have hTLc : ((TL.toNNReal : ℝ≥0) : ℝ≥0∞) = TL := ENNReal.coe_toNNReal hTLtop
  have hTLr : TL.toReal = (TL.toNNReal : ℝ) := rfl
  -- a record whose horizon exceeds `q`
  obtain ⟨T, hmT, hTζ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 (max_lt hqζ hT)
  have hqT : ((q : ℝ≥0) : ℝ) < T := NNReal.coe_lt_coe.2 (ENNReal.coe_lt_coe.1 ((le_max_left _ _).trans_lt hmT))
  have hTLT' : TL < T := (le_max_right _ _).trans_lt hmT
  have hLT' : (TL.toNNReal : ℝ) < T := by
    have h1 := hTLT'
    rw [← hTLc] at h1
    exact NNReal.coe_lt_coe.2 (ENNReal.coe_lt_coe.1 h1)
  set mx : ℝ := max ((q : ℝ≥0) : ℝ) (TL.toNNReal : ℝ) with hmx
  have hmxT : mx < T := max_lt hqT hLT'
  set S₁ : ℝ := (mx - TL.toNNReal + ((T : ℝ) - TL.toNNReal)) / 2 with hS₁
  have hS₁pos : 0 < S₁ := by rw [hS₁]; linarith [le_max_right ((q : ℝ≥0) : ℝ) (TL.toNNReal : ℝ)]
  have hS₁T : TL.toReal + S₁ < T := by rw [hTLr, hS₁]; linarith
  have hqS : ((q : ℝ≥0) : ℝ) < (TL.toNNReal : ℝ) + S₁ := by
    rw [hS₁]; linarith [le_max_left ((q : ℝ≥0) : ℝ) (TL.toNNReal : ℝ)]
  obtain ⟨p, g, β', γ, tL, Wr₀, ηr₀, hp, hch', hw, hag, -, hγeq⟩ := hrec hF T hTζ.le hTLT' S₁ hS₁pos hS₁T
  have htt : tL = TL.toNNReal := by rw [← ENNReal.coe_inj, hTLc]; exact hw.2.2.2.2.1
  subst htt
  obtain ⟨hpc, hp0, hpH, -, hpA⟩ := hp
  obtain ⟨hc, hgc, hgi, -, -⟩ := hch'
  obtain ⟨hβ', hβ'0, hβ'A, htL, -, hγ, -, hlift⟩ := hw
  have hconf : (Lv.launchChart κ b jumps E (k + 1) ω).IsConformal := isConformal_of_shift hc.1.1
  have hchω : I.chart ω = (Lv.launchChart κ b jumps E (k + 1) ω).recenter (launchEntry κ b jumps E (k + 1) u ω) :=
    hch hF
  have hηq : Vh.etaRead D q ω = η ω q := hη q hqζ.le
  have hgoodIff := relGood_iff D I hconf hc.1 hchω hηq
  -- before the entrance, the shifted flow is in `hullK`, off the domain
  obtain ⟨-, tL', htL', -, hpre, -, -⟩ := SB.s2HullStatement p β' hpc hp0 hpH hβ' hβ'0 hβ'A
  have htt' : tL' = TL.toNNReal := hβ'.2.1 (htL'.trans htL.symm)
  subst htt'
  refine ⟨fun hgood => ?_, fun hgood => ?_⟩
  · rw [hgoodIff] at hgood
    by_contra hle
    rw [not_lt, ← hTLc, ENNReal.coe_le_coe] at hle
    have hβq : β' q = η ω q - u := hag q (by linarith [NNReal.coe_le_coe.2 hle, hS₁pos])
    have hK : β' q ∈ hullK (p '' Icc 0 1) := hpre ⟨q, ⟨zero_le, hle⟩, rfl⟩
    rw [hβq] at hK
    rcases hK with hK | ⟨x, -, hx⟩
    · exact hgood.2 hK
    · have h1 : (0 : ℝ) < (η ω q - u).im := hgood.1
      rw [← hx] at h1
      simp at h1
  · rw [hgoodIff] at hgood
    have hpre' : TL < ((q : ℝ≥0) : ℝ≥0∞) := by
      by_contra hle
      rw [not_lt, ← hTLc, ENNReal.coe_le_coe] at hle
      have hβq : β' q = η ω q - u := hag q (by linarith [NNReal.coe_le_coe.2 hle, hS₁pos])
      have hK : β' q ∈ hullK (p '' Icc 0 1) := hpre ⟨q, ⟨zero_le, hle⟩, rfl⟩
      rw [hβq] at hK
      rcases hK with hK | ⟨x, -, hx⟩
      · exact hgood.2 hK
      · have h1 : (0 : ℝ) < (η ω q - u).im := hgood.1
        rw [← hx] at h1
        simp at h1
    have hle : TL.toNNReal ≤ (q : ℝ≥0) := by
      rw [← ENNReal.coe_le_coe, hTLc]; exact hpre'.le
    set s : ℝ≥0 := (q : ℝ≥0) - TL.toNNReal with hs
    have hqs : TL.toNNReal + s = (q : ℝ≥0) := add_tsub_cancel_of_le hle
    have hsS : (s : ℝ) < S₁ := by
      rw [hs, NNReal.coe_sub hle]; linarith
    have hgood' : η ω (TL.toNNReal + s) - u ∈ H \ fillH (p '' Icc 0 1) := by rw [hqs]; exact hgood
    have hlf := Vh.lift_eq_fwd hc.1 hgc hgi hγ hlift hag hsS hgood'
    rw [hqs] at hlf
    rw [(relRead_eq D I hconf hc.1 hchω hηq hgood).1, ← hlf]
    exact hγeq s hsS

end InteractingSLE.Theorem14.SB.Vf
