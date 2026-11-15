/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2VcLift
import InteractingSLE.Spec.Supplement.SB2TcRec

/-!
# SB2(1)'s chain record almost surely, with the lift read from the flow

Packet PROVE-AUX61-NOJUMP (Theorem 1.4, SB2(1)'s version half, ruling R108).

* **`ae_lineGeom_liftOf`**: almost surely at a launch, every record of `Tc.ae_lineGeom` (horizon `T ≤ ζ` after the
  entrance, `0 < S₁`, `T_L + S₁ < T`) has the lift `γ = liftOf c' η u t_L A'` below `S₁`, where `c'` is the shifted
  launch chart and `A'` the shifted retained prefix. The bad times have empty interior by
  `Vh.interior_notMem_dom_eq_empty`, from the record's no real arc, S2's hull clause (`SB.s2HullStatement`), and no
  common arc. The last comes from the named input `Tc.SB2EntranceNoCommonArcStatement` via
  `Tc.interior_mem_eq_empty_of_noArc`.

So the version's relative curve can be `liftOf`, a function of the flow and the chart. Theorem 1.3 enters as a
hypothesis (R48); serves Theorem 1.4 only.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Vc

open Lv Exist.Staged Exist.StagedLaw

/-- **The records' lift is `liftOf`**, almost surely (Theorem 1.3 and Lemma S3 in SB2(1)'s form as hypotheses). -/
theorem ae_lineGeom_liftOf (h13 : Exist.Theorem13Statement.{u}) (hS3 : Tc.SB2EntranceNoCommonArcStatement.{u})
    {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u ψ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ) :
    ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) → ∀ T : ℝ≥0, (T : ℝ≥0∞) ≤ ζ ω →
      firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω)) < T →
      ∀ S₁ : ℝ, 0 < S₁ →
        (firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω))).toReal + S₁ < T →
      ∃ (p : ℝ → ℂ) (g : ℂ → ℂ) (β' γ : ℝ≥0 → ℂ) (tL : ℝ≥0) (Wr : ℝ → ℝ) (ηr : ℝ → ℂ),
        (ContinuousOn p (Icc 0 1) ∧ p 0 = 0 ∧ (∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (p s).im) ∧
          (∀ z, (p ⁻¹' {z} ∩ Icc 0 1).Finite) ∧
          p '' Icc 0 1 = (fun z => z - (u : ℂ)) '' lowerPrefix κ b jumps E (k + 1) u ω) ∧
        (IsLeftEntryChart (p '' Icc 0 1) (realMin (p '' Icc 0 1))
            (Lw.shiftChart (Lv.launchChart κ b jumps E (k + 1) ω) u (launchEntry κ b jumps E (k + 1) u ω)) ∧
          ContinuousOn g {z | 0 ≤ z.im} ∧
          EqOn g (Lw.shiftChart (Lv.launchChart κ b jumps E (k + 1) ω) u
            (launchEntry κ b jumps E (k + 1) u ω)).2.1 H ∧
          (∀ z, (g ⁻¹' {z} ∩ {v | 0 ≤ v.im}).Finite) ∧
          FinRel.LiftRealOn (Lw.shiftChart (Lv.launchChart κ b jumps E (k + 1) ω) u
            (launchEntry κ b jumps E (k + 1) u ω))) ∧
        (Supp9B.IsProperCurve β' ∧ β' 0 = 0 ∧ p '' Icc 0 1 ⊆ Supp9B.closedRightSide β' ∧
          β' tL = realMin (p '' Icc 0 1) ∧
          ((tL : ℝ≥0) : ℝ≥0∞) = firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω)) ∧
          Supp9B.IsProperCurve γ ∧ γ 0 = 0 ∧ ∀ s, g (γ s) = β' (tL + s)) ∧
        (∀ t : ℝ≥0, (t : ℝ) < (tL : ℝ) + S₁ → β' t = η ω t - u) ∧
        ((∀ S₀ : ℝ, 0 ≤ S₀ → S₀ < S₁ → FinRel.IsSB2RelChain (p '' Icc 0 1)
            (Lw.shiftChart (Lv.launchChart κ b jumps E (k + 1) ω) u (launchEntry κ b jumps E (k + 1) u ω))
            β' γ tL S₀ Wr ηr) ∧
          interior {r ∈ Ioo (0 : ℝ) S₁ | β' (tL + r.toNNReal) ∈ {z : ℂ | z.im = 0}} = ∅) ∧
        (∀ s : ℝ≥0, (s : ℝ) < S₁ → γ s = liftOf (Lw.shiftChart (Lv.launchChart κ b jumps E (k + 1) ω) u
          (launchEntry κ b jumps E (k + 1) u ω)) (η ω) u tL
          ((fun z => z - (u : ℂ)) '' lowerPrefix κ b jumps E (k + 1) u ω) s) := by
  filter_upwards [Tc.ae_lineGeom h13 hS3 HP, hS3 κ b jumps P h E k u ψ η ζ HP]
    with ω hgeo hno hF T hTζ hvis S₁ hS₁ hS₁T
  obtain ⟨p, g, β', γ, tL, Wr, ηr, hp, hch, hw, hag, hrc⟩ := hgeo hF T hTζ hvis S₁ hS₁ hS₁T
  refine ⟨p, g, β', γ, tL, Wr, ηr, hp, hch, hw, hag, hrc, fun s hs => ?_⟩
  obtain ⟨hpc, hp0, hpH, -, hpA⟩ := hp
  obtain ⟨hc, hgc, hgi, -, -⟩ := hch
  obtain ⟨hβ', hβ'0, hβ'A, htL, hTL, hγ, -, hlift⟩ := hw
  obtain ⟨-, hnR⟩ := hrc
  -- S2's hull clause at the (unique) visit time
  obtain ⟨-, tL', htL', -, -, -, hhull⟩ := SB.s2HullStatement p β' hpc hp0 hpH hβ' hβ'0 hβ'A
  have htt : tL' = tL := hβ'.2.1 (htL'.trans htL.symm)
  rw [htt] at hhull
  -- no common arc with the shifted prefix on `(t_L, t_L + S₁)`
  have hTLr : (firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω))).toReal = tL := by
    rw [← hTL]; rfl
  have hno' : ∀ s₁ s₂ : ℝ≥0, tL ≤ s₁ → s₁ < s₂ → (s₂ : ℝ) ≤ tL + S₁ → ¬ β' '' Ioo s₁ s₂ ⊆ p '' Icc 0 1 := by
    intro s₁ s₂ h1 h12 h2 hsub
    have hs₂T : (s₂ : ℝ) < T := by rw [hTLr] at hS₁T; linarith
    refine hno hF s₁ s₂ (hTL ▸ ENNReal.coe_le_coe.2 h1) h12
      ((ENNReal.coe_le_coe.2 (NNReal.coe_le_coe.1 hs₂T.le)).trans hTζ) ?_
    rintro _ ⟨t, ht, rfl⟩
    have htS : (t : ℝ) < (tL : ℝ) + S₁ := lt_of_lt_of_le (NNReal.coe_lt_coe.2 ht.2) h2
    have hmem : β' t ∈ p '' Icc 0 1 := hsub ⟨t, ht, rfl⟩
    rw [hpA, hag t htS] at hmem
    obtain ⟨z, hz, hze⟩ := hmem
    have : z = η ω t := by linear_combination hze
    exact this ▸ hz
  have hcl : IsClosed (p '' Icc 0 1) := (isCompact_Icc.image_of_continuousOn hpc).isClosed
  have hnA := Tc.interior_mem_eq_empty_of_noArc hcl hno'
  have hbad := Vh.interior_notMem_dom_eq_empty hβ'.1 hβ'.2.2.1 hhull hnR hnA
  have h := liftOf_eq hc.1 hgc hgi hγ hlift hag hbad hs
  rw [hpA] at h
  exact h.symm

end InteractingSLE.Theorem14.SB.Vc
