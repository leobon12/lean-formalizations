/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2VcAe
import InteractingSLE.Spec.Supplement.SBS3DwBase
import InteractingSLE.Spec.Supplement.SBS3DwTcRec
import InteractingSLE.Spec.Supplement.SB2TcRec

/-!
# Successor of `SB2VcAe` with the upper angle `ψ ≤ π/2` (decision D22, ruling R121)

Worker PROVE-R6-CORNER (round 8). The declarations of `SB2VcAe` that use Lemma S3 in SB2(1)'s form,
restated so that Lemma S3 enters as `Tc.SB2EntranceNoCommonArcLeStatement` (upper angle `ψ ≤ π/2`, PROVED
from Theorems 1.2–1.3 as `Tc.sb2EntranceNoCommonArcLeStatement_of_thm`). Every launch problem carries the bound
as an instance argument `[Fact (ψ ≤ Real.pi / 2)]`; the proofs are those of the original file. Names: the
original names with the suffix `Le` (statements: `…LeStatement`).

* `ae_lineGeom_liftOfLe`.
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
theorem ae_lineGeom_liftOfLe (h13 : Exist.Theorem13Statement.{u}) (hS3 : Tc.SB2EntranceNoCommonArcLeStatement.{u})
    {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u ψ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ) [Fact (ψ ≤ Real.pi / 2)] :
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
  filter_upwards [Tc.ae_lineGeomLe h13 hS3 HP, hS3 κ b jumps P h E k u ψ η ζ HP]
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
