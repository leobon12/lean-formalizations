/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2VgBad
import InteractingSLE.Spec.Supplement.SBS3DwBase
import InteractingSLE.Spec.Supplement.SBS3DwVcAe
import InteractingSLE.Spec.Supplement.SB2VcAe
import InteractingSLE.Spec.Supplement.SBS3DwVeIn
import InteractingSLE.Spec.Supplement.SB2VeIn
import InteractingSLE.Spec.Supplement.SBS3DwDrvLineIfaceR
import InteractingSLE.Spec.Supplement.SBS3DwTcRec
import InteractingSLE.Spec.Supplement.SBS3DwVdAe
import InteractingSLE.Spec.Supplement.SBS3DwVdDrvAe
import InteractingSLE.Spec.Supplement.SBS3DwVhLife

/-!
# Successor of `SB2VgBad` with the upper angle `ψ ≤ π/2` (decision D22, ruling R121)

Worker PROVE-R6-CORNER (round 8). The declarations of `SB2VgBad` that use Lemma S3 in SB2(1)'s form,
restated so that Lemma S3 enters as `Tc.SB2EntranceNoCommonArcLeStatement` (upper angle `ψ ≤ π/2`, PROVED
from Theorems 1.2–1.3 as `Tc.sb2EntranceNoCommonArcLeStatement_of_thm`). Every launch problem carries the bound
as an instance argument `[Fact (ψ ≤ Real.pi / 2)]`; the proofs are those of the original file. Names: the
original names with the suffix `Le` (statements: `…LeStatement`).

* `ae_bad_interior_emptyLe`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Vg

open Lv Exist.Staged Exist.StagedLaw

/-- **The flow is outside the chart domain only on a nowhere dense set of times after the entrance**, a.s. -/
theorem ae_bad_interior_emptyLe (h13 : Exist.Theorem13Statement.{u}) (hS3 : Tc.SB2EntranceNoCommonArcLeStatement.{u})
    {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u ψ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ) [Fact (ψ ≤ Real.pi / 2)] :
    ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) → Ve.entT κ b jumps E k u η ζ ω < ζ ω →
      ∀ S₁ : ℝ, 0 < S₁ → ENNReal.ofReal ((Ve.entT κ b jumps E k u η ζ ω).toReal + S₁) < ζ ω →
        interior {r ∈ Ioo (0 : ℝ) S₁ | η ω ((Ve.entT κ b jumps E k u η ζ ω).toNNReal + r.toNNReal) - u ∉
          H \ fillH ((fun z => z - (u : ℂ)) '' lowerPrefix κ b jumps E (k + 1) u ω)} = ∅ := by
  filter_upwards [Tc.ae_lineGeomLe h13 hS3 HP, hS3 κ b jumps P h E k u ψ η ζ HP] with ω hgeo hno hF hT S₁ hS₁ hS₁ζ
  set TL := Ve.entT κ b jumps E k u η ζ ω with hTLdef
  have hTLtop : TL ≠ ⊤ := ne_top_of_lt hT
  have hTLc : ((TL.toNNReal : ℝ≥0) : ℝ≥0∞) = TL := ENNReal.coe_toNNReal hTLtop
  have hTLr : TL.toReal = (TL.toNNReal : ℝ) := rfl
  -- a horizon `T` strictly between `T_L + S₁` and `ζ`
  obtain ⟨T, hT1, hTζ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hS₁ζ
  have hT1' : TL.toReal + S₁ < T := by
    have hnn : 0 ≤ TL.toReal + S₁ := by rw [hTLr]; positivity
    have := (ENNReal.ofReal_lt_iff_lt_toReal hnn ENNReal.coe_ne_top).1 hT1
    simpa using this
  have hvis : TL < T := by
    rw [← hTLc]; refine ENNReal.coe_lt_coe.2 (NNReal.coe_lt_coe.1 ?_); rw [hTLr] at hT1'; linarith
  obtain ⟨p, g, β', γ, tL, Wr, ηr, hp, -, hw, hag, hrc⟩ := hgeo hF T hTζ.le hvis S₁ hS₁ hT1'
  have htt : tL = TL.toNNReal := by rw [← ENNReal.coe_inj, hTLc]; exact hw.2.2.2.2.1
  subst htt
  obtain ⟨hpc, hp0, hpH, -, hpA⟩ := hp
  obtain ⟨hβ', hβ'0, hβ'A, htL, hTL, -, -, -⟩ := hw
  obtain ⟨-, hnR⟩ := hrc
  obtain ⟨-, tL', htL', -, -, -, hhull⟩ := SB.s2HullStatement p β' hpc hp0 hpH hβ' hβ'0 hβ'A
  have htt' : tL' = TL.toNNReal := hβ'.2.1 (htL'.trans htL.symm)
  rw [htt'] at hhull
  have hno' : ∀ s₁ s₂ : ℝ≥0, TL.toNNReal ≤ s₁ → s₁ < s₂ → (s₂ : ℝ) ≤ TL.toNNReal + S₁ →
      ¬ β' '' Ioo s₁ s₂ ⊆ p '' Icc 0 1 := by
    intro s₁ s₂ h1 h12 h2 hsub
    have hs₂T : (s₂ : ℝ) < T := by rw [hTLr] at hT1'; linarith
    refine hno hF s₁ s₂ (hTL ▸ ENNReal.coe_le_coe.2 h1) h12
      ((ENNReal.coe_le_coe.2 (NNReal.coe_le_coe.1 hs₂T.le)).trans hTζ.le) ?_
    rintro _ ⟨t, ht, rfl⟩
    have htS : (t : ℝ) < (TL.toNNReal : ℝ) + S₁ := lt_of_lt_of_le (NNReal.coe_lt_coe.2 ht.2) h2
    have hmem : β' t ∈ p '' Icc 0 1 := hsub ⟨t, ht, rfl⟩
    rw [hpA, hag t htS] at hmem
    obtain ⟨z, hz, hze⟩ := hmem
    have : z = η ω t := by linear_combination hze
    exact this ▸ hz
  have hcl : IsClosed (p '' Icc 0 1) := (isCompact_Icc.image_of_continuousOn hpc).isClosed
  have hbad := Vh.interior_notMem_dom_eq_empty hβ'.1 hβ'.2.2.1 hhull hnR (Tc.interior_mem_eq_empty_of_noArc hcl hno')
  rw [hpA] at hbad
  -- read on the flow
  refine subset_empty_iff.1 (hbad ▸ interior_mono fun r hr => ⟨hr.1, ?_⟩)
  have hrS : ((TL.toNNReal + r.toNNReal : ℝ≥0) : ℝ) < (TL.toNNReal : ℝ) + S₁ := by
    rw [NNReal.coe_add, Real.coe_toNNReal _ hr.1.1.le]; linarith [hr.1.2]
  rw [hag _ hrS]
  exact hr.2

end InteractingSLE.Theorem14.SB.Vg
