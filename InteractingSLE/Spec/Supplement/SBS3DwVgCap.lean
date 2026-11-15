/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2VgCap
import InteractingSLE.Spec.Supplement.SBS3DwBase
import InteractingSLE.Spec.Supplement.SBS3DwVgDense
import InteractingSLE.Spec.Supplement.SB2VgDense
import InteractingSLE.Spec.Restart.ClockMeasCap
import InteractingSLE.Spec.Sec5.CrossRestartLawPath
import InteractingSLE.Spec.Supplement.SBS3DwDrvLineIfaceR
import InteractingSLE.Spec.Supplement.SBS3DwTcRec
import InteractingSLE.Spec.Supplement.SBS3DwVcAe
import InteractingSLE.Spec.Supplement.SBS3DwVdAe
import InteractingSLE.Spec.Supplement.SBS3DwVdDrvAe
import InteractingSLE.Spec.Supplement.SBS3DwVeIn
import InteractingSLE.Spec.Supplement.SBS3DwVfReadAe
import InteractingSLE.Spec.Supplement.SBS3DwVgBad
import InteractingSLE.Spec.Supplement.SBS3DwVhLife

/-!
# Successor of `SB2VgCap` with the upper angle `ψ ≤ π/2` (decision D22, ruling R121)

Worker PROVE-R6-CORNER (round 8). The declarations of `SB2VgCap` that use Lemma S3 in SB2(1)'s form,
restated so that Lemma S3 enters as `Tc.SB2EntranceNoCommonArcLeStatement` (upper angle `ψ ≤ π/2`, PROVED
from Theorems 1.2–1.3 as `Tc.sb2EntranceNoCommonArcLeStatement_of_thm`). Every launch problem carries the bound
as an instance argument `[Fact (ψ ≤ Real.pi / 2)]`; the proofs are those of the original file. Names: the
original names with the suffix `Le` (statements: `…LeStatement`).

* `ae_clockOf_eq_capReadLe`.
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

section

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u ψ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
  {u₀ : ℂ → ℝ}

/-- **The relative clock is the capacity of the good readings**, almost surely, before the lifetime. -/
theorem ae_clockOf_eq_capReadLe (h13 : Exist.Theorem13Statement.{u})
    (hS3 : Tc.SB2EntranceNoCommonArcLeStatement.{u}) (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ)
    [Fact (ψ ≤ Real.pi / 2)]
    (I : K2LaunchInputs κ b jumps P h E k u ψ) (D : EntranceUnion κ b jumps P h E k u η ζ u₀) :
    ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) → Ve.entT κ b jumps E k u η ζ ω < ζ ω →
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω →
        Vc.clockOf (Ve.flowLift κ b jumps E k u η ζ ω) (Ve.entT κ b jumps E k u η ζ ω).toNNReal (ζ ω) t =
          ENNReal.ofReal (capRead D I t ω) := by
  classical
  filter_upwards [Vf.ae_readingLe h13 hS3 HP I D, ae_good_ratLe h13 hS3 HP I D, Vd.ae_lift_regularLe h13 hS3 HP,
    Vd.ae_clockDataLe h13 hS3 HP] with ω hrd hgr hreg hcd hF hT t htζ
  obtain ⟨hγ0, hγc⟩ := hreg hF hT
  obtain ⟨hcap0, hloc⟩ := hcd hF hT
  set TL := Ve.entT κ b jumps E k u η ζ ω with hTLdef
  set γ : ℝ≥0 → ℂ := Ve.flowLift κ b jumps E k u η ζ ω with hγdef
  have hTLtop : TL ≠ ⊤ := ne_top_of_lt hT
  have hTLc : ((TL.toNNReal : ℝ≥0) : ℝ≥0∞) = TL := ENNReal.coe_toNNReal hTLtop
  have hTLr : TL.toReal = (TL.toNNReal : ℝ) := rfl
  -- the per-sample facts, stated for `γ`
  have hγ0 : γ 0 = 0 := hγ0
  have hγc : ∀ s : ℝ≥0, ((TL.toNNReal + s : ℝ≥0) : ℝ≥0∞) < ζ ω → ContinuousAt γ s := hγc
  have hcap0 : Sec7.Lemma71C.capClock (fun r : ℝ => γ r.toNNReal) 0 = 0 := hcap0
  have hloc : ∀ T₁ : ℝ≥0, TL.toNNReal ≤ T₁ → (T₁ : ℝ≥0∞) < ζ ω →
      ContinuousOn (Sec7.Lemma71C.capClock fun r : ℝ => γ r.toNNReal) (Icc 0 ((T₁ : ℝ) - TL.toNNReal)) ∧
        MonotoneOn (Sec7.Lemma71C.capClock fun r : ℝ => γ r.toNNReal) (Icc 0 ((T₁ : ℝ) - TL.toNNReal)) := hloc
  set s : ℝ≥0 := t - TL.toNNReal with hs
  have hTLs : ((TL.toNNReal + s : ℝ≥0) : ℝ≥0∞) < ζ ω := by
    rcases le_total TL.toNNReal t with hle | hle
    · rw [hs, add_tsub_cancel_of_le hle]; exact htζ
    · rw [hs, tsub_eq_zero_of_le hle, add_zero, hTLc]; exact hT
  -- the lift is continuous on `[0, s]`
  have hcs : ContinuousOn γ (Icc 0 s) := fun x hx =>
    (hγc x (lt_of_le_of_lt (ENNReal.coe_le_coe.2 (add_le_add le_rfl hx.2)) hTLs)).continuousWithinAt
  -- the range of the readings: inside the prefix, and dense in it
  have hsub : range (fun q => clockRead D I t q ω) ⊆ γ '' Icc 0 s := by
    rintro _ ⟨q, rfl⟩
    by_cases hc : ((q : ℝ≥0) : ℝ≥0∞) ≤ t ∧ Vh.etaRead D q ω ∈ (I.chart ω).dom
    · obtain ⟨hqt, hqg⟩ := hc
      have hqζ : ((q : ℝ≥0) : ℝ≥0∞) < ζ ω := lt_of_le_of_lt hqt htζ
      simp only [clockRead, hqt, hqg, and_self, ↓reduceIte]
      rw [(hrd hF hT q hqζ).2 hqg]
      exact ⟨(q : ℝ≥0) - TL.toNNReal, ⟨zero_le, tsub_le_tsub_right (ENNReal.coe_le_coe.1 hqt) _⟩, rfl⟩
    · simp only [clockRead, hc, ↓reduceIte]
      exact ⟨0, ⟨le_rfl, zero_le⟩, hγ0⟩
  have hzero : (0 : ℂ) ∈ range (fun q => clockRead D I t q ω) := by
    obtain ⟨n, hn⟩ := exists_nat_gt (t : ℝ)
    refine ⟨(n : ℚ≥0), ?_⟩
    have hnt : ¬ (((n : ℚ≥0) : ℝ≥0) : ℝ≥0∞) ≤ t := by
      rw [not_le, ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe]; push_cast; exact hn
    simp only [clockRead, hnt, false_and, ↓reduceIte]
  have hdense : γ '' Icc 0 s ⊆ closure (range fun q => clockRead D I t q ω) := by
    rintro _ ⟨s', hs', rfl⟩
    rcases (zero_le : (0 : ℝ≥0) ≤ s).eq_or_lt with hs0 | hspos
    · have hs'0 : s' = 0 := le_antisymm (by rw [hs0]; exact hs'.2) zero_le
      rw [hs'0, hγ0]; exact subset_closure hzero
    · rw [Metric.mem_closure_iff]
      intro ε hε
      have hTLt : TL.toNNReal < t := by
        by_contra hle
        rw [not_lt] at hle
        rw [hs, tsub_eq_zero_of_le hle] at hspos
        exact lt_irrefl _ hspos
      have hsr : (s : ℝ) = (t : ℝ) - TL.toNNReal := by rw [hs, NNReal.coe_sub hTLt.le]
      have hγcs' : ContinuousAt γ s' :=
        hγc s' (lt_of_le_of_lt (ENNReal.coe_le_coe.2 (add_le_add le_rfl hs'.2)) hTLs)
      obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.1 hγcs' ε hε
      have hs'r : (s' : ℝ) ≤ s := NNReal.coe_le_coe.2 hs'.2
      have hs'0 : (0 : ℝ) ≤ s' := s'.2
      have hspos' : (0 : ℝ) < s := NNReal.coe_pos.2 hspos
      set a : ℝ := TL.toReal + max ((s' : ℝ) - δ) 0 with ha
      set c : ℝ := TL.toReal + min ((s' : ℝ) + δ) s with hc
      have hac : a < c := by
        rw [ha, hc]
        have : max ((s' : ℝ) - δ) 0 < min ((s' : ℝ) + δ) s :=
          max_lt (lt_min (by linarith) (by linarith)) (lt_min (by linarith) hspos')
        linarith
      have hcζ : ENNReal.ofReal c < ζ ω := by
        refine lt_of_le_of_lt ?_ htζ
        rw [← ENNReal.ofReal_coe_nnreal]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hc, hTLr]
        have := min_le_right ((s' : ℝ) + δ) s
        linarith
      obtain ⟨q, hq1, hq2, hqg⟩ := hgr hF hT a c (by rw [ha]; linarith [le_max_right ((s' : ℝ) - δ) 0]) hac hcζ
      have hqtr : ((q : ℝ≥0) : ℝ) ≤ t := by
        have := min_le_right ((s' : ℝ) + δ) s
        rw [hc, hTLr] at hq2
        linarith
      have hqt : ((q : ℝ≥0) : ℝ≥0∞) ≤ t := ENNReal.coe_le_coe.2 (NNReal.coe_le_coe.1 hqtr)
      have hqζ : ((q : ℝ≥0) : ℝ≥0∞) < ζ ω := lt_of_le_of_lt hqt htζ
      have hTLq : TL.toNNReal ≤ (q : ℝ≥0) := by
        rw [← NNReal.coe_le_coe]
        have := le_max_right ((s' : ℝ) - δ) 0
        rw [ha, hTLr] at hq1
        linarith
      refine ⟨clockRead D I t q ω, ⟨q, rfl⟩, ?_⟩
      have hval : clockRead D I t q ω = γ ((q : ℝ≥0) - TL.toNNReal) := by
        simp only [clockRead, hqt, hqg, and_self, ↓reduceIte]
        exact (hrd hF hT q hqζ).2 hqg
      rw [hval, dist_comm]
      apply hball
      rw [NNReal.dist_eq, NNReal.coe_sub hTLq, abs_lt]
      have h1 := le_max_left ((s' : ℝ) - δ) 0
      have h2 := min_le_left ((s' : ℝ) + δ) s
      rw [ha, hTLr] at hq1
      rw [hc, hTLr] at hq2
      constructor <;> linarith
  have hclosed : IsClosed (γ '' Icc 0 s) := (isCompact_Icc.image_of_continuousOn hcs).isClosed
  have hcl_eq : closure (range fun q => clockRead D I t q ω) = γ '' Icc 0 s :=
    le_antisymm (closure_minimal hsub hclosed) hdense
  have hhit : WholeField.hcapHit (range fun q => clockRead D I t q ω) =
      ENNReal.ofReal (2 * Sec7.Lemma71C.capClock (fun r : ℝ => γ r.toNNReal) (s : ℝ)) := by
    rw [← Sec5.CrossRestart.hcapHit_closure, hcl_eq, Restart.hcapHit_image_eq hcs (by rw [hγ0]; simp)]
    congr 1
    have himg : (fun r : ℝ => γ r.toNNReal) '' Icc 0 (s : ℝ) = γ '' Icc 0 s := by
      have := Vd.image_liftR γ (NNReal.coe_nonneg s)
      rw [Real.toNNReal_coe] at this
      exact this
    unfold Sec7.Lemma71C.capClock
    rw [himg]
    ring
  unfold capRead
  rw [hhit, ofReal_toReal_ofReal_two]
  rcases le_or_gt t TL.toNNReal with hle | hlt
  · rw [Vc.clockOf_eq_zero_of_le hle hcap0]
    have hs0 : s = 0 := by rw [hs]; exact tsub_eq_zero_of_le hle
    rw [hs0, NNReal.coe_zero, hcap0, ENNReal.ofReal_zero]
  · obtain ⟨-, hmono⟩ := hloc t hlt.le htζ
    rw [Vc.clockOf_eq hlt.le htζ hmono, hs, NNReal.coe_sub hlt.le]

end

end InteractingSLE.Theorem14.SB.Vg
