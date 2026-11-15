/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2ViAbs
import InteractingSLE.Spec.Supplement.SBS3DwBase
import InteractingSLE.Spec.Supplement.SBS3DwVgClock
import InteractingSLE.Spec.Supplement.SB2VgClock
import InteractingSLE.Spec.Supplement.SBS3DwDrvLineIfaceR
import InteractingSLE.Spec.Supplement.SBS3DwTcRec
import InteractingSLE.Spec.Supplement.SBS3DwVcAe
import InteractingSLE.Spec.Supplement.SBS3DwVdAe
import InteractingSLE.Spec.Supplement.SBS3DwVdDrvAe
import InteractingSLE.Spec.Supplement.SBS3DwVeIn
import InteractingSLE.Spec.Supplement.SBS3DwVfReadAe
import InteractingSLE.Spec.Supplement.SBS3DwVgBad
import InteractingSLE.Spec.Supplement.SBS3DwVgCap
import InteractingSLE.Spec.Supplement.SBS3DwVgDense
import InteractingSLE.Spec.Supplement.SBS3DwVhLife

/-!
# Successor of `SB2ViAbs` with the upper angle `ψ ≤ π/2` (decision D22, ruling R121)

Worker PROVE-R6-CORNER (round 8). The declarations of `SB2ViAbs` that use Lemma S3 in SB2(1)'s form,
restated so that Lemma S3 enters as `Tc.SB2EntranceNoCommonArcLeStatement` (upper angle `ψ ≤ π/2`, PROVED
from Theorems 1.2–1.3 as `Tc.sb2EntranceNoCommonArcLeStatement_of_thm`). Every launch problem carries the bound
as an instance argument `[Fact (ψ ≤ Real.pi / 2)]`; the proofs are those of the original file. Names: the
original names with the suffix `Le` (statements: `…LeStatement`).

* `ae_absLift_goodLe`;
* `exists_measurable_absLiftLe`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Vi

open Lv Exist.Staged Exist.StagedLaw

section

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u ψ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
  {u₀ : ℂ → ℝ}

/-- **The absolute lift at a time before the lifetime**, almost surely at a launch on the entrance event: continuous
at `T`, equal to the reading at every good index, with good indices accumulating at `T`. -/
theorem ae_absLift_goodLe (h13 : Exist.Theorem13Statement.{u}) (hS3 : Tc.SB2EntranceNoCommonArcLeStatement.{u})
    (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ)
    [Fact (ψ ≤ Real.pi / 2)] (I : K2LaunchInputs κ b jumps P h E k u ψ)
    (D : EntranceUnion κ b jumps P h E k u η ζ u₀) :
    ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) → Ve.entT κ b jumps E k u η ζ ω < ζ ω →
      ∀ T : ℝ≥0, (T : ℝ≥0∞) < ζ ω →
        ContinuousAt (absLift κ b jumps E k u η ζ ω) T ∧
        (∀ i, goodIdx D I T i ω → absLift κ b jumps E k u η ζ ω (Lk.ratPt i) = absVal D I T i ω) ∧
        ∀ ε : ℝ, 0 < ε → ∃ i, goodIdx D I T i ω ∧ dist (Lk.ratPt i) T < ε := by
  classical
  filter_upwards [Vf.ae_readingLe h13 hS3 HP I D, Vg.ae_good_ratLe h13 hS3 HP I D, Vd.ae_lift_regularLe h13 hS3 HP]
    with ω hrd hgr hreg hF hT T hTζ
  obtain ⟨hγ0, hγc⟩ := hreg hF hT
  set TL := Ve.entT κ b jumps E k u η ζ ω with hTLdef
  have hTLtop : TL ≠ ⊤ := ne_top_of_lt hT
  have hTLc : ((TL.toNNReal : ℝ≥0) : ℝ≥0∞) = TL := ENNReal.coe_toNNReal hTLtop
  have hTLr : TL.toReal = (TL.toNNReal : ℝ) := rfl
  have hγ0 : Ve.flowLift κ b jumps E k u η ζ ω 0 = 0 := hγ0
  have hγc : ∀ s : ℝ≥0, ((TL.toNNReal + s : ℝ≥0) : ℝ≥0∞) < ζ ω →
      ContinuousAt (Ve.flowLift κ b jumps E k u η ζ ω) s := hγc
  have hlt : ∀ x : ℝ≥0, (x : ℝ≥0∞) < ζ ω → ((TL.toNNReal + (x - TL.toNNReal) : ℝ≥0) : ℝ≥0∞) < ζ ω := by
    intro x hx
    rcases le_total TL.toNNReal x with hle | hle
    · rw [add_tsub_cancel_of_le hle]; exact hx
    · rw [tsub_eq_zero_of_le hle, add_zero, hTLc]; exact hT
  refine ⟨?_, fun i hi => ?_, fun ε hε => ?_⟩
  · -- continuity at `T`
    show ContinuousAt (fun T' : ℝ≥0 => Ve.flowLift κ b jumps E k u η ζ ω (T' - TL.toNNReal)) T
    exact ContinuousAt.comp (f := fun T' : ℝ≥0 => T' - TL.toNNReal) (hγc _ (hlt T hTζ))
      (continuous_id.sub continuous_const).continuousAt
  · -- values at the good indices
    obtain ⟨hiT, hgood⟩ := hi
    have hiζ : ((Lk.ratPt i : ℝ≥0) : ℝ≥0∞) < ζ ω := lt_of_le_of_lt (ENNReal.coe_le_coe.2 hiT) hTζ
    have hq : ((Vf.ratQ i : ℚ≥0) : ℝ≥0) = Lk.ratPt i := Vf.coe_ratQ i
    simp only [absVal, hiT, ↓reduceIte]
    rcases hgood with hdom | hnone
    · rw [(hrd hF hT (Vf.ratQ i) (by rw [hq]; exact hiζ)).2 hdom]
      unfold absLift
      rw [hq]
    · have hnot := hnone i le_rfl
      have hzero : Vh.relRead D I (Vf.ratQ i) ω = 0 := by
        unfold Vh.relRead
        exact Set.indicator_of_notMem (show ω ∉ {ω | Vh.etaRead D (Vf.ratQ i) ω ∈ (I.chart ω).dom} from hnot) _
      rw [hzero]
      have hle : Lk.ratPt i ≤ TL.toNNReal := by
        by_contra hgt
        rw [not_le] at hgt
        obtain ⟨q, hq1, hq2, hqdom⟩ := hgr hF hT TL.toReal (Lk.ratPt i) le_rfl
          (by rw [hTLr]; exact NNReal.coe_lt_coe.2 hgt) (by rw [ENNReal.ofReal_coe_nnreal]; exact hiζ)
        obtain ⟨j, hj1, hj2⟩ := exists_ratQ_eq q
        exact hnone j (by rw [hj2, ← NNReal.coe_le_coe]; exact hq2.le) (hj1 ▸ hqdom)
      unfold absLift
      rw [tsub_eq_zero_of_le hle, hγ0]
  · -- density of the good indices at `T`
    rcases lt_or_ge TL.toNNReal T with hlt' | hle
    · have hTLT : TL.toReal < T := by rw [hTLr]; exact NNReal.coe_lt_coe.2 hlt'
      obtain ⟨q, hq1, hq2, hqdom⟩ := hgr hF hT (max TL.toReal ((T : ℝ) - ε / 2)) T (le_max_left _ _)
        (max_lt hTLT (by linarith)) (by rw [ENNReal.ofReal_coe_nnreal]; exact hTζ)
      obtain ⟨j, hj1, hj2⟩ := exists_ratQ_eq q
      refine ⟨j, ⟨by rw [hj2, ← NNReal.coe_le_coe]; exact hq2.le, Or.inl (hj1 ▸ hqdom)⟩, ?_⟩
      rw [hj2, NNReal.dist_eq, abs_lt]
      constructor <;> linarith [le_max_right TL.toReal ((T : ℝ) - ε / 2)]
    · obtain ⟨q, hqT, hqd⟩ := exists_nnrat_le_near T hε
      obtain ⟨j, hj1, hj2⟩ := exists_ratQ_eq q
      refine ⟨j, ⟨by rw [hj2]; exact hqT, Or.inr fun j' hj' hdom => ?_⟩, by rw [hj2]; exact hqd⟩
      have hj'T : Lk.ratPt j' ≤ T := hj'.trans (hj2 ▸ hqT)
      have hq' : ((Vf.ratQ j' : ℚ≥0) : ℝ≥0) = Lk.ratPt j' := Vf.coe_ratQ j'
      have h1 := (hrd hF hT (Vf.ratQ j') (by rw [hq']; exact lt_of_le_of_lt (ENNReal.coe_le_coe.2 hj'T) hTζ)).1 hdom
      rw [hq', ← hTLc, ENNReal.coe_lt_coe] at h1
      exact absurd (h1.trans_le (hj'T.trans hle)) (lt_irrefl _)

open scoped Classical in
/-- **The absolute lift is measurable for the completed line filtration** at every time, on a measurable conull good
event inside the entrance event and below the lifetime. -/
theorem exists_measurable_absLiftLe (h13 : Exist.Theorem13Statement.{u})
    (hS3 : Tc.SB2EntranceNoCommonArcLeStatement.{u}) (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ)
    [Fact (ψ ≤ Real.pi / 2)]
    (I : K2LaunchInputs κ b jumps P h E k u ψ) (D : EntranceUnion κ b jumps P h E k u η ζ u₀) :
    ∃ G : Set Ω, MeasurableSet G ∧ P Gᶜ = 0 ∧ ∀ T : ℝ≥0, Measurable[D.lineFiltC HP T] (fun ω =>
      if ω ∈ G ∩ D.event ∩ {ω | (T : ℝ≥0∞) < ζ ω} then absLift κ b jumps E k u η ζ ω T else 0) := by
  have hgood : ∀ᵐ ω ∂P, (ω ∈ launchSet κ b jumps E (k + 1) →
      (ω ∈ D.event ↔ firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω)) < ζ ω)) ∧
      (ω ∈ launchSet κ b jumps E (k + 1) → Ve.entT κ b jumps E k u η ζ ω < ζ ω →
        ∀ T : ℝ≥0, (T : ℝ≥0∞) < ζ ω →
          ContinuousAt (absLift κ b jumps E k u η ζ ω) T ∧
          (∀ i, goodIdx D I T i ω → absLift κ b jumps E k u η ζ ω (Lk.ratPt i) = absVal D I T i ω) ∧
          ∀ ε : ℝ, 0 < ε → ∃ i, goodIdx D I T i ω ∧ dist (Lk.ratPt i) T < ε) := by
    filter_upwards [D.ae_mem_event_iff, ae_absLift_goodLe h13 hS3 HP I D] with ω hev hgd
    exact ⟨hev, hgd⟩
  obtain ⟨G, hGm, hGnull, hG⟩ := Vf.exists_measurable_conull hgood
  refine ⟨G, hGm, hGnull, fun T => ?_⟩
  have hGc : MeasurableSet[D.lineFiltC HP T] G :=
    Vf.measurableSet_cmpl_of_conull (𝒢 := D.absMarks (T : ℝ≥0∞)) hGm hGnull
  have hEc : MeasurableSet[D.lineFiltC HP T] D.event := D.marks_le_lineFiltC HP T _ (D.measurableSet_event HP)
  have hζc : MeasurableSet[D.lineFiltC HP T] {ω | (T : ℝ≥0∞) < ζ ω} :=
    D.lineFilt_le_lineFiltC HP T _ (Vg.EntranceUnion.measurableSet_lt_lifetime D T)
  have hgood' : ∀ i, MeasurableSet[D.lineFiltC HP T] {ω | goodIdx D I T i ω} := fun i =>
    D.lineFilt_le_lineFiltC HP T _ (measurableSet_goodIdx D I T i)
  have hV' : ∀ i, Measurable[D.lineFiltC HP T] (absVal D I T i) := fun i =>
    (measurable_absVal D I T i).mono (D.lineFilt_le_lineFiltC HP T) le_rfl
  have hfacts : ∀ ω ∈ G ∩ D.event ∩ {ω | (T : ℝ≥0∞) < ζ ω},
      ContinuousAt (absLift κ b jumps E k u η ζ ω) T ∧
      (∀ i, goodIdx D I T i ω → absLift κ b jumps E k u η ζ ω (Lk.ratPt i) = absVal D I T i ω) ∧
      ∀ ε : ℝ, 0 < ε → ∃ i, goodIdx D I T i ω ∧ dist (Lk.ratPt i) T < ε := by
    rintro ω ⟨⟨hωG, hωE⟩, hTζ⟩
    have hl := D.event_subset hωE
    exact (hG ω hωG).2 hl (((hG ω hωG).1 hl).1 hωE) T hTζ
  convert @Vc.measurable_of_dense_good_at Ω (D.lineFiltC HP T) (fun ω => absLift κ b jumps E k u η ζ ω)
    (absVal D I T) (goodIdx D I T) hgood' hV' _ ((hGc.inter hEc).inter hζc) T
    (fun ω hω => (hfacts ω hω).1) (fun ω hω => (hfacts ω hω).2.1) (fun ω hω => (hfacts ω hω).2.2)

end

end InteractingSLE.Theorem14.SB.Vi
