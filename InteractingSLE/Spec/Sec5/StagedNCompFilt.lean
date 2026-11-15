/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.StagedNCompGal
import InteractingSLE.Spec.Sec5.StagedS5Filt

/-!
# The flag candidate's chart clause for its Galmarino filtration, with no remaining hypothesis

Packet PROVE-STAGED-NODECOMP. PROVE-STAGED-S5's `StagedS5Av` and `StagedS5Filt` (candidate part) for the flag
candidate of arbitrary angle flags (`StagedNCompInst`, `StagedNCompGal`); the generic parts of S5 are reused.

* `candTsF_succ`, `candTsF_bounds`, `candTsF_eq_candTq`: the switch own times;
* **`exists_candSigmaF_ae_eq_candWinF_s4Av`** (`hAv`);
* `measurableSet_candFiltF_of_stopD`, `measurable_candFiltF_of_stopD` (the Galmarino transfer);
* **`adaptedBefore_s3W/s3VL/s3VR_candFiltF`**, **`isMeasChart_s3Chart_candFiltF`**, `measurableSet_s3Alive_candFiltF`;
* **`candErF_candFF_candFiltF`** (`hEr`, `hFm`) and **`ae_condExp_candFiltF_full`**: the flag candidate's chart clause
  at every fixed restarted time for `candFiltF`, with no hypothesis.

R48: the only named input is `h44 : Theorem12ParamCond44Statement` (R74).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal Real
open QuantumZipper (H fwdHull)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Sec5.CrossCond.StagedNComp

open WangWu hiding ratPt exists_ratPt_dist_lt
open WangWu.ImgWord LawUnique GlueCond Cond44Ref Word49 StagedS3 StagedS4 StagedS5
open Restart Exist.StagedLaw Exist.Staged
open Sec7.AdmCode Prop513TreeExtract Prop513Schedule Prop513Target Prop59Pieces StagedRepLater Prop59NodeTree
open Sec4 (IsStripGFF IsStripCounterflowDriver)
open Sec7.Lemma71C (capClock)
open WangWu.ChartConst (dyq dyqQ dyqQ_coe)
open StagedFinal (imgStageRhoL imgStageRhoR)

section Times

variable {fl : ℕ → Bool}
variable {ℓ : ℕ} {t : Fin ℓ → ℝ≥0}

theorem candTsF_succ (hv : IsValid ℓ t) (j : Fin ℓ) : candTsF fl ℓ t (j + 1) = (oTime (t j) : ℝ) := by
  rw [candTsF, candSchedF, startT_schedD_mkSchedF hv (lt_add_one _) j.2]

theorem candTsF_bounds (hv : IsValid ℓ t) (j : Fin ℓ) :
    0 ≤ candTsF fl ℓ t (j + 1) ∧ candTsF fl ℓ t (j + 1) ≤ (lastO ℓ t : ℝ) := by
  rw [candTsF_succ hv j]
  exact ⟨by exact_mod_cast (oTime_pos hv _).le, by exact_mod_cast oTime_le_lastO hv _⟩

theorem candTsF_eq_candTq (hv : IsValid ℓ t) (j : Fin ℓ) : candTsF fl ℓ t (j + 1) = (candTq ℓ t (j + 1) : ℝ) := by
  rw [candTsF_succ hv j]
  have hj : (j : ℕ) + 1 - 1 < ℓ := by simp
  have e : candTq ℓ t (j + 1) = oTime (t ⟨(j : ℕ) + 1 - 1, hj⟩) := by simp only [candTq, hj, ↓reduceDIte]
  rw [e]
  congr 3

end Times

section Cand

variable (x₀ : ℝ) (h44 : Theorem12ParamCond44Statement.{0}) {κ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  (hb : IsFig51Bounds κ a b a' b') {Ω : Type} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ)
  (ζ : Ω → ℝ≥0∞) (fl : ℕ → Bool)

omit [StandardBorelSpace Ω] in
/-- On a window at the own time `Q`, the restarted validity event at `Q` is the template's forward validity event. -/
theorem candWinF_inter_s4Av_eq (hhm : Measurable h) {ℓ : ℕ} {t : Fin ℓ → ℝ≥0} {s : ℝ≥0}
    (φ : TestOn upperHalfPlaneOpens) (r : ℝ≥0) (Q : ℚ) (hQ0 : (0 : ℝ) ≤ Q) :
    candWinF x₀ h44 hκ hκ4 hb P h W ζ fl hhm ℓ t s Q r ∩
        s4Av s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hhm ℓ t s) (lastO ℓ t : ℝ) φ
          (Q : ℝ).toNNReal =
      candWinF x₀ h44 hκ hκ4 hb P h W ζ fl hhm ℓ t s Q r ∩
        cfAv s (fun _ => ⊤) (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hhm ℓ t s) φ
          (Q : ℝ).toNNReal := by
  set Wc := candWF x₀ h44 hκ hκ4 hb h fl ℓ t with hWc
  set Eg := candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hhm ℓ t s with hEgdef
  have hEg : ∀ p ∈ Eg, IsGood49 s (fun _ => ⊤) Wc p := fun p hp => isGood49_of_mem_glueGood p hp
  have hQQ : (((Q : ℝ).toNNReal : ℝ≥0) : ℝ) = Q := Real.coe_toNNReal _ hQ0
  ext p
  simp only [mem_inter_iff]
  refine and_congr_right fun hW => ?_
  have hW' := hW
  rw [candWinF, mem_ofPred_eq] at hW'
  obtain ⟨halive, hlt, hQP, -⟩ := hW'
  have hτQ : (lastO ℓ t : ℝ) ≤ Q := by exact_mod_cast hlt.le
  have hav := isChartAvoid_s3_iff hEg halive hQP hτQ φ
  have hav' := isChartAvoid_capClock_iff' hEg halive.1 hQP φ
  simp only [s4Av, cfAv, s4R, mem_ofPred_eq, hQQ]
  constructor
  · rintro ⟨-, -, -, h⟩
    exact ⟨halive.1, hQP, hav'.2 (hav.1 h)⟩
  · rintro ⟨-, -, h⟩
    exact ⟨halive, by exact_mod_cast hlt, hQP, hav.2 (hav'.1 h)⟩

include hκ4 in
/-- **`hAv`: on the window at a dyadic own time, the restarted validity event is almost surely an event of the
marks.** -/
theorem exists_candSigmaF_ae_eq_candWinF_s4Av (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) (us : ℂ → ℝ) {ℓ : ℕ} {t : Fin ℓ → ℝ≥0}
    (hv : IsValid ℓ t) {s : ℝ≥0} (hs : 0 < s) (φ : TestOn upperHalfPlaneOpens) (r : ℝ≥0) (n k : ℕ)
    (hq : lastO ℓ t < dyqQ n k) :
    ∃ B, MeasurableSet[candSigmaF x₀ h44 hκ hκ4 hb h fl us ℓ t (dyqQ n k) s] B ∧
      B =ᵐ[candMu x₀ (κ := κ) P h W ζ hG.1] (candWinF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s (dyqQ n k) r ∩
        s4Av s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s) (lastO ℓ t : ℝ) φ
          (dyq n k)) := by
  set Wc := candWF x₀ h44 hκ hκ4 hb h fl ℓ t with hWc
  set Eg := candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s with hEgdef
  have hEg : ∀ p ∈ Eg, IsGood49 s (fun _ => ⊤) Wc p := fun p hp => isGood49_of_mem_glueGood p hp
  have hQpos : 0 < dyqQ n k := lt_of_le_of_lt (lastO_nonneg hv) hq
  have hQ0 : (0 : ℝ) ≤ (dyqQ n k : ℝ) := by exact_mod_cast hQpos.le
  have hdq : dyq n k = ((dyqQ n k : ℚ) : ℝ).toNNReal := by
    rw [dyqQ_coe, Real.toNNReal_coe]
  have hgood : ∀ᵐ p ∂(candMu x₀ (κ := κ) P h W ζ hG.1), p ∈ Eg ∧
      Aux50Hit.IsGoodPath Wc (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ) (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ) (fun _ => ⊤) p.1 :=
    (ae_good_candF x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf ℓ t hv hs).mono fun p hp => ⟨hp.1, hp.2.1⟩
  obtain ⟨B₁, hB₁, hB₁e⟩ := exists_candMarksF_ae_eq_candWinF x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs (dyqQ n k) r
  rw [candMarksF_of_lt x₀ h44 hκ hκ4 hb h fl hq] at hB₁
  obtain ⟨B', hB', hB'e⟩ := exists_marks_ae_eq_avoid (μ := candMu x₀ (κ := κ) P h W ζ hG.1) hQpos hEg hgood φ
  obtain ⟨B₂, hB₂, hB₂e⟩ := exists_candSigmaF_ae_eq_of_cfGlueMarks x₀ h44 hκ hκ4 hb P h W ζ fl hG us hv hq s hB'
  refine ⟨B₁ ∩ B₂, hB₁.inter hB₂, (hB₁e.inter (hB₂e.trans hB'e)).trans ?_⟩
  rw [hdq, candWinF_inter_s4Av_eq x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 φ r (dyqQ n k) hQ0]

end Cand

section Cand

variable (x₀ : ℝ) (h44 : Theorem12ParamCond44Statement.{0}) {κ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  (hb : IsFig51Bounds κ a b a' b') {Ω : Type} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ)
  (ζ : Ω → ℝ≥0∞) (fl : ℕ → Bool)

omit [StandardBorelSpace Ω] in
theorem candEgF_good (hhm : Measurable h) (ℓ : ℕ) (t : Fin ℓ → ℝ≥0) (s : ℝ≥0) :
    ∀ p ∈ candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hhm ℓ t s, IsGood49 s (fun _ => ⊤) (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) p :=
  fun p hp => isGood49_of_mem_glueGood p hp

include hκ4 in
/-- **An event read from the stopped data on every window is an event of the Galmarino filtration.** -/
theorem measurableSet_candFiltF_of_stopD (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) (us : ℂ → ℝ) {ℓ : ℕ} {t : Fin ℓ → ℝ≥0}
    (hv : IsValid ℓ t) {s : ℝ≥0} (hs : 0 < s) {r : ℝ≥0} {A : Set (Ω × HistorySpace 0 0)} (hA : MeasurableSet A)
    (hrep : ∀ q : ℚ, lastO ℓ t < q → ∃ C : Set (Y49 0 0), MeasurableSet C ∧
      ∀ p ∈ candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s,
        Aux50Hit.IsGoodPath (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ)
          (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ) (fun _ => ⊤) p.1 →
        p ∈ candWinF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s q r →
        (p ∈ A ↔ stopD (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ)
          (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ) (fun _ => ⊤) q s p ∈ C)) :
    MeasurableSet[candFiltF x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs r] A := by
  rw [candFiltF, measurableSet_galFilt_iff]
  refine ⟨hA, fun q => ?_⟩
  by_cases hq : lastO ℓ t < q
  · rw [candMarksF_of_lt x₀ h44 hκ hκ4 hb h fl hq]
    have hEg := candEgF_good x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s
    have hqpos : 0 < q := lt_of_le_of_lt (lastO_nonneg hv) hq
    have hτ0 : (0 : ℝ) ≤ (lastO ℓ t : ℝ) := by exact_mod_cast lastO_nonneg hv
    have hτq : ((lastO ℓ t : ℚ) : ℝ) ≤ q := by exact_mod_cast hq.le
    obtain ⟨C, hC, hAC⟩ := hrep q hq
    obtain ⟨CW, hCW, hWC⟩ := exists_measurableSet_of_subtypeD
      (measurableSet_s5Win (s := s) (q := q) (τ := lastO ℓ t) hτ0 hτq r)
    obtain ⟨B, hB, hBe⟩ := exists_candSigmaF_ae_eq_stopD x₀ h44 hκ hκ4 hb P h W ζ fl hG us hv hq s (hC.inter hCW)
    refine ⟨B, hB, hBe.trans ?_⟩
    filter_upwards [ae_good_candF x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf ℓ t hv hs] with p hpg
    obtain ⟨hpE, hg, -⟩ := hpg
    have hwin : p ∈ candWinF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s q r ↔
        stopD (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ)
          (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ) (fun _ => ⊤) q s p ∈ CW := by
      change _ ↔ (stopX hqpos hEg hpE hg).1 ∈ CW
      rw [← (hWC (stopX hqpos hEg hpE hg)), mem_s5Win_iff hqpos hEg hpE hg hq.le r]
      simp only [candWinF, mem_ofPred_eq]
      exact ⟨fun h => ⟨h.1, h.2.2.1, h.2.2.2⟩, fun h => ⟨h.1, hq, h.2.1, h.2.2⟩⟩
    show (p ∈ stopD _ _ _ _ q s ⁻¹' (C ∩ CW)) = (p ∈ A ∩ _)
    rw [eq_iff_iff, mem_preimage, mem_inter_iff, mem_inter_iff]
    constructor
    · rintro ⟨h1, h2⟩
      have hw := hwin.2 h2
      exact ⟨(hAC p hpE hg hw).2 h1, hw⟩
    · rintro ⟨h1, h2⟩
      exact ⟨(hAC p hpE hg h2).1 h1, hwin.1 h2⟩
  · refine ⟨∅, @MeasurableSet.empty _ (candMarksF x₀ h44 hκ hκ4 hb h fl us ℓ t s q), Eventually.of_forall fun p => ?_⟩
    show (p ∈ (∅ : Set (Ω × HistorySpace 0 0))) = (p ∈ A ∩ _)
    rw [eq_iff_iff]
    simp only [mem_empty_iff_false, false_iff, mem_inter_iff, candWinF, mem_ofPred_eq, not_and]
    intro _ _ h
    exact absurd h hq

include hκ4 in
/-- **A function read from the stopped data on every window is measurable for the Galmarino filtration.** -/
theorem measurable_candFiltF_of_stopD (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) (us : ℂ → ℝ) {ℓ : ℕ} {t : Fin ℓ → ℝ≥0}
    (hv : IsValid ℓ t) {s : ℝ≥0} (hs : 0 < s) {r : ℝ≥0} {β : Type*} [MeasurableSpace β]
    {f : Ω × HistorySpace 0 0 → β} (hf : Measurable f)
    (hrep : ∀ q : ℚ, (hq : lastO ℓ t < q) → ∃ fD : XD s q → β, Measurable fD ∧
      ∀ p (hp : p ∈ candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s)
        (hg : Aux50Hit.IsGoodPath (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ)
          (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ) (fun _ => ⊤) p.1),
        p ∈ candWinF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s q r →
        f p = fD (stopX (lt_of_le_of_lt (lastO_nonneg hv) hq) (candEgF_good x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s)
          hp hg)) :
    Measurable[candFiltF x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs r] f := by
  intro B hB
  refine measurableSet_candFiltF_of_stopD x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs (hf hB) fun q hq => ?_
  obtain ⟨fD, hfD, hrepf⟩ := hrep q hq
  obtain ⟨C, hC, hSC⟩ := exists_measurableSet_of_subtypeD (hfD hB)
  refine ⟨C, hC, fun p hp hg hw => ?_⟩
  rw [mem_preimage, hrepf p hp hg hw]
  exact hSC _

/-! ### The restarted processes are adapted -/

include hκ4 in
theorem adaptedBefore_s3W_candFiltF (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) (us : ℂ → ℝ) {ℓ : ℕ} {t : Fin ℓ → ℝ≥0}
    (hv : IsValid ℓ t) {s : ℝ≥0} (hs : 0 < s) :
    AdaptedBefore (candFiltF x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs)
      (s3ζ s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s) (lastO ℓ t : ℝ))
      (s3W s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s) (lastO ℓ t : ℝ)) := by
  intro r B hB
  have hW := adaptedBefore_candWF x₀ h44 hκ hκ4 hb h fl hG.1 ℓ t
  have hE : MeasurableSet (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s) := measurableSet_glueGood
  have hEg := candEgF_good x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s
  refine measurableSet_candFiltF_of_stopD x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs
    ((measurableSet_lt measurable_const (measurable_s3ζ hW hE hEg _)).inter (measurable_s3W hW hE hEg _ r hB))
    fun q hq => ?_
  obtain ⟨C, hC, hSC⟩ := exists_measurableSet_of_subtypeD
    ((measurable_s5W (s := s) (q := q) (lastO ℓ t) r) hB)
  refine ⟨C, hC, fun p hp hg hw => ?_⟩
  have hqpos : 0 < q := lt_of_le_of_lt (lastO_nonneg hv) hq
  obtain ⟨hal, -, hqP, hlt⟩ := hw
  have hz := (lt_s3ζ_and_lt_s5ζ hqpos hEg hp hg hq hal hqP hlt le_rfl).1
  have he := s3W_eq_s5W hqpos hEg hp hg hq hal hqP hlt le_rfl
  change _ ↔ (stopX hqpos hEg hp hg).1 ∈ C
  rw [← hSC (stopX hqpos hEg hp hg)]
  simp only [mem_ofPred_eq, mem_preimage]
  rw [he]
  exact ⟨fun h => h.2, fun h => ⟨hz, h⟩⟩

include hκ4 in
theorem adaptedBefore_s3VL_candFiltF (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) (us : ℂ → ℝ) {ℓ : ℕ} {t : Fin ℓ → ℝ≥0}
    (hv : IsValid ℓ t) {s : ℝ≥0} (hs : 0 < s) {nL : ℕ} (xL : Fin nL → ℝ) (i : Fin (ℓ + (nL + 1))) :
    AdaptedBefore (candFiltF x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs)
      (s3ζ s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s) (lastO ℓ t : ℝ))
      (s3VL xL (candTsF fl ℓ t) ℓ s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s)
        (lastO ℓ t : ℝ) i) := by
  intro r B hB
  have hW := adaptedBefore_candWF x₀ h44 hκ hκ4 hb h fl hG.1 ℓ t
  have hE : MeasurableSet (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s) := measurableSet_glueGood
  have hEg := candEgF_good x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s
  refine measurableSet_candFiltF_of_stopD x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs
    ((measurableSet_lt measurable_const (measurable_s3ζ hW hE hEg _)).inter
      (measurable_s3VL hW hE hEg xL (candTsF_bounds hv) (candTsF_eq_candTq hv) i r hB))
    fun q hq => ?_
  obtain ⟨C, hC, hSC⟩ := exists_measurableSet_of_subtypeD
    ((measurable_s5VL (s := s) (q := q) xL (candTsF_bounds hv) (candTsF_eq_candTq hv) i r) hB)
  refine ⟨C, hC, fun p hp hg hw => ?_⟩
  have hqpos : 0 < q := lt_of_le_of_lt (lastO_nonneg hv) hq
  obtain ⟨hal, -, hqP, hlt⟩ := hw
  have hz := (lt_s3ζ_and_lt_s5ζ hqpos hEg hp hg hq hal hqP hlt le_rfl).1
  have he := s3VL_eq_s5VL hqpos hEg hp hg hq hal hqP hlt xL (candTsF_bounds (fl := fl) hv) i le_rfl
  change _ ↔ (stopX hqpos hEg hp hg).1 ∈ C
  rw [← hSC (stopX hqpos hEg hp hg)]
  simp only [mem_ofPred_eq, mem_preimage]
  rw [he]
  exact ⟨fun h => h.2, fun h => ⟨hz, h⟩⟩

include hκ4 in
theorem adaptedBefore_s3VR_candFiltF (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) (us : ℂ → ℝ) {ℓ : ℕ} {t : Fin ℓ → ℝ≥0}
    (hv : IsValid ℓ t) {s : ℝ≥0} (hs : 0 < s) {nR : ℕ} (xR : Fin nR → ℝ) (i : Fin (ℓ + (nR + 1))) :
    AdaptedBefore (candFiltF x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs)
      (s3ζ s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s) (lastO ℓ t : ℝ))
      (s3VR xR (candTsF fl ℓ t) ℓ s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s)
        (lastO ℓ t : ℝ) i) := by
  intro r B hB
  have hW := adaptedBefore_candWF x₀ h44 hκ hκ4 hb h fl hG.1 ℓ t
  have hE : MeasurableSet (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s) := measurableSet_glueGood
  have hEg := candEgF_good x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s
  refine measurableSet_candFiltF_of_stopD x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs
    ((measurableSet_lt measurable_const (measurable_s3ζ hW hE hEg _)).inter
      (measurable_s3VR hW hE hEg xR (candTsF_bounds hv) (candTsF_eq_candTq hv) i r hB))
    fun q hq => ?_
  obtain ⟨C, hC, hSC⟩ := exists_measurableSet_of_subtypeD
    ((measurable_s5VR (s := s) (q := q) xR (candTsF_bounds hv) (candTsF_eq_candTq hv) i r) hB)
  refine ⟨C, hC, fun p hp hg hw => ?_⟩
  have hqpos : 0 < q := lt_of_le_of_lt (lastO_nonneg hv) hq
  obtain ⟨hal, -, hqP, hlt⟩ := hw
  have hz := (lt_s3ζ_and_lt_s5ζ hqpos hEg hp hg hq hal hqP hlt le_rfl).1
  have he := s3VR_eq_s5VR hqpos hEg hp hg hq hal hqP hlt xR (candTsF_bounds (fl := fl) hv) i le_rfl
  change _ ↔ (stopX hqpos hEg hp hg).1 ∈ C
  rw [← hSC (stopX hqpos hEg hp hg)]
  simp only [mem_ofPred_eq, mem_preimage]
  rw [he]
  exact ⟨fun h => h.2, fun h => ⟨hz, h⟩⟩

/-! ### The restarted chart and the chart clause -/

include hκ4 in
/-- **The restarted chart has `candFiltF 0`-measurable data.** -/
theorem isMeasChart_s3Chart_candFiltF (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) (us : ℂ → ℝ) {ℓ : ℕ} {t : Fin ℓ → ℝ≥0}
    (hv : IsValid ℓ t) {s : ℝ≥0} (hs : 0 < s) :
    IsMeasChart (candFiltF x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs 0)
      (s3Chart s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s)
        (lastO ℓ t : ℝ)) := by
  have hW := adaptedBefore_candWF x₀ h44 hκ hκ4 hb h fl hG.1 ℓ t
  have hE : MeasurableSet (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s) := measurableSet_glueGood
  have hEg := candEgF_good x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s
  have hamb := isMeasChart_s3Chart hW hE hEg (lastO ℓ t)
  have hrepC : ∀ q : ℚ, (hq : lastO ℓ t < q) → ∀ p (hp : p ∈ candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s)
      (hg : Aux50Hit.IsGoodPath (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ)
        (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ) (fun _ => ⊤) p.1),
      p ∈ candWinF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s q 0 →
      s3Chart s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s) (lastO ℓ t : ℝ) p =
        s5Chart s q (lastO ℓ t) (stopX (lt_of_le_of_lt (lastO_nonneg hv) hq) hEg hp hg) := by
    intro q hq p hp hg hw
    obtain ⟨hal, -, hqP, hlt⟩ := hw
    exact s3Chart_eq_s5Chart (lt_of_le_of_lt (lastO_nonneg hv) hq) hEg hp hg hq hal hqP hlt
  refine ⟨hamb.conf, hamb.lift, fun z ε => ?_, fun z => ?_, fun z => ?_⟩
  · refine measurableSet_candFiltF_of_stopD x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs (hamb.ball z ε) fun q hq => ?_
    obtain ⟨C, hC, hSC⟩ := exists_measurableSet_of_subtypeD ((isMeasChart_s5Chart (s := s) (q := q)
      (lastO ℓ t)).ball z ε)
    refine ⟨C, hC, fun p hp hg hw => ?_⟩
    change _ ↔ (stopX (lt_of_le_of_lt (lastO_nonneg hv) hq) hEg hp hg).1 ∈ C
    rw [← hSC, mem_ofPred_eq, mem_ofPred_eq, hrepC q hq p hp hg hw]
  · refine measurable_candFiltF_of_stopD x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs (hamb.fwd z) fun q hq => ?_
    refine ⟨_, (isMeasChart_s5Chart (s := s) (q := q) (lastO ℓ t)).fwd z, fun p hp hg hw => ?_⟩
    exact indicator_fwd_congr (hrepC q hq p hp hg hw) z
  · refine measurable_candFiltF_of_stopD x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs (hamb.lft z) fun q hq => ?_
    refine ⟨_, (isMeasChart_s5Chart (s := s) (q := q) (lastO ℓ t)).lft z, fun p hp hg hw => ?_⟩
    exact indicator_lift_congr (hrepC q hq p hp hg hw) z

include hκ4 in
/-- The alive event is an event of every `candFiltF r`. -/
theorem measurableSet_s3Alive_candFiltF (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) (us : ℂ → ℝ) {ℓ : ℕ} {t : Fin ℓ → ℝ≥0}
    (hv : IsValid ℓ t) {s : ℝ≥0} (hs : 0 < s) (r : ℝ≥0) :
    MeasurableSet[candFiltF x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs r]
      (s3Alive s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s)
        (lastO ℓ t : ℝ)) := by
  have hW := adaptedBefore_candWF x₀ h44 hκ hκ4 hb h fl hG.1 ℓ t
  have hE : MeasurableSet (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s) := measurableSet_glueGood
  have hEg := candEgF_good x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s
  exact measurableSet_candFiltF_of_stopD x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs
    (StagedS4.measurableSet_s3Alive hW hE hEg (lastO ℓ t)) fun q _ =>
      ⟨univ, MeasurableSet.univ, fun _ _ _ hw => ⟨fun _ => mem_univ _, fun _ => hw.1⟩⟩

include hκ4 in
/-- **`hEr` and `hFm`: the candidate's validity event at the restarted time `r` is a `candFiltF r`-event and its chart
formula is `candFiltF r`-strongly measurable on it.** -/
theorem candErF_candFF_candFiltF (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) (us : ℂ → ℝ) {ℓ : ℕ} {t : Fin ℓ → ℝ≥0}
    (hv : IsValid ℓ t) {s : ℝ≥0} (hs : 0 < s) (φ : TestOn upperHalfPlaneOpens) (r : ℝ≥0) :
    MeasurableSet[candFiltF x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs r]
        (candErF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s φ r) ∧
      StronglyMeasurable[candFiltF x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs r]
        ((candErF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s φ r).indicator
          (candFF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s φ r)) := by
  set c := sourceWord (x₀ := x₀) hκ hb with hc
  have hEg := candEgF_good x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s
  have hch := isMeasChart_s3Chart_candFiltF x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs
  obtain ⟨hAv, hM, hV⟩ := Sec7.Lemma71M.measurable_chartAvoid (𝓐 := candFiltF x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us
      hv hs)
    (𝓐₀ := candFiltF x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs 0) κ
    (imgStageRhoL κ (flagAngle (fl 0)) (flowLineRhoL κ c.fn c.jumps 0 (flagAngle (fl 0))) (fun j => candAngF fl ℓ t j
        - candAngF fl ℓ t 0) ℓ)
    (imgStageRhoR κ (flagAngle (fl 0)) (flowLineRhoR κ c.fn c.jumps 0 (flagAngle (fl 0))) (fun j => candAngF fl ℓ t j
        - candAngF fl ℓ t 0) ℓ)
    (2 * Real.pi * QuantumZipper.chiC κ + (candAngF fl ℓ t ℓ - candAngF fl ℓ t 0) * QuantumZipper.chiC κ)
    (QuantumZipper.chiC κ)
    (adaptedBefore_s3W_candFiltF x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs) (StagedS4.continuousOn_s3W hEg)
    (adaptedBefore_s3VL_candFiltF x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs (flowLineXL c.fn c.jumps 0))
    (adaptedBefore_s3VR_candFiltF x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs (flowLineXR c.fn c.jumps 0)) r
    ((candFiltF x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs).mono (by exact zero_le)) (fun p => (s3Chart s
      (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s) (lastO ℓ t : ℝ) p).dom.isOpen)
    hch.ball hch.conf (fun _ => rfl) hch.fwd hch.lft hch.lift φ
  have hAl := measurableSet_s3Alive_candFiltF x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs r
  have hEr : MeasurableSet[candFiltF x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs r]
      (candErF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s φ r) := hAl.inter hAv
  refine ⟨hEr, ?_⟩
  have e := indicator_cexp_eq (E := candErF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s φ r)
    (A := {p | Sec7.Lemma71D.IsChartAvoid
      (fun r' => s3W s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s)
        (lastO ℓ t : ℝ) r' p)
      (s3ζ s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s) (lastO ℓ t : ℝ) p)
      (s3Chart s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s) (lastO ℓ t : ℝ) p)
      φ r})
    (M := fun p => Sec7.Lemma71D.chartMean κ
        (imgStageRhoL κ (flagAngle (fl 0)) (flowLineRhoL κ c.fn c.jumps 0 (flagAngle (fl 0))) (fun j => candAngF fl ℓ
            t j - candAngF fl ℓ t 0) ℓ)
        (imgStageRhoR κ (flagAngle (fl 0)) (flowLineRhoR κ c.fn c.jumps 0 (flagAngle (fl 0))) (fun j => candAngF fl ℓ
            t j - candAngF fl ℓ t 0) ℓ)
        (fun r' => s3W s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s)
          (lastO ℓ t : ℝ) r' p)
        (fun i r' => s3VL (flowLineXL c.fn c.jumps 0) (candTsF fl ℓ t) ℓ s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t)
          (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s) (lastO ℓ t : ℝ) i r' p)
        (fun i r' => s3VR (flowLineXR c.fn c.jumps 0) (candTsF fl ℓ t) ℓ s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t)
          (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s) (lastO ℓ t : ℝ) i r' p)
        (s3Chart s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s) (lastO ℓ t :
            ℝ) p)
        (2 * Real.pi * QuantumZipper.chiC κ + (candAngF fl ℓ t ℓ - candAngF fl ℓ t 0) * QuantumZipper.chiC κ)
        (QuantumZipper.chiC κ) φ r)
    (V := fun p => Sec7.Lemma71D.chartVar
        (fun r' => s3W s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s)
          (lastO ℓ t : ℝ) r' p)
        (s3Chart s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s) (lastO ℓ t :
            ℝ) p)
        φ r)
    (F := candFF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s φ r) (fun p hp => hp.2) (fun p _ => rfl)
  rw [e]
  refine Measurable.stronglyMeasurable ?_
  refine Measurable.indicator ?_ hEr
  exact Complex.measurable_exp.comp ((measurable_const.mul (Complex.measurable_ofReal.comp hM)).sub
    (Complex.measurable_ofReal.comp (measurable_const.mul hV)))

include hκ4 in
/-- **The candidate's chart clause at a fixed restarted time `r` for its Galmarino filtration, with no remaining
hypothesis**: almost surely on the validity event `candErF r`, the conditional characteristic value of the root field
given `candFiltF r` is the chart formula of the restarted word at `r`. -/
theorem ae_condExp_candFiltF_full (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) {us : ℂ → ℝ}
    (hus : IsBoundedHarmonicExtension (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps us)
    {ℓ : ℕ} {t : Fin ℓ → ℝ≥0} (hv : IsValid ℓ t) {s : ℝ≥0} (hs : 0 < s) (φ : TestOn upperHalfPlaneOpens)
    (r : ℝ≥0) :
    ∀ᵐ p ∂(candMu x₀ (κ := κ) P h W ζ hG.1), p ∈ candErF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s φ r →
      (candMu x₀ (κ := κ) P h W ζ hG.1)[fun p' => Complex.exp (Complex.I *
          (rootFieldT κ x₀ (flagAngle (fl 0)) h p'.1 φ : ℂ)) | candFiltF x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs
              r] p =
        candFF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s φ r p :=
  ae_condExp_candFiltF x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf hus hv hs φ r
    (fun n k hq => exists_candSigmaF_ae_eq_candWinF_s4Av x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs φ r n k hq)
    (candErF_candFF_candFiltF x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs φ r).1
    (candErF_candFF_candFiltF x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs φ r).2

end Cand

end InteractingSLE.Sec5.CrossCond.StagedNComp
