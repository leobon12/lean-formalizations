/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.StagedS5Rep
import InteractingSLE.Spec.Sec5.StagedS5Av

/-!
# The candidate's restarted word is adapted to its Galmarino filtration (`hEr`, `hFm`)

Packet PROVE-STAGED-S5 ((M3) of `planning/handoffs/PROVE-STAGED-S3.md` §5.2 and the facts `hEr`, `hFm` of
`StagedS4.ae_condExp_candFilt`). An event (a function) is in the candidate's Galmarino filtration `candFilt r` as soon
as it is measurable and, on every window at a rational own time `q` after the last switch, it is read from Word49's
stopped data at `q` (`measurableSet_candFilt_of_stopD`, `measurable_candFilt_of_stopD`; the window itself is
`s5Win`, `mem_s5Win_iff`; the marks transfer is `exists_candSigma_ae_eq_stopD`). With the identities of `StagedS5Rep`:

* **`adaptedBefore_s3W_candFilt`**, **`adaptedBefore_s3VL_candFilt`**, **`adaptedBefore_s3VR_candFilt`**: the restarted
  driver and marks are adapted to `candFilt` before the restarted lifetime;
* **`isMeasChart_s3Chart_candFilt`**: the restarted chart has `candFilt 0`-measurable data;
* **`measurableSet_candEr_candFilt`** (`hEr`) and **`stronglyMeasurable_candF_candFilt`** (`hFm`), by
  `Sec7.Lemma71M.measurable_chartAvoid`;
* **`ae_condExp_candFilt_full`**: the candidate's chart clause at every fixed restarted time for `candFilt`, with no
  remaining measurability hypothesis (`hAv` is `StagedS5Av`).

R48: only `h44` (R74) is used.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal Real
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Sec5.CrossCond.StagedS5

open WangWu hiding ratPt exists_ratPt_dist_lt
open WangWu.ImgWord LawUnique GlueCond Cond44Ref Word49 StagedS3 StagedS4
open Restart Exist.StagedLaw Exist.Staged
open Sec7.AdmCode Prop513TreeExtract Prop513Schedule Prop513Target Prop59Pieces StagedRepLater
open Sec4 (IsStripGFF IsStripCounterflowDriver)
open Sec7.Lemma71C (capClock)
open WangWu.ChartConst (dyq dyqQ)
open StagedFinal (imgStageRhoL imgStageRhoR)

/-! ### The switch own times of a candidate -/

section Times

/-- The rational switch own times of a candidate (`candTq (j + 1) = oTime (t j)`). -/
def candTq (ℓ : ℕ) (t : Fin ℓ → ℝ≥0) : ℕ → ℚ := fun m => if hm : m - 1 < ℓ then oTime (t ⟨m - 1, hm⟩) else 0

variable {ℓ : ℕ} {t : Fin ℓ → ℝ≥0}

theorem candTs_succ (hv : IsValid ℓ t) (j : Fin ℓ) : candTs ℓ t (j + 1) = (oTime (t j) : ℝ) := by
  rw [candTs, candSched, startT_schedD_mkSched hv (lt_add_one _) j.2]

theorem candTs_bounds (hv : IsValid ℓ t) (j : Fin ℓ) :
    0 ≤ candTs ℓ t (j + 1) ∧ candTs ℓ t (j + 1) ≤ (lastO ℓ t : ℝ) := by
  rw [candTs_succ hv j]
  exact ⟨by exact_mod_cast (oTime_pos hv _).le, by exact_mod_cast oTime_le_lastO hv _⟩

theorem candTs_eq_candTq (hv : IsValid ℓ t) (j : Fin ℓ) : candTs ℓ t (j + 1) = (candTq ℓ t (j + 1) : ℝ) := by
  rw [candTs_succ hv j]
  have hj : (j : ℕ) + 1 - 1 < ℓ := by simp
  have e : candTq ℓ t (j + 1) = oTime (t ⟨(j : ℕ) + 1 - 1, hj⟩) := by simp only [candTq, hj, ↓reduceDIte]
  rw [e]
  congr 3

end Times


/-! ### Indicator identities -/

section Ind

theorem indicator_fwd_congr {X Y : Type*} {c : X → Chart} {d : Y → Chart} {x : X} {y : Y} (h : c x = d y)
    (z : ℂ) :
    ({x | z ∈ (c x).dom}.indicator fun x => (c x).1 z) x = ({y | z ∈ (d y).dom}.indicator fun y => (d y).1 z) y := by
  by_cases hz : z ∈ (d y).dom
  · rw [indicator_of_mem (show x ∈ {x | z ∈ (c x).dom} by rw [mem_ofPred_eq, h]; exact hz),
      indicator_of_mem (show y ∈ {y | z ∈ (d y).dom} from hz), h]
  · rw [indicator_of_notMem (show x ∉ {x | z ∈ (c x).dom} by rw [mem_ofPred_eq, h]; exact hz),
      indicator_of_notMem (show y ∉ {y | z ∈ (d y).dom} from hz)]

theorem indicator_lift_congr {X Y : Type*} {c : X → Chart} {d : Y → Chart} {x : X} {y : Y} (h : c x = d y)
    (z : ℂ) :
    ({x | z ∈ (c x).dom}.indicator fun x => (c x).2.2 z) x =
      ({y | z ∈ (d y).dom}.indicator fun y => (d y).2.2 z) y := by
  by_cases hz : z ∈ (d y).dom
  · rw [indicator_of_mem (show x ∈ {x | z ∈ (c x).dom} by rw [mem_ofPred_eq, h]; exact hz),
      indicator_of_mem (show y ∈ {y | z ∈ (d y).dom} from hz), h]
  · rw [indicator_of_notMem (show x ∉ {x | z ∈ (c x).dom} by rw [mem_ofPred_eq, h]; exact hz),
      indicator_of_notMem (show y ∉ {y | z ∈ (d y).dom} from hz)]

theorem indicator_cexp_eq {X : Type*} {E A : Set X} (hEA : E ⊆ A) {M V : X → ℝ} {F : X → ℂ}
    (hF : ∀ p ∈ E, F p = Complex.exp (Complex.I * ((M p : ℝ) : ℂ) - (((1 / 2 : ℝ) * V p : ℝ) : ℂ))) :
    E.indicator F = E.indicator fun p => Complex.exp (Complex.I * ((A.indicator M p : ℝ) : ℂ) -
      (((1 / 2 : ℝ) * A.indicator V p : ℝ) : ℂ)) := by
  refine indicator_congr fun p hp => ?_
  rw [indicator_of_mem (hEA hp), indicator_of_mem (hEA hp)]
  exact hF p hp

end Ind

/-! ### Events and functions of the Galmarino filtration from stopped data -/

section Cand

variable (x₀ : ℝ) (h44 : Theorem12ParamCond44Statement.{0}) {κ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  (hb : IsFig51Bounds κ a b a' b') {Ω : Type} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ)
  (ζ : Ω → ℝ≥0∞)

omit [StandardBorelSpace Ω] in
theorem candEg_good (hhm : Measurable h) (ℓ : ℕ) (t : Fin ℓ → ℝ≥0) (s : ℝ≥0) :
    ∀ p ∈ candEg x₀ h44 hκ hκ4 hb P h W ζ hhm ℓ t s, IsGood49 s (fun _ => ⊤) (candW x₀ h44 hκ hκ4 hb h ℓ t) p :=
  fun p hp => isGood49_of_mem_glueGood p hp

include hκ4 in
/-- **An event read from the stopped data on every window is an event of the Galmarino filtration.** -/
theorem measurableSet_candFilt_of_stopD (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) (us : ℂ → ℝ) {ℓ : ℕ} {t : Fin ℓ → ℝ≥0}
    (hv : IsValid ℓ t) {s : ℝ≥0} (hs : 0 < s) {r : ℝ≥0} {A : Set (Ω × HistorySpace 0 0)} (hA : MeasurableSet A)
    (hrep : ∀ q : ℚ, lastO ℓ t < q → ∃ C : Set (Y49 0 0), MeasurableSet C ∧
      ∀ p ∈ candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s,
        Aux50Hit.IsGoodPath (candW x₀ h44 hκ hκ4 hb h ℓ t) (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ)
          (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ) (fun _ => ⊤) p.1 →
        p ∈ candWin x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s q r →
        (p ∈ A ↔ stopD (candW x₀ h44 hκ hκ4 hb h ℓ t) (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ)
          (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ) (fun _ => ⊤) q s p ∈ C)) :
    MeasurableSet[candFilt x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs r] A := by
  rw [candFilt, measurableSet_galFilt_iff]
  refine ⟨hA, fun q => ?_⟩
  by_cases hq : lastO ℓ t < q
  · rw [candMarks_of_lt x₀ h44 hκ hκ4 hb h hq]
    have hEg := candEg_good x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s
    have hqpos : 0 < q := lt_of_le_of_lt (lastO_nonneg hv) hq
    have hτ0 : (0 : ℝ) ≤ (lastO ℓ t : ℝ) := by exact_mod_cast lastO_nonneg hv
    have hτq : ((lastO ℓ t : ℚ) : ℝ) ≤ q := by exact_mod_cast hq.le
    obtain ⟨C, hC, hAC⟩ := hrep q hq
    obtain ⟨CW, hCW, hWC⟩ := exists_measurableSet_of_subtypeD
      (measurableSet_s5Win (s := s) (q := q) (τ := lastO ℓ t) hτ0 hτq r)
    obtain ⟨B, hB, hBe⟩ := exists_candSigma_ae_eq_stopD x₀ h44 hκ hκ4 hb P h W ζ hG us hv hq s (hC.inter hCW)
    refine ⟨B, hB, hBe.trans ?_⟩
    filter_upwards [ae_good_cand x₀ h44 hκ hκ4 hb P h W ζ hG hcf ℓ t hv hs] with p hpg
    obtain ⟨hpE, hg, -⟩ := hpg
    have hwin : p ∈ candWin x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s q r ↔
        stopD (candW x₀ h44 hκ hκ4 hb h ℓ t) (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ)
          (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ) (fun _ => ⊤) q s p ∈ CW := by
      change _ ↔ (stopX hqpos hEg hpE hg).1 ∈ CW
      rw [← (hWC (stopX hqpos hEg hpE hg)), mem_s5Win_iff hqpos hEg hpE hg hq.le r]
      simp only [candWin, mem_ofPred_eq]
      exact ⟨fun h => ⟨h.1, h.2.2.1, h.2.2.2⟩, fun h => ⟨h.1, hq, h.2.1, h.2.2⟩⟩
    show (p ∈ stopD _ _ _ _ q s ⁻¹' (C ∩ CW)) = (p ∈ A ∩ _)
    rw [eq_iff_iff, mem_preimage, mem_inter_iff, mem_inter_iff]
    constructor
    · rintro ⟨h1, h2⟩
      have hw := hwin.2 h2
      exact ⟨(hAC p hpE hg hw).2 h1, hw⟩
    · rintro ⟨h1, h2⟩
      exact ⟨(hAC p hpE hg h2).1 h1, hwin.1 h2⟩
  · refine ⟨∅, @MeasurableSet.empty _ (candMarks x₀ h44 hκ hκ4 hb h us ℓ t s q), Eventually.of_forall fun p => ?_⟩
    show (p ∈ (∅ : Set (Ω × HistorySpace 0 0))) = (p ∈ A ∩ _)
    rw [eq_iff_iff]
    simp only [mem_empty_iff_false, false_iff, mem_inter_iff, candWin, mem_ofPred_eq, not_and]
    intro _ _ h
    exact absurd h hq

include hκ4 in
/-- **A function read from the stopped data on every window is measurable for the Galmarino filtration.** -/
theorem measurable_candFilt_of_stopD (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) (us : ℂ → ℝ) {ℓ : ℕ} {t : Fin ℓ → ℝ≥0}
    (hv : IsValid ℓ t) {s : ℝ≥0} (hs : 0 < s) {r : ℝ≥0} {β : Type*} [MeasurableSpace β]
    {f : Ω × HistorySpace 0 0 → β} (hf : Measurable f)
    (hrep : ∀ q : ℚ, (hq : lastO ℓ t < q) → ∃ fD : XD s q → β, Measurable fD ∧
      ∀ p (hp : p ∈ candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s)
        (hg : Aux50Hit.IsGoodPath (candW x₀ h44 hκ hκ4 hb h ℓ t) (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ)
          (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ) (fun _ => ⊤) p.1),
        p ∈ candWin x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s q r →
        f p = fD (stopX (lt_of_le_of_lt (lastO_nonneg hv) hq) (candEg_good x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s)
          hp hg)) :
    Measurable[candFilt x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs r] f := by
  intro B hB
  refine measurableSet_candFilt_of_stopD x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs (hf hB) fun q hq => ?_
  obtain ⟨fD, hfD, hrepf⟩ := hrep q hq
  obtain ⟨C, hC, hSC⟩ := exists_measurableSet_of_subtypeD (hfD hB)
  refine ⟨C, hC, fun p hp hg hw => ?_⟩
  rw [mem_preimage, hrepf p hp hg hw]
  exact hSC _

/-! ### The restarted processes are adapted -/

include hκ4 in
theorem adaptedBefore_s3W_candFilt (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) (us : ℂ → ℝ) {ℓ : ℕ} {t : Fin ℓ → ℝ≥0}
    (hv : IsValid ℓ t) {s : ℝ≥0} (hs : 0 < s) :
    AdaptedBefore (candFilt x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs)
      (s3ζ s (candW x₀ h44 hκ hκ4 hb h ℓ t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s) (lastO ℓ t : ℝ))
      (s3W s (candW x₀ h44 hκ hκ4 hb h ℓ t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s) (lastO ℓ t : ℝ)) := by
  intro r B hB
  have hW := adaptedBefore_candW x₀ h44 hκ hκ4 hb h hG.1 ℓ t
  have hE : MeasurableSet (candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s) := measurableSet_glueGood
  have hEg := candEg_good x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s
  refine measurableSet_candFilt_of_stopD x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs
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
theorem adaptedBefore_s3VL_candFilt (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) (us : ℂ → ℝ) {ℓ : ℕ} {t : Fin ℓ → ℝ≥0}
    (hv : IsValid ℓ t) {s : ℝ≥0} (hs : 0 < s) {nL : ℕ} (xL : Fin nL → ℝ) (i : Fin (ℓ + (nL + 1))) :
    AdaptedBefore (candFilt x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs)
      (s3ζ s (candW x₀ h44 hκ hκ4 hb h ℓ t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s) (lastO ℓ t : ℝ))
      (s3VL xL (candTs ℓ t) ℓ s (candW x₀ h44 hκ hκ4 hb h ℓ t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s)
        (lastO ℓ t : ℝ) i) := by
  intro r B hB
  have hW := adaptedBefore_candW x₀ h44 hκ hκ4 hb h hG.1 ℓ t
  have hE : MeasurableSet (candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s) := measurableSet_glueGood
  have hEg := candEg_good x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s
  refine measurableSet_candFilt_of_stopD x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs
    ((measurableSet_lt measurable_const (measurable_s3ζ hW hE hEg _)).inter
      (measurable_s3VL hW hE hEg xL (candTs_bounds hv) (candTs_eq_candTq hv) i r hB))
    fun q hq => ?_
  obtain ⟨C, hC, hSC⟩ := exists_measurableSet_of_subtypeD
    ((measurable_s5VL (s := s) (q := q) xL (candTs_bounds hv) (candTs_eq_candTq hv) i r) hB)
  refine ⟨C, hC, fun p hp hg hw => ?_⟩
  have hqpos : 0 < q := lt_of_le_of_lt (lastO_nonneg hv) hq
  obtain ⟨hal, -, hqP, hlt⟩ := hw
  have hz := (lt_s3ζ_and_lt_s5ζ hqpos hEg hp hg hq hal hqP hlt le_rfl).1
  have he := s3VL_eq_s5VL hqpos hEg hp hg hq hal hqP hlt xL (candTs_bounds hv) i le_rfl
  change _ ↔ (stopX hqpos hEg hp hg).1 ∈ C
  rw [← hSC (stopX hqpos hEg hp hg)]
  simp only [mem_ofPred_eq, mem_preimage]
  rw [he]
  exact ⟨fun h => h.2, fun h => ⟨hz, h⟩⟩

include hκ4 in
theorem adaptedBefore_s3VR_candFilt (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) (us : ℂ → ℝ) {ℓ : ℕ} {t : Fin ℓ → ℝ≥0}
    (hv : IsValid ℓ t) {s : ℝ≥0} (hs : 0 < s) {nR : ℕ} (xR : Fin nR → ℝ) (i : Fin (ℓ + (nR + 1))) :
    AdaptedBefore (candFilt x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs)
      (s3ζ s (candW x₀ h44 hκ hκ4 hb h ℓ t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s) (lastO ℓ t : ℝ))
      (s3VR xR (candTs ℓ t) ℓ s (candW x₀ h44 hκ hκ4 hb h ℓ t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s)
        (lastO ℓ t : ℝ) i) := by
  intro r B hB
  have hW := adaptedBefore_candW x₀ h44 hκ hκ4 hb h hG.1 ℓ t
  have hE : MeasurableSet (candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s) := measurableSet_glueGood
  have hEg := candEg_good x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s
  refine measurableSet_candFilt_of_stopD x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs
    ((measurableSet_lt measurable_const (measurable_s3ζ hW hE hEg _)).inter
      (measurable_s3VR hW hE hEg xR (candTs_bounds hv) (candTs_eq_candTq hv) i r hB))
    fun q hq => ?_
  obtain ⟨C, hC, hSC⟩ := exists_measurableSet_of_subtypeD
    ((measurable_s5VR (s := s) (q := q) xR (candTs_bounds hv) (candTs_eq_candTq hv) i r) hB)
  refine ⟨C, hC, fun p hp hg hw => ?_⟩
  have hqpos : 0 < q := lt_of_le_of_lt (lastO_nonneg hv) hq
  obtain ⟨hal, -, hqP, hlt⟩ := hw
  have hz := (lt_s3ζ_and_lt_s5ζ hqpos hEg hp hg hq hal hqP hlt le_rfl).1
  have he := s3VR_eq_s5VR hqpos hEg hp hg hq hal hqP hlt xR (candTs_bounds hv) i le_rfl
  change _ ↔ (stopX hqpos hEg hp hg).1 ∈ C
  rw [← hSC (stopX hqpos hEg hp hg)]
  simp only [mem_ofPred_eq, mem_preimage]
  rw [he]
  exact ⟨fun h => h.2, fun h => ⟨hz, h⟩⟩

/-! ### The restarted chart and the chart clause -/

include hκ4 in
/-- **The restarted chart has `candFilt 0`-measurable data.** -/
theorem isMeasChart_s3Chart_candFilt (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) (us : ℂ → ℝ) {ℓ : ℕ} {t : Fin ℓ → ℝ≥0}
    (hv : IsValid ℓ t) {s : ℝ≥0} (hs : 0 < s) :
    IsMeasChart (candFilt x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs 0)
      (s3Chart s (candW x₀ h44 hκ hκ4 hb h ℓ t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s) (lastO ℓ t : ℝ)) := by
  have hW := adaptedBefore_candW x₀ h44 hκ hκ4 hb h hG.1 ℓ t
  have hE : MeasurableSet (candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s) := measurableSet_glueGood
  have hEg := candEg_good x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s
  have hamb := isMeasChart_s3Chart hW hE hEg (lastO ℓ t)
  have hrepC : ∀ q : ℚ, (hq : lastO ℓ t < q) → ∀ p (hp : p ∈ candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s)
      (hg : Aux50Hit.IsGoodPath (candW x₀ h44 hκ hκ4 hb h ℓ t) (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ)
        (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ) (fun _ => ⊤) p.1),
      p ∈ candWin x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s q 0 →
      s3Chart s (candW x₀ h44 hκ hκ4 hb h ℓ t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s) (lastO ℓ t : ℝ) p =
        s5Chart s q (lastO ℓ t) (stopX (lt_of_le_of_lt (lastO_nonneg hv) hq) hEg hp hg) := by
    intro q hq p hp hg hw
    obtain ⟨hal, -, hqP, hlt⟩ := hw
    exact s3Chart_eq_s5Chart (lt_of_le_of_lt (lastO_nonneg hv) hq) hEg hp hg hq hal hqP hlt
  refine ⟨hamb.conf, hamb.lift, fun z ε => ?_, fun z => ?_, fun z => ?_⟩
  · refine measurableSet_candFilt_of_stopD x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs (hamb.ball z ε) fun q hq => ?_
    obtain ⟨C, hC, hSC⟩ := exists_measurableSet_of_subtypeD ((isMeasChart_s5Chart (s := s) (q := q)
      (lastO ℓ t)).ball z ε)
    refine ⟨C, hC, fun p hp hg hw => ?_⟩
    change _ ↔ (stopX (lt_of_le_of_lt (lastO_nonneg hv) hq) hEg hp hg).1 ∈ C
    rw [← hSC, mem_ofPred_eq, mem_ofPred_eq, hrepC q hq p hp hg hw]
  · refine measurable_candFilt_of_stopD x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs (hamb.fwd z) fun q hq => ?_
    refine ⟨_, (isMeasChart_s5Chart (s := s) (q := q) (lastO ℓ t)).fwd z, fun p hp hg hw => ?_⟩
    exact indicator_fwd_congr (hrepC q hq p hp hg hw) z
  · refine measurable_candFilt_of_stopD x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs (hamb.lft z) fun q hq => ?_
    refine ⟨_, (isMeasChart_s5Chart (s := s) (q := q) (lastO ℓ t)).lft z, fun p hp hg hw => ?_⟩
    exact indicator_lift_congr (hrepC q hq p hp hg hw) z

include hκ4 in
/-- The alive event is an event of every `candFilt r`. -/
theorem measurableSet_s3Alive_candFilt (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) (us : ℂ → ℝ) {ℓ : ℕ} {t : Fin ℓ → ℝ≥0}
    (hv : IsValid ℓ t) {s : ℝ≥0} (hs : 0 < s) (r : ℝ≥0) :
    MeasurableSet[candFilt x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs r]
      (s3Alive s (candW x₀ h44 hκ hκ4 hb h ℓ t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s) (lastO ℓ t : ℝ)) := by
  have hW := adaptedBefore_candW x₀ h44 hκ hκ4 hb h hG.1 ℓ t
  have hE : MeasurableSet (candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s) := measurableSet_glueGood
  have hEg := candEg_good x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s
  exact measurableSet_candFilt_of_stopD x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs
    (StagedS4.measurableSet_s3Alive hW hE hEg (lastO ℓ t)) fun q _ =>
      ⟨univ, MeasurableSet.univ, fun _ _ _ hw => ⟨fun _ => mem_univ _, fun _ => hw.1⟩⟩

include hκ4 in
/-- **`hEr` and `hFm`: the candidate's validity event at the restarted time `r` is a `candFilt r`-event and its chart
formula is `candFilt r`-strongly measurable on it.** -/
theorem candEr_candF_candFilt (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) (us : ℂ → ℝ) {ℓ : ℕ} {t : Fin ℓ → ℝ≥0}
    (hv : IsValid ℓ t) {s : ℝ≥0} (hs : 0 < s) (φ : TestOn upperHalfPlaneOpens) (r : ℝ≥0) :
    MeasurableSet[candFilt x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs r]
        (candEr x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s φ r) ∧
      StronglyMeasurable[candFilt x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs r]
        ((candEr x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s φ r).indicator
          (candF x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s φ r)) := by
  set c := sourceWord (x₀ := x₀) hκ hb with hc
  have hEg := candEg_good x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s
  have hch := isMeasChart_s3Chart_candFilt x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs
  obtain ⟨hAv, hM, hV⟩ := Sec7.Lemma71M.measurable_chartAvoid (𝓐 := candFilt x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs)
    (𝓐₀ := candFilt x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs 0) κ
    (imgStageRhoL κ (π / 2) (flowLineRhoL κ c.fn c.jumps 0 (π / 2)) (fun j => candAng ℓ t j - candAng ℓ t 0) ℓ)
    (imgStageRhoR κ (π / 2) (flowLineRhoR κ c.fn c.jumps 0 (π / 2)) (fun j => candAng ℓ t j - candAng ℓ t 0) ℓ)
    (2 * Real.pi * QuantumZipper.chiC κ + (candAng ℓ t ℓ - candAng ℓ t 0) * QuantumZipper.chiC κ)
    (QuantumZipper.chiC κ)
    (adaptedBefore_s3W_candFilt x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs) (StagedS4.continuousOn_s3W hEg)
    (adaptedBefore_s3VL_candFilt x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs (flowLineXL c.fn c.jumps 0))
    (adaptedBefore_s3VR_candFilt x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs (flowLineXR c.fn c.jumps 0)) r
    ((candFilt x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs).mono (by exact zero_le)) (fun p => (s3Chart s
      (candW x₀ h44 hκ hκ4 hb h ℓ t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s) (lastO ℓ t : ℝ) p).dom.isOpen)
    hch.ball hch.conf (fun _ => rfl) hch.fwd hch.lft hch.lift φ
  have hAl := measurableSet_s3Alive_candFilt x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs r
  have hEr : MeasurableSet[candFilt x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs r]
      (candEr x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s φ r) := hAl.inter hAv
  refine ⟨hEr, ?_⟩
  have e := indicator_cexp_eq (E := candEr x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s φ r)
    (A := {p | Sec7.Lemma71D.IsChartAvoid
      (fun r' => s3W s (candW x₀ h44 hκ hκ4 hb h ℓ t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s)
        (lastO ℓ t : ℝ) r' p)
      (s3ζ s (candW x₀ h44 hκ hκ4 hb h ℓ t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s) (lastO ℓ t : ℝ) p)
      (s3Chart s (candW x₀ h44 hκ hκ4 hb h ℓ t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s) (lastO ℓ t : ℝ) p)
      φ r})
    (M := fun p => Sec7.Lemma71D.chartMean κ
        (imgStageRhoL κ (π / 2) (flowLineRhoL κ c.fn c.jumps 0 (π / 2)) (fun j => candAng ℓ t j - candAng ℓ t 0) ℓ)
        (imgStageRhoR κ (π / 2) (flowLineRhoR κ c.fn c.jumps 0 (π / 2)) (fun j => candAng ℓ t j - candAng ℓ t 0) ℓ)
        (fun r' => s3W s (candW x₀ h44 hκ hκ4 hb h ℓ t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s)
          (lastO ℓ t : ℝ) r' p)
        (fun i r' => s3VL (flowLineXL c.fn c.jumps 0) (candTs ℓ t) ℓ s (candW x₀ h44 hκ hκ4 hb h ℓ t)
          (candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s) (lastO ℓ t : ℝ) i r' p)
        (fun i r' => s3VR (flowLineXR c.fn c.jumps 0) (candTs ℓ t) ℓ s (candW x₀ h44 hκ hκ4 hb h ℓ t)
          (candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s) (lastO ℓ t : ℝ) i r' p)
        (s3Chart s (candW x₀ h44 hκ hκ4 hb h ℓ t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s) (lastO ℓ t : ℝ) p)
        (2 * Real.pi * QuantumZipper.chiC κ + (candAng ℓ t ℓ - candAng ℓ t 0) * QuantumZipper.chiC κ)
        (QuantumZipper.chiC κ) φ r)
    (V := fun p => Sec7.Lemma71D.chartVar
        (fun r' => s3W s (candW x₀ h44 hκ hκ4 hb h ℓ t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s)
          (lastO ℓ t : ℝ) r' p)
        (s3Chart s (candW x₀ h44 hκ hκ4 hb h ℓ t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s) (lastO ℓ t : ℝ) p)
        φ r)
    (F := candF x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s φ r) (fun p hp => hp.2) (fun p _ => rfl)
  rw [e]
  refine Measurable.stronglyMeasurable ?_
  refine Measurable.indicator ?_ hEr
  exact Complex.measurable_exp.comp ((measurable_const.mul (Complex.measurable_ofReal.comp hM)).sub
    (Complex.measurable_ofReal.comp (measurable_const.mul hV)))

include hκ4 in
/-- **The candidate's chart clause at a fixed restarted time `r` for its Galmarino filtration, with no remaining
hypothesis**: almost surely on the validity event `candEr r`, the conditional characteristic value of the root field
given `candFilt r` is the chart formula of the restarted word at `r`. -/
theorem ae_condExp_candFilt_full (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) {us : ℂ → ℝ}
    (hus : IsBoundedHarmonicExtension (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps us)
    {ℓ : ℕ} {t : Fin ℓ → ℝ≥0} (hv : IsValid ℓ t) {s : ℝ≥0} (hs : 0 < s) (φ : TestOn upperHalfPlaneOpens)
    (r : ℝ≥0) :
    ∀ᵐ p ∂(candMu x₀ (κ := κ) P h W ζ hG.1), p ∈ candEr x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s φ r →
      (candMu x₀ (κ := κ) P h W ζ hG.1)[fun p' => Complex.exp (Complex.I *
          (rootField (κ := κ) (x₀ := x₀) h p'.1 φ : ℂ)) | candFilt x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs r] p =
        candF x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s φ r p :=
  ae_condExp_candFilt x₀ h44 hκ hκ4 hb P h W ζ hG hcf hus hv hs φ r
    (fun n k hq => exists_candSigma_ae_eq_candWin_s4Av x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs φ r n k hq)
    (candEr_candF_candFilt x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs φ r).1
    (candEr_candF_candFilt x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs φ r).2

end Cand

end InteractingSLE.Sec5.CrossCond.StagedS5
