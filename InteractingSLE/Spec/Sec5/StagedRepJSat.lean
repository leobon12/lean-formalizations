/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.StagedRepJMarks

/-!
# Prop 5.9's later root stages: the glued past from the saturation of the stopped data

Packet PROVE-STAGED-REPJ. `GluePast` asks that every event of `Gam`'s canonical past of the candidate `(j+1, t)` inside
its reached event be, after `gZ`, almost surely an event of the Galmarino filtration `candFilt` at the restart time
`0` inside the alive event. Here it is reduced to a **saturation** statement (`GlueSat`): good window samples (good for
the staged driver, good for `Gam`, in the window `candWin q 0` of a rational time `q` after the last switch) with the
same stopped data `stopD q`, the first with a reached image (`gamR`), have `gamQ`-indistinguishable images under `gZ`.

* `stopRes`, `stopRes_stopD`: the stopped data at `q ≤ q₀` are a Borel function of those at `q₀`;
* `measurable_stopD_cand`, `measurableSet_candWin`, `mem_candWin_of_le`, `exists_mem_candWin`: the windows are Borel,
  decrease in `q`, and every alive good sample is in the windows of all rational times close after the last switch;
* **`gluePast_of_sat`**: per window, Lusin separation (`exists_measurableSet_inter_eq`) on the good samples gives a
  Borel `C_q` with `gZ⁻¹ M = stopD_q⁻¹ C_q` there; the right limit
  `A = ⋂ₙ ⋃_{lastO < q < lastO + 1/(n+1)} (candWin q 0 ∩ stopD_q⁻¹ C_q)` is a `candFilt 0`-event (on the window of
  `q₀` only the `q < q₀` matter, read through `stopRes`), lies in the alive event, and equals `gZ⁻¹ M` on the good
  samples (`gamGood` a.s. by the clearance form of Part A, the driver a.s. good);
* `GlueSatStatement`, **`gluePastStatement_of_sat`**, **`rootLaterOn_s4Objects_of_sat`**.

The good set `gamGood` is not causal (it quantifies over all lists and whole paths), which is why the event `A` is
built from the windows only and identified with `gZ⁻¹ M` almost surely.

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal Real
open LQGMetric (DistOn)

namespace InteractingSLE.Sec5.CrossCond.StagedRepJ

open WangWu hiding ratPt exists_ratPt_dist_lt
open WangWu.ImgWord LawUnique GlueCond Cond44Ref Word49 StagedS3 StagedS4 StagedS5 StagedS6
open Restart Exist.StagedLaw Exist.Staged Wire.Night
open Sec7.AdmCode Prop513TreeExtract Prop513Schedule Prop513Target Prop59Pieces Prop59Stage Prop59System
open StagedRepLater StagedKCand StagedKill StagedRep StagedCand
open Sec4 (IsStripGFF IsStripCounterflowDriver)
open Sec7.Lemma71C (capClock)

/-! ### Restricting stopped data -/

section Stop

theorem stopHistory_const_stopHistory_const {nL nR : ℕ} {a b : ℝ≥0} (hab : a ≤ b) (γ : HistorySpace nL nR) :
    Sec4.stopHistory (fun _ => a) (Sec4.stopHistory (fun _ => b) γ) = Sec4.stopHistory (fun _ => a) γ := by
  refine Prod.ext rfl (funext fun p => ?_)
  simp only [Sec4.stopHistory]
  split_ifs with h1 h2
  · rfl
  · exact absurd (h1.trans hab) h2
  · rfl

/-- The stopped data restricted to an earlier rational time. -/
def stopRes (q : ℚ) (y : Y49 0 0) : Y49 0 0 := (Sec4.stopHistory (fun _ => (q : ℝ).toNNReal) y.1, y.2)

theorem measurable_stopRes (q : ℚ) : Measurable (stopRes q) :=
  ((Sec4.measurable_stopHistory measurable_const).comp measurable_fst).prodMk measurable_snd

theorem stopRes_stopD {Ω : Type*} {W : ℝ≥0 → Ω → ℝ} {VL : Fin 0 → ℝ≥0 → Ω → ℝ} {VR : Fin 0 → ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} {q q₀ : ℚ} (hq : q ≤ q₀) (s : ℝ≥0) (p : Ω × HistorySpace 0 0) :
    stopRes q (stopD W VL VR ζ q₀ s p) = stopD W VL VR ζ q s p := by
  simp only [stopRes, stopD]
  rw [stopHistory_const_stopHistory_const (Real.toNNReal_le_toNNReal (by exact_mod_cast hq))]

end Stop

/-! ### The windows of the candidate -/

section Win

variable (x₀ : ℝ) (h44 : Theorem12ParamCond44Statement.{0}) {κ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  (hb : IsFig51Bounds κ a b a' b') {Ω : Type} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ)
  (ζ : Ω → ℝ≥0∞)

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
/-- The stopped data of the candidate's driver are Borel. -/
theorem measurable_stopD_cand (hhm : Measurable h) (ℓ : ℕ) (t : Fin ℓ → ℝ≥0) (q : ℚ) (s : ℝ≥0) :
    Measurable (stopD (candW x₀ h44 hκ hκ4 hb h ℓ t) (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ) (Fin.elim0 : Fin 0 → ℝ≥0 → Ω →
        ℝ) (fun _ => ⊤) q s) := by
  have hqm : Measurable (qField x₀ κ h) :=
    (measurable_targetField κ (Real.exp (π * x₀)) (Real.exp_pos _)).comp hhm
  have hX : IsMeasurableKilledDriving (candW x₀ h44 hκ hκ4 hb h ℓ t) (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ) (Fin.elim0 :
      Fin 0 → ℝ≥0 → Ω → ℝ) (fun _ => ⊤) := by
    intro r A hA
    have hm : Measurable fun ω => (candW x₀ h44 hκ hκ4 hb h ℓ t) r ω :=
      (measurable_pi_apply r).comp (measurable_continuedDriver
        (fun k => (measurable_codeDriver h44 hκ hκ4 _ _ k).comp hqm) _ _ _)
    have e : {ω | (r : ℝ≥0∞) < (fun _ : Ω => (⊤ : ℝ≥0∞)) ω ∧ ((candW x₀ h44 hκ hκ4 hb h ℓ t) r ω, fun i =>
        (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ) i r ω,
        fun i => (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ) i r ω) ∈ A} = (fun ω => ((candW x₀ h44 hκ hκ4 hb h ℓ t) r ω, (fun
            i => (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ) i r ω : Fin 0 → ℝ),
        (fun i => (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ) i r ω : Fin 0 → ℝ))) ⁻¹' A := by
      ext ω
      simp only [mem_ofPred_eq, mem_preimage, ENNReal.coe_lt_top, true_and]
    rw [e]
    exact (hm.prodMk ((measurable_of_subsingleton_codomain _).prodMk (measurable_of_subsingleton_codomain _))) hA
  exact (measurable_stopD q s).mono (CrossCond.cfGlueMarks_le _ _ hX) le_rfl

omit [StandardBorelSpace Ω] in
/-- The windows are Borel. -/
theorem measurableSet_candWin (hhm : Measurable h) (ℓ : ℕ) (t : Fin ℓ → ℝ≥0) (s : ℝ≥0) (q : ℚ) (r : ℝ≥0) :
    MeasurableSet (candWin x₀ h44 hκ hκ4 hb P h W ζ hhm ℓ t s q r) := by
  classical
  have hW := adaptedBefore_candW x₀ h44 hκ hκ4 hb h hhm ℓ t
  have hE : MeasurableSet (candEg x₀ h44 hκ hκ4 hb P h W ζ hhm ℓ t s) := measurableSet_glueGood
  have hEg := candEg_good x₀ h44 hκ hκ4 hb P h W ζ hhm ℓ t s
  have hpre := measurableSet_mem_gPre hW hE hEg q
  have hlt : MeasurableSet {p | (((s3Start s (candW x₀ h44 hκ hκ4 hb h ℓ t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hhm ℓ t
      s) (lastO ℓ t : ℝ)) p + r : ℝ≥0) : ℝ) <
      ({p | (q : ℝ) ∈ (gPre s (fun _ => ⊤) (candW x₀ h44 hκ hκ4 hb h ℓ t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hhm ℓ t
          s)) p}.indicator fun p => capClock ((gCurve s (fun _ => ⊤) (candW x₀ h44 hκ hκ4 hb h ℓ t) (candEg x₀ h44 hκ
          hκ4 hb P h W ζ hhm ℓ t s)) p) q) p} :=
    measurableSet_lt (measurable_coe_nnreal_real.comp ((measurable_s3Start hW hE hEg _).add_const r))
      (measurable_indicator_capClock_gCurve hW hE hEg q)
  have e : candWin x₀ h44 hκ hκ4 hb P h W ζ hhm ℓ t s q r = (s3Alive s (candW x₀ h44 hκ hκ4 hb h ℓ t) (candEg x₀ h44
      hκ hκ4 hb P h W ζ hhm ℓ t s) (lastO ℓ t : ℝ)) ∩ {_p | lastO ℓ t < q} ∩
      {p | (q : ℝ) ∈ (gPre s (fun _ => ⊤) (candW x₀ h44 hκ hκ4 hb h ℓ t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hhm ℓ t s))
          p} ∩ {p | (((s3Start s (candW x₀ h44 hκ hκ4 hb h ℓ t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hhm ℓ t s) (lastO ℓ
          t : ℝ)) p + r : ℝ≥0) : ℝ) <
        ({p | (q : ℝ) ∈ (gPre s (fun _ => ⊤) (candW x₀ h44 hκ hκ4 hb h ℓ t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hhm ℓ t
            s)) p}.indicator fun p => capClock ((gCurve s (fun _ => ⊤) (candW x₀ h44 hκ hκ4 hb h ℓ t) (candEg x₀ h44
            hκ hκ4 hb P h W ζ hhm ℓ t s)) p) q) p} := by
    ext p
    simp only [candWin, mem_ofPred_eq, mem_inter_iff]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨⟨⟨h1, h2⟩, h3⟩, by rwa [indicator_of_mem (show p ∈ {p | (q : ℝ) ∈ (gPre s (fun _ => ⊤) (candW x₀ h44 hκ
          hκ4 hb h ℓ t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hhm ℓ t s)) p} from h3)]⟩
    · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
      exact ⟨h1, h2, h3, by rwa [indicator_of_mem (show p ∈ {p | (q : ℝ) ∈ (gPre s (fun _ => ⊤) (candW x₀ h44 hκ hκ4
          hb h ℓ t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hhm ℓ t s)) p} from h3)] at h4⟩
  rw [e]
  exact (((measurableSet_s3Alive hW hE hEg _).inter (MeasurableSet.const _)).inter hpre).inter hlt

omit [StandardBorelSpace Ω] in
/-- The windows at `0` decrease in the rational time after the last switch. -/
theorem mem_candWin_of_le (hhm : Measurable h) {ℓ : ℕ} {t : Fin ℓ → ℝ≥0} {s : ℝ≥0} {q q₀ : ℚ}
    {p : Ω × HistorySpace 0 0} (hp : p ∈ (candWin x₀ h44 hκ hκ4 hb P h W ζ hhm ℓ t s q₀ 0)) (hq : lastO ℓ t < q)
        (hqq : q ≤ q₀) :
    p ∈ (candWin x₀ h44 hκ hκ4 hb P h W ζ hhm ℓ t s q 0) := by
  have hEg := candEg_good x₀ h44 hκ hκ4 hb P h W ζ hhm ℓ t s
  have hγ := isKilledArc_gCurve hEg p
  obtain ⟨hal, -, hq₀, -⟩ := hp
  have hqP : (q : ℝ) ∈ (gPre s (fun _ => ⊤) (candW x₀ h44 hκ hκ4 hb h ℓ t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hhm ℓ t
      s)) p :=
    hγ.icc _ hq₀ ⟨(hγ.nonneg _ hal.2).trans (by exact_mod_cast hq.le), by exact_mod_cast hqq⟩
  refine ⟨hal, hq, hqP, ?_⟩
  rw [add_zero, coe_s3Start_of_alive hEg hal]
  exact hγ.strictMonoOn_capClock hal.2 hqP (by exact_mod_cast hq)

omit [StandardBorelSpace Ω] in
/-- An alive good sample is in the windows at `0` of rational times arbitrarily close after the last switch. -/
theorem exists_mem_candWin (hhm : Measurable h) {ℓ : ℕ} {t : Fin ℓ → ℝ≥0} {s : ℝ≥0}
    {p : Ω × HistorySpace 0 0} (hal : p ∈ (s3Alive s (candW x₀ h44 hκ hκ4 hb h ℓ t) (candEg x₀ h44 hκ hκ4 hb P h W ζ
        hhm ℓ t s) (lastO ℓ t : ℝ))) {ε : ℚ} (hε : 0 < ε) :
    ∃ q : ℚ, lastO ℓ t < q ∧ q < lastO ℓ t + ε ∧ p ∈ (candWin x₀ h44 hκ hκ4 hb P h W ζ hhm ℓ t s q 0) := by
  have hEg := candEg_good x₀ h44 hκ hκ4 hb P h W ζ hhm ℓ t s
  have hγ := isKilledArc_gCurve hEg p
  obtain ⟨S', hS', hlt⟩ := hγ.exists_gt _ hal.2
  have hε' : ((lastO ℓ t : ℚ) : ℝ) < ((lastO ℓ t + ε : ℚ) : ℝ) := by exact_mod_cast lt_add_of_pos_right _ hε
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (lt_min hlt hε')
  have hq1' : lastO ℓ t < q := by exact_mod_cast hq1
  refine ⟨q, hq1', by exact_mod_cast (lt_min_iff.1 hq2).2, ?_⟩
  have hqP : (q : ℝ) ∈ (gPre s (fun _ => ⊤) (candW x₀ h44 hκ hκ4 hb h ℓ t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hhm ℓ t
      s)) p := hγ.icc _ hS' ⟨(hγ.nonneg _ hal.2).trans hq1.le, (lt_min_iff.1 hq2).1.le⟩
  refine ⟨hal, hq1', hqP, ?_⟩
  rw [add_zero, coe_s3Start_of_alive hEg hal]
  exact hγ.strictMonoOn_capClock hal.2 hqP hq1

/-- **The good window samples** at the rational time `q`: good for the glued word and for the staged driver, in the
window `candWin q 0`, and good for `Gam`. -/
def goodWin (hhm : Measurable h) (ℓ : ℕ) (t : Fin ℓ → ℝ≥0) (s : ℝ≥0) (q : ℚ) : Set (Ω × HistorySpace 0 0) :=
  {p | p ∈ (candEg x₀ h44 hκ hκ4 hb P h W ζ hhm ℓ t s) ∧ Aux50Hit.IsGoodPath (candW x₀ h44 hκ hκ4 hb h ℓ t)
      (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ) (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ) (fun _ => ⊤) p.1 ∧ p ∈ (candWin x₀ h44 hκ
      hκ4 hb P h W ζ hhm ℓ t s q 0) ∧ gZ x₀ (κ := κ) h p ∈ gamGood h44 hκ hκ4 (x₀ := x₀) hb}

/-- **The saturation of the glued past** (named statement): good window samples with the same stopped data, the
first with a reached image, have `gamQ`-indistinguishable images under `gZ`. -/
def GlueSat (hhm : Measurable h) (ℓ : ℕ) (t : Fin ℓ → ℝ≥0) (s : ℝ≥0) : Prop :=
  ∀ q : ℚ, lastO ℓ t < q → ∀ p ∈ goodWin x₀ h44 hκ hκ4 hb P h W ζ hhm ℓ t s q,
    ∀ p' ∈ goodWin x₀ h44 hκ hκ4 hb P h W ζ hhm ℓ t s q, (stopD (candW x₀ h44 hκ hκ4 hb h ℓ t) (Fin.elim0 : Fin 0 →
        ℝ≥0 → Ω → ℝ) (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ) (fun _ => ⊤) q s) p = (stopD (candW x₀ h44 hκ hκ4 hb h ℓ t)
        (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ) (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ) (fun _ => ⊤) q s) p' →
      gZ x₀ (κ := κ) h p ∈ gamR h44 hκ hκ4 (x₀ := x₀) hb s ℓ t →
      ∀ M, MeasurableSet[gamQ h44 hκ hκ4 (x₀ := x₀) hb s ℓ t] M → (gZ x₀ (κ := κ) h p ∈ M ↔ gZ x₀ (κ := κ) h p' ∈ M)

include hκ4 in
/-- **`GluePast` from the saturation of the stopped data** (and the clearance form of Part A). -/
theorem gluePast_of_sat (hA : PartAInputsSixteenDivOfClearance)
    (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) (us : ℂ → ℝ) {j : ℕ}
    {t : Fin (j + 1) → ℝ≥0} (hv : IsValid (j + 1) t) {s : ℝ≥0} (hs : 0 < s)
    (hsat : GlueSat x₀ h44 hκ hκ4 hb P h W ζ hG.1 (j + 1) t s) :
    GluePast x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs := by
  classical
  intro M hM hMR
  have hEm : MeasurableSet (candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 (j + 1) t s) := measurableSet_glueGood
  have hZm := measurable_gZ x₀ (κ := κ) h hG.1
  have hBm : MeasurableSet (gZ x₀ (κ := κ) h ⁻¹' M) := hZm (gamQ_le h44 hκ hκ4 hb s (j + 1) t M hM)
  have hgood := ae_good_cand x₀ h44 hκ hκ4 hb P h W ζ hG hcf (j + 1) t hv hs
  -- a measurable null set outside which the staged driver is a good path
  obtain ⟨N, hNsub, hNm, hN0⟩ : ∃ N : Set (Ω × HistorySpace 0 0), {p | ¬ Aux50Hit.IsGoodPath (candW x₀ h44 hκ hκ4 hb
      h (j + 1) t) (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ) (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ) (fun _ => ⊤) p.1} ⊆ N ∧
      MeasurableSet N ∧ gMu x₀ (κ := κ) P h W ζ hG.1 N = 0 := by
    refine ⟨toMeasurable (gMu x₀ (κ := κ) P h W ζ hG.1) {p | ¬ Aux50Hit.IsGoodPath (candW x₀ h44 hκ hκ4 hb h (j + 1)
        t) (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ) (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ) (fun _ => ⊤) p.1}, subset_toMeasurable
        _ _,
      measurableSet_toMeasurable _ _, ?_⟩
    rw [measure_toMeasurable]
    exact ae_iff.1 (hgood.mono fun p hp => hp.2.1)
  have hG0m : MeasurableSet ((candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 (j + 1) t s) ∩ gZ x₀ (κ := κ) h ⁻¹' gamGood h44 hκ
      hκ4 (x₀ := x₀) hb ∩ Nᶜ) :=
    (hEm.inter (hZm (measurableSet_gamGood h44 hκ hκ4 hb))).inter hNm.compl
  have hG0sub : ∀ q : ℚ, ∀ p ∈ ((candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 (j + 1) t s) ∩ gZ x₀ (κ := κ) h ⁻¹' gamGood h44
      hκ hκ4 (x₀ := x₀) hb ∩ Nᶜ), p ∈ (candWin x₀ h44 hκ hκ4 hb P h W ζ hG.1 (j + 1) t s q 0) →
      p ∈ goodWin x₀ h44 hκ hκ4 hb P h W ζ hG.1 (j + 1) t s q :=
    fun q p hp hw => ⟨hp.1.1, of_not_not fun hn => hp.2 (hNsub hn), hw, hp.1.2⟩
  -- Lusin separation on every window
  have hC : ∀ q : ℚ, ∃ C : Set (Y49 0 0), MeasurableSet C ∧ (lastO (j + 1) t < q →
      gZ x₀ (κ := κ) h ⁻¹' M ∩ (((candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 (j + 1) t s) ∩ gZ x₀ (κ := κ) h ⁻¹' gamGood
          h44 hκ hκ4 (x₀ := x₀) hb ∩ Nᶜ) ∩ (candWin x₀ h44 hκ hκ4 hb P h W ζ hG.1 (j + 1) t s q 0)) = (((candEg x₀
          h44 hκ hκ4 hb P h W ζ hG.1 (j + 1) t s) ∩ gZ x₀ (κ := κ) h ⁻¹' gamGood h44 hκ hκ4 (x₀ := x₀) hb ∩ Nᶜ) ∩
          (candWin x₀ h44 hκ hκ4 hb P h W ζ hG.1 (j + 1) t s q 0)) ∩ (stopD (candW x₀ h44 hκ hκ4 hb h (j + 1) t)
          (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ) (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ) (fun _ => ⊤) q s) ⁻¹' C) := by
    intro q
    by_cases hq : lastO (j + 1) t < q
    · obtain ⟨C, hCm, hCe⟩ := exists_measurableSet_inter_eq
        (measurable_stopD_cand x₀ h44 hκ hκ4 hb h hG.1 (j + 1) t q s) hBm
        (hG0m.inter (measurableSet_candWin x₀ h44 hκ hκ4 hb P h W ζ hG.1 (j + 1) t s q 0))
        (fun p hp p' hp' he => ((hsat q hq p (hG0sub q p hp.2.1 hp.2.2) p' (hG0sub q p' hp'.1 hp'.2) he.symm
          (hMR hp.1)) M hM).1 hp.1)
      exact ⟨C, hCm, fun _ => hCe⟩
    · exact ⟨∅, MeasurableSet.empty, fun h' => absurd h' hq⟩
  choose C hCm hCe using hC
  have hAm : MeasurableSet (⋂ n : ℕ, ⋃ (q : ℚ) (_ : lastO (j + 1) t < q ∧
      q < lastO (j + 1) t + 1 / ((n : ℚ) + 1)), (candWin x₀ h44 hκ hκ4 hb P h W ζ hG.1 (j + 1) t s q 0) ∩ (stopD
          (candW x₀ h44 hκ hκ4 hb h (j + 1) t) (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ) (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ)
          (fun _ => ⊤) q s) ⁻¹' C q) :=
    MeasurableSet.iInter fun n => MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun _ =>
      (measurableSet_candWin x₀ h44 hκ hκ4 hb P h W ζ hG.1 (j + 1) t s q 0).inter
        (measurable_stopD_cand x₀ h44 hκ hκ4 hb h hG.1 (j + 1) t q s (hCm q))
  have hinv : ∀ n N₀ : ℕ, 1 / (((n + N₀ : ℕ) : ℚ) + 1) ≤ 1 / ((N₀ : ℚ) + 1) ∧
      1 / (((n + N₀ : ℕ) : ℚ) + 1) ≤ 1 / ((n : ℚ) + 1) := fun n N₀ => by
    have h1 : (0 : ℚ) ≤ n := Nat.cast_nonneg n
    have h2 : (0 : ℚ) ≤ N₀ := Nat.cast_nonneg N₀
    have e : ((n + N₀ : ℕ) : ℚ) = (n : ℚ) + N₀ := by push_cast; ring
    rw [e]
    constructor <;> exact one_div_le_one_div_of_le (by positivity) (by linarith)
  refine ⟨⋂ n : ℕ, ⋃ (q : ℚ) (_ : lastO (j + 1) t < q ∧ q < lastO (j + 1) t + 1 / ((n : ℚ) + 1)),
    (candWin x₀ h44 hκ hκ4 hb P h W ζ hG.1 (j + 1) t s q 0) ∩ (stopD (candW x₀ h44 hκ hκ4 hb h (j + 1) t)
        (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ) (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ) (fun _ => ⊤) q s) ⁻¹' C q, ?_, ?_, ?_⟩
  · -- an event of the Galmarino filtration at `0`
    refine measurableSet_candFilt_of_stopD x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs hAm fun q₀ hq₀ => ?_
    obtain ⟨N₀, hN₀⟩ := exists_nat_one_div_lt (sub_pos.2 hq₀)
    refine ⟨⋂ n : ℕ, ⋃ (q : ℚ) (_ : lastO (j + 1) t < q ∧
        q < lastO (j + 1) t + 1 / (((n + N₀ : ℕ) : ℚ) + 1)), stopRes q ⁻¹' C q,
      MeasurableSet.iInter fun n => MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun _ =>
        measurable_stopRes q (hCm q), ?_⟩
    intro p _ _ hpw
    simp only [mem_iInter, mem_iUnion, mem_inter_iff, mem_preimage, exists_prop]
    constructor
    · intro hpA n
      obtain ⟨q, ⟨hq1, hq2⟩, -, hqC⟩ := hpA (n + N₀)
      have hqle : q ≤ q₀ := by linarith [(hinv n N₀).1]
      exact ⟨q, ⟨hq1, hq2⟩, by rw [stopRes_stopD hqle s p]; exact hqC⟩
    · intro hpC n
      obtain ⟨q, ⟨hq1, hq2⟩, hqC⟩ := hpC n
      have hqle : q ≤ q₀ := by linarith [(hinv n N₀).1]
      rw [stopRes_stopD hqle s p] at hqC
      exact ⟨q, ⟨hq1, by linarith [(hinv n N₀).2]⟩,
        mem_candWin_of_le x₀ h44 hκ hκ4 hb P h W ζ hG.1 hpw hq1 hqle, hqC⟩
  · -- inside the alive event
    intro p hp
    simp only [mem_iInter, mem_iUnion, mem_inter_iff, exists_prop] at hp
    obtain ⟨q, -, hw, -⟩ := hp 0
    exact hw.1
  · -- equal to `gZ⁻¹ M` on the good samples
    have hgam := ae_gamGood_glue x₀ h44 hκ hκ4 hb P h W ζ hA hG hcf
    have hN' : ∀ᵐ p ∂(gMu x₀ (κ := κ) P h W ζ hG.1), p ∉ N :=
      ae_iff.2 (by simp only [not_not, ofPred_mem_eq]; exact hN0)
    filter_upwards [hgam, hgood, hN'] with p hpZ hpg hpN
    have hp0 : p ∈ ((candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 (j + 1) t s) ∩ gZ x₀ (κ := κ) h ⁻¹' gamGood h44 hκ hκ4
        (x₀ := x₀) hb ∩ Nᶜ) := ⟨⟨hpg.1, hpZ⟩, hpN⟩
    rw [eq_iff_iff]
    simp only [mem_iInter, mem_iUnion, mem_inter_iff, mem_preimage, exists_prop]
    constructor
    · intro hpA
      obtain ⟨q, ⟨hq1, -⟩, hw, hqC⟩ := hpA 0
      have h' : p ∈ (((candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 (j + 1) t s) ∩ gZ x₀ (κ := κ) h ⁻¹' gamGood h44 hκ hκ4
          (x₀ := x₀) hb ∩ Nᶜ) ∩ (candWin x₀ h44 hκ hκ4 hb P h W ζ hG.1 (j + 1) t s q 0)) ∩ (stopD (candW x₀ h44 hκ
          hκ4 hb h (j + 1) t) (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ) (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ) (fun _ => ⊤) q s)
          ⁻¹' C q := ⟨⟨hp0, hw⟩, hqC⟩
      rw [← hCe q hq1] at h'
      exact h'.1
    · intro hpM n
      have hDr := isReg_gamData h44 hκ hκ4 (x₀ := x₀) hb s
      have hDt := isTree_gamData x₀ h44 hκ hκ4 hb s
      have hal : gZ x₀ (κ := κ) h p ∈ (gamData h44 hκ hκ4 (x₀ := x₀) hb s).alive (j + 1) t :=
        (TreeData.reach (rootNL_pos _) (rootNR_pos _) hDr hDt (fun _ _ => Iff.rfl) (j + 1) t (gZ x₀ (κ := κ) h p)
          (hMR hpM)).2 (Nat.succ_pos j)
      have hpA : p ∈ (s3Alive s (candW x₀ h44 hκ hκ4 hb h (j + 1) t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 (j + 1) t
          s) (lastO (j + 1) t : ℝ)) :=
        (mem_gamData_alive_iff x₀ h44 hκ hκ4 hb P h W ζ hv hpg.1 hpZ).1 hal
      obtain ⟨q, hq1, hq2, hw⟩ := exists_mem_candWin x₀ h44 hκ hκ4 hb P h W ζ hG.1 hpA
        (ε := 1 / ((n : ℚ) + 1)) (by positivity)
      refine ⟨q, ⟨hq1, hq2⟩, hw, ?_⟩
      have h' : p ∈ gZ x₀ (κ := κ) h ⁻¹' M ∩ (((candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 (j + 1) t s) ∩ gZ x₀ (κ := κ) h
          ⁻¹' gamGood h44 hκ hκ4 (x₀ := x₀) hb ∩ Nᶜ) ∩ (candWin x₀ h44 hκ hκ4 hb P h W ζ hG.1 (j + 1) t s q 0)) :=
          ⟨hpM, hp0, hw⟩
      rw [hCe q hq1] at h'
      exact h'.2

end Win

/-- **The saturation of the glued pasts of the later root stages** (named statement, `GlueSat` everywhere). -/
def GlueSatStatement (h44 : Theorem12ParamCond44Statement.{0}) : Prop :=
  ∀ {κ x₀ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsFig51Bounds κ a b a' b')
    {Ω : Type} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
    (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀}),
    IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ →
    ∀ {q : ℚ}, 0 < q → ∀ {j : ℕ} {t : Fin (j + 1) → ℝ≥0}, IsValid (j + 1) t →
      GlueSat x₀ h44 hκ hκ4 hb P h W ζ hG.1 (j + 1) t (q : ℝ).toNNReal

/-- **`GluePastStatement` from the saturation** (and the clearance form of Part A). -/
theorem gluePastStatement_of_sat (h44 : Theorem12ParamCond44Statement.{0}) (hA : PartAInputsSixteenDivOfClearance)
    (hsat : GlueSatStatement h44) : GluePastStatement h44 := by
  intro κ x₀ a b a' b' hκ hκ4 hb Ω _ _ P _ h W ζ hG hcf us _ q hq j t hv
  exact gluePast_of_sat x₀ h44 hκ hκ4 hb P h W ζ hA hG hcf us hv _ (hsat hκ hκ4 hb P h W ζ hG hcf hq hv)

/-- **Theorem 1.2's leaf `hRootLater`** for the concrete stage objects, from the saturation of the glued pasts (and the
clearance form of Part A). -/
theorem rootLaterOn_s4Objects_of_sat (h44 : Theorem12ParamCond44Statement.{0})
    (hA : PartAInputsSixteenDivOfClearance) (hsat : GlueSatStatement h44) :
    RootLaterOn h44 (s4Objects h44) :=
  rootLaterOn_s4Objects_of_gluePast h44 hA (gluePastStatement_of_sat h44 hA hsat)

end InteractingSLE.Sec5.CrossCond.StagedRepJ
