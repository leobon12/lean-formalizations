import QuantumZipper.Proofs.Zipper.LocLenR5cDrive
import QuantumZipper.Proofs.Zipper.LocLenMeasArc
import QuantumZipper.Proofs.Zipper.LocLenF1FlowDet

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R5c (D75): local readers of the open-arc left length and of its hitting time

Open-arc copy (`handoff/FOLLOW-PAPER-13.md`, task R5c) of `LocHitScaleRead.lean:175–209`,
`LocHitScaleLen.lean` and `LocHitScaleArea.lean:82–108`: the left length is read with the
open-arc reader `LocLen.arcRd` (instead of `F1.vagueRd` on the closed arc), which computes
`arcLen` as soon as the unzipped field is good off `offSet W q` (`arcRd_eq_arcLen`); no global
boundary limit is used.

* `lenLocArc`, `measurable_lenLocArc`, **`lenLocArc_locRich`** (= the open-arc left length);
* `tauLocArc`, `measurable_tauLocArc`, **`tauLocArc_locRich`** (= `lenTimeArc`);
* `aLocArc`, `measurable_aLocArc`.

Own elementary bookkeeping, as for the originals (Sheffield arXiv:1012.4797 §5.4, pp. 70–72).
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped NNReal ENNReal Topology

namespace QuantumZipper.LocLen.R5c

open E6 D3Plus MeasUnzip CharFun

/-- `arcRd γ · b c` only sees the regularized averages on `[b - 1, c + 1]`. -/
theorem arcRd_congr_on {γ : ℝ} {y y' : FieldSample} {b c : ℝ}
    (h : ∀ k, ∀ t ∈ Icc (b - 1) (c + 1), avgReg y k (t : ℂ) = avgReg y' k (t : ℂ)) :
    arcRd γ y b c = arcRd γ y' b c := by
  unfold arcRd
  split_ifs with hbc
  · refine iSup_congr fun n => vagueRd_congr_on fun k t ht => h k t ⟨?_, ?_⟩
    · linarith [ht.1, arcMargin_pos hbc n]
    · linarith [ht.2, arcMargin_pos hbc n]
  · rfl

theorem arcRd_congr_avg {γ : ℝ} {y y' : FieldSample} (h : avgReg y = avgReg y') (b c : ℝ) :
    arcRd γ y b c = arcRd γ y' b c :=
  arcRd_congr_on fun k t _ => by rw [h]

/-- The open-arc left length at time `q` read from the rich local data. -/
def lenLocArc (γ κ : ℝ) (T R' : ℕ) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) T) (d : FullData) : ℝ≥0∞ :=
  arcRd γ (ufJ (natCast_nonneg' T) γ κ ((pathX κ T d.2, locField R' d.1), q))
    (sideJ (natCast_nonneg' T) κ q hq (pathX κ T d.2)).1 0

theorem measurable_lenLocArc (γ κ : ℝ) (T R' : ℕ) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) T) :
    Measurable (lenLocArc γ κ T R' q hq) :=
  measurable_arcRd_comp γ (measurable_ufJ_loc γ κ T R' q) (measurable_sideJ_loc κ T q hq)
    measurable_const

/-- **The local open-arc left length is the true open-arc left length** (copy of
`E6.lenLoc_locRich`), when the unzipped field is good off `offSet W q`. -/
theorem lenLocArc_locRich {γ κ : ℝ} (hκ : 0 < κ) {T R' : ℕ} (hTR : T ≤ R') {M : ℝ}
    (x : FieldSample) {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    (hM : ∀ r ∈ Icc (0 : ℝ) T, |W r| ≤ M) (hR' : 9 * M + 9 * Real.sqrt T + 7 ≤ R')
    {q : ℝ} (hq : q ∈ Icc (0 : ℝ) T) (hq0 : 0 < q)
    (halive : ∀ y : ℝ, y ≠ 0 → ∃ u, IsForwardSol W (y : ℂ) q u)
    (hlim : IsLQGGoodOff γ (unzippedField γ (x, W) q) (offSet W q)) :
    lenLocArc γ κ T R' q hq (locRich R' (x, W)) = (unzipLengthsArc γ (x, W) q).1 := by
  have hT := natCast_nonneg' T
  set f := pathX κ T (locRich R' (x, W)).2 with hfdef
  have hWf : ∀ r ∈ Icc (0 : ℝ) T, Wof κ T hT f r = W r := Wof_pathX_locRich hκ hTR x hW
  set W₁ := Wof κ T hT f with hW₁def
  have hW₁c : Continuous W₁ := continuous_Wof κ T hT f
  have hW₁0 : W₁ 0 = 0 := by rw [hWf 0 ⟨le_rfl, hT⟩, hW0]
  have hfPZ : f ∈ PZ hT κ := hW₁0
  have hWq : ∀ r ∈ Icc (0 : ℝ) q, W r = W₁ r := fun r hr =>
    (hWf r ⟨hr.1, hr.2.trans hq.2⟩).symm
  have hMq : ∀ r ∈ Icc (0 : ℝ) q, |W r| ≤ M := fun r hr => hM r ⟨hr.1, hr.2.trans hq.2⟩
  have halive' : ∀ y : ℝ, y ≠ 0 →
      ∃ u, IsForwardSol (Wof κ q hq.1 (resPath hT q f)) (y : ℂ) q u := by
    intro y hy
    obtain ⟨u, hu⟩ := halive y hy
    exact ⟨u, B5.isForwardSol_of_eqOn hu fun r hr => by
      rw [Wof_resPath_eqOn hT κ hq f r hr]; exact hWq r hr⟩
  have hside : sideImages W₁ q = sideJ hT κ q hq f := sideImages_eq_sideJ hT κ hq f halive'
  have hsideW : sideImages W q = sideImages W₁ q := ESM.sideImages_congr_drive hq.1 hWq
  have hsq : Real.sqrt q ≤ Real.sqrt T := Real.sqrt_le_sqrt hq.2
  have hb : |(sideJ hT κ q hq f).1| ≤ 3 * M + 3 * Real.sqrt T := by
    have := (abs_sideImages_le hW hW0 hq0 hMq halive).1
    rw [hsideW, hside] at this
    linarith
  have havg : avgReg (unzippedField γ (x, W₁) q) = avgReg (unzippedField γ (x, W) q) :=
    funext fun k => funext fun z => B5.avgReg_coordChange_eqOn x
      (ESM.fwdMapInv_eqOn_of_drive_eqOn hW₁c hW hW₁0 hW0 hq.1 fun r hr => (hWq r hr).symm)
      (Qc γ) k z
  have hflow : ∀ u ∈ H, ‖u‖ ≤ 3 * M + 3 * Real.sqrt T + 4 → ‖fwdMapInv W₁ q u‖ + 3 ≤ R' := by
    intro u hu hub
    have h1 := B5.norm_fwdMapInv_sub_le hW₁c hW₁0 hq0
      (fun r hr => by rw [← hWq r hr]; exact hMq r hr) hu
    have h2 := norm_sub_norm_le (fwdMapInv W₁ q u) u
    linarith
  unfold lenLocArc
  rw [arcRd_congr_on (y' := ufJ hT γ κ ((f, x), q)) ?_]
  · rw [arcRd_congr_avg ((avgReg_ufJ hT γ κ hfPZ hq x).trans havg)]
    have hp : 0 ≤ (sideImages W q).2 := sideImages_snd_nonneg_of_cont hW hW0 hq.1
    obtain ⟨hreg, ⟨ν, hν⟩, -⟩ := hlim
    rw [arcRd_eq_arcLen (isClosed_offSet W q).isOpen_compl (hν.isVagueLimitOnR hreg)
      (by rw [← hside, ← hsideW]; exact (Ioo_left_disjoint_offSet W q hp).subset_compl_right),
      ← hside, ← hsideW]
    rfl
  · intro k t ht
    refine avgReg_ufJ_locField hT hfPZ hq x hflow k ?_
    rw [Complex.norm_real, Real.norm_eq_abs]
    have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 ⟨le_rfl, hT⟩)
    have h2 := abs_le.1 hb
    have h3 := Real.sqrt_nonneg (T : ℝ)
    have : |t| ≤ 3 * M + 3 * Real.sqrt T + 1 :=
      abs_le.2 ⟨by linarith [ht.1], by linarith [ht.2]⟩
    linarith

/-- The hitting time of `ℓ` by the local open-arc left length, along the rationals of
`(0, T]` (copy of `E6.tauLoc`). -/
def tauLocArc (γ κ ℓ : ℝ) (T R' : ℕ) (d : FullData) : ℝ :=
  ratInf T fun q => ∃ hq : (q : ℝ) ∈ Icc (0 : ℝ) T, ENNReal.ofReal ℓ ≤ lenLocArc γ κ T R' q hq d

theorem measurable_tauLocArc (γ κ ℓ : ℝ) (T R' : ℕ) : Measurable (tauLocArc γ κ ℓ T R') := by
  refine measurable_ratInf T fun q => ?_
  by_cases hq : (q : ℝ) ∈ Icc (0 : ℝ) T
  · have e : {d : FullData | ∃ hq : (q : ℝ) ∈ Icc (0 : ℝ) T,
        ENNReal.ofReal ℓ ≤ lenLocArc γ κ T R' q hq d} =
        {d | ENNReal.ofReal ℓ ≤ lenLocArc γ κ T R' q hq d} := by
      ext d; simp only [Set.mem_ofPred_eq, exists_prop_of_true hq]
    rw [e]
    exact measurableSet_le measurable_const (measurable_lenLocArc γ κ T R' q hq)
  · have e : {d : FullData | ∃ hq : (q : ℝ) ∈ Icc (0 : ℝ) T,
        ENNReal.ofReal ℓ ≤ lenLocArc γ κ T R' q hq d} = ∅ := by
      ext d; simp only [Set.mem_ofPred_eq, mem_empty_iff_false, iff_false]
      exact fun ⟨h, _⟩ => hq h
    rw [e]
    exact MeasurableSet.empty

/-- **The local hitting time is the true open-arc hitting time** (copy of
`E6.tauLoc_locRich`). -/
theorem tauLocArc_locRich {γ κ ℓ : ℝ} (hκ : 0 < κ) {T R' : ℕ} (hTR : T ≤ R') {M : ℝ}
    (x : FieldSample) {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    (hM : ∀ r ∈ Icc (0 : ℝ) T, |W r| ≤ M) (hR' : 9 * M + 9 * Real.sqrt T + 7 ≤ R')
    (halive : ∀ y : ℝ, y ≠ 0 → ∀ s : ℝ, 0 ≤ s → ∃ u, IsForwardSol W (y : ℂ) s u)
    (hlim : ∀ q : ℚ, 0 < (q : ℝ) →
      IsLQGGoodOff γ (unzippedField γ (x, W) q) (offSet W q))
    (hmono : ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ T →
      (unzipLengthsArc γ (x, W) s).1 ≤ (unzipLengthsArc γ (x, W) t).1)
    (hreach : ENNReal.ofReal ℓ ≤ (unzipLengthsArc γ (x, W) T).1) :
    tauLocArc γ κ ℓ T R' (locRich R' (x, W)) = lenTimeArc γ ℓ (x, W) := by
  have hT := natCast_nonneg' T
  refine iInf_rat_eq (E := {s : ℝ | 0 ≤ s ∧ ENNReal.ofReal ℓ ≤ (unzipLengthsArc γ (x, W) s).1})
    (fun q hq0 hqT => ?_) (fun s hs => hs.1) (fun s hs q hsq hqT => ?_) ⟨T, hT, hreach⟩
    (csInf_le ⟨0, fun _ h => h.1⟩ ⟨hT, hreach⟩)
  · have hq : (q : ℝ) ∈ Icc (0 : ℝ) T := ⟨hq0.le, hqT⟩
    have e := lenLocArc_locRich (γ := γ) hκ hTR x hW hW0 hM hR' hq hq0
      (fun y hy => halive y hy q hq0.le) (hlim q hq0)
    constructor
    · rintro ⟨hq', hl⟩
      exact ⟨hq0.le, by rw [← e]; exact hl⟩
    · rintro ⟨-, hl⟩
      exact ⟨hq, by rw [e]; exact hl⟩
  · exact ⟨hs.1.trans hsq.le, hs.2.trans (hmono s q hs.1 hsq.le hqT)⟩

/-- The local scale at the local open-arc hitting time (copy of `E6.aLoc`). -/
def aLocArc (γ κ ℓ : ℝ) (T R' N : ℕ) (d : FullData) : ℝ :=
  aLocAt γ κ T R' N (tauLocArc γ κ ℓ T R' d) d

theorem measurable_aLocArc (γ κ ℓ : ℝ) (T R' N : ℕ) : Measurable (aLocArc γ κ ℓ T R' N) := by
  have h1 : Measurable fun d : FullData =>
      ((pathX κ T d.2, locField R' d.1), tauLocArc γ κ ℓ T R' d) :=
    ((measurable_pathX_snd κ T).prodMk ((measurable_locField R').comp measurable_fst)).prodMk
      (measurable_tauLocArc γ κ ℓ T R')
  have hy : Measurable fun d : FullData => yLoc γ κ T R' (tauLocArc γ κ ℓ T R' d) d :=
    (measurable_ufJ (natCast_nonneg' T) γ κ).comp h1
  exact measurable_ratInf N fun q =>
    measurableSet_le measurable_const ((Thm18Asm.measurable_areaProxy γ q).comp hy)

end QuantumZipper.LocLen.R5c
