/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.StagedS6Mart
import InteractingSLE.Spec.Sec5.Prop59StageLawProofWords
import InteractingSLE.Spec.Sec5.Prop59StageCross

/-!
# Proposition 5.9 at depth `ℓ`, step S7 (a): the restarted word's weights, its strict start and its threshold

Packet PROVE-STAGED-S7 (`planning/handoffs/PROVE-STAGED-S6.md` §5, item 1). For PIECES' candidate `(ℓ, t)` after its
last switch (the restarted word of PROVE-STAGED-S6, in tree order):

* **the weights in tree order are PIECES' stage weights**: `candAng_of_le` (the schedule's angles alternate,
  `π/2` at even indices), `swL_candAng`, `swR_candAng` (the switch weights are `newL`, `newR`),
  **`imgStageRhoL_treeIdx`**, **`imgStageRhoR_treeIdx`** (`imgStageRhoL … ∘ treeIdx = stageρL κ (jwL cL6 κ ρL) ℓ`);
* **the threshold condition fails at time `0`** for a strictly ordered start (`not_threshold_stage`): only the two
  newest born marks can sit at the driver, with weights `±(2 − κ/2) > −2`;
* **the image stage marks are strictly ordered in tree order** for a driver with a proper-arc trace
  (`imgBornL_lt_imgBornL`, `relL_lt_chartAL`, **`strictAnti_imgStageVL_treeIdx`** and the right mirrors), hence the
  restarted start is strictly ordered on every good alive sample whose counterflow history is good
  (**`strictAnti_s6Start`**, **`strictMono_s6Start`**).

Conditional helpers with distinct names; they replace no source theorem. R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal Real
open QuantumZipper (H chiC)

namespace InteractingSLE.Sec5.CrossCond.StagedS7

open WangWu hiding ratPt exists_ratPt_dist_lt
open WangWu.ImgWord LawUnique GlueCond Cond44Ref Word49 StagedS3 StagedS4 StagedS5 StagedS6
open Restart Exist.StagedLaw Exist.Staged MartChar.RealFlow
open Sec7.AdmCode Prop513TreeExtract Prop513Schedule Prop513Target Prop59Pieces StagedRepLater
open Prop59Stage Prop59System
open StagedFinal (imgStageRhoL imgStageRhoR swL swR imgStageVL imgStageVR imgBornL imgBornR rootVL rootVR)
open Prop59NodeTree (shiftDrv continuous_shiftDrv)
open WangWu (chartAL chartAR)
open Theorem14.GW2Schedule (schedAngle)
open QuantumZipper.RS (shiftDrive)
open Sec7.Lemma71C (capClock)

/-! ### The schedule's angles and the switch weights -/

section Angles

variable {κ : ℝ} {ℓ : ℕ} {t : Fin ℓ → ℝ≥0}

/-- **The candidate's angles alternate**: `π/2` at even indices, `−π/2` at odd ones, up to the last piece. -/
theorem candAng_of_le (hv : IsValid ℓ t) {m : ℕ} (hm : m ≤ ℓ) :
    candAng ℓ t m = if Even m then π / 2 else -(π / 2) := by
  have hlt : lastO ℓ t < lastO ℓ t + 1 := lt_add_one _
  simp only [candAng, candSched, schedAngle]
  rcases hm.lt_or_eq with hm | rfl
  · rw [getD_scheduleList_mkSched_lt hv hlt hm]
    simp [gmap, stageFlag]
  · rw [getD_scheduleList_mkSched_last hv hlt]
    simp [gmap, stageFlag]

theorem candAng_succ_sub (hv : IsValid ℓ t) {m : ℕ} (hm : m + 1 ≤ ℓ) :
    candAng ℓ t (m + 1) - candAng ℓ t m = if Even m then -π else π := by
  rw [candAng_of_le hv hm, candAng_of_le hv (by omega)]
  by_cases h : Even m
  · have h' : ¬ Even (m + 1) := Nat.not_even_iff_odd.2 h.add_one
    simp only [h, h', ↓reduceIte]
    ring
  · have h' : Even (m + 1) := (Nat.not_even_iff_odd.1 h).add_one
    simp only [h, h', ↓reduceIte]
    ring

/-- **The left switch weights are PIECES' alternating left weights.** -/
theorem swL_candAng (hv : IsValid ℓ t) {m : ℕ} (hm : m + 1 ≤ ℓ) :
    swL κ (fun j => candAng ℓ t j - candAng ℓ t 0) (m + 1) = newL κ m := by
  have e : candAng ℓ t (m + 1) - candAng ℓ t 0 - (candAng ℓ t (m + 1 - 1) - candAng ℓ t 0) =
      candAng ℓ t (m + 1) - candAng ℓ t m := by
    rw [Nat.add_sub_cancel]
    ring
  simp only [swL, newL]
  rw [e, candAng_succ_sub hv hm]
  have hM : angleWeightBound κ = π * chiC κ / sleLambda κ := rfl
  by_cases h : Even m
  · simp only [h, ↓reduceIte, h.neg_one_pow, one_mul, hM]
    ring
  · simp only [h, ↓reduceIte, (Nat.not_even_iff_odd.1 h).neg_one_pow, hM]
    ring

/-- **The right switch weights are PIECES' alternating right weights.** -/
theorem swR_candAng (hv : IsValid ℓ t) {m : ℕ} (hm : m + 1 ≤ ℓ) :
    swR κ (fun j => candAng ℓ t j - candAng ℓ t 0) (m + 1) = newR κ m := by
  have e : candAng ℓ t (m + 1) - candAng ℓ t 0 - (candAng ℓ t (m + 1 - 1) - candAng ℓ t 0) =
      candAng ℓ t (m + 1) - candAng ℓ t m := by
    rw [Nat.add_sub_cancel]
    ring
  simp only [swR, newR]
  rw [e, candAng_succ_sub hv hm]
  have hM : angleWeightBound κ = π * chiC κ / sleLambda κ := rfl
  by_cases h : Even m
  · simp only [h, ↓reduceIte, h.neg_one_pow, one_mul, hM]
    ring
  · simp only [h, ↓reduceIte, (Nat.not_even_iff_odd.1 h).neg_one_pow, hM]
    ring

/-- **The left weights of the restarted word in tree order are PIECES' stage weights** of the root word. -/
theorem imgStageRhoL_treeIdx (hv : IsValid ℓ t) {nL : ℕ} (ρL : Fin nL → ℝ) (i : Fin (nL + 1 + ℓ)) :
    imgStageRhoL κ (π / 2) ρL (fun j => candAng ℓ t j - candAng ℓ t 0) ℓ (treeIdx ℓ (nL + 1) i) =
      stageρL κ (jwL cL6 κ ρL) ℓ i := by
  rw [stageρL, consAlt_apply]
  by_cases h : (i : ℕ) < ℓ
  · rw [imgStageRhoL, append_treeIdx_of_lt _ _ h]
    simp only [consAltN, h, ↓reduceIte]
    exact swL_candAng hv (m := ℓ - 1 - i) (by omega)
  · rw [imgStageRhoL, append_treeIdx_of_ge _ _ (not_lt.1 h)]
    have hi : (i : ℕ) - ℓ < nL + 1 := by omega
    simp only [consAltN, h, ↓reduceIte, hi, ↓reduceDIte, jwL, Theta.imgRhoLT, Theta.cLT_pi_div_two]

/-- **The right weights of the restarted word in tree order are PIECES' stage weights** of the root word. -/
theorem imgStageRhoR_treeIdx (hv : IsValid ℓ t) {nR : ℕ} (ρR : Fin nR → ℝ) (j : Fin (nR + 1 + ℓ)) :
    imgStageRhoR κ (π / 2) ρR (fun j => candAng ℓ t j - candAng ℓ t 0) ℓ (treeIdx ℓ (nR + 1) j) =
      stageρR κ (jwR cR6 κ ρR) ℓ j := by
  rw [stageρR, consAlt_apply]
  by_cases h : (j : ℕ) < ℓ
  · rw [imgStageRhoR, append_treeIdx_of_lt _ _ h]
    simp only [consAltN, h, ↓reduceIte]
    exact swR_candAng hv (m := ℓ - 1 - j) (by omega)
  · rw [imgStageRhoR, append_treeIdx_of_ge _ _ (not_lt.1 h)]
    have hj : (j : ℕ) - ℓ < nR + 1 := by omega
    simp only [consAltN, h, ↓reduceIte, hj, ↓reduceDIte, jwR, Theta.imgRhoRT, Theta.cRT_pi_div_two]

end Angles

/-! ### The threshold condition at time `0` -/

section Threshold

variable {κ : ℝ}

/-- A sum over the marks at a point, when at most the mark `i₀` can be there. -/
theorem sum_filter_eq_ite {m : ℕ} {v : Fin m → ℝ} {w : ℝ} (i₀ : Fin m) (h : ∀ i, i ≠ i₀ → v i ≠ w)
    (ρ : Fin m → ℝ) :
    ∑ i ∈ Finset.univ.filter (fun i => v i = w), ρ i = if v i₀ = w then ρ i₀ else 0 := by
  have e : Finset.univ.filter (fun i => v i = w) = Finset.univ.filter (fun i => i = i₀ ∧ v i₀ = w) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hi
      by_cases hii : i = i₀
      · subst hii
        exact ⟨rfl, hi⟩
      · exact absurd hi (h i hii)
    · rintro ⟨rfl, hi⟩
      exact hi
  rw [e]
  split_ifs with h0
  · simp only [h0, and_true, Finset.filter_eq', Finset.mem_univ, ↓reduceIte, Finset.sum_singleton]
  · simp only [h0, and_false, Finset.filter_false, Finset.sum_empty]

theorem neg_two_lt_newL (hκ : 0 < κ) (hκ4 : κ < 4) (j : ℕ) : -2 < newL κ j := by
  have h1 := angleWeightBound_pos hκ hκ4
  have h2 := angleWeightBound_lt_two hκ
  simp only [newL]
  rcases neg_one_pow_eq_or ℝ j with h | h <;> rw [h] <;> linarith

theorem neg_two_lt_newR (hκ : 0 < κ) (hκ4 : κ < 4) (j : ℕ) : -2 < newR κ j := by
  have h1 := angleWeightBound_pos hκ hκ4
  have h2 := angleWeightBound_lt_two hκ
  simp only [newR]
  rcases neg_one_pow_eq_or ℝ j with h | h <;> rw [h] <;> linarith

/-- The newest left stage weight is `newL κ (ℓ − 1)`. -/
theorem stageρL_zero {nL₀ : ℕ} (ρL₀ : Fin nL₀ → ℝ) {ℓ : ℕ} (hℓ : 0 < ℓ) :
    stageρL κ ρL₀ ℓ ⟨0, by omega⟩ = newL κ (ℓ - 1) := by
  rw [stageρL, consAlt_apply]
  simp only [consAltN, hℓ, ↓reduceIte, Nat.sub_zero]

/-- The newest right stage weight is `newR κ (ℓ − 1)`. -/
theorem stageρR_zero {nR₀ : ℕ} (ρR₀ : Fin nR₀ → ℝ) {ℓ : ℕ} (hℓ : 0 < ℓ) :
    stageρR κ ρR₀ ℓ ⟨0, by omega⟩ = newR κ (ℓ - 1) := by
  rw [stageρR, consAlt_apply]
  simp only [consAltN, hℓ, ↓reduceIte, Nat.sub_zero]

theorem zero_lt_of_ne {m : ℕ} (hm : 0 < m) (i : Fin m) (hi : i ≠ ⟨0, hm⟩) : (⟨0, hm⟩ : Fin m) < i := by
  rw [Fin.lt_def]
  have : (i : ℕ) ≠ 0 := fun h => hi (Fin.ext h)
  simp only
  omega

/-- **The threshold condition fails at a strictly ordered start of a stage word** (`ℓ ≥ 1` switches): only the
newest mark of each side can sit at the driver, with weight `±(2 − κ/2) > −2`. -/
theorem not_threshold_stage (hκ : 0 < κ) (hκ4 : κ < 4) {nL₀ nR₀ ℓ : ℕ} (hℓ : 0 < ℓ) (ρL₀ : Fin nL₀ → ℝ)
    (ρR₀ : Fin nR₀ → ℝ) {w : ℝ} {vL : Fin (nL₀ + ℓ) → ℝ} {vR : Fin (nR₀ + ℓ) → ℝ} (hL : StrictAnti vL)
    (hR : StrictMono vR) (hL0 : vL ⟨0, by omega⟩ ≤ w) (hR0 : w ≤ vR ⟨0, by omega⟩) :
    ¬ ForceWord.ThresholdCondition (stageρL κ ρL₀ ℓ) (stageρR κ ρR₀ ℓ) w vL vR := by
  rw [ForceWord.ThresholdCondition,
    sum_filter_eq_ite (⟨0, by omega⟩ : Fin (nL₀ + ℓ))
      (fun i hi => (lt_of_lt_of_le (hL (zero_lt_of_ne _ i hi)) hL0).ne) _,
    sum_filter_eq_ite (⟨0, by omega⟩ : Fin (nR₀ + ℓ))
      (fun j hj => (lt_of_le_of_lt hR0 (hR (zero_lt_of_ne _ j hj))).ne') _]
  push Not
  refine ⟨?_, ?_⟩ <;> split_ifs
  · rw [stageρL_zero ρL₀ hℓ]
    exact neg_two_lt_newL hκ hκ4 _
  · norm_num
  · rw [stageρR_zero ρR₀ hℓ]
    exact neg_two_lt_newR hκ hκ4 _
  · norm_num

end Threshold

/-! ### Strictly ordered image stage marks -/

section Strict

variable {nL nR ℓ : ℕ} {w : ℝ → ℝ} {η : ℝ → ℂ} {T : ℝ} {A : ℕ → ℝ}

/-- **Strictly antitone in tree order.** -/
theorem strictAnti_append_treeIdx {n : ℕ} {b : Fin ℓ → ℝ} {r : Fin n → ℝ} (hb : StrictMono b)
    (hr : StrictAnti r) (hbr : ∀ j k, r k < b j) : StrictAnti fun i => Fin.append b r (treeIdx ℓ n i) := by
  intro i i' hii
  have hii' : (i : ℕ) < i' := hii
  by_cases h' : (i' : ℕ) < ℓ
  · have h : (i : ℕ) < ℓ := lt_trans hii' h'
    simp only [append_treeIdx_of_lt b r h, append_treeIdx_of_lt b r h']
    exact hb (show (⟨ℓ - 1 - (i' : ℕ), by omega⟩ : Fin ℓ) < ⟨ℓ - 1 - (i : ℕ), by omega⟩ by
      rw [Fin.mk_lt_mk]; omega)
  · by_cases h : (i : ℕ) < ℓ
    · simp only [append_treeIdx_of_lt b r h, append_treeIdx_of_ge b r (not_lt.1 h')]
      exact hbr _ _
    · simp only [append_treeIdx_of_ge b r (not_lt.1 h), append_treeIdx_of_ge b r (not_lt.1 h')]
      exact hr (show (⟨(i : ℕ) - ℓ, by omega⟩ : Fin n) < ⟨(i' : ℕ) - ℓ, by omega⟩ by
        rw [Fin.mk_lt_mk]; omega)

/-- **Strictly monotone in tree order** (the right marks). -/
theorem strictMono_append_treeIdx {n : ℕ} {b : Fin ℓ → ℝ} {r : Fin n → ℝ} (hb : StrictAnti b)
    (hr : StrictMono r) (hbr : ∀ j k, b j < r k) : StrictMono fun i => Fin.append b r (treeIdx ℓ n i) := by
  have h := strictAnti_append_treeIdx (b := fun j => -b j) (r := fun k => -r k) (fun _ _ h => neg_lt_neg (hb h))
    (fun _ _ h => neg_lt_neg (hr h)) fun j k => neg_lt_neg (hbr j k)
  intro i i' hii
  have := h hii
  have e : ∀ m, Fin.append (fun j => -b j) (fun k => -r k) m = -Fin.append b r m := fun m => by
    refine Fin.addCases (fun j => ?_) (fun k => ?_) m
    · simp only [Fin.append_left]
    · simp only [Fin.append_right]
  simp only [e] at this
  linarith

/-- For a driver whose trace is a proper arc, every positive point is alive for the reflected shifted driver. -/
theorem alive_neg_shiftDrv (hη : IsLoewnerTrace w η) (hηp : IsProperArc η) (hw : Continuous w) (hw0 : w 0 = 0)
    {S r : ℝ} (hS : 0 ≤ S) (hr : 0 ≤ r) : ∀ y, 0 < y → Alive (shiftDrv (fun s => -w s) S) y r := by
  have h := GlueImg.alive_neg_of_isProperArc (StagedLaw.isLoewnerTrace_futureArc hη hw hw0 hS)
    (WangWu.isProperArc_futureArc hη hηp hw hw0 hS) (QuantumZipper.RS.continuous_shiftDrive hw S)
    (StagedFinal.shiftDrive_zero_apply w S) hr
  rwa [shiftDrv_neg_eq]

/-- For a driver whose trace is a proper arc, every positive point is alive for the shifted driver. -/
theorem alive_shiftDrv (hη : IsLoewnerTrace w η) (hηp : IsProperArc η) (hw : Continuous w) (hw0 : w 0 = 0)
    {S r : ℝ} (hS : 0 ≤ S) (hr : 0 ≤ r) : ∀ y, 0 < y → Alive (shiftDrv w S) y r :=
  GlueImg.alive_of_isProperArc (StagedLaw.isLoewnerTrace_futureArc hη hw hw0 hS)
    (WangWu.isProperArc_futureArc hη hηp hw hw0 hS) (QuantumZipper.RS.continuous_shiftDrive hw S)
    (StagedFinal.shiftDrive_zero_apply w S) hr

theorem shiftDrive_zero_eq (hw0 : w 0 = 0) : shiftDrive w 0 = w := by
  funext r
  simp only [shiftDrive, zero_add, hw0, sub_zero]

/-- **A left mark born strictly later lies strictly closer to the driver.** -/
theorem imgBornL_lt_imgBornL (hη : IsLoewnerTrace w η) (hηp : IsProperArc η) (hw : Continuous w) (hw0 : w 0 = 0)
    {a b : ℕ} (ha : 0 ≤ A a) (hab : A a < A b) (hT : A b ≤ T) : imgBornL w T A a < imgBornL w T A b := by
  have h := StagedS3.chartAL_shift hw (a := A a) (S := A b) (r := T - A b) hab.le (sub_nonneg.2 hT)
  rw [show A b + (T - A b) - A a = T - A a by ring] at h
  simp only [imgBornL]
  rw [← h]
  have hc : Continuous (shiftDrv (fun s => -w s) (A b)) := continuous_shiftDrv hw.neg _
  have hx : 0 < -chartAL (shiftDrive w (A a)) (A b - A a) :=
    neg_pos.2 (StagedFinal.chartA_shiftDrive_of_isProperArc hη hηp hw hw0 ha (sub_pos.2 hab)).1
  have hal := alive_neg_shiftDrv hη hηp hw hw0 (ha.trans hab.le) (sub_nonneg.2 hT)
  have hlt := GlueImg.rightImg_lt_gImg_of_lt hc (sub_nonneg.2 hT) hal le_rfl hx
  rw [← rightImg_eq_gImg hc (sub_nonneg.2 hT) (hal _ hx)] at hlt
  have e : chartAL (shiftDrive w (A b)) (T - A b) =
      -rightImg (shiftDrv (fun s => -w s) (A b)) 0 (T - A b) - shiftDrv w (A b) (T - A b) := by
    rw [shiftDrv_neg_eq, shiftDrv_eq_shiftDrive]
    rfl
  rw [e]
  linarith

/-- **A right mark born strictly later lies strictly closer to the driver.** -/
theorem imgBornR_lt_imgBornR (hη : IsLoewnerTrace w η) (hηp : IsProperArc η) (hw : Continuous w) (hw0 : w 0 = 0)
    {a b : ℕ} (ha : 0 ≤ A a) (hab : A a < A b) (hT : A b ≤ T) : imgBornR w T A b < imgBornR w T A a := by
  have h := StagedS3.chartAR_shift hw (a := A a) (S := A b) (r := T - A b) hab.le (sub_nonneg.2 hT)
  rw [show A b + (T - A b) - A a = T - A a by ring] at h
  simp only [imgBornR]
  rw [← h]
  have hc : Continuous (shiftDrv w (A b)) := continuous_shiftDrv hw _
  have hx : 0 < chartAR (shiftDrive w (A a)) (A b - A a) :=
    (StagedFinal.chartA_shiftDrive_of_isProperArc hη hηp hw hw0 ha (sub_pos.2 hab)).2
  have hal := alive_shiftDrv hη hηp hw hw0 (ha.trans hab.le) (sub_nonneg.2 hT)
  have hlt := GlueImg.rightImg_lt_gImg_of_lt hc (sub_nonneg.2 hT) hal le_rfl hx
  rw [← rightImg_eq_gImg hc (sub_nonneg.2 hT) (hal _ hx)] at hlt
  have e : chartAR (shiftDrive w (A b)) (T - A b) =
      rightImg (shiftDrv w (A b)) 0 (T - A b) - shiftDrv w (A b) (T - A b) := rfl
  rw [e]
  linarith

/-- **Every flowed left mark lies strictly left of every mark born at a positive capacity `S ≤ T`.** -/
theorem relL_lt_chartAL (hη : IsLoewnerTrace w η) (hηp : IsProperArc η) (hw : Continuous w) (hw0 : w 0 = 0)
    {S : ℝ} (hS : 0 < S) (hT : S ≤ T) {x : ℝ} (hx : 0 ≤ x) :
    -rightImg (fun s => -w s) x T - w T < chartAL (shiftDrive w S) (T - S) := by
  have h := StagedS3.relL_shift hw (S := S) (r := T - S) hS.le (sub_nonneg.2 hT) x
  rw [show S + (T - S) = T by ring] at h
  rw [← h]
  have hc : Continuous (shiftDrv (fun s => -w s) S) := continuous_shiftDrv hw.neg _
  have h0 : chartAL w S < 0 := by
    have := (StagedFinal.chartA_shiftDrive_of_isProperArc hη hηp hw hw0 le_rfl hS).1
    rwa [shiftDrive_zero_eq hw0] at this
  have hy : 0 < -(-rightImg (fun s => -w s) x S - w S) := by
    have hm := rightImg_mono_index (w := fun s => -w s) hw.neg hS.le hx
    simp only [chartAL] at h0
    linarith
  have hal := alive_neg_shiftDrv hη hηp hw hw0 hS.le (sub_nonneg.2 hT)
  have hlt := GlueImg.rightImg_lt_gImg_of_lt hc (sub_nonneg.2 hT) hal le_rfl hy
  rw [← rightImg_eq_gImg hc (sub_nonneg.2 hT) (hal _ hy)] at hlt
  have e : chartAL (shiftDrive w S) (T - S) =
      -rightImg (shiftDrv (fun s => -w s) S) 0 (T - S) - shiftDrv w S (T - S) := by
    rw [shiftDrv_neg_eq, shiftDrv_eq_shiftDrive]
    rfl
  rw [e]
  linarith

/-- **Every flowed right mark lies strictly right of every mark born at a positive capacity `S ≤ T`.** -/
theorem chartAR_lt_relR (hη : IsLoewnerTrace w η) (hηp : IsProperArc η) (hw : Continuous w) (hw0 : w 0 = 0)
    {S : ℝ} (hS : 0 < S) (hT : S ≤ T) {x : ℝ} (hx : 0 ≤ x) :
    chartAR (shiftDrive w S) (T - S) < rightImg w x T - w T := by
  have h := StagedS3.relR_shift hw (S := S) (r := T - S) hS.le (sub_nonneg.2 hT) x
  rw [show S + (T - S) = T by ring] at h
  rw [← h]
  have hc : Continuous (shiftDrv w S) := continuous_shiftDrv hw _
  have h0 : 0 < chartAR w S := by
    have := (StagedFinal.chartA_shiftDrive_of_isProperArc hη hηp hw hw0 le_rfl hS).2
    rwa [shiftDrive_zero_eq hw0] at this
  have hy : 0 < rightImg w x S - w S := by
    have hm := rightImg_mono_index hw hS.le hx
    simp only [chartAR] at h0
    linarith
  have hal := alive_shiftDrv hη hηp hw hw0 hS.le (sub_nonneg.2 hT)
  have hlt := GlueImg.rightImg_lt_gImg_of_lt hc (sub_nonneg.2 hT) hal le_rfl hy
  rw [← rightImg_eq_gImg hc (sub_nonneg.2 hT) (hal _ hy)] at hlt
  have e : chartAR (shiftDrive w S) (T - S) = rightImg (shiftDrv w S) 0 (T - S) - shiftDrv w S (T - S) := rfl
  rw [e]
  linarith

/-- **The left image stage marks are strictly antitone in tree order**, for a driver with a proper-arc trace, positive
strictly increasing switch capacities `≤ T` and strictly antitone root marks `≤ 0`. -/
theorem strictAnti_imgStageVL_treeIdx (hη : IsLoewnerTrace w η) (hηp : IsProperArc η) (hw : Continuous w)
    (hw0 : w 0 = 0) (xL : Fin nL → ℝ) (ω : ℝ → ℝ) (s : ℝ) (hT : 0 ≤ T) (hA0 : ∀ j : Fin ℓ, 0 < A (j + 1))
    (hAT : ∀ j : Fin ℓ, A (j + 1) ≤ T) (hAm : StrictMono fun j : Fin ℓ => A (j + 1))
    (hx : StrictAnti (GlueImg.imgMarkL xL ω s)) (hx0 : ∀ k, GlueImg.imgMarkL xL ω s k ≤ 0) :
    StrictAnti fun i => imgStageVL xL ω s w T A ℓ (treeIdx ℓ (nL + 1) i) := by
  have hwn : Continuous fun r => -w r := hw.neg
  refine strictAnti_append_treeIdx
    (fun j j' hjj => imgBornL_lt_imgBornL hη hηp hw hw0 (hA0 j).le (hAm hjj) (hAT j')) (fun k k' hkk => ?_)
    fun j k => ?_
  · simp only [rootVL]
    have hal := GlueImg.alive_neg_of_isProperArc hη hηp hw hw0 hT
    have h0 : 0 ≤ -GlueImg.imgMarkL xL ω s k := neg_nonneg.2 (hx0 k)
    have hlt' : -GlueImg.imgMarkL xL ω s k < -GlueImg.imgMarkL xL ω s k' := neg_lt_neg (hx hkk)
    have hlt := GlueImg.rightImg_lt_gImg_of_lt hwn hT hal h0 hlt'
    rw [← rightImg_eq_gImg hwn hT (hal _ (h0.trans_lt hlt'))] at hlt
    linarith
  · simp only [rootVL, imgBornL]
    exact relL_lt_chartAL hη hηp hw hw0 (hA0 j) (hAT j) (neg_nonneg.2 (hx0 k))

/-- **The right image stage marks are strictly monotone in tree order.** -/
theorem strictMono_imgStageVR_treeIdx (hη : IsLoewnerTrace w η) (hηp : IsProperArc η) (hw : Continuous w)
    (hw0 : w 0 = 0) (xR : Fin nR → ℝ) (ω : ℝ → ℝ) (s : ℝ) (hT : 0 ≤ T) (hA0 : ∀ j : Fin ℓ, 0 < A (j + 1))
    (hAT : ∀ j : Fin ℓ, A (j + 1) ≤ T) (hAm : StrictMono fun j : Fin ℓ => A (j + 1))
    (hx : StrictMono (GlueImg.imgMarkR xR ω s)) (hx0 : ∀ k, 0 ≤ GlueImg.imgMarkR xR ω s k) :
    StrictMono fun i => imgStageVR xR ω s w T A ℓ (treeIdx ℓ (nR + 1) i) := by
  refine strictMono_append_treeIdx
    (fun j j' hjj => imgBornR_lt_imgBornR hη hηp hw hw0 (hA0 j).le (hAm hjj) (hAT j')) (fun k k' hkk => ?_)
    fun j k => ?_
  · simp only [rootVR]
    have hal := GlueImg.alive_of_isProperArc hη hηp hw hw0 hT
    have hlt := GlueImg.rightImg_lt_gImg_of_lt hw hT hal (hx0 k) (hx hkk)
    rw [← rightImg_eq_gImg hw hT (hal _ ((hx0 k).trans_lt (hx hkk)))] at hlt
    linarith
  · simp only [rootVR, imgBornR]
    exact chartAR_lt_relR hη hηp hw hw0 (hA0 j) (hAT j) (hx0 k)

end Strict

/-! ### The restarted start is strictly ordered -/

section Glued

variable {Ω : Type*} {nL nR ℓ : ℕ} {s : ℝ≥0} {Wj : ℝ≥0 → Ω → ℝ} {E : Set (Ω × HistorySpace 0 0)} {τ : ℝ}
  {τs : ℕ → ℝ}

/-- On the alive event the initial marks are the image stage marks of a continuous extension of the chain driver
whose Loewner trace is a proper arc. -/
theorem exists_s3X_eq_trace (hEg : ∀ p ∈ E, IsGood49 s (fun _ => ⊤) Wj p) {p : Ω × HistorySpace 0 0}
    (hp : p ∈ s3Alive s Wj E τ) (hτs : ∀ j : Fin ℓ, 0 ≤ τs (j + 1) ∧ τs (j + 1) ≤ τ) (xL : Fin nL → ℝ)
    (xR : Fin nR → ℝ) :
    ∃ (w : ℝ → ℝ) (η : ℝ → ℂ), Continuous w ∧ w 0 = 0 ∧ IsLoewnerTrace w η ∧ IsProperArc η ∧
      s3XL xL τs ℓ s Wj E τ p = imgStageVL xL (cfDrv0 s p.2) s w (s3Start s Wj E τ p)
        (fun m => capClock (gCurve s (fun _ => ⊤) Wj E p) (τs m)) ℓ ∧
      s3XR xR τs ℓ s Wj E τ p = imgStageVR xR (cfDrv0 s p.2) s w (s3Start s Wj E τ p)
        (fun m => capClock (gCurve s (fun _ => ⊤) Wj E p) (τs m)) ℓ := by
  classical
  have hγ := isKilledArc_gCurve hEg p
  obtain ⟨S, -, -, htS, w, hw, hw0, hEq, η, hηL, hηP, -⟩ :=
    hγ.exists_kPath_trace (StagedS4.s3Start_lt_kLife hEg hp)
  have hEq' : EqOn (kPath (gCurve s (fun _ => ⊤) Wj E p) (gPre s (fun _ => ⊤) Wj E p)) w
      (Icc 0 (s3Start s Wj E τ p : ℝ)) := hEq.mono (Icc_subset_Icc_right htS.le)
  have hA := s3_switch hEg hp hτs
  refine ⟨w, η, hw, hw0, hηL, hηP, ?_, ?_⟩
  · simp only [s3XL, hp, ↓reduceIte]
    exact imgStageVL_congr hw hEq' xL _ _ hA (s3Start s Wj E τ p).coe_nonneg
  · simp only [s3XR, hp, ↓reduceIte]
    exact imgStageVR_congr hw hEq' xR _ _ hA (s3Start s Wj E τ p).coe_nonneg

/-- The switch capacities of a positive strictly increasing switch schedule are positive and strictly increasing. -/
theorem capClock_switch_strict (hEg : ∀ p ∈ E, IsGood49 s (fun _ => ⊤) Wj p) {p : Ω × HistorySpace 0 0}
    (hp : p ∈ s3Alive s Wj E τ) (hτs : ∀ j : Fin ℓ, 0 < τs (j + 1) ∧ τs (j + 1) ≤ τ)
    (hτm : StrictMono fun j : Fin ℓ => τs (j + 1)) :
    (∀ j : Fin ℓ, 0 < capClock (gCurve s (fun _ => ⊤) Wj E p) (τs (j + 1))) ∧
      StrictMono fun j : Fin ℓ => capClock (gCurve s (fun _ => ⊤) Wj E p) (τs (j + 1)) := by
  have hγ := isKilledArc_gCurve hEg p
  have hτP : τ ∈ gPre s (fun _ => ⊤) Wj E p := hp.2
  have hmem : ∀ j : Fin ℓ, τs (j + 1) ∈ gPre s (fun _ => ⊤) Wj E p := fun j =>
    hγ.icc τ hτP ⟨(hτs j).1.le, (hτs j).2⟩
  refine ⟨fun j => ?_, fun j j' hjj => hγ.strictMonoOn_capClock (hmem j) (hmem j') (hτm hjj)⟩
  rw [← hγ.capClock_zero]
  exact hγ.strictMonoOn_capClock hγ.zero_mem (hmem j) (hτs j).1

/-- **The initial left marks of the restarted word are strictly antitone in tree order** on a good alive sample whose
counterflow history is good. -/
theorem strictAnti_s3XL_treeIdx (hEg : ∀ p ∈ E, IsGood49 s (fun _ => ⊤) Wj p) {p : Ω × HistorySpace 0 0}
    (hp : p ∈ s3Alive s Wj E τ) (hy : p.2 ∈ goodSet49 s) {xL : Fin nL → ℝ} (hxL : ∀ i, xL i ≤ 0)
    (hxLs : StrictAnti xL) (hτs : ∀ j : Fin ℓ, 0 < τs (j + 1) ∧ τs (j + 1) ≤ τ)
    (hτm : StrictMono fun j : Fin ℓ => τs (j + 1)) :
    StrictAnti fun i => s3XL xL τs ℓ s Wj E τ p (treeIdx ℓ (nL + 1) i) := by
  obtain ⟨w, η, hw, hw0, hηL, hηP, hL, -⟩ := exists_s3X_eq_trace (xR := (Fin.elim0 : Fin 0 → ℝ)) hEg hp
    (fun j => ⟨(hτs j).1.le, (hτs j).2⟩) xL
  rw [hL]
  obtain ⟨hy', hjL, -⟩ := hy
  have hc := continuous_cfDrv0 s p.2
  have hal : ∀ a, 0 < a → Alive (cfDrv0 s p.2) a s := fun a ha =>
    (StagedRep.alive_cfDrv0_of_mem_goodHitSet hy' s ha).1
  have hx : StrictAnti (GlueImg.imgMarkL xL (cfDrv0 s p.2) s) :=
    StagedRep.strictAnti_snoc
      (fun i i' hii => StagedRep.psiL_lt_psiL hc s.coe_nonneg hal hjL (hxLs hii) (hxL i))
      (fun i => StagedRep.junL_lt_psiL hc s.coe_nonneg hal hjL (hxL i))
  have hx0 : ∀ k, GlueImg.imgMarkL xL (cfDrv0 s p.2) s k ≤ 0 :=
    snoc_le (fun i => psiL_nonpos hc s.coe_nonneg hjL (hxL i))
      ((junL_le_psiL hc s.coe_nonneg hjL le_rfl).trans (psiL_nonpos hc s.coe_nonneg hjL le_rfl))
  obtain ⟨hA0, hAm⟩ := capClock_switch_strict hEg hp hτs hτm
  exact strictAnti_imgStageVL_treeIdx hηL hηP hw hw0 xL _ _ (s3Start s Wj E τ p).coe_nonneg hA0
    (fun j => (s3_switch hEg hp (fun j => ⟨(hτs j).1.le, (hτs j).2⟩) j).2) hAm hx hx0

/-- **The initial right marks of the restarted word are strictly monotone in tree order.** -/
theorem strictMono_s3XR_treeIdx (hEg : ∀ p ∈ E, IsGood49 s (fun _ => ⊤) Wj p) {p : Ω × HistorySpace 0 0}
    (hp : p ∈ s3Alive s Wj E τ) (hy : p.2 ∈ goodSet49 s) {xR : Fin nR → ℝ} (hxR : ∀ j, 0 ≤ xR j)
    (hxRs : StrictMono xR) (hτs : ∀ j : Fin ℓ, 0 < τs (j + 1) ∧ τs (j + 1) ≤ τ)
    (hτm : StrictMono fun j : Fin ℓ => τs (j + 1)) :
    StrictMono fun j => s3XR xR τs ℓ s Wj E τ p (treeIdx ℓ (nR + 1) j) := by
  obtain ⟨w, η, hw, hw0, hηL, hηP, -, hR⟩ := exists_s3X_eq_trace (xL := (Fin.elim0 : Fin 0 → ℝ)) hEg hp
    (fun j => ⟨(hτs j).1.le, (hτs j).2⟩) xR
  rw [hR]
  obtain ⟨hy', -, hjR⟩ := hy
  have hc := continuous_cfDrv0 s p.2
  have hal : ∀ a, 0 < a → Alive (fun r => -cfDrv0 s p.2 r) a s := fun a ha =>
    (StagedRep.alive_cfDrv0_of_mem_goodHitSet hy' s ha).2
  have hx : StrictMono (GlueImg.imgMarkR xR (cfDrv0 s p.2) s) :=
    StagedRep.strictMono_snoc
      (fun j j' hjj => StagedRep.psiR_lt_psiR hc s.coe_nonneg hal hjR (hxRs hjj) (hxR j))
      (fun j => StagedRep.psiR_lt_junR hc s.coe_nonneg hal hjR (hxR j))
  have hx0 : ∀ k, 0 ≤ GlueImg.imgMarkR xR (cfDrv0 s p.2) s k :=
    le_snoc (fun j => psiR_nonneg hc s.coe_nonneg hjR (hxR j))
      ((psiR_nonneg hc s.coe_nonneg hjR le_rfl).trans (psiR_le_junR hc s.coe_nonneg hjR le_rfl))
  obtain ⟨hA0, hAm⟩ := capClock_switch_strict hEg hp hτs hτm
  exact strictMono_imgStageVR_treeIdx hηL hηP hw hw0 xR _ _ (s3Start s Wj E τ p).coe_nonneg hA0
    (fun j => (s3_switch hEg hp (fun j => ⟨(hτs j).1.le, (hτs j).2⟩) j).2) hAm hx hx0

/-- **The restarted word starts strictly ordered on the left** (good alive sample, good counterflow history). -/
theorem strictAnti_s6Start (hEg : ∀ p ∈ E, IsGood49 s (fun _ => ⊤) Wj p) {p : Ω × HistorySpace 0 0}
    (hp : p ∈ s3Alive s Wj E τ) (hy : p.2 ∈ goodSet49 s) {xL : Fin nL → ℝ} (hxL : ∀ i, xL i ≤ 0)
    (hxLs : StrictAnti xL) (hτs : ∀ j : Fin ℓ, 0 < τs (j + 1) ∧ τs (j + 1) ≤ τ)
    (hτm : StrictMono fun j : Fin ℓ => τs (j + 1)) :
    StrictAnti fun i => s6VL xL τs ℓ s Wj E τ i 0 p := by
  simp only [s6VL_zero hEg (fun j => ⟨(hτs j).1.le, (hτs j).2⟩) p]
  exact strictAnti_s3XL_treeIdx hEg hp hy hxL hxLs hτs hτm

/-- **The restarted word starts strictly ordered on the right.** -/
theorem strictMono_s6Start (hEg : ∀ p ∈ E, IsGood49 s (fun _ => ⊤) Wj p) {p : Ω × HistorySpace 0 0}
    (hp : p ∈ s3Alive s Wj E τ) (hy : p.2 ∈ goodSet49 s) {xR : Fin nR → ℝ} (hxR : ∀ j, 0 ≤ xR j)
    (hxRs : StrictMono xR) (hτs : ∀ j : Fin ℓ, 0 < τs (j + 1) ∧ τs (j + 1) ≤ τ)
    (hτm : StrictMono fun j : Fin ℓ => τs (j + 1)) :
    StrictMono fun j => s6VR xR τs ℓ s Wj E τ j 0 p := by
  simp only [s6VR_zero hEg (fun j => ⟨(hτs j).1.le, (hτs j).2⟩) p]
  exact strictMono_s3XR_treeIdx hEg hp hy hxR hxRs hτs hτm

end Glued

end InteractingSLE.Sec5.CrossCond.StagedS7
