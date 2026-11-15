/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2TipStageWord
import InteractingSLE.Spec.Supplement.GB6RestartProofWord
import InteractingSLE.Spec.Supplement.GW2JDetR5Stages
import InteractingSLE.Spec.Supplement.GW2RdShift
import InteractingSLE.Spec.Exist.StagedLawData

/-!
# GW2's stage word map, part 1: far heights and the two totals separately (D9's check)

Packet PROVE-GW2-GEOM2 (round 7: the stage word map, moved from PROVE-GW2-STAGEMEAN; DECISIONS-FABLE-2 D9,
DECISIONS-FABLE-3 D12 item 3). D9: the two limit totals of a near family presenting the stage word are needed
separately, `∑ ρL₀ = κ − 4`, `∑ ρR₀ = κ/2 − 2` (N4's `horientation`), and they come out right only with R62's offset
`specOffset κ = 2πχ`. The totals of an angle-`θ` flow-line word depend only on the word's two far heights
(`GW2TipStage.sum_flowLineRhoL_eq_of_far`), so the check is: the stage word has far heights `−λ′ + πχ` (left) and
`λ′ − πχ` (right), at every stage. This file proves it.

* `FarL c h`, `FarR c h`: the word equals `h` eventually to the left (right), off its jumps;
* **`farL_flowLine`**, **`farR_flowLine`**: then it equals `h` beyond the outermost flow-line mark (the hypothesis
  form of `GW2TipStage.sum_flowLineRhoL_eq_of_far` and of `GW2Sdw.totals_eq_of_presentsO`);
* `sum_flowLineRhoL_of_farL`, `sum_flowLineRhoR_of_farR`, **`totals_half_pi_of_far`**,
  **`totals_neg_half_pi_of_far`**: the totals `(κ − 4, κ/2 − 2)` at `π/2` and `(κ/2 − 2, κ − 4)` at `−π/2`;
* **`farL_stopWord`**, **`farR_stopWord`**: a stopped piece of any angle keeps both far heights;
* `farL_shiftW`, `farR_shiftW` (re-centring at a root), `fn_upW`, `farL_upW`, `farR_upW` (raising);
* **`farL_jointWordOfRec`**, **`farR_jointWordOfRec`**: the root word with R62's offset,
  `jointWordOfRec (specOffset κ) κ c′ r`, has far heights `−λ′ + πχ` and `λ′ − πχ` as soon as the counterflow's hull
  has positive extent on both sides (`markPosL < 0 < markPos` at the seed);
* `pastRoot`, **`farL_stageWord`**, **`farR_stageWord`**: every stage word `GW2JDetR5.stageWord W₀ θ n x` keeps the
  root word's far heights.

Deterministic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Finset
open scoped NNReal ENNReal
open QuantumZipper (chiC)

namespace InteractingSLE.Theorem14.GW2Wm

open Restart Exist.Staged Exist.StagedLaw Sec7.StripSysField GW2JointKernel GW1W GW2TipStage

/-! ### Far heights -/

/-- **The far-left height of a word**: eventually to the left, off the jumps, the word is `h`. -/
def FarL (c : BoundaryWord) (h : ℝ) : Prop := ∃ A : ℝ, ∀ y, y < A → y ∉ c.jumps → c.fn y = h

/-- **The far-right height of a word**: eventually to the right, off the jumps, the word is `h`. -/
def FarR (c : BoundaryWord) (h : ℝ) : Prop := ∃ B : ℝ, ∀ y, B < y → y ∉ c.jumps → c.fn y = h

section Flow

variable {κ : ℝ} {c : BoundaryWord} {hL hR : ℝ}

/-- **The far-left height beyond the outermost left flow-line mark.** -/
theorem farL_flowLine (hκ : 0 < κ) (hfar : FarL c hL) :
    ∀ y, y < flowLineXL c.fn c.jumps 0 (lastL c.fn c.jumps) → y ∉ c.jumps → c.fn y = hL := by
  obtain ⟨A, hA⟩ := hfar
  have hb := c.isPiecewiseConstantBoundaryData
  have hm0 : flowLineXL c.fn c.jumps 0 (lastL c.fn c.jumps) ≤ 0 := GW3Word.flowLineXL_nonpos _ _ _
  have hle : ∀ i, flowLineXL c.fn c.jumps 0 (lastL c.fn c.jumps) ≤ flowLineXL c.fn c.jumps 0 i := fun i =>
    (StrictAnti.antitone (fun _ _ h => GW0.flowLineXL_lt c.fn c.jumps 0 h))
      (show i ≤ lastL c.fn c.jumps from Fin.le_def.2 (by simp only [lastL]; have := i.isLt; omega))
  have hval : ∀ y, y < flowLineXL c.fn c.jumps 0 (lastL c.fn c.jumps) → y ∉ c.jumps →
      c.fn y = -sleLambda κ * (1 + ∑ i, flowLineRhoL κ c.fn c.jumps 0 0 i) := by
    intro y hy hyJ
    have hy0 : y < 0 := hy.trans_le hm0
    rw [← Sec4.forceBoundaryData_flowLine hκ hb hy0.ne hyJ, Sec4.forceBoundaryData_of_neg _ _ _ _ hy0,
      Finset.filter_true_of_mem fun i _ => hy.trans_le (hle i)]
  intro y hy hyJ
  obtain ⟨u, -, hu2, huJ⟩ := Sec4.exists_mem_Ioo_not_mem c.jumps (show min A y - 1 < min A y by linarith)
  rw [hval y hy hyJ, ← hval u (lt_of_lt_of_le hu2 ((min_le_right _ _).trans hy.le)) huJ]
  exact hA u (lt_of_lt_of_le hu2 (min_le_left _ _)) huJ

/-- **The far-right height beyond the outermost right flow-line mark.** -/
theorem farR_flowLine (hκ : 0 < κ) (hfar : FarR c hR) :
    ∀ y, flowLineXR c.fn c.jumps 0 (lastR c.fn c.jumps) < y → y ∉ c.jumps → c.fn y = hR := by
  obtain ⟨B, hB⟩ := hfar
  have hb := c.isPiecewiseConstantBoundaryData
  have hm0 : 0 ≤ flowLineXR c.fn c.jumps 0 (lastR c.fn c.jumps) := GW3Word.flowLineXR_nonneg _ _ _
  have hle : ∀ j, flowLineXR c.fn c.jumps 0 j ≤ flowLineXR c.fn c.jumps 0 (lastR c.fn c.jumps) := fun j =>
    (StrictMono.monotone (fun _ _ h => GW0.flowLineXR_lt c.fn c.jumps 0 h))
      (show j ≤ lastR c.fn c.jumps from Fin.le_def.2 (by simp only [lastR]; have := j.isLt; omega))
  have hval : ∀ y, flowLineXR c.fn c.jumps 0 (lastR c.fn c.jumps) < y → y ∉ c.jumps →
      c.fn y = sleLambda κ * (1 + ∑ j, flowLineRhoR κ c.fn c.jumps 0 0 j) := by
    intro y hy hyJ
    have hy0 : 0 < y := hm0.trans_lt hy
    rw [← Sec4.forceBoundaryData_flowLine hκ hb hy0.ne' hyJ, Sec4.forceBoundaryData_of_nonneg _ _ _ _ hy0.le,
      Finset.filter_true_of_mem fun j _ => (hle j).trans hy.le]
  intro y hy hyJ
  obtain ⟨u, hu1, -, huJ⟩ := Sec4.exists_mem_Ioo_not_mem c.jumps (show max B y < max B y + 1 by linarith)
  rw [hval y hy hyJ, ← hval u (hy.trans_le ((le_max_right _ _).trans hu1.le)) huJ]
  exact hB u (lt_of_le_of_lt (le_max_left _ _) hu1) huJ

/-- The left total of the angle-`θ` flow-line word from the far-left height. -/
theorem sum_flowLineRhoL_of_farL (hκ : 0 < κ) (hfar : FarL c hL) (θ : ℝ) :
    ∑ i, flowLineRhoL κ c.fn c.jumps 0 θ i = Sec4.cumWeightLeft κ (hL + θ * chiC κ) :=
  sum_flowLineRhoL_eq_of_far hκ c.isPiecewiseConstantBoundaryData θ (farL_flowLine hκ hfar)

/-- The right total of the angle-`θ` flow-line word from the far-right height. -/
theorem sum_flowLineRhoR_of_farR (hκ : 0 < κ) (hfar : FarR c hR) (θ : ℝ) :
    ∑ j, flowLineRhoR κ c.fn c.jumps 0 θ j = Sec4.cumWeightRight κ (hR + θ * chiC κ) :=
  sum_flowLineRhoR_eq_of_far hκ c.isPiecewiseConstantBoundaryData θ (farR_flowLine hκ hfar)

/-- **Both totals separately at `θ = π/2`** (N4's `horientation`, leftward case): `(κ − 4, κ/2 − 2)`. -/
theorem totals_half_pi_of_far (hκ : 0 < κ) (hfL : FarL c (-sleLambda (16 / κ) + Real.pi * chiC κ))
    (hfR : FarR c (sleLambda (16 / κ) - Real.pi * chiC κ)) :
    ∑ i, flowLineRhoL κ c.fn c.jumps 0 (Real.pi / 2) i = κ - 4 ∧
      ∑ j, flowLineRhoR κ c.fn c.jumps 0 (Real.pi / 2) j = κ / 2 - 2 := by
  rw [sum_flowLineRhoL_of_farL hκ hfL, sum_flowLineRhoR_of_farR hκ hfR]
  exact totals_far_half_pi hκ

/-- **Both totals separately at `θ = −π/2`** (N4's `horientation`, rightward case): `(κ/2 − 2, κ − 4)`. -/
theorem totals_neg_half_pi_of_far (hκ : 0 < κ) (hfL : FarL c (-sleLambda (16 / κ) + Real.pi * chiC κ))
    (hfR : FarR c (sleLambda (16 / κ) - Real.pi * chiC κ)) :
    ∑ i, flowLineRhoL κ c.fn c.jumps 0 (-(Real.pi / 2)) i = κ / 2 - 2 ∧
      ∑ j, flowLineRhoR κ c.fn c.jumps 0 (-(Real.pi / 2)) j = κ - 4 := by
  rw [sum_flowLineRhoL_of_farL hκ hfL, sum_flowLineRhoR_of_farR hκ hfR]
  exact totals_far_neg_half_pi hκ

end Flow

/-! ### A stopped piece keeps the far heights -/

section Stop

variable {κ : ℝ} {c : BoundaryWord} {hL hR : ℝ}

/-- **A stopped piece of any angle keeps the far-left height.** -/
theorem farL_stopWord (hκ : 0 < κ) (hfar : FarL c hL) (θ : ℝ) (r : RecData) :
    FarL (stopWord κ (c, θ, r)) hL := by
  have hne : (Finset.range (flowLineNL c.fn c.jumps 0)).Nonempty :=
    ⟨0, Finset.mem_range.2 (Supp8.GB6.zero_lt_flowLineNL _ _)⟩
  refine ⟨(Finset.range (flowLineNL c.fn c.jumps 0)).inf' hne
    (fun i => markPosL (rdrv r) (rtime r) ((padFL 0 0 c.fn c.jumps).1.1 i)), fun z hz hzJ => ?_⟩
  have hlt : ∀ i < flowLineNL c.fn c.jumps 0, z < markPosL (rdrv r) (rtime r) ((padFL 0 0 c.fn c.jumps).1.1 i) :=
    fun i hi => hz.trans_le (Finset.inf'_le _ (Finset.mem_range.2 hi))
  have hp0 : markPosL (rdrv r) (rtime r) ((padFL 0 0 c.fn c.jumps).1.1 0) ≤ 0 := by
    rw [Supp8.GB6.padFL_seedL]
    exact markPosL_nonpos (continuous_rdrv r) (rdrv_zero r) (rtime_nonneg r) le_rfl
  have hz0 : z < 0 := (hlt 0 (Supp8.GB6.zero_lt_flowLineNL _ _)).trans_le hp0
  have hmo := isMarkOrder_stopWord c r
  refine (fn_forceWord κ (padFL κ θ c.fn c.jumps).2.1 (padFL κ θ c.fn c.jumps).2.2 (θ * chiC κ) hmo hzJ
    hz0.ne).trans ?_
  rw [Sec4.forceBoundaryData_of_neg _ _ _ _ hz0,
    Finset.filter_true_of_mem fun (i : Fin (flowLineNL c.fn c.jumps 0)) _ => hlt i i.2]
  have hs : ∑ i : Fin (flowLineNL c.fn c.jumps 0), (padFL κ θ c.fn c.jumps).2.1 i =
      Sec4.cumWeightLeft κ (hL + θ * chiC κ) := by
    rw [← sum_flowLineRhoL_of_farL hκ hfar θ]
    exact Finset.sum_congr rfl fun i _ => padFL_snd_fst_fin κ θ c.fn c.jumps i
  rw [hs]
  have hlam : sleLambda κ ≠ 0 := (Sec4.sleLambda_pos hκ).ne'
  unfold Sec4.cumWeightLeft
  field_simp
  ring

/-- **A stopped piece of any angle keeps the far-right height.** -/
theorem farR_stopWord (hκ : 0 < κ) (hfar : FarR c hR) (θ : ℝ) (r : RecData) :
    FarR (stopWord κ (c, θ, r)) hR := by
  have hne : (Finset.range (flowLineNR c.fn c.jumps 0)).Nonempty :=
    ⟨0, Finset.mem_range.2 (Supp8.GB6.zero_lt_flowLineNR _ _)⟩
  refine ⟨(Finset.range (flowLineNR c.fn c.jumps 0)).sup' hne
    (fun j => markPos (rdrv r) (rtime r) ((padFL 0 0 c.fn c.jumps).1.2 j)), fun z hz hzJ => ?_⟩
  have hlt : ∀ j < flowLineNR c.fn c.jumps 0, markPos (rdrv r) (rtime r) ((padFL 0 0 c.fn c.jumps).1.2 j) < z :=
    fun j hj => (Finset.le_sup' _ (Finset.mem_range.2 hj)).trans_lt hz
  have hp0 : 0 ≤ markPos (rdrv r) (rtime r) ((padFL 0 0 c.fn c.jumps).1.2 0) := by
    rw [Supp8.GB6.padFL_seedR]
    exact markPos_nonneg (continuous_rdrv r) (rdrv_zero r) (rtime_nonneg r) le_rfl
  have hz0 : 0 < z := hp0.trans_lt (hlt 0 (Supp8.GB6.zero_lt_flowLineNR _ _))
  have hmo := isMarkOrder_stopWord c r
  refine (fn_forceWord κ (padFL κ θ c.fn c.jumps).2.1 (padFL κ θ c.fn c.jumps).2.2 (θ * chiC κ) hmo hzJ
    hz0.ne').trans ?_
  rw [Sec4.forceBoundaryData_of_nonneg _ _ _ _ hz0.le,
    Finset.filter_true_of_mem fun (j : Fin (flowLineNR c.fn c.jumps 0)) _ => (hlt j j.2).le]
  have hs : ∑ j : Fin (flowLineNR c.fn c.jumps 0), (padFL κ θ c.fn c.jumps).2.2 j =
      Sec4.cumWeightRight κ (hR + θ * chiC κ) := by
    rw [← sum_flowLineRhoR_of_farR hκ hfar θ]
    exact Finset.sum_congr rfl fun j _ => padFL_snd_snd_fin κ θ c.fn c.jumps j
  rw [hs]
  have hlam : sleLambda κ ≠ 0 := (Sec4.sleLambda_pos hκ).ne'
  unfold Sec4.cumWeightRight
  field_simp
  ring

end Stop

/-! ### Re-centring and raising -/

section Shift

variable {c : BoundaryWord} {h : ℝ}

theorem add_notMem_jumps_of_notMem_shiftW {a : ℝ} {y : ℝ}
    (hy : y ∉ (Exist.StagedLaw.BoundaryWord.shiftW a c).jumps) : y + a ∉ c.jumps := by
  intro h
  apply hy
  rw [Exist.StagedLaw.BoundaryWord.jumps_shiftW]
  exact Finset.mem_image.2 ⟨y + a, h, by ring⟩

theorem farL_shiftW (a : ℝ) (hf : FarL c h) : FarL (Exist.StagedLaw.BoundaryWord.shiftW a c) h := by
  obtain ⟨A, hA⟩ := hf
  exact ⟨A - a, fun y hy hyJ => by
    rw [Exist.StagedLaw.BoundaryWord.fn_shiftW]; exact hA _ (by linarith) (add_notMem_jumps_of_notMem_shiftW hyJ)⟩

theorem farR_shiftW (a : ℝ) (hf : FarR c h) : FarR (Exist.StagedLaw.BoundaryWord.shiftW a c) h := by
  obtain ⟨B, hB⟩ := hf
  exact ⟨B - a, fun y hy hyJ => by
    rw [Exist.StagedLaw.BoundaryWord.fn_shiftW]; exact hB _ (by linarith) (add_notMem_jumps_of_notMem_shiftW hyJ)⟩

/-- The raised word is the word plus the constant. -/
theorem fn_upW (a : ℝ) (c : BoundaryWord) (y : ℝ) : (GW2Rd.upW a c).fn y = c.fn y + a := rfl

theorem jumps_upW (a : ℝ) (c : BoundaryWord) : (GW2Rd.upW a c).jumps = c.jumps := rfl

theorem farL_upW (a : ℝ) (hf : FarL c h) : FarL (GW2Rd.upW a c) (h + a) := by
  obtain ⟨A, hA⟩ := hf
  exact ⟨A, fun y hy hyJ => by rw [fn_upW, hA y hy hyJ]⟩

theorem farR_upW (a : ℝ) (hf : FarR c h) : FarR (GW2Rd.upW a c) (h + a) := by
  obtain ⟨B, hB⟩ := hf
  exact ⟨B, fun y hy hyJ => by rw [fn_upW, hB y hy hyJ]⟩

end Shift

/-! ### The root word with R62's offset -/

section Root

variable {κ : ℝ}

theorem neg_inv_mem_jumps_retWord {g : BoundaryWord} (hg : g.IsSorted) (a l : ℝ) {y : ℝ}
    (hy : -y⁻¹ ∈ g.jumps) : y ∈ (retWord a l g).jumps := by
  rw [jumps_retWord hg]
  refine Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨_, hy, ?_⟩)
  rw [inv_neg, inv_inv, neg_neg]

/-- **The far-left height of the root word is `−λ′ + πχ`** (R62's offset; the counterflow's right flank, returned
through `R`). -/
theorem farL_jointWordOfRec (hκ : 0 < κ) (c' : BoundaryWord) (r : RecData)
    (hpos : 0 < markPos (rdrv r) (rtime r) 0) :
    FarL (jointWordOfRec (specOffset κ) κ c' r) (-sleLambda (16 / κ) + Real.pi * chiC κ) := by
  refine ⟨-(markPos (rdrv r) (rtime r) 0)⁻¹, fun y hy hyJ => ?_⟩
  have hm : 0 < (markPos (rdrv r) (rtime r) 0)⁻¹ := inv_pos.2 hpos
  have hy0 : y < 0 := by linarith
  have hgs := isSorted_stopWord (16 / κ) (c', 0, r)
  unfold jointWordOfRec at hyJ ⊢
  rw [fn_retWord hgs _ _ hyJ]
  have hz0 : 0 < -y⁻¹ := neg_pos.2 (inv_lt_zero.2 hy0)
  have hzm : -y⁻¹ < markPos (rdrv r) (rtime r) 0 := by
    rw [← inv_neg]
    exact inv_lt_of_inv_lt₀ hpos (by linarith)
  have hzJ : -y⁻¹ ∉ (stopWord (16 / κ) (c', 0, r)).jumps := fun h => hyJ (neg_inv_mem_jumps_retWord hgs _ _ h)
  unfold returnData liftBoundary
  rw [Supp8.GB6.stopWord_fn_flank_right c' 0 r hz0 hzm hzJ, ite_eq_left_of_eq_true _ _ (eq_true hy0),
    retA_add_specOffset hκ]
  unfold retL
  rw [Sec4.chiC_sixteen_div hκ]
  ring

/-- **The far-right height of the root word is `λ′ − πχ`** (R62's offset; the counterflow's left flank, returned
through `R`). -/
theorem farR_jointWordOfRec (hκ : 0 < κ) (c' : BoundaryWord) (r : RecData)
    (hneg : markPosL (rdrv r) (rtime r) 0 < 0) :
    FarR (jointWordOfRec (specOffset κ) κ c' r) (sleLambda (16 / κ) - Real.pi * chiC κ) := by
  refine ⟨-(markPosL (rdrv r) (rtime r) 0)⁻¹, fun y hy hyJ => ?_⟩
  have hm : (markPosL (rdrv r) (rtime r) 0)⁻¹ < 0 := inv_lt_zero.2 hneg
  have hy0 : 0 < y := by linarith
  have hgs := isSorted_stopWord (16 / κ) (c', 0, r)
  unfold jointWordOfRec at hyJ ⊢
  rw [fn_retWord hgs _ _ hyJ]
  have hz0 : -y⁻¹ < 0 := neg_neg_of_pos (inv_pos.2 hy0)
  have hzm : markPosL (rdrv r) (rtime r) 0 < -y⁻¹ := by
    have h1 : (-markPosL (rdrv r) (rtime r) 0)⁻¹ < y := by rw [inv_neg]; linarith
    have h2 : y⁻¹ < -markPosL (rdrv r) (rtime r) 0 := inv_lt_of_inv_lt₀ (neg_pos.2 hneg) h1
    linarith
  have hzJ : -y⁻¹ ∉ (stopWord (16 / κ) (c', 0, r)).jumps := fun h => hyJ (neg_inv_mem_jumps_retWord hgs _ _ h)
  unfold returnData liftBoundary
  rw [Supp8.GB6.stopWord_fn_flank_left c' 0 r hzm hz0 hzJ,
    ite_eq_right_of_eq_false _ _ (eq_false (not_lt.2 hy0.le)), retA_add_specOffset hκ]
  ring

end Root

/-! ### Every stage word keeps the far heights -/

section Stage

variable {S : Type*} {κ : ℝ}

/-- The initial record of a complete retained past. -/
def pastRoot : (n : ℕ) → GW2JDetR5.Past S n → S
  | 0 => fun x => x
  | n + 1 => fun x => pastRoot n x.1

/-- **Every stage word keeps the root word's far-left height.** -/
theorem farL_stageWord (hκ : 0 < κ) {W₀ : S → BoundaryWord} (θ : ℕ → ℝ) {A₀ : Set S} {h : ℝ}
    (h0 : ∀ x ∈ A₀, FarL (W₀ x) h) :
    ∀ n (x : GW2JDetR5.Past S n), pastRoot n x ∈ A₀ → FarL (GW2JDetR5.stageWord (κ := κ) W₀ θ n x) h
  | 0, x, hx => h0 x hx
  | n + 1, x, hx => farL_stopWord hκ (farL_stageWord hκ θ h0 n x.1 hx) (θ n) x.2

/-- **Every stage word keeps the root word's far-right height.** -/
theorem farR_stageWord (hκ : 0 < κ) {W₀ : S → BoundaryWord} (θ : ℕ → ℝ) {A₀ : Set S} {h : ℝ}
    (h0 : ∀ x ∈ A₀, FarR (W₀ x) h) :
    ∀ n (x : GW2JDetR5.Past S n), pastRoot n x ∈ A₀ → FarR (GW2JDetR5.stageWord (κ := κ) W₀ θ n x) h
  | 0, x, hx => h0 x hx
  | n + 1, x, hx => farR_stopWord hκ (farR_stageWord hκ θ h0 n x.1 hx) (θ n) x.2

end Stage

end InteractingSLE.Theorem14.GW2Wm
