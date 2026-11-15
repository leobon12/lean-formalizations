/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2JointKernelProof
import InteractingSLE.Spec.Supplement.GW1ActiveWord
import InteractingSLE.Spec.Supplement.GB6Law

/-!
# Proposition GB6, step (d): the conditional word in the chart of `U`

Packet PROVE-GB6-RESTART. Supplement §8.6, Proposition GB6 (`source/spec/p481-528.md` L929–L975, pp. 518–520), first
paragraph of the proof, and Astra's follow-up 3, Q3 §3.3 ("After the prescribed inversion the final sums are the two
GB6 sums on p. 518, both at least `c`. The surviving original sums are unchanged. These computations determine the
entire word, including its junctions").

The conditional field of GB6 is the field `h` read in the chart `ownComponentChart w s = R ∘ f_s` of the flow's own
target component (`R(z) = −1/z`), in the counterflow frame. Given the flow prefix, the field read in the flow's own
Loewner chart `f_s` is the GFF of the flow's **stop word** `stopWord κ (c, θ, r)` (PROVE-STAGEDLAW3), so the
conditional word in the chart of `U` is the stop word **returned** through `R` with the constant `πχ` and the lift
coefficient `χ` (`gb6WordOfRec`). This file proves the deterministic facts about that word that GB6's step (d) uses:

* `gb6WordOfRec`, `gb6Word`, `jLOfRec`, `jROfRec` (the junctions `−1/V̂^{0,R}`, `−1/V̂^{0,L}` read from the record
  through the stop word's seed positions), measurability and sortedness;
* the flank heights of the stop word (`stopWord_fn_flank_left`, `stopWord_fn_flank_right`: `−λ − θχ` and `λ − θχ`);
* **`isGB6TailData_gb6WordOfRec`**: the two protected tails (GB6: "the terminal counterflow side partial sums … Both
  are at least `c = k/2 − 2` for the stipulated angle range");
* `exists_stopWord_fn_eq_of_lt_seedL`, `exists_stopWord_fn_eq_of_gt_seedR`: beyond the seed positions the stop word
  only takes values of the launch word on the same side ("The surviving original sums are unchanged");
* **`isGB6AdmData_gb6WordOfRec`**: the conditional word is admissible as soon as the returned launch word is
  ("Consequently the entire conditional word is admissible").
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Finset
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (TestOn DistOn)

namespace InteractingSLE

namespace Supp8

namespace GB6

open Restart Exist.Staged Exist.StagedLaw Sec7.StripSysField Theorem14.GW2JointKernel Theorem14.GW1W

/-! ### The conditional word and the junctions read from the record -/

/-- **The word of GB6's conditional field in the chart of `U`**: the flow prefix's stop word returned through
`R(z) = −1/z` with the constant `πχ` and the lift coefficient `χ`. -/
def gb6WordOfRec (κ θ : ℝ) (c : BoundaryWord) (r : RecData) : BoundaryWord :=
  retWord (Real.pi * chiC κ) (chiC κ) (stopWord κ (c, θ, r))

/-- The conditional word of the flow driver `w` stopped at the own time `s`. -/
def gb6Word (κ θ : ℝ) (c : BoundaryWord) (s : ℝ≥0) (w : ℝ≥0 → ℝ) : BoundaryWord :=
  gb6WordOfRec κ θ c (recOf (s : ℝ≥0∞) (w, ⊤))

/-- The left junction read from a record: `−1/V̂^{0,R}`, the image of the right seed position. -/
def jLOfRec (r : RecData) : ℝ := -(markPos (rdrv r) (rtime r) 0)⁻¹

/-- The right junction read from a record: `−1/V̂^{0,L}`, the image of the left seed position. -/
def jROfRec (r : RecData) : ℝ := -(markPosL (rdrv r) (rtime r) 0)⁻¹

theorem measurable_gb6WordOfRec (κ θ : ℝ) (c : BoundaryWord) : Measurable (gb6WordOfRec κ θ c) :=
  (measurable_retWord _ _).comp ((measurable_stopWord κ).comp
    (measurable_const.prodMk (measurable_const.prodMk measurable_id)))

theorem isSorted_gb6WordOfRec (κ θ : ℝ) (c : BoundaryWord) (r : RecData) : (gb6WordOfRec κ θ c r).IsSorted :=
  isSorted_retWord (isSorted_stopWord _ _) _ _

theorem measurable_markPos_rec : Measurable fun r : RecData => markPos (rdrv r) (rtime r) 0 :=
  measurable_markPos continuous_rdrv measurable_rdrv_apply rdrv_zero measurable_rtime rtime_nonneg measurable_const

theorem measurable_markPosL_rec : Measurable fun r : RecData => markPosL (rdrv r) (rtime r) 0 :=
  measurable_markPosL continuous_rdrv measurable_rdrv_apply rdrv_zero measurable_rtime rtime_nonneg
    measurable_const

theorem measurable_jLOfRec : Measurable jLOfRec := measurable_markPos_rec.inv.neg

theorem measurable_jROfRec : Measurable jROfRec := measurable_markPosL_rec.inv.neg

/-! ### The seed positions of the stop word -/

theorem zero_lt_flowLineNL (b : ℝ → ℝ) (J : Finset ℝ) : 0 < flowLineNL b J 0 := by
  unfold flowLineNL; omega

theorem zero_lt_flowLineNR (b : ℝ → ℝ) (J : Finset ℝ) : 0 < flowLineNR b J 0 := by
  unfold flowLineNR; omega

/-- The left seed of the padded flow-line word is `0`. -/
theorem padFL_seedL (c : BoundaryWord) : (padFL 0 0 c.fn c.jumps).1.1 0 = 0 := by
  have h := padFL_fst_fst_fin c.fn c.jumps ⟨0, zero_lt_flowLineNL c.fn c.jumps⟩
  rw [h]
  exact Sec4.flowLineXL_zero c.fn c.jumps

/-- The right seed of the padded flow-line word is `0`. -/
theorem padFL_seedR (c : BoundaryWord) : (padFL 0 0 c.fn c.jumps).1.2 0 = 0 := by
  have h := padFL_fst_snd_fin c.fn c.jumps ⟨0, zero_lt_flowLineNR c.fn c.jumps⟩
  rw [h]
  exact Sec4.flowLineXR_zero c.fn c.jumps

/-! ### The flank heights of the stop word -/

section Flank

variable {κ : ℝ}

/-- **The left flank** (GB6: "An exposed own flow piece of angle `θ` has `h`-heights `−λ − θχ` … on its two sides"):
between the left seed position and `0` the stop word is `−λ − θχ`. -/
theorem stopWord_fn_flank_left (c : BoundaryWord) (θ : ℝ) (r : RecData) {z : ℝ}
    (hz : markPosL (rdrv r) (rtime r) 0 < z) (hz0 : z < 0) (hzJ : z ∉ (stopWord κ (c, θ, r)).jumps) :
    (stopWord κ (c, θ, r)).fn z = -sleLambda κ - θ * chiC κ := by
  have hmo := isMarkOrder_stopWord c r
  refine (fn_forceWord κ (padFL κ θ c.fn c.jumps).2.1 (padFL κ θ c.fn c.jumps).2.2 (θ * chiC κ) hmo hzJ
    hz0.ne).trans ?_
  rw [Sec4.forceBoundaryData_of_neg _ _ _ _ hz0]
  have hempty : (univ.filter fun i : Fin (flowLineNL c.fn c.jumps 0) =>
      z < markPosL (rdrv r) (rtime r) ((padFL 0 0 c.fn c.jumps).1.1 i)) = ∅ := by
    refine Finset.filter_eq_empty_iff.2 fun i _ => not_lt.2 ?_
    have h1 := hmo.1 0 i (Nat.zero_le _) i.2
    beta_reduce at h1
    rw [padFL_seedL] at h1
    exact h1.trans hz.le
  rw [hempty, Finset.sum_empty]
  ring

/-- **The right flank**: between `0` and the right seed position the stop word is `λ − θχ`. -/
theorem stopWord_fn_flank_right (c : BoundaryWord) (θ : ℝ) (r : RecData) {z : ℝ} (hz0 : 0 < z)
    (hz : z < markPos (rdrv r) (rtime r) 0) (hzJ : z ∉ (stopWord κ (c, θ, r)).jumps) :
    (stopWord κ (c, θ, r)).fn z = sleLambda κ - θ * chiC κ := by
  have hmo := isMarkOrder_stopWord c r
  refine (fn_forceWord κ (padFL κ θ c.fn c.jumps).2.1 (padFL κ θ c.fn c.jumps).2.2 (θ * chiC κ) hmo hzJ
    hz0.ne').trans ?_
  rw [Sec4.forceBoundaryData_of_nonneg _ _ _ _ hz0.le]
  have hempty : (univ.filter fun j : Fin (flowLineNR c.fn c.jumps 0) =>
      markPos (rdrv r) (rtime r) ((padFL 0 0 c.fn c.jumps).1.2 j) ≤ z) = ∅ := by
    refine Finset.filter_eq_empty_iff.2 fun j _ => not_le.2 ?_
    have h1 := hmo.2.2.1 0 j (Nat.zero_le _) j.2
    beta_reduce at h1
    rw [padFL_seedR] at h1
    exact hz.trans_le h1
  rw [hempty, Finset.sum_empty]
  ring

end Flank

/-! ### The protected tails -/

section Tails

variable {κ : ℝ}

/-- Beyond the right junction `−1/p` (`p < 0`), the inverted point lies between `p` and `0`. -/
theorem negInv_mem_of_gt {p y : ℝ} (hp : p < 0) (hy : -p⁻¹ < y) : p < -y⁻¹ ∧ -y⁻¹ < 0 := by
  have hp' : 0 < -p := neg_pos.2 hp
  have hy0 : 0 < y := lt_trans (by rw [← inv_neg]; exact inv_pos.2 hp') hy
  have h1 : (-p)⁻¹ < y := by rwa [inv_neg]
  have h2 : y⁻¹ < -p := inv_lt_of_inv_lt₀ hp' h1
  exact ⟨by linarith, neg_neg_of_pos (inv_pos.2 hy0)⟩

/-- Beyond the left junction `−1/p` (`p > 0`), the inverted point lies between `0` and `p`. -/
theorem negInv_mem_of_lt {p y : ℝ} (hp : 0 < p) (hy : y < -p⁻¹) : 0 < -y⁻¹ ∧ -y⁻¹ < p := by
  have hy0 : y < 0 := lt_trans hy (neg_neg_of_pos (inv_pos.2 hp))
  have h1 : p⁻¹ < -y := by linarith
  have h2 : (-y)⁻¹ < p := inv_lt_of_inv_lt₀ hp h1
  rw [inv_neg] at h2
  exact ⟨neg_pos.2 (inv_lt_zero.2 hy0), h2⟩

theorem liftBoundary_of_pos {x : ℝ} (hx : 0 < x) : liftBoundary x = 0 := by
  simp only [liftBoundary, not_lt.2 hx.le, ↓reduceIte]

theorem liftBoundary_of_neg {x : ℝ} (hx : x < 0) : liftBoundary x = -(2 * Real.pi) := by
  simp only [liftBoundary, hx, ↓reduceIte]

/-- The conditional word at a positive non-jump point: `−g(−1/y) + πχ` (`g` the stop word). -/
theorem gb6WordOfRec_fn_of_pos (θ : ℝ) (c : BoundaryWord) (r : RecData) {y : ℝ} (hy : 0 < y)
    (hyJ : y ∉ (gb6WordOfRec κ θ c r).jumps) :
    (gb6WordOfRec κ θ c r).fn y = -(stopWord κ (c, θ, r)).fn (-y⁻¹) + Real.pi * chiC κ := by
  rw [gb6WordOfRec, fn_retWord (isSorted_stopWord _ _) _ _ hyJ, returnData, liftBoundary_of_pos hy]
  ring

/-- The conditional word at a negative non-jump point: `−g(−1/y) − πχ`. -/
theorem gb6WordOfRec_fn_of_neg (θ : ℝ) (c : BoundaryWord) (r : RecData) {y : ℝ} (hy : y < 0)
    (hyJ : y ∉ (gb6WordOfRec κ θ c r).jumps) :
    (gb6WordOfRec κ θ c r).fn y = -(stopWord κ (c, θ, r)).fn (-y⁻¹) - Real.pi * chiC κ := by
  rw [gb6WordOfRec, fn_retWord (isSorted_stopWord _ _) _ _ hyJ, returnData, liftBoundary_of_neg hy]
  ring

/-- A non-jump of the conditional word inverts to a non-jump of the stop word. -/
theorem negInv_notMem_stopWord_jumps (θ : ℝ) (c : BoundaryWord) (r : RecData) {y : ℝ}
    (hyJ : y ∉ (gb6WordOfRec κ θ c r).jumps) : -y⁻¹ ∉ (stopWord κ (c, θ, r)).jumps := by
  have hJ := jumps_retWord (isSorted_stopWord κ (c, θ, r)) (Real.pi * chiC κ) (chiC κ)
  rw [gb6WordOfRec, hJ] at hyJ
  exact negInv_notMem_of_notMem_returnExcept hyJ

/-- **The two protected tails of the conditional word** (GB6, proof: the terminal counterflow side partial sums on
the flow sides are `S_R`, `S_L`, "Both are at least `c = k/2 − 2` for the stipulated angle range"), at every record
whose seed positions are nondegenerate. -/
theorem isGB6TailData_gb6WordOfRec (hκ : 0 < κ) (hκ4 : κ < 4) {θ : ℝ} (hθ₁ : -(Real.pi / 2) ≤ θ)
    (hθ₂ : θ ≤ Real.pi / 2) (c : BoundaryWord) (r : RecData) (hR : 0 < markPos (rdrv r) (rtime r) 0)
    (hL : markPosL (rdrv r) (rtime r) 0 < 0) :
    IsGB6TailData κ (gb6WordOfRec κ θ c r) (jLOfRec r) (jROfRec r) := by
  have hΛ := bigLambda_pos hκ
  have hjR : 0 < jROfRec r := by unfold jROfRec; rw [← inv_neg]; exact inv_pos.2 (neg_pos.2 hL)
  refine ⟨neg_neg_of_pos (inv_pos.2 hR), hjR, fun y hy hyJ => ?_, fun y hy hyJ => ?_⟩
  · obtain ⟨h1, h2⟩ := negInv_mem_of_gt hL hy
    have hy0 : 0 < y := lt_trans hjR hy
    rw [gb6WordOfRec_fn_of_pos θ c r hy0 hyJ,
      stopWord_fn_flank_left c θ r h1 h2 (negInv_notMem_stopWord_jumps θ c r hyJ)]
    have hv := rightValue_eq hκ θ
    rw [chiC_sixteen_div hκ] at hv
    have hS := protLevel_le_sumR hκ hκ4 hθ₁
    unfold tailLevel
    have : bigLambda κ * (protLevel κ + 1) ≤ bigLambda κ * (1 + sumR κ θ) := by nlinarith
    linarith
  · obtain ⟨h1, h2⟩ := negInv_mem_of_lt hR hy
    have hy0 : y < 0 := lt_trans hy (neg_neg_of_pos (inv_pos.2 hR))
    rw [gb6WordOfRec_fn_of_neg θ c r hy0 hyJ,
      stopWord_fn_flank_right c θ r h1 h2 (negInv_notMem_stopWord_jumps θ c r hyJ)]
    have hv := leftValue_eq hκ θ
    have hS := protLevel_le_sumL hκ hκ4 hθ₂
    unfold tailLevel
    have : bigLambda κ * (protLevel κ + 1) ≤ bigLambda κ * (1 + sumL κ θ) := by nlinarith
    linarith

end Tails

/-! ### Beyond the seed positions: values of the launch word -/

section Values

variable {κ : ℝ}

/-- **Left of the left seed position the stop word takes a value of the launch word left of `0`** ("The surviving
original sums are unchanged"): the left marks right of the point form a prefix of the flow-line word, and an original
point with the same prefix carries the same height (the angle shift cancels in the seed weight). -/
theorem exists_stopWord_fn_eq_of_lt_seedL (hκ : 0 < κ) (c : BoundaryWord) (θ : ℝ) (r : RecData) (E : Finset ℝ)
    {z : ℝ} (hz : z < markPosL (rdrv r) (rtime r) 0) (hzJ : z ∉ (stopWord κ (c, θ, r)).jumps) :
    ∃ u, u < 0 ∧ u ∉ E ∧ u ∉ c.jumps ∧ (stopWord κ (c, θ, r)).fn z = c.fn u := by
  classical
  have hmo := isMarkOrder_stopWord c r
  have hord := Theorem15.isOrderedForceWord_flowLine c.fn c.jumps 0
  have hz0 : z < 0 := hz.trans_le (markPosL_nonpos (continuous_rdrv r) (rdrv_zero r) (rtime_nonneg r) le_rfl)
  set nL := flowLineNL c.fn c.jumps 0 with hnL
  set xL := flowLineXL c.fn c.jumps 0 with hxL
  have hpad : ∀ i : Fin nL, (padFL 0 0 c.fn c.jumps).1.1 i = xL i := padFL_fst_fst_fin c.fn c.jumps
  set F : Finset (Fin nL) := univ.filter fun i => z < markPosL (rdrv r) (rtime r) (xL i) with hF
  have hfilt : (univ.filter fun i : Fin nL => z < markPosL (rdrv r) (rtime r) ((padFL 0 0 c.fn c.jumps).1.1 i)) =
      F := Finset.filter_congr fun i _ => by rw [hpad i]
  have hval : (stopWord κ (c, θ, r)).fn z =
      -sleLambda κ * (1 + ∑ i ∈ F, flowLineRhoL κ c.fn c.jumps 0 θ i) - θ * chiC κ := by
    refine (fn_forceWord κ _ _ _ hmo hzJ hz0.ne).trans ?_
    rw [Sec4.forceBoundaryData_of_neg _ _ _ _ hz0, hfilt,
      Finset.sum_congr rfl fun i _ => padFL_snd_fst_fin κ θ c.fn c.jumps i]
  have h0F : (⟨0, zero_lt_flowLineNL _ _⟩ : Fin nL) ∈ F := by
    rw [hF, Finset.mem_filter]
    refine ⟨mem_univ _, ?_⟩
    have h := padFL_seedL c
    rw [show (0 : ℕ) = ((⟨0, zero_lt_flowLineNL c.fn c.jumps⟩ : Fin nL) : ℕ) from rfl, hpad] at h
    rw [h]
    exact hz
  have hdown : ∀ i j : Fin nL, j ≤ i → i ∈ F → j ∈ F := by
    intro i j hji hi
    rw [hF, Finset.mem_filter] at hi ⊢
    have h1 := hmo.1 j i hji i.2
    beta_reduce at h1
    rw [hpad i, hpad j] at h1
    exact ⟨mem_univ _, hi.2.trans_le h1⟩
  have hsep : ∀ i ∈ F, ∀ j ∉ F, xL j < xL i := by
    intro i hi j hj
    have hij : i < j := by
      by_contra h
      exact hj (hdown i j (not_lt.1 h) hi)
    rcases (hord.1 hij.le).lt_or_eq with h | h
    · exact h
    · exfalso
      apply hj
      rw [hF, Finset.mem_filter] at hi ⊢
      exact ⟨mem_univ _, by rw [h]; exact hi.2⟩
  have hFne : (F.image xL).Nonempty := ⟨_, Finset.mem_image_of_mem xL h0F⟩
  set a := (F.image xL).min' hFne with ha
  have hb : ∃ b, b < a ∧ ∀ j ∉ F, xL j ≤ b := by
    by_cases hG : (univ.filter fun j => j ∉ F).Nonempty
    · refine ⟨((univ.filter fun j => j ∉ F).image xL).max' (hG.image _), ?_, fun j hj => ?_⟩
      · obtain ⟨j, hj, hjb⟩ := Finset.mem_image.1 (Finset.max'_mem _ (hG.image xL))
        obtain ⟨i, hi, hia⟩ := Finset.mem_image.1 (Finset.min'_mem _ hFne)
        rw [← hjb, ha, ← hia]
        exact hsep i hi j (Finset.mem_filter.1 hj).2
      · exact Finset.le_max' _ _ (Finset.mem_image_of_mem xL (Finset.mem_filter.2 ⟨mem_univ _, hj⟩))
    · exact ⟨a - 1, by linarith, fun j hj => absurd ⟨j, Finset.mem_filter.2 ⟨mem_univ _, hj⟩⟩ hG⟩
  obtain ⟨b, hba, hbF⟩ := hb
  obtain ⟨u, hbu, hua, huE⟩ := Sec4.exists_mem_Ioo_not_mem (insert 0 (E ∪ c.jumps)) hba
  have ha0 : a ≤ 0 := by
    have h := Finset.min'_le (F.image xL) _ (Finset.mem_image_of_mem xL h0F)
    rw [← ha] at h
    exact h.trans_eq (Sec4.flowLineXL_zero c.fn c.jumps)
  have hu0 : u < 0 := hua.trans_le ha0
  have huJ : u ∉ c.jumps := fun h => huE (Finset.mem_insert_of_mem (Finset.mem_union_right _ h))
  have hG : (univ.filter fun i : Fin nL => u < xL i) = F := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      by_contra hi
      exact absurd (hbF i hi) (not_le.2 (hbu.trans h))
    · intro hi
      exact hua.trans_le (Finset.min'_le _ _ (Finset.mem_image_of_mem xL hi))
  refine ⟨u, hu0, fun h => huE (Finset.mem_insert_of_mem (Finset.mem_union_left _ h)), huJ, ?_⟩
  have hfb := Exist.forceBoundaryData_flowLine_seed hκ c.isPiecewiseConstantBoundaryData 0 θ (y := u) hu0.ne
    (by rw [add_zero]; exact huJ)
  rw [Sec4.forceBoundaryData_of_neg _ _ _ _ hu0, hG, add_zero] at hfb
  rw [hval]
  linarith

/-- **Right of the right seed position the stop word takes a value of the launch word right of `0`** (the mirror
of `exists_stopWord_fn_eq_of_lt_seedL`). -/
theorem exists_stopWord_fn_eq_of_gt_seedR (hκ : 0 < κ) (c : BoundaryWord) (θ : ℝ) (r : RecData) (E : Finset ℝ)
    {z : ℝ} (hz : markPos (rdrv r) (rtime r) 0 < z) (hzJ : z ∉ (stopWord κ (c, θ, r)).jumps) :
    ∃ u, 0 < u ∧ u ∉ E ∧ u ∉ c.jumps ∧ (stopWord κ (c, θ, r)).fn z = c.fn u := by
  classical
  have hmo := isMarkOrder_stopWord c r
  have hord := Theorem15.isOrderedForceWord_flowLine c.fn c.jumps 0
  have hz0 : 0 < z := (markPos_nonneg (continuous_rdrv r) (rdrv_zero r) (rtime_nonneg r) le_rfl).trans_lt hz
  set nR := flowLineNR c.fn c.jumps 0 with hnR
  set xR := flowLineXR c.fn c.jumps 0 with hxR
  have hpad : ∀ j : Fin nR, (padFL 0 0 c.fn c.jumps).1.2 j = xR j := padFL_fst_snd_fin c.fn c.jumps
  set F : Finset (Fin nR) := univ.filter fun j => markPos (rdrv r) (rtime r) (xR j) ≤ z with hF
  have hfilt : (univ.filter fun j : Fin nR => markPos (rdrv r) (rtime r) ((padFL 0 0 c.fn c.jumps).1.2 j) ≤ z) =
      F := Finset.filter_congr fun j _ => by rw [hpad j]
  have hval : (stopWord κ (c, θ, r)).fn z =
      sleLambda κ * (1 + ∑ j ∈ F, flowLineRhoR κ c.fn c.jumps 0 θ j) - θ * chiC κ := by
    refine (fn_forceWord κ _ _ _ hmo hzJ hz0.ne').trans ?_
    rw [Sec4.forceBoundaryData_of_nonneg _ _ _ _ hz0.le, hfilt,
      Finset.sum_congr rfl fun j _ => padFL_snd_snd_fin κ θ c.fn c.jumps j]
  have h0F : (⟨0, zero_lt_flowLineNR _ _⟩ : Fin nR) ∈ F := by
    rw [hF, Finset.mem_filter]
    refine ⟨mem_univ _, ?_⟩
    have h := padFL_seedR c
    rw [show (0 : ℕ) = ((⟨0, zero_lt_flowLineNR c.fn c.jumps⟩ : Fin nR) : ℕ) from rfl, hpad] at h
    rw [h]
    exact hz.le
  have hdown : ∀ i j : Fin nR, j ≤ i → i ∈ F → j ∈ F := by
    intro i j hji hi
    rw [hF, Finset.mem_filter] at hi ⊢
    have h1 := hmo.2.2.1 j i hji i.2
    beta_reduce at h1
    rw [hpad i, hpad j] at h1
    exact ⟨mem_univ _, h1.trans hi.2⟩
  have hsep : ∀ i ∈ F, ∀ j ∉ F, xR i < xR j := by
    intro i hi j hj
    have hij : i < j := by
      by_contra h
      exact hj (hdown i j (not_lt.1 h) hi)
    rcases (hord.2.2.1 hij.le).lt_or_eq with h | h
    · exact h
    · exfalso
      apply hj
      rw [hF, Finset.mem_filter] at hi ⊢
      exact ⟨mem_univ _, by rw [← h]; exact hi.2⟩
  have hFne : (F.image xR).Nonempty := ⟨_, Finset.mem_image_of_mem xR h0F⟩
  set a := (F.image xR).max' hFne with ha
  have hb : ∃ b, a < b ∧ ∀ j ∉ F, b ≤ xR j := by
    by_cases hG : (univ.filter fun j => j ∉ F).Nonempty
    · refine ⟨((univ.filter fun j => j ∉ F).image xR).min' (hG.image _), ?_, fun j hj => ?_⟩
      · obtain ⟨j, hj, hjb⟩ := Finset.mem_image.1 (Finset.min'_mem _ (hG.image xR))
        obtain ⟨i, hi, hia⟩ := Finset.mem_image.1 (Finset.max'_mem _ hFne)
        rw [← hjb, ha, ← hia]
        exact hsep i hi j (Finset.mem_filter.1 hj).2
      · exact Finset.min'_le _ _ (Finset.mem_image_of_mem xR (Finset.mem_filter.2 ⟨mem_univ _, hj⟩))
    · exact ⟨a + 1, by linarith, fun j hj => absurd ⟨j, Finset.mem_filter.2 ⟨mem_univ _, hj⟩⟩ hG⟩
  obtain ⟨b, hab, hbF⟩ := hb
  obtain ⟨u, hau, hub, huE⟩ := Sec4.exists_mem_Ioo_not_mem (insert 0 (E ∪ c.jumps)) hab
  have ha0 : 0 ≤ a := by
    have h := Finset.le_max' (F.image xR) _ (Finset.mem_image_of_mem xR h0F)
    rw [← ha] at h
    exact (Sec4.flowLineXR_zero c.fn c.jumps).symm.trans_le h
  have hu0 : 0 < u := ha0.trans_lt hau
  have huJ : u ∉ c.jumps := fun h => huE (Finset.mem_insert_of_mem (Finset.mem_union_right _ h))
  have hG : (univ.filter fun j : Fin nR => xR j ≤ u) = F := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      by_contra hj
      exact absurd (hbF j hj) (not_le.2 (h.trans_lt hub))
    · intro hj
      exact (Finset.le_max' _ _ (Finset.mem_image_of_mem xR hj)).trans hau.le
  refine ⟨u, hu0, fun h => huE (Finset.mem_insert_of_mem (Finset.mem_union_left _ h)), huJ, ?_⟩
  have hfb := Exist.forceBoundaryData_flowLine_seed hκ c.isPiecewiseConstantBoundaryData 0 θ (y := u) hu0.ne'
    (by rw [add_zero]; exact huJ)
  rw [Sec4.forceBoundaryData_of_nonneg _ _ _ _ hu0.le, hG, add_zero] at hfb
  rw [hval]
  linarith

end Values

/-! ### Admissibility of the conditional word -/

section Adm

variable {κ : ℝ}

/-- The left seed position is a jump of the stop word. -/
theorem seedL_mem_stopWord_jumps (c : BoundaryWord) (θ : ℝ) (r : RecData) :
    markPosL (rdrv r) (rtime r) 0 ∈ (stopWord κ (c, θ, r)).jumps := by
  have hmo := isMarkOrder_stopWord c r
  have hn := zero_lt_flowLineNL c.fn c.jumps
  refine BoundaryWord.mem_jumps.2 ⟨flowLineNL c.fn c.jumps 0 - 1, ?_, ?_⟩
  · change _ < flowLineNL c.fn c.jumps 0 + 1 + flowLineNR c.fn c.jumps 0
    omega
  · change cumMax (rawPos _ _ _) _ = _
    rw [cumMax_rawPos hmo (by omega)]
    simp only [rawPos, show flowLineNL c.fn c.jumps 0 - 1 < flowLineNL c.fn c.jumps 0 by omega, ↓reduceIte,
      show flowLineNL c.fn c.jumps 0 - 1 - (flowLineNL c.fn c.jumps 0 - 1) = 0 by omega]
    rw [padFL_seedL]

/-- The right seed position is a jump of the stop word. -/
theorem seedR_mem_stopWord_jumps (c : BoundaryWord) (θ : ℝ) (r : RecData) :
    markPos (rdrv r) (rtime r) 0 ∈ (stopWord κ (c, θ, r)).jumps := by
  have hmo := isMarkOrder_stopWord c r
  have hn := zero_lt_flowLineNR c.fn c.jumps
  refine BoundaryWord.mem_jumps.2 ⟨flowLineNL c.fn c.jumps 0 + 1, ?_, ?_⟩
  · change _ < flowLineNL c.fn c.jumps 0 + 1 + flowLineNR c.fn c.jumps 0
    omega
  · change cumMax (rawPos _ _ _) _ = _
    rw [cumMax_rawPos hmo (by omega)]
    simp only [rawPos, show ¬ flowLineNL c.fn c.jumps 0 + 1 < flowLineNL c.fn c.jumps 0 by omega, ↓reduceIte,
      show flowLineNL c.fn c.jumps 0 + 1 ≠ flowLineNL c.fn c.jumps 0 by omega,
      show flowLineNL c.fn c.jumps 0 + 1 - flowLineNL c.fn c.jumps 0 - 1 = 0 by omega]
    rw [padFL_seedR]

theorem negInv_lt_of_lt_negInv {p y : ℝ} (hp : p < 0) (hy0 : 0 < y) (hy : y < -p⁻¹) : -y⁻¹ < p := by
  have hp' : 0 < -p := neg_pos.2 hp
  rw [← inv_neg] at hy
  have h := (lt_inv_comm₀ hy0 hp').1 hy
  linarith

theorem lt_negInv_of_negInv_lt {p y : ℝ} (hp : 0 < p) (hy0 : y < 0) (hy : -p⁻¹ < y) : p < -y⁻¹ := by
  have hy' : 0 < -y := neg_pos.2 hy0
  have h := (lt_inv_comm₀ hy' hp).1 (by linarith)
  rwa [inv_neg] at h

/-- **The conditional word is admissible** (GB6, proof: "Consequently the entire conditional word is admissible"):
its flow-side tails are protected (`isGB6TailData_gb6WordOfRec`), and on the original real line, between the two
junctions, it takes the values `−g + πχ` (right of `0`) and `−g − πχ` (left of `0`) of the launch word `g` on the
opposite side, which are admissible for the counterflow as soon as the hypotheses `hcL`, `hcR` hold (they are the
data form of the original counterflow word's admissibility; a finite exceptional set `E` is allowed). -/
theorem isGB6AdmData_gb6WordOfRec (hκ : 0 < κ) (hκ4 : κ < 4) {θ : ℝ} (hθ₁ : -(Real.pi / 2) ≤ θ)
    (hθ₂ : θ ≤ Real.pi / 2) (c : BoundaryWord) (r : RecData) (hR : 0 < markPos (rdrv r) (rtime r) 0)
    (hL : markPosL (rdrv r) (rtime r) 0 < 0) (E : Finset ℝ)
    (hcL : ∀ u, u < 0 → u ∉ E → u ∉ c.jumps → -bigLambda κ < -c.fn u + Real.pi * chiC κ)
    (hcR : ∀ u, 0 < u → u ∉ E → u ∉ c.jumps → -c.fn u - Real.pi * chiC κ < bigLambda κ) :
    IsGB6AdmData κ (gb6WordOfRec κ θ c r) := by
  have hT := isGB6TailData_gb6WordOfRec hκ hκ4 hθ₁ hθ₂ c r hR hL
  have hΛ := bigLambda_pos hκ
  have hc := neg_two_lt_protLevel hκ hκ4
  have htl : -bigLambda κ < tailLevel κ := by unfold tailLevel; nlinarith
  have hJ := jumps_retWord (isSorted_stopWord κ (c, θ, r)) (Real.pi * chiC κ) (chiC κ)
  refine ⟨fun y hy hyJ => ?_, fun y hy hyJ => ?_⟩
  · rcases lt_trichotomy y (jROfRec r) with h | h | h
    · have hz : -y⁻¹ < markPosL (rdrv r) (rtime r) 0 := negInv_lt_of_lt_negInv hL hy h
      obtain ⟨u, hu0, huE, huJ, he⟩ :=
        exists_stopWord_fn_eq_of_lt_seedL hκ c θ r E hz (negInv_notMem_stopWord_jumps θ c r hyJ)
      rw [gb6WordOfRec_fn_of_pos θ c r hy hyJ, he]
      exact hcL u hu0 huE huJ
    · exfalso
      apply hyJ
      rw [gb6WordOfRec, hJ, h, jROfRec]
      exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (seedL_mem_stopWord_jumps c θ r))
    · exact htl.trans_le (hT.2.2.1 y h hyJ)
  · rcases lt_trichotomy y (jLOfRec r) with h | h | h
    · exact (hT.2.2.2 y h hyJ).trans_lt (by linarith)
    · exfalso
      apply hyJ
      rw [gb6WordOfRec, hJ, h, jLOfRec]
      exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (seedR_mem_stopWord_jumps c θ r))
    · have hz : markPos (rdrv r) (rtime r) 0 < -y⁻¹ := lt_negInv_of_negInv_lt hR hy h
      obtain ⟨u, hu0, huE, huJ, he⟩ :=
        exists_stopWord_fn_eq_of_gt_seedR hκ c θ r E hz (negInv_notMem_stopWord_jumps θ c r hyJ)
      rw [gb6WordOfRec_fn_of_neg θ c r hy hyJ, he]
      exact hcR u hu0 huE huJ

end Adm

end GB6

end Supp8

end InteractingSLE
