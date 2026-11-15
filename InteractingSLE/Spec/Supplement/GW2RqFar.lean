/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RqShell
import InteractingSLE.Spec.Sec7.StripDet
import InteractingSLE.Spec.Supplement.GW2RdShift

/-!
# The far block of the region pair is bounded (decision D33)

PROVE-GW2-ROOTX round 8. A word with two ANGLE REGIONS `(aL, 0)` and `(0, aR)`, in which every height reads a
separated angle and heights of equal rank on the two sides read the same angle, has a valid pair of block sizes whose
far block is bounded by the heights and the number of jumps beyond the regions only:

* `rkR c u`, `rkL c v`: the number of genuine jumps in `(0, u)`, resp. `(v, 0)`; `rkR_eq`, `rkL_eq`: the rank of a
  point between consecutive labels is the label's index;
* `pRc β aR`, `pLc β aL`: the numbers of labels inside the regions; `xR_lt_iff`, `xL_gt_iff`;
* `phiR_succ_eq`, `phiL_succ_eq`: the angle read from the weights up to a label is the angle of the height right
  after it (`φ0 + (λ − h)/χ` on the right, `φ0 − (λ + h)/χ` on the left);
* **`RegionFact κ β φ0 aL aR Hm N`**: the regions are nonempty, heights there read separated angles, heights of
  equal rank pair (`h_R − h_L = 2λ`), all heights are bounded by `Hm`, at most `N` jumps beyond each region;
* **`valid_region`**: the region pair `(pRc − 1, pLc)` is valid; **`farD_region_le`**: its far weight is at most
  `4 (N + 1) Hm / λ`;
* **`optShell_of_region`**: the optimal shell presents the word, has separated angles, and its drift is at most
  `driftC κ Hm N = 8M/3 + 4/3 · 4 (N + 1) Hm / λ`.

Deterministic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Finset
open scoped NNReal
open QuantumZipper (chiC)

namespace InteractingSLE.Theorem14.GW2Rq

open Restart GW2Sde GW2Sdf GW2Sdy GW2TipSystem GW2TipSystem.RootL6 Sec5 GW2Rs
open PiecewiseConstantBoundaryData (jumpSet leftLim rightLim)

variable (κ : ℝ) (β : BoundaryWord) (φ0 : ℝ)

/-! ### Ranks -/

/-- The right rank of `u`: the number of genuine jumps in `(0, u)`. -/
def rkR (c : BoundaryWord) (u : ℝ) : ℕ := ((jumpSet c.fn c.jumps).filter fun y => 0 < y ∧ y < u).card

/-- The left rank of `v`: the number of genuine jumps in `(v, 0)`. -/
def rkL (c : BoundaryWord) (v : ℝ) : ℕ := ((jumpSet c.fn c.jumps).filter fun y => v < y ∧ y < 0).card

/-- The number of right labels left of `aR`. -/
def pRc (aR : ℝ) : ℕ :=
  (univ.filter fun j : Fin (flowLineNR β.fn β.jumps 0) => flowLineXR β.fn β.jumps 0 j < aR).card

/-- The number of left labels right of `aL`. -/
def pLc (aL : ℝ) : ℕ :=
  (univ.filter fun i : Fin (flowLineNL β.fn β.jumps 0) => aL < flowLineXL β.fn β.jumps 0 i).card

/-- A downward closed set of `Fin n` is an initial segment. -/
theorem mem_iff_lt_card {n : ℕ} {S : Finset (Fin n)} (hS : ∀ j ∈ S, ∀ k ≤ j, k ∈ S) (j : Fin n) :
    j ∈ S ↔ (j : ℕ) < S.card := by
  constructor
  · intro hj
    have h : Finset.Iic j ⊆ S := fun k hk => hS j hj k (Finset.mem_Iic.1 hk)
    have := Finset.card_le_card h
    rw [Fin.card_Iic] at this
    omega
  · intro hj
    by_contra hn
    have h : S ⊆ Finset.Iio j := fun k hk => by
      rw [Finset.mem_Iio]
      by_contra hk'
      exact hn (hS k hk j (not_lt.1 hk'))
    have := Finset.card_le_card h
    rw [Fin.card_Iio] at this
    omega

theorem xR_lt_iff (aR : ℝ) (j : Fin (flowLineNR β.fn β.jumps 0)) :
    flowLineXR β.fn β.jumps 0 j < aR ↔ (j : ℕ) < pRc β aR := by
  have h := mem_iff_lt_card (S := univ.filter fun j : Fin (flowLineNR β.fn β.jumps 0) =>
    flowLineXR β.fn β.jumps 0 j < aR) (fun j hj k hk => by
      rw [Finset.mem_filter] at hj ⊢
      exact ⟨Finset.mem_univ _, ((Sec7.StripDet.strictMono_flowLineXR β.fn β.jumps).monotone hk).trans_lt hj.2⟩) j
  unfold pRc
  rw [Finset.mem_filter] at h
  simpa only [Finset.mem_univ, true_and] using h

theorem xL_gt_iff (aL : ℝ) (i : Fin (flowLineNL β.fn β.jumps 0)) :
    aL < flowLineXL β.fn β.jumps 0 i ↔ (i : ℕ) < pLc β aL := by
  have h := mem_iff_lt_card (S := univ.filter fun i : Fin (flowLineNL β.fn β.jumps 0) =>
    aL < flowLineXL β.fn β.jumps 0 i) (fun j hj k hk => by
      rw [Finset.mem_filter] at hj ⊢
      exact ⟨Finset.mem_univ _, hj.2.trans_le ((Sec7.StripDet.strictAnti_flowLineXL β.fn β.jumps).antitone hk)⟩) i
  unfold pLc
  rw [Finset.mem_filter] at h
  simpa only [Finset.mem_univ, true_and] using h

theorem pRc_le (aR : ℝ) : pRc β aR ≤ flowLineNR β.fn β.jumps 0 :=
  (Finset.card_filter_le _ _).trans (by rw [Finset.card_univ, Fintype.card_fin])

theorem pLc_le (aL : ℝ) : pLc β aL ≤ flowLineNL β.fn β.jumps 0 :=
  (Finset.card_filter_le _ _).trans (by rw [Finset.card_univ, Fintype.card_fin])

/-! ### Labels are the genuine jumps -/

theorem xR_zero : flowLineXR β.fn β.jumps 0 ⟨0, Supp8.GB6.zero_lt_flowLineNR _ _⟩ = 0 := rfl

theorem xL_zero : flowLineXL β.fn β.jumps 0 ⟨0, by unfold flowLineNL; omega⟩ = 0 := rfl

theorem xR_pos {j : Fin (flowLineNR β.fn β.jumps 0)} (hj : (j : ℕ) ≠ 0) : 0 < flowLineXR β.fn β.jumps 0 j := by
  have h0 : (⟨0, Supp8.GB6.zero_lt_flowLineNR _ _⟩ : Fin (flowLineNR β.fn β.jumps 0)) < j :=
    Fin.lt_def.2 (Nat.pos_of_ne_zero hj)
  have := Sec7.StripDet.strictMono_flowLineXR β.fn β.jumps h0
  rwa [xR_zero] at this

theorem xL_neg {i : Fin (flowLineNL β.fn β.jumps 0)} (hi : (i : ℕ) ≠ 0) : flowLineXL β.fn β.jumps 0 i < 0 := by
  have h0 : (⟨0, by unfold flowLineNL; omega⟩ : Fin (flowLineNL β.fn β.jumps 0)) < i :=
    Fin.lt_def.2 (Nat.pos_of_ne_zero hi)
  have := Sec7.StripDet.strictAnti_flowLineXL β.fn β.jumps h0
  rwa [xL_zero] at this

theorem xR_mem_jumpSet {j : Fin (flowLineNR β.fn β.jumps 0)} (hj : (j : ℕ) ≠ 0) :
    flowLineXR β.fn β.jumps 0 j ∈ jumpSet β.fn β.jumps := by
  obtain ⟨j, hj'⟩ := j
  rcases j with _ | k
  · exact absurd rfl hj
  · set s := (jumpSet β.fn β.jumps).filter ((0 : ℝ) < ·) with hs
    have hk : k < s.card := by
      have e : flowLineNR β.fn β.jumps 0 = s.card + 1 := rfl
      omega
    have e : flowLineXR β.fn β.jumps 0 ⟨k + 1, hj'⟩ = s.orderEmbOfFin rfl ⟨k, hk⟩ - 0 := rfl
    rw [e, sub_zero]
    exact (Finset.mem_filter.1 (s.orderEmbOfFin_mem rfl _)).1

theorem xL_mem_jumpSet {i : Fin (flowLineNL β.fn β.jumps 0)} (hi : (i : ℕ) ≠ 0) :
    flowLineXL β.fn β.jumps 0 i ∈ jumpSet β.fn β.jumps := by
  obtain ⟨i, hi'⟩ := i
  rcases i with _ | k
  · exact absurd rfl hi
  · set s := (jumpSet β.fn β.jumps).filter (· < (0 : ℝ)) with hs
    have hk : k < s.card := by
      have e : flowLineNL β.fn β.jumps 0 = s.card + 1 := rfl
      omega
    have e : flowLineXL β.fn β.jumps 0 ⟨k + 1, hi'⟩ = s.orderEmbOfFin rfl (Fin.rev ⟨k, hk⟩) - 0 := rfl
    rw [e, sub_zero]
    exact (Finset.mem_filter.1 (s.orderEmbOfFin_mem rfl _)).1

theorem exists_xR_eq {t : ℝ} (ht : t ∈ jumpSet β.fn β.jumps) (ht0 : 0 < t) :
    ∃ j : Fin (flowLineNR β.fn β.jumps 0), (j : ℕ) ≠ 0 ∧ flowLineXR β.fn β.jumps 0 j = t := by
  set s := (jumpSet β.fn β.jumps).filter ((0 : ℝ) < ·) with hs
  have hts : t ∈ (s : Set ℝ) := Finset.mem_filter.2 ⟨ht, ht0⟩
  rw [← Finset.range_orderEmbOfFin s rfl] at hts
  obtain ⟨k, hk⟩ := hts
  have hlt : (k : ℕ) + 1 < flowLineNR β.fn β.jumps 0 := by
    have e : flowLineNR β.fn β.jumps 0 = s.card + 1 := rfl
    have := k.isLt
    omega
  refine ⟨⟨k + 1, hlt⟩, Nat.succ_ne_zero _, ?_⟩
  have e : flowLineXR β.fn β.jumps 0 ⟨k + 1, hlt⟩ = s.orderEmbOfFin rfl ⟨k, k.isLt⟩ - 0 := rfl
  rw [e, sub_zero]
  exact hk

theorem exists_xL_eq {t : ℝ} (ht : t ∈ jumpSet β.fn β.jumps) (ht0 : t < 0) :
    ∃ i : Fin (flowLineNL β.fn β.jumps 0), (i : ℕ) ≠ 0 ∧ flowLineXL β.fn β.jumps 0 i = t := by
  set s := (jumpSet β.fn β.jumps).filter (· < (0 : ℝ)) with hs
  have hts : t ∈ (s : Set ℝ) := Finset.mem_filter.2 ⟨ht, ht0⟩
  rw [← Finset.range_orderEmbOfFin s rfl] at hts
  obtain ⟨k, hk⟩ := hts
  have hk' : ((Fin.rev k : Fin s.card) : ℕ) + 1 < flowLineNL β.fn β.jumps 0 := by
    have e : flowLineNL β.fn β.jumps 0 = s.card + 1 := rfl
    have := (Fin.rev k).isLt
    omega
  refine ⟨⟨(Fin.rev k : ℕ) + 1, hk'⟩, Nat.succ_ne_zero _, ?_⟩
  have e : flowLineXL β.fn β.jumps 0 ⟨(Fin.rev k : ℕ) + 1, hk'⟩ =
      s.orderEmbOfFin rfl (Fin.rev ⟨(Fin.rev k : ℕ), (Fin.rev k).isLt⟩) - 0 := rfl
  rw [e, sub_zero]
  have : (Fin.rev ⟨(Fin.rev k : ℕ), (Fin.rev k).isLt⟩ : Fin s.card) = k := by
    rw [Fin.eta, Fin.rev_rev]
  rw [this]
  exact hk

/-- **The right rank between consecutive labels** is the index of the lower label. -/
theorem rkR_eq {i : ℕ} (hi : i < flowLineNR β.fn β.jumps 0) {y : ℝ}
    (hy : flowLineXR β.fn β.jumps 0 ⟨i, hi⟩ < y)
    (hy' : ∀ j : Fin (flowLineNR β.fn β.jumps 0), i < (j : ℕ) → y ≤ flowLineXR β.fn β.jumps 0 j) :
    rkR β y = i := by
  classical
  set xR := flowLineXR β.fn β.jumps 0 with hxR
  have hsm := Sec7.StripDet.strictMono_flowLineXR β.fn β.jumps
  set S := univ.filter fun j : Fin (flowLineNR β.fn β.jumps 0) => (j : ℕ) ≠ 0 ∧ xR j < y with hS
  have himg : (jumpSet β.fn β.jumps).filter (fun t => 0 < t ∧ t < y) = S.image xR := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and, hS]
    constructor
    · rintro ⟨htJ, ht0, hty⟩
      obtain ⟨j, hj0, hjt⟩ := exists_xR_eq β htJ ht0
      exact ⟨j, ⟨hj0, by rw [show xR j = t from hjt]; exact hty⟩, hjt⟩
    · rintro ⟨j, ⟨hj0, hjy⟩, rfl⟩
      exact ⟨xR_mem_jumpSet β hj0, xR_pos β hj0, hjy⟩
  have hSeq : S = (Finset.Iic (⟨i, hi⟩ : Fin (flowLineNR β.fn β.jumps 0))).erase
      ⟨0, Supp8.GB6.zero_lt_flowLineNR _ _⟩ := by
    ext j
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, Finset.mem_Iic, ne_eq,
      Fin.ext_iff, Fin.le_def]
    constructor
    · rintro ⟨hj0, hjy⟩
      refine ⟨hj0, ?_⟩
      by_contra hji
      exact absurd hjy (not_lt.2 (hy' j (by omega)))
    · rintro ⟨hj0, hji⟩
      refine ⟨hj0, lt_of_le_of_lt (hsm.monotone (Fin.le_def.2 hji)) hy⟩
  unfold rkR
  rw [himg, Finset.card_image_of_injective _ hsm.injective, hSeq,
    Finset.card_erase_of_mem (Finset.mem_Iic.2 (Fin.le_def.2 (Nat.zero_le _))), Fin.card_Iic]
  rfl

/-- **The left rank between consecutive labels** is the index of the upper label. -/
theorem rkL_eq {i : ℕ} (hi : i < flowLineNL β.fn β.jumps 0) {y : ℝ}
    (hy : y < flowLineXL β.fn β.jumps 0 ⟨i, hi⟩)
    (hy' : ∀ j : Fin (flowLineNL β.fn β.jumps 0), i < (j : ℕ) → flowLineXL β.fn β.jumps 0 j ≤ y) :
    rkL β y = i := by
  classical
  set xL := flowLineXL β.fn β.jumps 0 with hxL
  have hsa := Sec7.StripDet.strictAnti_flowLineXL β.fn β.jumps
  set S := univ.filter fun j : Fin (flowLineNL β.fn β.jumps 0) => (j : ℕ) ≠ 0 ∧ y < xL j with hS
  have himg : (jumpSet β.fn β.jumps).filter (fun t => y < t ∧ t < 0) = S.image xL := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and, hS]
    constructor
    · rintro ⟨htJ, hyt, ht0⟩
      obtain ⟨j, hj0, hjt⟩ := exists_xL_eq β htJ ht0
      exact ⟨j, ⟨hj0, by rw [show xL j = t from hjt]; exact hyt⟩, hjt⟩
    · rintro ⟨j, ⟨hj0, hjy⟩, rfl⟩
      exact ⟨xL_mem_jumpSet β hj0, hjy, xL_neg β hj0⟩
  have hSeq : S = (Finset.Iic (⟨i, hi⟩ : Fin (flowLineNL β.fn β.jumps 0))).erase ⟨0, by unfold flowLineNL; omega⟩ := by
    ext j
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, Finset.mem_Iic, ne_eq,
      Fin.ext_iff, Fin.le_def]
    constructor
    · rintro ⟨hj0, hjy⟩
      refine ⟨hj0, ?_⟩
      by_contra hji
      exact absurd hjy (not_lt.2 (hy' j (by omega)))
    · rintro ⟨hj0, hji⟩
      exact ⟨hj0, lt_of_lt_of_le hy (hsa.antitone (Fin.le_def.2 hji))⟩
  unfold rkL
  rw [himg, Finset.card_image_of_injective _ hsa.injective, hSeq,
    Finset.card_erase_of_mem (Finset.mem_Iic.2 (Fin.le_def.2 (Nat.zero_le _))), Fin.card_Iic]
  rfl

/-! ### The angles read from the weights -/

/-- The angles read from the left weights alone. -/
def phiL : ℕ → ℝ
  | 0 => φ0
  | i + 1 => phiL i + sleLambda κ / chiC κ * wLn κ β i

theorem phiR_eq_sum (i : ℕ) : phiR κ β φ0 i = φ0 - sleLambda κ / chiC κ * ∑ j ∈ range i, wRn κ β j := by
  induction i with
  | zero => simp [phiR]
  | succ i ih => rw [phiR, ih, Finset.sum_range_succ]; ring

theorem phiL_eq_sum (i : ℕ) : phiL κ β φ0 i = φ0 + sleLambda κ / chiC κ * ∑ j ∈ range i, wLn κ β j := by
  induction i with
  | zero => simp [phiL]
  | succ i ih => rw [phiL, ih, Finset.sum_range_succ]; ring

theorem range_filter_lt {n i : ℕ} (h : i ≤ n) : (range n).filter (· < i) = range i := by
  ext j
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

/-- The right weights up to a label sum to the conversion of the height right after it. -/
theorem sum_range_wRn (hκ : 0 < κ) {i : ℕ} (hi : i < flowLineNR β.fn β.jumps 0) {y : ℝ} (hy0 : 0 < y)
    (hyJ : y ∉ β.jumps) (hy : flowLineXR β.fn β.jumps 0 ⟨i, hi⟩ ≤ y)
    (hy' : ∀ j : Fin (flowLineNR β.fn β.jumps 0), i < (j : ℕ) → y < flowLineXR β.fn β.jumps 0 j) :
    sleLambda κ * (1 + ∑ j ∈ range (i + 1), wRn κ β j) = β.fn y := by
  classical
  have hsm := Sec7.StripDet.strictMono_flowLineXR β.fn β.jumps
  have h1 := Exist.forceBoundaryData_flowLine_seed hκ β.isPiecewiseConstantBoundaryData 0 0 hy0.ne'
    (by simpa using hyJ)
  rw [Sec4.forceBoundaryData_of_nonneg _ _ _ _ hy0.le, add_zero, zero_mul, add_zero] at h1
  rw [← h1]
  congr 2
  have hf : univ.filter (fun j : Fin (flowLineNR β.fn β.jumps 0) => flowLineXR β.fn β.jumps 0 j ≤ y) =
      univ.filter (fun j : Fin (flowLineNR β.fn β.jumps 0) => (j : ℕ) < i + 1) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hj
      by_contra hji
      exact absurd hj (not_le.2 (hy' j (by omega)))
    · intro hj
      exact (hsm.monotone (Fin.le_def.2 (show (j : ℕ) ≤ i by omega))).trans hy
  rw [hf]
  have hw : ∀ j ∈ univ.filter (fun j : Fin (flowLineNR β.fn β.jumps 0) => (j : ℕ) < i + 1),
      flowLineRhoR κ β.fn β.jumps 0 0 j = wRn κ β j := fun j _ => by
    simp only [wRn, j.isLt, ↓reduceDIte]
  rw [Finset.sum_congr rfl hw, Exist.StagedLaw.sum_fin_filter_eq (flowLineNR β.fn β.jumps 0) (· < i + 1) (wRn κ β),
    range_filter_lt (by omega)]

/-- The left weights up to a label sum to the conversion of the height left of it. -/
theorem sum_range_wLn (hκ : 0 < κ) {i : ℕ} (hi : i < flowLineNL β.fn β.jumps 0) {y : ℝ} (hy0 : y < 0)
    (hyJ : y ∉ β.jumps) (hy : y < flowLineXL β.fn β.jumps 0 ⟨i, hi⟩)
    (hy' : ∀ j : Fin (flowLineNL β.fn β.jumps 0), i < (j : ℕ) → flowLineXL β.fn β.jumps 0 j ≤ y) :
    -sleLambda κ * (1 + ∑ j ∈ range (i + 1), wLn κ β j) = β.fn y := by
  classical
  have hsa := Sec7.StripDet.strictAnti_flowLineXL β.fn β.jumps
  have h1 := Exist.forceBoundaryData_flowLine_seed hκ β.isPiecewiseConstantBoundaryData 0 0 hy0.ne
    (by simpa using hyJ)
  rw [Sec4.forceBoundaryData_of_neg _ _ _ _ hy0, add_zero, zero_mul, add_zero] at h1
  rw [← h1]
  congr 2
  have hf : univ.filter (fun j : Fin (flowLineNL β.fn β.jumps 0) => y < flowLineXL β.fn β.jumps 0 j) =
      univ.filter (fun j : Fin (flowLineNL β.fn β.jumps 0) => (j : ℕ) < i + 1) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hj
      by_contra hji
      exact absurd hj (not_lt.2 (hy' j (by omega)))
    · intro hj
      exact hy.trans_le (hsa.antitone (Fin.le_def.2 (show (j : ℕ) ≤ i by omega)))
  rw [hf]
  have hw : ∀ j ∈ univ.filter (fun j : Fin (flowLineNL β.fn β.jumps 0) => (j : ℕ) < i + 1),
      flowLineRhoL κ β.fn β.jumps 0 0 j = wLn κ β j := fun j _ => by
    simp only [wLn, j.isLt, ↓reduceDIte]
  rw [Finset.sum_congr rfl hw, Exist.StagedLaw.sum_fin_filter_eq (flowLineNL β.fn β.jumps 0) (· < i + 1) (wLn κ β),
    range_filter_lt (by omega)]

/-- **The right angle after a label** is the angle of the height there. -/
theorem phiR_succ_eq (hκ : 0 < κ) (hκ4 : κ < 4) {i : ℕ} (hi : i < flowLineNR β.fn β.jumps 0) {y : ℝ}
    (hy0 : 0 < y) (hyJ : y ∉ β.jumps) (hy : flowLineXR β.fn β.jumps 0 ⟨i, hi⟩ ≤ y)
    (hy' : ∀ j : Fin (flowLineNR β.fn β.jumps 0), i < (j : ℕ) → y < flowLineXR β.fn β.jumps 0 j) :
    phiR κ β φ0 (i + 1) = φ0 + (sleLambda κ - β.fn y) / chiC κ := by
  have hχ : chiC κ ≠ 0 := (Sec4.chiC_pos hκ hκ4).ne'
  have hs := sum_range_wRn κ β hκ hi hy0 hyJ hy hy'
  rw [phiR_eq_sum]
  set S := ∑ j ∈ range (i + 1), wRn κ β j
  have e : sleLambda κ * S = β.fn y - sleLambda κ := by linarith [hs, mul_add (sleLambda κ) 1 S]
  rw [div_mul_eq_mul_div, e]
  field_simp
  ring

/-- **The left angle after a label** is the angle of the height there. -/
theorem phiL_succ_eq (hκ : 0 < κ) (hκ4 : κ < 4) {i : ℕ} (hi : i < flowLineNL β.fn β.jumps 0) {y : ℝ}
    (hy0 : y < 0) (hyJ : y ∉ β.jumps) (hy : y < flowLineXL β.fn β.jumps 0 ⟨i, hi⟩)
    (hy' : ∀ j : Fin (flowLineNL β.fn β.jumps 0), i < (j : ℕ) → flowLineXL β.fn β.jumps 0 j ≤ y) :
    phiL κ β φ0 (i + 1) = φ0 - (sleLambda κ + β.fn y) / chiC κ := by
  have hχ : chiC κ ≠ 0 := (Sec4.chiC_pos hκ hκ4).ne'
  have hs := sum_range_wLn κ β hκ hi hy0 hyJ hy hy'
  rw [phiL_eq_sum]
  set S := ∑ j ∈ range (i + 1), wLn κ β j
  have e : sleLambda κ * S = -β.fn y - sleLambda κ := by
    linarith [hs, mul_add (-sleLambda κ) 1 S, neg_mul (sleLambda κ) S]
  rw [div_mul_eq_mul_div, e]
  field_simp
  ring

/-! ### Points between labels inside a region -/

theorem exists_pt_right {aR : ℝ} {i : ℕ} (hi : i < flowLineNR β.fn β.jumps 0)
    (hiR : flowLineXR β.fn β.jumps 0 ⟨i, hi⟩ < aR) :
    ∃ u, flowLineXR β.fn β.jumps 0 ⟨i, hi⟩ < u ∧ u < aR ∧ u ∉ β.jumps ∧
      ∀ j : Fin (flowLineNR β.fn β.jumps 0), i < (j : ℕ) → u < flowLineXR β.fn β.jumps 0 j := by
  have hsm := Sec7.StripDet.strictMono_flowLineXR β.fn β.jumps
  by_cases h : i + 1 < flowLineNR β.fn β.jumps 0
  · have hlt : flowLineXR β.fn β.jumps 0 ⟨i, hi⟩ < min (flowLineXR β.fn β.jumps 0 ⟨i + 1, h⟩) aR :=
      lt_min (hsm (Fin.lt_def.2 (by simp))) hiR
    obtain ⟨u, hu1, hu2, huJ⟩ := Sec4.exists_mem_Ioo_not_mem β.jumps hlt
    refine ⟨u, hu1, hu2.trans_le (min_le_right _ _), huJ, fun j hj => ?_⟩
    exact (hu2.trans_le (min_le_left _ _)).trans_le (hsm.monotone (Fin.le_def.2 (by simp; omega)))
  · obtain ⟨u, hu1, hu2, huJ⟩ := Sec4.exists_mem_Ioo_not_mem β.jumps hiR
    exact ⟨u, hu1, hu2, huJ, fun j hj => absurd j.isLt (by omega)⟩

theorem exists_pt_left {aL : ℝ} {i : ℕ} (hi : i < flowLineNL β.fn β.jumps 0)
    (hiL : aL < flowLineXL β.fn β.jumps 0 ⟨i, hi⟩) :
    ∃ v, aL < v ∧ v < flowLineXL β.fn β.jumps 0 ⟨i, hi⟩ ∧ v ∉ β.jumps ∧
      ∀ j : Fin (flowLineNL β.fn β.jumps 0), i < (j : ℕ) → flowLineXL β.fn β.jumps 0 j < v := by
  have hsa := Sec7.StripDet.strictAnti_flowLineXL β.fn β.jumps
  by_cases h : i + 1 < flowLineNL β.fn β.jumps 0
  · have hlt : max (flowLineXL β.fn β.jumps 0 ⟨i + 1, h⟩) aL < flowLineXL β.fn β.jumps 0 ⟨i, hi⟩ :=
      max_lt (hsa (Fin.lt_def.2 (by simp))) hiL
    obtain ⟨v, hv1, hv2, hvJ⟩ := Sec4.exists_mem_Ioo_not_mem β.jumps hlt
    refine ⟨v, (le_max_right _ _).trans_lt hv1, hv2, hvJ, fun j hj => ?_⟩
    exact (hsa.antitone (Fin.le_def.2 (by simp; omega))).trans_lt ((le_max_left _ _).trans_lt hv1)
  · obtain ⟨v, hv1, hv2, hvJ⟩ := Sec4.exists_mem_Ioo_not_mem β.jumps hiL
    exact ⟨v, hv1, hv2, hvJ, fun j hj => absurd j.isLt (by omega)⟩

/-! ### The region fact and the valid region pair -/

/-- **The two angle regions of a word**: `(aL, 0)` and `(0, aR)` are nonempty, every height there reads a separated
angle (`φ0 + (λ − h)/χ` on the right, `φ0 − (λ + h)/χ` on the left), heights of equal rank on the two sides read
the same angle (`h_R − h_L = 2λ`), all heights are bounded by `Hm`, and at most `N` jumps lie beyond each region. -/
structure RegionFact (aL aR Hm : ℝ) (N : ℕ) : Prop where
  aL_neg : aL < 0
  aR_pos : 0 < aR
  start_mem : φ0 ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)
  bandR : ∀ z, 0 < z → z < aR → z ∉ β.jumps →
    φ0 + (sleLambda κ - β.fn z) / chiC κ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)
  bandL : ∀ z, aL < z → z < 0 → z ∉ β.jumps →
    φ0 - (sleLambda κ + β.fn z) / chiC κ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)
  pair : ∀ u v, 0 < u → u < aR → u ∉ β.jumps → aL < v → v < 0 → v ∉ β.jumps → rkR β u = rkL β v →
    β.fn u - β.fn v = 2 * sleLambda κ
  bound : ∀ z, z ∉ β.jumps → |β.fn z| ≤ Hm
  farR : (β.jumps.filter fun y => aR < y).card ≤ N
  farL : (β.jumps.filter fun y => y < aL).card ≤ N

variable {κ β φ0}

theorem RegionFact.one_le_pRc {aL aR Hm : ℝ} {N : ℕ} (h : RegionFact κ β φ0 aL aR Hm N) : 1 ≤ pRc β aR := by
  have := (xR_lt_iff β aR ⟨0, Supp8.GB6.zero_lt_flowLineNR _ _⟩).1 (by rw [xR_zero]; exact h.aR_pos)
  have h0 : 0 < pRc β aR := by simpa using this
  omega

theorem RegionFact.one_le_pLc {aL aR Hm : ℝ} {N : ℕ} (h : RegionFact κ β φ0 aL aR Hm N) : 1 ≤ pLc β aL := by
  have := (xL_gt_iff β aL ⟨0, by unfold flowLineNL; omega⟩).1 (by rw [xL_zero]; exact h.aL_neg)
  have h0 : 0 < pLc β aL := by simpa using this
  omega

/-- **The region pair is valid.** -/
theorem valid_region (hκ : 0 < κ) (hκ4 : κ < 4) {aL aR Hm : ℝ} {N : ℕ} (h : RegionFact κ β φ0 aL aR Hm N) :
    Valid κ β φ0 (pRc β aR - 1, pLc β aL) := by
  have hχ : chiC κ ≠ 0 := (Sec4.chiC_pos hκ hκ4).ne'
  have hpR1 := h.one_le_pRc
  have hpRle := pRc_le β aR
  have hpLle := pLc_le β aL
  -- the right angle after a label inside the right region
  have hR : ∀ i (hi : i < pRc β aR), ∃ u, 0 < u ∧ u < aR ∧ u ∉ β.jumps ∧ rkR β u = i ∧
      phiR κ β φ0 (i + 1) = φ0 + (sleLambda κ - β.fn u) / chiC κ := by
    intro i hi
    have hiN : i < flowLineNR β.fn β.jumps 0 := hi.trans_le hpRle
    have hiR := (xR_lt_iff β aR ⟨i, hiN⟩).2 hi
    obtain ⟨u, hu1, hu2, huJ, hu3⟩ := exists_pt_right β hiN hiR
    have hu0 : 0 < u := (GW3Word.flowLineXR_nonneg β.fn β.jumps _).trans_lt hu1
    exact ⟨u, hu0, hu2, huJ, rkR_eq β hiN hu1 fun j hj => (hu3 j hj).le,
      phiR_succ_eq κ β φ0 hκ hκ4 hiN hu0 huJ hu1.le hu3⟩
  have hL : ∀ i (hi : i < pLc β aL), ∃ v, aL < v ∧ v < 0 ∧ v ∉ β.jumps ∧ rkL β v = i ∧
      phiL κ β φ0 (i + 1) = φ0 - (sleLambda κ + β.fn v) / chiC κ := by
    intro i hi
    have hiN : i < flowLineNL β.fn β.jumps 0 := hi.trans_le hpLle
    have hiL := (xL_gt_iff β aL ⟨i, hiN⟩).2 hi
    obtain ⟨v, hv1, hv2, hvJ, hv3⟩ := exists_pt_left β hiN hiL
    have hv0 : v < 0 := hv2.trans_le (GW3Word.flowLineXL_nonpos β.fn β.jumps _)
    exact ⟨v, hv1, hv0, hvJ, rkL_eq β hiN hv2 fun j hj => (hv3 j hj).le,
      phiL_succ_eq κ β φ0 hκ hκ4 hiN hv0 hvJ hv2 fun j hj => (hv3 j hj).le⟩
  -- the two readings agree on the common block
  have hagree : ∀ i ≤ pLc β aL, phiM κ β φ0 (pRc β aR - 1) i = phiL κ β φ0 i := by
    intro i
    induction i with
    | zero => intro _; rfl
    | succ i ih =>
      intro hi
      by_cases hiR : i + 1 ≤ pRc β aR - 1 + 1
      · have hpm : phiM κ β φ0 (pRc β aR - 1) (i + 1) = phiR κ β φ0 (i + 1) := by
          simp only [phiM, hiR, ↓reduceIte]
        obtain ⟨u, hu0, hua, huJ, hur, hpu⟩ := hR i (by omega)
        obtain ⟨v, hva, hv0, hvJ, hvr, hpv⟩ := hL i (by omega)
        have hp := h.pair u v hu0 hua huJ hva hv0 hvJ (hur.trans hvr.symm)
        rw [hpm, hpu, hpv]
        have e : sleLambda κ - β.fn u = -(sleLambda κ + β.fn v) := by linarith
        rw [e, neg_div]
        ring
      · have hpm : phiM κ β φ0 (pRc β aR - 1) (i + 1) =
            phiM κ β φ0 (pRc β aR - 1) i + sleLambda κ / chiC κ * wLn κ β i := by
          simp only [phiM, hiR, ↓reduceIte]
        rw [hpm, ih (by omega)]
        rfl
  refine ⟨by omega, hpLle, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
  · -- the right band
    rcases i with _ | i
    · exact h.start_mem
    · obtain ⟨u, hu0, hua, huJ, -, hpu⟩ := hR i (by omega)
      rw [hpu]
      exact h.bandR u hu0 hua huJ
  · -- the left match
    rw [hagree i hi.le, hagree (i + 1) hi]
    change wLn κ β i = -(chiC κ / sleLambda κ * (phiL κ β φ0 i -
      (phiL κ β φ0 i + sleLambda κ / chiC κ * wLn κ β i)))
    have hlam : sleLambda κ ≠ 0 := (Sec4.sleLambda_pos hκ).ne'
    field_simp
    ring
  · -- the left band
    rw [hagree i hi]
    rcases i with _ | i
    · exact h.start_mem
    · obtain ⟨v, hva, hv0, hvJ, -, hpv⟩ := hL i (by omega)
      rw [hpv]
      exact h.bandL v hva hv0 hvJ

/-! ### The far weight of the region pair -/

theorem abs_rightLim_le {b : ℝ → ℝ} {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J) {Hm : ℝ}
    (hB : ∀ z, z ∉ J → |b z| ≤ Hm) (y : ℝ) : |rightLim b y| ≤ Hm := by
  obtain ⟨hi, hy, h⟩ := GW2Rd.exists_Ioo_eq_rightLim hb y
  obtain ⟨t, ht1, ht2, htJ⟩ := Sec4.exists_mem_Ioo_not_mem J hy
  rw [← h t ⟨ht1, ht2⟩]
  exact hB t htJ

theorem abs_leftLim_le {b : ℝ → ℝ} {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J) {Hm : ℝ}
    (hB : ∀ z, z ∉ J → |b z| ≤ Hm) (y : ℝ) : |leftLim b y| ≤ Hm := by
  obtain ⟨lo, hy, h⟩ := GW2Rd.exists_Ioo_eq_leftLim hb y
  obtain ⟨t, ht1, ht2, htJ⟩ := Sec4.exists_mem_Ioo_not_mem J hy
  rw [← h t ⟨ht1, ht2⟩]
  exact hB t htJ

theorem abs_jump_div_le {Hm a b : ℝ} (hlam : 0 < sleLambda κ) (ha : |a| ≤ Hm) (hb : |b| ≤ Hm) :
    |(a - b) / sleLambda κ| ≤ 2 * Hm / sleLambda κ := by
  rw [abs_div, abs_of_pos hlam]
  gcongr
  calc |a - b| ≤ |a| + |b| := abs_sub _ _
    _ ≤ 2 * Hm := by linarith

theorem abs_wRn_le (hκ : 0 < κ) {Hm : ℝ} (hB : ∀ z, z ∉ β.jumps → |β.fn z| ≤ Hm) (hHm : 0 ≤ Hm) {j : ℕ}
    (hj : 1 ≤ j) : |wRn κ β j| ≤ 2 * Hm / sleLambda κ := by
  have hlam := Sec4.sleLambda_pos hκ
  have hb := β.isPiecewiseConstantBoundaryData
  rcases j with _ | k
  · omega
  · unfold wRn
    split_ifs with h
    · set s := (jumpSet β.fn β.jumps).filter ((0 : ℝ) < ·) with hs
      have hk : k < s.card := by
        have e : flowLineNR β.fn β.jumps 0 = s.card + 1 := rfl
        omega
      have e : flowLineRhoR κ β.fn β.jumps 0 0 ⟨k + 1, h⟩ =
          (rightLim β.fn (s.orderEmbOfFin rfl ⟨k, hk⟩) - leftLim β.fn (s.orderEmbOfFin rfl ⟨k, hk⟩)) /
            sleLambda κ := rfl
      rw [e]
      exact abs_jump_div_le hlam (abs_rightLim_le hb hB _) (abs_leftLim_le hb hB _)
    · rw [abs_zero]; positivity

theorem abs_wLn_le (hκ : 0 < κ) {Hm : ℝ} (hB : ∀ z, z ∉ β.jumps → |β.fn z| ≤ Hm) (hHm : 0 ≤ Hm) {j : ℕ}
    (hj : 1 ≤ j) : |wLn κ β j| ≤ 2 * Hm / sleLambda κ := by
  have hlam := Sec4.sleLambda_pos hκ
  have hb := β.isPiecewiseConstantBoundaryData
  rcases j with _ | k
  · omega
  · unfold wLn
    split_ifs with h
    · set s := (jumpSet β.fn β.jumps).filter (· < (0 : ℝ)) with hs
      have hk : k < s.card := by
        have e : flowLineNL β.fn β.jumps 0 = s.card + 1 := rfl
        omega
      have e : flowLineRhoL κ β.fn β.jumps 0 0 ⟨k + 1, h⟩ =
          (rightLim β.fn (s.orderEmbOfFin rfl (Fin.rev ⟨k, hk⟩)) -
            leftLim β.fn (s.orderEmbOfFin rfl (Fin.rev ⟨k, hk⟩))) / sleLambda κ := rfl
      rw [e]
      exact abs_jump_div_le hlam (abs_rightLim_le hb hB _) (abs_leftLim_le hb hB _)
    · rw [abs_zero]; positivity

/-- At most `N + 1` right labels lie at or beyond `aR > 0`. -/
theorem card_farR_le {aR : ℝ} (hR : 0 < aR) {N : ℕ} (h : (β.jumps.filter fun y => aR < y).card ≤ N) :
    flowLineNR β.fn β.jumps 0 - pRc β aR ≤ N + 1 := by
  classical
  have hsm := Sec7.StripDet.strictMono_flowLineXR β.fn β.jumps
  have hsplit := Finset.card_filter_add_card_filter_not (s := univ)
    (fun j : Fin (flowLineNR β.fn β.jumps 0) => flowLineXR β.fn β.jumps 0 j < aR)
  rw [Finset.card_univ, Fintype.card_fin] at hsplit
  have himg : (univ.filter fun j : Fin (flowLineNR β.fn β.jumps 0) => ¬ flowLineXR β.fn β.jumps 0 j < aR).image
      (flowLineXR β.fn β.jumps 0) ⊆ insert aR (β.jumps.filter fun y => aR < y) := by
    intro t ht
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 ht
    have hj' := not_lt.1 (Finset.mem_filter.1 hj).2
    have hj0 : (j : ℕ) ≠ 0 := fun h0 => by
      have : j = ⟨0, Supp8.GB6.zero_lt_flowLineNR _ _⟩ := Fin.ext h0
      rw [this, xR_zero] at hj'
      linarith
    rcases hj'.lt_or_eq with hlt | heq
    · exact Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨(Finset.mem_filter.1 (xR_mem_jumpSet β hj0)).1, hlt⟩)
    · rw [← heq]; exact Finset.mem_insert_self _ _
  have h1 := Finset.card_le_card himg
  rw [Finset.card_image_of_injective _ hsm.injective] at h1
  have h2 := Finset.card_insert_le aR (β.jumps.filter fun y => aR < y)
  unfold pRc
  omega

/-- At most `N + 1` left labels lie at or beyond `aL < 0`. -/
theorem card_farL_le {aL : ℝ} (hL : aL < 0) {N : ℕ} (h : (β.jumps.filter fun y => y < aL).card ≤ N) :
    flowLineNL β.fn β.jumps 0 - pLc β aL ≤ N + 1 := by
  classical
  have hsa := Sec7.StripDet.strictAnti_flowLineXL β.fn β.jumps
  have hsplit := Finset.card_filter_add_card_filter_not (s := univ)
    (fun i : Fin (flowLineNL β.fn β.jumps 0) => aL < flowLineXL β.fn β.jumps 0 i)
  rw [Finset.card_univ, Fintype.card_fin] at hsplit
  have himg : (univ.filter fun i : Fin (flowLineNL β.fn β.jumps 0) => ¬ aL < flowLineXL β.fn β.jumps 0 i).image
      (flowLineXL β.fn β.jumps 0) ⊆ insert aL (β.jumps.filter fun y => y < aL) := by
    intro t ht
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 ht
    have hi' := not_lt.1 (Finset.mem_filter.1 hi).2
    have hi0 : (i : ℕ) ≠ 0 := fun h0 => by
      have : i = ⟨0, by unfold flowLineNL; omega⟩ := Fin.ext h0
      rw [this, xL_zero] at hi'
      linarith
    rcases hi'.lt_or_eq with hlt | heq
    · exact Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨(Finset.mem_filter.1 (xL_mem_jumpSet β hi0)).1, hlt⟩)
    · rw [heq]; exact Finset.mem_insert_self _ _
  have h1 := Finset.card_le_card himg
  rw [Finset.card_image_of_injective _ hsa.injective] at h1
  have h2 := Finset.card_insert_le aL (β.jumps.filter fun y => y < aL)
  unfold pLc
  omega

theorem RegionFact.bound_nonneg {aL aR Hm : ℝ} {N : ℕ} (h : RegionFact κ β φ0 aL aR Hm N) : 0 ≤ Hm := by
  obtain ⟨z, -, -, hzJ⟩ := Sec4.exists_mem_Ioo_not_mem β.jumps (show (0 : ℝ) < 1 by norm_num)
  exact (abs_nonneg _).trans (h.bound z hzJ)

/-- **The far weight of the region pair** is at most `4 (N + 1) Hm / λ`. -/
theorem farD_region_le (hκ : 0 < κ) {aL aR Hm : ℝ} {N : ℕ} (h : RegionFact κ β φ0 aL aR Hm N) :
    farD κ β (pRc β aR - 1, pLc β aL) ≤ 4 * ((N : ℝ) + 1) * Hm / sleLambda κ := by
  have hlam := Sec4.sleLambda_pos hκ
  have hHm := h.bound_nonneg
  have hpR1 := h.one_le_pRc
  have hpL1 := h.one_le_pLc
  have hcR := card_farR_le h.aR_pos h.farR
  have hcL := card_farL_le h.aL_neg h.farL
  have hq : 0 ≤ 2 * Hm / sleLambda κ := by positivity
  unfold farD
  have hL : ∑ j ∈ range (flowLineNL β.fn β.jumps 0 - pLc β aL), |wLn κ β (pLc β aL + j)| ≤
      ((N : ℝ) + 1) * (2 * Hm / sleLambda κ) := by
    calc _ ≤ ∑ _j ∈ range (flowLineNL β.fn β.jumps 0 - pLc β aL), 2 * Hm / sleLambda κ :=
          Finset.sum_le_sum fun j _ => abs_wLn_le hκ h.bound hHm (by omega)
      _ = ((flowLineNL β.fn β.jumps 0 - pLc β aL : ℕ) : ℝ) * (2 * Hm / sleLambda κ) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ ((N : ℝ) + 1) * (2 * Hm / sleLambda κ) := by
          gcongr
          exact_mod_cast hcL
  have hR : ∑ j ∈ range (flowLineNR β.fn β.jumps 0 - 1 - (pRc β aR - 1)), |wRn κ β (1 + (pRc β aR - 1) + j)| ≤
      ((N : ℝ) + 1) * (2 * Hm / sleLambda κ) := by
    calc _ ≤ ∑ _j ∈ range (flowLineNR β.fn β.jumps 0 - 1 - (pRc β aR - 1)), 2 * Hm / sleLambda κ :=
          Finset.sum_le_sum fun j _ => abs_wRn_le hκ h.bound hHm (by omega)
      _ = ((flowLineNR β.fn β.jumps 0 - 1 - (pRc β aR - 1) : ℕ) : ℝ) * (2 * Hm / sleLambda κ) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ ((N : ℝ) + 1) * (2 * Hm / sleLambda κ) := by
          gcongr
          have : flowLineNR β.fn β.jumps 0 - 1 - (pRc β aR - 1) ≤ N + 1 := by omega
          exact_mod_cast this
  have e : 4 * ((N : ℝ) + 1) * Hm / sleLambda κ =
      ((N : ℝ) + 1) * (2 * Hm / sleLambda κ) + ((N : ℝ) + 1) * (2 * Hm / sleLambda κ) := by ring
  rw [e]
  exact add_le_add hL hR

/-! ### The optimal shell of a word with two angle regions -/

/-- **The drift constant** of heights bounded by `Hm` and at most `N` jumps beyond each region. -/
def driftC (κ Hm : ℝ) (N : ℕ) : ℝ := 8 * angleWeightBound κ / 3 + 4 / 3 * (4 * ((N : ℝ) + 1) * Hm / sleLambda κ)

/-- **The optimal shell of a word with two angle regions** presents the word, has separated angles, and its drift
is at most `driftC κ Hm N`. -/
theorem optShell_of_region (hκ : 0 < κ) (hκ4 : κ < 4) {aL aR Hm : ℝ} {N : ℕ}
    (h : RegionFact κ β φ0 aL aR Hm N) (k : ℕ) (start : ℝ) :
    PresentsO κ β (rootScale k) false (optShell κ β φ0 k start).xL
      (angleWordL κ (optShell κ β φ0 k start).φ (optShell κ β φ0 k start).mL (optShell κ β φ0 k start).ρL₀)
      (optShell κ β φ0 k start).xR
      (angleWordR κ (optShell κ β φ0 k start).φ (optShell κ β φ0 k start).mR
        (optShell κ β φ0 k start).ρR₀) ∧
    (∀ i, (optShell κ β φ0 k start).φ i ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) ∧
    Prop59Stage.stageDriftBound κ (optShell κ β φ0 k start).ρL₀ (optShell κ β φ0 k start).ρR₀ ≤
      driftC κ Hm N := by
  have hv := valid_region hκ hκ4 h
  refine ⟨presentsO_optShell κ β φ0 hκ hκ4 hv k start, optShell_angles κ β φ0 hv k start, ?_⟩
  refine (stageDriftBound_optShell_le κ β φ0 hv k start).trans ?_
  unfold driftC
  have := farD_region_le hκ h
  linarith

end InteractingSLE.Theorem14.GW2Rq
