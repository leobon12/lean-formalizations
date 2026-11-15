/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.ChartGauss
import InteractingSLE.Frozen.Spec.forceBoundaryData
import InteractingSLE.Frozen.Spec.forceJumpSet

/-!
# The sorted boundary word of force data

Packet PROVE-STAGEDLAW3. The conditional law at the stop of a flow-line piece is the GFF whose boundary data is the
force data of Theorem 1.1 at the current centred mark positions, shifted by `−θχ`. This file writes that datum as a
**sorted boundary word** (`Restart.BoundaryWord`), as a measurable function of padded data:

* `forceWord κ nL nR pL pR ρL ρR s`: jump positions `pL (nL−1), …, pL 0, 0, pR 0, …, pR (nR−1)` (made weakly
  increasing by a cumulative maximum, `cumMax`, so the word is sorted for **every** input), heights the values of the
  force data (`wordHeight`) minus `s`;
* `isSorted_forceWord`, `measurable_forceWord`;
* **`fn_forceWord`**: for antitone nonpositive left positions and monotone nonnegative right positions, the word's
  boundary function is the force data minus `s` off the jumps;
* **`eqOn_mean_forceWord`**: every bounded harmonic extension of the force data is `mean + s` on `ℍ`;
* `tendsto_mean_forceWord` (the mean is continuous in the positions and the point) and `abs_mean_forceWord_le` (a bound
  independent of the positions).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Exist

namespace StagedLaw

open Restart

/-! ### Cumulative maxima -/

/-- The cumulative maximum `k ↦ max_{j ≤ k} f j`. -/
def cumMax (f : ℕ → ℝ) : ℕ → ℝ
  | 0 => f 0
  | k + 1 => max (cumMax f k) (f (k + 1))

theorem monotone_cumMax (f : ℕ → ℝ) : Monotone (cumMax f) :=
  monotone_nat_of_le_succ fun _ => le_max_left _ _

theorem le_cumMax (f : ℕ → ℝ) (k : ℕ) : f k ≤ cumMax f k := by
  cases k with
  | zero => exact le_rfl
  | succ k => exact le_max_right _ _

theorem cumMax_eq_of_monotoneOn {f : ℕ → ℝ} {n : ℕ} (hf : ∀ i j, i ≤ j → j < n → f i ≤ f j) :
    ∀ k < n, cumMax f k = f k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    change max (cumMax f k) (f (k + 1)) = f (k + 1)
    rw [ih (by omega), max_eq_right (hf k (k + 1) (by omega) hk)]

theorem continuous_cumMax_apply (k : ℕ) : Continuous fun f : ℕ → ℝ => cumMax f k := by
  induction k with
  | zero => exact continuous_apply 0
  | succ k ih => exact ih.max (continuous_apply (k + 1))

/-! ### The word -/

/-- The raw jump positions in increasing order: `pL (nL−1), …, pL 0, 0, pR 0, …`. -/
def rawPos (nL : ℕ) (pL pR : ℕ → ℝ) (k : ℕ) : ℝ :=
  if k < nL then pL (nL - 1 - k) else if k = nL then 0 else pR (k - nL - 1)

/-- The heights: the force data on the `k`-th interval, minus `s`. -/
def wordHeight (κ : ℝ) (nL : ℕ) (ρL ρR : ℕ → ℝ) (s : ℝ) (k : ℕ) : ℝ :=
  if k ≤ nL then -(Real.pi / Real.sqrt κ) * (1 + ∑ i ∈ Finset.range (nL - k), ρL i) - s
  else (Real.pi / Real.sqrt κ) * (1 + ∑ i ∈ Finset.range (k - nL - 1), ρR i) - s

/-- **The sorted word of the force data at positions `(pL; pR)` with weights `(ρL; ρR)`, shifted by `−s`.** -/
def forceWord (κ : ℝ) (nL nR : ℕ) (pL pR ρL ρR : ℕ → ℝ) (s : ℝ) : BoundaryWord :=
  (nL + 1 + nR, cumMax (rawPos nL pL pR), wordHeight κ nL ρL ρR s)

theorem isSorted_forceWord (κ : ℝ) (nL nR : ℕ) (pL pR ρL ρR : ℕ → ℝ) (s : ℝ) :
    (forceWord κ nL nR pL pR ρL ρR s).IsSorted := fun _ _ hij _ => monotone_cumMax _ hij

/-! ### The boundary function of the word -/

/-- A downward closed finite set of naturals is an initial segment. -/
theorem eq_range_card_of_downward {D : Finset ℕ} (hD : ∀ k ∈ D, ∀ j ≤ k, j ∈ D) : D = Finset.range D.card := by
  have hsub : D ⊆ Finset.range D.card := by
    intro k hk
    rw [Finset.mem_range]
    by_contra h
    push Not at h
    have h1 : Finset.range (k + 1) ⊆ D := fun j hj => hD k hk j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))
    have h2 := Finset.card_le_card h1
    rw [Finset.card_range] at h2
    omega
  exact Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_range])

/-- A sum over a filter of `Fin n` as a sum over a filter of `range n`. -/
theorem sum_fin_filter_eq (n : ℕ) (P : ℕ → Prop) [DecidablePred P] (g : ℕ → ℝ) :
    (∑ i ∈ Finset.univ.filter (fun i : Fin n => P i), g i) = ∑ i ∈ (Finset.range n).filter P, g i := by
  rw [Finset.sum_filter, Finset.sum_filter]
  exact Fin.sum_univ_eq_sum_range (fun i => if P i then g i else 0) n

section Fn

variable {nL nR : ℕ} {pL pR : ℕ → ℝ}

/-- The hypotheses on the positions: left antitone and nonpositive, right monotone and nonnegative. -/
def IsMarkOrder (nL nR : ℕ) (pL pR : ℕ → ℝ) : Prop :=
  (∀ i j, i ≤ j → j < nL → pL j ≤ pL i) ∧ (∀ i < nL, pL i ≤ 0) ∧ (∀ i j, i ≤ j → j < nR → pR i ≤ pR j) ∧
    (∀ i < nR, 0 ≤ pR i)

theorem rawPos_mono (h : IsMarkOrder nL nR pL pR) :
    ∀ i j, i ≤ j → j < nL + 1 + nR → rawPos nL pL pR i ≤ rawPos nL pL pR j := by
  obtain ⟨hL, hL0, hR, hR0⟩ := h
  intro i j hij hj
  unfold rawPos
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 <;> first
    | exact hL _ _ (by omega) (by omega)
    | exact hL0 _ (by omega)
    | exact (hL0 _ (by omega)).trans (hR0 _ (by omega))
    | exact hR0 _ (by omega)
    | exact le_rfl
    | exact hR _ _ (by omega) (by omega)
    | omega

theorem cumMax_rawPos (h : IsMarkOrder nL nR pL pR) {k : ℕ} (hk : k < nL + 1 + nR) :
    cumMax (rawPos nL pL pR) k = rawPos nL pL pR k :=
  cumMax_eq_of_monotoneOn (rawPos_mono h) k hk

theorem rawPos_ne_of_notMem {κ : ℝ} {ρL ρR : ℕ → ℝ} {s y : ℝ} (h : IsMarkOrder nL nR pL pR)
    (hy : y ∉ (forceWord κ nL nR pL pR ρL ρR s).jumps) {k : ℕ} (hk : k < nL + 1 + nR) :
    rawPos nL pL pR k ≠ y := fun he =>
  hy (BoundaryWord.mem_jumps.2 ⟨k, hk, by change cumMax _ k = y; rw [cumMax_rawPos h hk, he]⟩)

/-- **The word's boundary function is the force data minus the shift**, off the jumps and `0`. -/
theorem fn_forceWord (κ : ℝ) (ρL ρR : ℕ → ℝ) (s : ℝ) (h : IsMarkOrder nL nR pL pR) {y : ℝ}
    (hy : y ∉ (forceWord κ nL nR pL pR ρL ρR s).jumps) (hy0 : y ≠ 0) :
    (forceWord κ nL nR pL pR ρL ρR s).fn y =
      forceBoundaryData κ (fun i : Fin nL => ρL i) (fun j : Fin nR => ρR j) (fun i : Fin nL => pL i)
        (fun j : Fin nR => pR j) y - s := by
  classical
  have hne := fun k hk => rawPos_ne_of_notMem h hy (k := k) hk
  obtain ⟨hL, hL0, hR, hR0⟩ := h
  have hfilt : (Finset.range (nL + 1 + nR)).filter (fun k => cumMax (rawPos nL pL pR) k < y) =
      (Finset.range (nL + 1 + nR)).filter (fun k => rawPos nL pL pR k < y) :=
    Finset.filter_congr fun k hk => by rw [cumMax_rawPos ⟨hL, hL0, hR, hR0⟩ (Finset.mem_range.1 hk)]
  unfold BoundaryWord.fn BoundaryWord.index forceBoundaryData
  change wordHeight κ nL ρL ρR s
      ((Finset.range (nL + 1 + nR)).filter (fun k => cumMax (rawPos nL pL pR) k < y)).card = _
  rw [hfilt]
  rcases lt_or_gt_of_ne hy0 with hneg | hpos
  · -- left of the seed
    set DL := (Finset.range nL).filter (fun i => y < pL i) with hDLdef
    have hDL : DL = Finset.range DL.card := eq_range_card_of_downward fun k hk j hjk => by
      rw [hDLdef, Finset.mem_filter, Finset.mem_range] at hk ⊢
      exact ⟨by omega, hk.2.trans_le (hL j k hjk hk.1)⟩
    have hmL : DL.card ≤ nL := (Finset.card_filter_le _ _).trans (Finset.card_range _).le
    have hidx : (Finset.range (nL + 1 + nR)).filter (fun k => rawPos nL pL pR k < y) =
        Finset.range (nL - DL.card) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨hk, hky⟩
        by_cases hkL : k < nL
        · have hmem : nL - 1 - k ∉ DL := by
            rw [hDLdef, Finset.mem_filter]
            rintro ⟨-, hlt⟩
            unfold rawPos at hky
            rw [ite_eq_left hkL] at hky
            linarith
          rw [hDL, Finset.mem_range] at hmem
          omega
        · exfalso
          unfold rawPos at hky
          rw [ite_eq_right hkL] at hky
          split_ifs at hky with hk2
          · linarith
          · linarith [hR0 (k - nL - 1) (by omega)]
      · intro hk
        refine ⟨by omega, ?_⟩
        have hkL : k < nL := by omega
        unfold rawPos
        rw [ite_eq_left hkL]
        have hmem : nL - 1 - k ∉ DL := by
          rw [hDL, Finset.mem_range]
          omega
        rw [hDLdef, Finset.mem_filter, not_and, Finset.mem_range] at hmem
        have h1 := hmem (by omega)
        have h2 := hne k (by omega)
        unfold rawPos at h2
        rw [ite_eq_left hkL] at h2
        exact lt_of_le_of_ne (not_lt.1 h1) h2
    rw [hidx, Finset.card_range, ite_eq_left hneg]
    unfold wordHeight
    rw [ite_eq_left (Nat.sub_le _ _), Nat.sub_sub_self hmL, sum_fin_filter_eq nL (fun i => y < pL i) ρL, ← hDLdef,
      hDL, Finset.card_range]
  · -- right of the seed
    set DR := (Finset.range nR).filter (fun j => pR j < y) with hDRdef
    have hDR : DR = Finset.range DR.card := eq_range_card_of_downward fun k hk j hjk => by
      rw [hDRdef, Finset.mem_filter, Finset.mem_range] at hk ⊢
      exact ⟨by omega, (hR j k hjk hk.1).trans_lt hk.2⟩
    have hidx : (Finset.range (nL + 1 + nR)).filter (fun k => rawPos nL pL pR k < y) =
        Finset.range (nL + 1 + DR.card) := by
      have hmR : DR.card ≤ nR := (Finset.card_filter_le _ _).trans (Finset.card_range _).le
      ext k
      simp only [Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨hk, hky⟩
        by_cases hk1 : k < nL + 1
        · omega
        · have hmem : k - nL - 1 ∈ DR := by
            rw [hDRdef, Finset.mem_filter, Finset.mem_range]
            unfold rawPos at hky
            rw [ite_eq_right (by omega), ite_eq_right (by omega)] at hky
            exact ⟨by omega, hky⟩
          rw [hDR, Finset.mem_range] at hmem
          omega
      · intro hk
        refine ⟨by omega, ?_⟩
        unfold rawPos
        split_ifs with h1 h2
        · exact (hL0 _ (by omega)).trans_lt hpos
        · exact hpos
        · have hmem : k - nL - 1 ∈ DR := by rw [hDR, Finset.mem_range]; omega
          rw [hDRdef, Finset.mem_filter] at hmem
          exact hmem.2
    rw [hidx, Finset.card_range, ite_eq_right (not_lt.2 hpos.le)]
    unfold wordHeight
    rw [ite_eq_right (by omega), show nL + 1 + DR.card - nL - 1 = DR.card by omega]
    have hfe : (Finset.range nR).filter (fun j => pR j ≤ y) = DR := by
      rw [hDRdef]
      refine Finset.filter_congr fun j hj => ⟨fun hle => lt_of_le_of_ne hle fun he => ?_, le_of_lt⟩
      have h2 := hne (nL + 1 + j) (by have := Finset.mem_range.1 hj; omega)
      unfold rawPos at h2
      rw [ite_eq_right (by omega), ite_eq_right (by omega), show nL + 1 + j - nL - 1 = j by omega] at h2
      exact h2 he
    rw [sum_fin_filter_eq nR (fun j => pR j ≤ y) ρR, hfe, hDR, Finset.card_range]

end Fn

/-! ### The mean of the word -/

section Mean

variable {nL nR : ℕ} {pL pR : ℕ → ℝ}

/-- **Every bounded harmonic extension of the force data is the word mean plus the shift** on `ℍ`. -/
theorem eqOn_mean_forceWord (κ : ℝ) (ρL ρR : ℕ → ℝ) (s : ℝ) (h : IsMarkOrder nL nR pL pR) {u : ℂ → ℝ}
    (hu : IsBoundedHarmonicExtension
      (forceBoundaryData κ (fun i : Fin nL => ρL i) (fun j : Fin nR => ρR j) (fun i : Fin nL => pL i)
        (fun j : Fin nR => pR j))
      (forceJumpSet (fun i : Fin nL => pL i) (fun j : Fin nR => pR j)) u) :
    EqOn u (fun z => (forceWord κ nL nR pL pR ρL ρR s).mean z + s) QuantumZipper.H := by
  set c := forceWord κ nL nR pL pR ρL ρR s with hcdef
  have hm := BoundaryWord.isBoundedHarmonicExtension_mean c (isSorted_forceWord κ nL nR pL pR ρL ρR s)
  set S : Set ℝ := insert 0 ((c.jumps : Set ℝ) ∪
    forceJumpSet (fun i : Fin nL => pL i) (fun j : Fin nR => pR j)) with hSdef
  have hSf : S.Finite := by
    refine Set.Finite.insert 0 (c.jumps.finite_toSet.union ?_)
    exact ((Set.finite_range _).union (Set.finite_range _)).insert 0
  have hv : IsBoundedHarmonicExtension
      (forceBoundaryData κ (fun i : Fin nL => ρL i) (fun j : Fin nR => ρR j) (fun i : Fin nL => pL i)
        (fun j : Fin nR => pR j)) S (fun z => c.mean z + s) := by
    obtain ⟨C, hC⟩ := hm.2.1
    refine ⟨fun z hz => (hm.1 z hz).add (InnerProductSpace.harmonicAt_const s),
      ⟨C + |s|, fun z hz => (abs_add_le _ _).trans (by linarith [hC z hz])⟩, fun y hy => ?_⟩
    have hy0 : y ≠ 0 := fun he => hy (he ▸ Set.mem_insert 0 _)
    have hyj : y ∉ c.jumps := fun he => hy (Set.mem_insert_of_mem 0 (Or.inl he))
    have h1 := (hm.2.2 y hyj).add_const s
    rwa [fn_forceWord κ ρL ρR s h hyj hy0, sub_add_cancel] at h1
  have hu' : IsBoundedHarmonicExtension
      (forceBoundaryData κ (fun i : Fin nL => ρL i) (fun j : Fin nR => ρR j) (fun i : Fin nL => pL i)
        (fun j : Fin nR => pR j)) S u :=
    ⟨hu.1, hu.2.1, fun y hy => hu.2.2 y fun he => hy (Set.mem_insert_of_mem 0 (Or.inr he))⟩
  exact PiecewiseConstant.eqOn_of_isBoundedHarmonicExtension hSf hv hu'

/-- The explicit mean of the word. -/
theorem mean_forceWord (κ : ℝ) (nL nR : ℕ) (pL pR ρL ρR : ℕ → ℝ) (s : ℝ) (z : ℂ) :
    (forceWord κ nL nR pL pR ρL ρR s).mean z = wordHeight κ nL ρL ρR s (nL + 1 + nR) +
      ∑ j ∈ Finset.range (nL + 1 + nR), (wordHeight κ nL ρL ρR s j - wordHeight κ nL ρL ρR s (j + 1)) *
        (Complex.arg (z - (cumMax (rawPos nL pL pR) j : ℂ)) / Real.pi) := rfl

/-- A bound for the word mean, independent of the positions and the point. -/
def wordBound (κ : ℝ) (nL nR : ℕ) (ρL ρR : ℕ → ℝ) (s : ℝ) : ℝ :=
  |wordHeight κ nL ρL ρR s (nL + 1 + nR)| +
    ∑ j ∈ Finset.range (nL + 1 + nR), |wordHeight κ nL ρL ρR s j - wordHeight κ nL ρL ρR s (j + 1)|

theorem abs_mean_forceWord_le (κ : ℝ) (nL nR : ℕ) (pL pR ρL ρR : ℕ → ℝ) (s : ℝ) (z : ℂ) :
    |(forceWord κ nL nR pL pR ρL ρR s).mean z| ≤ wordBound κ nL nR ρL ρR s := by
  rw [mean_forceWord]
  refine (abs_add_le _ _).trans (add_le_add le_rfl ((Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun j _ => ?_)))
  rw [abs_mul]
  refine mul_le_of_le_one_right (abs_nonneg _) ?_
  rw [abs_div, abs_of_pos Real.pi_pos]
  exact (div_le_one Real.pi_pos).2 (Complex.abs_arg_le_pi _)

theorem tendsto_rawPos {ι : Type*} {l : Filter ι} {pLs pRs : ι → ℕ → ℝ}
    (hL : ∀ i, Tendsto (fun a => pLs a i) l (𝓝 (pL i))) (hR : ∀ j, Tendsto (fun a => pRs a j) l (𝓝 (pR j))) :
    Tendsto (fun a => rawPos nL (pLs a) (pRs a)) l (𝓝 (rawPos nL pL pR)) := by
  refine tendsto_pi_nhds.2 fun k => ?_
  unfold rawPos
  split_ifs
  · exact hL _
  · exact tendsto_const_nhds
  · exact hR _

/-- **The word mean is continuous in the positions and the point** (at points of `ℍ`). -/
theorem tendsto_mean_forceWord (κ : ℝ) (ρL ρR : ℕ → ℝ) (s : ℝ) {ι : Type*} {l : Filter ι}
    {pLs pRs : ι → ℕ → ℝ} {zs : ι → ℂ} {z : ℂ} (hL : ∀ i, Tendsto (fun a => pLs a i) l (𝓝 (pL i)))
    (hR : ∀ j, Tendsto (fun a => pRs a j) l (𝓝 (pR j))) (hz : Tendsto zs l (𝓝 z)) (hzH : 0 < z.im) :
    Tendsto (fun a => (forceWord κ nL nR (pLs a) (pRs a) ρL ρR s).mean (zs a)) l
      (𝓝 ((forceWord κ nL nR pL pR ρL ρR s).mean z)) := by
  simp only [mean_forceWord]
  refine tendsto_const_nhds.add (tendsto_finsetSum _ fun j _ => tendsto_const_nhds.mul ?_)
  refine Tendsto.div_const ?_ _
  have hpos := ((continuous_cumMax_apply j).tendsto _).comp (tendsto_rawPos (nL := nL) hL hR)
  have hw : Tendsto (fun a => zs a - (cumMax (rawPos nL (pLs a) (pRs a)) j : ℂ)) l
      (𝓝 (z - (cumMax (rawPos nL pL pR) j : ℂ))) :=
    hz.sub ((Complex.continuous_ofReal.tendsto _).comp hpos)
  refine (Complex.continuousAt_arg ?_).tendsto.comp hw
  refine Complex.mem_slitPlane_iff.2 (Or.inr ?_)
  simp only [Complex.sub_im, Complex.ofReal_im, sub_zero]
  exact hzH.ne'

end Mean

/-! ### Measurability -/

theorem measurable_rawPos_apply (nL k : ℕ) :
    Measurable fun p : (ℕ → ℝ) × (ℕ → ℝ) => rawPos nL p.1 p.2 k := by
  unfold rawPos
  split_ifs
  · exact (measurable_pi_apply _).comp measurable_fst
  · exact measurable_const
  · exact (measurable_pi_apply _).comp measurable_snd

theorem measurable_wordHeight_apply (κ : ℝ) (nL k : ℕ) :
    Measurable fun p : (ℕ → ℝ) × (ℕ → ℝ) × ℝ => wordHeight κ nL p.1 p.2.1 p.2.2 k := by
  unfold wordHeight
  split_ifs
  · exact (measurable_const.mul (measurable_const.add (Finset.measurable_sum _ fun i _ =>
      (measurable_pi_apply i).comp measurable_fst))).sub (measurable_snd.comp measurable_snd)
  · exact (measurable_const.mul (measurable_const.add (Finset.measurable_sum _ fun i _ =>
      (measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)))).sub
      (measurable_snd.comp measurable_snd)

/-- **The force word is a measurable function of all its data.** -/
theorem measurable_forceWord (κ : ℝ) {α : Type*} [MeasurableSpace α] {nL nR : α → ℕ}
    {pL pR ρL ρR : α → ℕ → ℝ} {s : α → ℝ} (hnL : Measurable nL) (hnR : Measurable nR) (hpL : Measurable pL)
    (hpR : Measurable pR) (hρL : Measurable ρL) (hρR : Measurable ρR) (hs : Measurable s) :
    Measurable fun a => forceWord κ (nL a) (nR a) (pL a) (pR a) (ρL a) (ρR a) (s a) := by
  set F : ((ℕ → ℝ) × (ℕ → ℝ) × (ℕ → ℝ) × (ℕ → ℝ) × ℝ) × (ℕ × ℕ) → BoundaryWord :=
    fun q => forceWord κ q.2.1 q.2.2 q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2.1 q.1.2.2.2.2 with hFdef
  have hF : Measurable F := by
    refine measurable_from_prod_countable_left fun n => ?_
    refine Measurable.prodMk (measurable_const (a := n.1 + 1 + n.2)) (Measurable.prodMk ?_ ?_)
    · refine measurable_pi_iff.2 fun k => ?_
      have h1 : Measurable fun x : (ℕ → ℝ) × (ℕ → ℝ) × (ℕ → ℝ) × (ℕ → ℝ) × ℝ =>
          rawPos n.1 x.1 x.2.1 := measurable_pi_iff.2 fun j =>
        (measurable_rawPos_apply n.1 j).comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
      exact (continuous_cumMax_apply k).measurable.comp h1
    · refine measurable_pi_iff.2 fun k => ?_
      exact (measurable_wordHeight_apply κ n.1 k).comp
        ((measurable_fst.comp (measurable_snd.comp measurable_snd)).prodMk
          ((measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))).prodMk
            (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))))
  exact hF.comp ((hpL.prodMk (hpR.prodMk (hρL.prodMk (hρR.prodMk hs)))).prodMk (hnL.prodMk hnR))

end StagedLaw

end Exist

end InteractingSLE
