/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RqFar
import InteractingSLE.Spec.Supplement.GW2SdpHeight
import InteractingSLE.Spec.Supplement.GW2WmPos

/-!
# The right angle region of a stopped piece: heights and ranks (decision D33)

PROVE-GW2-ROOTX round 8. The stage word `c' = stopWord κ (c, θ, r)` has its positive labels at the images
`pRs j = markPos (rdrv r) (rtime r) (xR j)` of the old right labels. Off the jumps, a point `z > 0` of `c'` carries
the old height reached by the first `KR z` labels (`fnR_stop`): `KR z = 0` reads the piece's right side `λ − θχ`,
`KR z = k + 1` reads the old height after label `k` (`fnR_stop_eq_old`).

If the flow `markPos` is strictly increasing on `[0, aR]` (the piece does not split the right angle region `(0, aR)`),
the genuine jumps of `c'` in `(0, markPos aR)` are the images of the old labels below `aR`, the seed image counting
only when the piece's right side differs from the old first height (`δR`):

* **`rkR_stop`**: `rkR c' z = (KR z − 1) + δR` when `KR z ≥ 1`;
* `rkR_stop_zero`: `rkR c' z = 0` left of the seed image.

Deterministic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Finset
open scoped NNReal
open QuantumZipper (chiC)

namespace InteractingSLE.Theorem14.GW2Rq

open Restart Exist.Staged Exist.StagedLaw
open PiecewiseConstantBoundaryData (jumpSet leftLim rightLim)

section Right

variable {κ : ℝ} (c : BoundaryWord) (θ : ℝ) (r : RecData)

theorem rightLim_eq_of_gap' {b : ℝ → ℝ} {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J) {p δ x : ℝ}
    (hδ : ∀ z ∈ J, z ∉ Ioo p (p + δ)) (hx : x ∈ Ioo p (p + δ)) : rightLim b p = b x :=
  Sec4.rightLim_eq_of_forall (lt_trans hx.1 hx.2) fun _ ht =>
    Sec4.eq_of_mem_Ioo_of_isPiecewiseConstant hb hδ hx ht

theorem leftLim_eq_of_gap' {b : ℝ → ℝ} {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J) {p δ x : ℝ}
    (hδ : ∀ z ∈ J, z ∉ Ioo (p - δ) p) (hx : x ∈ Ioo (p - δ) p) : leftLim b p = b x :=
  Sec4.leftLim_eq_of_forall (lt_trans hx.1 hx.2) fun _ ht =>
    Sec4.eq_of_mem_Ioo_of_isPiecewiseConstant hb hδ hx ht

/-- The images of the old right labels under the piece's right mark flow. -/
def pRs (j : Fin (flowLineNR c.fn c.jumps 0)) : ℝ := markPos (rdrv r) (rtime r) (flowLineXR c.fn c.jumps 0 j)

/-- The number of old right labels whose images are at most `z`. -/
def KR (z : ℝ) : ℕ := (Finset.univ.filter fun j : Fin (flowLineNR c.fn c.jumps 0) => pRs c r j ≤ z).card

/-- The right seed shift: the seed image counts iff the piece's right side is nondegenerate and its height differs from
the old first right height. -/
def δR (κ : ℝ) : ℕ :=
  if 0 < markPos (rdrv r) (rtime r) 0 ∧ rightLim c.fn 0 ≠ sleLambda κ - θ * chiC κ then 1 else 0

theorem pRs_zero : pRs c r ⟨0, Supp8.GB6.zero_lt_flowLineNR _ _⟩ = markPos (rdrv r) (rtime r) 0 := rfl

theorem monotone_pRs : Monotone (pRs c r) := fun _ _ h =>
  Sec7.StripSideHeightProb.markPos_mono (continuous_rdrv r) (rdrv_zero r) (rtime_nonneg r)
    (GW3Word.flowLineXR_nonneg _ _ _) ((Sec7.StripDet.strictMono_flowLineXR c.fn c.jumps).monotone h)

theorem pRs_le_iff (z : ℝ) (j : Fin (flowLineNR c.fn c.jumps 0)) : pRs c r j ≤ z ↔ (j : ℕ) < KR c r z := by
  have h := mem_iff_lt_card (S := Finset.univ.filter fun j : Fin (flowLineNR c.fn c.jumps 0) => pRs c r j ≤ z)
    (fun j hj k hk => by
      rw [Finset.mem_filter] at hj ⊢
      exact ⟨Finset.mem_univ _, (monotone_pRs c r hk).trans hj.2⟩) j
  unfold KR
  rw [Finset.mem_filter] at h
  simpa only [Finset.mem_univ, true_and] using h

theorem KR_le_card (z : ℝ) : KR c r z ≤ flowLineNR c.fn c.jumps 0 :=
  (Finset.card_filter_le _ _).trans (by rw [Finset.card_univ, Fintype.card_fin])

theorem pRs_mem_jumps (j : Fin (flowLineNR c.fn c.jumps 0)) : pRs c r j ∈ (stopWord κ (c, θ, r)).jumps := by
  have h := GW2Wm.markPos_mem_jumps_stopWord (k := κ) c θ r j.isLt
  rwa [show (padFL 0 0 c.fn c.jumps).1.2 j = flowLineXR c.fn c.jumps 0 j from padFL_fst_snd_fin _ _ j] at h

/-- Every positive jump of the stopped word is an image of an old right label. -/
theorem exists_pRs_eq {y : ℝ} (hy : y ∈ (stopWord κ (c, θ, r)).jumps) (hy0 : 0 < y) :
    ∃ j : Fin (flowLineNR c.fn c.jumps 0), y = pRs c r j := by
  rcases Sec5.CrossCond.StagedFinal.mem_jumps_stopWord hy with ⟨i, hi⟩ | h0 | ⟨j, hj⟩
  · have := Sec7.StripSideHeightProb.markPosL_nonpos (continuous_rdrv r) (rdrv_zero r) (rtime_nonneg r)
      (GW3Word.flowLineXL_nonpos c.fn c.jumps i)
    linarith
  · linarith
  · exact ⟨j, hj⟩

/-- **The heights right of the tip of a stopped word**, read from the first `KR z` labels. -/
theorem fnR_stop {z : ℝ} (hz : 0 < z) (hzJ : z ∉ (stopWord κ (c, θ, r)).jumps) :
    (stopWord κ (c, θ, r)).fn z = sleLambda κ * (1 + ∑ j ∈ Finset.univ.filter
      (fun j : Fin (flowLineNR c.fn c.jumps 0) => (j : ℕ) < KR c r z), flowLineRhoR κ c.fn c.jumps 0 θ j) -
        θ * chiC κ := by
  classical
  have h := fn_forceWord κ (padFL κ θ c.fn c.jumps).2.1 (padFL κ θ c.fn c.jumps).2.2 (θ * chiC κ)
    (Sec7.StripSideHeightProb.isMarkOrder_stopWord c r) hzJ hz.ne'
  refine h.trans ?_
  rw [Sec4.forceBoundaryData_of_nonneg _ _ _ _ hz.le]
  simp only [padFL_fst_snd_fin, padFL_snd_snd_fin]
  have e : Finset.univ.filter (fun j : Fin (flowLineNR c.fn c.jumps 0) =>
      markPos (rdrv r) (rtime r) (flowLineXR c.fn c.jumps 0 j) ≤ z) =
      Finset.univ.filter (fun j : Fin (flowLineNR c.fn c.jumps 0) => (j : ℕ) < KR c r z) :=
    Finset.filter_congr fun j _ => pRs_le_iff c r z j
  rw [e]

/-- **The old heights right of the tip**, read from the labels at most `u`. -/
theorem fn_old_R (hκ : 0 < κ) {u : ℝ} (hu : 0 < u) (huJ : u ∉ c.jumps) :
    c.fn u = sleLambda κ * (1 + ∑ j ∈ Finset.univ.filter
      (fun j : Fin (flowLineNR c.fn c.jumps 0) => flowLineXR c.fn c.jumps 0 j ≤ u),
        flowLineRhoR κ c.fn c.jumps 0 θ j) - θ * chiC κ := by
  have h1 := Exist.forceBoundaryData_flowLine_seed hκ c.isPiecewiseConstantBoundaryData 0 θ hu.ne'
    (by simpa using huJ)
  rw [Sec4.forceBoundaryData_of_nonneg _ _ _ _ hu.le, add_zero] at h1
  linarith

/-- The labels at most a point of the old interval after label `k` are the first `k + 1`. -/
theorem xR_le_iff_of_mem {k : ℕ} (hk : k < flowLineNR c.fn c.jumps 0) {u : ℝ}
    (hu : flowLineXR c.fn c.jumps 0 ⟨k, hk⟩ < u)
    (hu' : ∀ j : Fin (flowLineNR c.fn c.jumps 0), k < (j : ℕ) → u < flowLineXR c.fn c.jumps 0 j)
    (j : Fin (flowLineNR c.fn c.jumps 0)) : flowLineXR c.fn c.jumps 0 j ≤ u ↔ (j : ℕ) < k + 1 := by
  constructor
  · intro h
    by_contra hj
    exact absurd h (not_le.2 (hu' j (by omega)))
  · intro h
    exact ((Sec7.StripDet.strictMono_flowLineXR c.fn c.jumps).monotone
      (Fin.le_def.2 (show (j : ℕ) ≤ k by omega))).trans hu.le

/-- **A point of the stopped word with `KR z = k + 1` carries the old height after label `k`.** -/
theorem fnR_stop_eq_old (hκ : 0 < κ) {z : ℝ} (hz : 0 < z) (hzJ : z ∉ (stopWord κ (c, θ, r)).jumps) {k : ℕ}
    (hK : KR c r z = k + 1) (hk : k < flowLineNR c.fn c.jumps 0) {u : ℝ} (hu0 : 0 < u) (huJ : u ∉ c.jumps)
    (hu : flowLineXR c.fn c.jumps 0 ⟨k, hk⟩ < u)
    (hu' : ∀ j : Fin (flowLineNR c.fn c.jumps 0), k < (j : ℕ) → u < flowLineXR c.fn c.jumps 0 j) :
    (stopWord κ (c, θ, r)).fn z = c.fn u := by
  rw [fnR_stop c θ r hz hzJ, fn_old_R c θ hκ hu0 huJ, hK,
    Finset.filter_congr fun j _ => xR_le_iff_of_mem c hk hu hu' j]

/-- Left of the seed image the stopped word has the piece's right side. -/
theorem fnR_stop_of_lt {z : ℝ} (hz : 0 < z) (hzJ : z ∉ (stopWord κ (c, θ, r)).jumps)
    (hz0 : z < markPos (rdrv r) (rtime r) 0) : (stopWord κ (c, θ, r)).fn z = sleLambda κ - θ * chiC κ := by
  have hK : KR c r z = 0 := by
    by_contra hne
    have := (pRs_le_iff c r z ⟨0, Supp8.GB6.zero_lt_flowLineNR _ _⟩).2 (by simp; omega)
    rw [pRs_zero] at this
    linarith
  rw [fnR_stop c θ r hz hzJ, hK]
  simp

/-- **No genuine jump left of the seed image.** -/
theorem rkR_stop_zero {z : ℝ} (hz0 : z ≤ markPos (rdrv r) (rtime r) 0) : rkR (stopWord κ (c, θ, r)) z = 0 := by
  unfold rkR
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro y hy ⟨hy0, hyz⟩
  obtain ⟨j, rfl⟩ := exists_pRs_eq c θ r (Finset.mem_filter.1 hy).1 hy0
  have := monotone_pRs c r (Fin.le_def.2 (Nat.zero_le (j : ℕ)) : (⟨0, Supp8.GB6.zero_lt_flowLineNR _ _⟩ :
    Fin (flowLineNR c.fn c.jumps 0)) ≤ j)
  rw [pRs_zero] at this
  linarith

/-! ### The region after the seed image, when the region is not split -/

variable {c r}

theorem pRs_lt_iff {aR : ℝ} (hA : StrictMonoOn (markPos (rdrv r) (rtime r)) (Icc 0 aR))
    {i j : Fin (flowLineNR c.fn c.jumps 0)} (hi : flowLineXR c.fn c.jumps 0 i ≤ aR)
    (hj : flowLineXR c.fn c.jumps 0 j ≤ aR) : pRs c r i < pRs c r j ↔ i < j := by
  have hsm := Sec7.StripDet.strictMono_flowLineXR c.fn c.jumps
  constructor
  · intro h
    by_contra hij
    have := monotone_pRs c r (not_lt.1 hij)
    linarith
  · intro h
    exact hA ⟨GW3Word.flowLineXR_nonneg _ _ _, hi⟩ ⟨GW3Word.flowLineXR_nonneg _ _ _, hj⟩ (hsm h)

theorem pRs_lt_markPos {aR : ℝ} (hA : StrictMonoOn (markPos (rdrv r) (rtime r)) (Icc 0 aR))
    {j : Fin (flowLineNR c.fn c.jumps 0)} (hj : flowLineXR c.fn c.jumps 0 j < aR) :
    pRs c r j < markPos (rdrv r) (rtime r) aR :=
  hA ⟨GW3Word.flowLineXR_nonneg _ _ _, hj.le⟩ ⟨(GW3Word.flowLineXR_nonneg _ _ _).trans hj.le, le_rfl⟩ hj

theorem markPos_le_pRs {aR : ℝ} (haR : 0 ≤ aR) {j : Fin (flowLineNR c.fn c.jumps 0)}
    (hj : aR ≤ flowLineXR c.fn c.jumps 0 j) : markPos (rdrv r) (rtime r) aR ≤ pRs c r j :=
  Sec7.StripSideHeightProb.markPos_mono (continuous_rdrv r) (rdrv_zero r) (rtime_nonneg r) haR hj

/-- Below the image of `aR`, only labels inside the region are counted. -/
theorem KR_le_pRc {aR : ℝ} (haR : 0 ≤ aR) {z : ℝ} (hz : z < markPos (rdrv r) (rtime r) aR) :
    KR c r z ≤ pRc c aR := by
  by_contra h
  push Not at h
  have hlt : KR c r z - 1 < flowLineNR c.fn c.jumps 0 := by have := KR_le_card c r z; omega
  have hmem := (pRs_le_iff c r z ⟨KR c r z - 1, hlt⟩).2 (by simp; omega)
  have hout : ¬ flowLineXR c.fn c.jumps 0 ⟨KR c r z - 1, hlt⟩ < aR := by
    rw [xR_lt_iff]; simp; omega
  have := markPos_le_pRs (c := c) (r := r) haR (not_lt.1 hout)
  linarith

/-- The right seed weight at angle `θ` reads the old first height. -/
theorem seedR_height (hκ : 0 < κ) :
    sleLambda κ * (1 + flowLineRhoR κ c.fn c.jumps 0 θ ⟨0, Supp8.GB6.zero_lt_flowLineNR _ _⟩) - θ * chiC κ =
      rightLim c.fn 0 := by
  have hlam : sleLambda κ ≠ 0 := (Sec4.sleLambda_pos hκ).ne'
  change sleLambda κ * (1 + ((rightLim c.fn 0 + θ * chiC κ) / sleLambda κ - 1)) - θ * chiC κ = _
  field_simp
  ring

/-- A right label after the seed is a genuine jump: its weight is nonzero. -/
theorem flowLineRhoR_ne_zero (hκ : 0 < κ) {j : Fin (flowLineNR c.fn c.jumps 0)} (hj : (j : ℕ) ≠ 0) :
    flowLineRhoR κ c.fn c.jumps 0 θ j ≠ 0 := by
  have hlam : sleLambda κ ≠ 0 := (Sec4.sleLambda_pos hκ).ne'
  obtain ⟨j, hj'⟩ := j
  rcases j with _ | k
  · exact absurd rfl hj
  · set s := (jumpSet c.fn c.jumps).filter ((0 : ℝ) < ·) with hs
    have hk : k < s.card := by
      have e : flowLineNR c.fn c.jumps 0 = s.card + 1 := rfl
      omega
    have e : flowLineRhoR κ c.fn c.jumps 0 θ ⟨k + 1, hj'⟩ =
        (rightLim c.fn (s.orderEmbOfFin rfl ⟨k, hk⟩) - leftLim c.fn (s.orderEmbOfFin rfl ⟨k, hk⟩)) /
          sleLambda κ := rfl
    rw [e]
    have hmem := (Finset.mem_filter.1 (s.orderEmbOfFin_mem rfl ⟨k, hk⟩)).1
    have hne := (Finset.mem_filter.1 hmem).2
    exact div_ne_zero (sub_ne_zero.2 hne.symm) hlam

/-- The sum over the first `k + 1` labels splits off label `k`. -/
theorem sum_filter_succ (f : Fin (flowLineNR c.fn c.jumps 0) → ℝ) {k : ℕ}
    (hk : k < flowLineNR c.fn c.jumps 0) :
    ∑ j ∈ Finset.univ.filter (fun j : Fin (flowLineNR c.fn c.jumps 0) => (j : ℕ) < k + 1), f j =
      (∑ j ∈ Finset.univ.filter (fun j : Fin (flowLineNR c.fn c.jumps 0) => (j : ℕ) < k), f j) + f ⟨k, hk⟩ := by
  have e : Finset.univ.filter (fun j : Fin (flowLineNR c.fn c.jumps 0) => (j : ℕ) < k + 1) =
      insert ⟨k, hk⟩ (Finset.univ.filter (fun j : Fin (flowLineNR c.fn c.jumps 0) => (j : ℕ) < k)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  rw [e, Finset.sum_insert (by simp), add_comm]

variable (c r)

/-- **The one-sided limits of a stopped word at a label image inside an unsplit region.** -/
theorem lims_pRs {aR : ℝ} (hA : StrictMonoOn (markPos (rdrv r) (rtime r)) (Icc 0 aR))
    {j : ℕ} (hj : j < pRc c aR) (hj0 : 0 < pRs c r ⟨j, (hj.trans_le (pRc_le c aR))⟩) :
    rightLim (stopWord κ (c, θ, r)).fn (pRs c r ⟨j, hj.trans_le (pRc_le c aR)⟩) =
        sleLambda κ * (1 + ∑ i ∈ Finset.univ.filter
          (fun i : Fin (flowLineNR c.fn c.jumps 0) => (i : ℕ) < j + 1), flowLineRhoR κ c.fn c.jumps 0 θ i) -
          θ * chiC κ ∧
      leftLim (stopWord κ (c, θ, r)).fn (pRs c r ⟨j, hj.trans_le (pRc_le c aR)⟩) =
        sleLambda κ * (1 + ∑ i ∈ Finset.univ.filter
          (fun i : Fin (flowLineNR c.fn c.jumps 0) => (i : ℕ) < j), flowLineRhoR κ c.fn c.jumps 0 θ i) -
          θ * chiC κ := by
  classical
  have hpR := pRc_le c aR
  have hjN : j < flowLineNR c.fn c.jumps 0 := hj.trans_le hpR
  set c' := stopWord κ (c, θ, r) with hc'
  have hb' := c'.isPiecewiseConstantBoundaryData
  set y := pRs c r ⟨j, hjN⟩ with hy
  have hxin : ∀ i : Fin (flowLineNR c.fn c.jumps 0), (i : ℕ) < pRc c aR → flowLineXR c.fn c.jumps 0 i < aR :=
    fun i hi => (xR_lt_iff c aR i).2 hi
  have hyA : y < markPos (rdrv r) (rtime r) aR := pRs_lt_markPos hA (hxin ⟨j, hjN⟩ hj)
  have haR : 0 ≤ aR := (GW3Word.flowLineXR_nonneg _ _ _).trans (hxin ⟨j, hjN⟩ hj).le
  -- the next stop to the right
  set nxt : ℝ := if h : j + 1 < pRc c aR then pRs c r ⟨j + 1, h.trans_le hpR⟩ else markPos (rdrv r) (rtime r) aR
    with hnxt
  have hynxt : y < nxt := by
    rw [hnxt]
    split_ifs with h
    · exact (pRs_lt_iff hA (hxin _ hj).le (hxin _ h).le).2 (Fin.lt_def.2 (by simp))
    · exact hyA
  have hnxtA : nxt ≤ markPos (rdrv r) (rtime r) aR := by
    rw [hnxt]
    split_ifs with h
    · exact (pRs_lt_markPos hA (hxin _ h)).le
    · exact le_rfl
  have hge : ∀ i : Fin (flowLineNR c.fn c.jumps 0), j < (i : ℕ) → nxt ≤ pRs c r i := by
    intro i hi
    by_cases hia : flowLineXR c.fn c.jumps 0 i < aR
    · have hi' := (xR_lt_iff c aR i).1 hia
      have h1 : j + 1 < pRc c aR := by omega
      rw [hnxt]
      simp only [h1, ↓reduceDIte]
      exact monotone_pRs c r (Fin.le_def.2 (by simp; omega))
    · exact hnxtA.trans (markPos_le_pRs haR (not_lt.1 hia))
  -- no jumps of the stopped word strictly between `y` and `nxt`
  have hgapR : ∀ t ∈ c'.jumps, t ∉ Ioo y (y + (nxt - y)) := by
    intro t ht htI
    have ht0 : 0 < t := hj0.trans htI.1
    obtain ⟨i, rfl⟩ := exists_pRs_eq c θ r ht ht0
    rw [add_sub_cancel] at htI
    by_cases hij : (i : ℕ) ≤ j
    · have := monotone_pRs c r (Fin.le_def.2 hij : i ≤ ⟨j, hjN⟩)
      linarith [htI.1]
    · have := hge i (by omega)
      linarith [htI.2]
  obtain ⟨z₁, hz₁a, hz₁b, hz₁J⟩ := Sec4.exists_mem_Ioo_not_mem c'.jumps hynxt
  have hKz₁ : KR c r z₁ = j + 1 := by
    apply le_antisymm
    · by_contra h
      push Not at h
      have hlt : j + 1 < flowLineNR c.fn c.jumps 0 := by have := KR_le_card c r z₁; omega
      have hmem := (pRs_le_iff c r z₁ ⟨j + 1, hlt⟩).2 (by simp; omega)
      have := hge ⟨j + 1, hlt⟩ (by simp)
      linarith
    · have := (pRs_le_iff c r z₁ ⟨j, hjN⟩).1 hz₁a.le
      simp at this
      omega
  refine ⟨?_, ?_⟩
  · rw [rightLim_eq_of_gap' hb' hgapR ⟨hz₁a, by rw [add_sub_cancel]; exact hz₁b⟩,
      fnR_stop c θ r (hj0.trans hz₁a) hz₁J, hKz₁]
  · -- the previous stop to the left
    set prv : ℝ := if h : 0 < j then pRs c r ⟨j - 1, by omega⟩ else 0 with hprv
    have hprvy : prv < y := by
      rw [hprv]
      split_ifs with h
      · exact (pRs_lt_iff hA (hxin _ (by simp; omega)).le (hxin _ hj).le).2 (Fin.lt_def.2 (by simp; omega))
      · exact hj0
    have hprv0 : 0 ≤ prv := by
      rw [hprv]
      split_ifs with h
      · exact Sec7.StripSideHeightProb.markPos_nonneg (continuous_rdrv r) (rdrv_zero r) (rtime_nonneg r)
          (GW3Word.flowLineXR_nonneg _ _ _)
      · exact le_rfl
    have hle : ∀ i : Fin (flowLineNR c.fn c.jumps 0), (i : ℕ) < j → pRs c r i ≤ prv := by
      intro i hi
      have h : 0 < j := by omega
      rw [hprv]
      simp only [h, ↓reduceDIte]
      exact monotone_pRs c r (Fin.le_def.2 (by simp; omega))
    have hgapL : ∀ t ∈ c'.jumps, t ∉ Ioo (y - (y - prv)) y := by
      intro t ht htI
      rw [sub_sub_cancel] at htI
      have ht0 : 0 < t := lt_of_le_of_lt hprv0 htI.1
      obtain ⟨i, rfl⟩ := exists_pRs_eq c θ r ht ht0
      by_cases hij : (i : ℕ) < j
      · have := hle i hij
        linarith [htI.1]
      · have := monotone_pRs c r (Fin.le_def.2 (not_lt.1 hij) : (⟨j, hjN⟩ : Fin _) ≤ i)
        linarith [htI.2]
    obtain ⟨z₀, hz₀a, hz₀b, hz₀J⟩ := Sec4.exists_mem_Ioo_not_mem c'.jumps hprvy
    have hKz₀ : KR c r z₀ = j := by
      apply le_antisymm
      · by_contra h
        push Not at h
        have hmem := (pRs_le_iff c r z₀ ⟨j, hjN⟩).2 (by simp; omega)
        linarith
      · rcases Nat.eq_zero_or_pos j with h0 | hpos
        · omega
        · have := (pRs_le_iff c r z₀ ⟨j - 1, by omega⟩).1 ((hle ⟨j - 1, by omega⟩ (by simp; omega)).trans hz₀a.le)
          simp at this
          omega
    rw [leftLim_eq_of_gap' hb' hgapL ⟨by rw [sub_sub_cancel]; exact hz₀a, hz₀b⟩,
      fnR_stop c θ r (lt_of_le_of_lt hprv0 hz₀a) hz₀J, hKz₀]

/-- The first `K` elements of `Fin n`. -/
theorem card_filter_val_lt {n K : ℕ} (hK : K ≤ n) : (Finset.univ.filter fun j : Fin n => (j : ℕ) < K).card = K := by
  have e : (Finset.univ.filter fun j : Fin n => (j : ℕ) < K).image Fin.val = Finset.range K := by
    ext m
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range]
    constructor
    · rintro ⟨j, hj, rfl⟩; exact hj
    · intro hm; exact ⟨⟨m, by omega⟩, hm, rfl⟩
  rw [← Finset.card_image_of_injective _ Fin.val_injective, e, Finset.card_range]

/-- **The rank of a point of an unsplit right region after the seed image.** -/
theorem rkR_stop (hκ : 0 < κ) {aR : ℝ} (haR : 0 ≤ aR) (hA : StrictMonoOn (markPos (rdrv r) (rtime r)) (Icc 0 aR))
    {z : ℝ} (hz : z < markPos (rdrv r) (rtime r) aR) (hzJ : z ∉ (stopWord κ (c, θ, r)).jumps) (hK : 1 ≤ KR c r z) :
    rkR (stopWord κ (c, θ, r)) z = (KR c r z - 1) + δR c θ r κ := by
  classical
  have hpR := pRc_le c aR
  have hKp := KR_le_pRc (c := c) (r := r) haR hz
  have hxin : ∀ i : Fin (flowLineNR c.fn c.jumps 0), (i : ℕ) < pRc c aR → flowLineXR c.fn c.jumps 0 i < aR :=
    fun i hi => (xR_lt_iff c aR i).2 hi
  set c' := stopWord κ (c, θ, r) with hc'
  set D : Prop := 0 < markPos (rdrv r) (rtime r) 0 ∧ rightLim c.fn 0 ≠ sleLambda κ - θ * chiC κ with hD
  set S := Finset.univ.filter (fun j : Fin (flowLineNR c.fn c.jumps 0) => (j : ℕ) < KR c r z ∧ ((j : ℕ) ≠ 0 ∨ D))
    with hS
  have hinj : Set.InjOn (pRs c r) (S : Set (Fin (flowLineNR c.fn c.jumps 0))) := by
    intro i hi j hj hij
    have hi' := (Finset.mem_filter.1 hi).2.1
    have hj' := (Finset.mem_filter.1 hj).2.1
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have := (pRs_lt_iff hA (hxin i (by omega)).le (hxin j (by omega)).le).2 h
      linarith
    · have := (pRs_lt_iff hA (hxin j (by omega)).le (hxin i (by omega)).le).2 h
      linarith
  have hmp0 : 0 ≤ markPos (rdrv r) (rtime r) 0 :=
    Sec7.StripSideHeightProb.markPos_nonneg (continuous_rdrv r) (rdrv_zero r) (rtime_nonneg r) le_rfl
  have hseed : ∀ hlt : 0 < pRs c r ⟨0, Supp8.GB6.zero_lt_flowLineNR _ _⟩,
      rightLim c'.fn (pRs c r ⟨0, Supp8.GB6.zero_lt_flowLineNR _ _⟩) = rightLim c.fn 0 ∧
        leftLim c'.fn (pRs c r ⟨0, Supp8.GB6.zero_lt_flowLineNR _ _⟩) = sleLambda κ - θ * chiC κ := by
    intro hlt
    have hl := lims_pRs (κ := κ) c θ r hA (j := 0) (by omega) hlt
    have e : Finset.univ.filter (fun i : Fin (flowLineNR c.fn c.jumps 0) => (i : ℕ) < 0 + 1) =
        {⟨0, Supp8.GB6.zero_lt_flowLineNR _ _⟩} := by
      ext i; simp [Fin.ext_iff]
    have e0 : Finset.univ.filter (fun i : Fin (flowLineNR c.fn c.jumps 0) => (i : ℕ) < 0) = ∅ := by
      ext i; simp
    refine ⟨?_, ?_⟩
    · rw [hl.1, e, Finset.sum_singleton, seedR_height θ hκ]
    · rw [hl.2, e0, Finset.sum_empty]; ring
  have himg : (jumpSet c'.fn c'.jumps).filter (fun y => 0 < y ∧ y < z) = S.image (pRs c r) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_image, hS, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hyJ, hy0, hyz⟩
      obtain ⟨j, rfl⟩ := exists_pRs_eq c θ r (Finset.mem_filter.1 hyJ).1 hy0
      have hjK := (pRs_le_iff c r z j).1 hyz.le
      refine ⟨j, ⟨hjK, ?_⟩, rfl⟩
      by_cases hj0 : (j : ℕ) = 0
      · right
        have hj : j = ⟨0, Supp8.GB6.zero_lt_flowLineNR _ _⟩ := Fin.ext hj0
        subst hj
        refine ⟨by rw [← pRs_zero]; exact hy0, fun hH => ?_⟩
        have hgen := (Finset.mem_filter.1 hyJ).2
        obtain ⟨h1, h2⟩ := hseed hy0
        exact hgen (by rw [h1, h2, hH])
      · exact Or.inl hj0
    · rintro ⟨j, ⟨hjK, hjD⟩, rfl⟩
      have hjN : (j : ℕ) < pRc c aR := by omega
      have hpos : 0 < pRs c r j := by
        by_cases hj0 : (j : ℕ) = 0
        · have hj : j = ⟨0, Supp8.GB6.zero_lt_flowLineNR _ _⟩ := Fin.ext hj0
          rw [hj, pRs_zero]
          rcases hjD with h | h
          · exact absurd hj0 h
          · exact h.1
        · have h0 : (⟨0, Supp8.GB6.zero_lt_flowLineNR _ _⟩ : Fin (flowLineNR c.fn c.jumps 0)) < j :=
            Fin.lt_def.2 (Nat.pos_of_ne_zero hj0)
          have := (pRs_lt_iff hA (hxin _ (by simp; omega)).le (hxin j hjN).le).2 h0
          rw [pRs_zero] at this
          exact lt_of_le_of_lt hmp0 this
      have hmemJ := pRs_mem_jumps c θ r (κ := κ) j
      have hlez := (pRs_le_iff c r z j).2 hjK
      have hltz : pRs c r j < z := lt_of_le_of_ne hlez fun h => hzJ (h ▸ hmemJ)
      refine ⟨Finset.mem_filter.2 ⟨hmemJ, ?_⟩, hpos, hltz⟩
      by_cases hj0 : (j : ℕ) = 0
      · have hj : j = ⟨0, Supp8.GB6.zero_lt_flowLineNR _ _⟩ := Fin.ext hj0
        subst hj
        obtain ⟨h1, h2⟩ := hseed hpos
        rw [h1, h2]
        rcases hjD with h | h
        · exact absurd hj0 h
        · exact fun he => h.2 he.symm
      · obtain ⟨j, hjlt⟩ := j
        have hl := lims_pRs (κ := κ) c θ r hA (j := j) hjN hpos
        rw [hl.1, hl.2, sum_filter_succ (fun i => flowLineRhoR κ c.fn c.jumps 0 θ i) hjlt]
        intro he
        have hne := flowLineRhoR_ne_zero (c := c) θ hκ (j := ⟨j, hjlt⟩) hj0
        have hlam : sleLambda κ ≠ 0 := (Sec4.sleLambda_pos hκ).ne'
        apply hne
        have : sleLambda κ * flowLineRhoR κ c.fn c.jumps 0 θ ⟨j, hjlt⟩ = 0 := by linarith
        rcases mul_eq_zero.1 this with h | h
        · exact absurd h hlam
        · exact h
  unfold rkR
  rw [himg, Finset.card_image_of_injOn hinj]
  have hKN : KR c r z ≤ flowLineNR c.fn c.jumps 0 := KR_le_card c r z
  unfold δR
  split_ifs with hDd
  · have e : S = Finset.univ.filter (fun j : Fin (flowLineNR c.fn c.jumps 0) => (j : ℕ) < KR c r z) := by
      rw [hS]
      exact Finset.filter_congr fun j _ => ⟨fun h => h.1, fun h => ⟨h, Or.inr hDd⟩⟩
    rw [e, card_filter_val_lt hKN]
    omega
  · have e : S = (Finset.univ.filter (fun j : Fin (flowLineNR c.fn c.jumps 0) => (j : ℕ) < KR c r z)).erase
        ⟨0, Supp8.GB6.zero_lt_flowLineNR _ _⟩ := by
      ext j
      simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, ne_eq, Fin.ext_iff]
      constructor
      · rintro ⟨h1, h2 | h2⟩
        · exact ⟨h2, h1⟩
        · exact absurd h2 hDd
      · rintro ⟨h1, h2⟩
        exact ⟨h2, Or.inl h1⟩
    rw [e, Finset.card_erase_of_mem (Finset.mem_filter.2 ⟨Finset.mem_univ _, by simp; omega⟩),
      card_filter_val_lt hKN]
    omega

end Right

end InteractingSLE.Theorem14.GW2Rq
