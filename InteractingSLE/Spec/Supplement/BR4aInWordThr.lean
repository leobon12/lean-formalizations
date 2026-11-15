/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.BR4aInWordMean

/-!
# BR4a's relative words: no continuation threshold (deterministic)

Packet PROVE-T14-BR4A3 (`BR4aChain.BR4aWordDetStatement`, conjuncts (1)–(2); HULLDET §4.1 (c): "the merged weight at
a collision is read from the boundary value just left/right of the tip, so a threshold state of `W` at `q` is one of
`W'` at `t`"). At one original time `t` with relative time `q` (`ConjData`): if the relative chain with the word of the
transformed field is at a continuation threshold, so is the original chain.

The merged weight of the marks at the driver is read off the force datum just right (left) of `0`
(`fbd_near_right`, `fbd_near_left`); the relative marks can reach the relative driver only if the original hull image
touches the driver on that side (`ConjData.nf_R0_le_rightImg`, `ConjData.leftImg_le_nf_L0`); just beside the driver
the two flowed data agree at the images of alive points (`ConjData.alive_case`, `[x < P] = [v < 0]` there).

* `fbd_near_right`, `fbd_near_left`, `exists_pos_le`;
* **`ConjData.not_threshold`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric Finset
open QuantumZipper (H fwdHull chiC)
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.BR4aIn

open BR4aPath BR4aChain ConformalImage ConformalImageFull Supp8.HullDetGen Sec5.CrossRestart MartChar.RealFlow

/-- **The force datum just right of the driver** is `λ (1 + Σ_{marks at 0} ρ)`. -/
theorem fbd_near_right (κ : ℝ) {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (pL : Fin nL → ℝ)
    {pR : Fin nR → ℝ} (hpR : ∀ j, 0 ≤ pR j) {Y : ℝ} (hY0 : 0 < Y) (hY : ∀ j, 0 < pR j → Y < pR j) :
    forceBoundaryData κ ρL ρR pL pR Y = Real.pi / Real.sqrt κ * (1 + ∑ j ∈ univ.filter (fun j => pR j = 0), ρR j) := by
  unfold forceBoundaryData
  simp only [not_lt.2 hY0.le, ↓reduceIte]
  congr 3
  refine Finset.filter_congr fun j _ => ⟨fun h => ?_, fun h => by rw [h]; exact hY0.le⟩
  rcases (hpR j).lt_or_eq with hp | hp
  · exact absurd h (not_le.2 (hY j hp))
  · exact hp.symm

/-- **The force datum just left of the driver** is `−λ (1 + Σ_{marks at 0} ρ)`. -/
theorem fbd_near_left (κ : ℝ) {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) {pL : Fin nL → ℝ}
    (pR : Fin nR → ℝ) (hpL : ∀ i, pL i ≤ 0) {Y : ℝ} (hY0 : Y < 0) (hY : ∀ i, pL i < 0 → pL i < Y) :
    forceBoundaryData κ ρL ρR pL pR Y =
      -(Real.pi / Real.sqrt κ) * (1 + ∑ i ∈ univ.filter (fun i => pL i = 0), ρL i) := by
  unfold forceBoundaryData
  simp only [hY0, ↓reduceIte]
  congr 3
  refine Finset.filter_congr fun i _ => ⟨fun h => ?_, fun h => by rw [h]; exact hY0⟩
  rcases (hpL i).lt_or_eq with hp | hp
  · exact absurd h (not_lt.2 (hY i hp).le)
  · exact hp

/-- A finite family has a positive lower bound on its positive values. -/
theorem exists_pos_le {n : ℕ} (p : Fin n → ℝ) : ∃ δ > 0, ∀ j, 0 < p j → δ ≤ p j := by
  set S := (univ.filter fun j => 0 < p j).image p with hS
  by_cases hne : S.Nonempty
  · refine ⟨S.min' hne, ?_, fun j hj => S.min'_le _ (Finset.mem_image.2 ⟨j, by simp [hj], rfl⟩)⟩
    obtain ⟨j, hj, he⟩ := Finset.mem_image.1 (S.min'_mem hne)
    rw [← he]
    exact (Finset.mem_filter.1 hj).2
  · refine ⟨1, one_pos, fun j hj => absurd ⟨p j, Finset.mem_image.2 ⟨j, by simp [hj], rfl⟩⟩ hne⟩

namespace ConjData

variable {w u : ℝ → ℝ} {t q v α κN P : ℝ}

/-- `P` is off the driver, on the side of `v`'s sign. -/
theorem side_P (h : ConjData w u t q v α κN P) : (v < 0 ∧ w t < P) ∨ (0 < v ∧ P < w t) := by
  rcases lt_or_gt_of_ne h.hv with hv | hv
  · exact Or.inl ⟨hv, h.w_le_rightImg.trans_lt (h.rightImg_lt_P hv)⟩
  · exact Or.inr ⟨hv, (h.P_lt_leftImg hv).trans_le h.leftImg_le_w⟩

/-- Near the driver, on the driver's side of `P`, the indicator `[x < P]` is `[v < 0]`. -/
theorem ite_near (h : ConjData w u t q v α κN P) {x : ℝ} (hx : |x - w t| < |P - w t|) :
    (if x < P then Real.pi else 0) = if v < 0 then Real.pi else 0 := by
  rcases h.side_P with ⟨hv, hP⟩ | ⟨hv, hP⟩
  · rw [abs_of_pos (by linarith : 0 < P - w t)] at hx
    have : x < P := by have := le_abs_self (x - w t); linarith
    simp only [this, hv, ↓reduceIte]
  · rw [abs_of_neg (by linarith : P - w t < 0)] at hx
    have : ¬ x < P := by have := neg_abs_le (x - w t); linarith
    simp only [this, not_lt.2 hv.le, ↓reduceIte]

/-- `N` is continuous at `w_t`: near `w_t`, `N x − u_q` is small. -/
theorem exists_nf_near (h : ConjData w u t q v α κN P) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε > 0, ∀ x : ℝ, |x - w t| < ε → |α - κN / (x - P) - u q| < δ := by
  have hwP : w t - P ≠ 0 := by
    rcases h.side_P with ⟨-, hP⟩ | ⟨-, hP⟩ <;> [exact (sub_neg.2 hP).ne; exact (sub_pos.2 hP).ne']
  have hc : ContinuousAt (fun x : ℝ => α - κN / (x - P) - u q) (w t) :=
    (continuousAt_const.sub (continuousAt_const.div (continuousAt_id.sub continuousAt_const) hwP)).sub
      continuousAt_const
  obtain ⟨ε, hε, hball⟩ := Metric.continuousAt_iff.1 hc δ hδ
  refine ⟨ε, hε, fun x hx => ?_⟩
  have := hball (show dist x (w t) < ε by rwa [Real.dist_eq])
  rw [Real.dist_eq, ← h.hdrv, sub_self, sub_zero] at this
  exact this

/-- **No relative continuation threshold**: if the relative chain with the word of the transformed field is at a
continuation threshold at `q`, the original chain is at one at `t`. -/
theorem not_threshold (h : ConjData w u t q v α κN P) {κ : ℝ} (hκ : 0 < κ) {b' : ℝ → ℝ} {J' : Finset ℝ}
    (hb' : IsPiecewiseConstantBoundaryData b' J') {c : Restart.BoundaryWord}
    (h0 : ∀ u₀ uc : ℂ → ℝ, IsBoundedHarmonicExtension b' J' u₀ → IsBoundedHarmonicExtension c.fn c.jumps uc →
      ∀ z ∈ H, uc z = u₀ (mobInv v z) + chiC κ * (brChart v).2.2 (mobInv v z))
    (hnt : ¬ ForceWord.ThresholdCondition (flowLineRhoL κ b' J' 0 0) (flowLineRhoR κ b' J' 0 0) (w t)
      (fun i => -rightImg (fun s => -w s) (-flowLineXL b' J' 0 i) t) (fun j => rightImg w (flowLineXR b' J' 0 j) t)) :
    ¬ ForceWord.ThresholdCondition (flowLineRhoL κ c.fn c.jumps 0 0) (flowLineRhoR κ c.fn c.jumps 0 0) (u q)
      (fun i => -rightImg (fun s => -u s) (-flowLineXL c.fn c.jumps 0 i) q)
      (fun j => rightImg u (flowLineXR c.fn c.jumps 0 j) q) := by
  have hlam : 0 < Real.pi / Real.sqrt κ := div_pos Real.pi_pos (Real.sqrt_pos.2 hκ)
  have hordb := Theorem15.isOrderedForceWord_flowLine b' J' 0
  have hordc := Theorem15.isOrderedForceWord_flowLine c.fn c.jumps 0
  have hun : Continuous fun s => -u s := h.hu.neg
  have hwn : Continuous fun s => -w s := h.hw.neg
  -- centred flowed marks
  set pRb : Fin (flowLineNR b' J' 0) → ℝ := fun j => rightImg w (flowLineXR b' J' 0 j) t - w t with hpRb
  set pLb : Fin (flowLineNL b' J' 0) → ℝ := fun i => -rightImg (fun s => -w s) (-flowLineXL b' J' 0 i) t - w t
    with hpLb
  set pRc : Fin (flowLineNR c.fn c.jumps 0) → ℝ := fun j => rightImg u (flowLineXR c.fn c.jumps 0 j) q - u q
    with hpRc
  set pLc : Fin (flowLineNL c.fn c.jumps 0) → ℝ :=
    fun i => -rightImg (fun s => -u s) (-flowLineXL c.fn c.jumps 0 i) q - u q with hpLc
  have hpRb0 : ∀ j, 0 ≤ pRb j := fun j => by simp only [hpRb]; linarith [le_rightImg h.hw (flowLineXR b' J' 0 j) h.ht]
  have hpRc0 : ∀ j, 0 ≤ pRc j := fun j => by
    simp only [hpRc]; linarith [le_rightImg h.hu (flowLineXR c.fn c.jumps 0 j) h.hq]
  have hpLb0 : ∀ i, pLb i ≤ 0 := fun i => by
    simp only [hpLb]; linarith [le_rightImg hwn (-flowLineXL b' J' 0 i) h.ht]
  have hpLc0 : ∀ i, pLc i ≤ 0 := fun i => by
    simp only [hpLc]; linarith [le_rightImg hun (-flowLineXL c.fn c.jumps 0 i) h.hq]
  obtain ⟨δb, hδb, hδbR⟩ := exists_pos_le pRb
  obtain ⟨δb', hδb', hδbL⟩ := exists_pos_le fun i => -pLb i
  obtain ⟨δc, hδc, hδcR⟩ := exists_pos_le pRc
  obtain ⟨δc', hδc', hδcL⟩ := exists_pos_le fun i => -pLc i
  obtain ⟨ε, hε, hεN⟩ := h.exists_nf_near (lt_min hδc hδc')
  have hPw : 0 < |P - w t| := by
    rcases h.side_P with ⟨-, hP⟩ | ⟨-, hP⟩ <;> exact abs_pos.2 (by linarith)
  set ε₀ := min (min δb δb') (min ε |P - w t|) with hε₀
  have hε₀ : 0 < ε₀ := lt_min (lt_min hδb hδb') (lt_min hε hPw)
  -- the finite bad set
  obtain ⟨E, hE, hstep⟩ := h.step_eq hκ hb' h0
  set B : Set ℝ := ((fun X => X + w t) '' flowJumps b' J' w t) ∪
    ((fun x => α - κN / (x - P) - u q) ⁻¹' flowJumps c.fn c.jumps u q) ∪
    (flowVal w t '' ↑(badPts v J' c)) ∪ {P} with hB
  have hBf : B.Finite :=
    ((((flowJumps_finite b' J' w t).image _).union
      ((flowJumps_finite c.fn c.jumps u q).preimage (injective_nfR h.hκN _).injOn)).union
      ((badPts v J' c).finite_toSet.image _)).union (Set.finite_singleton _)
  -- the identity of the two data near the driver, at a good point `x`
  have hagree : ∀ x : ℝ, x ∉ B → |x - w t| < ε₀ → x ≠ w t →
      (x < w t → x < -rightImg (fun s => -w s) 0 t) → (w t < x → rightImg w 0 t < x) →
      flowData κ c.fn c.jumps u q (α - κN / (x - P) - u q) = flowData κ b' J' w t (x - w t) := by
    intro x hxB hxε hxw hxL hxR
    have hxS : x - w t ∉ flowJumps b' J' w t := fun hm => hxB (Or.inl (Or.inl (Or.inl ⟨_, hm, by ring⟩)))
    have hxS' : α - κN / (x - P) - u q ∉ flowJumps c.fn c.jumps u q :=
      fun hm => hxB (Or.inl (Or.inl (Or.inr hm)))
    have hite := h.ite_near (lt_of_lt_of_le hxε ((min_le_right _ _).trans (min_le_right _ _)))
    rcases lt_or_gt_of_ne hxw with hlt | hgt
    · obtain ⟨y, hy0, hal, hg⟩ := Restart.FCAux79.exists_alive_gImg_eq hwn h.ht (M := -x) (by linarith [hxL hlt])
      have hc := notMem_closure_of_alive_neg h.hw h.hw0 h.ht hal
      have hfv : flowVal w t (-y) = x := by
        rcases (flowVal_spec h.hw h.hw0 h.ht hc (neg_ne_zero.2 hy0.ne')).2 with ⟨hp, -, -⟩ | ⟨-, -, hf⟩
        · linarith
        · rw [hf, neg_neg, hg, neg_neg]
      have hyb : -y ∉ badPts v J' c := fun hm => hxB (Or.inl (Or.inr ⟨-y, hm, hfv⟩))
      obtain ⟨hyJ, -, hyp, hmyJ⟩ := notMem_jumps_of_notMem_badPts h.hv hyb
      have key := h.alive_case hκ hb' h0 hc (neg_ne_zero.2 hy0.ne') hyJ hyp hmyJ (by rwa [hfv])
      have hβ := flowData_flowVal hκ hb' h.hw h.hw0 h.ht hc (neg_ne_zero.2 hy0.ne') hyJ (by rwa [hfv])
      rw [hfv] at key hβ
      rw [hite] at key
      rw [hβ]
      linarith
    · obtain ⟨y, hy0, hal, hg⟩ := Restart.FCAux79.exists_alive_gImg_eq h.hw h.ht (M := x) (hxR hgt)
      have hc := notMem_closure_of_alive h.hw h.hw0 h.ht hal
      have hfv : flowVal w t y = x := by
        rcases (flowVal_spec h.hw h.hw0 h.ht hc hy0.ne').2 with ⟨-, -, hf⟩ | ⟨hn, -, -⟩
        · rw [hf, hg]
        · linarith
      have hyb : y ∉ badPts v J' c := fun hm => hxB (Or.inl (Or.inr ⟨y, hm, hfv⟩))
      obtain ⟨hyJ, -, hyp, hmyJ⟩ := notMem_jumps_of_notMem_badPts h.hv hyb
      have key := h.alive_case hκ hb' h0 hc hy0.ne' hyJ hyp hmyJ (by rwa [hfv])
      have hβ := flowData_flowVal hκ hb' h.hw h.hw0 h.ht hc hy0.ne' hyJ (by rwa [hfv])
      rw [hfv] at key hβ
      rw [hite] at key
      rw [hβ]
      linarith
  intro hthr
  apply hnt
  rcases hthr with hL | hR
  · -- left threshold
    left
    have hfilt : univ.filter (fun i => -rightImg (fun s => -u s) (-flowLineXL c.fn c.jumps 0 i) q = u q) =
        univ.filter (fun i => pLc i = 0) := Finset.filter_congr fun i _ => by simp only [hpLc, sub_eq_zero]
    rw [hfilt] at hL
    have hne : (univ.filter (fun i => pLc i = 0)).Nonempty := by
      by_contra hc
      rw [Finset.not_nonempty_iff_eq_empty] at hc
      rw [hc, Finset.sum_empty] at hL
      norm_num at hL
    obtain ⟨i₀, hi₀⟩ := hne
    have hL0u : -rightImg (fun s => -u s) 0 q = u q := by
      have h1 : rightImg (fun s => -u s) 0 q ≤ rightImg (fun s => -u s) (-flowLineXL c.fn c.jumps 0 i₀) q :=
        rightImg_mono_index hun h.hq (neg_nonneg.2 (hordc.2.1 i₀))
      have h2 := le_rightImg hun 0 h.hq
      have h3 : pLc i₀ = 0 := (Finset.mem_filter.1 hi₀).2
      simp only [hpLc] at h3
      linarith
    -- the original hull image touches the driver on the left
    have hLw : -rightImg (fun s => -w s) 0 t = w t := by
      by_contra hne'
      have hlt : -rightImg (fun s => -w s) 0 t < w t := lt_of_le_of_ne h.leftImg_le_w hne'
      have hside : w t < P ∨ P < -rightImg (fun s => -w s) 0 t := by
        rcases h.side_P with ⟨hv, hP⟩ | ⟨hv, hP⟩
        · exact Or.inl hP
        · exact Or.inr (h.P_lt_leftImg hv)
      have := nfR_lt_nfR (α := α) h.hκN hlt hside
      have h4 := h.leftImg_le_nf_L0
      rw [hL0u, h.hdrv] at h4
      linarith
    -- a good point just left of the driver
    obtain ⟨x, hxI, hxB⟩ := ((Set.Ioo_infinite (show w t - ε₀ < w t by linarith)).sdiff hBf).nonempty
    have hxε : |x - w t| < ε₀ := by rw [abs_lt]; constructor <;> linarith [hxI.1, hxI.2]
    have hxw : x ≠ w t := hxI.2.ne
    have hag := hagree x hxB hxε hxw (fun _ => by rw [hLw]; exact hxI.2) (fun hgt => absurd hgt (not_lt.2 hxI.2.le))
    have hYc : α - κN / (x - P) - u q < 0 := by
      rw [h.hdrv]
      have hside : w t < P ∨ P < x := by
        rcases h.side_P with ⟨-, hP⟩ | ⟨-, hP⟩
        · exact Or.inl hP
        · right
          have := le_abs_self (P - w t)
          have h5 : |x - w t| < |P - w t| := lt_of_lt_of_le hxε ((min_le_right _ _).trans (min_le_right _ _))
          rw [abs_sub_comm] at h5
          rw [abs_of_neg (by linarith : P - w t < 0)] at h5
          have h6 := le_abs_self (w t - x)
          linarith
      linarith [nfR_lt_nfR (α := α) h.hκN hxI.2 hside]
    have hYb : |α - κN / (x - P) - u q| < min δc δc' :=
      hεN x (lt_of_lt_of_le hxε ((min_le_right _ _).trans (min_le_left _ _)))
    have hrel := fbd_near_left κ (flowLineRhoL κ c.fn c.jumps 0 0) (flowLineRhoR κ c.fn c.jumps 0 0) pRc hpLc0 hYc
      (fun i hi => by
        have h1 := hδcL i (by linarith)
        have h2 : |α - κN / (x - P) - u q| < δc' := lt_of_lt_of_le hYb (min_le_right _ _)
        rw [abs_of_neg hYc] at h2
        linarith)
    have horig := fbd_near_left κ (flowLineRhoL κ b' J' 0 0) (flowLineRhoR κ b' J' 0 0) pRb hpLb0
      (show x - w t < 0 by linarith [hxI.2])
      (fun i hi => by
        have h1 := hδbL i (by linarith)
        have h2 : |x - w t| < δb' := lt_of_lt_of_le hxε ((min_le_left _ _).trans (min_le_right _ _))
        rw [abs_of_neg (by linarith [hxI.2])] at h2
        linarith)
    have e1 : flowData κ c.fn c.jumps u q (α - κN / (x - P) - u q) =
        -(Real.pi / Real.sqrt κ) * (1 + ∑ i ∈ univ.filter (fun i => pLc i = 0), flowLineRhoL κ c.fn c.jumps 0 0 i) :=
      hrel
    have e2 : flowData κ b' J' w t (x - w t) =
        -(Real.pi / Real.sqrt κ) * (1 + ∑ i ∈ univ.filter (fun i => pLb i = 0), flowLineRhoL κ b' J' 0 0 i) :=
      horig
    rw [e1, e2] at hag
    have hfiltb : univ.filter (fun i => -rightImg (fun s => -w s) (-flowLineXL b' J' 0 i) t = w t) =
        univ.filter (fun i => pLb i = 0) := Finset.filter_congr fun i _ => by simp only [hpLb, sub_eq_zero]
    rw [hfiltb]
    have hsum : ∑ i ∈ univ.filter (fun i => pLb i = 0), flowLineRhoL κ b' J' 0 0 i =
        ∑ i ∈ univ.filter (fun i => pLc i = 0), flowLineRhoL κ c.fn c.jumps 0 0 i := by
      have := mul_left_cancel₀ (neg_ne_zero.2 hlam.ne') hag
      linarith
    rw [hsum]
    exact hL
  · -- right threshold
    right
    have hfilt : univ.filter (fun j => rightImg u (flowLineXR c.fn c.jumps 0 j) q = u q) =
        univ.filter (fun j => pRc j = 0) := Finset.filter_congr fun j _ => by simp only [hpRc, sub_eq_zero]
    rw [hfilt] at hR
    have hne : (univ.filter (fun j => pRc j = 0)).Nonempty := by
      by_contra hc
      rw [Finset.not_nonempty_iff_eq_empty] at hc
      rw [hc, Finset.sum_empty] at hR
      norm_num at hR
    obtain ⟨j₀, hj₀⟩ := hne
    have hR0u : rightImg u 0 q = u q := by
      have h1 : rightImg u 0 q ≤ rightImg u (flowLineXR c.fn c.jumps 0 j₀) q :=
        rightImg_mono_index h.hu h.hq (hordc.2.2.2 j₀)
      have h2 := le_rightImg h.hu 0 h.hq
      have h3 : pRc j₀ = 0 := (Finset.mem_filter.1 hj₀).2
      simp only [hpRc] at h3
      linarith
    have hRw : rightImg w 0 t = w t := by
      by_contra hne'
      have hlt : w t < rightImg w 0 t := lt_of_le_of_ne h.w_le_rightImg (Ne.symm hne')
      have hside : rightImg w 0 t < P ∨ P < w t := by
        rcases h.side_P with ⟨hv, hP⟩ | ⟨hv, hP⟩
        · exact Or.inl (h.rightImg_lt_P hv)
        · exact Or.inr hP
      have := nfR_lt_nfR (α := α) h.hκN hlt hside
      have h4 := h.nf_R0_le_rightImg
      rw [hR0u, h.hdrv] at h4
      linarith
    obtain ⟨x, hxI, hxB⟩ := ((Set.Ioo_infinite (show w t < w t + ε₀ by linarith)).sdiff hBf).nonempty
    have hxε : |x - w t| < ε₀ := by rw [abs_lt]; constructor <;> linarith [hxI.1, hxI.2]
    have hxw : x ≠ w t := hxI.1.ne'
    have hag := hagree x hxB hxε hxw (fun hlt => absurd hlt (not_lt.2 hxI.1.le)) (fun _ => by rw [hRw]; exact hxI.1)
    have hYc : 0 < α - κN / (x - P) - u q := by
      rw [h.hdrv]
      have hside : x < P ∨ P < w t := by
        rcases h.side_P with ⟨-, hP⟩ | ⟨-, hP⟩
        · left
          have h5 : |x - w t| < |P - w t| := lt_of_lt_of_le hxε ((min_le_right _ _).trans (min_le_right _ _))
          rw [abs_of_pos (by linarith : 0 < P - w t)] at h5
          have h6 := le_abs_self (x - w t)
          linarith
        · exact Or.inr hP
      linarith [nfR_lt_nfR (α := α) h.hκN hxI.1 hside]
    have hYb : |α - κN / (x - P) - u q| < min δc δc' :=
      hεN x (lt_of_lt_of_le hxε ((min_le_right _ _).trans (min_le_left _ _)))
    have hrel := fbd_near_right κ (flowLineRhoL κ c.fn c.jumps 0 0) (flowLineRhoR κ c.fn c.jumps 0 0) pLc hpRc0 hYc
      (fun j hj => by
        have h1 := hδcR j hj
        have h2 : |α - κN / (x - P) - u q| < δc := lt_of_lt_of_le hYb (min_le_left _ _)
        rw [abs_of_pos hYc] at h2
        linarith)
    have horig := fbd_near_right κ (flowLineRhoL κ b' J' 0 0) (flowLineRhoR κ b' J' 0 0) pLb hpRb0
      (show 0 < x - w t by linarith [hxI.1])
      (fun j hj => by
        have h1 := hδbR j hj
        have h2 : |x - w t| < δb := lt_of_lt_of_le hxε ((min_le_left _ _).trans (min_le_left _ _))
        rw [abs_of_pos (by linarith [hxI.1])] at h2
        linarith)
    have e1 : flowData κ c.fn c.jumps u q (α - κN / (x - P) - u q) =
        Real.pi / Real.sqrt κ * (1 + ∑ j ∈ univ.filter (fun j => pRc j = 0), flowLineRhoR κ c.fn c.jumps 0 0 j) :=
      hrel
    have e2 : flowData κ b' J' w t (x - w t) =
        Real.pi / Real.sqrt κ * (1 + ∑ j ∈ univ.filter (fun j => pRb j = 0), flowLineRhoR κ b' J' 0 0 j) :=
      horig
    rw [e1, e2] at hag
    have hfiltb : univ.filter (fun j => rightImg w (flowLineXR b' J' 0 j) t = w t) =
        univ.filter (fun j => pRb j = 0) := Finset.filter_congr fun j _ => by simp only [hpRb, sub_eq_zero]
    rw [hfiltb]
    have hsum : ∑ j ∈ univ.filter (fun j => pRb j = 0), flowLineRhoR κ b' J' 0 0 j =
        ∑ j ∈ univ.filter (fun j => pRc j = 0), flowLineRhoR κ c.fn c.jumps 0 0 j := by
      have := mul_left_cancel₀ hlam.ne' hag
      linarith
    rw [hsum]
    exact hR

end ConjData

end InteractingSLE.Theorem14.BR4aIn
