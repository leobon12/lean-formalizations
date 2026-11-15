/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.BR4aInWordFlow

/-!
# BR4a's relative words: the boundary step identity (★) (deterministic)

Packet PROVE-T14-BR4A3 (`BR4aChain.BR4aWordDetStatement`; HULLDET §Details 4). At one original time `t` with relative
time `q`, under the conjugation `g̃_q ∘ mob v = N ∘ g_t` (`ConjData`), the flowed force data `β` (original word of
`b'` along `w`) and `β'` (word of the transformed field `c` along the relative driver `u`) satisfy

  `β'(N x − u_q) − β(x − w_t) + 2χπ[x < P] = 2χπ[v < 0]`   off a finite set of `x`

(**`step_eq`**). Cases: on the image of the right (left) side of the trace both are `λ` (`−λ`), since `N` maps the
image `[L₀, R₀]` of the hull's sides into the relative one (`nf_R0_le_rightImg`, `leftImg_le_nf_L0`); at the image of
an alive real point `y` the original datum is `b'(y)`, the relative one is `c(mob v y) = b'(y) + χ liftBdry v y`
(`word_eq`), and `liftBdry v y + 2π[y < −1/v] = 2π[v < 0]` (`liftBdry_add`).

* `ConjData`, `ConjData.P_eq`, `ConjData.rightImg_lt_P`, `ConjData.P_lt_leftImg`, `ConjData.inv_real`;
* `flowData`, `flowJumps`: the flowed force datum of a flow-line word and its jump set;
* **`ConjData.nf_R0_le_rightImg`**, **`ConjData.leftImg_le_nf_L0`**;
* **`ConjData.alive_case`**, **`ConjData.step_eq`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open QuantumZipper (H fwdHull chiC)
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.BR4aIn

open BR4aPath BR4aChain ConformalImage ConformalImageFull Supp8.HullDetGen Sec5.CrossRestart MartChar.RealFlow

/-- **The conjugation data at one original time** (the output of `exists_conj`, with the standing assumptions). -/
structure ConjData (w u : ℝ → ℝ) (t q v α κN P : ℝ) : Prop where
  hw : Continuous w
  hw0 : w 0 = 0
  hu : Continuous u
  hu0 : u 0 = 0
  ht : 0 ≤ t
  hq : 0 ≤ q
  hv : v ≠ 0
  hκN : 0 < κN
  hK : mob v '' fwdHull w t = fwdHull u q
  hconj : ∀ z ∈ H \ fwdHull w t, gmap u q (mob v z) = nf α κN P (gmap w t z)
  hp : ((pole v : ℝ) : ℂ) ∉ closure (fwdHull w t)
  hP : (P : ℂ) = bdryVal w (pole v) t
  hdrv : u q = α - κN / (w t - P)

/-- The flowed force datum of the flow-line word of `b` (parameter `κ`) along `w` at time `t`, centred. -/
def flowData (κ : ℝ) (b : ℝ → ℝ) (J : Finset ℝ) (w : ℝ → ℝ) (t : ℝ) : ℝ → ℝ :=
  forceBoundaryData κ (flowLineRhoL κ b J 0 0) (flowLineRhoR κ b J 0 0)
    (fun i => -rightImg (fun s => -w s) (-flowLineXL b J 0 i) t - w t)
    (fun j => rightImg w (flowLineXR b J 0 j) t - w t)

/-- The jump set of `flowData`. -/
def flowJumps (b : ℝ → ℝ) (J : Finset ℝ) (w : ℝ → ℝ) (t : ℝ) : Set ℝ :=
  forceJumpSet (fun i => -rightImg (fun s => -w s) (-flowLineXL b J 0 i) t - w t)
    (fun j => rightImg w (flowLineXR b J 0 j) t - w t)

theorem pole_ne_zero {v : ℝ} (hv : v ≠ 0) : pole v ≠ 0 := by
  simp [pole, hv]

theorem mul_pole_add_one {v : ℝ} (hv : v ≠ 0) : v * pole v + 1 = 0 := by
  simp [pole, mul_inv_cancel₀ hv]

theorem eq_pole_of {v y : ℝ} (hv : v ≠ 0) (h : v * y + 1 = 0) : y = pole v := by
  unfold pole
  field_simp
  linarith

/-- For `v < 0`: `y < −1/v ↔ vy + 1 > 0`. -/
theorem lt_pole_iff_of_neg {v y : ℝ} (hv : v < 0) : y < pole v ↔ 0 < v * y + 1 := by
  have hvv : v * (-v⁻¹) = -1 := by rw [mul_neg, mul_inv_cancel₀ hv.ne]
  unfold pole
  constructor
  · intro h
    have := mul_lt_mul_of_neg_left h hv
    linarith
  · intro h
    by_contra h'
    push Not at h'
    have := mul_le_mul_of_nonpos_left h' hv.le
    linarith

/-- For `v > 0`: `y < −1/v ↔ vy + 1 < 0`. -/
theorem lt_pole_iff_of_pos {v y : ℝ} (hv : 0 < v) : y < pole v ↔ v * y + 1 < 0 := by
  have hvv : v * (-v⁻¹) = -1 := by rw [mul_neg, mul_inv_cancel₀ hv.ne']
  unfold pole
  constructor
  · intro h
    have := mul_lt_mul_of_pos_left h hv
    linarith
  · intro h
    by_contra h'
    push Not at h'
    have := mul_le_mul_of_nonneg_left h' hv.le
    linarith

/-- The closure of a hull lies in a closed ball. -/
theorem exists_closure_fwdHull_subset {w : ℝ → ℝ} (hw : Continuous w) (t : ℝ) :
    ∃ R : ℝ, 0 < R ∧ closure (fwdHull w t) ⊆ closedBall 0 R := by
  obtain ⟨R, hR⟩ := (isBounded_fwdHull hw t).subset_closedBall 0
  refine ⟨max R 1, lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
  exact closure_minimal (hR.trans (closedBall_subset_closedBall (le_max_left _ _))) isClosed_closedBall

/-- A real point beyond a ball radius is off the closed hull. -/
theorem notMem_of_far {K : Set ℂ} {R : ℝ} (hK : closure K ⊆ closedBall 0 R) {y : ℝ} (hy : R < |y|) :
    (y : ℂ) ∉ closure K := fun h => by
  have := hK h
  rw [mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs] at this
  linarith

/-- An alive real point is off the closed hull. -/
theorem notMem_closure_of_alive {w : ℝ → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) {t y : ℝ} (ht : 0 ≤ t)
    (hy : Alive w y t) : (y : ℂ) ∉ closure (fwdHull w t) := by
  obtain ⟨f, hf, -⟩ := Restart.FCAux79.exists_isForwardSol_of_alive hw hw0 ht hy
  exact Supp8.RelTrans.notMem_closure_fwdHull_of_isForwardSol hw ht hf

/-- A point alive for the reflected driver is off the closed hull on the left. -/
theorem notMem_closure_of_alive_neg {w : ℝ → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) {t y : ℝ} (ht : 0 ≤ t)
    (hy : Alive (fun s => -w s) y t) : ((-y : ℝ) : ℂ) ∉ closure (fwdHull w t) := by
  have hwn : Continuous fun s => -w s := hw.neg
  obtain ⟨f, hf, -⟩ := Restart.FCAux79.exists_isForwardSol_of_alive hwn (by simp [hw0]) ht hy
  have hf' := QuantumZipper.RS.isForwardSol_neg hf
  have e : (fun s => -(fun s => -w s) s) = w := by funext s; simp
  rw [e] at hf'
  have h := Supp8.RelTrans.notMem_closure_fwdHull_of_isForwardSol hw ht hf'
  rwa [show -((y : ℝ) : ℂ) = ((-y : ℝ) : ℂ) by push_cast; ring] at h

namespace ConjData

variable {w u : ℝ → ℝ} {t q v α κN P : ℝ}

/-- `P = g_t(−1/v)`. -/
theorem P_eq (h : ConjData w u t q v α κN P) : P = flowVal w t (pole v) := by
  have hs := (flowVal_spec h.hw h.hw0 h.ht h.hp (pole_ne_zero h.hv)).1
  exact Complex.ofReal_injective (h.hP.trans hs)

/-- Real points off the closed hull and off the pole have images other than `P`. -/
theorem flowVal_ne_P (h : ConjData w u t q v α κN P) {y : ℝ} (hy : (y : ℂ) ∉ closure (fwdHull w t))
    (hy0 : y ≠ 0) (hyp : v * y + 1 ≠ 0) : flowVal w t y ≠ P := by
  rw [h.P_eq]
  have hyq : y ≠ pole v := fun he => hyp (by rw [he, mul_pole_add_one h.hv])
  rcases lt_or_gt_of_ne hyq with hlt | hgt
  · exact (flowVal_lt_flowVal h.hw h.hw0 h.ht hy hy0 h.hp (pole_ne_zero h.hv) hlt).ne
  · exact (flowVal_lt_flowVal h.hw h.hw0 h.ht h.hp (pole_ne_zero h.hv) hy hy0 hgt).ne'

/-- `y < −1/v ↔ g_t(y) < P` for real points off the closed hull. -/
theorem lt_P_iff (h : ConjData w u t q v α κN P) {y : ℝ} (hy : (y : ℂ) ∉ closure (fwdHull w t))
    (hy0 : y ≠ 0) : flowVal w t y < P ↔ y < pole v := by
  rw [h.P_eq]
  constructor
  · intro hlt
    by_contra hge
    push Not at hge
    rcases hge.lt_or_eq with hgt | heq
    · exact absurd hlt (not_lt.2 (flowVal_lt_flowVal h.hw h.hw0 h.ht h.hp (pole_ne_zero h.hv) hy hy0 hgt).le)
    · rw [heq] at hlt
      exact lt_irrefl _ hlt
  · exact flowVal_lt_flowVal h.hw h.hw0 h.ht hy hy0 h.hp (pole_ne_zero h.hv)

/-- The image `L₀` of `0⁻` is at most `w_t`, which is at most the image `R₀` of `0⁺`. -/
theorem leftImg_le_w (h : ConjData w u t q v α κN P) : -rightImg (fun s => -w s) 0 t ≤ w t := by
  have := le_rightImg (w := fun s => -w s) h.hw.neg 0 h.ht
  linarith

theorem w_le_rightImg (h : ConjData w u t q v α κN P) : w t ≤ rightImg w 0 t := le_rightImg h.hw 0 h.ht

/-- **For `v < 0`, the hull image lies left of `P`**: `R₀ < P`. -/
theorem rightImg_lt_P (h : ConjData w u t q v α κN P) (hv : v < 0) : rightImg w 0 t < P := by
  have hp0 : 0 < pole v := by simp only [pole, neg_pos, inv_lt_zero]; exact hv
  obtain ⟨r, hr, hd⟩ := exists_disjoint_ball_of_notMem_closure h.hp
  set y₁ : ℝ := pole v - min r (pole v) / 2 with hy₁
  have hm : 0 < min r (pole v) := lt_min hr hp0
  have hy₁0 : 0 < y₁ := by have := min_le_right r (pole v); rw [hy₁]; linarith
  have hy₁p : y₁ < pole v := by rw [hy₁]; linarith
  have hy₁c : (y₁ : ℂ) ∉ closure (fwdHull w t) := by
    have hd' := hd.closure_right isOpen_ball
    refine fun hc => Set.disjoint_left.1 hd' ?_ hc
    rw [mem_ball, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_neg (by linarith)]
    have := min_le_left r (pole v)
    linarith
  rw [h.P_eq]
  exact (rightImg_le_flowVal h.hw h.hw0 h.ht hy₁c hy₁0).trans_lt
    (flowVal_lt_flowVal h.hw h.hw0 h.ht hy₁c hy₁0.ne' h.hp (pole_ne_zero h.hv) hy₁p)

/-- **For `v > 0`, the hull image lies right of `P`**: `P < L₀`. -/
theorem P_lt_leftImg (h : ConjData w u t q v α κN P) (hv : 0 < v) : P < -rightImg (fun s => -w s) 0 t := by
  have hp0 : pole v < 0 := by simp only [pole, neg_lt_zero, inv_pos]; exact hv
  obtain ⟨r, hr, hd⟩ := exists_disjoint_ball_of_notMem_closure h.hp
  set y₁ : ℝ := pole v + min r (-pole v) / 2 with hy₁
  have hm : 0 < min r (-pole v) := lt_min hr (by linarith)
  have hy₁0 : y₁ < 0 := by have := min_le_right r (-pole v); rw [hy₁]; linarith
  have hy₁p : pole v < y₁ := by rw [hy₁]; linarith
  have hy₁c : (y₁ : ℂ) ∉ closure (fwdHull w t) := by
    have hd' := hd.closure_right isOpen_ball
    refine fun hc => Set.disjoint_left.1 hd' ?_ hc
    rw [mem_ball, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith)]
    have := min_le_left r (-pole v)
    linarith
  rw [h.P_eq]
  exact (flowVal_lt_flowVal h.hw h.hw0 h.ht h.hp (pole_ne_zero h.hv) hy₁c hy₁0.ne hy₁p).trans_le
    (flowVal_le_leftImg h.hw h.hw0 h.ht hy₁c hy₁0)

/-- **Relative real points come from original ones**: a real `y' ≠ 0, 1/v` off the closed relative hull is
`mob v y` for `y = y'/(1 − v y')`, off the closed hull, `y ≠ 0`, `vy + 1 ≠ 0`. -/
theorem inv_real (h : ConjData w u t q v α κN P) {y' : ℝ} (hy' : (y' : ℂ) ∉ closure (fwdHull u q))
    (hy'0 : y' ≠ 0) (hy'v : -v * y' + 1 ≠ 0) :
    ((y' / (-v * y' + 1) : ℝ) : ℂ) ∉ closure (fwdHull w t) ∧ y' / (-v * y' + 1) ≠ 0 ∧
      v * (y' / (-v * y' + 1)) + 1 ≠ 0 ∧ y' / (-v * y' + 1) / (v * (y' / (-v * y' + 1)) + 1) = y' := by
  have hK' : mob (-v) '' fwdHull u q = fwdHull w t := by
    rw [← h.hK]
    exact mobInv_image_mob_image v ((QuantumZipper.fwdHull_mono).2 t)
  have h1 := notMem_closure_mob hK' hy' hy'v
  rw [mob_ofReal] at h1
  have hden : v * (y' / (-v * y' + 1)) + 1 = 1 / (-v * y' + 1) := by
    rw [mul_div_assoc', div_add_one hy'v]
    congr 1
    ring
  refine ⟨h1, div_ne_zero hy'0 hy'v, by rw [hden]; exact one_div_ne_zero hy'v, ?_⟩
  rw [hden, div_div_eq_mul_div, div_one, div_mul_cancel₀ _ hy'v]

/-- Every relative real point off the closed relative hull, right of `0`, has image at least `N(R₀)`. -/
theorem nf_R0_le_aux (h : ConjData w u t q v α κN P) {y' : ℝ} (hy' : (y' : ℂ) ∉ closure (fwdHull u q))
    (hy'0 : 0 < y') (hy'v : -v * y' + 1 ≠ 0) :
    α - κN / (rightImg w 0 t - P) ≤ flowVal u q y' := by
  obtain ⟨hy, hy0, hyp, hmy⟩ := h.inv_real hy' hy'0.ne' hy'v
  set y := y' / (-v * y' + 1) with hydef
  obtain ⟨-, -, hfl⟩ := flowVal_conj h.hw h.hw0 h.hu h.hu0 h.ht h.hq h.hK h.hconj hy hy0 hyp
    (h.flowVal_ne_P hy hy0 hyp)
  rw [hmy] at hfl
  rw [hfl]
  rcases lt_or_gt_of_ne hy0 with hyn | hyp'
  · -- `y < 0`: then `v > 0` and `y < −1/v`
    have hpos : y / (v * y + 1) > 0 := by rw [hmy]; exact hy'0
    have hvy : v * y + 1 < 0 := by
      by_contra hc
      push Not at hc
      exact absurd hpos (not_lt.2 (div_nonpos_of_nonpos_of_nonneg hyn.le hc))
    have hv : 0 < v := by
      by_contra hc
      push Not at hc
      nlinarith
    have hyP := (h.lt_P_iff hy hy0).2 ((lt_pole_iff_of_pos hv).2 hvy)
    have hRP : P < rightImg w 0 t := (h.P_lt_leftImg hv).trans_le (h.leftImg_le_w.trans h.w_le_rightImg)
    exact ((nfR_lt h.hκN hRP).trans (lt_nfR h.hκN hyP)).le
  · have hR := rightImg_le_flowVal h.hw h.hw0 h.ht hy hyp'
    rcases lt_or_gt_of_ne h.hv with hv | hv
    · have hvy : 0 < v * y + 1 := by
        by_contra hc
        push Not at hc
        exact absurd (show y / (v * y + 1) > 0 by rw [hmy]; exact hy'0)
          (not_lt.2 (div_nonpos_of_nonneg_of_nonpos hyp'.le hc))
      have hyP := (h.lt_P_iff hy hy0).2 ((lt_pole_iff_of_neg hv).2 hvy)
      exact nfR_le_nfR h.hκN hR (Or.inl hyP)
    · have hRP : P < rightImg w 0 t := (h.P_lt_leftImg hv).trans_le (h.leftImg_le_w.trans h.w_le_rightImg)
      exact nfR_le_nfR h.hκN hR (Or.inr hRP)

/-- Every relative real point off the closed relative hull, left of `0`, has image at most `N(L₀)`. -/
theorem flowVal_le_nf_L0_aux (h : ConjData w u t q v α κN P) {y' : ℝ} (hy' : (y' : ℂ) ∉ closure (fwdHull u q))
    (hy'0 : y' < 0) (hy'v : -v * y' + 1 ≠ 0) :
    flowVal u q y' ≤ α - κN / (-rightImg (fun s => -w s) 0 t - P) := by
  obtain ⟨hy, hy0, hyp, hmy⟩ := h.inv_real hy' hy'0.ne hy'v
  set y := y' / (-v * y' + 1) with hydef
  obtain ⟨-, -, hfl⟩ := flowVal_conj h.hw h.hw0 h.hu h.hu0 h.ht h.hq h.hK h.hconj hy hy0 hyp
    (h.flowVal_ne_P hy hy0 hyp)
  rw [hmy] at hfl
  rw [hfl]
  rcases lt_or_gt_of_ne hy0 with hyn | hyp'
  · have hL := flowVal_le_leftImg h.hw h.hw0 h.ht hy hyn
    rcases lt_or_gt_of_ne h.hv with hv | hv
    · have hLP : -rightImg (fun s => -w s) 0 t < P :=
        (h.leftImg_le_w.trans h.w_le_rightImg).trans_lt (h.rightImg_lt_P hv)
      exact nfR_le_nfR h.hκN hL (Or.inl hLP)
    · have hvy : 0 < v * y + 1 := by
        by_contra hc
        push Not at hc
        exact absurd (show y / (v * y + 1) < 0 by rw [hmy]; exact hy'0)
          (not_lt.2 (div_nonneg_of_nonpos hyn.le hc))
      have hPy : P < flowVal w t y := by
        rcases (lt_or_ge (flowVal w t y) P) with hlt | hge
        · exact absurd ((h.lt_P_iff hy hy0).1 hlt) (fun hlt' => absurd ((lt_pole_iff_of_pos hv).1 hlt')
            (not_lt.2 hvy.le))
        · exact lt_of_le_of_ne hge (h.flowVal_ne_P hy hy0 hyp).symm
      exact nfR_le_nfR h.hκN hL (Or.inr hPy)
  · -- `y > 0`: then `v < 0` and `y > −1/v`
    have hvy : v * y + 1 < 0 := by
      by_contra hc
      push Not at hc
      exact absurd (show y / (v * y + 1) < 0 by rw [hmy]; exact hy'0)
        (not_lt.2 (div_nonneg hyp'.le hc))
    have hv : v < 0 := by
      by_contra hc
      push Not at hc
      nlinarith
    have hPy : P < flowVal w t y := by
      rcases (lt_or_ge (flowVal w t y) P) with hlt | hge
      · exact absurd ((lt_pole_iff_of_neg hv).1 ((h.lt_P_iff hy hy0).1 hlt)) (not_lt.2 hvy.le)
      · exact lt_of_le_of_ne hge (h.flowVal_ne_P hy hy0 hyp).symm
    have hLP : -rightImg (fun s => -w s) 0 t < P :=
      (h.leftImg_le_w.trans h.w_le_rightImg).trans_lt (h.rightImg_lt_P hv)
    exact ((nfR_lt h.hκN hPy).trans (lt_nfR h.hκN hLP)).le

/-- **Every relative real point right of `0` off the closed relative hull has image at least `N(R₀)`** (the old
target `1/v` included, by monotonicity of the relative flow). -/
theorem nf_R0_le (h : ConjData w u t q v α κN P) {y' : ℝ} (hy' : (y' : ℂ) ∉ closure (fwdHull u q))
    (hy'0 : 0 < y') : α - κN / (rightImg w 0 t - P) ≤ flowVal u q y' := by
  by_cases hy'v : -v * y' + 1 = 0
  · have hvy' : v * y' = 1 := by linarith
    have hv : 0 < v := by
      by_contra hc
      push Not at hc
      nlinarith
    obtain ⟨R, hR0, hR⟩ := exists_closure_fwdHull_subset h.hw t
    set Y : ℝ := R + 1 with hYdef
    have hY0 : 0 < Y := by rw [hYdef]; linarith
    have hYc : (Y : ℂ) ∉ closure (fwdHull w t) := notMem_of_far hR (by rw [abs_of_pos hY0]; linarith)
    have hd : 0 < v * Y + 1 := by positivity
    obtain ⟨hmc, hm0, -⟩ := flowVal_conj h.hw h.hw0 h.hu h.hu0 h.ht h.hq h.hK h.hconj hYc hY0.ne' hd.ne'
      (h.flowVal_ne_P hYc hY0.ne' hd.ne')
    have hmy0 : 0 < Y / (v * Y + 1) := div_pos hY0 hd
    have hmyv : -v * (Y / (v * Y + 1)) + 1 ≠ 0 := by
      have e : -v * (Y / (v * Y + 1)) + 1 = 1 / (v * Y + 1) := by
        rw [neg_mul, mul_div_assoc', ← neg_div, div_add_one hd.ne']
        congr 1
        ring
      rw [e]
      exact one_div_ne_zero hd.ne'
    have h1 := h.nf_R0_le_aux hmc hmy0 hmyv
    have hlt : Y / (v * Y + 1) < y' := by
      have e : y' * (v * Y + 1) = Y + y' := by linear_combination Y * hvy'
      rw [div_lt_iff₀ hd, e]
      linarith
    have h2 := flowVal_lt_flowVal h.hu h.hu0 h.hq hmc hm0 hy' hy'0.ne' hlt
    linarith
  · exact h.nf_R0_le_aux hy' hy'0 hy'v

/-- **Every relative real point left of `0` off the closed relative hull has image at most `N(L₀)`.** -/
theorem flowVal_le_nf_L0 (h : ConjData w u t q v α κN P) {y' : ℝ} (hy' : (y' : ℂ) ∉ closure (fwdHull u q))
    (hy'0 : y' < 0) : flowVal u q y' ≤ α - κN / (-rightImg (fun s => -w s) 0 t - P) := by
  by_cases hy'v : -v * y' + 1 = 0
  · have hvy' : v * y' = 1 := by linarith
    have hv : v < 0 := by
      by_contra hc
      push Not at hc
      nlinarith
    obtain ⟨R, hR0, hR⟩ := exists_closure_fwdHull_subset h.hw t
    set Y : ℝ := -(R + 1) with hYdef
    have hY0 : Y < 0 := by rw [hYdef]; linarith
    have hYc : (Y : ℂ) ∉ closure (fwdHull w t) :=
      notMem_of_far hR (by rw [abs_of_neg hY0, hYdef]; linarith)
    have hd : 0 < v * Y + 1 := by nlinarith
    obtain ⟨hmc, hm0, -⟩ := flowVal_conj h.hw h.hw0 h.hu h.hu0 h.ht h.hq h.hK h.hconj hYc hY0.ne hd.ne'
      (h.flowVal_ne_P hYc hY0.ne hd.ne')
    have hmy0 : Y / (v * Y + 1) < 0 := div_neg_of_neg_of_pos hY0 hd
    have hmyv : -v * (Y / (v * Y + 1)) + 1 ≠ 0 := by
      have e : -v * (Y / (v * Y + 1)) + 1 = 1 / (v * Y + 1) := by
        rw [neg_mul, mul_div_assoc', ← neg_div, div_add_one hd.ne']
        congr 1
        ring
      rw [e]
      exact one_div_ne_zero hd.ne'
    have h1 := h.flowVal_le_nf_L0_aux hmc hmy0 hmyv
    have hlt : y' < Y / (v * Y + 1) := by
      have e : y' * (v * Y + 1) = Y + y' := by linear_combination Y * hvy'
      rw [lt_div_iff₀ hd, e]
      linarith
    have h2 := flowVal_lt_flowVal h.hu h.hu0 h.hq hy' hy'0.ne hmc hm0 hlt
    linarith
  · exact h.flowVal_le_nf_L0_aux hy' hy'0 hy'v

/-- **The relative image of `0⁺` is at least `N(R₀)`.** -/
theorem nf_R0_le_rightImg (h : ConjData w u t q v α κN P) :
    α - κN / (rightImg w 0 t - P) ≤ rightImg u 0 q := by
  refine le_csInf (imgSet_nonempty h.hu 0 h.hq) ?_
  rintro _ ⟨y', hy'0, hal, rfl⟩
  have hc := notMem_closure_of_alive h.hu h.hu0 h.hq hal
  have h1 := h.nf_R0_le hc hy'0
  rcases (flowVal_spec h.hu h.hu0 h.hq hc hy'0.ne').2 with ⟨-, -, hf⟩ | ⟨hn, -, -⟩
  · rwa [hf] at h1
  · linarith

/-- **The relative image of `0⁻` is at most `N(L₀)`.** -/
theorem leftImg_le_nf_L0 (h : ConjData w u t q v α κN P) :
    -rightImg (fun s => -u s) 0 q ≤ α - κN / (-rightImg (fun s => -w s) 0 t - P) := by
  have hun : Continuous fun s => -u s := h.hu.neg
  have key : -(α - κN / (-rightImg (fun s => -w s) 0 t - P)) ≤ rightImg (fun s => -u s) 0 q := by
    refine le_csInf (imgSet_nonempty hun 0 h.hq) ?_
    rintro _ ⟨y'', hy''0, hal, rfl⟩
    have hc := notMem_closure_of_alive_neg h.hu h.hu0 h.hq hal
    have h1 := h.flowVal_le_nf_L0 hc (neg_lt_zero.2 hy''0)
    rcases (flowVal_spec h.hu h.hu0 h.hq hc (neg_ne_zero.2 hy''0.ne')).2 with ⟨hp, -, -⟩ | ⟨-, -, hf⟩
    · linarith
    · rw [hf, neg_neg] at h1
      linarith
  linarith

/-- **The alive case of the step identity**: at the image `x = g_t(y)` of a real point `y` off the closed hull and
off the exceptional points, `β'(N x − u_q) − b'(y) + 2χπ[x < P] = 2χπ[v < 0]`. -/
theorem alive_case (h : ConjData w u t q v α κN P) {κ : ℝ} (hκ : 0 < κ) {b' : ℝ → ℝ} {J' : Finset ℝ}
    (hb' : IsPiecewiseConstantBoundaryData b' J') {c : Restart.BoundaryWord}
    (h0 : ∀ u₀ uc : ℂ → ℝ, IsBoundedHarmonicExtension b' J' u₀ → IsBoundedHarmonicExtension c.fn c.jumps uc →
      ∀ z ∈ H, uc z = u₀ (mobInv v z) + chiC κ * (brChart v).2.2 (mobInv v z))
    {y : ℝ} (hy : (y : ℂ) ∉ closure (fwdHull w t)) (hy0 : y ≠ 0) (hyJ : y ∉ J') (hyp : v * y + 1 ≠ 0)
    (hmyJ : y / (v * y + 1) ∉ c.jumps)
    (hS' : α - κN / (flowVal w t y - P) - u q ∉ flowJumps c.fn c.jumps u q) :
    flowData κ c.fn c.jumps u q (α - κN / (flowVal w t y - P) - u q) - b' y +
        chiC κ * (2 * (if flowVal w t y < P then Real.pi else 0)) =
      chiC κ * (2 * (if v < 0 then Real.pi else 0)) := by
  obtain ⟨hmc, hm0, hfl⟩ := flowVal_conj h.hw h.hw0 h.hu h.hu0 h.ht h.hq h.hK h.hconj hy hy0 hyp
    (h.flowVal_ne_P hy hy0 hyp)
  set my : ℝ := y / (v * y + 1) with hmydef
  have hval : flowData κ c.fn c.jumps u q (flowVal u q my - u q) = c.fn my := by
    rcases (flowVal_spec h.hu h.hu0 h.hq hmc hm0).2 with ⟨hmp, hal, hf⟩ | ⟨hmn, hal, hf⟩
    · rw [hf]
      exact fbd_flow_right hκ c.isPiecewiseConstantBoundaryData h.hu h.hq hmp hal hmyJ
    · have hne : ∀ i, -gImg (fun s => -u s) (-my) q - u q ≠
          -rightImg (fun s => -u s) (-flowLineXL c.fn c.jumps 0 i) q - u q := by
        intro i he
        apply hS'
        rw [← hfl, hf, he]
        exact Set.mem_insert_of_mem _ (Or.inl ⟨i, rfl⟩)
      have h1 := fbd_flow_left hκ c.isPiecewiseConstantBoundaryData h.hu h.hq (neg_pos.2 hmn) hal
        (by rwa [neg_neg]) hne
      rw [neg_neg] at h1
      rw [hf]
      exact h1
  rw [← hfl, hval, word_eq hb' h0 hy0 hyp hyJ hmyJ]
  have hL := liftBdry_add h.hv hy0 hyp
  have hiff := h.lt_P_iff hy hy0
  by_cases hyq : y < pole v
  · have h1 : flowVal w t y < P := hiff.2 hyq
    simp only [h1, hyq, ↓reduceIte] at hL ⊢
    linear_combination chiC κ * hL
  · have h1 : ¬ flowVal w t y < P := fun h' => hyq (hiff.1 h')
    simp only [h1, hyq, ↓reduceIte] at hL ⊢
    linear_combination chiC κ * hL

/-- The bad real points of the step identity, as a finite set. -/
def badPts (v : ℝ) (J' : Finset ℝ) (c : Restart.BoundaryWord) : Finset ℝ :=
  J' ∪ {0, pole v} ∪ c.jumps.image fun y' => y' / (-v * y' + 1)

theorem notMem_jumps_of_notMem_badPts {v : ℝ} (hv : v ≠ 0) {J' : Finset ℝ} {c : Restart.BoundaryWord} {y : ℝ}
    (hy : y ∉ badPts v J' c) :
    y ∉ J' ∧ y ≠ 0 ∧ v * y + 1 ≠ 0 ∧ y / (v * y + 1) ∉ c.jumps := by
  simp only [badPts, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_image, not_or] at hy
  obtain ⟨⟨hJ, h0, hp⟩, himg⟩ := hy
  have hyp : v * y + 1 ≠ 0 := fun he => hp (eq_pole_of hv he)
  refine ⟨hJ, h0, hyp, fun hm => himg ⟨_, hm, ?_⟩⟩
  have hden : -v * (y / (v * y + 1)) + 1 = 1 / (v * y + 1) := by
    rw [neg_mul, mul_div_assoc', ← neg_div, div_add_one hyp]
    congr 1
    ring
  rw [hden, div_div_eq_mul_div, div_one, div_mul_cancel₀ _ hyp]

/-- **The boundary step identity (★)** off a finite set. -/
theorem step_eq (h : ConjData w u t q v α κN P) {κ : ℝ} (hκ : 0 < κ) {b' : ℝ → ℝ} {J' : Finset ℝ}
    (hb' : IsPiecewiseConstantBoundaryData b' J') {c : Restart.BoundaryWord}
    (h0 : ∀ u₀ uc : ℂ → ℝ, IsBoundedHarmonicExtension b' J' u₀ → IsBoundedHarmonicExtension c.fn c.jumps uc →
      ∀ z ∈ H, uc z = u₀ (mobInv v z) + chiC κ * (brChart v).2.2 (mobInv v z)) :
    ∃ E : Set ℝ, E.Finite ∧ ∀ x : ℝ, x ∉ E → x ≠ P →
      α - κN / (x - P) - u q ∉ flowJumps c.fn c.jumps u q → x - w t ∉ flowJumps b' J' w t →
      flowData κ c.fn c.jumps u q (α - κN / (x - P) - u q) - flowData κ b' J' w t (x - w t) +
        chiC κ * (2 * (if x < P then Real.pi else 0)) = chiC κ * (2 * (if v < 0 then Real.pi else 0)) := by
  set R₀ := rightImg w 0 t with hR₀
  set L₀ := -rightImg (fun s => -w s) 0 t with hL₀
  refine ⟨{R₀, L₀} ∪ flowVal w t '' ↑(badPts v J' c), ((Set.finite_singleton _).insert _).union
    ((badPts v J' c).finite_toSet.image _), fun x hxE hxP hxS' hxS => ?_⟩
  have hR : x ≠ R₀ := fun he => hxE (Or.inl (by simp [he]))
  have hL : x ≠ L₀ := fun he => hxE (Or.inl (by simp [he]))
  have hbad : ∀ y, y ∈ badPts v J' c → x ≠ flowVal w t y := fun y hy he => hxE (Or.inr ⟨y, hy, he.symm⟩)
  have hord := Theorem15.isOrderedForceWord_flowLine b' J' 0
  have hwL := h.leftImg_le_w
  have hwR := h.w_le_rightImg
  rcases lt_or_gt_of_ne hR with hxR | hxR
  · rcases lt_or_gt_of_ne hL with hxL | hxL
    · -- left alive
      have hwn : Continuous fun s => -w s := h.hw.neg
      obtain ⟨y, hy0, hal, hg⟩ := Restart.FCAux79.exists_alive_gImg_eq hwn h.ht (M := -x) (by rw [hL₀] at hxL; linarith)
      have hc := notMem_closure_of_alive_neg h.hw h.hw0 h.ht hal
      have hfv : flowVal w t (-y) = x := by
        rcases (flowVal_spec h.hw h.hw0 h.ht hc (neg_ne_zero.2 hy0.ne')).2 with ⟨hp, -, -⟩ | ⟨-, -, hf⟩
        · linarith
        · rw [hf, neg_neg, hg, neg_neg]
      have hyb : -y ∉ badPts v J' c := fun hm => hbad _ hm hfv.symm
      obtain ⟨hyJ, -, hyp, hmyJ⟩ := notMem_jumps_of_notMem_badPts h.hv hyb
      have hβ : flowData κ b' J' w t (x - w t) = b' (-y) := by
        have hne : ∀ i, -gImg (fun s => -w s) y t - w t ≠
            -rightImg (fun s => -w s) (-flowLineXL b' J' 0 i) t - w t := by
          intro i he
          apply hxS
          rw [show x = -gImg (fun s => -w s) y t by rw [hg, neg_neg], he]
          exact Set.mem_insert_of_mem _ (Or.inl ⟨i, rfl⟩)
        have := fbd_flow_left hκ hb' h.hw h.ht hy0 hal hyJ hne
        rw [show x = -gImg (fun s => -w s) y t by rw [hg, neg_neg]]
        exact this
      have hS'' : α - κN / (flowVal w t (-y) - P) - u q ∉ flowJumps c.fn c.jumps u q := by rwa [hfv]
      have key := h.alive_case hκ hb' h0 hc (neg_ne_zero.2 hy0.ne') hyJ hyp hmyJ hS''
      rw [hfv] at key
      rw [hβ]
      exact key
    · rcases lt_or_ge x (w t) with hxw | hxw
      · -- left side of the trace
        have hβ : flowData κ b' J' w t (x - w t) = -(Real.pi / Real.sqrt κ) :=
          Restart.FCAux79.forceBoundaryData_flow_slit_left _ _ h.hw h.ht (fun i => hord.2.1 i) (by linarith)
            (by rw [hL₀] at hxL; linarith)
        have hside : (x < P ∧ L₀ < P ∧ w t < P) ∨ (P < x ∧ P < L₀ ∧ P < w t) := by
          rcases lt_or_gt_of_ne h.hv with hv | hv
          · have := h.rightImg_lt_P hv
            exact Or.inl ⟨by linarith, by linarith, by linarith⟩
          · have := h.P_lt_leftImg hv
            exact Or.inr ⟨by linarith, by linarith, by linarith⟩
        have h1 : α - κN / (x - P) < α - κN / (w t - P) := by
          refine nfR_lt_nfR h.hκN hxw ?_
          rcases hside with ⟨-, -, h3⟩ | ⟨h1, -, -⟩
          · exact Or.inl h3
          · exact Or.inr h1
        have h2 : α - κN / (L₀ - P) < α - κN / (x - P) := by
          refine nfR_lt_nfR h.hκN hxL ?_
          rcases hside with ⟨h1, -, -⟩ | ⟨-, h2, -⟩
          · exact Or.inl h1
          · exact Or.inr h2
        have h3 := h.leftImg_le_nf_L0
        rw [← hL₀] at h3
        have hβ' : flowData κ c.fn c.jumps u q (α - κN / (x - P) - u q) = -(Real.pi / Real.sqrt κ) :=
          Restart.FCAux79.forceBoundaryData_flow_slit_left _ _ h.hu h.hq
            (fun i => (Theorem15.isOrderedForceWord_flowLine c.fn c.jumps 0).2.1 i)
            (by rw [h.hdrv]; linarith) (by rw [h.hdrv] at *; linarith)
        rw [hβ, hβ']
        rcases lt_or_gt_of_ne h.hv with hv | hv
        · have hxP' : x < P := by have := h.rightImg_lt_P hv; linarith
          simp only [hxP', hv, ↓reduceIte]
          ring
        · have hxP' : ¬ x < P := by have := h.P_lt_leftImg hv; linarith
          simp only [hxP', not_lt.2 hv.le, ↓reduceIte]
          ring
      · -- right side of the trace
        have hβ : flowData κ b' J' w t (x - w t) = Real.pi / Real.sqrt κ :=
          Restart.FCAux79.forceBoundaryData_flow_slit_right _ _ h.hw h.ht (fun j => hord.2.2.2 j) (by linarith)
            (by rw [hR₀] at hxR; linarith)
        have hside : (x < P ∧ R₀ < P ∧ w t < P) ∨ (P < x ∧ P < R₀ ∧ P < w t) := by
          rcases lt_or_gt_of_ne h.hv with hv | hv
          · have := h.rightImg_lt_P hv
            exact Or.inl ⟨by linarith, by linarith, by linarith⟩
          · have := h.P_lt_leftImg hv
            exact Or.inr ⟨by linarith, by linarith, by linarith⟩
        have h1 : α - κN / (w t - P) ≤ α - κN / (x - P) := by
          refine nfR_le_nfR h.hκN hxw ?_
          rcases hside with ⟨h1, -, -⟩ | ⟨-, -, h3⟩
          · exact Or.inl h1
          · exact Or.inr h3
        have h2 : α - κN / (x - P) < α - κN / (R₀ - P) := by
          refine nfR_lt_nfR h.hκN hxR ?_
          rcases hside with ⟨-, h2, -⟩ | ⟨h1, -, -⟩
          · exact Or.inl h2
          · exact Or.inr h1
        have h3 := h.nf_R0_le_rightImg
        rw [← hR₀] at h3
        have hβ' : flowData κ c.fn c.jumps u q (α - κN / (x - P) - u q) = Real.pi / Real.sqrt κ :=
          Restart.FCAux79.forceBoundaryData_flow_slit_right _ _ h.hu h.hq
            (fun j => (Theorem15.isOrderedForceWord_flowLine c.fn c.jumps 0).2.2.2 j)
            (by rw [h.hdrv]; linarith) (by linarith)
        rw [hβ, hβ']
        rcases lt_or_gt_of_ne h.hv with hv | hv
        · have hxP' : x < P := by have := h.rightImg_lt_P hv; linarith
          simp only [hxP', hv, ↓reduceIte]
          ring
        · have hxP' : ¬ x < P := by have := h.P_lt_leftImg hv; linarith
          simp only [hxP', not_lt.2 hv.le, ↓reduceIte]
          ring
  · -- right alive
    obtain ⟨y, hy0, hal, hg⟩ := Restart.FCAux79.exists_alive_gImg_eq h.hw h.ht (M := x) (by rw [hR₀] at hxR; exact hxR)
    have hc := notMem_closure_of_alive h.hw h.hw0 h.ht hal
    have hfv : flowVal w t y = x := by
      rcases (flowVal_spec h.hw h.hw0 h.ht hc hy0.ne').2 with ⟨-, -, hf⟩ | ⟨hn, -, -⟩
      · rw [hf, hg]
      · linarith
    have hyb : y ∉ badPts v J' c := fun hm => hbad _ hm hfv.symm
    obtain ⟨hyJ, -, hyp, hmyJ⟩ := notMem_jumps_of_notMem_badPts h.hv hyb
    have hβ : flowData κ b' J' w t (x - w t) = b' y := by
      rw [← hg]
      exact fbd_flow_right hκ hb' h.hw h.ht hy0 hal hyJ
    have hS'' : α - κN / (flowVal w t y - P) - u q ∉ flowJumps c.fn c.jumps u q := by rwa [hfv]
    have key := h.alive_case hκ hb' h0 hc hy0.ne' hyJ hyp hmyJ hS''
    rw [hfv] at key
    rw [hβ]
    exact key

end ConjData

end InteractingSLE.Theorem14.BR4aIn
