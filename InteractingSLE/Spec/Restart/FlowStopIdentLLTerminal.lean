/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FlowStopIdentLLCut
import InteractingSLE.Foundations.Loewner.TraceClose

/-!
# Terminal collision intervals from the inverse boundary map

Packet PROVE-L1-LL. Closing the inverse map at the finite horizon identifies
every nonempty side collision group with its physical terminal real interval.
This uses the proved terminal boundary-extension theorem, and does not require
the converse assertion that every real terminal tip is a side collision.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Finset Complex
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Restart.FlowStopIdentLL

open Sec2 MartChar.RealFlow
open QuantumZipper (H Hbar fwdMapInv)

section Scalar

variable {D : ℝ → ℝ} {t : ℝ} {p : ℂ}

/-- Geometric images are one-Lipschitz in their initial position on one side.
This is the infimum version of the existing bound for alive real images. -/
theorem rightImg_le_add_index (hD : Continuous D) (ht : 0 ≤ t)
    {x x' : ℝ} (hxx : x ≤ x') :
    rightImg D x' t ≤ rightImg D x t + (x' - x) := by
  have hle : rightImg D x' t - (x' - x) ≤ rightImg D x t := by
    apply le_csInf (imgSet_nonempty hD x ht)
    rintro g ⟨y, hxy, hy, rfl⟩
    have hyd : y ≤ y + (x' - x) := by linarith only [hxx]
    have hy' : Alive D (y + (x' - x)) t := hy.of_le hD hyd ht
    have hbound := (abs_le.1 (abs_gImg_sub_le hD ht hy hy')).2
    rw [abs_of_nonneg (by linarith only [hxx] : 0 ≤ y + (x' - x) - y)] at hbound
    have himg := rightImg_le_gImg hD ht
      (by linarith only [hxy] : x' < y + (x' - x)) hy'
    linarith only [hbound, himg]
  linarith only [hle]

/-- Approximate a geometric image by alive real points, including their physical
limit under the inverse boundary map. -/
theorem exists_alive_tendsto_of_rightImg_eq
    (hD : Continuous D) (hD0 : D 0 = 0) (ht : 0 ≤ t)
    (hB : HasBdryLimits (fwdMapInv D t))
    (htip : extendFrom H (fwdMapInv D t) 0 = p)
    {x : ℝ} (hcoll : rightImg D x t = D t) :
    ∃ y : ℕ → ℝ, (∀ n, x < y n ∧ Alive D (y n) t) ∧
      Tendsto (fun n => gImg D (y n) t) atTop (𝓝 (D t)) ∧
      Tendsto (fun n => ((y n : ℝ) : ℂ)) atTop (𝓝 p) := by
  have hex : ∀ n : ℕ, ∃ y, x < y ∧ Alive D y t ∧
      gImg D y t < D t + 1 / ((n : ℝ) + 1) := fun n =>
    exists_lt_of_rightImg_lt hD ht (by rw [hcoll]; exact lt_add_of_pos_right _ (by positivity))
  choose y hxy hya hupper using hex
  have hupperlim : Tendsto (fun n : ℕ => D t + 1 / ((n : ℝ) + 1)) atTop (𝓝 (D t)) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_add (D t)
  have hG : Tendsto (fun n => gImg D (y n) t) atTop (𝓝 (D t)) := by
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupperlim
      (fun n => ((hya n).lt_gImg hD ⟨ht, le_rfl⟩).le) (fun n => (hupper n).le)
  have hgap : Tendsto (fun n => gImg D (y n) t - D t) atTop (𝓝 0) := by
    simpa only [sub_self] using hG.sub_const (D t)
  have hgapC : Tendsto (fun n => ((gImg D (y n) t - D t : ℝ) : ℂ)) atTop
      (𝓝[Hbar] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => ?_⟩
    · simpa only [Function.comp_def, ofReal_zero] using (continuous_ofReal.tendsto 0).comp hgap
    · show 0 ≤ ((gImg D (y n) t - D t : ℝ) : ℂ).im
      simp
  have hF := (hB.continuousOn 0 (show (0 : ℂ) ∈ Hbar by simp [Hbar])).tendsto.comp hgapC
  rw [htip] at hF
  have hval : ∀ n, extendFrom H (fwdMapInv D t)
      ((gImg D (y n) t - D t : ℝ) : ℂ) = (y n : ℂ) := by
    intro n
    have h := Sec7.SideHeight.extendFrom_eq_of_isForwardSol' hB hD hD0 ht
      (show (y n : ℂ) ∈ Hbar by simp [Hbar]) (WangWu.isForwardSol_of_alive hD (hya n))
    convert h using 1; simp only [gImg, add_sub_cancel_left]
  exact ⟨y, fun n => ⟨hxy n, hya n⟩, hG, hF.congr fun n => hval n⟩

/-- Every colliding image is below the physical real terminal tip. -/
theorem real_tip_of_rightImg_eq
    (hD : Continuous D) (hD0 : D 0 = 0) (ht : 0 ≤ t)
    (hB : HasBdryLimits (fwdMapInv D t))
    (htip : extendFrom H (fwdMapInv D t) 0 = p)
    {x : ℝ} (hcoll : rightImg D x t = D t) : p.im = 0 ∧ x ≤ p.re := by
  obtain ⟨y, hy, -, hlim⟩ := exists_alive_tendsto_of_rightImg_eq hD hD0 ht hB htip hcoll
  constructor
  · have h : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 p.im) := by
      simpa only [Function.comp_def, ofReal_im] using (continuous_im.tendsto p).comp hlim
    exact tendsto_nhds_unique h tendsto_const_nhds
  · have h := (continuous_re.tendsto p).comp hlim
    exact ge_of_tendsto h (Eventually.of_forall fun n => (hy n).1.le)

/-- If the zero-side image collides, all other collisions on that side form
exactly the closed real interval ending at the physical terminal tip. -/
theorem rightImg_eq_iff_of_zero_collision
    (hD : Continuous D) (hD0 : D 0 = 0) (ht : 0 ≤ t)
    (hB : HasBdryLimits (fwdMapInv D t))
    (htip : extendFrom H (fwdMapInv D t) 0 = p)
    (hzero : rightImg D 0 t = D t) (x : ℝ) :
    rightImg D x t = D t ↔ x ≤ p.re := by
  constructor
  · exact fun h => (real_tip_of_rightImg_eq hD hD0 ht hB htip h).2
  · intro hxp
    obtain ⟨y, hy, hG, hY⟩ := exists_alive_tendsto_of_rightImg_eq hD hD0 ht hB htip hzero
    have hYre := (continuous_re.tendsto p).comp hY
    have hstrict : ∀ z : ℝ, z < p.re → rightImg D z t = D t := by
      intro z hz
      have hevent : ∀ᶠ n in atTop, z < y n := by
        have h := hYre (lt_mem_nhds hz)
        change ∀ᶠ n in atTop, z < (y n : ℂ).re at h
        simpa only [ofReal_re] using h
      apply le_antisymm ?_ (le_rightImg hD z ht)
      exact ge_of_tendsto hG (hevent.mono fun n hn => rightImg_le_gImg hD ht hn (hy n).2)
    have hupper : ∀ ε : ℝ, 0 < ε → rightImg D x t ≤ D t + ε := by
      intro ε hε
      have hz : x - ε < p.re := by linarith only [hxp, hε]
      have h := rightImg_le_add_index hD ht (by linarith only [hε] : x - ε ≤ x)
      rw [hstrict (x - ε) hz] at h
      linarith only [h]
    exact le_antisymm (le_of_forall_pos_le_add hupper) (le_rightImg hD x ht)

end Scalar

section Terminal

variable {D : ℝ → ℝ} {w : ℝ≥0 → ℝ} {U : ℝ≥0∞}
  {γ : ℝ≥0 → ℂ} {T : ℝ≥0}

/-- The already proved terminal inverse-map extension, adapted to NNReal traces
and any continuous extension of their driver. -/
theorem terminal_boundary_data (hg : IsGeneratingTrace w U γ)
    (hT : 0 < T) (hTU : (T : ℝ≥0∞) ≤ U)
    (hD : Continuous D) (hD0 : D 0 = 0)
    (hDw : ∀ s : ℝ≥0, s < T → D s = w s) :
    HasBdryLimits (fwdMapInv D T) ∧
      extendFrom H (fwdMapInv D T) 0 = γ T := by
  have hag : ∀ s : ℝ, 0 ≤ s → s < T → D s = w s.toNNReal := by
    intro s hs hsT
    simpa only [Real.coe_toNNReal s hs] using
      hDw s.toNNReal ((Real.toNNReal_lt_iff_lt_coe hs).2 hsT)
  have hLT := GB7a.isLoewnerTraceLT_of_agree hg hTU hag
  have hc : ContinuousOn (fun s : ℝ => γ s.toNNReal) (Icc 0 (T : ℝ)) := by
    refine hg.2.1.comp continuous_real_toNNReal.continuousOn fun s hs => ?_
    exact (ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hs.2)).trans hTU
  refine ⟨TraceClose.hasBdryLimits_of_isLoewnerTraceLT hLT hD hD0
    (NNReal.coe_pos.2 hT) hc, ?_⟩
  simpa only [Real.toNNReal_coe] using TraceClose.extendFrom_zero_eq hLT hD hD0
    (NNReal.coe_pos.2 hT) hc

/-- The full terminal rule reduces to two zero-image implications. This extra
converse identifies which side is accessed at a real terminal tip. It is not
needed by the lifetime clause, which treats an empty collision group directly.
The named `hrealTipCollision` premise is deliberately explicit here. -/
theorem terminalImageRule_of_real_tip_collision
    (hg : IsGeneratingTrace w U γ) (hT : 0 < T) (hTU : (T : ℝ≥0∞) ≤ U)
    (hD : Continuous D) (hD0 : D 0 = 0)
    (hDw : ∀ s : ℝ≥0, s < T → D s = w s)
    (hrealTipCollision :
      ((γ T).im = 0 → (γ T).re ≤ 0 → rightImg (fun s => -D s) 0 T = -D T) ∧
      ((γ T).im = 0 → 0 ≤ (γ T).re → rightImg D 0 T = D T)) :
    TerminalImageRule D T (γ T) := by
  obtain ⟨hB, htip⟩ := terminal_boundary_data hg hT hTU hD hD0 hDw
  obtain ⟨hBL, htipL⟩ := terminal_boundary_data (LP.isGeneratingTrace_reflect hg)
    hT hTU hD.neg (by simp [hD0]) (fun s hs => congrArg Neg.neg (hDw s hs))
  constructor
  · intro x hx
    constructor
    · intro hcoll
      have hp := real_tip_of_rightImg_eq hD.neg (by simp [hD0]) T.coe_nonneg hBL htipL hcoll
      have him : (γ T).im = 0 := by simpa [LP.reflectC] using hp.1
      have hxp : x ≤ -(γ T).re := by simpa [LP.reflectC] using hp.2
      exact ⟨him, by linarith only [hxp, hx], hxp⟩
    · rintro ⟨him, hre, hxp⟩
      exact (rightImg_eq_iff_of_zero_collision hD.neg (by simp [hD0]) T.coe_nonneg
        hBL htipL (hrealTipCollision.1 him hre) x).2 (by simpa [LP.reflectC] using hxp)
  · intro x hx
    constructor
    · intro hcoll
      have hp := real_tip_of_rightImg_eq hD hD0 T.coe_nonneg hB htip hcoll
      exact ⟨hp.1, hx.trans hp.2, hp.2⟩
    · rintro ⟨him, hre, hxp⟩
      exact (rightImg_eq_iff_of_zero_collision hD hD0 T.coe_nonneg hB htip
        (hrealTipCollision.2 him hre) x).2 hxp

/-- **Common terminal collision cuts, with no additional geometric input.**
If the zero-side image is separated, all marks on that side are separated.
If it collides, the inverse boundary map identifies the entire collision interval
with the real tip. This is the part of the terminal image rule needed by (L1). -/
theorem hasCommonCollisionCuts_terminal_images
    {b bR : ℝ → ℝ} {J JR : Finset ℝ} {y : ℝ} {O : Set ℝ}
    (hO : IsOpen O) (hg : IsGeneratingTrace w U γ)
    (hT : 0 < T) (hTU : (T : ℝ≥0∞) ≤ U)
    (hD : Continuous D) (hD0 : D 0 = 0)
    (hDw : ∀ s : ℝ≥0, s < T → D s = w s)
    (hreal : (γ T).im = 0 → y + (γ T).re ∈ O) :
    HasCommonCollisionCuts b J bR JR y O (D T)
      (fun i => -rightImg (fun s => -D s) (-flowLineXL b J y i) T)
      (fun j => rightImg D (flowLineXR b J y j) T) (D T)
      (fun i => -rightImg (fun s => -D s) (-flowLineXL bR JR y i) T)
      (fun j => rightImg D (flowLineXR bR JR y j) T) := by
  obtain ⟨hB, htip⟩ := terminal_boundary_data hg hT hTU hD hD0 hDw
  obtain ⟨hBL, htipL⟩ := terminal_boundary_data (LP.isGeneratingTrace_reflect hg)
    hT hTU hD.neg (by simp [hD0]) (fun s hs => congrArg Neg.neg (hDw s hs))
  have hnone (E : ℝ → ℝ) (hE : Continuous E) (hzero : rightImg E 0 T ≠ E T)
      {x : ℝ} (hx : 0 ≤ x) : rightImg E x T ≠ E T := by
    intro h
    apply hzero
    exact le_antisymm ((rightImg_mono_index hE T.coe_nonneg hx).trans h.le)
      (le_rightImg hE 0 T.coe_nonneg)
  apply hasCommonCollisionCuts_of_real_intervals hO
  · by_cases hz : rightImg (fun s => -D s) 0 T = -D T
    · have hp := real_tip_of_rightImg_eq hD.neg (by simp [hD0]) T.coe_nonneg hBL htipL hz
      have hpim : (γ T).im = 0 := by simpa [LP.reflectC] using hp.1
      have hpre : (γ T).re ≤ 0 := by simpa [LP.reflectC] using hp.2
      have hiff (d : ℝ → ℝ) (K : Finset ℝ) (i : Fin (flowLineNL d K y)) :
          -rightImg (fun s => -D s) (-flowLineXL d K y i) T = D T ↔
            y + (γ T).re ≤ y + flowLineXL d K y i := by
        rw [neg_eq_iff_eq_neg, rightImg_eq_iff_of_zero_collision (D := fun s => -D s) hD.neg
          (by simp [hD0]) T.coe_nonneg hBL htipL hz]
        simp only [LP.reflectC, neg_re, conj_re]
        constructor <;> intro h <;> linarith only [h]
      exact Or.inr ⟨y + (γ T).re, hreal hpim, by linarith only [hpre],
        hiff b J, hiff bR JR⟩
    · refine Or.inl ⟨fun i hi => ?_, fun i hi => ?_⟩
      · exact hnone _ hD.neg hz (neg_nonneg.2 (flowLineXL_nonpos_seed b J y i))
          (neg_eq_iff_eq_neg.1 hi)
      · exact hnone _ hD.neg hz (neg_nonneg.2 (flowLineXL_nonpos_seed bR JR y i))
          (neg_eq_iff_eq_neg.1 hi)
  · by_cases hz : rightImg D 0 T = D T
    · have hp := real_tip_of_rightImg_eq hD hD0 T.coe_nonneg hB htip hz
      have hiff (d : ℝ → ℝ) (K : Finset ℝ) (i : Fin (flowLineNR d K y)) :
          rightImg D (flowLineXR d K y i) T = D T ↔
            y + flowLineXR d K y i ≤ y + (γ T).re := by
        rw [rightImg_eq_iff_of_zero_collision hD hD0 T.coe_nonneg hB htip hz]
        constructor <;> intro h <;> linarith only [h]
      exact Or.inr ⟨y + (γ T).re, hreal hp.1, by linarith only [hp.2],
        hiff b J, hiff bR JR⟩
    · exact Or.inl ⟨fun i => hnone D hD hz (flowLineXR_nonneg_seed b J y i),
        fun i => hnone D hD hz (flowLineXR_nonneg_seed bR JR y i)⟩

end Terminal

section Lifetime

variable {κ θ y : ℝ} {b bR : ℝ → ℝ} {J JR : Finset ℝ} {O : Set ℝ}
  {V : Set ℂ} {w wR β βR : ℝ≥0 → ℝ}
  {vL : Fin (flowLineNL b J y) → ℝ≥0 → ℝ}
  {vR : Fin (flowLineNR b J y) → ℝ≥0 → ℝ}
  {vLR : Fin (flowLineNL bR JR y) → ℝ≥0 → ℝ}
  {vRR : Fin (flowLineNR bR JR y) → ℝ≥0 → ℝ}
  {U : ℝ≥0∞} {Γ : ℝ≥0 → ℂ} {T : ℝ≥0} {D : ℝ → ℝ}

/-- The generating trace provides the continuity needed by the exit/lifetime
distinction, including when the terminal raw driver value is arbitrary. -/
theorem eq_lifetime_at_exit_of_generatingTrace
    (hV : IsOpen V) (hg : IsGeneratingTrace w U (fun t => Γ t - y))
    (he : (T : ℝ≥0∞) = RLC.exitTime V Γ U) (hmem : Γ T ∈ V) :
    (T : ℝ≥0∞) = U := by
  have hΓ : ContinuousOn Γ {t | (t : ℝ≥0∞) < U} := by
    have h := (hg.2.1.mono (fun (s : ℝ≥0) (ht : (s : ℝ≥0∞) < U) => ht.le)).add
      (continuousOn_const (c := (y : ℂ)))
    change ContinuousOn (fun t => (Γ t - y) + y) {t | (t : ℝ≥0∞) < U} at h
    simpa only [sub_add_cancel] using h
  exact eq_lifetime_of_mem_exitTime hV hΓ he hmem

/-- **The positive deterministic lifetime clause without a geometric input.**
The terminal inverse map constructs the common collision cuts directly. -/
theorem lifetime_clause_pos
    (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b J)
    (hbR : IsPiecewiseConstantBoundaryData bR JR) (hO : IsOpen O)
    (hbbR : ∀ a ∈ O, b a = bR a) (hV : IsOpen V)
    (hVO : ∀ z ∈ V, z.im = 0 → z.re ∈ O)
    (hp : IsIntegratedSLEPath κ (flowLineXL b J y) (flowLineXR b J y)
      (flowLineRhoL κ b J y θ) (flowLineRhoR κ b J y θ) w vL vR β U)
    (hg : IsGeneratingTrace w U (fun t => Γ t - y))
    (hpR : IsSLEPathUpTo κ (flowLineXL bR JR y) (flowLineXR bR JR y)
      (flowLineRhoL κ bR JR y θ) (flowLineRhoR κ bR JR y θ) wR vLR vRR βR
      (RLC.exitTime V Γ U))
    (hgR : IsGeneratingTrace wR (RLC.exitTime V Γ U) (fun t => Γ t - y))
    (hT : 0 < T) (he : (T : ℝ≥0∞) = RLC.exitTime V Γ U) (hmem : Γ T ∈ V)
    (hD : Continuous D) (hD0 : D 0 = 0)
    (hDw : ∀ s : ℝ≥0, s < T → D s = w s) :
    Continuous (closeState T wR vLR vRR
      (imageState D (flowLineXL bR JR y) (flowLineXR bR JR y) T)) ∧
    ForceWord.ThresholdCondition (flowLineRhoL κ bR JR y θ)
      (flowLineRhoR κ bR JR y θ) (D T)
      (fun i => -rightImg (fun s => -D s) (-flowLineXL bR JR y i) T)
      (fun j => rightImg D (flowLineXR bR JR y j) T) := by
  have hU := eq_lifetime_at_exit_of_generatingTrace hV hg he hmem
  have hpT := hp.isSLEPathUpTo hU.le
  have hpRT : IsSLEPathUpTo κ (flowLineXL bR JR y) (flowLineXR bR JR y)
      (flowLineRhoL κ bR JR y θ) (flowLineRhoR κ bR JR y θ) wR vLR vRR βR T := by
    simpa only [← he] using hpR
  have hgT : IsGeneratingTrace w T (fun t => Γ t - y) := by
    simpa only [← hU] using hg
  have hgRT : IsGeneratingTrace wR T (fun t => Γ t - y) := by
    simpa only [← he] using hgR
  have hlim := tendsto_state_imageState hpT hD hD0
    (fun s hs => hDw s (ENNReal.coe_lt_coe.1 hs)) rfl
  have hthr := hp.isForcePath.threshold_of_tendsto hT hU hlim
  have hreal : (Γ T - (y : ℂ)).im = 0 → y + (Γ T - (y : ℂ)).re ∈ O := by
    intro him
    have h := hVO (Γ T) hmem (by simpa using him)
    simpa using h
  have hcuts := hasCommonCollisionCuts_terminal_images (b := b) (J := J)
    (bR := bR) (JR := JR) hO hg hT hU.le hD hD0 hDw hreal
  exact ⟨continuous_closeState_of_common_trace hpRT hgT hgRT hD hD0 hDw,
    (thresholdCondition_iff_of_commonCollisionCuts hκ hb hbR hbbR hcuts).1 hthr⟩

/-- **All finite deterministic lifetime clauses, without an extra mathematical
input.** The only limit needed is the original driver's limit, already supplied
almost surely by Auxiliary lemma 3. The zero case preserves the initial state. -/
theorem lifetime_clause_at_exit
    (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b J)
    (hbR : IsPiecewiseConstantBoundaryData bR JR) (hO : IsOpen O)
    (hbbR : ∀ a ∈ O, b a = bR a) (hV : IsOpen V)
    (hVO : ∀ z ∈ V, z.im = 0 → z.re ∈ O)
    (hp : IsIntegratedSLEPath κ (flowLineXL b J y) (flowLineXR b J y)
      (flowLineRhoL κ b J y θ) (flowLineRhoR κ b J y θ) w vL vR β U)
    (hg : IsGeneratingTrace w U (fun t => Γ t - y))
    (hpR : IsSLEPathUpTo κ (flowLineXL bR JR y) (flowLineXR bR JR y)
      (flowLineRhoL κ bR JR y θ) (flowLineRhoR κ bR JR y θ) wR vLR vRR βR
      (RLC.exitTime V Γ U))
    (hgR : IsGeneratingTrace wR (RLC.exitTime V Γ U) (fun t => Γ t - y))
    (he : (T : ℝ≥0∞) = RLC.exitTime V Γ U) (hmem : Γ T ∈ V) (c : ℝ)
    (hlim : 0 < T → Tendsto w (𝓝[<] T) (𝓝 c)) :
    ∃ z : ℝ × (Fin (flowLineNL bR JR y) → ℝ) × (Fin (flowLineNR bR JR y) → ℝ),
      Continuous (closeState T wR vLR vRR z) ∧
      (∀ t : ℝ≥0, t < T ∨ t = 0 →
        closeState T wR vLR vRR z t = (wR t, fun i => vLR i t, fun j => vRR j t)) ∧
      ForceWord.ThresholdCondition (flowLineRhoL κ bR JR y θ)
        (flowLineRhoR κ bR JR y θ) (closeState T wR vLR vRR z T).1
        (closeState T wR vLR vRR z T).2.1 (closeState T wR vLR vRR z T).2.2 := by
  rcases eq_or_lt_of_le (show (0 : ℝ≥0) ≤ T from zero_le) with hT | hT
  · subst T
    exact lifetime_clause_of_driver_limit hκ hb hbR hO hbbR hV hVO hp hg hpR hgR he hmem
      c hlim (fun hpos => (lt_irrefl 0 hpos).elim)
  · have hTU : (T : ℝ≥0∞) ≤ U := he ▸ min_le_left _ _
    have hpT := hp.isSLEPathUpTo hTU
    have hc : ContinuousOn w (Iio T) := by
      simpa only [← setOf_lt_coe_eq_Iio T] using hpT.continuousOn_w
    have hD : Continuous (FiniteEndpoint.extDriver w T c) :=
      FiniteEndpoint.continuous_extDriver hc (hlim hT)
    have hD0 : FiniteEndpoint.extDriver w T c 0 = 0 := by
      simp only [FiniteEndpoint.extDriver, Real.toNNReal_zero, ite_eq_left hT, hpT.w_zero]
    have hDw : ∀ s : ℝ≥0, s < T → FiniteEndpoint.extDriver w T c s = w s := by
      intro s hs
      simp only [FiniteEndpoint.extDriver, Real.toNNReal_coe, ite_eq_left hs]
    obtain ⟨hcont, hthr⟩ := lifetime_clause_pos hκ hb hbR hO hbbR hV hVO hp hg hpR hgR
      hT he hmem hD hD0 hDw
    refine ⟨imageState (FiniteEndpoint.extDriver w T c)
      (flowLineXL bR JR y) (flowLineXR bR JR y) T, hcont, ?_, ?_⟩
    · intro t ht
      have htT : t < T := ht.elim id (fun ht0 => ht0 ▸ hT)
      simp only [closeState, closeAt, ite_eq_left htT]
    · simpa only [closeState_self, imageState] using hthr

/-- The lifetime clause for the supplied endpoint version. Its continuity is
already a conjunct of `IsStoppedHullCoupling`; no new endpoint hypothesis is
needed when this adapter is applied to a stopped flow line. -/
theorem thresholdCondition_at_exit_continuous
    (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b J)
    (hbR : IsPiecewiseConstantBoundaryData bR JR) (hO : IsOpen O)
    (hbbR : ∀ a ∈ O, b a = bR a) (hV : IsOpen V)
    (hVO : ∀ z ∈ V, z.im = 0 → z.re ∈ O)
    (hp : IsIntegratedSLEPath κ (flowLineXL b J y) (flowLineXR b J y)
      (flowLineRhoL κ b J y θ) (flowLineRhoR κ b J y θ) w vL vR β U)
    (hg : IsGeneratingTrace w U (fun t => Γ t - y))
    (hpR : IsSLEPathUpTo κ (flowLineXL bR JR y) (flowLineXR bR JR y)
      (flowLineRhoL κ bR JR y θ) (flowLineRhoR κ bR JR y θ) wR vLR vRR βR
      (RLC.exitTime V Γ U))
    (hgR : IsGeneratingTrace wR (RLC.exitTime V Γ U) (fun t => Γ t - y))
    (he : (T : ℝ≥0∞) = RLC.exitTime V Γ U) (hmem : Γ T ∈ V) (c : ℝ)
    (hlim : 0 < T → Tendsto w (𝓝[<] T) (𝓝 c))
    (hcR : ContinuousOn (fun t => (wR t, fun i => vLR i t, fun j => vRR j t)) (Iic T)) :
    ForceWord.ThresholdCondition (flowLineRhoL κ bR JR y θ)
      (flowLineRhoR κ bR JR y θ) (wR T) (fun i => vLR i T) (fun j => vRR j T) := by
  obtain ⟨z, hcont, hagree, hthr⟩ := lifetime_clause_at_exit hκ hb hbR hO hbbR hV hVO
    hp hg hpR hgR he hmem c hlim
  have heq : closeState T wR vLR vRR z T = (wR T, fun i => vLR i T, fun j => vRR j T) := by
    rcases eq_or_lt_of_le (show (0 : ℝ≥0) ≤ T from zero_le) with hT | hT
    · subst T
      exact hagree 0 (Or.inr rfl)
    · have := Sec2.IsForcePath.neBot_nhdsLT hT
      have hl₁ := (hcont.tendsto T).mono_left (nhdsWithin_le_nhds (s := Iio T))
      have hl₂ := (hcR T self_mem_Iic).tendsto.mono_left
        (nhdsWithin_mono _ Iio_subset_Iic_self)
      have hev : (fun t => (wR t, fun i => vLR i t, fun j => vRR j t)) =ᶠ[𝓝[<] T]
          closeState T wR vLR vRR z := by
        filter_upwards [self_mem_nhdsWithin] with t ht using (hagree t (Or.inl ht)).symm
      exact tendsto_nhds_unique hl₁ (hl₂.congr' hev)
  have h := congrArg (fun q : ℝ × (Fin (flowLineNL bR JR y) → ℝ) ×
      (Fin (flowLineNR bR JR y) → ℝ) =>
    ForceWord.ThresholdCondition (flowLineRhoL κ bR JR y θ)
      (flowLineRhoR κ bR JR y θ) q.1 q.2.1 q.2.2) heq
  exact h ▸ hthr

end Lifetime

section FlowLines

open FlowStopIdentG StoppedExtend
open LQGMetric (DistOn TestOn)

/-- **The lifetime clause is automatic for a stopped flow line in the locality
setting.** The original evolution supplies its driver limit almost surely;
absolute continuity transfers that event. Every other premise is already part
of the source flow line or the stopped replacement coupling. -/
theorem isStoppedFlowLineL_of_isStoppedFlowLine
    {κ θ y : ℝ} {b bR : ℝ → ℝ} {J JR : Finset ℝ} {O : Set ℝ} {V : Set ℂ}
    {S : Type u} [MeasurableSpace S] {Q₀ Q : Measure S}
    [IsProbabilityMeasure Q₀] [IsProbabilityMeasure Q]
    {H₀ Ĥ : S → DistOn upperHalfPlaneOpens} {Γ : S → ℝ≥0 → ℂ} {U : S → ℝ≥0∞}
    (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b J)
    (hbR : IsPiecewiseConstantBoundaryData bR JR) (hO : IsOpen O)
    (hbbR : ∀ a ∈ O, b a = bR a) (hV : IsOpen V)
    (hVO : ∀ z ∈ V, z.im = 0 → z.re ∈ O) (hQQ₀ : Q ≪ Q₀)
    (hflow : IsFlowLine κ b J y θ Q₀ H₀ Γ U)
    (hstop : IsStoppedFlowLine κ bR JR y θ Q Ĥ Γ (fun ω => RLC.exitTime V (Γ ω) (U ω))) :
    IsStoppedFlowLineL κ bR JR y θ V Q Ĥ Γ (fun ω => RLC.exitTime V (Γ ω) (U ω)) := by
  obtain ⟨H₀', 𝓕₀, W₀, VL₀, VR₀, B₀, -, hC₀, hgen₀⟩ := hflow
  obtain ⟨Ĥ', 𝓕, W, VL, VR, B, htr, hC, hgen⟩ := hstop
  refine ⟨Ĥ', 𝓕, W, VL, VR, B, htr, hC, hgen, ?_⟩
  filter_upwards [hC₀.1.ae_isIntegratedSLEPath.filter_mono hQQ₀.ae_le,
    (hC₀.1.ae_tendsto_threshold hκ).filter_mono hQQ₀.ae_le,
    hgen₀.filter_mono hQQ₀.ae_le, hC.1.ae_path, hC.2.1, hgen]
    with ω hp hlimits hg hpR hcR hgR T he hmem
  have hU := eq_lifetime_at_exit_of_generatingTrace hV hg he hmem
  obtain ⟨c, hc⟩ : ∃ c : ℝ, 0 < T → Tendsto (W₀ · ω) (𝓝[<] T) (𝓝 c) := by
    by_cases hT : 0 < T
    · obtain ⟨c, zL, zR, hlim, -⟩ := hlimits T hT hU
      exact ⟨c, fun _ => (continuous_fst.tendsto _).comp hlim⟩
    · exact ⟨0, fun hpos => (hT hpos).elim⟩
  exact thresholdCondition_at_exit_continuous hκ hb hbR hO hbbR hV hVO hp hg hpR hgR
    he hmem c hc (hcR T he)

/-- The deterministic lifetime clause adds no assumption to the pre-existing
stopped identification statement. Its stochastic identification is the separate
(L1) task; this theorem supplies the complete upgrade once that task is proved. -/
theorem flowLineStopIdentLStatement_of_stopIdent
    (hL1 : FlowLineStopIdentStatement.{u}) : FlowLineStopIdentLStatement.{u} := by
  intro κ hκ hκ4 b bR J JR hb hbR O hO hbbR N hN hNO V hV hVb hVN y θ
    S mS Q₀ Q hQ₀ hQ hQ₀Q hQQ₀ H₀ Ĥ hH₀ hĤ hlocal Γ U hflow
  have hstop := hL1 κ hκ hκ4 b bR J JR hb hbR O hO hbbR N hN hNO V hV hVb hVN
    y θ Q₀ Q hQ₀Q hQQ₀ H₀ Ĥ hH₀ hĤ hlocal Γ U hflow
  exact isStoppedFlowLineL_of_isStoppedFlowLine hκ hb hbR hO hbbR hV
    (fun z hz => hNO z (hVN (subset_closure hz))) hQQ₀ hflow hstop

end FlowLines

end InteractingSLE.Restart.FlowStopIdentLL
