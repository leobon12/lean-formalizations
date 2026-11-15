/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FlowStopIdentLLMarks
import InteractingSLE.Spec.Sec7.Lemma76EJunction

/-!
# Real collision intervals, common cuts, and the lifetime clause

Packet PROVE-L1-LL, continuation. Finite collision intervals have common cuts off
both words' jump candidates. Local force coordinates are identified with the
existing geometric images of a common continuous driver, giving their terminal
limits and continuous stopped versions. The terminal real-image rule is kept as
an explicit named input wherever its boundary-tip identification is needed.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Finset
open scoped NNReal ENNReal

namespace InteractingSLE.Restart.FlowStopIdentLL

open Sec2 MartChar.RealFlow

/-! ### Choosing cuts without changing a finite collision interval -/

/-- Move a left endpoint slightly left, inside `O`, without crossing any point
of the finite set. The resulting strict cut selects the original closed interval. -/
theorem exists_left_cut {O : Set ℝ} (hO : IsOpen O) {c : ℝ} (hc : c ∈ O)
    (F : Finset ℝ) :
    ∃ a : ℝ, a ∈ O ∧ a < c ∧ a ∉ F ∧ ∀ z ∈ F, (a < z ↔ c ≤ z) := by
  have hopen : IsOpen (O ∩ ((F.erase c : Finset ℝ) : Set ℝ)ᶜ) :=
    hO.inter (F.erase c).finite_toSet.isClosed.isOpen_compl
  have hmem : c ∈ O ∩ ((F.erase c : Finset ℝ) : Set ℝ)ᶜ := ⟨hc, by simp⟩
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (hopen.mem_nhds hmem)
  let a := c - ε / 2
  have hac : a < c := by dsimp [a]; linarith only [hε]
  have haB : a ∈ Metric.ball c ε := by
    rw [Metric.mem_ball, Real.dist_eq, abs_sub_lt_iff]
    dsimp [a]
    constructor <;> linarith only [hε]
  have haF : a ∉ F := fun ha => (hball haB).2
    (Finset.mem_erase.2 ⟨hac.ne, ha⟩)
  refine ⟨a, (hball haB).1, hac, haF, fun z hz => ⟨fun haz => ?_, fun hcz => hac.trans_le hcz⟩⟩
  by_contra hcz
  have hzc : z < c := lt_of_not_ge hcz
  have hzB : z ∈ Metric.ball c ε := by
    rw [Metric.mem_ball, Real.dist_eq, abs_of_neg (sub_neg.2 hzc)]
    dsimp [a] at haz
    linarith only [haz, hε]
  exact (hball hzB).2 (Finset.mem_erase.2 ⟨hzc.ne, hz⟩)

/-- Move a right endpoint slightly right without changing which finite points
are in its closed lower interval. -/
theorem exists_right_cut {O : Set ℝ} (hO : IsOpen O) {c : ℝ} (hc : c ∈ O)
    (F : Finset ℝ) :
    ∃ a : ℝ, a ∈ O ∧ c < a ∧ a ∉ F ∧ ∀ z ∈ F, (z ≤ a ↔ z ≤ c) := by
  have hopen : IsOpen (O ∩ ((F.erase c : Finset ℝ) : Set ℝ)ᶜ) :=
    hO.inter (F.erase c).finite_toSet.isClosed.isOpen_compl
  have hmem : c ∈ O ∩ ((F.erase c : Finset ℝ) : Set ℝ)ᶜ := ⟨hc, by simp⟩
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (hopen.mem_nhds hmem)
  let a := c + ε / 2
  have hca : c < a := by dsimp [a]; linarith only [hε]
  have haB : a ∈ Metric.ball c ε := by
    rw [Metric.mem_ball, Real.dist_eq, abs_sub_lt_iff]
    dsimp [a]
    constructor <;> linarith only [hε]
  have haF : a ∉ F := fun ha => (hball haB).2
    (Finset.mem_erase.2 ⟨hca.ne', ha⟩)
  refine ⟨a, (hball haB).1, hca, haF, fun z hz => ⟨fun hza => ?_, fun hzc => hzc.trans hca.le⟩⟩
  by_contra hzc
  have hcz : c < z := lt_of_not_ge hzc
  have hzB : z ∈ Metric.ball c ε := by
    rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (sub_pos.2 hcz)]
    dsimp [a] at hza
    linarith only [hza, hε]
  exact (hball hzB).2 (Finset.mem_erase.2 ⟨hcz.ne', hz⟩)

/-- The physical position of a left mark is the seed or a jump candidate. -/
theorem physical_flowLineXL_mem (b : ℝ → ℝ) (J : Finset ℝ) (y : ℝ)
    (i : Fin (flowLineNL b J y)) : y + flowLineXL b J y i ∈ insert y J := by
  revert i
  unfold flowLineXL flowLineNL
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Fin.cons_zero, add_zero, mem_insert_self]
  · have hz := Finset.orderEmbOfFin_mem
      ((PiecewiseConstantBoundaryData.jumpSet b J).filter (· < y)) rfl (Fin.rev j)
    have hzJ := (Finset.mem_filter.1 (Finset.mem_filter.1 hz).1).1
    simp only [Fin.cons_succ]
    exact mem_insert_of_mem (by convert hzJ using 1; ring)

/-- The physical position of a right mark is the seed or a jump candidate. -/
theorem physical_flowLineXR_mem (b : ℝ → ℝ) (J : Finset ℝ) (y : ℝ)
    (i : Fin (flowLineNR b J y)) : y + flowLineXR b J y i ∈ insert y J := by
  rcases Sec7.Lemma76E.flowLineXR_cases y i with h0 | ⟨z, hz, -, he⟩
  · rw [h0, add_zero]
    exact mem_insert_self _ _
  · rw [he, show y + (z - y) = z by ring]
    exact mem_insert_of_mem hz

section Cuts

variable {b bR : ℝ → ℝ} {J JR : Finset ℝ} {y : ℝ} {O : Set ℝ}
  {w wR : ℝ} {vL : Fin (flowLineNL b J y) → ℝ}
  {vR : Fin (flowLineNR b J y) → ℝ} {vLR : Fin (flowLineNL bR JR y) → ℝ}
  {vRR : Fin (flowLineNR bR JR y) → ℝ}

/-- **The geometric finite-cut step.** If both words' collision groups are the
same physical closed intervals from the seed, whose endpoints lie in `O`, then
there are common strict cuts in `O` off both finite sets of jump candidates. -/
theorem hasCommonCollisionCuts_of_real_intervals (hO : IsOpen O)
    (hL : ((∀ i, vL i ≠ w) ∧ ∀ i, vLR i ≠ wR) ∨
      ∃ c : ℝ, c ∈ O ∧ c ≤ y ∧
        (∀ i, vL i = w ↔ c ≤ y + flowLineXL b J y i) ∧
        (∀ i, vLR i = wR ↔ c ≤ y + flowLineXL bR JR y i))
    (hR : ((∀ i, vR i ≠ w) ∧ ∀ i, vRR i ≠ wR) ∨
      ∃ c : ℝ, c ∈ O ∧ y ≤ c ∧
        (∀ i, vR i = w ↔ y + flowLineXR b J y i ≤ c) ∧
        (∀ i, vRR i = wR ↔ y + flowLineXR bR JR y i ≤ c)) :
    HasCommonCollisionCuts b J bR JR y O w vL vR wR vLR vRR := by
  classical
  let F : Finset ℝ := insert y (J ∪ JR)
  have hincL : insert y J ⊆ F := Finset.insert_subset_insert y Finset.subset_union_left
  have hincR : insert y JR ⊆ F := Finset.insert_subset_insert y Finset.subset_union_right
  constructor
  · rcases hL with hnone | ⟨c, hcO, hcy, hc, hcR⟩
    · exact Or.inl hnone
    obtain ⟨a, haO, hac, haF, hcut⟩ := exists_left_cut hO hcO F
    have haJ : a ∉ J := fun h => haF (mem_insert_of_mem (mem_union_left JR h))
    have haJR : a ∉ JR := fun h => haF (mem_insert_of_mem (mem_union_right J h))
    refine Or.inr ⟨a, haO, hac.trans_le hcy, haJ, haJR, fun i => ?_, fun i => ?_⟩
    · rw [hc i, ← hcut _ (hincL (physical_flowLineXL_mem b J y i))]
      constructor <;> intro h <;> linarith only [h]
    · rw [hcR i, ← hcut _ (hincR (physical_flowLineXL_mem bR JR y i))]
      constructor <;> intro h <;> linarith only [h]
  · rcases hR with hnone | ⟨c, hcO, hyc, hc, hcR⟩
    · exact Or.inl hnone
    obtain ⟨a, haO, hca, haF, hcut⟩ := exists_right_cut hO hcO F
    have haJ : a ∉ J := fun h => haF (mem_insert_of_mem (mem_union_left JR h))
    have haJR : a ∉ JR := fun h => haF (mem_insert_of_mem (mem_union_right J h))
    refine Or.inr ⟨a, haO, hyc.trans_lt hca, haJ, haJR, fun i => ?_, fun i => ?_⟩
    · rw [hc i, ← hcut _ (hincL (physical_flowLineXR_mem b J y i))]
      constructor <;> intro h <;> linarith only [h]
    · rw [hcR i, ← hcut _ (hincR (physical_flowLineXR_mem bR JR y i))]
      constructor <;> intro h <;> linarith only [h]

end Cuts

/-! ### Local force coordinates and their terminal limits -/

section Images

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
  {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {w β : ℝ≥0 → ℝ}
  {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {ζ : ℝ≥0∞}
  {D : ℝ → ℝ}

/-- Adapter of the existing scalar force-image theorem to a local word and
any continuous extension of its driver. No maximality clause is needed. -/
theorem right_mark_eq_image
    (hp : IsSLEPathUpTo κ xL xR ρL ρR w vL vR β ζ)
    (hD : Continuous D) (hD0 : D 0 = 0)
    (heq : ∀ s : ℝ≥0, (s : ℝ≥0∞) < ζ → D s = w s)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) (i : Fin nR) :
    vR i t = rightImg D (xR i) t := by
  have htime : ∀ s ∈ Icc (0 : ℝ) t, (s.toNNReal : ℝ≥0∞) < ζ :=
    fun s hs => toNNReal_lt_of_mem_Icc ht hs
  have hfr : ∀ s ∈ Icc (0 : ℝ) t, D s = w s.toNNReal := by
    intro s hs
    simpa only [Real.coe_toNNReal s hs.1] using heq s.toNNReal (htime s hs)
  have h0 : ((0 : ℝ≥0) : ℝ≥0∞) < ζ := lt_of_le_of_lt (by simp) ht
  have hx : 0 ≤ xR i := by
    simpa only [hp.w_zero, hp.vR_zero] using hp.w_le_vR h0 i
  have hint : IntervalIntegrable
      (fun s : ℝ => 2 / (vR i s.toNNReal - D s)) volume 0 t := by
    refine ((hp.integrable_gapR ht i).const_mul (-2)).congr fun s hs => ?_
    rw [uIoc_of_le t.coe_nonneg] at hs
    rw [hfr s ⟨hs.1.le, hs.2⟩, div_eq_mul_inv, ← neg_sub, inv_neg]
    ring
  have hn : volume {s : ℝ | s ∈ Icc 0 (t : ℝ) ∧ D s = vR i s.toNNReal} = 0 := by
    refine measure_mono_null (fun s hs => ?_) (hp.volume_collisionR i)
    exact ⟨hs.1.1, htime s hs.1, (hfr s hs.1).symm.trans hs.2⟩
  have h := WangWu.eq_rightImg_of_forceEq (v := fun s : ℝ => vR i s.toNNReal)
    hD hD0 hx
    ((hp.continuousOn_vR i).comp continuous_real_toNNReal.continuousOn htime)
    (fun s hs => by rw [hfr s hs]; exact hp.w_le_vR (htime s hs) i) hint
    (fun s hs => by
      have hv := hp.vR_eq (htime s hs) i
      rw [Real.coe_toNNReal s hs.1] at hv
      rw [hv]
      congr 1
      refine intervalIntegral.integral_congr fun r hr => ?_
      rw [uIcc_of_le hs.1] at hr
      rw [hfr r ⟨hr.1, hr.2.trans hs.2⟩]) hn ⟨t.coe_nonneg, le_rfl⟩
  simpa only [Real.toNNReal_coe] using h

/-- Left force coordinates are the reflected geometric images. -/
theorem left_mark_eq_image
    (hp : IsSLEPathUpTo κ xL xR ρL ρR w vL vR β ζ)
    (hD : Continuous D) (hD0 : D 0 = 0)
    (heq : ∀ s : ℝ≥0, (s : ℝ≥0∞) < ζ → D s = w s)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) (i : Fin nL) :
    vL i t = -rightImg (fun s => -D s) (-xL i) t := by
  have h := right_mark_eq_image hp.reflect hD.neg (by simp [hD0])
    (fun s hs => congrArg Neg.neg (heq s hs)) ht i
  exact neg_eq_iff_eq_neg.1 h

/-- The geometric state of a word for a continuous real driver. -/
def imageState (D : ℝ → ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ)
    (t : ℝ≥0) : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) :=
  (D t, fun i => -rightImg (fun s => -D s) (-xL i) t,
    fun j => rightImg D (xR j) t)

/-- Geometric force images are continuous even at a finite terminal time. -/
theorem continuous_imageState (hD : Continuous D) :
    Continuous (imageState D xL xR) := by
  exact (hD.comp NNReal.continuous_coe).prodMk
    ((continuous_pi fun i => ((continuousOn_rightImg hD.neg (-xL i)).comp_continuous
      NNReal.continuous_coe (fun t => t.coe_nonneg)).neg).prodMk
    (continuous_pi fun j => (continuousOn_rightImg hD (xR j)).comp_continuous
      NNReal.continuous_coe (fun t => t.coe_nonneg)))

/-- A continuous driver extension supplies a terminal limit for the entire
local word, including marks which the original word did not contain. -/
theorem tendsto_state_imageState
    (hp : IsSLEPathUpTo κ xL xR ρL ρR w vL vR β ζ)
    (hD : Continuous D) (hD0 : D 0 = 0)
    (heq : ∀ s : ℝ≥0, (s : ℝ≥0∞) < ζ → D s = w s)
    {T : ℝ≥0} (hT : (T : ℝ≥0∞) = ζ) :
    Tendsto (fun t => (w t, fun i => vL i t, fun j => vR j t))
      (𝓝[<] T) (𝓝 (imageState D xL xR T)) := by
  refine ((continuous_imageState hD).continuousAt.tendsto.mono_left
    nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have htζ : (t : ℝ≥0∞) < ζ := hT ▸ ENNReal.coe_lt_coe.2 ht
  exact Prod.ext (heq t htζ) (Prod.ext
    (funext fun i => (left_mark_eq_image hp hD hD0 heq htζ i).symm)
    (funext fun j => (right_mark_eq_image hp hD hD0 heq htζ j).symm))

end Images

section CloseState

variable {nL nR : ℕ}

/-- Close every coordinate by its specified terminal value. This deterministic
version is identified with the measurable stopped reader at positive lifetimes. -/
def closeState (T : ℝ≥0) (w : ℝ≥0 → ℝ) (vL : Fin nL → ℝ≥0 → ℝ)
    (vR : Fin nR → ℝ≥0 → ℝ) (z : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ))
    (t : ℝ≥0) : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) :=
  (closeAt T w z.1 t, fun i => closeAt T (vL i) (z.2.1 i) t,
    fun j => closeAt T (vR j) (z.2.2 j) t)

theorem closeState_self {T : ℝ≥0} {w : ℝ≥0 → ℝ}
    {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ}
    {z : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)} : closeState T w vL vR z T = z := by
  simp only [closeState, closeAt_self]

/-- Closing a local state by its left limit gives continuity through the lifetime. -/
theorem continuous_closeState {T : ℝ≥0} {w : ℝ≥0 → ℝ}
    {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ}
    {z : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)}
    (hc : ContinuousOn (fun t => (w t, fun i => vL i t, fun j => vR j t)) (Iio T))
    (hlim : Tendsto (fun t => (w t, fun i => vL i t, fun j => vR j t))
      (𝓝[<] T) (𝓝 z)) : Continuous (closeState T w vL vR z) := by
  have hwc := continuous_fst.comp_continuousOn hc
  have hLc := continuous_fst.comp_continuousOn (continuous_snd.comp_continuousOn hc)
  have hRc := continuous_snd.comp_continuousOn (continuous_snd.comp_continuousOn hc)
  have hwlim := (continuous_fst.tendsto _).comp hlim
  have hLlim := ((continuous_fst.comp continuous_snd).tendsto _).comp hlim
  have hRlim := ((continuous_snd.comp continuous_snd).tendsto _).comp hlim
  exact (continuous_closeAt_of_tendsto hwc hwlim).prodMk
    ((continuous_pi fun i => continuous_closeAt_of_tendsto ((continuousOn_pi.1 hLc) i)
      (((continuous_apply i).tendsto _).comp hLlim)).prodMk
    (continuous_pi fun j => continuous_closeAt_of_tendsto ((continuousOn_pi.1 hRc) j)
      (((continuous_apply j).tendsto _).comp hRlim)))

end CloseState

section CommonTrace

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
  {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {w w₀ β : ℝ≥0 → ℝ}
  {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ}
  {T : ℝ≥0} {D : ℝ → ℝ} {γ : ℝ≥0 → ℂ}

/-- The common trace transfers a continuous driver extension to every local
word generating that trace, hence supplies that word's whole terminal limit. -/
theorem tendsto_state_of_common_trace
    (hp : IsSLEPathUpTo κ xL xR ρL ρR w vL vR β T)
    (hg₀ : IsGeneratingTrace w₀ T γ) (hg : IsGeneratingTrace w T γ)
    (hD : Continuous D) (hD0 : D 0 = 0)
    (hDw : ∀ s : ℝ≥0, s < T → D s = w₀ s) :
    Tendsto (fun t => (w t, fun i => vL i t, fun j => vR j t))
      (𝓝[<] T) (𝓝 (imageState D xL xR T)) := by
  apply tendsto_state_imageState hp hD hD0 ?_ rfl
  intro s hs
  exact (hDw s (ENNReal.coe_lt_coe.1 hs)).trans
    (Sec7.SideHeight.eq_of_isGeneratingTrace hg₀ hg hs)

/-- Continuity through the lifetime of the replacement state needs no terminal
collision rule. It follows from the common trace and a driver limit alone. -/
theorem continuous_closeState_of_common_trace
    (hp : IsSLEPathUpTo κ xL xR ρL ρR w vL vR β T)
    (hg₀ : IsGeneratingTrace w₀ T γ) (hg : IsGeneratingTrace w T γ)
    (hD : Continuous D) (hD0 : D 0 = 0)
    (hDw : ∀ s : ℝ≥0, s < T → D s = w₀ s) :
    Continuous (closeState T w vL vR (imageState D xL xR T)) := by
  apply continuous_closeState ?_ (tendsto_state_of_common_trace hp hg₀ hg hD hD0 hDw)
  have hc := hp.continuousOn_w.prodMk
    ((continuousOn_pi.2 hp.continuousOn_vL).prodMk
      (continuousOn_pi.2 hp.continuousOn_vR))
  simpa only [setOf_lt_coe_eq_Iio T] using hc

/-- The measurable dyadic version of a replacement state is continuous through
every positive finite lifetime, with the geometric images as its terminal value.
This theorem is independent of the terminal collision identification. -/
theorem continuous_stopVal_state_of_common_trace
    {Ω : Type*} {ω : Ω} {ζ : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    (hp : IsSLEPathUpTo κ xL xR ρL ρR (W · ω)
      (fun i t => VL i t ω) (fun j t => VR j t ω) β (ζ ω))
    (hg₀ : IsGeneratingTrace w₀ (ζ ω) γ)
    (hg : IsGeneratingTrace (W · ω) (ζ ω) γ)
    (hT : 0 < T) (hζ : (T : ℝ≥0∞) = ζ ω)
    (hD : Continuous D) (hD0 : D 0 = 0)
    (hDw : ∀ s : ℝ≥0, s < T → D s = w₀ s) :
    Continuous (fun t => (LocalExt.stopVal W (fun x => (ζ x : WithTop ℝ≥0)) t ω,
      fun i => LocalExt.stopVal (VL i) (fun x => (ζ x : WithTop ℝ≥0)) t ω,
      fun j => LocalExt.stopVal (VR j) (fun x => (ζ x : WithTop ℝ≥0)) t ω)) ∧
    (LocalExt.stopVal W (fun x => (ζ x : WithTop ℝ≥0)) T ω,
      fun i => LocalExt.stopVal (VL i) (fun x => (ζ x : WithTop ℝ≥0)) T ω,
      fun j => LocalExt.stopVal (VR j) (fun x => (ζ x : WithTop ℝ≥0)) T ω) =
        imageState D xL xR T := by
  have hpT : IsSLEPathUpTo κ xL xR ρL ρR (W · ω)
      (fun i t => VL i t ω) (fun j t => VR j t ω) β T := by
    simpa only [← hζ] using hp
  have hg₀T : IsGeneratingTrace w₀ T γ := by simpa only [← hζ] using hg₀
  have hgT : IsGeneratingTrace (W · ω) T γ := by simpa only [← hζ] using hg
  have hlim := tendsto_state_of_common_trace hpT hg₀T hgT hD hD0 hDw
  have hc := hp.continuousOn_w.prodMk
    ((continuousOn_pi.2 hp.continuousOn_vL).prodMk
      (continuousOn_pi.2 hp.continuousOn_vR))
  exact ⟨continuous_stopVal_state_of_tendsto hT hζ hc hlim,
    stopVal_state_at_lifetime hT hζ hlim⟩

end CommonTrace

/-! ### The terminal boundary-tip input -/

/-- The missing terminal geometric identification, stated for scalar Loewner
images rather than force words. For a simple generating trace with terminal tip
`p`, a right image meets the driver exactly when the tip is real, on the right,
and beyond its initial point; the left assertion is its reflection.

This is an explicit input, not a theorem asserted here. The existing
`Sec7.Lemma76E.vR_eq_w_iff` concerns strictly pre-lifetime times. Its extension
to the terminal time, where the generating-trace predicate asserts no hull
identity, remains to be proved. -/
def TerminalImageRule (D : ℝ → ℝ) (T : ℝ≥0) (p : ℂ) : Prop :=
  (∀ x : ℝ, 0 ≤ x →
    (rightImg (fun s => -D s) x T = -D T ↔
      p.im = 0 ∧ p.re ≤ 0 ∧ x ≤ -p.re)) ∧
  (∀ x : ℝ, 0 ≤ x →
    (rightImg D x T = D T ↔ p.im = 0 ∧ 0 ≤ p.re ∧ x ≤ p.re))

/-- Left marks of a flow-line word are nonpositive, at every seed. -/
theorem flowLineXL_nonpos_seed (b : ℝ → ℝ) (J : Finset ℝ) (y : ℝ)
    (i : Fin (flowLineNL b J y)) : flowLineXL b J y i ≤ 0 := by
  rcases Supp8.flowLineXL_cases y i with h | ⟨z, -, hz, he⟩
  · exact h.le
  · rw [he]
    exact (sub_neg.2 hz).le

/-- Right marks of a flow-line word are nonnegative, at every seed. -/
theorem flowLineXR_nonneg_seed (b : ℝ → ℝ) (J : Finset ℝ) (y : ℝ)
    (i : Fin (flowLineNR b J y)) : 0 ≤ flowLineXR b J y i := by
  rcases Sec7.Lemma76E.flowLineXR_cases y i with h | ⟨z, -, hz, he⟩
  · exact h.symm.le
  · rw [he]
    exact (sub_pos.2 hz).le

/-- The scalar terminal rule supplies common collision cuts for arbitrary
flow-line words, even when their jump candidates and numbers of marks differ. -/
theorem hasCommonCollisionCuts_imageState
    {b bR : ℝ → ℝ} {J JR : Finset ℝ} {y : ℝ} {O : Set ℝ}
    (hO : IsOpen O) {D : ℝ → ℝ} {T : ℝ≥0} {p : ℂ}
    (hreal : p.im = 0 → y + p.re ∈ O) (himage : TerminalImageRule D T p) :
    HasCommonCollisionCuts b J bR JR y O (D T)
      (fun i => -rightImg (fun s => -D s) (-flowLineXL b J y i) T)
      (fun j => rightImg D (flowLineXR b J y j) T) (D T)
      (fun i => -rightImg (fun s => -D s) (-flowLineXL bR JR y i) T)
      (fun j => rightImg D (flowLineXR bR JR y j) T) := by
  have hL (d : ℝ → ℝ) (K : Finset ℝ) (i : Fin (flowLineNL d K y)) :
      -rightImg (fun s => -D s) (-flowLineXL d K y i) T = D T ↔
        p.im = 0 ∧ p.re ≤ 0 ∧ p.re ≤ flowLineXL d K y i := by
    rw [neg_eq_iff_eq_neg, himage.1 _ (neg_nonneg.2 (flowLineXL_nonpos_seed d K y i))]
    simp only [neg_le_neg_iff]
  have hR (d : ℝ → ℝ) (K : Finset ℝ) (i : Fin (flowLineNR d K y)) :=
    himage.2 _ (flowLineXR_nonneg_seed d K y i)
  apply hasCommonCollisionCuts_of_real_intervals hO
  · by_cases hp : p.im = 0 ∧ p.re ≤ 0
    · refine Or.inr ⟨y + p.re, hreal hp.1, by linarith only [hp.2], ?_, ?_⟩
      · intro i
        rw [hL, and_iff_right hp.1, and_iff_right hp.2]
        constructor <;> intro h <;> linarith only [h]
      · intro i
        rw [hL, and_iff_right hp.1, and_iff_right hp.2]
        constructor <;> intro h <;> linarith only [h]
    · exact Or.inl ⟨fun i h => hp ⟨((hL b J i).1 h).1, ((hL b J i).1 h).2.1⟩,
        fun i h => hp ⟨((hL bR JR i).1 h).1, ((hL bR JR i).1 h).2.1⟩⟩
  · by_cases hp : p.im = 0 ∧ 0 ≤ p.re
    · refine Or.inr ⟨y + p.re, hreal hp.1, by linarith only [hp.2], ?_, ?_⟩
      · intro i
        rw [hR, and_iff_right hp.1, and_iff_right hp.2]
        constructor <;> intro h <;> linarith only [h]
      · intro i
        rw [hR, and_iff_right hp.1, and_iff_right hp.2]
        constructor <;> intro h <;> linarith only [h]
    · exact Or.inl ⟨fun i h => hp ⟨((hR b J i).1 h).1, ((hR b J i).1 h).2.1⟩,
        fun i h => hp ⟨((hR bR JR i).1 h).1, ((hR bR JR i).1 h).2.1⟩⟩

/-! ### Deterministic assembly of the lifetime clause -/

/-- At time zero both collision groups have the common physical endpoint `y`.
The common-cut assertion therefore needs no terminal Loewner input. -/
theorem hasCommonCollisionCuts_initial
    {b bR : ℝ → ℝ} {J JR : Finset ℝ} {y : ℝ} {O : Set ℝ}
    (hO : IsOpen O) (hy : y ∈ O) :
    HasCommonCollisionCuts b J bR JR y O 0 (flowLineXL b J y) (flowLineXR b J y)
      0 (flowLineXL bR JR y) (flowLineXR bR JR y) := by
  apply hasCommonCollisionCuts_of_real_intervals hO
  · refine Or.inr ⟨y, hy, le_rfl, fun i => ?_, fun i => ?_⟩
    · have hx := flowLineXL_nonpos_seed b J y i
      constructor <;> intro h <;> linarith only [h, hx]
    · have hx := flowLineXL_nonpos_seed bR JR y i
      constructor <;> intro h <;> linarith only [h, hx]
  · refine Or.inr ⟨y, hy, le_rfl, fun i => ?_, fun i => ?_⟩
    · have hx := flowLineXR_nonneg_seed b J y i
      constructor <;> intro h <;> linarith only [h, hx]
    · have hx := flowLineXR_nonneg_seed bR JR y i
      constructor <;> intro h <;> linarith only [h, hx]

section Lifetime

variable {κ θ y : ℝ} {b bR : ℝ → ℝ} {J JR : Finset ℝ} {O : Set ℝ}
  {V : Set ℂ} {w wR β βR : ℝ≥0 → ℝ}
  {vL : Fin (flowLineNL b J y) → ℝ≥0 → ℝ}
  {vR : Fin (flowLineNR b J y) → ℝ≥0 → ℝ}
  {vLR : Fin (flowLineNL bR JR y) → ℝ≥0 → ℝ}
  {vRR : Fin (flowLineNR bR JR y) → ℝ≥0 → ℝ}
  {U : ℝ≥0∞} {Γ : ℝ≥0 → ℂ} {T : ℝ≥0} {D : ℝ → ℝ}

/-- **The deterministic positive-lifetime clause of (L1).** The original full
word and the replacement local word generate the same trace up to the exit.
If the terminal point is still in `V`, the replacement state has a continuous
closed version whose terminal state is at threshold. The only geometric input
left explicit is the scalar `TerminalImageRule`. -/
theorem lifetime_clause_pos_of_terminalImageRule
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
    (hDw : ∀ s : ℝ≥0, s < T → D s = w s)
    (himage : TerminalImageRule D T (Γ T - y)) :
    Continuous (closeState T wR vLR vRR
      (imageState D (flowLineXL bR JR y) (flowLineXR bR JR y) T)) ∧
    ForceWord.ThresholdCondition (flowLineRhoL κ bR JR y θ)
      (flowLineRhoR κ bR JR y θ) (D T)
      (fun i => -rightImg (fun s => -D s) (-flowLineXL bR JR y i) T)
      (fun j => rightImg D (flowLineXR bR JR y j) T) := by
  have hΓ : ContinuousOn Γ {t | (t : ℝ≥0∞) < U} := by
    have h := (hg.2.1.mono (fun (s : ℝ≥0) (ht : (s : ℝ≥0∞) < U) => ht.le)).add
      (continuousOn_const (c := (y : ℂ)))
    change ContinuousOn (fun t => (Γ t - y) + y) {t | (t : ℝ≥0∞) < U} at h
    simpa only [sub_add_cancel] using h
  have hU := eq_lifetime_of_mem_exitTime hV hΓ he hmem
  have hpT : IsSLEPathUpTo κ (flowLineXL b J y) (flowLineXR b J y)
      (flowLineRhoL κ b J y θ) (flowLineRhoR κ b J y θ) w vL vR β T :=
    hp.isSLEPathUpTo hU.le
  have hpRT : IsSLEPathUpTo κ (flowLineXL bR JR y) (flowLineXR bR JR y)
      (flowLineRhoL κ bR JR y θ) (flowLineRhoR κ bR JR y θ) wR vLR vRR βR T := by
    simpa only [← he] using hpR
  have hgT : IsGeneratingTrace w T (fun t => Γ t - y) := by
    simpa only [← hU] using hg
  have hgRT : IsGeneratingTrace wR T (fun t => Γ t - y) := by
    simpa only [← he] using hgR
  have hDwT : ∀ s : ℝ≥0, (s : ℝ≥0∞) < T → D s = w s :=
    fun s hs => hDw s (ENNReal.coe_lt_coe.1 hs)
  have hDwR : ∀ s : ℝ≥0, (s : ℝ≥0∞) < T → D s = wR s :=
    fun s hs => (hDwT s hs).trans (Sec7.SideHeight.eq_of_isGeneratingTrace hgT hgRT hs)
  have hlim := tendsto_state_imageState hpT hD hD0 hDwT rfl
  have hlimR := tendsto_state_imageState hpRT hD hD0 hDwR rfl
  have hthr := hp.isForcePath.threshold_of_tendsto hT hU hlim
  have hcuts := hasCommonCollisionCuts_imageState (b := b) (J := J)
    (bR := bR) (JR := JR) (y := y) hO (fun hreal => ?_) himage
  · refine ⟨continuous_closeState ?_ hlimR,
      (thresholdCondition_iff_of_commonCollisionCuts hκ hb hbR hbbR hcuts).1 hthr⟩
    have hset : {t : ℝ≥0 | (t : ℝ≥0∞) < (T : ℝ≥0∞)} = Iio T :=
      setOf_lt_coe_eq_Iio T
    have hc := hpRT.continuousOn_w.prodMk
      ((continuousOn_pi.2 hpRT.continuousOn_vL).prodMk
        (continuousOn_pi.2 hpRT.continuousOn_vR))
    rwa [hset] at hc
  · have hreal' : (Γ T).im = 0 := by simpa using hreal
    have h := hVO (Γ T) hmem hreal'
    have heq : y + (Γ T - (y : ℂ)).re = (Γ T).re := by simp
    rwa [heq]

/-- **The assembled deterministic lifetime clause, including a zero lifetime.**
Only a driver limit from the original full word is required; the replacement
word's force limits are derived. Closing by these limits gives a continuous
state, preserves all earlier values and the initial state, and puts its terminal
value at threshold. `himage` is the explicitly unresolved scalar terminal rule.
The source evolution supplies `hlim` by Auxiliary lemma 3. -/
theorem lifetime_clause_of_driver_limit
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
    (himage : 0 < T → TerminalImageRule (FiniteEndpoint.extDriver w T c) T (Γ T - y)) :
    ∃ z : ℝ × (Fin (flowLineNL bR JR y) → ℝ) × (Fin (flowLineNR bR JR y) → ℝ),
      Continuous (closeState T wR vLR vRR z) ∧
      (∀ t : ℝ≥0, t < T ∨ t = 0 →
        closeState T wR vLR vRR z t = (wR t, fun i => vLR i t, fun j => vRR j t)) ∧
      ForceWord.ThresholdCondition (flowLineRhoL κ bR JR y θ)
        (flowLineRhoR κ bR JR y θ) (closeState T wR vLR vRR z T).1
        (closeState T wR vLR vRR z T).2.1 (closeState T wR vLR vRR z T).2.2 := by
  have hΓ : ContinuousOn Γ {t | (t : ℝ≥0∞) < U} := by
    have h := (hg.2.1.mono (fun (s : ℝ≥0) (ht : (s : ℝ≥0∞) < U) => ht.le)).add
      (continuousOn_const (c := (y : ℂ)))
    change ContinuousOn (fun t => (Γ t - y) + y) {t | (t : ℝ≥0∞) < U} at h
    simpa only [sub_add_cancel] using h
  have hU := eq_lifetime_of_mem_exitTime hV hΓ he hmem
  rcases eq_or_lt_of_le (show (0 : ℝ≥0) ≤ T from zero_le) with hT | hT
  · subst T
    have hy : y ∈ O := by
      have hΓ0 : Γ 0 = y := sub_eq_zero.1 hg.1
      have h := hVO (Γ 0) hmem (by simp [hΓ0])
      simpa only [hΓ0, Complex.ofReal_re] using h
    have hcuts := hasCommonCollisionCuts_initial (b := b) (J := J)
      (bR := bR) (JR := JR) hO hy
    have hthr := (thresholdCondition_iff_of_commonCollisionCuts hκ hb hbR hbbR hcuts).1
      (hp.isForcePath.threshold_of_eq_zero hU.symm)
    refine ⟨(wR 0, fun i => vLR i 0, fun j => vRR j 0), ?_, ?_, ?_⟩
    · have heq : closeState 0 wR vLR vRR
          (wR 0, fun i => vLR i 0, fun j => vRR j 0) =
          fun _ => (wR 0, fun i => vLR i 0, fun j => vRR j 0) := by
        funext t
        simp [closeState, closeAt]
      rw [heq]
      exact continuous_const
    · intro t ht
      rcases ht with ht | rfl
      · exact (not_lt_of_ge (show (0 : ℝ≥0) ≤ t from zero_le) ht).elim
      · exact closeState_self
    · simpa only [closeState_self, hpR.w_zero, hpR.vL_zero, hpR.vR_zero] using hthr
  · have hpT := hp.isSLEPathUpTo hU.le
    have hc : ContinuousOn w (Iio T) := by
      simpa only [← setOf_lt_coe_eq_Iio T] using hpT.continuousOn_w
    have hD : Continuous (FiniteEndpoint.extDriver w T c) :=
      FiniteEndpoint.continuous_extDriver hc (hlim hT)
    have hD0 : FiniteEndpoint.extDriver w T c 0 = 0 := by
      simp only [FiniteEndpoint.extDriver, Real.toNNReal_zero, ite_eq_left hT, hpT.w_zero]
    have hDw : ∀ s : ℝ≥0, s < T → FiniteEndpoint.extDriver w T c s = w s := by
      intro s hs
      simp only [FiniteEndpoint.extDriver, Real.toNNReal_coe, ite_eq_left hs]
    obtain ⟨hcont, hthr⟩ := lifetime_clause_pos_of_terminalImageRule hκ hb hbR hO hbbR
      hV hVO hp hg hpR hgR hT he hmem hD hD0 hDw (himage hT)
    refine ⟨imageState (FiniteEndpoint.extDriver w T c)
      (flowLineXL bR JR y) (flowLineXR bR JR y) T, hcont, ?_, ?_⟩
    · intro t ht
      have htT : t < T := ht.elim id (fun ht0 => ht0 ▸ hT)
      simp only [closeState, closeAt, ite_eq_left htT]
    · simpa only [closeState_self, imageState] using hthr

/-- The positive-lifetime clause for the actual measurable stopped reader used
by (L1). Its continuity is derived independently of the collision rule; its
terminal threshold follows from the deterministic lifetime assembly above. -/
theorem lifetime_clause_stopVal_pos
    {Ω : Type*} {ω : Ω} {ζ : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin (flowLineNL bR JR y) → ℝ≥0 → Ω → ℝ}
    {VR : Fin (flowLineNR bR JR y) → ℝ≥0 → Ω → ℝ}
    (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b J)
    (hbR : IsPiecewiseConstantBoundaryData bR JR) (hO : IsOpen O)
    (hbbR : ∀ a ∈ O, b a = bR a) (hV : IsOpen V)
    (hVO : ∀ z ∈ V, z.im = 0 → z.re ∈ O)
    (hp : IsIntegratedSLEPath κ (flowLineXL b J y) (flowLineXR b J y)
      (flowLineRhoL κ b J y θ) (flowLineRhoR κ b J y θ) w vL vR β U)
    (hg : IsGeneratingTrace w U (fun t => Γ t - y))
    (hpR : IsSLEPathUpTo κ (flowLineXL bR JR y) (flowLineXR bR JR y)
      (flowLineRhoL κ bR JR y θ) (flowLineRhoR κ bR JR y θ) (W · ω)
      (fun i t => VL i t ω) (fun j t => VR j t ω) βR (ζ ω))
    (hgR : IsGeneratingTrace (W · ω) (ζ ω) (fun t => Γ t - y))
    (hζ : ζ ω = RLC.exitTime V Γ U) (hT : 0 < T) (he : (T : ℝ≥0∞) = ζ ω)
    (hmem : Γ T ∈ V) (hD : Continuous D) (hD0 : D 0 = 0)
    (hDw : ∀ s : ℝ≥0, s < T → D s = w s)
    (himage : TerminalImageRule D T (Γ T - y)) :
    Continuous (fun t => (LocalExt.stopVal W (fun x => (ζ x : WithTop ℝ≥0)) t ω,
      fun i => LocalExt.stopVal (VL i) (fun x => (ζ x : WithTop ℝ≥0)) t ω,
      fun j => LocalExt.stopVal (VR j) (fun x => (ζ x : WithTop ℝ≥0)) t ω)) ∧
    ForceWord.ThresholdCondition (flowLineRhoL κ bR JR y θ)
      (flowLineRhoR κ bR JR y θ)
      (LocalExt.stopVal W (fun x => (ζ x : WithTop ℝ≥0)) T ω)
      (fun i => LocalExt.stopVal (VL i) (fun x => (ζ x : WithTop ℝ≥0)) T ω)
      (fun j => LocalExt.stopVal (VR j) (fun x => (ζ x : WithTop ℝ≥0)) T ω) := by
  have hpRe : IsSLEPathUpTo κ (flowLineXL bR JR y) (flowLineXR bR JR y)
      (flowLineRhoL κ bR JR y θ) (flowLineRhoR κ bR JR y θ) (W · ω)
      (fun i t => VL i t ω) (fun j t => VR j t ω) βR (RLC.exitTime V Γ U) := by
    simpa only [hζ] using hpR
  have hgRe : IsGeneratingTrace (W · ω) (RLC.exitTime V Γ U) (fun t => Γ t - y) := by
    simpa only [hζ] using hgR
  have hle : ζ ω ≤ U := by rw [hζ]; exact min_le_left _ _
  have hgζ := LP.isGeneratingTrace_mono hg hle
  obtain ⟨hcont, hstate⟩ := continuous_stopVal_state_of_common_trace hpR hgζ hgR
    hT he hD hD0 hDw
  have hthr := (lifetime_clause_pos_of_terminalImageRule hκ hb hbR hO hbbR hV hVO hp
    hg hpRe hgRe hT (he.trans hζ) hmem hD hD0 hDw himage).2
  refine ⟨hcont, ?_⟩
  have h := congrArg (fun z : ℝ × (Fin (flowLineNL bR JR y) → ℝ) ×
      (Fin (flowLineNR bR JR y) → ℝ) =>
    ForceWord.ThresholdCondition (flowLineRhoL κ bR JR y θ)
      (flowLineRhoR κ bR JR y θ) z.1 z.2.1 z.2.2) hstate
  exact h ▸ hthr

end Lifetime

end InteractingSLE.Restart.FlowStopIdentLL
