/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSeedOpen
import InteractingSLE.Spec.Sec7.PocketJordanInf

/-!
# The boundary orientation of an arbitrary Jordan coordinate of a change pocket

PROVE-SIDE-ANCHOR. The flow-chart orientation `PocketMarks.IsFlowChartOriented` (Aux. lemma 119: "The left incoming
arc maps to `ℝ₋` and the right one to `ℝ₊`") is stated for every two-point uniformizer of the Cayley image of the
change pocket. The side tests of the late wiring of Theorems 1.2–1.3 use an **arbitrary** Jordan coordinate `ψ` of the
inverted pocket (`IsCfJordan`, `IsCfJordanInf`), not the canonical one of `exists_measurable_pocketMarks_pts`. Here a
Jordan coordinate is turned back into a two-point uniformizer (`jordanUnif p ψ w = m(ψ(cfPt w))`, `m(z) = −1/z`,
`p ↦ 0`), the converse of `PocketJordan.isJordanCoord_cfCoord`. Hence every Jordan coordinate sends the open right-wall
arc to the negative and the open left-wall arc to the positive half-line (`jordan_sides`, `jordanInf_sides`): the
distant marks of the late pocket words are on the correct sides of the seed for every chart.

## Main results

* `isBdryUniformizer_jordanUnif`, `isBdryUniformizer_jordanUnif_inf`;
* **`IsChangeConfigInc.jordan_sides`** (bounded pocket), **`IsChangeConfigInc.jordanInf_sides`** (pocket opening at
  the flow seed).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Filter Topology Metric Function Bornology
open QuantumZipper (H Hbar)
open QuantumZipper.CA (cayley cayleyInv)
open SupercriticalConformalCovariance (IsConformalBijection)
open InteractingSLE.WangWu (negInv)
open scoped NNReal

namespace InteractingSLE.Sec7.SideAnc

open WangWu PocketCoord Lemma71I PocketJordan PocketMarks

/-- **The uniformizer of a Jordan coordinate**: `w ↦ m(ψ(cfPt w))`, `m(z) = −1/z`, and `p ↦ 0`. -/
def jordanUnif (p : ℂ) (ψ : ℂ → ℂ) (w : ℂ) : ℂ :=
  open scoped Classical in if w = p then 0 else negInv (ψ (cfPt w))

theorem jordanUnif_self (p : ℂ) (ψ : ℂ → ℂ) : jordanUnif p ψ p = 0 := by simp [jordanUnif]

theorem jordanUnif_of_ne {p : ℂ} {ψ : ℂ → ℂ} {w : ℂ} (hw : w ≠ p) : jordanUnif p ψ w = negInv (ψ (cfPt w)) := by
  simp [jordanUnif, hw]

theorem norm_jordanUnif_of_ne {p : ℂ} {ψ : ℂ → ℂ} {w : ℂ} (hw : w ≠ p) :
    ‖jordanUnif p ψ w‖ = ‖(ψ (cfPt w))⁻¹‖ := by
  rw [jordanUnif_of_ne hw, WangWu.negInv, norm_neg]

theorem ne_neg_one_of_mem_cayley_image {C : Set ℂ} (hCH : C ⊆ H) {w : ℂ} (hw : w ∈ cayley '' C) : w ≠ -1 :=
  fun h => by
    have := Lemma71F.cayley_image_subset_ball hCH hw
    rw [h, mem_ball_zero_iff, norm_neg, norm_one] at this
    exact lt_irrefl _ this

theorem differentiableAt_cfPt {w : ℂ} (hw : w ≠ -1) : DifferentiableAt ℂ cfPt w := by
  have hw' : -w ≠ 1 := fun h => hw (by rw [← neg_neg w, h])
  exact (QuantumZipper.CA.differentiableAt_cayleyInv hw').comp w differentiableAt_id.neg

/-- `cfPt` is a conformal bijection of the Cayley image onto the inverted pocket. -/
theorem isConformalBijection_cfPt {C : Set ℂ} (hCH : C ⊆ H) :
    IsConformalBijection cfPt (cayley '' C) (negInv '' C) := by
  refine ⟨fun w hw => (differentiableAt_cfPt (ne_neg_one_of_mem_cayley_image hCH hw)).differentiableWithinAt,
    ?_, injOn_cfPt.mono fun w hw => ne_neg_one_of_mem_cayley_image hCH hw, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    rw [cfPt_cayley (H_subset_Hbar' (hCH hz)) (PocketJordan.ne_zero_of_mem_H (hCH hz))]
    exact mem_image_of_mem _ hz
  · rw [image_negInv_eq hCH]
    exact surjOn_image _ _

theorem cfPt_mem_closure_image {C : Set ℂ} (hCH : C ⊆ H) {w : ℂ} (hw : w ∈ closure (cayley '' C))
    (hw1 : w ≠ -1) : cfPt w ∈ closure (negInv '' C) := by
  have := (continuousAt_cfPt hw1).continuousWithinAt.mem_closure_image hw
  rwa [← image_negInv_eq hCH] at this

/-- `‖cfPt w‖ → ∞` as `w → −1`. -/
theorem tendsto_norm_cfPt_neg_one : Tendsto (fun w => ‖cfPt w‖) (𝓝[≠] (-1 : ℂ)) atTop := by
  have h1 : Tendsto (fun w : ℂ => ‖1 - w‖) (𝓝[≠] (-1 : ℂ)) (𝓝 2) := by
    have : Tendsto (fun w : ℂ => ‖1 - w‖) (𝓝 (-1 : ℂ)) (𝓝 ‖1 - (-1 : ℂ)‖) :=
      ((continuous_const.sub continuous_id).norm).tendsto _
    refine (this.mono_left nhdsWithin_le_nhds).congr' (Eventually.of_forall fun _ => rfl) |>.trans ?_
    norm_num
  have h2 : Tendsto (fun w : ℂ => 1 + w) (𝓝[≠] (-1 : ℂ)) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun w hw h => hw ?_⟩
    · have : Tendsto (fun w : ℂ => 1 + w) (𝓝 (-1 : ℂ)) (𝓝 (1 + -1)) := (continuous_const.add continuous_id).tendsto _
      rw [add_neg_cancel] at this
      exact this.mono_left nhdsWithin_le_nhds
    · show w = -1
      linear_combination (mem_singleton_iff.1 h)
  have h3 : Tendsto (fun w : ℂ => ‖(1 + w)⁻¹‖) (𝓝[≠] (-1 : ℂ)) atTop :=
    tendsto_norm_atTop_iff_cobounded.2 (tendsto_inv₀_nhdsNE_zero.comp h2)
  refine (h1.pos_mul_atTop (by norm_num) h3).congr fun w => ?_
  simp only [cfPt, QuantumZipper.CA.cayleyInv, sub_neg_eq_add, norm_mul, Complex.norm_I, one_mul,
    norm_inv, div_eq_mul_inv]
  rw [show 1 + -w = 1 - w by ring]

/-- **A Jordan coordinate gives a two-point uniformizer** (bounded case; the converse of
`PocketJordan.isJordanCoord_cfCoord`): if `ψ` is a Jordan coordinate of `m(C)` with `cfPt p ↦ ∞` and `cfPt q ↦ 0`,
and `−1` is not adherent to the Cayley image `D` of `C`, then `jordanUnif p ψ` is a two-point uniformizer of `D`
with `p ↦ 0` and `q ↦ ∞`. -/
theorem isBdryUniformizer_jordanUnif {C : Set ℂ} (hCo : IsOpen C) (hCH : C ⊆ H) {p q : ℂ}
    (h1 : (-1 : ℂ) ∉ closure (cayley '' C)) (hp : p ∈ frontier (cayley '' C)) (hq : q ∈ closure (cayley '' C))
    (hpq : p ≠ q) {ψ : ℂ → ℂ} (hψ : Sec6.IsJordanCoord (negInv '' C) (cfPt p) (cfPt q) ψ) :
    IsBdryUniformizer (cayley '' C) p q (jordanUnif p ψ) := by
  obtain ⟨hcont, hinj, hmaps, hconf, -, hzero, htend⟩ := hψ
  set D := cayley '' C with hD
  set C' := negInv '' C with hC'
  have hDo : IsOpen D := Lemma71F.isOpen_cayley_image hCo hCH
  have hpD : p ∉ D := by
    rw [hDo.frontier_eq] at hp
    exact hp.2
  have hpc : p ∈ closure D := frontier_subset_closure hp
  have hne1 : ∀ w ∈ closure D, w ≠ -1 := fun w hw h => h1 (h ▸ hw)
  have hcfp : ∀ w ∈ closure D, w ≠ p → cfPt w ≠ cfPt p := fun w hw hwp h =>
    hwp (injOn_cfPt (hne1 w hw) (hne1 p hpc) h)
  have hmapsP : MapsTo cfPt (closure D \ {p}) (closure C' \ {cfPt p}) := fun w hw =>
    ⟨cfPt_mem_closure_image hCH hw.1 (hne1 w hw.1), hcfp w hw.1 hw.2⟩
  have hnz : ∀ w ∈ closure D, w ≠ p → w ≠ q → ψ (cfPt w) ≠ 0 := fun w hw hwp hwq h0 => by
    have := hinj (hmapsP ⟨hw, hwp⟩) (hmapsP ⟨hq, hpq.symm⟩) (h0.trans hzero.symm)
    exact hwq (injOn_cfPt (hne1 w hw) (hne1 q hq) this)
  have hψc : ∀ w ∈ closure D, w ≠ p → ContinuousWithinAt (fun x => ψ (cfPt x)) (closure D \ {p}) w :=
    fun w hw hwp => (hcont (cfPt w) (hmapsP ⟨hw, hwp⟩)).comp (continuousAt_cfPt (hne1 w hw)).continuousWithinAt
      hmapsP
  have hmem : ∀ w ∈ closure D, w ≠ p → closure D \ {p} ∈ 𝓝[closure D \ {q}] w := fun w _ hwp => by
    rw [sdiff_eq]
    exact inter_mem (mem_of_superset self_mem_nhdsWithin sdiff_subset)
      (mem_nhdsWithin_of_mem_nhds (isOpen_compl_singleton.mem_nhds hwp))
  refine ⟨?_, ?_, ?_, ?_, jordanUnif_self p ψ, ?_⟩
  · -- conformal bijection
    have hcomp := isConformalBijection_comp isConformalBijection_negInv_H
      (isConformalBijection_comp hconf (isConformalBijection_cfPt hCH))
    have heq : EqOn (jordanUnif p ψ) (negInv ∘ ψ ∘ cfPt) D := fun w hw => by
      have hwp : w ≠ p := fun h => hpD (h ▸ hw)
      simp only [jordanUnif_of_ne hwp, Function.comp_apply]
    exact ⟨hcomp.1.congr fun z hz => heq hz, hcomp.2.congr heq.symm⟩
  · -- continuity
    intro w hw
    by_cases hwp : w = p
    · rw [hwp] at hw ⊢
      rw [← continuousWithinAt_sdiff_self, ContinuousWithinAt, jordanUnif_self, tendsto_zero_iff_norm_tendsto_zero]
      have hct : Tendsto cfPt (𝓝[(closure D \ {q}) \ {p}] p) (𝓝[closure C' \ {cfPt p}] (cfPt p)) :=
        tendsto_nhdsWithin_iff.2 ⟨(continuousAt_cfPt (hne1 p hpc)).tendsto.mono_left nhdsWithin_le_nhds,
          eventually_nhdsWithin_of_forall fun x hx => hmapsP ⟨hx.1.1, hx.2⟩⟩
      have hψt : Tendsto (fun x => ‖ψ (cfPt x)‖) (𝓝[(closure D \ {q}) \ {p}] p) atTop :=
        tendsto_norm_atTop_iff_cobounded.2 (htend.comp hct)
      refine (tendsto_inv_atTop_zero.comp hψt).congr' (eventually_nhdsWithin_of_forall fun x hx => ?_)
      show ‖ψ (cfPt x)‖⁻¹ = ‖jordanUnif p ψ x‖
      rw [norm_jordanUnif_of_ne hx.2, norm_inv]
    · have heq : jordanUnif p ψ =ᶠ[𝓝 w] fun x => negInv (ψ (cfPt x)) := by
        filter_upwards [isOpen_compl_singleton.mem_nhds hwp] with x hx
        exact jordanUnif_of_ne hx
      refine ContinuousWithinAt.congr_of_eventuallyEq ?_ (eventually_nhdsWithin_of_eventually_nhds heq)
        (jordanUnif_of_ne hwp)
      exact ContinuousAt.comp_continuousWithinAt (f := fun x => ψ (cfPt x)) (x := w)
        (continuousAt_negInv (hnz w hw.1 hwp hw.2)) ((hψc w hw.1 hwp).mono_of_mem_nhdsWithin (hmem w hw.1 hwp))
  · -- injectivity
    intro w hw w' hw' h
    by_cases hwp : w = p
    · by_cases hw'p : w' = p
      · rw [hwp, hw'p]
      · rw [hwp, jordanUnif_self, jordanUnif_of_ne hw'p] at h
        exact absurd (negInv_eq_zero_iff.1 h.symm) (hnz w' hw'.1 hw'p hw'.2)
    · by_cases hw'p : w' = p
      · rw [hw'p, jordanUnif_self, jordanUnif_of_ne hwp] at h
        exact absurd (negInv_eq_zero_iff.1 h) (hnz w hw.1 hwp hw.2)
      · rw [jordanUnif_of_ne hwp, jordanUnif_of_ne hw'p] at h
        have h' := WangWu.negInv_involutive.injective h
        exact injOn_cfPt (hne1 w hw.1) (hne1 w' hw'.1) (hinj (hmapsP ⟨hw.1, hwp⟩) (hmapsP ⟨hw'.1, hw'p⟩) h')
  · -- values in the closed half-plane
    intro w hw
    by_cases hwp : w = p
    · rw [hwp, jordanUnif_self]
      show (0 : ℝ) ≤ (0 : ℂ).im
      simp
    · rw [jordanUnif_of_ne hwp]
      exact negInv_mem_Hbar (hmaps (hmapsP ⟨hw.1, hwp⟩))
  · -- `q ↦ ∞`
    have hqp : q ≠ p := hpq.symm
    have hc' : Tendsto (fun x => ψ (cfPt x)) (𝓝[closure D \ {q}] q) (𝓝 0) := by
      have := ((hψc q hq hqp).mono_of_mem_nhdsWithin (hmem q hq hqp)).tendsto
      rwa [hzero] at this
    have hψq : Tendsto (fun x => ψ (cfPt x)) (𝓝[closure D \ {q}] q) (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨hc', ?_⟩
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (isOpen_compl_singleton.mem_nhds hqp)] with x hx hxp
      exact hnz x hx.1 hxp hx.2
    have hn : Tendsto (fun x => ‖(ψ (cfPt x))⁻¹‖) (𝓝[closure D \ {q}] q) atTop :=
      tendsto_norm_atTop_iff_cobounded.2 (tendsto_inv₀_nhdsNE_zero.comp hψq)
    refine hn.congr' ?_
    filter_upwards [nhdsWithin_le_nhds (isOpen_compl_singleton.mem_nhds hqp)] with x hxp
    exact (norm_jordanUnif_of_ne hxp).symm

/-- **A Jordan coordinate at infinity gives a two-point uniformizer** (pocket opening at the flow seed; the converse
of `PocketJordan.isJordanCoordInf_cfCoord`): `jordanUnif (−1) ψ` sends `−1 ↦ 0` and `q ↦ ∞`. -/
theorem isBdryUniformizer_jordanUnif_inf {C : Set ℂ} (hCo : IsOpen C) (hCH : C ⊆ H) {q : ℂ}
    (hp : (-1 : ℂ) ∈ frontier (cayley '' C)) (hq : q ∈ closure (cayley '' C)) (hq1 : q ≠ -1) {ψ : ℂ → ℂ}
    (hψ : Sec6.IsJordanCoordInf (negInv '' C) (cfPt q) ψ) :
    IsBdryUniformizer (cayley '' C) (-1) q (jordanUnif (-1) ψ) := by
  obtain ⟨hcont, hinj, hmaps, hconf, -, hzero, htend⟩ := hψ
  set D := cayley '' C with hD
  set C' := negInv '' C with hC'
  have hDo : IsOpen D := Lemma71F.isOpen_cayley_image hCo hCH
  have hpD : (-1 : ℂ) ∉ D := by
    rw [hDo.frontier_eq] at hp
    exact hp.2
  have hmapsP : MapsTo cfPt (closure D \ {-1}) (closure C') := fun w hw =>
    cfPt_mem_closure_image hCH hw.1 hw.2
  have hnz : ∀ w ∈ closure D, w ≠ -1 → w ≠ q → ψ (cfPt w) ≠ 0 := fun w hw hwp hwq h0 => by
    have := hinj (hmapsP ⟨hw, hwp⟩) (hmapsP ⟨hq, hq1⟩) (h0.trans hzero.symm)
    exact hwq (injOn_cfPt hwp hq1 this)
  have hψc : ∀ w ∈ closure D, w ≠ -1 → ContinuousWithinAt (fun x => ψ (cfPt x)) (closure D \ {-1}) w :=
    fun w hw hwp => (hcont (cfPt w) (hmapsP ⟨hw, hwp⟩)).comp (continuousAt_cfPt hwp).continuousWithinAt hmapsP
  have hmem : ∀ w ∈ closure D, w ≠ -1 → closure D \ {-1} ∈ 𝓝[closure D \ {q}] w := fun w _ hwp => by
    rw [sdiff_eq]
    exact inter_mem (mem_of_superset self_mem_nhdsWithin sdiff_subset)
      (mem_nhdsWithin_of_mem_nhds (isOpen_compl_singleton.mem_nhds hwp))
  refine ⟨?_, ?_, ?_, ?_, jordanUnif_self (-1) ψ, ?_⟩
  · have hcomp := isConformalBijection_comp isConformalBijection_negInv_H
      (isConformalBijection_comp hconf (isConformalBijection_cfPt hCH))
    have heq : EqOn (jordanUnif (-1) ψ) (negInv ∘ ψ ∘ cfPt) D := fun w hw => by
      have hwp : w ≠ -1 := fun h => hpD (h ▸ hw)
      simp only [jordanUnif_of_ne hwp, Function.comp_apply]
    exact ⟨hcomp.1.congr fun z hz => heq hz, hcomp.2.congr heq.symm⟩
  · intro w hw
    by_cases hwp : w = -1
    · rw [hwp] at hw ⊢
      rw [← continuousWithinAt_sdiff_self, ContinuousWithinAt, jordanUnif_self, tendsto_zero_iff_norm_tendsto_zero]
      have hct : Tendsto cfPt (𝓝[(closure D \ {q}) \ {-1}] (-1)) (cobounded ℂ ⊓ 𝓟 (closure C')) := by
        refine tendsto_inf.2 ⟨tendsto_norm_atTop_iff_cobounded.1
          (tendsto_norm_cfPt_neg_one.mono_left (nhdsWithin_mono _ fun x hx => hx.2)), ?_⟩
        exact tendsto_principal.2 (eventually_nhdsWithin_of_forall fun x hx => hmapsP ⟨hx.1.1, hx.2⟩)
      have hψt : Tendsto (fun x => ‖ψ (cfPt x)‖) (𝓝[(closure D \ {q}) \ {-1}] (-1)) atTop :=
        tendsto_norm_atTop_iff_cobounded.2 (htend.comp hct)
      refine (tendsto_inv_atTop_zero.comp hψt).congr' (eventually_nhdsWithin_of_forall fun x hx => ?_)
      show ‖ψ (cfPt x)‖⁻¹ = ‖jordanUnif (-1) ψ x‖
      rw [norm_jordanUnif_of_ne hx.2, norm_inv]
    · have heq : jordanUnif (-1) ψ =ᶠ[𝓝 w] fun x => negInv (ψ (cfPt x)) := by
        filter_upwards [isOpen_compl_singleton.mem_nhds hwp] with x hx
        exact jordanUnif_of_ne hx
      refine ContinuousWithinAt.congr_of_eventuallyEq ?_ (eventually_nhdsWithin_of_eventually_nhds heq)
        (jordanUnif_of_ne hwp)
      exact ContinuousAt.comp_continuousWithinAt (f := fun x => ψ (cfPt x)) (x := w)
        (continuousAt_negInv (hnz w hw.1 hwp hw.2)) ((hψc w hw.1 hwp).mono_of_mem_nhdsWithin (hmem w hw.1 hwp))
  · intro w hw w' hw' h
    by_cases hwp : w = -1
    · by_cases hw'p : w' = -1
      · rw [hwp, hw'p]
      · rw [hwp, jordanUnif_self, jordanUnif_of_ne hw'p] at h
        exact absurd (negInv_eq_zero_iff.1 h.symm) (hnz w' hw'.1 hw'p hw'.2)
    · by_cases hw'p : w' = -1
      · rw [hw'p, jordanUnif_self, jordanUnif_of_ne hwp] at h
        exact absurd (negInv_eq_zero_iff.1 h) (hnz w hw.1 hwp hw.2)
      · rw [jordanUnif_of_ne hwp, jordanUnif_of_ne hw'p] at h
        have h' := WangWu.negInv_involutive.injective h
        exact injOn_cfPt hwp hw'p (hinj (hmapsP ⟨hw.1, hwp⟩) (hmapsP ⟨hw'.1, hw'p⟩) h')
  · intro w hw
    by_cases hwp : w = -1
    · rw [hwp, jordanUnif_self]
      show (0 : ℝ) ≤ (0 : ℂ).im
      simp
    · rw [jordanUnif_of_ne hwp]
      exact negInv_mem_Hbar (hmaps (hmapsP ⟨hw.1, hwp⟩))
  · have hc' : Tendsto (fun x => ψ (cfPt x)) (𝓝[closure D \ {q}] q) (𝓝 0) := by
      have := ((hψc q hq hq1).mono_of_mem_nhdsWithin (hmem q hq hq1)).tendsto
      rwa [hzero] at this
    have hψq : Tendsto (fun x => ψ (cfPt x)) (𝓝[closure D \ {q}] q) (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨hc', ?_⟩
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (isOpen_compl_singleton.mem_nhds hq1)] with x hx hxp
      exact hnz x hx.1 hxp hx.2
    have hn : Tendsto (fun x => ‖(ψ (cfPt x))⁻¹‖) (𝓝[closure D \ {q}] q) atTop :=
      tendsto_norm_atTop_iff_cobounded.2 (tendsto_inv₀_nhdsNE_zero.comp hψq)
    refine hn.congr' ?_
    filter_upwards [nhdsWithin_le_nhds (isOpen_compl_singleton.mem_nhds hq1)] with x hxp
    exact (norm_jordanUnif_of_ne hxp).symm

/-! ### The arc points of a change pocket -/

section Arcs

variable {R L : ℝ≥0 → ℂ} {r : ℝ≥0}

theorem toDisc_right_mem_frontier (h : IsChangeConfigInc R L r) {s : ℝ}
    (hs : s ∈ Icc (rightLo R L r) (rightHi R L r)) :
    toDisc (realPath R) s ∈ frontier (cayley '' changePocket R L r) := by
  rw [h.cayleyChange_props.2.2]
  exact Or.inl ⟨s, hs, rfl⟩

theorem toDisc_left_mem_frontier (h : IsChangeConfigInc R L r) {t : ℝ}
    (ht : t ∈ Icc (leftLo R L r) (leftHi R L r)) :
    toDisc (realPath L) t ∈ frontier (cayley '' changePocket R L r) := by
  obtain ⟨-, hj1, hj2, -, -, -⟩ := h.changeCorners
  rw [h.cayleyChange_props.2.2, pocketCurve, hj1, hj2]
  exact Or.inr ⟨t, ht, rfl⟩

theorem toDisc_right_ne_openPt (h : IsChangeConfigInc R L r) {s : ℝ}
    (hs : s ∈ Ioo (rightLo R L r) (rightHi R L r)) : toDisc (realPath R) s ≠ openPt R L r := fun he => by
  obtain ⟨hu, hv, -⟩ := h.changeCorner_props
  exact hs.1.ne' (h.isDiscCrosscut_right.inj ⟨hu.1.trans hs.1.le, hs.2.le.trans hv.2⟩ hu he)

theorem toDisc_left_ne_openPt (h : IsChangeConfigInc R L r) {t : ℝ}
    (ht : t ∈ Ioo (leftLo R L r) (leftHi R L r)) : toDisc (realPath L) t ≠ openPt R L r := fun he => by
  obtain ⟨-, -, -, ha, hb, -, hLa, -⟩ := h.changeCorner_props
  rw [← hLa] at he
  exact ht.1.ne' (h.isDiscCrosscut_left.inj ⟨ha.1.trans ht.1.le, ht.2.le.trans hb.2⟩ ha he)

theorem toDisc_right_ne_neg_one (h : IsChangeConfigInc R L r) {s : ℝ}
    (hs : s ∈ Ioo (rightLo R L r) (rightHi R L r)) : toDisc (realPath R) s ≠ -1 := fun he => by
  obtain ⟨hu, hv, -⟩ := h.changeCorner_props
  have := h.isDiscCrosscut_right.inj ⟨hu.1.trans hs.1.le, hs.2.le.trans hv.2⟩ ⟨le_rfl, zero_le_one⟩
    (he.trans h.isDiscCrosscut_right.zero.symm)
  linarith [hu.1, hs.1]

theorem toDisc_left_ne_neg_one (h : IsChangeConfigInc R L r) {t : ℝ}
    (ht : t ∈ Ioo (leftLo R L r) (leftHi R L r)) : toDisc (realPath L) t ≠ -1 := fun he => by
  obtain ⟨-, -, -, ha, hb, -⟩ := h.changeCorner_props
  have := h.isDiscCrosscut_left.inj ⟨ha.1.trans ht.1.le, ht.2.le.trans hb.2⟩ ⟨le_rfl, zero_le_one⟩
    (he.trans h.isDiscCrosscut_left.zero.symm)
  linarith [ha.1, ht.1]

/-- The open-arc points of the right wall in the counterflow chart lie in the closed pocket. -/
theorem cfPt_right_mem_closure (h : IsChangeConfigInc R L r) {s : ℝ}
    (hs : s ∈ Ioo (rightLo R L r) (rightHi R L r)) :
    cfPt (toDisc (realPath R) s) ∈ closure (cfPocket R L r) :=
  cfPt_mem_closure_image h.changePocket_subset_H
    (frontier_subset_closure (toDisc_right_mem_frontier h (Ioo_subset_Icc_self hs))) (toDisc_right_ne_neg_one h hs)

theorem cfPt_left_mem_closure (h : IsChangeConfigInc R L r) {t : ℝ}
    (ht : t ∈ Ioo (leftLo R L r) (leftHi R L r)) :
    cfPt (toDisc (realPath L) t) ∈ closure (cfPocket R L r) :=
  cfPt_mem_closure_image h.changePocket_subset_H
    (frontier_subset_closure (toDisc_left_mem_frontier h (Ioo_subset_Icc_self ht))) (toDisc_left_ne_neg_one h ht)

theorem cfPt_right_ne_cfPt_openPt (h : IsChangeConfigInc R L r) (h0 : (0 : ℂ) ∉ closure (changePocket R L r))
    {s : ℝ} (hs : s ∈ Ioo (rightLo R L r) (rightHi R L r)) :
    cfPt (toDisc (realPath R) s) ≠ cfPt (openPt R L r) := fun he =>
  toDisc_right_ne_openPt h hs (injOn_cfPt (toDisc_right_ne_neg_one h hs) (h.openPt_ne_neg_one h0) he)

theorem cfPt_left_ne_cfPt_openPt (h : IsChangeConfigInc R L r) (h0 : (0 : ℂ) ∉ closure (changePocket R L r))
    {t : ℝ} (ht : t ∈ Ioo (leftLo R L r) (leftHi R L r)) :
    cfPt (toDisc (realPath L) t) ≠ cfPt (openPt R L r) := fun he =>
  toDisc_left_ne_openPt h ht (injOn_cfPt (toDisc_left_ne_neg_one h ht) (h.openPt_ne_neg_one h0) he)

/-! ### The sides of an arbitrary Jordan coordinate -/

theorem re_lt_zero_of_re_negInv_pos {x : ℂ} (hx : 0 < (negInv x).re) : x.re < 0 := by
  rw [re_negInv] at hx
  by_contra hle
  push Not at hle
  exact absurd hx (not_lt.2 (neg_nonpos.2 (div_nonneg hle (normSq_nonneg _))))

theorem re_pos_of_re_negInv_neg {x : ℂ} (hx : (negInv x).re < 0) : 0 < x.re := by
  rw [re_negInv] at hx
  by_contra hle
  push Not at hle
  exact absurd hx (not_lt.2 (neg_nonneg.2 (div_nonpos_of_nonpos_of_nonneg hle (normSq_nonneg _))))

/-- The sides of `ψ` from the orientation of its uniformizer. -/
theorem sides_of_jordanUnif (h : IsChangeConfigInc R L r) (hor : IsFlowChartOriented R L r) {ψ : ℂ → ℂ}
    (hU : IsBdryUniformizer (cayley '' changePocket R L r) (openPt R L r) (closePt R L r)
      (jordanUnif (openPt R L r) ψ)) :
    (∀ s ∈ Ioo (rightLo R L r) (rightHi R L r), (ψ (cfPt (toDisc (realPath R) s))).re < 0) ∧
      ∀ t ∈ Ioo (leftLo R L r) (leftHi R L r), 0 < (ψ (cfPt (toDisc (realPath L) t))).re := by
  have hpos := hor _ hU
  have hneg := h.re_neg_left_of_re_pos hU hpos
  refine ⟨fun s hs => ?_, fun t ht => ?_⟩
  · have hp := hpos s hs
    rw [jordanUnif_of_ne (toDisc_right_ne_openPt h hs)] at hp
    exact re_lt_zero_of_re_negInv_pos hp
  · have hn := hneg t ht
    rw [jordanUnif_of_ne (toDisc_left_ne_openPt h ht)] at hn
    exact re_pos_of_re_negInv_neg hn

/-- **The sides of an arbitrary Jordan coordinate** of a bounded change pocket under the flow-chart orientation:
the open right-wall arc goes to the negative, the open left-wall arc to the positive half-line. -/
theorem jordan_sides (h : IsChangeConfigInc R L r) (h0 : (0 : ℂ) ∉ closure (changePocket R L r))
    (hor : IsFlowChartOriented R L r) {ψ : ℂ → ℂ} (hψ : PocketWordAssembly.IsCfJordan R L r ψ) :
    (∀ s ∈ Ioo (rightLo R L r) (rightHi R L r), (ψ (cfPt (toDisc (realPath R) s))).re < 0) ∧
      ∀ t ∈ Ioo (leftLo R L r) (leftHi R L r), 0 < (ψ (cfPt (toDisc (realPath L) t))).re :=
  sides_of_jordanUnif h hor (isBdryUniformizer_jordanUnif h.isOpen_changePocket h.changePocket_subset_H
    (h.neg_one_notMem_closure_cayley h0) h.openPt_mem_frontier (frontier_subset_closure h.closePt_mem_frontier)
    h.openPt_ne_closePt hψ)

/-- **The sides of an arbitrary Jordan coordinate at infinity** of a change pocket opening at the flow seed. -/
theorem jordanInf_sides (h : IsChangeConfigInc R L r) (h0 : rightLo R L r = 0) (hor : IsFlowChartOriented R L r)
    {ψ : ℂ → ℂ} (hψ : PocketSeedOpen.IsCfJordanInf R L r ψ) :
    (∀ s ∈ Ioo (rightLo R L r) (rightHi R L r), (ψ (cfPt (toDisc (realPath R) s))).re < 0) ∧
      ∀ t ∈ Ioo (leftLo R L r) (leftHi R L r), 0 < (ψ (cfPt (toDisc (realPath L) t))).re := by
  have hop : openPt R L r = -1 := h.openPt_eq_neg_one_iff.2 h0
  have hU := isBdryUniformizer_jordanUnif_inf h.isOpen_changePocket h.changePocket_subset_H
    (hop ▸ h.openPt_mem_frontier) (frontier_subset_closure h.closePt_mem_frontier) h.closePt_ne_neg_one hψ
  rw [← hop] at hU
  exact sides_of_jordanUnif h hor hU

end Arcs

/-! ### Measurability of the marks for an arbitrary point-measurable Jordan coordinate -/

section Marks

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {G : Set Ω} {ψ : Ω → ℂ → ℂ}

theorem measurable_indicator_re {A : Set Ω} {p : Ω → ℂ} (h : Measurable (A.indicator fun ω => ψ ω (p ω))) :
    Measurable (A.indicator fun ω => (ψ ω (p ω)).re) := by
  have h1 := Complex.measurable_re.comp h
  convert h1 using 1
  funext ω
  by_cases hω : ω ∈ A
  · simp only [indicator_of_mem hω, Function.comp_apply]
  · simp only [indicator_of_notMem hω, Function.comp_apply, Complex.zero_re]

/-- **The left wall's change mark is measurable** for an arbitrary point-measurable Jordan coordinate (bounded
pocket). -/
theorem measurable_leftMark (hψm : PocketWordAssembly.IsPointMeasurable R L r G ψ)
    (hLm : ∀ t, Measurable fun ω => L ω t) {A : Set Ω} (hA : MeasurableSet A) (hAG : A ⊆ G)
    (hG : ∀ ω ∈ A, IsChangeConfigInc (R ω) (L ω) r) (h0 : ∀ ω ∈ A, (0 : ℂ) ∉ closure (changePocket (R ω) (L ω) r)) :
    Measurable (A.indicator fun ω => (ψ ω (cfPt (toDisc (realPath (L ω)) (discTime r)))).re) :=
  measurable_indicator_re (hψm A hA hAG _ (measurable_cfPt.comp (measurable_toDisc_apply hLm _)) fun ω hω =>
    ⟨cfPt_left_mem_closure (hG ω hω) (hG ω hω).changeCorners.2.2.2.2.1,
      cfPt_left_ne_cfPt_openPt (hG ω hω) (h0 ω hω) (hG ω hω).changeCorners.2.2.2.2.1⟩)

/-- **A right-wall mark on the open right arc is measurable** for an arbitrary point-measurable Jordan coordinate
(bounded pocket). -/
theorem measurable_rightMark (hψm : PocketWordAssembly.IsPointMeasurable R L r G ψ)
    (hRm : ∀ t, Measurable fun ω => R ω t) {A : Set Ω} (hA : MeasurableSet A) (hAG : A ⊆ G)
    (hG : ∀ ω ∈ A, IsChangeConfigInc (R ω) (L ω) r) (h0 : ∀ ω ∈ A, (0 : ℂ) ∉ closure (changePocket (R ω) (L ω) r))
    {c₁ : ℝ} (hc : ∀ ω ∈ A, c₁ ∈ Ioo (rightLo (R ω) (L ω) r) (rightHi (R ω) (L ω) r)) :
    Measurable (A.indicator fun ω => (ψ ω (cfPt (toDisc (realPath (R ω)) c₁))).re) :=
  measurable_indicator_re (hψm A hA hAG _ (measurable_cfPt.comp (measurable_toDisc_apply hRm _)) fun ω hω =>
    ⟨cfPt_right_mem_closure (hG ω hω) (hc ω hω), cfPt_right_ne_cfPt_openPt (hG ω hω) (h0 ω hω) (hc ω hω)⟩)

/-- The left wall's change mark is measurable (pocket opening at the flow seed). -/
theorem measurable_leftMarkInf (hψm : PocketSeedOpen.IsPointMeasurableInf R L r G ψ)
    (hLm : ∀ t, Measurable fun ω => L ω t) {A : Set Ω} (hA : MeasurableSet A) (hAG : A ⊆ G)
    (hG : ∀ ω ∈ A, IsChangeConfigInc (R ω) (L ω) r) :
    Measurable (A.indicator fun ω => (ψ ω (cfPt (toDisc (realPath (L ω)) (discTime r)))).re) :=
  measurable_indicator_re (hψm A hA hAG _ (measurable_cfPt.comp (measurable_toDisc_apply hLm _)) fun ω hω =>
    cfPt_left_mem_closure (hG ω hω) (hG ω hω).changeCorners.2.2.2.2.1)

/-- A right-wall mark on the open right arc is measurable (pocket opening at the flow seed). -/
theorem measurable_rightMarkInf (hψm : PocketSeedOpen.IsPointMeasurableInf R L r G ψ)
    (hRm : ∀ t, Measurable fun ω => R ω t) {A : Set Ω} (hA : MeasurableSet A) (hAG : A ⊆ G)
    (hG : ∀ ω ∈ A, IsChangeConfigInc (R ω) (L ω) r) {c₁ : ℝ}
    (hc : ∀ ω ∈ A, c₁ ∈ Ioo (rightLo (R ω) (L ω) r) (rightHi (R ω) (L ω) r)) :
    Measurable (A.indicator fun ω => (ψ ω (cfPt (toDisc (realPath (R ω)) c₁))).re) :=
  measurable_indicator_re (hψm A hA hAG _ (measurable_cfPt.comp (measurable_toDisc_apply hRm _)) fun ω hω =>
    cfPt_right_mem_closure (hG ω hω) (hc ω hω))

end Marks

end InteractingSLE.Sec7.SideAnc
