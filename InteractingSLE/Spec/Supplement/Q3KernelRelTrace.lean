/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.Q3KernelTip
import InteractingSLE.Spec.Supplement.Q3KernelNoReturn
import InteractingSLE.Spec.Supplement.GB6RelDetDrv

/-!
# GB6's relative chain has a continuous trace; GB6's relative configuration on one sample

Packet PROVE-Q3-REL2, item (A)1 of `planning/handoffs/PROVE-Q3-REL.md` §4.1. `IsRelConfigOff` needs the relative chain
as a globally continuous driver `Wr` from `0` with a continuous Loewner trace `ηr`. GB6C's glued chain
(`GB6.exists_glued_relChain`) gives the relative driver before the first contact `T_c`, with hulls
`K̃_{a(t)} = Ψ(K'_t)` that are the fillings of `Ψ(γ([0, t]) ∩ ℍ)`. Its trace is the chart image of the counterflow
trace read through the inverse clock: `Γ(v) = Ψ̄(γ(c(v)))`, where `Ψ̄` is the continuous extension of
`Ψ = relMap U σ` to the real points off the closed retained set (`Q3Rel.tendsto_relMap`), and `c` inverts the
relative clock on a compact interval.

* `relExt`, `relGood`, `continuousOn_relExt`, `relExt_eq`, `im_relExt_eq_zero`, `relExt_zero`: the boundary extension;
* `exists_clockInv_Icc`: the inverse of a continuous strictly increasing clock on `[0, T]`;
* **`exists_relChain_trace`**: before every `t₁ < T_c`, a globally continuous relative driver `Wr` from `0` with a
  continuous Loewner trace generates `Ψ(K'_t)` at `a(t)` for every `t ≤ t₁`;
* **`exists_relChain_tip`**: in addition the tip identity of `IsRelConfigOff` holds at every `t < t₁`
  (`tendsto_tip_of_later`).

Deterministic. Conditional helpers with distinct names; they replace no source theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Filter Set Topology Metric Complex
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull)

namespace InteractingSLE.Supp8.Q3Kernel

open GB6 (relMap relInv relClock firstContactTime sphereInv)
open Q3Rel (invHull)

/-! ### The boundary extension of GB6's relative map -/

section Ext

variable {U : ℝ → ℝ} {σ : ℝ}

/-- The continuous extension of `Ψ = relMap U σ` from `ℍ ∖ A` (`A = invHull U σ`). -/
def relExt (U : ℝ → ℝ) (σ : ℝ) : ℂ → ℂ := extendFrom (H \ invHull U σ) (relMap U σ)

/-- The points where `Ψ` extends continuously: `ℍ ∖ A` and the real points off the closed retained set. -/
def relGood (U : ℝ → ℝ) (σ : ℝ) : Set ℂ :=
  (H \ invHull U σ) ∪ {z | z.im = 0 ∧ z ∉ closure (invHull U σ)}

theorem negInv_notMem_fwdHull {w : ℂ} (hw : w ∉ invHull U σ) : -w⁻¹ ∉ fwdHull U σ := fun h =>
  hw ⟨-w⁻¹, h, GB6.neg_inv_neg_inv w⟩

theorem tendsto_relMap_of_mem (hU : Continuous U) (hσ : 0 ≤ σ) {w : ℂ} (hw : w ∈ H \ invHull U σ) :
    Tendsto (relMap U σ) (𝓝[H \ invHull U σ] w) (𝓝 (relMap U σ w)) :=
  (GB6.continuousAt_relMap hU hσ hw.1 (negInv_notMem_fwdHull hw.2)).tendsto.mono_left nhdsWithin_le_nhds

theorem zero_notMem_closure_invHull (hU : Continuous U) (hσ : 0 ≤ σ) : (0 : ℂ) ∉ closure (invHull U σ) := by
  obtain ⟨M, hM⟩ := (isBounded_fwdHull hU σ).subset_closedBall 0
  have hKH : fwdHull U σ ⊆ H := (isHPHull_fwdHull hU hσ).1
  intro h0
  obtain ⟨w, hw, hwd⟩ := Metric.mem_closure_iff.1 h0 (1 / (|M| + 1)) (by positivity)
  obtain ⟨z, hz, rfl⟩ := hw
  have hz0 : z ≠ 0 := GB6.ne_zero_of_mem_H (hKH hz)
  have hzM : ‖z‖ ≤ |M| := (mem_closedBall_zero_iff.1 (hM hz)).trans (le_abs_self M)
  rw [dist_zero_left, norm_neg, norm_inv] at hwd
  have hpos : 0 < ‖z‖ := norm_pos_iff.2 hz0
  rw [inv_lt_comm₀ hpos (by positivity), one_div, inv_inv] at hwd
  linarith

/-- `Ψ → 0` at `0` (the image of the flow's target `∞`): `f_σ` moves points by a bounded amount. -/
theorem tendsto_relMap_zero (hU : Continuous U) (hU0 : U 0 = 0) (hσ : 0 ≤ σ) :
    Tendsto (relMap U σ) (𝓝[H \ invHull U σ] 0) (𝓝 0) := by
  obtain ⟨C, -, hC⟩ := WangWu.exists_norm_fwdMap_sub_le hU hU0 hσ
  have h1 : Tendsto (fun w : ℂ => -w⁻¹) (𝓝[H \ invHull U σ] 0) (Bornology.cobounded ℂ) :=
    Filter.tendsto_neg_cobounded.comp (tendsto_inv₀_nhdsNE_zero.mono_left
      (nhdsWithin_mono _ fun w hw => GB6.ne_zero_of_mem_H hw.1))
  have h2 : Tendsto (fun w => fwdMap U σ (-w⁻¹)) (𝓝[H \ invHull U σ] 0) (Bornology.cobounded ℂ) := by
    rw [← tendsto_norm_atTop_iff_cobounded]
    refine tendsto_atTop_mono' _ ?_ (tendsto_atTop_add_const_right _ (-C)
      (tendsto_norm_atTop_iff_cobounded.2 h1))
    filter_upwards [self_mem_nhdsWithin] with w hw
    have := hC _ (Q3Rel.negInv_mem_compl hw)
    have h3 := norm_sub_norm_le (-w⁻¹) (fwdMap U σ (-w⁻¹))
    rw [norm_sub_rev] at this
    linarith
  have h4 := (tendsto_inv₀_cobounded.comp h2).neg
  rw [neg_zero] at h4
  exact h4

theorem relGood_subset_closure : relGood U σ ⊆ closure (H \ invHull U σ) := by
  rintro z (hz | ⟨hz0, hzA⟩)
  · exact subset_closure hz
  · obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 isClosed_closure.isOpen_compl z hzA
    have ht : Tendsto (fun n : ℕ => z + ((r / 2 / ((n : ℝ) + 1) : ℝ) : ℂ) * I) atTop (𝓝 z) := by
      have h1 : Tendsto (fun n : ℕ => r / 2 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
        have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (r / 2)
        rw [mul_zero] at this
        exact this.congr fun n => by rw [mul_one_div]
      have h2 := ((Complex.continuous_ofReal.tendsto 0).comp h1).mul_const I
      simpa using (tendsto_const_nhds (x := z)).add h2
    refine mem_closure_of_tendsto ht (Eventually.of_forall fun n => ?_)
    set x : ℝ := r / 2 / ((n : ℝ) + 1) with hx
    have hpos : 0 < x := by positivity
    have hle : x ≤ r / 2 := div_le_self (by positivity) (by linarith [n.cast_nonneg (α := ℝ)])
    have him : (z + (x : ℂ) * I).im = x := by
      simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
        Complex.I_im, mul_one, zero_mul, add_zero, hz0, zero_add]
    refine ⟨show (0 : ℝ) < (z + (x : ℂ) * I).im by rw [him]; exact hpos, fun hA => ?_⟩
    have hd : z + (x : ℂ) * I ∈ ball z r := by
      rw [mem_ball, dist_eq, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
        Real.norm_of_nonneg hpos.le]
      linarith
    exact hball hd (subset_closure hA)

theorem exists_tendsto_relMap (hU : Continuous U) (hU0 : U 0 = 0) (hσ : 0 ≤ σ) {z : ℂ} (hz : z ∈ relGood U σ) :
    ∃ y, Tendsto (relMap U σ) (𝓝[H \ invHull U σ] z) (𝓝 y) := by
  rcases hz with hz | ⟨hz0, hzA⟩
  · exact ⟨_, tendsto_relMap_of_mem hU hσ hz⟩
  · have hzr : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [hz0])
    rw [hzr] at hzA ⊢
    obtain ⟨x, hx⟩ := Q3Rel.tendsto_relMap hU hU0 hσ hzA
    exact ⟨_, hx⟩

theorem continuousOn_relExt (hU : Continuous U) (hU0 : U 0 = 0) (hσ : 0 ≤ σ) :
    ContinuousOn (relExt U σ) (relGood U σ) :=
  continuousOn_extendFrom relGood_subset_closure fun _ hz => exists_tendsto_relMap hU hU0 hσ hz

theorem relExt_eq (hU : Continuous U) (hσ : 0 ≤ σ) {w : ℂ} (hw : w ∈ H \ invHull U σ) :
    relExt U σ w = relMap U σ w :=
  extendFrom_eq (subset_closure hw) (tendsto_relMap_of_mem hU hσ hw)

theorem im_relExt_eq_zero (hU : Continuous U) (hU0 : U 0 = 0) (hσ : 0 ≤ σ) {z : ℂ} (hz0 : z.im = 0)
    (hzA : z ∉ closure (invHull U σ)) : (relExt U σ z).im = 0 := by
  have hzr : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [hz0])
  rw [hzr] at hzA ⊢
  obtain ⟨x, hx⟩ := Q3Rel.tendsto_relMap hU hU0 hσ hzA
  rw [relExt, extendFrom_eq (relGood_subset_closure (Or.inr ⟨by simp, hzA⟩)) hx, Complex.ofReal_im]

theorem relExt_zero (hU : Continuous U) (hU0 : U 0 = 0) (hσ : 0 ≤ σ) : relExt U σ 0 = 0 :=
  extendFrom_eq (relGood_subset_closure (Or.inr ⟨Complex.zero_im, zero_notMem_closure_invHull hU hσ⟩))
    (tendsto_relMap_zero hU hU0 hσ)

/-- The extension sends the good points of `ℍ` into `ℍ` and the good real points into `ℝ`; so the part in `ℍ` of the
image of a set of good points is the image of its part in `ℍ`. -/
theorem relExt_image_inter_H (hU : Continuous U) (hU0 : U 0 = 0) (hσ : 0 ≤ σ) {S : Set ℂ}
    (hS : S ⊆ relGood U σ) : relExt U σ '' S ∩ H = relMap U σ '' (S ∩ H) := by
  ext z
  constructor
  · rintro ⟨⟨p, hp, rfl⟩, hzH⟩
    rcases hS hp with hpD | ⟨hp0, hpA⟩
    · exact ⟨p, ⟨hp, hpD.1⟩, (relExt_eq hU hσ hpD).symm⟩
    · exact absurd (im_relExt_eq_zero hU hU0 hσ hp0 hpA) (ne_of_gt hzH)
  · rintro ⟨p, ⟨hp, hpH⟩, rfl⟩
    have hpD : p ∈ H \ invHull U σ := by
      rcases hS hp with hpD | ⟨hp0, -⟩
      · exact hpD
      · exact absurd hp0 (ne_of_gt hpH)
    exact ⟨⟨p, hp, relExt_eq hU hσ hpD⟩, GB6.relMap_mem_H hU hσ hpD.1 (negInv_notMem_fwdHull hpD.2)⟩

end Ext

/-! ### The inverse of a clock on a compact interval -/

/-- **The inverse clock.** A continuous strictly increasing `a` on `[0, T]` with `a 0 = 0` has a continuous inverse
`c` on `[0, a T]`. -/
theorem exists_clockInv_Icc {a : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T) (ha0 : a 0 = 0) (hac : ContinuousOn a (Icc 0 T))
    (hsm : StrictMonoOn a (Icc 0 T)) :
    ∃ c : ℝ → ℝ, ContinuousOn c (Icc 0 (a T)) ∧ (∀ v ∈ Icc 0 (a T), c v ∈ Icc 0 T ∧ a (c v) = v) ∧
      ∀ t ∈ Icc 0 T, c (a t) = t := by
  have hmem : ∀ x : Icc (0 : ℝ) T, a x ∈ Icc 0 (a T) := fun x => by
    have h0 : a 0 ≤ a x := hsm.monotoneOn ⟨le_rfl, hT⟩ x.2 x.2.1
    rw [ha0] at h0
    exact ⟨h0, hsm.monotoneOn x.2 ⟨hT, le_rfl⟩ x.2.2⟩
  set f : Icc (0 : ℝ) T → Icc (0 : ℝ) (a T) := fun x => ⟨a x, hmem x⟩ with hf
  have hfm : StrictMono f := fun x y hxy => show a x < a y from hsm x.2 y.2 hxy
  have hfs : Function.Surjective f := by
    rintro ⟨v, hv⟩
    obtain ⟨t, ht, hat⟩ := intermediate_value_Icc hT hac (by rw [ha0]; exact hv)
    exact ⟨⟨t, ht⟩, Subtype.ext hat⟩
  set e := StrictMono.orderIsoOfSurjective f hfm hfs with he
  classical
  set c : ℝ → ℝ := fun v => if hv : v ∈ Icc (0 : ℝ) (a T) then (e.symm ⟨v, hv⟩ : ℝ) else 0 with hc
  have hce : ∀ v (hv : v ∈ Icc (0 : ℝ) (a T)), c v = (e.symm ⟨v, hv⟩ : ℝ) := fun v hv => by
    simp only [hc, hv, ↓reduceDIte]
  have hspec : ∀ v (hv : v ∈ Icc (0 : ℝ) (a T)), a (e.symm ⟨v, hv⟩ : ℝ) = v := fun v hv => by
    have := e.apply_symm_apply ⟨v, hv⟩
    exact congrArg Subtype.val this
  refine ⟨c, ?_, fun v hv => ?_, fun t ht => ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    have : (Icc (0 : ℝ) (a T)).domRestrict c = fun v => ((e.symm v : Icc (0 : ℝ) T) : ℝ) := by
      funext v
      exact hce v v.2
    rw [this]
    exact continuous_subtype_val.comp e.symm.continuous
  · rw [hce v hv]
    exact ⟨(e.symm ⟨v, hv⟩).2, hspec v hv⟩
  · have hv : a t ∈ Icc (0 : ℝ) (a T) := hmem ⟨t, ht⟩
    rw [hce _ hv]
    have : e.symm ⟨a t, hv⟩ = ⟨t, ht⟩ := by
      rw [OrderIso.symm_apply_eq]
      exact Subtype.ext rfl
    rw [this]

/-! ### GB6's relative chain with a global trace -/

section Chain

variable {wα w : ℝ≥0 → ℝ} {Tα : ℝ≥0∞} {α γ : ℝ≥0 → ℂ} {s : ℝ≥0} {U : ℝ → ℝ} {t₂ : ℝ}

/-- **The relative chain has a continuous trace** (GB6, p. 519, the chart image of the counterflow; deterministic).
Let `α` be a generating trace of the flow driver `wα` with an interior tip `α(s) ∈ ℍ`, `U` a continuous driver from
`0` agreeing with the flow driver on `[0, t₂]`, `s < t₂ < Tα` (the frozen flow driver), and `γ` a complete generating
trace of the continuous counterflow driver `w`. Then before every `t₁ < T_c` there is a globally continuous relative
driver `Wr` from `0` with a continuous Loewner trace, generating `Ψ(K'_t)` at the relative clock `a(t)` for every
`t ≤ t₁` (`Ψ = relMap U s`, `a = relClock U s`). -/
theorem exists_relChain_trace (hα : IsGeneratingTrace wα Tα α) (hwα : ContinuousOn wα {t | (t : ℝ≥0∞) < Tα})
    (hwα0 : wα 0 = 0) (hs : (s : ℝ≥0∞) < Tα) (hsH : α s ∈ H) (hU : Continuous U) (hU0 : U 0 = 0)
    (hst₂ : (s : ℝ) < t₂) (hUeq : ∀ r ∈ Icc (0 : ℝ) t₂, U r = wα r.toNNReal)
    (hγ : IsGeneratingTrace w ⊤ γ) (hw : Continuous w) (hw0 : w 0 = 0) {t₁ : ℝ≥0}
    (ht₁ : (t₁ : ℝ≥0∞) < firstContactTime (fun t => sphereInv (γ t : OnePoint ℂ))
      ((fun t => (α t : OnePoint ℂ)) '' Icc 0 s)) :
    ∃ (Wr : ℝ → ℝ) (ηr : ℝ → ℂ), Continuous Wr ∧ Wr 0 = 0 ∧ IsLoewnerTrace Wr ηr ∧
      (∀ t : ℝ≥0, t ≤ t₁ →
        relMap U s '' fwdHull (fun r : ℝ => w r.toNNReal) t =
          fwdHull Wr (relClock U s (fun r : ℝ => w r.toNNReal) t)) ∧
      relClock U s (fun r : ℝ => w r.toNNReal) 0 = 0 ∧
      StrictMonoOn (fun t : ℝ≥0 => relClock U s (fun r : ℝ => w r.toNNReal) t)
        {t | (t : ℝ≥0∞) < firstContactTime (fun t => sphereInv (γ t : OnePoint ℂ))
          ((fun t => (α t : OnePoint ℂ)) '' Icc 0 s)} ∧
      ContinuousOn (fun t : ℝ≥0 => relClock U s (fun r : ℝ => w r.toNNReal) t)
        {t | (t : ℝ≥0∞) < firstContactTime (fun t => sphereInv (γ t : OnePoint ℂ))
          ((fun t => (α t : OnePoint ℂ)) '' Icc 0 s)} ∧
      ∀ T : ℝ≥0, (T : ℝ≥0∞) < firstContactTime (fun t => sphereInv (γ t : OnePoint ℂ))
          ((fun t => (α t : OnePoint ℂ)) '' Icc 0 s) →
        Disjoint (closure (fwdHull U s)) (closure ((fun w : ℂ => -w⁻¹) '' fwdHull (fun r : ℝ => w r.toNNReal) T)) :=
    by
  set Tc := firstContactTime (fun t => sphereInv (γ t : OnePoint ℂ)) ((fun t => (α t : OnePoint ℂ)) '' Icc 0 s)
    with hTcdef
  set Wc : ℝ → ℝ := fun r => w r.toNNReal with hWcdef
  have hWcc : Continuous Wc := hw.comp continuous_real_toNNReal
  have hs0 : (0 : ℝ) < s := by
    rcases eq_or_lt_of_le (NNReal.coe_nonneg s) with h0 | h0
    · exfalso
      have hs' : s = 0 := by exact_mod_cast h0.symm
      exact GB6.ne_zero_of_mem_H hsH (by rw [hs']; exact hα.1)
    · exact h0
  have hagree : ∀ r ∈ Icc (0 : ℝ) t₂, (fun r : ℝ => wα r.toNNReal) r = U r := fun r hr => (hUeq r hr).symm
  have hhull : fwdHull (fun r : ℝ => wα r.toNNReal) s = fwdHull U s :=
    fwdHull_eq_of_eqOn (NNReal.coe_nonneg s) hst₂ hagree
  have htip : Tendsto (fwdMapInv U s) (𝓝[H] 0) (𝓝 (α s)) := by
    have h1 := IsGeneratingTrace.tendsto_fwdMapInv_tip hα hwα hwα0 hs
    rwa [fwdMapInv_eq_of_eqOn (NNReal.coe_nonneg s) hst₂ hagree] at h1
  have hd : ∀ T : ℝ≥0, (T : ℝ≥0∞) < Tc → Disjoint (closure (fwdHull U s))
      (closure ((fun w : ℂ => -w⁻¹) '' fwdHull Wc T)) := fun T hT => by
    rw [← hhull]
    exact GB6.disjoint_closure_fwdHull_of_lt_firstContactTime hα hwα hwα0 hγ hw.continuousOn hw0 hs
      ENNReal.coe_lt_top hT
  have hγc : Continuous γ := by
    have := hγ.2.1
    simp only [le_top, ofPred_true] at this
    exact continuousOn_univ.1 this
  have hTc : 0 < Tc := by
    have hk : IsCompact (α '' Icc 0 s) := isCompact_Icc.image_of_continuousOn
      (hα.2.1.mono fun t ht => le_trans (by exact_mod_cast ht.2) hs.le)
    have := GB6.firstContactTime_pos hγc.continuousAt hγ.1 hk.isBounded
    rwa [image_image] at this
  have hγK : ∀ t : ℝ≥0, (t : ℝ≥0∞) < Tc → IsFilling (fwdHull Wc t) (γ '' Icc 0 t) :=
    fun t _ => hγ.2.2 t ENNReal.coe_lt_top
  obtain ⟨W', hW'0, ha0, hsm, hac, hW'c, hK⟩ := GB6.exists_glued_relChain hw hw0 hU hU0 hs0 htip hTc hd hγK
  set a : ℝ → ℝ := relClock U s Wc with hadef
  obtain ⟨t₃, ht₁₃, ht₃⟩ : ∃ t₃ : ℝ≥0, t₁ < t₃ ∧ (t₃ : ℝ≥0∞) < Tc := by
    obtain ⟨r, h1, h2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht₁
    exact ⟨r, ENNReal.coe_lt_coe.1 h1, h2⟩
  obtain ⟨t₄, ht₃₄, ht₄⟩ : ∃ t₄ : ℝ≥0, t₃ < t₄ ∧ (t₄ : ℝ≥0∞) < Tc := by
    obtain ⟨r, h1, h2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht₃
    exact ⟨r, ENNReal.coe_lt_coe.1 h1, h2⟩
  -- the clock on `[0, t₃]` as a function of a real variable
  have hltTc : ∀ r : ℝ, r ≤ t₃ → ((r.toNNReal : ℝ≥0) : ℝ≥0∞) < Tc := fun r hr =>
    lt_of_le_of_lt (ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hr)) ht₃
  have haR : ∀ r : ℝ, 0 ≤ r → a r = a (r.toNNReal : ℝ) := fun r hr => by rw [Real.coe_toNNReal _ hr]
  have hsmI : StrictMonoOn a (Icc 0 (t₃ : ℝ)) := fun x hx y hy hxy => by
    rw [haR x hx.1, haR y hy.1]
    exact hsm (hltTc x hx.2) (hltTc y hy.2) ((Real.toNNReal_lt_toNNReal_iff' ).2 ⟨hxy, lt_of_le_of_lt hx.1 hxy⟩)
  have hacI : ContinuousOn a (Icc 0 (t₃ : ℝ)) := by
    have h1 : ContinuousOn (fun r : ℝ => a (r.toNNReal : ℝ)) (Icc 0 (t₃ : ℝ)) :=
      hac.comp continuous_real_toNNReal.continuousOn fun r hr => hltTc r hr.2
    exact h1.congr fun r hr => haR r hr.1
  obtain ⟨c, hcc, hcmem, hca⟩ := exists_clockInv_Icc (T := (t₃ : ℝ)) t₃.2 ha0 hacI hsmI
  have hmonoI : MonotoneOn a (Icc 0 (t₃ : ℝ)) := hsmI.monotoneOn
  set b : ℝ := a t₁ with hbdef
  set b₃ : ℝ := a t₃ with hb₃def
  have hbb₃ : b < b₃ := hsm (lt_of_le_of_lt (ENNReal.coe_le_coe.2 ht₁₃.le) ht₃) ht₃ ht₁₃
  have hb₃₄ : b₃ < a t₄ := hsm ht₃ ht₄ ht₃₄
  have hb0 : 0 ≤ b := by
    have := hmonoI ⟨le_rfl, t₃.2⟩ ⟨t₁.2, by exact_mod_cast ht₁₃.le⟩ t₁.2
    rwa [ha0] at this
  have hb₃0 : 0 ≤ b₃ := hb0.trans hbb₃.le
  -- the relative driver frozen after `b₃`
  set W₃ : ℝ → ℝ := frozenDrive W' b₃ with hW₃def
  have hW₃c : Continuous W₃ := continuous_frozenDrive (hW'c.mono fun u hu => by
    refine ⟨t₄, ht₄, lt_of_le_of_lt ?_ hb₃₄⟩
    have : (u : ℝ) ≤ (b₃.toNNReal : ℝ) := by exact_mod_cast hu
    rwa [Real.coe_toNNReal _ hb₃0] at this)
  have hW₃0 : W₃ 0 = 0 := by rw [hW₃def, frozenDrive_zero hb₃0, hW'0]
  have hW₃eq : ∀ r ∈ Icc (0 : ℝ) b₃, W₃ r = (fun r : ℝ => W' r.toNNReal) r := fun r hr => frozenDrive_eq hr
  have hW₃hull : ∀ v, 0 ≤ v → v < b₃ → fwdHull W₃ v = fwdHull (fun r : ℝ => W' r.toNNReal) v :=
    fun v hv hvb => fwdHull_eq_of_eqOn hv hvb hW₃eq
  -- the counterflow trace stays among the good points of `Ψ` up to `t₃`
  have hγL := isLoewnerTrace_of_isGeneratingTrace hγ
  have hdA : Disjoint (closure (fwdHull Wc t₃)) (closure (invHull U s)) :=
    Q3Rel.disjoint_closure_invHull hU hs0.le (hd t₃ ht₃)
  have hgood : ∀ r : ℝ≥0, r ≤ t₃ → γ r ∈ relGood U s := by
    intro r hr
    rcases eq_or_lt_of_le (bot_le : (0 : ℝ≥0) ≤ r) with h0 | h0
    · rw [← h0]
      show γ 0 ∈ relGood U s
      rw [hγ.1]
      exact Or.inr ⟨Complex.zero_im, zero_notMem_closure_invHull hU hs0.le⟩
    · have h1 : γ r ∈ closure (fwdHull Wc r) := by
        have := trace_mem_closure_fwdHull hγL hWcc (by simp [hw0]) (u := (r : ℝ)) (by exact_mod_cast h0)
        simpa using this
      have h2 : γ r ∈ closure (fwdHull Wc t₃) := closure_mono (fwdHull_mono' (by exact_mod_cast hr)) h1
      have hnA : γ r ∉ closure (invHull U s) := fun h => Set.disjoint_left.1 hdA h2 h
      have hHb : γ r ∈ Hbar := by
        have hsub : closure (fwdHull Wc t₃) ⊆ Hbar := by
          rw [← closure_H]; exact closure_mono (isHPHull_fwdHull hWcc t₃.2).1
        exact hsub h2
      rcases eq_or_lt_of_le (show (0 : ℝ) ≤ (γ r).im from hHb) with him | him
      · exact Or.inr ⟨him.symm, hnA⟩
      · exact Or.inl ⟨him, fun h => hnA (subset_closure h)⟩
  -- the relative trace before `b₃`: the chart image of the counterflow trace through the inverse clock
  set Γ : ℝ → ℂ := fun v => relExt U s (γ (c v).toNNReal) with hΓdef
  have hcle : ∀ v ∈ Icc (0 : ℝ) b₃, (c v).toNNReal ≤ t₃ := fun v hv =>
    Real.toNNReal_le_iff_le_coe.2 (hcmem v hv).1.2
  have hc0 : c 0 = 0 := by
    have := hca 0 ⟨le_rfl, t₃.2⟩
    rwa [ha0] at this
  have hΓ0 : Γ 0 = 0 := by
    simp only [hΓdef, hc0, Real.toNNReal_zero]
    rw [hγ.1]
    exact relExt_zero hU hU0 hs0.le
  have hΓc : ContinuousOn Γ (Icc 0 b₃) := by
    have h1 : ContinuousOn (fun v => γ (c v).toNNReal) (Icc 0 b₃) :=
      (hγc.comp continuous_real_toNNReal).comp_continuousOn hcc
    exact (continuousOn_relExt hU hU0 hs0.le).comp h1 fun v hv => hgood _ (hcle v hv)
  have himg : ∀ v ∈ Icc (0 : ℝ) b₃, Γ '' Icc 0 v = relExt U s '' (γ '' Icc 0 (c v).toNNReal) := by
    intro v hv
    have hcv := hcmem v hv
    have hci : c '' Icc 0 v = Icc 0 (c v) := by
      ext r
      constructor
      · rintro ⟨v', hv', rfl⟩
        have hv'b : v' ∈ Icc (0 : ℝ) b₃ := ⟨hv'.1, hv'.2.trans hv.2⟩
        have hcv' := hcmem v' hv'b
        refine ⟨hcv'.1.1, ?_⟩
        by_contra hlt
        push Not at hlt
        have := hsmI hcv.1 hcv'.1 hlt
        rw [hcv.2, hcv'.2] at this
        linarith [hv'.2]
      · intro hr
        have hrI : r ∈ Icc (0 : ℝ) t₃ := ⟨hr.1, hr.2.trans hcv.1.2⟩
        refine ⟨a r, ⟨?_, ?_⟩, hca r hrI⟩
        · have := hmonoI ⟨le_rfl, t₃.2⟩ hrI hr.1
          rwa [ha0] at this
        · have := hmonoI hrI hcv.1 hr.2
          rwa [hcv.2] at this
    rw [show Γ = relExt U s ∘ (fun x : ℝ => γ x.toNNReal) ∘ c from rfl, image_comp, image_comp, hci,
      image_toNNReal_Icc γ hcv.1.1]
  have hLT : IsLoewnerTraceLT W₃ b₃ Γ := by
    refine ⟨hΓ0, hΓc.mono Ico_subset_Icc_self, fun v hv hvb => ?_⟩
    have hvI : v ∈ Icc (0 : ℝ) b₃ := ⟨hv, hvb.le⟩
    obtain ⟨hcvI, hacv⟩ := hcmem v hvI
    set tN : ℝ≥0 := (c v).toNNReal with htN
    have htNc : (tN : ℝ) = c v := Real.coe_toNNReal _ hcvI.1
    have htN3 : tN ≤ t₃ := hcle v hvI
    have htNTc : (tN : ℝ≥0∞) < Tc := lt_of_le_of_lt (ENNReal.coe_le_coe.2 htN3) ht₃
    have hav : a (tN : ℝ) = v := by rw [htNc]; exact hacv
    obtain ⟨hKt, hFt⟩ := hK tN htNTc
    rw [hW₃hull v hv hvb, himg v hvI]
    rw [hav] at hKt hFt
    have hsubg : γ '' Icc 0 tN ⊆ relGood U s := by
      rintro _ ⟨r, hr, rfl⟩
      exact hgood r (hr.2.trans htN3)
    have hKcc : IsCompact (relExt U s '' (γ '' Icc 0 tN)) := (isCompact_Icc.image hγc).image_of_continuousOn
      ((continuousOn_relExt hU hU0 hs0.le).mono hsubg)
    have hKcH := relExt_image_inter_H hU hU0 hs0.le hsubg
    have hHK : H \ relExt U s '' (γ '' Icc 0 tN) = H \ relMap U s '' (γ '' Icc 0 tN ∩ H) := by
      rw [← hKcH, sdiff_inter_self_eq_sdiff]
    have hFill : IsFilling (fwdHull (fun r : ℝ => W' r.toNNReal) v) (relExt U s '' (γ '' Icc 0 tN)) := by
      unfold IsFilling at hFt ⊢
      rw [hHK]
      exact hFt
    have hKH : fwdHull (fun r : ℝ => W' r.toNNReal) v ⊆ H := by
      rw [← hW₃hull v hv hvb]
      exact (isHPHull_fwdHull hW₃c hv).1
    exact (fillH_eq_iff_isFilling_of_isClosed hKcc.isBounded hKcc.isClosed hKH).1 hFill
  have hext := hLT.isLoewnerTrace_ext hW₃c hW₃0 hb0 hbb₃
  refine ⟨YuanCorollary13.extDrive W₃ b, YuanCorollary13.extTrace W₃ Γ b, YuanCorollary13.continuous_extDrive hW₃c,
    YuanCorollary13.extDrive_zero hW₃0 hb0, hext, fun t ht => ?_, ha0, hsm, hac, hd⟩
  have htTc : (t : ℝ≥0∞) < Tc := lt_of_le_of_lt (ENNReal.coe_le_coe.2 ht) ht₁
  have htI : (t : ℝ) ∈ Icc (0 : ℝ) t₃ := ⟨t.2, by exact_mod_cast ht.trans ht₁₃.le⟩
  have hav0 : 0 ≤ a t := by
    have := hmonoI ⟨le_rfl, t₃.2⟩ htI t.2
    rwa [ha0] at this
  have hatb : a t ≤ b := hmonoI htI ⟨t₁.2, by exact_mod_cast ht₁₃.le⟩ (by exact_mod_cast ht)
  show relMap U s '' fwdHull Wc t = fwdHull (YuanCorollary13.extDrive W₃ b) (a t)
  rw [YuanCorollary13.fwdHull_eq_of_eqOn_Icc (YuanCorollary13.continuous_extDrive hW₃c) hW₃c hav0
    (fun r hr => YuanCorollary13.extDrive_eq (hr.2.trans hatb)), hW₃hull _ hav0 (hatb.trans_lt hbb₃)]
  exact (hK t htTc).1.symm

/-- **GB6's relative chain at a counterflow time `t`, with the tip identity** (deterministic; the chain fields of
`Q3Rel.isRelConfigOff_gb6`). In the setting of `exists_relChain_trace`, let `(relMap U s, relInv U s, relLog U s)` be a
retained chart of `invHull U s` landing off `relBad U s` (`ae_exists_frozen_retainedChartOff`), and `0 < t < t₁ < T_c`.
Then a globally continuous relative driver `Wr` from `0` with a continuous Loewner trace generates `Ψ(K'_t)` at
`u = a(t) > 0`, the flow-frame closures are disjoint at `t`, and the transition `g'_t ∘ Ψi ∘ f̃_u` tends to `0` at
`0`. -/
theorem exists_relChain_tip (hα : IsGeneratingTrace wα Tα α) (hwα : ContinuousOn wα {t | (t : ℝ≥0∞) < Tα})
    (hwα0 : wα 0 = 0) (hs : (s : ℝ≥0∞) < Tα) (hsH : α s ∈ H) (hU : Continuous U) (hU0 : U 0 = 0)
    (hst₂ : (s : ℝ) < t₂) (hUeq : ∀ r ∈ Icc (0 : ℝ) t₂, U r = wα r.toNNReal)
    (hΨ : Q3Rel.IsRetainedChartOff (invHull U s) (relMap U s) (relInv U s) (Q3Rel.relLog U s) (Q3Rel.relBad U s))
    (hγ : IsGeneratingTrace w ⊤ γ) (hw : Continuous w) (hw0 : w 0 = 0) {t t₁ : ℝ≥0} (ht0 : 0 < t)
    (htt₁ : t < t₁)
    (ht₁ : (t₁ : ℝ≥0∞) < firstContactTime (fun t => sphereInv (γ t : OnePoint ℂ))
      ((fun t => (α t : OnePoint ℂ)) '' Icc 0 s)) :
    ∃ (Wr : ℝ → ℝ) (ηr : ℝ → ℂ), Continuous Wr ∧ Wr 0 = 0 ∧ IsLoewnerTrace Wr ηr ∧
      0 < relClock U s (fun r : ℝ => w r.toNNReal) t ∧
      relMap U s '' fwdHull (fun r : ℝ => w r.toNNReal) t =
        fwdHull Wr (relClock U s (fun r : ℝ => w r.toNNReal) t) ∧
      Disjoint (closure (fwdHull U s)) (closure ((fun w : ℂ => -w⁻¹) '' fwdHull (fun r : ℝ => w r.toNNReal) t)) ∧
      Tendsto (fun y => fwdMap (fun r : ℝ => w r.toNNReal) t
        (relInv U s (fwdMapInv Wr (relClock U s (fun r : ℝ => w r.toNNReal) t) y))) (𝓝[H] 0) (𝓝 0) := by
  set Tc := firstContactTime (fun t => sphereInv (γ t : OnePoint ℂ)) ((fun t => (α t : OnePoint ℂ)) '' Icc 0 s)
    with hTcdef
  set Wc : ℝ → ℝ := fun r => w r.toNNReal with hWcdef
  have hWcc : Continuous Wc := hw.comp continuous_real_toNNReal
  have hWc0 : Wc 0 = 0 := by simp [hWcdef, hw0]
  have hs0 : (0 : ℝ) < s := by
    rcases eq_or_lt_of_le (NNReal.coe_nonneg s) with h0 | h0
    · exfalso
      have hs' : s = 0 := by exact_mod_cast h0.symm
      exact GB6.ne_zero_of_mem_H hsH (by rw [hs']; exact hα.1)
    · exact h0
  obtain ⟨Wr, ηr, hWr, hWr0, hηr, hK, ha0, hsm, hac, hd⟩ :=
    exists_relChain_trace hα hwα hwα0 hs hsH hU hU0 hst₂ hUeq hγ hw hw0 ht₁
  set a : ℝ → ℝ := relClock U s Wc with hadef
  have htTc : (t : ℝ≥0∞) < Tc := lt_of_le_of_lt (ENNReal.coe_le_coe.2 htt₁.le) ht₁
  have h0Tc : ((0 : ℝ≥0) : ℝ≥0∞) < Tc := lt_of_le_of_lt bot_le htTc
  have hu : 0 < a t := by
    have := hsm h0Tc htTc ht0
    simpa [ha0] using this
  have hKt := hK t htt₁.le
  have hdt := hd t htTc
  have hdA : ∀ T : ℝ≥0, (T : ℝ≥0∞) < Tc → Disjoint (closure (fwdHull Wc T)) (closure (invHull U s)) :=
    fun T hT => Q3Rel.disjoint_closure_invHull hU hs0.le (hd T hT)
  have hγL := isLoewnerTrace_of_isGeneratingTrace hγ
  have hSbK := Q3Rel.relBad_notMem_closure hU hU0 hs0.le hWcc t.2 hKt (hdA t htTc)
  obtain ⟨hg, hA0⟩ := goodPt_zero_and_notMem hΨ hWcc t.2 hWr hWr0 hηr hu hKt (hdA t htTc) hSbK
  refine ⟨Wr, ηr, hWr, hWr0, hηr, hu, hKt, hdt, ?_⟩
  refine tendsto_tip_of_later hΨ hWcc hWc0 hγL t.2 hWr hWr0 hηr hu.le hKt (hdA t htTc) hg hA0 fun δ hδ => ?_
  have hopen : IsOpen {t : ℝ≥0 | (t : ℝ≥0∞) < Tc} := isOpen_lt ENNReal.continuous_coe continuous_const
  have hcont : ContinuousAt (fun t : ℝ≥0 => a t) t := hac.continuousAt (hopen.mem_nhds htTc)
  obtain ⟨η, hη, hηb⟩ := Metric.continuousAt_iff.1 hcont δ hδ
  set ε : ℝ := min (min δ η) ((t₁ : ℝ) - t) / 2 with hεdef
  have htt₁' : (t : ℝ) < t₁ := by exact_mod_cast htt₁
  have hε0 : 0 < ε := by
    have : 0 < min (min δ η) ((t₁ : ℝ) - t) := lt_min (lt_min hδ hη) (by linarith)
    rw [hεdef]; linarith
  have hεδ : ε < δ := by
    have := min_le_left (min δ η) ((t₁ : ℝ) - t)
    have := min_le_left δ η
    rw [hεdef]; linarith
  have hεη : ε < η := by
    have := min_le_left (min δ η) ((t₁ : ℝ) - t)
    have := min_le_right δ η
    rw [hεdef]; linarith
  have hεt : ε < (t₁ : ℝ) - t := by
    have := min_le_right (min δ η) ((t₁ : ℝ) - t)
    rw [hεdef]; linarith
  set t' : ℝ≥0 := ⟨(t : ℝ) + ε, by positivity⟩ with ht'def
  have ht'v : (t' : ℝ) = t + ε := rfl
  have htt' : t < t' := by rw [← NNReal.coe_lt_coe, ht'v]; linarith
  have ht't₁ : t' ≤ t₁ := by rw [← NNReal.coe_le_coe, ht'v]; linarith
  have ht'Tc : (t' : ℝ≥0∞) < Tc := lt_of_le_of_lt (ENNReal.coe_le_coe.2 ht't₁) ht₁
  have hdist : dist t' t < η := by
    rw [NNReal.dist_eq, ht'v, add_sub_cancel_left, abs_of_pos hε0]
    exact hεη
  have hau : a t < a t' := hsm htTc ht'Tc htt'
  have hau' : a t' < a t + δ := by
    have := hηb hdist
    rw [Real.dist_eq] at this
    linarith [le_abs_self (a t' - a t)]
  refine ⟨t', a t', by rw [ht'v]; linarith, by rw [ht'v]; linarith, hau, hau', hK t' ht't₁, ?_⟩
  exact Set.disjoint_of_subset_left subset_closure
    (Set.disjoint_of_subset_right subset_closure (hdA t' ht'Tc))

end Chain

end InteractingSLE.Supp8.Q3Kernel
