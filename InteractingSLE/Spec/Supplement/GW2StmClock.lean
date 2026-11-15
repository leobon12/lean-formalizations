/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6Restart
import InteractingSLE.Spec.Supplement.BW1DetIdent

/-!
# GW2's stage step, part 5: GB6's time change with an explicit measurable inverse clock

Packet PROVE-GW2-STAGEMEAN, round 2 (the conditional counterflow at every launch of a GW2 schedule, in the equality
form `GW2TipSystem.HasLaunchPairEq`). GB6's chart continuation (`Supp8.GB6.isGB6ChartContinuation_of_relHulls`)
identifies the relative counterflow with the physical one through the time change `ℓ = clockInv (relClock …) T_c`,
a choice of preimage; the launch datum needs a time change measurable in the sample. This file gives an explicit one:

* `ellQ a u`: the first rational time at which the clock `a` exceeds the level `u` (an infimum over `ℚ`), and
  **`ellQ_eq_clockInv`**: for an exhausting clock `a` before `T` (`Sec5.CrossRestart.IsExhaustingClock`) and any `b`
  equal to `a` before `T`, `ellQ b u` is the inverse `clockInv a T u` (values of `b` after `T` do not matter);
  **`measurable_ellQ`**: measurable in the sample whenever the clock is, at every time;
* `evalQ g t` (the time change read through rational times below `t`): **`evalQ_eq`** for monotone continuous `g`,
  **`measurable_evalQ`** at a measurable random time (the composite time change `ℓ_j ∘ ℓ₂` of the launch datum);
* **`chartContinuation_explicit`**: GB6's chart continuation (the hypotheses of
  `isGB6ChartContinuation_of_relHulls` without the transport) with the clock `relClock` exhausting before the first
  contact and the time change named: `η (clockInv (relClock …) T_c u) = c_U⁻¹ (Γ u)` whenever `Γ u ∈ ℍ`.

Deterministic. Conditional helpers with distinct names.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology Complex
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.GW2Stm

open Supp8.GB6 Sec5.CrossRestart

/-! ### The explicit inverse clock -/

/-- **The first rational time at which the clock `a` exceeds the level `u`.** -/
def ellQ (a : ℝ≥0 → ℝ) (u : ℝ≥0) : ℝ≥0 :=
  (⨅ q : ℚ, if 0 ≤ q ∧ (u : ℝ) < a (q : ℝ).toNNReal then (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) else ⊤).toNNReal

/-- **The explicit inverse is the inverse of an exhausting clock**, whatever the values after `T`. -/
theorem ellQ_eq_clockInv {a b : ℝ≥0 → ℝ} {T : ℝ≥0∞} (ha : IsExhaustingClock a T)
    (hab : ∀ t : ℝ≥0, (t : ℝ≥0∞) < T → b t = a t) (u : ℝ≥0) : ellQ b u = clockInv a T u := by
  obtain ⟨ht₀T, hat₀⟩ := ha.clockInv_spec u
  set t₀ := clockInv a T u with ht₀
  have key : (⨅ q : ℚ, if 0 ≤ q ∧ (u : ℝ) < b (q : ℝ).toNNReal then
      (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) else ⊤) = (t₀ : ℝ≥0∞) := by
    refine le_antisymm ?_ ?_
    · refine le_of_forall_gt_imp_ge_of_dense fun c hc => ?_
      obtain ⟨q, hq0, hq1, hq2⟩ := ENNReal.lt_iff_exists_rat_btwn.1 (lt_min hc ht₀T)
      have hqT : (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) < T := hq2.trans_le (min_le_right _ _)
      have hlt : t₀ < (q : ℝ).toNNReal := ENNReal.coe_lt_coe.1 hq1
      have hcond : 0 ≤ q ∧ (u : ℝ) < b (q : ℝ).toNNReal := by
        refine ⟨hq0, ?_⟩
        rw [hab _ hqT, ← hat₀]
        exact ha.mono ht₀T hqT hlt
      refine (iInf_le _ q).trans ?_
      simp only [hcond, and_self, ↓reduceIte]
      exact (hq2.trans_le (min_le_left _ _)).le
    · refine le_iInf fun q => ?_
      split_ifs with hcond
      · refine le_of_not_gt fun hlt => ?_
        have hlt' : (q : ℝ).toNNReal < t₀ := ENNReal.coe_lt_coe.1 hlt
        have hqT : (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) < T := hlt.trans ht₀T
        have h1 := ha.mono hqT ht₀T hlt'
        rw [hat₀, ← hab _ hqT] at h1
        exact absurd hcond.2 (not_lt.2 h1.le)
      · exact le_top
  rw [ellQ, key, ENNReal.toNNReal_coe]

/-- **The explicit inverse is measurable in the sample** when the clock is measurable at every time. -/
theorem measurable_ellQ {Ω : Type*} [MeasurableSpace Ω] {a : Ω → ℝ≥0 → ℝ} (ha : ∀ t, Measurable fun ω => a ω t)
    (u : ℝ≥0) : Measurable fun ω => ellQ (a ω) u := by
  classical
  refine Measurable.ennreal_toNNReal (Measurable.iInf fun q : ℚ => ?_)
  refine Measurable.ite ?_ measurable_const measurable_const
  exact (MeasurableSet.const _).inter (measurableSet_lt measurable_const (ha _))

/-! ### Evaluating a time change at a random time -/

/-- **A time change read through rational times**: `evalQ g t = sup {g q : q ∈ ℚ≥0, q ≤ t}`. For a monotone continuous
`g` it is `g t` (`evalQ_eq`); for a time change measurable at every fixed time it is measurable at every measurable
random time (`measurable_evalQ`), whatever the regularity of the other samples. -/
def evalQ (g : ℝ≥0 → ℝ≥0) (t : ℝ≥0) : ℝ≥0 :=
  ⨆ q : ℚ≥0, if (q : ℝ≥0) ≤ t then g q else 0

/-- A monotone continuous time change is read through rational times. -/
theorem evalQ_eq {g : ℝ≥0 → ℝ≥0} (hm : Monotone g) (hc : Continuous g) (t : ℝ≥0) : evalQ g t = g t := by
  have hbdd : BddAbove (range fun q : ℚ≥0 => if (q : ℝ≥0) ≤ t then g q else 0) := by
    refine ⟨g t, ?_⟩
    rintro _ ⟨q, rfl⟩
    dsimp only
    split_ifs with hq
    · exact hm hq
    · positivity
  refine le_antisymm (ciSup_le fun q => ?_) ?_
  · split_ifs with hq
    · exact hm hq
    · positivity
  · obtain ⟨qs, hqle, hqs⟩ := BW1Det.exists_seq_nnrat_le_tendsto t
    have hlim : Tendsto (fun m => g (qs m)) atTop (𝓝 (g t)) := (hc.tendsto t).comp hqs
    refine le_of_tendsto' hlim fun m => ?_
    refine le_trans ?_ (le_ciSup hbdd (qs m))
    simp only [hqle m, ↓reduceIte, le_refl]

/-- A time change measurable at every fixed time, read through rational times, is measurable at a random time. -/
theorem measurable_evalQ {Ω : Type*} [MeasurableSpace Ω] {g : Ω → ℝ≥0 → ℝ≥0} (hg : ∀ t, Measurable fun ω => g ω t)
    {T : Ω → ℝ≥0} (hT : Measurable T) : Measurable fun ω => evalQ (g ω) (T ω) := by
  classical
  refine Measurable.iSup fun q : ℚ≥0 => ?_
  exact Measurable.ite (measurableSet_le measurable_const hT) (hg _) measurable_const

/-! ### GB6's chart continuation with the time change named -/

/-- **GB6's chart continuation with an explicit exhausting clock** (`isGB6ChartContinuation_of_relHulls`, hypotheses
without the field transport): the relative clock is exhausting before the first contact `T_c`, and its inverse is the
time change of the identification `η(ℓ u) = c_U⁻¹(Γ u)` at every `u` with `Γ u ∈ ℍ`. -/
theorem chartContinuation_explicit
    {wα w W' : ℝ≥0 → ℝ} {Tα : ℝ≥0∞} {α γ Γ : ℝ≥0 → ℂ} {s : ℝ≥0}
    (hα : IsGeneratingTrace wα Tα α) (hwα : ContinuousOn wα {t | (t : ℝ≥0∞) < Tα}) (hwα0 : wα 0 = 0)
    (hs : (s : ℝ≥0∞) < Tα) (hsH : α s ∈ H)
    (hγ : IsGeneratingTrace w ⊤ γ) (hw : Continuous w) (hw0 : w 0 = 0)
    (hΓ : IsGeneratingTrace W' ⊤ Γ) (hW' : Continuous W') (hW'0 : W' 0 = 0)
    (hunb : ∀ u : ℝ, ∃ t : ℝ≥0, (t : ℝ≥0∞) < firstContactTime (fun t => sphereInv (γ t : OnePoint ℂ))
        ((fun t => (α t : OnePoint ℂ)) '' Icc 0 s) ∧
      u ≤ relClock (fun r : ℝ => wα r.toNNReal) s (fun r : ℝ => w r.toNNReal) t)
    (hK : ∀ t : ℝ≥0, (t : ℝ≥0∞) < firstContactTime (fun t => sphereInv (γ t : OnePoint ℂ))
        ((fun t => (α t : OnePoint ℂ)) '' Icc 0 s) →
      QuantumZipper.fwdHull (fun r : ℝ => W' r.toNNReal)
          (relClock (fun r : ℝ => wα r.toNNReal) s (fun r : ℝ => w r.toNNReal) t) =
        relMap (fun r : ℝ => wα r.toNNReal) s '' QuantumZipper.fwdHull (fun r : ℝ => w r.toNNReal) t) :
    IsExhaustingClock (fun t : ℝ≥0 => relClock (fun r : ℝ => wα r.toNNReal) s (fun r : ℝ => w r.toNNReal) t)
        (firstContactTime (fun t => sphereInv (γ t : OnePoint ℂ)) ((fun t => (α t : OnePoint ℂ)) '' Icc 0 s)) ∧
      ∀ u : ℝ≥0, Γ u ∈ H →
        sphereInv (γ (clockInv (fun t : ℝ≥0 => relClock (fun r : ℝ => wα r.toNNReal) s (fun r : ℝ => w r.toNNReal) t)
          (firstContactTime (fun t => sphereInv (γ t : OnePoint ℂ)) ((fun t => (α t : OnePoint ℂ)) '' Icc 0 s)) u) :
            OnePoint ℂ) =
          (((ownComponentChart (fun r : ℝ => wα r.toNNReal) s).2.1 (Γ u) : ℂ) : OnePoint ℂ) := by
  set Tc := firstContactTime (fun t => sphereInv (γ t : OnePoint ℂ)) ((fun t => (α t : OnePoint ℂ)) '' Icc 0 s)
    with hTcdef
  set Ur : ℝ → ℝ := fun r => wα r.toNNReal with hUr
  set Wr : ℝ → ℝ := fun r => w r.toNNReal with hWr
  have hs0 : (0 : ℝ) < s := by
    rcases eq_or_lt_of_le (NNReal.coe_nonneg s) with h0 | h0
    · exfalso
      have hs' : s = 0 := by exact_mod_cast h0.symm
      exact ne_zero_of_mem_H hsH (by rw [hs']; exact hα.1)
    · exact h0
  -- the flow driver frozen after a time `t₂ ∈ (s, Tα)`
  obtain ⟨t₂, hst₂, ht₂⟩ := exists_real_btwn_of_lt hs
  set U' : ℝ → ℝ := frozenDrive wα t₂ with hU'def
  have hU' : Continuous U' := continuous_frozenDrive_of_lt hwα ht₂
  have ht₂0 : (0 : ℝ) ≤ t₂ := le_trans (NNReal.coe_nonneg s) hst₂.le
  have hU'0 : U' 0 = 0 := by rw [hU'def, frozenDrive_zero ht₂0, hwα0]
  have hagree : ∀ r ∈ Icc (0 : ℝ) t₂, Ur r = U' r := fun r hr => (frozenDrive_eq hr).symm
  have hagree_s : ∀ r ∈ Icc (0 : ℝ) s, Ur r = U' r := fun r hr => hagree r ⟨hr.1, hr.2.trans hst₂.le⟩
  have hrel : relMap Ur s = relMap U' s := relMap_eq_of_eqOn (NNReal.coe_nonneg s) hagree_s
  have hclock : relClock Ur s Wr = relClock U' s Wr := relClock_eq_of_eqOn (NNReal.coe_nonneg s) hagree_s Wr
  have hhull : QuantumZipper.fwdHull Ur s = QuantumZipper.fwdHull U' s :=
    fwdHull_eq_of_eqOn (NNReal.coe_nonneg s) hst₂ hagree
  have hinv : (ownComponentChart Ur s).2.1 = (ownComponentChart U' s).2.1 :=
    ownComponentChart_inv_eq_of_eqOn (NNReal.coe_nonneg s) hst₂ hagree
  have htip : Tendsto (QuantumZipper.fwdMapInv U' s) (𝓝[H] 0) (𝓝 (α s)) := by
    have h1 := IsGeneratingTrace.tendsto_fwdMapInv_tip hα hwα hwα0 hs
    have h2 : QuantumZipper.fwdMapInv Ur s = QuantumZipper.fwdMapInv U' s :=
      fwdMapInv_eq_of_eqOn (NNReal.coe_nonneg s) hst₂ hagree
    rw [← h2]
    exact h1
  -- disjoint closed hulls before the contact
  have hd : ∀ T : ℝ≥0, (T : ℝ≥0∞) < Tc → Disjoint (closure (QuantumZipper.fwdHull U' s))
      (closure ((fun w : ℂ => -w⁻¹) '' QuantumZipper.fwdHull Wr T)) := fun T hT => by
    rw [← hhull]
    exact disjoint_closure_fwdHull_of_lt_firstContactTime hα hwα hwα0 hγ hw.continuousOn hw0 hs
      ENNReal.coe_lt_top hT
  -- the first contact is positive
  have hγc : Continuous γ := by
    have := hγ.2.1
    simp only [le_top, ofPred_true] at this
    exact continuousOn_univ.1 this
  have hTc : 0 < Tc := by
    have hk : IsCompact (α '' Icc 0 s) := isCompact_Icc.image_of_continuousOn
      (hα.2.1.mono fun t ht => le_trans (by exact_mod_cast ht.2) hs.le)
    have := firstContactTime_pos hγc.continuousAt hγ.1 hk.isBounded
    rwa [image_image] at this
  have hγK : ∀ t : ℝ≥0, (t : ℝ≥0∞) < Tc → IsFilling (QuantumZipper.fwdHull Wr t) (γ '' Icc 0 t) :=
    fun t _ => hγ.2.2 t ENNReal.coe_lt_top
  obtain ⟨-, -, ha0, hsm, hac, -, -⟩ := exists_glued_relChain hw hw0 hU' hU'0 hs0 htip hTc hd hγK
  have hexh : Sec5.CrossRestart.IsExhaustingClock (fun t : ℝ≥0 => relClock U' s Wr t) Tc := by
    refine ⟨hTc, ha0, hsm, hac, fun u => ?_⟩
    obtain ⟨t, ht, hu⟩ := hunb u
    exact ⟨t, ht, by rw [← hclock]; exact hu⟩
  have hnn : ∀ t : ℝ≥0, (t : ℝ≥0∞) < Tc → 0 ≤ relClock U' s Wr t := fun t ht => hexh.nonneg ht
  have hK' : ∀ t : ℝ≥0, (t : ℝ≥0∞) < Tc →
      QuantumZipper.fwdHull (fun r : ℝ => W' r.toNNReal) (relClock U' s Wr t) =
        relMap U' s '' QuantumZipper.fwdHull Wr t := fun t ht => by
    rw [← hclock, ← hrel]; exact hK t ht
  have hdom : ∀ t : ℝ≥0, (t : ℝ≥0∞) < Tc →
      ∀ x ∈ QuantumZipper.fwdHull Wr t, -x⁻¹ ∉ QuantumZipper.fwdHull U' s := fun t ht x hx hxK =>
    Set.disjoint_left.1 (hd t ht) (subset_closure hxK) (subset_closure ⟨x, hx, rfl⟩)
  have hγdom : ∀ t : ℝ≥0, (t : ℝ≥0∞) < Tc → γ t ∈ H → -(γ t)⁻¹ ∉ QuantumZipper.fwdHull U' s := by
    intro t ht hγt
    obtain ⟨T', htT', hT'⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht
    have hmem : γ t ∈ QuantumZipper.fwdHull Wr T' :=
      Sec5.CrossRestart.inter_H_subset_of_isFilling (hγ.2.2 T' ENNReal.coe_lt_top)
        ⟨⟨t, ⟨zero_le, (ENNReal.coe_lt_coe.1 htT').le⟩, rfl⟩, hγt⟩
    exact hdom T' hT' _ hmem
  have hexhU : IsExhaustingClock (fun t : ℝ≥0 => relClock Ur s Wr t) Tc := by
    have e : (fun t : ℝ≥0 => relClock Ur s Wr t) = fun t : ℝ≥0 => relClock U' s Wr t := by rw [hclock]
    rw [e]
    exact hexh
  refine ⟨hexhU, fun u hu => ?_⟩
  have e2 : clockInv (fun t : ℝ≥0 => relClock Ur s Wr t) Tc = clockInv (fun t : ℝ≥0 => relClock U' s Wr t) Tc := by
    rw [hclock]
  rw [e2]
  obtain ⟨ht, hat⟩ := hexh.clockInv_spec u
  set t := clockInv (fun t : ℝ≥0 => relClock U' s Wr t) Tc u with htdef
  have hnn' : (relClock U' s Wr t).toNNReal = u := by
    have hat' : relClock U' s Wr t = u := hat
    rw [hat', Real.toNNReal_coe]
  have hΓH : Γ (relClock U' s Wr t).toNNReal ∈ H := by rw [hnn']; exact hu
  obtain ⟨hγH, hΓeq⟩ := relTrace_eq hw hw0 hU' hU'0 (NNReal.coe_nonneg s) hγ hW' hW'0 hΓ hsm hnn hK' hdom hγdom ht hΓH
  have hΓeq' : Γ u = relMap U' s (γ t) :=
    calc Γ u = Γ (relClock U' s Wr t).toNNReal := by rw [hnn']
      _ = relMap U' s (γ t) := hΓeq
  rw [hΓeq', hinv, ownComponentChart_inv_relMap hU' hU'0 (NNReal.coe_nonneg s) hγH (hγdom t ht hγH),
    sphereInv_coe_of_ne (ne_zero_of_mem_H hγH)]

end InteractingSLE.Theorem14.GW2Stm
