/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.Assembly2Shift
import InteractingSLE.Spec.Sec2.AssemblyPathwise
import InteractingSLE.Frozen.Spec.IsOrderedForceWord

/-!
# Theorem 2.2 assembly: pathwise uniqueness after a separated time

Packet PROVE-SEC2-PATCH2. Two deterministic facts about solutions of Definition 2.1 for an
ordered force word:

* `IsIntegratedSLEPath.vL_lt_vR_of_pos`: at every time `0 < t < ζ` every left mark is strictly to
  the left of every right mark (the gap `V^{1,R} − V^{1,L}` grows strictly, the collision sets
  being null), so the state at a positive time is a *separated* word;
* `IsIntegratedSLEPath.eq_of_agree_of_separated`: two solutions driven by the same path that
  agree before a time `σ > 0`, the first being separated at `σ` if `σ < ζ`, have the same lifetime
  and coincide (restart both at `σ`, `IsIntegratedSLEPath.shift`, and apply pathwise uniqueness
  for separated words, `IsIntegratedSLEPath.eq_of_separated`; a solution cannot die at `σ` while
  the other continues, by the maximality clause and `not_threshold`).

The second fact is what makes the law of an evolution a function of the law of the evolution
stopped at a positive time (`Assembly2Reduce`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE

open Sec2 Sec2.Assembly Sec2.Assembly2

namespace IsIntegratedSLEPath

variable {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ} {w w' : ℝ≥0 → ℝ} {vL vL' : Fin nL → ℝ≥0 → ℝ} {vR vR' : Fin nR → ℝ≥0 → ℝ}
  {b : ℝ≥0 → ℝ} {ζ ζ' : ℝ≥0∞}

/-- The state at a time `t < ζ` with `0 < t` is the continuous left limit, so two solutions that
agree before `t` and both live past `t` agree at `t`. -/
theorem agree_at_of_agree_before (h : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ)
    (h' : IsIntegratedSLEPath a xL xR ρL ρR w' vL' vR' b ζ') {σ : ℝ≥0} (hσ0 : 0 < σ)
    (hσ : (σ : ℝ≥0∞) < ζ) (hσ' : (σ : ℝ≥0∞) < ζ')
    (hag : ∀ t < σ, w t = w' t ∧ (∀ i, vL i t = vL' i t) ∧ ∀ j, vR j t = vR' j t) :
    w σ = w' σ ∧ (∀ i, vL i σ = vL' i σ) ∧ ∀ j, vR j σ = vR' j σ := by
  have hp := h.isForcePath
  have hp' := h'.isForcePath
  have hsub : ∀ {ξ : ℝ≥0∞}, (σ : ℝ≥0∞) < ξ → Iic σ ⊆ {t : ℝ≥0 | (t : ℝ≥0∞) < ξ} :=
    fun hξ t ht => lt_of_le_of_lt (by exact_mod_cast ht) hξ
  refine ⟨eq_of_eqOn_Iio hσ0 (hp.continuousOn_w.mono (hsub hσ))
      (hp'.continuousOn_w.mono (hsub hσ')) fun s hs => (hag s hs).1, fun i => ?_, fun j => ?_⟩
  · exact eq_of_eqOn_Iio hσ0 ((hp.continuousOn_vL i).mono (hsub hσ))
      ((hp'.continuousOn_vL i).mono (hsub hσ')) fun s hs => (hag s hs).2.1 i
  · exact eq_of_eqOn_Iio hσ0 ((hp.continuousOn_vR j).mono (hsub hσ))
      ((hp'.continuousOn_vR j).mono (hsub hσ')) fun s hs => (hag s hs).2.2 j

/-- A solution cannot die at a time `σ > 0` at which another solution, agreeing with it before
`σ`, is still alive: the continuous left limit would be a threshold state. -/
theorem not_lifetime_eq_of_agree (h : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ)
    (h' : IsIntegratedSLEPath a xL xR ρL ρR w' vL' vR' b ζ') {σ : ℝ≥0} (hσ0 : 0 < σ)
    (hσ : (σ : ℝ≥0∞) = ζ) (hσ' : (σ : ℝ≥0∞) < ζ')
    (hag : ∀ t < σ, w t = w' t ∧ (∀ i, vL i t = vL' i t) ∧ ∀ j, vR j t = vR' j t) : False := by
  have hp := h.isForcePath
  have hp' := h'.isForcePath
  have hopen : IsOpen {t : ℝ≥0 | (t : ℝ≥0∞) < ζ'} := isOpen_lt ENNReal.continuous_coe
    continuous_const
  have hca : ∀ {f : ℝ≥0 → ℝ}, ContinuousOn f {t | (t : ℝ≥0∞) < ζ'} → ContinuousAt f σ :=
    fun hf => hf.continuousAt (hopen.mem_nhds hσ')
  have hcont : ContinuousAt (fun t => (w' t, fun i => vL' i t, fun j => vR' j t)) σ :=
    (hca hp'.continuousOn_w).prodMk ((continuousAt_pi.2 fun i => hca (hp'.continuousOn_vL i)).prodMk
      (continuousAt_pi.2 fun j => hca (hp'.continuousOn_vR j)))
  have hlim : Tendsto (fun t => (w t, fun i => vL i t, fun j => vR j t)) (𝓝[<] σ)
      (𝓝 (w' σ, fun i => vL' i σ, fun j => vR' j σ)) := by
    refine (hcont.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    obtain ⟨e1, e2, e3⟩ := hag t ht
    simp only [e1, e2, e3]
  exact hp'.not_threshold hσ' (hp.threshold_of_tendsto hσ0 hσ hlim)

/-- **Pathwise uniqueness after a separated time.** Two solutions of Definition 2.1 driven by the
same path, agreeing before a time `σ > 0` that neither has passed, the first being separated at
`σ` (if alive there), have the same lifetime and coincide before it. -/
theorem eq_of_agree_of_separated (h : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ)
    (h' : IsIntegratedSLEPath a xL xR ρL ρR w' vL' vR' b ζ') {σ : ℝ≥0} (hσ0 : 0 < σ)
    (hσζ : (σ : ℝ≥0∞) ≤ ζ) (hσζ' : (σ : ℝ≥0∞) ≤ ζ')
    (hag : ∀ t < σ, w t = w' t ∧ (∀ i, vL i t = vL' i t) ∧ ∀ j, vR j t = vR' j t)
    (hsep : (σ : ℝ≥0∞) < ζ → ∀ i j, vL i σ < vR j σ) :
    ζ = ζ' ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ →
      w t = w' t ∧ (∀ i, vL i t = vL' i t) ∧ ∀ j, vR j t = vR' j t := by
  have hag' : ∀ t < σ, w' t = w t ∧ (∀ i, vL' i t = vL i t) ∧ ∀ j, vR' j t = vR j t :=
    fun t ht => ⟨(hag t ht).1.symm, fun i => ((hag t ht).2.1 i).symm,
      fun j => ((hag t ht).2.2 j).symm⟩
  rcases hσζ.lt_or_eq with hlt | heq
  · rcases hσζ'.lt_or_eq with hlt' | heq'
    · -- both alive at `σ`: restart and use uniqueness for the separated word
      obtain ⟨e1, e2, e3⟩ := agree_at_of_agree_before h h' hσ0 hlt hlt' hag
      have hs := h.shift hlt
      have hs' := h'.shift hlt'
      have hxL : (fun i => vL' i σ - w' σ) = fun i => vL i σ - w σ := by
        funext i; rw [e1, e2 i]
      have hxR : (fun j => vR' j σ - w' σ) = fun j => vR j σ - w σ := by
        funext j; rw [e1, e3 j]
      rw [hxL, hxR] at hs'
      have hsep' : ∀ i j, vL i σ - w σ < vR j σ - w σ := fun i j => by
        linarith [hsep hlt i j]
      obtain ⟨hζ, hagr⟩ := eq_of_separated hsep' hs hs'
      have hζζ : ζ = ζ' := (tsub_left_inj hlt.le hlt'.le).1 hζ
      refine ⟨hζζ, fun t ht => ?_⟩
      rcases lt_or_ge t σ with hts | hts
      · exact hag t hts
      · have ht' : ((t - σ : ℝ≥0) : ℝ≥0∞) < ζ - σ := by
          rw [coe_lt_sub_iff, add_tsub_cancel_of_le hts]; exact ht
        obtain ⟨f1, f2, f3⟩ := hagr _ ht'
        simp only [shiftAt, add_tsub_cancel_of_le hts, e1, sub_left_inj] at f1 f2 f3
        exact ⟨f1, f2, f3⟩
    · exact (not_lifetime_eq_of_agree h' h hσ0 heq' hlt hag').elim
  · rcases hσζ'.lt_or_eq with hlt' | heq'
    · exact (not_lifetime_eq_of_agree h h' hσ0 heq hlt' hag).elim
    · refine ⟨heq.symm.trans heq', fun t ht => hag t ?_⟩
      rw [← heq] at ht; exact_mod_cast ht

/-- **Separation at positive times.** For an ordered force word, at every time `0 < t < ζ` every
left mark is strictly to the left of every right mark. -/
theorem vL_lt_vR_of_pos (h : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ)
    (hF : IsOrderedForceWord xL xR) {t : ℝ≥0} (ht0 : 0 < t) (ht : (t : ℝ≥0∞) < ζ) (i : Fin nL)
    (j : Fin nR) : vL i t < vR j t := by
  have hp := h.isForcePath
  have hnL : 0 < nL := Fin.pos i
  have hnR : 0 < nR := Fin.pos j
  set p : Fin nL := ⟨0, hnL⟩
  set q : Fin nR := ⟨0, hnR⟩
  have hip : vL i t ≤ vL p t := hp.antitone_vL ht (show p ≤ i from Nat.zero_le _)
  have hqj : vR q t ≤ vR j t := hp.monotone_vR ht (show q ≤ j from Nat.zero_le _)
  suffices hpq : vL p t < vR q t by linarith
  -- `V^{q,R} − W > 0` almost everywhere on `[0, t]`, so its force integral is positive
  have hf : IntervalIntegrable (fun s : ℝ => 2 / (vR q s.toNNReal - w s.toNNReal)) volume 0 t := by
    simpa only [two_div_sub_eq] using (hp.integrable_gapR ht q).const_mul (-2)
  have hg : IntervalIntegrable (fun s : ℝ => 2 / (vL p s.toNNReal - w s.toNNReal)) volume 0 t := by
    simpa only [two_div_sub_eq] using (hp.integrable_gapL ht p).const_mul (-2)
  have hnn : ∀ s : ℝ, s ∈ Icc (0 : ℝ) t → 0 ≤ 2 / (vR q s.toNNReal - w s.toNNReal) := by
    intro s hs
    have hst : ((s.toNNReal : ℝ≥0) : ℝ≥0∞) < ζ := lt_of_le_of_lt
      (by exact_mod_cast Real.toNNReal_le_iff_le_coe.2 hs.2) ht
    exact div_nonneg zero_le_two (sub_nonneg.2 (hp.w_le_vR hst q))
  have hnn' : ∀ s : ℝ, s ∈ Icc (0 : ℝ) t → 2 / (vL p s.toNNReal - w s.toNNReal) ≤ 0 := by
    intro s hs
    have hst : ((s.toNNReal : ℝ≥0) : ℝ≥0∞) < ζ := lt_of_le_of_lt
      (by exact_mod_cast Real.toNNReal_le_iff_le_coe.2 hs.2) ht
    exact div_nonpos_of_nonneg_of_nonpos zero_le_two (sub_nonpos.2 (hp.vL_le_w hst p))
  have hpos : 0 < ∫ s in (0 : ℝ)..t, 2 / (vR q s.toNNReal - w s.toNNReal) := by
    rw [intervalIntegral.integral_pos_iff_support_of_nonneg_ae' _ hf]
    · refine ⟨by exact_mod_cast ht0, ?_⟩
      -- the support contains `(0, t]` minus the null collision set
      have hnull := hp.volume_collisionR q
      have hsub : Ioc (0 : ℝ) t \ {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < ζ ∧
          w s.toNNReal = vR q s.toNNReal} ⊆
          Function.support (fun s : ℝ => 2 / (vR q s.toNNReal - w s.toNNReal)) ∩ Ioc 0 t := by
        rintro s ⟨hs, hsn⟩
        refine ⟨?_, hs⟩
        have hst : ((s.toNNReal : ℝ≥0) : ℝ≥0∞) < ζ := lt_of_le_of_lt
          (by exact_mod_cast Real.toNNReal_le_iff_le_coe.2 hs.2) ht
        have hne : w s.toNNReal ≠ vR q s.toNNReal := fun he => hsn ⟨hs.1.le, hst, he⟩
        have hle := hp.w_le_vR hst q
        have : 0 < vR q s.toNNReal - w s.toNNReal := sub_pos.2 (lt_of_le_of_ne hle hne)
        exact (div_pos two_pos this).ne'
      refine lt_of_lt_of_le ?_ (measure_mono hsub)
      rw [measure_sdiff_null hnull, Real.volume_Ioc, sub_zero, ENNReal.ofReal_pos]
      exact_mod_cast ht0
    · rw [uIoc_of_le (NNReal.coe_nonneg t)]
      exact (ae_restrict_iff' measurableSet_Ioc).2
        (Eventually.of_forall fun s hs => hnn s (Ioc_subset_Icc_self hs))
  have hneg : ∫ s in (0 : ℝ)..t, 2 / (vL p s.toNNReal - w s.toNNReal) ≤ 0 :=
    by
      have := intervalIntegral.integral_mono_on (NNReal.coe_nonneg t) hg
        (intervalIntegrable_const (c := (0 : ℝ))) hnn'
      simpa only [intervalIntegral.integral_const, smul_zero] using this
  rw [hp.vL_eq ht p, hp.vR_eq ht q]
  have := hF.2.1 p
  have := hF.2.2.2 q
  linarith

end IsIntegratedSLEPath

end InteractingSLE
