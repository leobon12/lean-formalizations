/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootH29Record

/-!
# Causal monotonicity of the actual switched candidate sigma algebras

Packet PROVE-T14-GW2ROOT2. Increasing a candidate's recording cutoff
enlarges its retained sigma algebra, even though the two candidates
use different canonical programs. Shorter-record reconstruction includes
death flags and every exceptional sample.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.RootH29

open GW2Schedule GW2Tip Exist Staged StagedLaw Restart LQGMetric RootC24

/-- The last recording duration is the prescribed time minus the
unchanged preceding time, with the source's nonnegative subtraction. -/
theorem specDelta_last (x θ : ℝ) (l : List (ℝ × ℝ≥0)) (q : ℝ≥0) :
    specDelta (schedSpec x (l ++ [(θ, q)])) l.length =
      ((q - schedTime 0 l l.length : ℝ≥0) : ℝ≥0∞) := by
  have hi := isFlowProg_scheduleProgram 0 (l ++ [(θ, q)]) l.length
    (by rw [length_scheduleProgram, List.length_append, List.length_singleton]; omega)
  have ht : instrTime (schedSpec x (l ++ [(θ, q)])) l.length =
      schedDelta 0 (l ++ [(θ, q)]) l.length := by
    simp only [instrTime, schedSpec, hi]
  rw [specDelta, ht, ite_eq_right (schedDelta_ne_top _ _ _)]
  simp only [schedDelta, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self,
    List.getD_cons_zero, schedTime_append 0 (θ, q) le_rfl]

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- The retained sigma algebra grows with a candidate's last cutoff,
at every real root and after every finite switched history. -/
theorem stageSigma_last_mono (c : SourceData Ω) (x θ : ℝ)
    (l : List (ℝ × ℝ≥0)) {q q' : ℝ≥0} (hqq' : q ≤ q') :
    stageSigma c.hκ c.h12p c.βA c.c₀ c.h c.s c.W c.ζ
        (schedSpec x (l ++ [(θ, q)])) (l.length + 1) ≤
      stageSigma c.hκ c.h12p c.βA c.c₀ c.h c.s c.W c.ζ
        (schedSpec x (l ++ [(θ, q')])) (l.length + 1) := by
  let σ := stageSigma c.hκ c.h12p c.βA c.c₀ c.h c.s c.W c.ζ
    (schedSpec x (l ++ [(θ, q')])) (l.length + 1)
  let _ : MeasurableSpace Ω := mΩ
  have hcf : Measurable[σ] (cfRec c.s c.W c.ζ) :=
    measurable_fst.comp (comap_measurable (stageMap c.hκ c.h12p c.βA c.c₀ c.h
      c.s c.W c.ζ (schedSpec x (l ++ [(θ, q')])) (l.length + 1)))
  have hrec : ∀ j : Fin (l.length + 1), Measurable[σ]
      (stopRec c.hκ c.h12p c.βA c.c₀ c.h (schedSpec x (l ++ [(θ, q)])) j) := by
    intro j
    by_cases hj : (j : ℕ) < l.length
    · have heq : stopRec c.hκ c.h12p c.βA c.c₀ c.h (schedSpec x (l ++ [(θ, q)])) j =
          stopRec c.hκ c.h12p c.βA c.c₀ c.h (schedSpec x (l ++ [(θ, q')])) j := by
        funext ω
        exact (stopRec_schedSpec_append c.hκ c.h12p c.βA c.c₀ c.h x (θ, q) hj ω).trans
          (stopRec_schedSpec_append c.hκ c.h12p c.βA c.c₀ c.h x (θ, q') hj ω).symm
      rw [heq]
      exact RootU19.measurable_stageSigma_stopRec c.hκ c.h12p c.βA c.c₀ c.h
        c.s c.W c.ζ _ _ j
    · have hj : (j : ℕ) = l.length := by omega
      have hδ : specDelta (schedSpec x (l ++ [(θ, q)])) l.length ≤
          specDelta (schedSpec x (l ++ [(θ, q')])) l.length := by
        rw [specDelta_last, specDelta_last]
        exact ENNReal.coe_le_coe.mpr (tsub_le_tsub_right hqq' _)
      let t := (specDelta (schedSpec x (l ++ [(θ, q)])) l.length).toNNReal
      have ht : (t : ℝ≥0∞) = specDelta (schedSpec x (l ++ [(θ, q)])) l.length :=
        ENNReal.coe_toNNReal (specDelta_ne_top _ _)
      have hm := measurable_next_record_other_cutoff c x θ l q q' t (ht.symm ▸ hδ)
      change Measurable[σ] fun ω => recOf (specDelta _ j) (canonSpecFam _ _ _ _ _ _ j ω)
      simp_rw [hj, ← ht]
      exact hm
  have hp : Measurable[σ] fun ω => fun j : Fin (l.length + 1) =>
      stopRec c.hκ c.h12p c.βA c.c₀ c.h (schedSpec x (l ++ [(θ, q)])) j ω :=
    (@measurable_pi_iff Ω (Fin (l.length + 1)) (fun _ => RecData) σ
      (fun _ => inferInstance) _).mpr hrec
  exact (hcf.prodMk hp).comap_le

/-- The exact root-test sigma algebras are monotone in the proposed
next recording time. No successful-history or regularity event is needed. -/
theorem rootSigma_next_mono (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (θ : c.Θ) {q q' : c.Q} (hqq' : q ≤ q') :
    c.sigma r ((θ, q) :: l) ≤ c.sigma r ((θ, q') :: l) := by
  have hm := stageSigma_last_mono c (rootPt r.1) θ
    (schedOf (rootEntry r.1) (entryList l)) hqq'
  simpa only [SourceData.sigma, rootSigma, schedSpecOf, entryList_cons,
    schedOf_cons, List.length_cons, length_schedOf] using hm

end InteractingSLE.Theorem14.GW2TipSystem.RootH29
