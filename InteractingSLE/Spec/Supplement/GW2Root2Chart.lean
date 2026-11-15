/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2Root2Records

/-!
# The counterflow hull is determined by its stopped regularized record

Packet PROVE-T14-GW2ROOT2. The endpoint case uses the death flag: after death
the whole regular driver has been retained; before death continuity past the
stop permits the existing Loewner hull congruence theorem.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.GW2TipSystem

open Exist Staged StagedLaw

/-- A regular driver's canonical stopped extension agrees with it through the stop. -/
theorem canonDrv_fst_eq_of_le {e : (ℝ≥0 → ℝ) × ℝ≥0∞}
    (he : IsRegularDriver e) {s r : ℝ≥0} (hr : r ≤ s) :
    (canonDrv (s : ℝ≥0∞) e).1 r = e.1 r := by
  change e.1 (min (r : ℝ≥0∞) (min (s : ℝ≥0∞) e.2)).toNNReal = e.1 r
  rw [← min_assoc, min_eq_left (ENNReal.coe_le_coe.2 hr)]
  by_cases hζ : (r : ℝ≥0∞) ≤ e.2
  · rw [min_eq_left hζ, ENNReal.toNNReal_coe]
  · rw [min_eq_right (not_le.1 hζ).le]
    exact (he.2.2.1 r (not_le.1 hζ).le).symm

/-- After a regular driver has died its stopped canonical extension is the driver. -/
theorem canonDrv_eq_self_of_lifetime_le {e : (ℝ≥0 → ℝ) × ℝ≥0∞}
    (he : IsRegularDriver e) {s : ℝ≥0} (hs : e.2 ≤ s) :
    canonDrv (s : ℝ≥0∞) e = e := by
  apply Prod.ext
  · funext r
    change e.1 (min (r : ℝ≥0∞) (min (s : ℝ≥0∞) e.2)).toNNReal = e.1 r
    rw [min_eq_right hs]
    by_cases hζ : (r : ℝ≥0∞) ≤ e.2
    · rw [min_eq_left hζ, ENNReal.toNNReal_coe]
    · rw [min_eq_right (not_le.1 hζ).le]
      exact (he.2.2.1 r (not_le.1 hζ).le).symm
  · exact ite_eq_left_of_eq_true _ _ (eq_true hs)

/-- Equal stopped records determine both the driver on the stopped interval and
the hull at its endpoint, even on samples with a finite lifetime. -/
theorem driver_hull_eq_of_recOf_eq {e e' : (ℝ≥0 → ℝ) × ℝ≥0∞}
    (he : IsRegularDriver e) (he' : IsRegularDriver e') {s : ℝ≥0}
    (hrec : recOf (s : ℝ≥0∞) e = recOf (s : ℝ≥0∞) e') :
    EqOn (fun r : ℝ => e.1 r.toNNReal) (fun r : ℝ => e'.1 r.toNNReal)
        (Icc 0 (s : ℝ)) ∧
      QuantumZipper.fwdHull (fun r : ℝ => e.1 r.toNNReal) s =
        QuantumZipper.fwdHull (fun r : ℝ => e'.1 r.toNNReal) s := by
  have hc := canonDrv_eq_of_readRec_eq he he' hrec
  have heq : EqOn (fun r : ℝ => e.1 r.toNNReal)
      (fun r : ℝ => e'.1 r.toNNReal) (Icc 0 (s : ℝ)) := by
    intro r hr
    have hrs : r.toNNReal ≤ s := Real.toNNReal_le_iff_le_coe.2 hr.2
    have hr' := congrArg (fun d : (ℝ≥0 → ℝ) × ℝ≥0∞ => d.1 r.toNNReal) hc
    rwa [canonDrv_fst_eq_of_le he hrs, canonDrv_fst_eq_of_le he' hrs] at hr'
  refine ⟨heq, ?_⟩
  have hflag : e.2 ≤ (s : ℝ≥0∞) ↔ e'.2 ≤ (s : ℝ≥0∞) := by
    have hf := congrArg (fun d : RecData => d.2.2) hrec
    exact decide_eq_decide.1 hf
  by_cases hs : e.2 ≤ (s : ℝ≥0∞)
  · rw [canonDrv_eq_self_of_lifetime_le he hs,
      canonDrv_eq_self_of_lifetime_le he' (hflag.1 hs)] at hc
    rw [hc]
  · have hs' : ¬ e'.2 ≤ (s : ℝ≥0∞) := mt hflag.2 hs
    obtain ⟨v, hsv, hv⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1
      (lt_min (not_le.1 hs) (not_le.1 hs'))
    have hcont : ∀ d : (ℝ≥0 → ℝ) × ℝ≥0∞, IsRegularDriver d →
        (v : ℝ≥0∞) < d.2 →
        ContinuousOn (fun r : ℝ => d.1 r.toNNReal) (Icc 0 (v : ℝ)) := by
      intro d hd hvd
      apply hd.1.comp continuous_real_toNNReal.continuousOn
      intro r hr
      exact lt_of_le_of_lt
        (ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hr.2)) hvd
    exact LocalExt.fwdHull_congr_of_continuousOn
      (hcont e he (lt_of_lt_of_le hv (min_le_left _ _)))
      (hcont e' he' (lt_of_lt_of_le hv (min_le_right _ _)))
      s.coe_nonneg (by exact_mod_cast hsv) heq

end InteractingSLE.Theorem14.GW2TipSystem
