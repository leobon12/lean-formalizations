/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootH29Causal

/-!
# Exact causal access to shorter next-piece records

Packet PROVE-T14-GW2ROOT2. A longer retained record determines every
shorter record, including the death flag, on all regular drivers. Apply
this to the canonical families and to different candidate programs.
Any Borel reader of the shorter record is therefore observable without
using a regular-source event or a noncausal continuous path decoder.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.RootH29

open GW2Schedule GW2Tip Exist Staged StagedLaw Restart LQGMetric RootC24

/-- Canonical freezing at a later own time preserves the whole earlier
record, including whether death has already occurred. -/
theorem recOf_canonDrv_of_le {e : (ℝ≥0 → ℝ) × ℝ≥0∞} (he : IsRegularDriver e)
    {t s : ℝ≥0} (hts : t ≤ s) :
    recOf (t : ℝ≥0∞) (canonDrv (s : ℝ≥0∞) e) = recOf (t : ℝ≥0∞) e := by
  have hts' : (t : ℝ≥0∞) ≤ s := ENNReal.coe_le_coe.mpr hts
  have hmin : min (t : ℝ≥0∞) (canonDrv (s : ℝ≥0∞) e).2 = min (t : ℝ≥0∞) e.2 := by
    by_cases hs : e.2 ≤ (s : ℝ≥0∞)
    · simp only [canonDrv, hs, ↓reduceIte]
    · simp only [canonDrv, hs, ↓reduceIte, min_top_right,
        min_eq_left (hts'.trans (not_le.mp hs).le)]
  have hflag : (canonDrv (s : ℝ≥0∞) e).2 ≤ (t : ℝ≥0∞) ↔ e.2 ≤ t := by
    by_cases hs : e.2 ≤ (s : ℝ≥0∞)
    · simp only [canonDrv, hs, ↓reduceIte]
    · simp only [canonDrv, hs, ↓reduceIte]
      exact iff_of_false (not_le.mpr ENNReal.coe_lt_top)
        (not_le.mpr (hts'.trans_lt (not_le.mp hs)))
  apply Prod.ext
  · funext q
    change (canonDrv (s : ℝ≥0∞) e).1
      (min (((q : ℝ).toNNReal : ℝ≥0∞))
        (min (t : ℝ≥0∞) (canonDrv (s : ℝ≥0∞) e).2)).toNNReal = _
    rw [hmin]
    apply canonDrv_fst_eq_of_le he
    apply ENNReal.coe_le_coe.mp
    rw [ENNReal.coe_toNNReal (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_left _ _))]
    exact (min_le_right _ _).trans ((min_le_left _ _).trans hts')
  · change (min (t : ℝ≥0∞) (canonDrv (s : ℝ≥0∞) e).2,
      decide ((canonDrv (s : ℝ≥0∞) e).2 ≤ (t : ℝ≥0∞))) = _
    exact Prod.ext hmin (decide_eq_decide.mpr hflag)

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- A canonical piece's shorter record is measurable in the actual
retained stage. This includes exceptional samples and death at the query. -/
theorem measurable_stageSigma_shorter_record (c : SourceData Ω) (spec : ExplSpec)
    (n : ℕ) (j : Fin n) (t : ℝ≥0) (ht : (t : ℝ≥0∞) ≤ specDelta spec j) :
    Measurable[stageSigma c.hκ c.h12p c.βA c.c₀ c.h c.s c.W c.ζ spec n]
      (fun ω => recOf (t : ℝ≥0∞) (canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h spec j ω)) := by
  have hE := measurable_canonFam c.hκ c.h12p c.βA c.c₀
    (specAngle spec) (specDelta spec) spec.1 c.hβA.1 c.hh.1 j
  have hreg : ∀ ω, IsRegularDriver
      (canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h spec j ω) := fun ω =>
    isRegularDriver_canonFam c.hκ c.h12p c.βA c.c₀
      (specAngle spec) (specDelta spec) spec.1 c.h j ω
  have hR := measurable_recOf hE hreg (t : ℝ≥0∞)
  have hstage : Measurable (stageMap c.hκ c.h12p c.βA c.c₀ c.h c.s c.W c.ζ spec n) :=
    Measurable.of_comap_le (stageSigma_le c.hβA.1 c.hh.1 c.hcf c.s spec n)
  apply measurable_comap_of_saturated hstage hR
  intro ω ω' hsame
  have hr := congrFun (congrArg Prod.snd hsame) j
  change recOf (specDelta spec j) (canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h spec j ω) =
    recOf (specDelta spec j) (canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h spec j ω') at hr
  let s := (specDelta spec j).toNNReal
  have hs : (s : ℝ≥0∞) = specDelta spec j := ENNReal.coe_toNNReal (specDelta_ne_top spec j)
  have hts : t ≤ s := ENNReal.coe_le_coe.mp (hs.symm ▸ ht)
  rw [← hs] at hr
  have hc := canonDrv_eq_of_readRec_eq (hreg ω) (hreg ω') hr
  change recOf (t : ℝ≥0∞) (canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h spec j ω) =
    recOf (t : ℝ≥0∞) (canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h spec j ω')
  rw [← recOf_canonDrv_of_le (hreg ω) hts, hc,
    recOf_canonDrv_of_le (hreg ω') hts]

/-- A shorter next-piece record of either candidate program is known
from the longer candidate's retained stage, on every sample. -/
theorem measurable_next_record_other_cutoff (c : SourceData Ω)
    (x θ : ℝ) (l : List (ℝ × ℝ≥0)) (q q' t : ℝ≥0)
    (ht : (t : ℝ≥0∞) ≤ specDelta (schedSpec x (l ++ [(θ, q')])) l.length) :
    Measurable[stageSigma c.hκ c.h12p c.βA c.c₀ c.h c.s c.W c.ζ
      (schedSpec x (l ++ [(θ, q')])) (l.length + 1)] (fun ω =>
        recOf (t : ℝ≥0∞) (canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h
          (schedSpec x (l ++ [(θ, q)])) l.length ω)) := by
  have hm := measurable_stageSigma_shorter_record c
    (schedSpec x (l ++ [(θ, q')])) (l.length + 1) ⟨l.length, Nat.lt_succ_self _⟩ t ht
  have heq : (fun ω => canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h
      (schedSpec x (l ++ [(θ, q)])) l.length ω) =
      (fun ω => canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h
        (schedSpec x (l ++ [(θ, q')])) l.length ω) :=
    funext (canonical_next_independent_time c.hκ c.h12p c.βA c.c₀ c.h x θ l q q')
  simp_rw [congrFun heq]
  exact hm

end InteractingSLE.Theorem14.GW2TipSystem.RootH29
