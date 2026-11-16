/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.RealContact.TermClockPath
import InteractingSLE.Spec.Supplement.AStopProcClock

/-!
# The chart path of an explorer against a completed path (builder frame)

Packet PROVE-RC-TERM, second run (ruling R124). For a generating-trace explorer `β` from `0` and a completed retained
path with entry data, in the builder frame:

* `retSet ξ T d`: the translated completed path; `physStop ξ T d β ζ = Supp7.contStop β ζ 0 (retSet ξ T d)`: the
  physical stop (first positive-time contact with the path, or the lifetime) — its `contSet` is the active set of the
  path statement;
* `chartPath V ξ T d β ζ = Supp7.contPath entryDom entryChart.1 β 0 physStop`: the chart path in physical time;
* `IsPathSample`: the pathwise hypotheses (entry data, positive tip, a generating trace, injective in `ℍ̄`, W5 on
  strict prefixes, a positive stop);
* `IsPathSample.chartPath_eq`: `chartPath r = entryExt (β (stopT r))`, the extended chart at the explorer stopped at
  the physical stop; `continuous_chartPath`, `chartPath_zero`, `entryInv_chartPath`, `injOn_chartPath`;
* **`IsPathSample.criterionA`** (from the proper lift of `exists_relChain_config`, accessible by
  `Supp9D.mem_closure_of_isProperCompletion`, and closedness at the stop), **`IsPathSample.interior_real_eq_empty`**;
* **`IsPathSample.exists_window`**: on every window `[0, U]`, `U ≤ physStop`, `chartClock chartPath` is a clock and a
  continuous driver from `0` has the filled chart path as hulls.

Deterministic; R48-neutral.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex Bornology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull logDerivFwd IsForwardSol)

namespace InteractingSLE.RealContact

namespace Term

open Supp9B HalfPlaneSep Theorem14 Theorem14.SB Theorem14.SB.FinRel Restart
open Supp7 (contStop contSet contPath)

variable {V : ℝ → ℝ} {T : ℝ≥0} {ξ : ℝ → ℂ} {p d : ℝ} {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {β : ℝ≥0 → ℂ}

/-- The translated completed path, as a set. -/
def retSet (ξ : ℝ → ℂ) (T : ℝ≥0) (d : ℝ) : Set ℂ := (fun t : ℝ≥0 => ξ (t : ℝ) + (d : ℂ)) '' Icc 0 T

theorem retSet_eq (hT : (0 : ℝ) < T) (ξ : ℝ → ℂ) (d : ℝ) : retSet ξ T d = entryPath ξ (T : ℝ) d '' Icc 0 1 :=
  (image_entryPath_eq hT ξ d).symm

/-- **The physical stop** of the explorer: its first positive-time contact with the completed path, or its
lifetime. -/
def physStop (ξ : ℝ → ℂ) (T : ℝ≥0) (d : ℝ) (β : ℝ≥0 → ℂ) (ζ : ℝ≥0∞) : ℝ≥0∞ := contStop β ζ 0 (retSet ξ T d)

/-- **The chart path** of the explorer in physical time: the forward chart limit before the physical stop, its left
limit afterwards. -/
def chartPath (V : ℝ → ℝ) (ξ : ℝ → ℂ) (T : ℝ≥0) (d : ℝ) (β : ℝ≥0 → ℂ) (ζ : ℝ≥0∞) : ℝ≥0 → ℂ :=
  contPath (entryDom ξ (T : ℝ) d) (entryChart V (T : ℝ) d).1 β 0 (physStop ξ T d β ζ)

/-- The explorer's time stopped at the physical stop. -/
def stopT (ξ : ℝ → ℂ) (T : ℝ≥0) (d : ℝ) (β : ℝ≥0 → ℂ) (ζ : ℝ≥0∞) (r : ℝ≥0) : ℝ≥0 :=
  (min (r : ℝ≥0∞) (physStop ξ T d β ζ)).toNNReal

/-- **The pathwise hypotheses of a sample** in the builder frame. -/
structure IsPathSample (V : ℝ → ℝ) (T : ℝ≥0) (ξ : ℝ → ℂ) (p d : ℝ) (w : ℝ≥0 → ℝ) (ζ : ℝ≥0∞) (β : ℝ≥0 → ℂ) :
    Prop where
  entry : IsEntryData V (T : ℝ) ξ p d
  tipPos : 0 < p
  ne : ∀ s : ℝ, 0 < s → s ≤ T → ξ s + (d : ℂ) ≠ 0
  gen : IsGeneratingTrace w ζ β
  drvCont : ContinuousOn w {s : ℝ≥0 | (s : ℝ≥0∞) < ζ}
  drvZero : w 0 = 0
  inj : InjOn β {t : ℝ≥0 | (t : ℝ≥0∞) ≤ ζ}
  hbar : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ → 0 ≤ (β t).im
  order : ∀ a : ℝ≥0, (a : ℝ≥0∞) < ζ → ∀ c : ℝ≥0, c < T →
    HasOrderedProperCompletions (fun t : ℝ≥0 => ξ (t : ℝ) + (d : ℂ)) c β a
  stopPos : 0 < physStop ξ T d β ζ

theorem physStop_le (ξ : ℝ → ℂ) (T : ℝ≥0) (d : ℝ) (β : ℝ≥0 → ℂ) (ζ : ℝ≥0∞) : physStop ξ T d β ζ ≤ ζ :=
  Supp7.contStop_le

theorem coe_stopT_le (ξ : ℝ → ℂ) (T : ℝ≥0) (d : ℝ) (β : ℝ≥0 → ℂ) (ζ : ℝ≥0∞) (r : ℝ≥0) :
    ((stopT ξ T d β ζ r : ℝ≥0) : ℝ≥0∞) ≤ physStop ξ T d β ζ := by
  unfold stopT
  rw [ENNReal.coe_toNNReal (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_left _ _))]
  exact min_le_right _ _

theorem stopT_of_le {r : ℝ≥0} (hr : (r : ℝ≥0∞) ≤ physStop ξ T d β ζ) : stopT ξ T d β ζ r = r := by
  unfold stopT
  rw [min_eq_left hr, ENNReal.toNNReal_coe]

theorem stopT_of_ge {r : ℝ≥0} (hr : physStop ξ T d β ζ ≤ (r : ℝ≥0∞)) :
    stopT ξ T d β ζ r = (physStop ξ T d β ζ).toNNReal := by
  unfold stopT
  rw [min_eq_right hr]

theorem continuous_stopT (ξ : ℝ → ℂ) (T : ℝ≥0) (d : ℝ) (β : ℝ≥0 → ℂ) (ζ : ℝ≥0∞) :
    Continuous (stopT ξ T d β ζ) := by
  have h1 : Continuous fun r : ℝ≥0 => min (r : ℝ≥0∞) (physStop ξ T d β ζ) :=
    ENNReal.continuous_coe.min continuous_const
  exact ENNReal.continuousOn_toNNReal.comp_continuous h1 fun r =>
    ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_left _ _)

theorem off_of_lt {t : ℝ≥0} (ht0 : 0 < t) (ht : (t : ℝ≥0∞) < physStop ξ T d β ζ) : β t ∉ retSet ξ T d :=
  Supp7.notMem_of_lt_contStop ht0 ht

theorem lt_life_of_lt {t : ℝ≥0} (ht : (t : ℝ≥0∞) < physStop ξ T d β ζ) : (t : ℝ≥0∞) < ζ :=
  lt_of_lt_of_le ht (physStop_le ξ T d β ζ)

namespace IsPathSample

variable (h : IsPathSample V T ξ p d w ζ β)
include h

theorem tpos : (0 : ℝ) < T := h.entry.tip.pos

theorem isRetPath : IsRetPath (fun t : ℝ≥0 => ξ (t : ℝ) + (d : ℂ)) T d (p + d) :=
  h.entry.isRetPath h.tipPos h.ne

theorem continuousOn_Icc {a : ℝ≥0} (ha : (a : ℝ≥0∞) ≤ ζ) : ContinuousOn β (Icc 0 a) :=
  h.gen.2.1.mono fun t ht => show (t : ℝ≥0∞) ≤ ζ from (ENNReal.coe_le_coe.2 ht.2).trans ha

theorem isExpPrefix {a : ℝ≥0} (ha : (a : ℝ≥0∞) < physStop ξ T d β ζ) :
    IsExpPrefix β a (fun t : ℝ≥0 => ξ (t : ℝ) + (d : ℂ)) T :=
  ⟨h.continuousOn_Icc (lt_life_of_lt ha).le,
    fun t ht => h.hbar t ((ENNReal.coe_le_coe.2 ht).trans (lt_life_of_lt ha).le), h.gen.1,
    fun _ ht ht0 => off_of_lt ht0 (lt_of_le_of_lt (ENNReal.coe_le_coe.2 ht) ha)⟩

/-- Before the physical stop the explorer is free for the completed path. -/
theorem isFreeAt {t : ℝ≥0} (ht0 : 0 < t) (ht : (t : ℝ≥0∞) < physStop ξ T d β ζ) :
    IsFreeAt (entryPath ξ (T : ℝ) d '' Icc 0 1) (β t) := by
  rw [← retSet_eq h.tpos]
  exact isFreeAt_explorer h.isRetPath (h.isExpPrefix ht) (h.order t (lt_life_of_lt ht)) le_rfl ht0

theorem ne_seed {t : ℝ≥0} (ht0 : 0 < t) (ht : (t : ℝ≥0∞) < physStop ξ T d β ζ) : β t ≠ (d : ℂ) := fun he =>
  off_of_lt ht0 ht ⟨0, ⟨le_rfl, zero_le⟩, by
    show ξ ((0 : ℝ≥0) : ℝ) + (d : ℂ) = β t
    rw [NNReal.coe_zero, h.entry.tip.trace.1, zero_add, he]⟩

/-- Up to the physical stop the explorer stays in the closure of the chart domain. -/
theorem mem_closure {t : ℝ≥0} (ht : (t : ℝ≥0∞) ≤ physStop ξ T d β ζ) :
    β t ∈ closure (entryDom ξ (T : ℝ) d) := by
  have hlt : ∀ s : ℝ≥0, (s : ℝ≥0∞) < physStop ξ T d β ζ → β s ∈ closure (entryDom ξ (T : ℝ) d) := by
    intro s hs
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ s) with hs0 | hs0
    · rw [← hs0, h.gen.1]
      exact h.entry.zero_mem_closure
    · exact mem_closure_entryDom_of_isFreeAt (h.hbar s (lt_life_of_lt hs).le) (h.isFreeAt hs0 hs)
  rcases ht.lt_or_eq with hlt' | heq
  · exact hlt t hlt'
  · -- the stop itself: a limit from the left
    have ht0 : 0 < t := by
      have := h.stopPos
      rw [← heq] at this
      exact_mod_cast this
    have hcw : ContinuousWithinAt β (Iic t) t :=
      (h.gen.2.1 t (ht.trans (physStop_le ξ T d β ζ))).mono fun s (hs : s ≤ t) =>
        show (s : ℝ≥0∞) ≤ ζ from (ENNReal.coe_le_coe.2 hs).trans (ht.trans (physStop_le ξ T d β ζ))
    have hlim : Tendsto β (𝓝[<] t) (𝓝 (β t)) := hcw.tendsto.mono_left (nhdsWithin_mono _ Iio_subset_Iic_self)
    have : (𝓝[<] t).NeBot := Supp7.neBot_nhdsLT ht0
    refine isClosed_closure.mem_of_tendsto hlim (eventually_nhdsWithin_of_forall fun s (hs : s < t) => ?_)
    exact hlt s (heq ▸ ENNReal.coe_lt_coe.2 hs)

theorem chartPath_of_lt {r : ℝ≥0} (hr : (r : ℝ≥0∞) < physStop ξ T d β ζ) :
    chartPath V ξ T d β ζ r = entryExt V ξ (T : ℝ) d (β r) := by
  have hz := h.mem_closure hr.le
  have : (𝓝[entryDom ξ (T : ℝ) d] (β r)).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hz
  unfold chartPath
  rw [Supp7.contPath_of_lt hr, zero_add]
  exact (h.entry.tendsto_entryExt hz).limUnder_eq

theorem tendsto_entryExt_stop {c : ℝ≥0} (hc : (c : ℝ≥0∞) = physStop ξ T d β ζ) :
    Tendsto (fun s => entryExt V ξ (T : ℝ) d (β s)) (𝓝[<] c) (𝓝 (entryExt V ξ (T : ℝ) d (β c))) := by
  have hcw : ContinuousWithinAt β (Iic c) c :=
    (h.gen.2.1 c (hc.le.trans (physStop_le ξ T d β ζ))).mono fun s (hs : s ≤ c) =>
      show (s : ℝ≥0∞) ≤ ζ from (ENNReal.coe_le_coe.2 hs).trans (hc.le.trans (physStop_le ξ T d β ζ))
  have hlim : Tendsto β (𝓝[<] c) (𝓝[closure (entryDom ξ (T : ℝ) d)] (β c)) :=
    tendsto_nhdsWithin_iff.2 ⟨hcw.tendsto.mono_left (nhdsWithin_mono _ Iio_subset_Iic_self),
      eventually_nhdsWithin_of_forall fun s (hs : s < c) =>
        h.mem_closure ((ENNReal.coe_le_coe.2 hs.le).trans hc.le)⟩
  exact (h.entry.continuousOn_entryExt (β c) (h.mem_closure hc.le)).tendsto.comp hlim

theorem chartPath_of_ge {r : ℝ≥0} (hr : physStop ξ T d β ζ ≤ (r : ℝ≥0∞)) :
    chartPath V ξ T d β ζ r = entryExt V ξ (T : ℝ) d (β (physStop ξ T d β ζ).toNNReal) := by
  have hfin : physStop ξ T d β ζ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hr
  set c := (physStop ξ T d β ζ).toNNReal with hcdef
  have hc : (c : ℝ≥0∞) = physStop ξ T d β ζ := ENNReal.coe_toNNReal hfin
  have hc0 : 0 < c := ENNReal.toNNReal_pos h.stopPos.ne' hfin
  have : (𝓝[<] c).NeBot := Supp7.neBot_nhdsLT hc0
  unfold chartPath
  rw [Supp7.contPath_of_le hr]
  refine Tendsto.limUnder_eq ((h.tendsto_entryExt_stop hc).congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs' : (s : ℝ≥0∞) < physStop ξ T d β ζ := hc ▸ ENNReal.coe_lt_coe.2 hs
  have := h.chartPath_of_lt (V := V) hs'
  unfold chartPath at this
  rw [Supp7.contPath_of_lt hs'] at this
  exact this.symm

/-- **The chart path is the extended chart at the explorer stopped at the physical stop.** -/
theorem chartPath_eq (r : ℝ≥0) :
    chartPath V ξ T d β ζ r = entryExt V ξ (T : ℝ) d (β (stopT ξ T d β ζ r)) := by
  rcases lt_or_ge (r : ℝ≥0∞) (physStop ξ T d β ζ) with hr | hr
  · rw [h.chartPath_of_lt hr, stopT_of_le hr.le]
  · rw [h.chartPath_of_ge hr, stopT_of_ge hr]

theorem chartPath_of_le {r : ℝ≥0} (hr : (r : ℝ≥0∞) ≤ physStop ξ T d β ζ) :
    chartPath V ξ T d β ζ r = entryExt V ξ (T : ℝ) d (β r) := by
  rw [h.chartPath_eq, stopT_of_le hr]

theorem continuous_chartPath : Continuous (chartPath V ξ T d β ζ) := by
  have he : chartPath V ξ T d β ζ = fun r => entryExt V ξ (T : ℝ) d (β (stopT ξ T d β ζ r)) :=
    funext h.chartPath_eq
  rw [he]
  have hβ : Continuous fun r => β (stopT ξ T d β ζ r) :=
    h.gen.2.1.comp_continuous (continuous_stopT ξ T d β ζ) fun r =>
      show ((stopT ξ T d β ζ r : ℝ≥0) : ℝ≥0∞) ≤ ζ from
        (coe_stopT_le ξ T d β ζ r).trans (physStop_le ξ T d β ζ)
  exact h.entry.continuousOn_entryExt.comp_continuous hβ fun r => h.mem_closure (coe_stopT_le ξ T d β ζ r)

theorem chartPath_zero : chartPath V ξ T d β ζ 0 = 0 := by
  rw [h.chartPath_of_le (by simp), h.gen.1, h.entry.entryExt_zero]

theorem chartPath_mem_Hbar (r : ℝ≥0) : 0 ≤ (chartPath V ξ T d β ζ r).im := by
  rw [h.chartPath_eq]
  exact h.entry.entryExt_mem_Hbar (h.mem_closure (coe_stopT_le ξ T d β ζ r))

/-- The boundary inverse of the entry chart sends the chart path back to the stopped explorer. -/
theorem entryInv_chartPath (r : ℝ≥0) :
    entryInv V (T : ℝ) d (chartPath V ξ T d β ζ r) = β (stopT ξ T d β ζ r) := by
  rw [h.chartPath_eq]
  exact h.entry.entryInv_entryExt (h.mem_closure (coe_stopT_le ξ T d β ζ r))

theorem injOn_chartPath : InjOn (chartPath V ξ T d β ζ) {r : ℝ≥0 | (r : ℝ≥0∞) ≤ physStop ξ T d β ζ} := by
  intro a ha b hb hab
  have h1 := h.entryInv_chartPath (V := V) a
  have h2 := h.entryInv_chartPath (V := V) b
  rw [stopT_of_le ha] at h1
  rw [stopT_of_le hb] at h2
  exact h.inj (ha.trans (physStop_le ξ T d β ζ)) (hb.trans (physStop_le ξ T d β ζ))
    (h1.symm.trans ((congrArg _ hab).trans h2))

/-- Before the physical stop and at positive times the chart path is the forward chart of the explorer. -/
theorem chartPath_eq_fwd {r : ℝ≥0} (hr0 : 0 < r) (hr : (r : ℝ≥0∞) < physStop ξ T d β ζ) :
    chartPath V ξ T d β ζ r = (entryChart V (T : ℝ) d).1 (β r) := by
  rw [h.chartPath_of_lt hr]
  exact h.entry.entryExt_of_isFreeAt (h.hbar r (lt_life_of_lt hr).le) (h.ne_seed hr0 hr) (h.isFreeAt hr0 hr)

/-! ### Criterion (a) -/

/-- Criterion (a) strictly before the physical stop, from the proper lift. -/
theorem criterionA_lt {t r : ℝ≥0} (htr : t < r) (hr : (r : ℝ≥0∞) < physStop ξ T d β ζ) :
    chartPath V ξ T d β ζ r ∈ closure (H \ fillH (chartPath V ξ T d β ζ '' Icc 0 t)) := by
  obtain ⟨a, hra, haL⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hr
  have hra' : r < a := ENNReal.coe_lt_coe.1 hra
  have ha0 : (0 : ℝ) < a := NNReal.coe_pos.2 (lt_of_le_of_lt zero_le hra')
  have haζ : (a : ℝ≥0∞) < ζ := lt_life_of_lt haL
  have hP := h.isExpPrefix haL
  obtain ⟨β', γ, Wr, ηr, -, hγ, hγ0, hγeq, -, -, -⟩ := exists_relChain_config (V := V) (ξ := ξ) (p := p)
    (d := d) (nL := 0) (nR := 0) (nL' := 0) (nR' := 0) (ρL := fun i => i.elim0) (ρR := fun i => i.elim0)
    (xL := fun i => i.elim0) (xR := fun i => i.elim0) (ρL' := fun i => i.elim0) (ρR' := fun i => i.elim0)
    (xL' := fun i => i.elim0) (xR' := fun i => i.elim0) 1 0 (fun i => i.elim0) (fun i => i.elim0)
    (fun i => i.elim0) (fun i => i.elim0) h.entry h.tipPos h.ne h.gen h.drvCont h.drvZero haζ
    (h.inj.mono fun s hs => show (s : ℝ≥0∞) ≤ ζ from (ENNReal.coe_le_coe.2 hs.2).trans haζ.le)
    hP.hbar hP.off (h.order a haζ) (S₀ := 0) le_rfl ha0
  -- the chart path is the lift on `[0, a]`
  have heq : ∀ s ≤ a, chartPath V ξ T d β ζ s = γ s := by
    intro s hs
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ s) with hs0 | hs0
    · rw [← hs0, h.chartPath_zero, hγ0]
    · rw [hγeq s hs0 hs, h.chartPath_eq_fwd hs0 (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hs) haL)]
  have hcomp : IsProperCompletion γ r γ := ⟨hγ.1, hγ.2.1, hγ.2.2.1, hγ.2.2.2, fun _ _ => rfl⟩
  have hmem := Supp9D.mem_closure_of_isProperCompletion hcomp
  have hanti := closure_mono (Supp9D.H_diff_fillH_anti (image_mono (Icc_subset_Icc_right htr.le))
    (F := γ '' Icc 0 t) (G := γ '' Icc 0 r)) hmem
  have himg : chartPath V ξ T d β ζ '' Icc 0 t = γ '' Icc 0 t :=
    image_congr fun s hs => heq s (hs.2.trans (htr.le.trans hra'.le))
  rw [himg, heq r hra'.le]
  exact hanti

/-- **Criterion (a)** up to the physical stop. -/
theorem criterionA {t r : ℝ≥0} (ht0 : 0 < t) (htr : t < r) (hr : (r : ℝ≥0∞) ≤ physStop ξ T d β ζ) :
    chartPath V ξ T d β ζ r ∈ closure (H \ fillH (chartPath V ξ T d β ζ '' Icc 0 t)) := by
  rcases hr.lt_or_eq with hlt | heq
  · exact h.criterionA_lt htr hlt
  · have hr0 : 0 < r := lt_trans ht0 htr
    have : (𝓝[<] r).NeBot := Supp7.neBot_nhdsLT hr0
    have hlim : Tendsto (chartPath V ξ T d β ζ) (𝓝[<] r) (𝓝 (chartPath V ξ T d β ζ r)) :=
      (h.continuous_chartPath.tendsto r).mono_left nhdsWithin_le_nhds
    refine isClosed_closure.mem_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsLT htr] with s hs
    exact h.criterionA_lt hs.1 (heq ▸ ENNReal.coe_lt_coe.2 hs.2)

/-! ### Criterion (b) -/

/-- At a positive time before the physical stop, a real chart point comes from a real point of the explorer. -/
theorem im_eq_zero_of_chartPath {r : ℝ≥0} (hr0 : 0 < r) (hr : (r : ℝ≥0∞) < physStop ξ T d β ζ)
    (him : (chartPath V ξ T d β ζ r).im = 0) : (β r).im = 0 := by
  have hinv := h.entryInv_chartPath (V := V) r
  rw [stopT_of_le hr.le] at hinv
  have hreal : chartPath V ξ T d β ζ r = (((chartPath V ξ T d β ζ r).re : ℝ) : ℂ) :=
    Complex.ext (by simp) (by simp [him])
  have hnotD : β r ∉ entryDom ξ (T : ℝ) d := by
    rw [← hinv, hreal]
    exact h.entry.entryInv_real_notMem _
  have hfr : β r ∈ frontier (entryDom ξ (T : ℝ) d) := by
    rw [h.entry.isDomainChart'.isOpen.frontier_eq]
    exact ⟨h.mem_closure hr.le, hnotD⟩
  have hsub := frontier_H_diff_fillH_subset h.entry.isCompact_path.isBounded hfr
  rw [h.entry.isCompact_path.isClosed.closure_eq] at hsub
  rcases hsub with h0 | hK
  · exact h0
  · exact absurd (by rw [retSet_eq h.tpos]; exact hK) (off_of_lt hr0 hr)

/-- **The chart path spends no open time interval on the real line** before the physical stop. -/
theorem interior_real_eq_empty {U : ℝ≥0} (hU : (U : ℝ≥0∞) ≤ physStop ξ T d β ζ) :
    interior {u ∈ Ioo (0 : ℝ) U | (chartPath V ξ T d β ζ u.toNNReal).im = 0} = ∅ := by
  by_contra hne
  obtain ⟨u₀, hu₀⟩ := nonempty_iff_ne_empty.2 hne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_interior u₀ hu₀
  have hu₀I := (interior_subset hu₀).1
  -- a horizon strictly between `u₀` and `U`
  set t₂ : ℝ := (u₀ + min (u₀ + ε) U) / 2 with ht₂
  have hmin : u₀ < min (u₀ + ε) U := lt_min (by linarith) hu₀I.2
  have ht₂u : u₀ < t₂ := by rw [ht₂]; linarith
  have ht₂U : t₂ < U := by rw [ht₂]; linarith [min_le_right (u₀ + ε) (U : ℝ)]
  have ht₂ε : t₂ < u₀ + ε := by rw [ht₂]; linarith [min_le_left (u₀ + ε) (U : ℝ)]
  have ht₂0 : 0 < t₂ := hu₀I.1.trans ht₂u
  have ht₂ζ : ENNReal.ofReal t₂ < ζ := by
    have h1 : ENNReal.ofReal t₂ < (U : ℝ≥0∞) := by
      rw [← ENNReal.ofReal_coe_nnreal]
      exact (ENNReal.ofReal_lt_ofReal_iff (lt_trans ht₂0 ht₂U)).2 ht₂U
    exact lt_of_lt_of_le h1 (hU.trans (physStop_le ξ T d β ζ))
  have hLT := h.gen.isLoewnerTraceLT ht₂ζ
  have hwc : ContinuousOn w (Iic t₂.toNNReal) := h.drvCont.mono fun s hs =>
    show (s : ℝ≥0∞) < ζ from lt_of_le_of_lt (ENNReal.coe_le_coe.2 hs) (by rwa [ENNReal.ofReal] at ht₂ζ)
  have hI := interior_real_times_eq_empty hLT (continuous_frozenDrive hwc)
    (by rw [frozenDrive_zero ht₂0.le, h.drvZero])
  -- a neighbourhood of `u₀` consists of real times of the explorer before the horizon
  have hsub : Ioo (max (u₀ - ε) 0) t₂ ⊆ {r ∈ Ioo (0 : ℝ) t₂ | (β r.toNNReal).im = 0} := by
    intro u hu
    have hu0 : 0 < u := lt_of_le_of_lt (le_max_right _ _) hu.1
    have hulow : u₀ - ε < u := lt_of_le_of_lt (le_max_left _ _) hu.1
    have humem : u ∈ {u ∈ Ioo (0 : ℝ) U | (chartPath V ξ T d β ζ u.toNNReal).im = 0} :=
      interior_subset (hball (by
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]
        constructor <;> linarith [hu.2]))
    refine ⟨⟨hu0, hu.2⟩, ?_⟩
    have hlt : ((u.toNNReal : ℝ≥0) : ℝ≥0∞) < physStop ξ T d β ζ := by
      refine lt_of_lt_of_le (ENNReal.coe_lt_coe.2 ?_) hU
      exact (Real.toNNReal_lt_iff_lt_coe hu0.le).2 humem.1.2
    exact h.im_eq_zero_of_chartPath (Real.toNNReal_pos.2 hu0) hlt humem.2
  have hopen : Ioo (max (u₀ - ε) 0) t₂ ⊆ interior {r ∈ Ioo (0 : ℝ) t₂ | (β r.toNNReal).im = 0} :=
    interior_maximal hsub isOpen_Ioo
  rw [hI] at hopen
  exact hopen ⟨max_lt (by linarith) hu₀I.1, ht₂u⟩

/-! ### Windows -/

/-- **On every window before or at the physical stop, the relative capacity is a clock and a continuous driver
generates the filled chart path.** -/
theorem exists_window {U : ℝ≥0} (hU0 : 0 < U) (hU : (U : ℝ≥0∞) ≤ physStop ξ T d β ζ) :
    IsClockOn (chartClock (chartPath V ξ T d β ζ)) U ∧ ∃ W : ℝ → ℝ, Continuous W ∧ W 0 = 0 ∧ ∀ t : ℝ≥0, t ≤ U →
      0 ≤ chartClock (chartPath V ξ T d β ζ) t ∧
        fwdHull W (chartClock (chartPath V ξ T d β ζ) t) = fillH (chartPath V ξ T d β ζ '' Icc 0 t) := by
  refine isClockOn_chartClock_of_criteria hU0 h.continuous_chartPath.continuousOn
    (h.injOn_chartPath.mono fun r (hr : r ≤ U) => show (r : ℝ≥0∞) ≤ physStop ξ T d β ζ from
      (ENNReal.coe_le_coe.2 hr).trans hU) h.chartPath_zero (fun r _ => h.chartPath_mem_Hbar r)
    (fun t r ht0 htr hr => h.criterionA ht0 htr ((ENNReal.coe_le_coe.2 hr).trans hU))
    (h.interior_real_eq_empty hU)

end IsPathSample

end Term

end InteractingSLE.RealContact
