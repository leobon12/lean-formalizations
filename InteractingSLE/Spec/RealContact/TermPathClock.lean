/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.RealContact.TermPathGood
import InteractingSLE.Spec.Restart.RetAux79Path
import InteractingSLE.Spec.Sec7.ReverseArcLift

/-!
# The chart path of an explorer against a completed path is a good sample (builder frame)

Packet PROVE-RC-TERM, second run (ruling R124). For a sample with the pathwise hypotheses `Term.IsPathSample`:

* `IsPathSample.isDomChart`: the entry chart with its boundary inverse is a chart of the unbounded domain in the
  sense of `Supp7.IsDomChart`;
* **`IsPathSample.chartClock_ge`**: additivity of capacity, `2t − hcap(fill path) ≤ 2 chartClock chartPath t` before
  the lifetime (`Supp7.IsDomChart.hcapSet_fillH_eq_add`);
* `IsPathSample.isClockOn`, `monotone_chartClock`, `continuous_chartClock`: the relative capacity is a clock on the
  physical stop, monotone and continuous on all times;
* **`IsPathSample.isAGood`**: the chart path with the physical stop is a good sample of the abstract A-stopped
  processes (`RLC.AStopProc.IsAGood`): one continuous driver from the window drivers
  (`Restart.RetAux79.exists_driver_of_windows`) generates it in capacity time
  (`Restart.RetAux79.isGeneratingTrace_invClock`).

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

open Theorem14 Theorem14.SB Theorem14.SB.FinRel Restart Restart.RetAux79
open Supp7 (contStop contSet contPath)
open Exist.StagedLaw (markPos markPosL)
open RLC.AStopProc

variable {V : ℝ → ℝ} {T : ℝ≥0} {ξ : ℝ → ℂ} {p d : ℝ} {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {β : ℝ≥0 → ℂ}

/-- The boundary inverse of the entry chart, set to `0` below the real line. -/
def entryInv' (V : ℝ → ℝ) (T d : ℝ) (v : ℂ) : ℂ := if 0 ≤ v.im then entryInv V T d v else 0

theorem entryInv'_of_nonneg {V : ℝ → ℝ} {T d : ℝ} {v : ℂ} (hv : 0 ≤ v.im) :
    entryInv' V T d v = entryInv V T d v := by
  simp only [entryInv', hv, ↓reduceIte]

/-- **The entry chart is a chart of the unbounded domain** of the completed path. -/
theorem IsEntryData.isDomChart {T : ℝ} (h : IsEntryData V T ξ p d) :
    Supp7.IsDomChart (entryPath ξ T d '' Icc 0 1) (entryChart V T d).1 (entryInv' V T d) := by
  have hDc := h.isDomainChart'
  have hinvH : ∀ v ∈ H, entryInv' V T d v = (entryChart V T d).2.1 v := fun v hv => by
    rw [entryInv'_of_nonneg (le_of_lt hv), h.entryInv_eq_inv hv]
  refine ⟨⟨fun z hz => hDc.fwd_mem hz, fun z hz z' hz' he => ?_, fun v hv => ?_⟩, hDc.differentiableOn_fwd,
    h.isLeftEntryChart.2.2.1, ⟨fun v hv => ?_, fun v hv v' hv' he => ?_, fun z hz => ?_⟩, fun v hv => ?_,
    fun v hv => ?_, ?_, ?_, ?_⟩
  · rw [← hDc.inv_fwd hz, ← hDc.inv_fwd hz', he]
  · exact ⟨(entryChart V T d).2.1 v, hDc.inv_mem hv, hDc.fwd_inv hv⟩
  · rw [hinvH v hv]; exact hDc.inv_mem hv
  · rw [hinvH v hv, hinvH v' hv'] at he
    exact hDc.1.injOn hv hv' he
  · exact ⟨(entryChart V T d).1 z, hDc.fwd_mem hz, by rw [hinvH _ (hDc.fwd_mem hz)]; exact hDc.inv_fwd hz⟩
  · rw [hinvH v hv]; exact hDc.fwd_inv hv
  · by_cases hv0 : 0 ≤ v.im
    · have him : v.im = 0 := le_antisymm (not_lt.1 hv) hv0
      have hvr : v = ((v.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
      rw [entryInv'_of_nonneg hv0, hvr]
      exact h.entryInv_real_notMem v.re
    · simp only [entryInv', hv0, ↓reduceIte]
      rintro ⟨h0, -⟩
      have : (0 : ℝ) < (0 : ℂ).im := h0
      simp at this
  · exact hDc.1.1.congr fun v hv => hinvH v hv
  · exact h.continuousOn_entryInv.congr fun v hv => entryInv'_of_nonneg hv
  · obtain ⟨C, hC⟩ := h.exists_norm_entryInv_sub_le
    exact ⟨C, fun v hv => by rw [entryInv'_of_nonneg hv]; exact hC v hv⟩

namespace IsPathSample

variable (h : IsPathSample V T ξ p d w ζ β)
include h

omit h in
theorem stopT_stopT (r : ℝ≥0) : stopT ξ T d β ζ (stopT ξ T d β ζ r) = stopT ξ T d β ζ r :=
  stopT_of_le (coe_stopT_le ξ T d β ζ r)

omit h in
theorem stopT_le_self (r : ℝ≥0) : stopT ξ T d β ζ r ≤ r := by
  have h1 : ((stopT ξ T d β ζ r : ℝ≥0) : ℝ≥0∞) ≤ r := by
    unfold stopT
    rw [ENNReal.coe_toNNReal (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_left _ _))]
    exact min_le_left _ _
  exact ENNReal.coe_le_coe.1 h1

omit h in
theorem monotone_stopT : Monotone (stopT ξ T d β ζ) := fun _ _ hab =>
  ENNReal.toNNReal_mono (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_left _ _))
    (min_le_min_right _ (ENNReal.coe_le_coe.2 hab))

theorem chartPath_stopT (r : ℝ≥0) :
    chartPath V ξ T d β ζ (stopT ξ T d β ζ r) = chartPath V ξ T d β ζ r := by
  rw [h.chartPath_eq, h.chartPath_eq (V := V) r, stopT_stopT]

theorem image_chartPath_Icc (r : ℝ≥0) :
    chartPath V ξ T d β ζ '' Icc 0 r = chartPath V ξ T d β ζ '' Icc 0 (stopT ξ T d β ζ r) := by
  apply Subset.antisymm
  · rintro _ ⟨s, hs, rfl⟩
    exact ⟨stopT ξ T d β ζ s, ⟨zero_le, monotone_stopT hs.2⟩, h.chartPath_stopT s⟩
  · exact image_mono (Icc_subset_Icc_right (stopT_le_self r))

theorem chartClock_stopT (r : ℝ≥0) :
    chartClock (chartPath V ξ T d β ζ) r = chartClock (chartPath V ξ T d β ζ) (stopT ξ T d β ζ r) := by
  unfold chartClock
  rw [h.image_chartPath_Icc]

/-- **Lower bound for the relative clock** (additivity of capacity). -/
theorem chartClock_ge {t : ℝ≥0} (htL : (t : ℝ≥0∞) ≤ physStop ξ T d β ζ) (htζ : (t : ℝ≥0∞) < ζ) :
    2 * (t : ℝ) - ConformalImage.hcapSet (fillH (entryPath ξ (T : ℝ) d '' Icc 0 1)) ≤
      2 * chartClock (chartPath V ξ T d β ζ) t := by
  set K := entryPath ξ (T : ℝ) d '' Icc 0 1 with hK
  set Γ := chartPath V ξ T d β ζ with hΓ
  have hV := h.entry.tip.cont
  have hV0 := h.entry.tip.zero
  have hT := h.entry.tip.pos.le
  have hD := h.entry.isDomChart
  have hKc : IsCompact K := h.entry.isCompact_path
  have hβc : ContinuousOn β (Icc 0 t) := h.continuousOn_Icc htζ.le
  set P := K ∪ β '' Icc 0 t with hP
  have hPc : IsCompact P := hKc.union (isCompact_Icc.image_of_continuousOn hβc)
  -- the hulls
  have hKpre : IsPreconnected (K ∪ {z : ℂ | z.im ≤ 0}) :=
    (isPreconnected_Icc.image _ h.entry.continuousOn_entryPath).union (entryPath ξ (T : ℝ) d 0)
      ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩ (show (entryPath ξ (T : ℝ) d 0).im ≤ 0 by
        rw [h.entry.entryPath_zero, ofReal_im]) isPreconnected_lowerHalf
  have hβpre : IsPreconnected (β '' Icc 0 t ∪ {z : ℂ | z.im ≤ 0}) :=
    (isPreconnected_Icc.image _ hβc).union (β 0) ⟨0, ⟨le_rfl, zero_le⟩, rfl⟩
      (show (β 0).im ≤ 0 by rw [h.gen.1, zero_im]) isPreconnected_lowerHalf
  have hKh : IsHPHull (fillH K) := isHPHull_fillH_of_isPreconnected hKc.isBounded hKpre
  have hPpre : IsPreconnected (P ∪ {z : ℂ | z.im ≤ 0}) := by
    have he : P ∪ {z : ℂ | z.im ≤ 0} = (K ∪ {z : ℂ | z.im ≤ 0}) ∪ (β '' Icc 0 t ∪ {z : ℂ | z.im ≤ 0}) := by
      rw [hP]; ext z; simp only [mem_union]; tauto
    rw [he]
    exact hKpre.union (0 : ℂ) (Or.inr (show (0 : ℂ).im ≤ 0 by simp))
      (Or.inr (show (0 : ℂ).im ≤ 0 by simp)) hβpre
  have hPh : IsHPHull (fillH P) := isHPHull_fillH_of_isPreconnected hPc.isBounded hPpre
  have hKP : fillH K ⊆ fillH P := fillH_mono subset_union_left
  -- the chart path inverts to the explorer
  have hinvΓ : ∀ r ∈ Icc 0 t, entryInv' V (T : ℝ) d (Γ r) = β r := by
    intro r hr
    rw [entryInv'_of_nonneg (h.chartPath_mem_Hbar r), h.entryInv_chartPath,
      stopT_of_le ((ENNReal.coe_le_coe.2 hr.2).trans htL)]
  have hPK : P ⊆ K ∪ entryInv' V (T : ℝ) d '' (Γ '' Icc 0 t) := by
    rintro z (hz | ⟨s, hs, rfl⟩)
    · exact Or.inl hz
    · exact Or.inr ⟨Γ s, ⟨s, hs, rfl⟩, hinvΓ s hs⟩
  have hΓP : ∀ r ∈ Icc 0 t, entryInv' V (T : ℝ) d (Γ r) ∈ P := fun r hr => by
    rw [hinvΓ r hr]; exact Or.inr ⟨r, hr, rfl⟩
  -- the mapping-out function
  have hg : IsMapOut (fillH K) (fun z => fwdMap V (T : ℝ) (z - (d : ℂ)) + V (T : ℝ) + (d : ℂ)) := by
    rw [h.entry.fillH_entryPath]
    exact Sec7.ReverseArc.isMapOut_translate (isMapOut_fwdMap hV hV0 hT) d
  have hφ : ∀ z, (entryChart V (T : ℝ) d).1 z =
      (fun z => fwdMap V (T : ℝ) (z - (d : ℂ)) + V (T : ℝ) + (d : ℂ)) z -
        ((V (T : ℝ) + d + markPosL V (T : ℝ) (-d) : ℝ) : ℂ) := by
    intro z
    rw [entryChart_fst]
    push_cast
    ring
  have hadd := hD.hcapSet_fillH_eq_add hg hφ (by rw [ofReal_im]) hKh hPh hPc hKP hPK
    h.continuous_chartPath.continuousOn (by rw [hΓ, h.chartPath_zero, zero_im]) hΓP
  -- the explorer's own capacity
  obtain ⟨Wg, ηg, hWg, hWg0, -, -, hKg⟩ := exists_globalTrace_of_isGeneratingTrace h.gen h.drvCont h.drvZero
    (t := (t : ℝ)) t.coe_nonneg (by rw [ENNReal.ofReal_coe_nnreal]; exact htζ)
  rw [Real.toNNReal_coe] at hKg
  have hβh : IsHPHull (fillH (β '' Icc 0 t)) := hKg ▸ isHPHull_fwdHull hWg t.coe_nonneg
  have hcapβ : ConformalImage.hcapSet (fillH (β '' Icc 0 t)) = 2 * (t : ℝ) := by
    rw [ConformalImage.hcapSet_eq hβh]
    have := hcap_fwdHull hWg hWg0 t.coe_nonneg
    simp only [← hKg]
    exact this
  have hmono : ConformalImage.hcapSet (fillH (β '' Icc 0 t)) ≤ ConformalImage.hcapSet (fillH P) := by
    rw [ConformalImage.hcapSet_eq hβh, ConformalImage.hcapSet_eq hPh]
    exact HPHull.hcap_mono (A := ⟨_, hβh⟩) (B := ⟨_, hPh⟩) (fillH_mono subset_union_right)
  have hcl : 2 * chartClock Γ t = ConformalImage.hcapSet (fillH (Γ '' Icc 0 t)) := by
    unfold chartClock; ring
  rw [hcl]
  linarith

/-- **The relative capacity is a clock on the physical stop.** -/
theorem isClockOn : IsClockOn (chartClock (chartPath V ξ T d β ζ)) (physStop ξ T d β ζ) := by
  set L := physStop ξ T d β ζ with hL
  have hL0 : 0 < L := h.stopPos
  obtain ⟨S₀, hS₀, hS₀L⟩ : ∃ S₀ : ℝ≥0, 0 < S₀ ∧ (S₀ : ℝ≥0∞) ≤ L := by
    by_cases hLt : L = ⊤
    · exact ⟨1, one_pos, by rw [hLt]; exact le_top⟩
    · exact ⟨L.toNNReal, ENNReal.toNNReal_pos hL0.ne' hLt, by rw [ENNReal.coe_toNNReal hLt]⟩
  refine ⟨(h.exists_window (V := V) hS₀ hS₀L).1.zero, fun a ha b hb hab => ?_, fun r hr => ?_, fun hLt M => ?_⟩
  · have hb0 : 0 < b := lt_of_le_of_lt zero_le hab
    exact (h.exists_window (V := V) hb0 hb).1.strictMonoOn
      (show (a : ℝ≥0∞) ≤ (b : ℝ≥0∞) from ENNReal.coe_le_coe.2 hab.le)
      (show (b : ℝ≥0∞) ≤ (b : ℝ≥0∞) from le_rfl) hab
  · by_cases hLt : L = ⊤
    · have hS : ((r + 1 : ℝ≥0) : ℝ≥0∞) ≤ L := by rw [hLt]; exact le_top
      have hc := (h.exists_window (V := V) (U := r + 1) (by positivity) hS).1.continuousOn r
        (show (r : ℝ≥0∞) ≤ ((r + 1 : ℝ≥0) : ℝ≥0∞) from ENNReal.coe_le_coe.2 le_self_add)
      refine hc.mono_of_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds (mem_of_superset
        (Iio_mem_nhds (lt_add_one r)) fun y hy => ?_))
      exact show (y : ℝ≥0∞) ≤ ((r + 1 : ℝ≥0) : ℝ≥0∞) from ENNReal.coe_le_coe.2 (le_of_lt hy)
    · have hS : ((L.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ L := by rw [ENNReal.coe_toNNReal hLt]
      have hc := (h.exists_window (V := V) (ENNReal.toNNReal_pos hL0.ne' hLt) hS).1.continuousOn
      refine (hc.mono fun y hy => ?_) r hr
      show (y : ℝ≥0∞) ≤ ((L.toNNReal : ℝ≥0) : ℝ≥0∞)
      rw [ENNReal.coe_toNNReal hLt]
      exact hy
  · -- unbounded capacity when the stop is infinite
    have hζ : ζ = ⊤ := top_le_iff.1 (hLt ▸ physStop_le ξ T d β ζ)
    set C := ConformalImage.hcapSet (fillH (entryPath ξ (T : ℝ) d '' Icc 0 1)) with hC
    set t : ℝ≥0 := (M + C / 2).toNNReal with ht
    have hge := h.chartClock_ge (V := V) (t := t) (by rw [← hL, hLt]; exact le_top)
      (by rw [hζ]; exact ENNReal.coe_lt_top)
    refine ⟨t, ?_⟩
    have h1 : M + C / 2 ≤ t := Real.le_coe_toNNReal _
    linarith

theorem monotone_chartClock : Monotone (chartClock (chartPath V ξ T d β ζ)) := by
  intro a b hab
  rw [h.chartClock_stopT a, h.chartClock_stopT b]
  exact h.isClockOn.strictMonoOn.monotoneOn (coe_stopT_le ξ T d β ζ a) (coe_stopT_le ξ T d β ζ b)
    (monotone_stopT hab)

theorem continuous_chartClock : Continuous (chartClock (chartPath V ξ T d β ζ)) := by
  have he : chartClock (chartPath V ξ T d β ζ) =
      fun r => chartClock (chartPath V ξ T d β ζ) (stopT ξ T d β ζ r) := funext h.chartClock_stopT
  rw [he]
  exact h.isClockOn.continuousOn.comp_continuous (continuous_stopT ξ T d β ζ) fun r =>
    coe_stopT_le ξ T d β ζ r

/-- **The chart path with the physical stop is a good sample** of the abstract A-stopped processes. -/
theorem isAGood {Ω : Type*} (ω : Ω) :
    IsAGood (fun _ : Ω => chartPath V ξ T d β ζ) (fun _ : Ω => physStop ξ T d β ζ) ω := by
  have hclk := h.isClockOn (V := V)
  have hwin : ∀ S : ℝ≥0, 0 < S → (S : ℝ≥0∞) ≤ physStop ξ T d β ζ → ∃ W : ℝ → ℝ, Continuous W ∧ W 0 = 0 ∧
      ∀ t ∈ Icc 0 S, fwdHull W (chartClock (chartPath V ξ T d β ζ) t) =
        fillH (chartPath V ξ T d β ζ '' Icc 0 t) := by
    intro S hS hSL
    obtain ⟨-, W, hW, hW0, hK⟩ := h.exists_window (V := V) hS hSL
    exact ⟨W, hW, hW0, fun t ht => (hK t ht.2).2⟩
  obtain ⟨W, hW, hW0, hK⟩ := exists_driver_of_windows hclk h.stopPos hwin
  refine ⟨h.stopPos, h.continuous_chartPath, h.chartPath_zero, hclk, h.monotone_chartClock,
    h.continuous_chartClock, fun s hs => ?_, W, hW, hW0, ?_⟩
  · have hfin : physStop ξ T d β ζ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hs
    rw [h.chartPath_of_ge hs, h.chartPath_of_ge (ENNReal.coe_toNNReal hfin).ge]
  · exact isGeneratingTrace_invClock hclk h.continuous_chartPath h.chartPath_zero hK

end IsPathSample

end Term

end InteractingSLE.RealContact
