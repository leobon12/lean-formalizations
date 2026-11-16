/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.RealContact.TermChart
import InteractingSLE.Spec.Supplement.CounterflowRange
import InteractingSLE.Spec.Restart.ClockTrace

/-!
# The terminal retained pair: the completed second path ends at a freshly reached real tip (deterministic)

Packet PROVE-RC-TERM (ruling R124), steps P1.1–P1.2 of `planning/handoffs/PROVE-RC-POCKET.md` for one sample. Let `e`
be a regular driver with a good record through its finite lifetime `T`, generating the simple path `η − x` on
`[0, T]`, and let `η(T) = q` be real with `q ≠ x`. Then:

* **`isFreshRealTip_of_trace`**: the record driver `rdrv (termRec e)`, the horizon `rtime (termRec e) = T` and the
  recentred path `s ↦ η(s) − x` form a freshly reached real tip `q − x` (`Term.IsFreshRealTip`). Freshness: the tip is
  not an earlier trace point (injectivity) and not a point swallowed untouched earlier
  (`Theorem14.SB.Wf.gen_end_ne_of_mem_closure_fill`);
* **`activeDomain_eq_image`**: the active domain of the retained pair `(0, T)` is the translate by `x` of the
  complement of the hull at the horizon;
* **`isActiveChart_term`**: the recentred centred Loewner map `z ↦ f_T(z − x)` is an active chart of that domain at
  the terminal point `q` (the first clause of `IsTerminalRetainedContinuation`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open scoped NNReal ENNReal

open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull logDerivFwd)

namespace InteractingSLE.RealContact

namespace Term

open Exist.Staged Exist.StagedLaw

variable {e : (ℝ≥0 → ℝ) × ℝ≥0∞} {η : ℝ≥0 → ℂ} {x q : ℝ} {T : ℝ≥0}

theorem rtime_termRec (hT : (T : ℝ≥0∞) = e.2) : rtime (termRec e) = (T : ℝ) := by
  change (((min ⊤ e.2).toNNReal : ℝ≥0) : ℝ) = T
  rw [min_eq_right le_top, ← hT, ENNReal.toNNReal_coe]

theorem rdrv_termRec (he : IsRegularDriver e) (hg : LocalExt.IsDrvGood (recHist (termRec e))) :
    rdrv (termRec e) = fun s : ℝ => (retOf ⊤ e).1 s.toNNReal :=
  recDrv_eq_stopDrv he hg

/-- The path `η − x` is a generating trace of the stopped driver of the record through the lifetime. -/
theorem isGeneratingTrace_retOf (hT : (T : ℝ≥0∞) = e.2) (hη : IsGeneratingTrace e.1 e.2 (fun t => η t - x)) :
    IsGeneratingTrace (retOf ⊤ e).1 (T : ℝ≥0∞) (fun t => η t - x) := by
  rw [hT]
  refine Restart.StoppedK2.isGeneratingTrace_congr (fun t ht => ?_) hη
  change e.1 t = e.1 (min (t : ℝ≥0∞) (min ⊤ e.2)).toNNReal
  rw [min_eq_right le_top, min_eq_left ht.le, ENNReal.toNNReal_coe]

/-- **The completed path ends at a freshly reached real tip.** -/
theorem isFreshRealTip_of_trace (he : IsRegularDriver e) (hg : LocalExt.IsDrvGood (recHist (termRec e)))
    (hT : (T : ℝ≥0∞) = e.2) (hη : IsGeneratingTrace e.1 e.2 (fun t => η t - x))
    (hinj : InjOn η {t | (t : ℝ≥0∞) ≤ e.2}) (htip : η T = q) (hq : q ≠ x) :
    IsFreshRealTip (rdrv (termRec e)) (rtime (termRec e)) (fun s : ℝ => η s.toNNReal - x) (q - x) := by
  have hη' := isGeneratingTrace_retOf hT hη
  have hwc : Continuous (retOf ⊤ e).1 := continuous_retOf he hg
  have hw0 : (retOf ⊤ e).1 0 = 0 := by
    change e.1 (min ((0 : ℝ≥0) : ℝ≥0∞) (min ⊤ e.2)).toNNReal = 0
    rw [ENNReal.coe_zero, min_eq_left (zero_le (a := min _ _)), ENNReal.toNNReal_zero]
    exact he.2.1
  have hTpos : 0 < T := by
    rcases eq_zero_or_pos T with h0 | hpos
    · exfalso
      have h1 : η 0 - x = 0 := hη.1
      rw [h0] at htip
      rw [htip, sub_eq_zero] at h1
      exact hq (by exact_mod_cast h1)
    · exact hpos
  have htrace := Theorem14.CounterflowRange.isLoewnerTraceLT_of_isGeneratingTrace hη'
  have hcγ : ContinuousOn (fun s : ℝ => η s.toNNReal - x) (Icc 0 (T : ℝ)) := by
    refine hη'.2.1.comp continuous_real_toNNReal.continuousOn fun s hs => ?_
    show ((s.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ T
    exact ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hs.2)
  rw [rdrv_termRec he hg, rtime_termRec hT]
  refine ⟨hwc.comp continuous_real_toNNReal, by simp only [Real.toNNReal_zero, hw0],
    NNReal.coe_pos.2 hTpos, htrace, hcγ, ?_, sub_ne_zero.2 hq, fun t ht htT => ?_⟩
  · simp only [Real.toNNReal_coe, htip, Complex.ofReal_sub]
  · intro hmem
    rw [htrace.2.2 t ht htT, image_toNNReal_Icc (fun r => η r - x) ht] at hmem
    have hsT : t.toNNReal < T := (Real.toNNReal_lt_iff_lt_coe ht).2 htT
    have hpA : ((q - x : ℝ) : ℂ) ∉ (fun r => η r - x) '' Icc 0 t.toNNReal := by
      rintro ⟨r, hr, hre⟩
      have h1 : η r = η T := by
        rw [htip]
        have h2 : η r - x = (q : ℂ) - x := by
          have hre' : η r - (x : ℂ) = ((q - x : ℝ) : ℂ) := hre
          rw [hre', Complex.ofReal_sub]
        exact sub_left_injective h2
      have hrT : r = T := hinj (show (r : ℝ≥0∞) ≤ e.2 from hT ▸ ENNReal.coe_le_coe.2 (hr.2.trans hsT.le))
        (show (T : ℝ≥0∞) ≤ e.2 from hT.le) h1
      exact absurd hr.2 (not_le.2 (hrT ▸ hsT))
    have hne := Theorem14.SB.Wf.gen_end_ne_of_mem_closure_fill hη' hwc.continuousOn hw0 hsT hpA hmem
    exact hne (by simp only [htip, Complex.ofReal_sub])

/-! ### The active domain and the chart in the original coordinates -/

/-- Translation by a real number preserves `ℍ`. -/
theorem image_add_real_H_diff (K : Set ℂ) (x : ℝ) :
    (fun z : ℂ => z + x) '' (H \ K) = H \ (fun z : ℂ => z + x) '' K := by
  ext z
  constructor
  · rintro ⟨w, ⟨hwH, hwK⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · show 0 < (w + x).im
      have h0 : 0 < w.im := hwH
      simpa using h0
    · rintro ⟨w', hw', he⟩
      exact hwK (by rwa [add_right_cancel he] at hw')
  · rintro ⟨hzH, hzK⟩
    refine ⟨z - x, ⟨?_, fun hK => hzK ⟨z - x, hK, sub_add_cancel z _⟩⟩, sub_add_cancel z _⟩
    show 0 < (z - x).im
    have h0 : 0 < z.im := hzH
    simpa using h0

/-- **The active domain of the retained pair `(0, T)`** is the translate of the complement of the hull at the
horizon. -/
theorem activeDomain_eq_image (he : IsRegularDriver e) (hg : LocalExt.IsDrvGood (recHist (termRec e)))
    (hT : (T : ℝ≥0∞) = e.2) (hη : IsGeneratingTrace e.1 e.2 (fun t => η t - x))
    (hinj : InjOn η {t | (t : ℝ≥0∞) ≤ e.2}) (htip : η T = q) (hq : q ≠ x) {η₁ : ℝ≥0 → ℂ}
    (h₁ : (η₁ 0).im = 0) :
    activeDomain η₁ 0 η T =
      (fun z : ℂ => z + x) '' (H \ fwdHull (rdrv (termRec e)) (rtime (termRec e))) := by
  have hf := isFreshRealTip_of_trace he hg hT hη hinj htip hq
  have hη' := isGeneratingTrace_retOf hT hη
  have hcη : ContinuousOn η (Icc 0 T) := by
    have h1 : ContinuousOn (fun t => η t - x) (Icc 0 T) :=
      hη'.2.1.mono fun t ht => ENNReal.coe_le_coe.2 ht.2
    have h2 := h1.add (continuousOn_const (c := (x : ℂ)))
    refine h2.congr fun t _ => ?_
    exact (sub_add_cancel (η t) (x : ℂ)).symm
  have hcomp : IsCompact (η '' Icc 0 T) := isCompact_Icc.image_of_continuousOn hcη
  have hclosed : IsClosed (η₁ '' Icc 0 0 ∪ η '' Icc 0 T) := by
    rw [Icc_self, image_singleton]
    exact isClosed_singleton.union hcomp.isClosed
  rw [Supp7.activeDomain_eq_H_diff_fillH hclosed, union_comm,
    Restart.fillH_union_of_forall_notMem_H (A := η '' Icc 0 T) (B := η₁ '' Icc 0 0) (by
      rw [Icc_self, image_singleton]
      intro z hz hzH
      rw [mem_singleton_iff] at hz
      have h2 : 0 < z.im := hzH
      rw [hz, h₁] at h2
      exact lt_irrefl 0 h2),
    TraceClose.fwdHull_eq_fillH_of_isLoewnerTraceLT hf.trace hf.cont hf.zero hf.pos hf.traceCont,
    rtime_termRec hT, SB2MbFill_image, image_add_real_H_diff, ← Restart.fillH_image_add_real,
    Restart.image_add_real_eq]
where
  SB2MbFill_image : (fun s : ℝ => η s.toNNReal - x) '' Icc 0 (T : ℝ) = (fun t => η t - x) '' Icc 0 T := by
    rw [image_toNNReal_Icc (fun r => η r - x) T.coe_nonneg, Real.toNNReal_coe]

/-- **The recentred Loewner map at the lifetime is an active chart of the retained pair `(0, T)` at the terminal
point** (the first clause of `IsTerminalRetainedContinuation`). -/
theorem isActiveChart_term (he : IsRegularDriver e) (hg : LocalExt.IsDrvGood (recHist (termRec e)))
    (hT : (T : ℝ≥0∞) = e.2) (hη : IsGeneratingTrace e.1 e.2 (fun t => η t - x))
    (hinj : InjOn η {t | (t : ℝ≥0∞) ≤ e.2}) (htip : η T = q) (hq : q ≠ x) {η₁ : ℝ≥0 → ℂ}
    (h₁ : (η₁ 0).im = 0) :
    IsActiveChart (activeDomain η₁ 0 η T) (η T)
      (fun z => fwdMap (rdrv (termRec e)) (rtime (termRec e)) (z - x)) := by
  have hf := isFreshRealTip_of_trace he hg hT hη hinj htip hq
  obtain ⟨hbij, hdiff, htend, hinf⟩ := hf.isActiveChart
  rw [activeDomain_eq_image he hg hT hη hinj htip hq h₁, htip]
  set D₀ := H \ fwdHull (rdrv (termRec e)) (rtime (termRec e)) with hD₀
  have hmaps : MapsTo (fun z : ℂ => z - x) ((fun z : ℂ => z + x) '' D₀) D₀ := by
    rintro _ ⟨w, hw, rfl⟩
    simpa only [add_sub_cancel_right] using hw
  refine ⟨⟨fun z hz => hbij.1 (hmaps hz), fun z hz z' hz' hzz' => ?_, fun w hw => ?_⟩, ?_, ?_, ?_⟩
  · exact sub_left_injective (hbij.2.1 (hmaps hz) (hmaps hz') hzz')
  · obtain ⟨z, hz, hzw⟩ := hbij.2.2 hw
    exact ⟨z + x, ⟨z, hz, rfl⟩, by simpa only [add_sub_cancel_right] using hzw⟩
  · exact hdiff.comp (differentiableOn_id.sub (differentiableOn_const _)) hmaps
  · have h1 : Tendsto (fun z : ℂ => z - x) (𝓝[(fun z : ℂ => z + x) '' D₀] (q : ℂ)) (𝓝[D₀] ((q - x : ℝ) : ℂ)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun z hz => hmaps hz⟩
      have h2 : Tendsto (fun z : ℂ => z - x) (𝓝 (q : ℂ)) (𝓝 ((q : ℂ) - x)) :=
        (continuous_id.sub continuous_const).tendsto _
      rw [Complex.ofReal_sub]
      exact h2.mono_left nhdsWithin_le_nhds
    exact htend.comp h1
  · have h1 : Tendsto (fun z : ℂ => z - x) (Bornology.cobounded ℂ ⊓ 𝓟 ((fun z : ℂ => z + x) '' D₀))
        (Bornology.cobounded ℂ ⊓ 𝓟 D₀) := by
      refine tendsto_inf.2 ⟨?_, tendsto_principal.2 (mem_inf_of_right (fun z hz => hmaps hz))⟩
      have h2 : Tendsto (fun z : ℂ => z - x) (Bornology.cobounded ℂ) (Bornology.cobounded ℂ) := by
        rw [← tendsto_norm_atTop_iff_cobounded]
        have h3 : Tendsto (fun z : ℂ => ‖z‖ - ‖(x : ℂ)‖) (Bornology.cobounded ℂ) atTop :=
          tendsto_atTop_add_const_right _ _ tendsto_norm_cobounded_atTop
        refine tendsto_atTop_mono (fun z => ?_) h3
        have := norm_sub_norm_le z (x : ℂ)
        linarith
      exact h2.mono_left inf_le_left
    exact hinf.comp h1

end Term

end InteractingSLE.RealContact
