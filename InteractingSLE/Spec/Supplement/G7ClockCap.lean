/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.G7ClockPath
import InteractingSLE.Spec.Supplement.G7RetainedReduce

/-!
# The relative capacity clock of a retained continuation (W8.1 for retained pairs)

Packet PROVE-G7B. Lemma G7 (`source/spec/p481-528.md`, pp. 497–498): "Local growth and strict capacity growth give
continuous relative capacity and a continuous driver. […] the original and relative clocks are the filled-hull
capacity clocks". For a retained continuation with a chart (`IsRetCont`) and its chart path `Γ = contPath …`
(`G7ClockPath.lean`):

* `IsRetCont.contPath_mem_closure`: criterion (a) of Proposition 6.12 — every later chart point is adherent to the
  unbounded domain of `Γ([0, t])` (relative domains by Janiszewski, `mem_relDomain_of_noContact`, then the forward
  image, `IsDomChart.fwd_image_subset`; at real or terminal points, approximation by interior times);
* `IsRetCont.chartClock_spec`: Proposition 6.12 for `Γ` on `[0, S]`, `S ≤ V`: its capacity clock `chartClock Γ`
  vanishes at `0`, is continuous and strictly increasing, and the simple chart path is the Loewner trace of a
  continuous driver `W` in that clock (`fwdHull W (chartClock Γ t) = fill Γ([0, t])`);
* `IsRetCont.chartClock_ge`: `hcap fill η([0, a + t]) − hcap fill K ≤ 2 chartClock Γ t` (additivity of capacity);
* **`IsRetCont.isClockOn`**: `chartClock Γ` is a clock on `[0, V]` (unbounded when the continuation is);
* **`IsRetCont.isRetainedClock`**: reading `Γ` (translated by a real `c`) in its inverse relative capacity clock gives
  `IsRetainedClock` (the clock relation of the named input `RetainedPairRestartStatement`) for any `ψ'` with
  `ψ'(w + c) = ψ(w)`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace Supp7

open Restart

namespace IsRetCont

variable {η : ℝ≥0 → ℂ} {ζ : ℝ≥0∞} {x : ℝ} {a : ℝ≥0} {O : Set ℂ} {φ ψ : ℂ → ℂ}
  (hR : IsRetCont η ζ x a O φ ψ)
include hR

/-- **Criterion (a) of Proposition 6.12 for the chart path.** -/
theorem contPath_mem_closure {t r : ℝ≥0} (htr : t < r) (hrV : (r : ℝ≥0∞) ≤ contLife η ζ a (O ∪ η '' Icc 0 a)) :
    contPath (H \ fillH (O ∪ η '' Icc 0 a)) φ η a (contLife η ζ a (O ∪ η '' Icc 0 a)) r ∈
      closure (H \ fillH (contPath (H \ fillH (O ∪ η '' Icc 0 a)) φ η a (contLife η ζ a (O ∪ η '' Icc 0 a)) ''
        Icc 0 t)) := by
  set K := O ∪ η '' Icc 0 a with hK
  set V := contLife η ζ a K with hVdef
  set Γ := contPath (H \ fillH K) φ η a V with hΓ
  have hcont : Continuous Γ := hR.continuous_contPath
  have hgood : ∀ y : ℝ≥0, t < y → (y : ℝ≥0∞) < V → η (a + y) ∈ H → Γ y ∈ H \ fillH (Γ '' Icc 0 t) := by
    intro y hty hyV hyH
    have hy0 : 0 < y := lt_of_le_of_lt zero_le hty
    have hΓy : Γ y = φ (η (a + y)) := (hR.contPath_mem_H hy0 hyV hyH).2
    have hlt : ((a + y : ℝ≥0) : ℝ≥0∞) < contStop η ζ a K := coe_add_lt_iff.1 hyV
    have hD := hR.mem_D_of_lt_contStop (lt_add_of_pos_right a hy0) hlt hyH
    have haty : a + t < a + y := (add_lt_add_iff_left a).2 hty
    have hrel := IsPathGood.mem_relDomain_of_noContact hR.path (le_self_add : a ≤ a + t) haty
      (hlt.le.trans contStop_le) hR.compact (fun t' h1 h2 hO => notMem_of_lt_contStop h1
        ((ENNReal.coe_le_coe.2 h2).trans_lt ((ENNReal.coe_lt_coe.2 haty).trans hlt)) (Or.inl hO)) hD
    rw [hΓy]
    have htζ : ((a + t : ℝ≥0) : ℝ≥0∞) ≤ ζ := (ENNReal.coe_le_coe.2 haty.le).trans (hlt.le.trans contStop_le)
    have hP : IsCompact (O ∪ η '' Icc 0 (a + t)) :=
      hR.compact.union (IsPathGood.isCompact_image_Icc_of_le hR.path htζ)
    have hKP : fillH K ⊆ fillH (O ∪ η '' Icc 0 (a + t)) :=
      fillH_mono (union_subset_union_right _ (image_mono (Icc_subset_Icc_right le_self_add)))
    refine hR.chart.fwd_image_subset hP hKP hcont.continuousOn (fun r' hr' => ?_) ⟨η (a + y), hrel, rfl⟩
    have hr'V : (r' : ℝ≥0∞) ≤ V := (ENNReal.coe_le_coe.2 (hr'.2.trans hty.le)).trans hyV.le
    rw [show ψ (Γ r') = η (a + r') from (hR.contPath_spec hr'V).2]
    exact Or.inr ⟨a + r', ⟨zero_le, add_le_add le_rfl hr'.2⟩, rfl⟩
  have hrζ : ((a + r : ℝ≥0) : ℝ≥0∞) ≤ ζ :=
    ((coe_add_le_iff hR.lt_contStop.le).1 hrV).trans contStop_le
  by_cases hrH : (r : ℝ≥0∞) < V ∧ η (a + r) ∈ H
  · exact subset_closure (hgood r htr hrH.1 hrH.2)
  · refine mem_closure_of_left (ζ := V) htr hrV hcont.continuousWithinAt fun c htc hcr => ?_
    obtain ⟨s, hs, hsH⟩ := IsPathGood.exists_mem_H_between hR.path ((add_lt_add_iff_left a).2 hcr) hrζ
    have has : a ≤ s := le_self_add.trans hs.1.le
    have hsr : s - a < r := (tsub_lt_iff_left has).2 hs.2
    refine ⟨s - a, ⟨lt_tsub_iff_left.2 hs.1, hsr⟩, ?_⟩
    have hx : a + (s - a) = s := add_tsub_cancel_of_le has
    exact hgood _ (htc.trans_lt (lt_tsub_iff_left.2 hs.1)) ((ENNReal.coe_lt_coe.2 hsr).trans_le hrV)
      (by rw [hx]; exact hsH)

/-- **Proposition 6.12 for the chart path** on `[0, S]`, `0 < S ≤ V`: the relative capacity clock vanishes at `0`, is
strictly increasing and continuous on `[0, S]`. -/
theorem chartClock_spec {S : ℝ≥0} (hS : 0 < S) (hSV : (S : ℝ≥0∞) ≤ contLife η ζ a (O ∪ η '' Icc 0 a)) :
    chartClock (contPath (H \ fillH (O ∪ η '' Icc 0 a)) φ η a (contLife η ζ a (O ∪ η '' Icc 0 a))) 0 = 0 ∧
      StrictMonoOn (chartClock (contPath (H \ fillH (O ∪ η '' Icc 0 a)) φ η a
        (contLife η ζ a (O ∪ η '' Icc 0 a)))) (Icc 0 S) ∧
      ContinuousOn (chartClock (contPath (H \ fillH (O ∪ η '' Icc 0 a)) φ η a
        (contLife η ζ a (O ∪ η '' Icc 0 a)))) (Icc 0 S) ∧
      ∃ W : ℝ → ℝ, Continuous W ∧ W 0 = 0 ∧ ∀ t ∈ Icc 0 S,
        0 ≤ chartClock (contPath (H \ fillH (O ∪ η '' Icc 0 a)) φ η a (contLife η ζ a (O ∪ η '' Icc 0 a))) t ∧
        QuantumZipper.fwdHull W (chartClock (contPath (H \ fillH (O ∪ η '' Icc 0 a)) φ η a
          (contLife η ζ a (O ∪ η '' Icc 0 a))) t) =
          fillH (contPath (H \ fillH (O ∪ η '' Icc 0 a)) φ η a (contLife η ζ a (O ∪ η '' Icc 0 a)) '' Icc 0 t) := by
  set K := O ∪ η '' Icc 0 a with hK
  set V := contLife η ζ a K with hVdef
  set Γ := contPath (H \ fillH K) φ η a V with hΓ
  have hS' : (0 : ℝ) < S := NNReal.coe_pos.2 hS
  have hcont : Continuous Γ := hR.continuous_contPath
  have hV : ∀ r ∈ Icc 0 S, (r : ℝ≥0∞) ≤ V := fun r hr => (ENNReal.coe_le_coe.2 hr.2).trans hSV
  have hmaps : MapsTo Real.toNNReal (Icc 0 (S : ℝ)) (Icc 0 S) := fun r hr =>
    ⟨zero_le, by simpa using Real.toNNReal_le_toNNReal hr.2⟩
  have hc : ContinuousOn (realPath Γ) (Icc 0 (S : ℝ)) :=
    hcont.continuousOn.comp continuous_real_toNNReal.continuousOn hmaps
  have hstopζ : contStop η ζ a K ≤ ζ := contStop_le
  have hΓi : InjOn Γ (Icc 0 S) := by
    intro p hp q hq hpq
    have h1 : ψ (Γ p) = η (a + p) := (hR.contPath_spec (hV p hp)).2
    have h2 : ψ (Γ q) = η (a + q) := (hR.contPath_spec (hV q hq)).2
    have hpζ := ((coe_add_le_iff hR.lt_contStop.le).1 (hV p hp)).trans hstopζ
    have hqζ := ((coe_add_le_iff hR.lt_contStop.le).1 (hV q hq)).trans hstopζ
    have := hR.path.1 hpζ hqζ (by rw [← h1, ← h2, hpq])
    exact add_left_cancel this
  have hinj : InjOn (realPath Γ) (Icc 0 (S : ℝ)) := fun p hp q hq hpq => by
    have := hΓi (hmaps hp) (hmaps hq) hpq
    rw [← Real.coe_toNNReal p hp.1, ← Real.coe_toNNReal q hq.1, this]
  have hH : MapsTo (realPath Γ) (Icc 0 (S : ℝ)) Hbar := fun r hr => (hR.contPath_spec (hV _ (hmaps hr))).1
  have hz : Γ 0 = 0 := hR.contPath_zero
  have h0 : realPath Γ 0 = 0 := by simp [realPath, hz]
  have ha : Sec6.DrivingCriterionA (realPath Γ) S := by
    rintro t ⟨ht0, htS⟩ _ ⟨r, hr, rfl⟩
    rw [realPath_image_Icc Γ ht0.le]
    have htr : t.toNNReal < r.toNNReal := (Real.toNNReal_lt_toNNReal_iff (ht0.trans hr.1)).2 hr.1
    exact hR.contPath_mem_closure htr (hV _ (hmaps ⟨(ht0.trans hr.1).le, hr.2⟩))
  have hRint : interior {u ∈ Ioo 0 (S : ℝ) | (realPath Γ u).im = 0} = ∅ := by
    by_contra hne
    obtain ⟨y, hy⟩ := Set.nonempty_iff_ne_empty.2 hne
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hy)
    have hy0 : 0 < y := (interior_subset hy : y ∈ _).1.1
    set b : ℝ := max (y / 2) (y - ε / 2) with hb
    have hb0 : 0 < b := lt_of_lt_of_le (half_pos hy0) (le_max_left _ _)
    have hby : b < y := max_lt (half_lt_self hy0) (by linarith)
    have hyS : y.toNNReal ≤ S := (Real.toNNReal_le_iff_le_coe).2 (interior_subset hy : y ∈ _).1.2.le
    have hyζ : ((a + y.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ ζ :=
      ((coe_add_le_iff hR.lt_contStop.le).1 ((ENNReal.coe_le_coe.2 hyS).trans hSV)).trans hstopζ
    obtain ⟨s, hs, hsH⟩ := IsPathGood.exists_mem_H_between hR.path
      ((add_lt_add_iff_left a).2 ((Real.toNNReal_lt_toNNReal_iff hy0).2 hby)) hyζ
    have has : a ≤ s := le_self_add.trans hs.1.le
    set r : ℝ≥0 := s - a with hr
    have hsr : a + r = s := add_tsub_cancel_of_le has
    have hbr : b.toNNReal < r := lt_tsub_iff_left.2 hs.1
    have hry : r < y.toNNReal := (tsub_lt_iff_left has).2 hs.2
    have hbr' : b < r := by
      have := NNReal.coe_lt_coe.2 hbr; rwa [Real.coe_toNNReal _ hb0.le] at this
    have hry' : (r : ℝ) < y := by
      have := NNReal.coe_lt_coe.2 hry; rwa [Real.coe_toNNReal _ hy0.le] at this
    have hmem : (r : ℝ) ∈ ball y ε := by
      rw [mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [le_max_right (y / 2) (y - ε / 2)]
    have hreal := (hball hmem).2
    rw [realPath_coe] at hreal
    have hrV : (r : ℝ≥0∞) < V := (ENNReal.coe_lt_coe.2 (hry.trans_le hyS)).trans_le hSV
    have hΓrH := (hR.contPath_mem_H (lt_of_le_of_lt zero_le hbr) hrV (by rw [hsr]; exact hsH)).1
    exact absurd hreal (ne_of_gt (show (0 : ℝ) < (Γ r).im from hΓrH))
  have hb : Sec6.DrivingCriterionB (realPath Γ) S := Sec6.drivingCriterionB_of_injOn hinj hRint
  obtain ⟨W, hW, hW0, σ, hσ0, hσm, hσc, hσK⟩ := Sec6.exists_driver_of_drivingCriteria hS' hc h0
    (Sec6.hasSimpleApproxOn_of_injOn hS' hc hinj h0 hH) ha hb
  have hclock : ∀ t ∈ Icc 0 S, chartClock Γ t = σ t := by
    intro t ht
    have ht' : (t : ℝ) ∈ Icc 0 (S : ℝ) := ⟨t.2, NNReal.coe_le_coe.2 ht.2⟩
    obtain ⟨hσt, hK', -⟩ := hσK t ht'
    rw [realPath_image_Icc Γ (NNReal.coe_nonneg t), Real.toNNReal_coe] at hK'
    have := hcap_fwdHull hW hW0 hσt
    unfold chartClock
    rw [← hK', ConformalImage.hcapSet_eq (isHPHull_fwdHull hW hσt), this]
    ring
  refine ⟨by rw [hclock 0 ⟨le_rfl, zero_le⟩]; exact_mod_cast hσ0, fun p hp q hq hpq => ?_, ?_,
    W, hW, hW0, fun t ht => ?_⟩
  · rw [hclock p hp, hclock q hq]
    exact hσm ⟨p.2, NNReal.coe_le_coe.2 hp.2⟩ ⟨q.2, NNReal.coe_le_coe.2 hq.2⟩ (NNReal.coe_lt_coe.2 hpq)
  · refine (hσc.comp NNReal.continuous_coe.continuousOn fun t ht =>
      ⟨t.2, NNReal.coe_le_coe.2 ht.2⟩).congr fun t ht => hclock t ht
  · have ht' : (t : ℝ) ∈ Icc 0 (S : ℝ) := ⟨t.2, NNReal.coe_le_coe.2 ht.2⟩
    obtain ⟨hσt, hK', -⟩ := hσK t ht'
    rw [realPath_image_Icc Γ (NNReal.coe_nonneg t), Real.toNNReal_coe] at hK'
    rw [hclock t ht]
    exact ⟨hσt, hK'⟩

/-- The retained union and the lower half-plane are preconnected. -/
theorem isPreconnected_K_union : IsPreconnected ((O ∪ η '' Icc 0 a) ∪ {z : ℂ | z.im ≤ 0}) :=
  isPreconnected_union_lowerHalf hR.hull (isPreconnected_image_union_lowerHalf
    (IsPathGood.continuousOn_Icc_of_le hR.path hR.lt.le) hR.path.seed.le)

/-- **Lower bound for the relative clock** (additivity of capacity). -/
theorem chartClock_ge {t : ℝ≥0} (htV : (t : ℝ≥0∞) ≤ contLife η ζ a (O ∪ η '' Icc 0 a)) :
    ConformalImage.hcapSet (fillH (η '' Icc 0 (a + t))) - ConformalImage.hcapSet (fillH (O ∪ η '' Icc 0 a)) ≤
      2 * chartClock (contPath (H \ fillH (O ∪ η '' Icc 0 a)) φ η a (contLife η ζ a (O ∪ η '' Icc 0 a))) t := by
  set K := O ∪ η '' Icc 0 a with hK
  set V := contLife η ζ a K with hVdef
  set Γ := contPath (H \ fillH K) φ η a V with hΓ
  obtain ⟨x₀, hφ⟩ := hR.hydro
  have htζ : ((a + t : ℝ≥0) : ℝ≥0∞) ≤ ζ := ((coe_add_le_iff hR.lt_contStop.le).1 htV).trans contStop_le
  have hca := IsPathGood.continuousOn_Icc_of_le hR.path htζ
  set P := O ∪ η '' Icc 0 (a + t) with hP
  have hPc : IsCompact P := hR.compact.union (IsPathGood.isCompact_image_Icc_of_le hR.path htζ)
  have hKh : IsHPHull (fillH K) := isHPHull_fillH_of_isPreconnected hR.isCompact_K.isBounded hR.isPreconnected_K_union
  have hPh : IsHPHull (fillH P) := isHPHull_fillH_of_isPreconnected hPc.isBounded
    (isPreconnected_union_lowerHalf hR.hull (isPreconnected_image_union_lowerHalf hca hR.path.seed.le))
  have hKP : fillH K ⊆ fillH P :=
    fillH_mono (union_subset_union_right _ (image_mono (Icc_subset_Icc_right le_self_add)))
  have hV : ∀ r ∈ Icc 0 t, (r : ℝ≥0∞) ≤ V := fun r hr => (ENNReal.coe_le_coe.2 hr.2).trans htV
  have hPK : P ⊆ K ∪ ψ '' (Γ '' Icc 0 t) := by
    rintro z (hz | ⟨s, hs, rfl⟩)
    · exact Or.inl (Or.inl hz)
    · by_cases hsa : s ≤ a
      · exact Or.inl (Or.inr ⟨s, ⟨zero_le, hsa⟩, rfl⟩)
      · push Not at hsa
        have hr : s - a ∈ Icc 0 t := ⟨zero_le, (tsub_le_iff_left).2 hs.2⟩
        refine Or.inr ⟨Γ (s - a), ⟨s - a, hr, rfl⟩, ?_⟩
        rw [show ψ (Γ (s - a)) = η (a + (s - a)) from (hR.contPath_spec (hV _ hr)).2,
          add_tsub_cancel_of_le hsa.le]
  have hΓP : ∀ r ∈ Icc 0 t, ψ (Γ r) ∈ P := fun r hr => by
    rw [show ψ (Γ r) = η (a + r) from (hR.contPath_spec (hV r hr)).2]
    exact Or.inr ⟨a + r, ⟨zero_le, add_le_add le_rfl hr.2⟩, rfl⟩
  have hadd := hR.chart.hcapSet_fillH_eq_add (ConformalImage.isMapOut_mapOut hKh) hφ (by simp) hKh hPh hPc hKP
    hPK hR.continuous_contPath.continuousOn (by rw [show Γ 0 = 0 from hR.contPath_zero]; simp) hΓP
  have h1 := isHPHull_fillH_image hca hR.path.seed.le
  have hmono : ConformalImage.hcapSet (fillH (η '' Icc 0 (a + t))) ≤ ConformalImage.hcapSet (fillH P) := by
    rw [ConformalImage.hcapSet_eq h1, ConformalImage.hcapSet_eq hPh]
    exact HPHull.hcap_mono (A := ⟨_, h1⟩) (B := ⟨_, hPh⟩) (fillH_mono subset_union_right)
  unfold chartClock
  linarith

/-- **The relative capacity clock is a clock on the whole continuation** (Lemma G7, W8.1). -/
theorem isClockOn :
    IsClockOn (chartClock (contPath (H \ fillH (O ∪ η '' Icc 0 a)) φ η a (contLife η ζ a (O ∪ η '' Icc 0 a))))
      (contLife η ζ a (O ∪ η '' Icc 0 a)) := by
  set K := O ∪ η '' Icc 0 a with hK
  set V := contLife η ζ a K with hVdef
  set Γ := contPath (H \ fillH K) φ η a V with hΓ
  have hU0 : 0 < V := hR.pos_contLife
  obtain ⟨S₀, hS₀, hS₀U⟩ : ∃ S₀ : ℝ≥0, 0 < S₀ ∧ (S₀ : ℝ≥0∞) ≤ V := by
    by_cases hU : V = ⊤
    · exact ⟨1, one_pos, by rw [hU]; exact le_top⟩
    · exact ⟨V.toNNReal, ENNReal.toNNReal_pos hU0.ne' hU, by rw [ENNReal.coe_toNNReal hU]⟩
  refine ⟨(hR.chartClock_spec hS₀ hS₀U).1, fun p hp q hq hpq => ?_, fun r hr => ?_, fun hU M => ?_⟩
  · exact (hR.chartClock_spec (lt_of_le_of_lt zero_le hpq) hq).2.1 ⟨zero_le, hpq.le⟩ ⟨zero_le, le_rfl⟩ hpq
  · by_cases hU : V = ⊤
    · have hS : ((r + 1 : ℝ≥0) : ℝ≥0∞) ≤ V := by rw [hU]; exact le_top
      refine ((hR.chartClock_spec (by positivity) hS).2.2.1 r ⟨zero_le, le_self_add⟩).mono_of_mem_nhdsWithin ?_
      exact mem_nhdsWithin_of_mem_nhds (mem_of_superset (Iio_mem_nhds (lt_add_one r))
        fun y hy => ⟨zero_le, le_of_lt hy⟩)
    · have hS : ((V.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ V := by rw [ENNReal.coe_toNNReal hU]
      exact ((hR.chartClock_spec (ENNReal.toNNReal_pos hU0.ne' hU) hS).2.2.1.mono fun y hy =>
        ⟨zero_le, IsClockOn.le_toNNReal hU hy⟩) r hr
  · have hstop : contStop η ζ a K = ⊤ := (ENNReal.sub_eq_top_iff.1 hU).1
    have hζ : ζ = ⊤ := top_le_iff.1 (hstop ▸ contStop_le)
    set C := ConformalImage.hcapSet (fillH K) with hCdef
    set t : ℝ≥0 := (M + C / 2).toNNReal with ht
    have htV : (t : ℝ≥0∞) ≤ V := by rw [hU]; exact le_top
    have hge := hR.chartClock_ge htV
    rw [hR.path.hcapSet (by rw [hζ]; exact ENNReal.coe_lt_top)] at hge
    refine ⟨t, ?_⟩
    have h1 : M + C / 2 ≤ t := Real.le_coe_toNNReal _
    have h2 : (0 : ℝ) ≤ a := NNReal.coe_nonneg _
    push_cast at hge
    linarith

/-- **The retained clock relation** (`IsRetainedClock`): the chart path, translated by a real `c`, read in its
inverse relative capacity clock, for any `ψ'` with `ψ'(w + c) = ψ(w)`. -/
theorem isRetainedClock (c : ℝ) {ψ' : ℂ → ℂ} (hψ' : ∀ w, ψ' (w + c) = ψ w) :
    IsRetainedClock η ζ a (O ∪ η '' Icc 0 a) ψ'
      (fun u => contPath (H \ fillH (O ∪ η '' Icc 0 a)) φ η a (contLife η ζ a (O ∪ η '' Icc 0 a))
        (invClock (chartClock (contPath (H \ fillH (O ∪ η '' Icc 0 a)) φ η a
          (contLife η ζ a (O ∪ η '' Icc 0 a)))) (contLife η ζ a (O ∪ η '' Icc 0 a)) u) + c)
      (capLife (chartClock (contPath (H \ fillH (O ∪ η '' Icc 0 a)) φ η a (contLife η ζ a (O ∪ η '' Icc 0 a))))
        (contLife η ζ a (O ∪ η '' Icc 0 a))) := by
  set K := O ∪ η '' Icc 0 a with hK
  set V := contLife η ζ a K with hVdef
  set Γ := contPath (H \ fillH K) φ η a V with hΓ
  have ha := hR.isClockOn
  have hstop : (a : ℝ≥0∞) ≤ contStop η ζ a K := hR.lt_contStop.le
  refine ⟨fun u => a + invClock (chartClock Γ) V u, capLife (chartClock Γ) V, le_rfl,
    fun u hu v hv huv => (add_lt_add_iff_left a).2 (ha.strictMonoOn_invClock hu hv huv), ?_, fun u hu => ?_,
    fun u hu => ?_⟩
  · have h : (fun u => a + invClock (chartClock Γ) V u) '' {s | (s : ℝ≥0∞) ≤ capLife (chartClock Γ) V} =
        {s | a ≤ s ∧ (s : ℝ≥0∞) ≤ contStop η ζ a K} := IsClockOn.image_add_invClock (ζ := contStop η ζ a K) ha hstop
    rw [h]
    exact contSet_eq.symm
  · rw [hψ', show ψ (Γ (invClock (chartClock Γ) V u)) = η (a + invClock (chartClock Γ) V u) from
      (hR.contPath_spec (ha.invClock_spec hu).1).2]
  · have h1 : Γ (invClock (chartClock Γ) V u) ∈ Hbar := (hR.contPath_spec (ha.invClock_spec hu).1).1
    show 0 ≤ (Γ (invClock (chartClock Γ) V u) + c).im
    rw [Complex.add_im, Complex.ofReal_im, add_zero]
    exact h1

/-- **The relative capacity clock is continuous** on all times (it is constant after a finite end). -/
theorem continuous_chartClock :
    Continuous (chartClock (contPath (H \ fillH (O ∪ η '' Icc 0 a)) φ η a (contLife η ζ a (O ∪ η '' Icc 0 a)))) := by
  set K := O ∪ η '' Icc 0 a with hK
  set V := contLife η ζ a K with hVdef
  set Γ := contPath (H \ fillH K) φ η a V with hΓ
  have hclk := hR.isClockOn
  by_cases hV : V = ⊤
  · have h := hclk.continuousOn
    exact continuousOn_univ.1 (h.mono fun r _ => show (r : ℝ≥0∞) ≤ V by rw [hV]; exact le_top)
  · set c := V.toNNReal with hc
    have hcV : (c : ℝ≥0∞) = V := ENNReal.coe_toNNReal hV
    have hΓc : ∀ s, c ≤ s → Γ s = Γ c := fun s hs => by
      rw [hΓ, contPath_of_le (hcV ▸ ENNReal.coe_le_coe.2 hs), contPath_of_le hcV.symm.le]
    have hconst : ∀ r, chartClock Γ r = chartClock Γ (min r c) := by
      intro r
      rcases le_total r c with h | h
      · rw [min_eq_left h]
      · rw [min_eq_right h]
        unfold chartClock
        congr 3
        apply Subset.antisymm
        · rintro _ ⟨s, hs, rfl⟩
          by_cases hsc : s ≤ c
          · exact ⟨s, ⟨hs.1, hsc⟩, rfl⟩
          · exact ⟨c, ⟨zero_le, le_rfl⟩, (hΓc s (le_of_not_ge hsc)).symm⟩
        · exact image_mono (Icc_subset_Icc_right h)
    rw [show chartClock Γ = fun r => chartClock Γ (min r c) from funext hconst]
    exact hclk.continuousOn.comp_continuous (continuous_id.min continuous_const) fun r =>
      show ((min r c : ℝ≥0) : ℝ≥0∞) ≤ V from hcV ▸ ENNReal.coe_le_coe.2 (min_le_right _ _)

end IsRetCont

end Supp7

end InteractingSLE
