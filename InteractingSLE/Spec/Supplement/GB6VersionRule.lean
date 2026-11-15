/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6VersionStops

/-!
# Readable stopping rules for the relative driver

The events below are Borel events of a record and the driver prefix even on
irregular paths. On a continuous sample they describe a closed-level entrance.
Thus they can be used in the completed-filtration clause of `IsGB6RelVersion`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE.Supp8.GB6.RelDrv.Version

open Exist.StagedLaw

/-- A scalar observable read from a record and a driver path. -/
abbrev GaugeReadout := ℝ≥0 → RecData × (ℝ≥0 → ℝ) → ℝ

/-- Causality of the readout, including its value at the endpoint. -/
def IsCausal (G : GaugeReadout) : Prop :=
  ∀ t r w w', (∀ u ≤ t, w u = w' u) → G t (r, w) = G t (r, w')

/-- Countable closed-entrance test, capped at `c`. -/
def prefixHitSet (G : GaugeReadout) (ε : RecData → ℝ) (c t : ℝ≥0) :
    Set (RecData × (ℝ≥0 → ℝ)) :=
  {p | c ≤ t ∨ ∀ n : ℕ, ∃ q : ℚ≥0, (q : ℝ≥0) ≤ t ∧
    G q p < ε p.1 + 1 / ((n : ℝ) + 1)}

theorem measurableSet_prefixHitSet {G : GaugeReadout} (hG : ∀ t, Measurable (G t))
    {ε : RecData → ℝ} (hε : Measurable ε) (c t : ℝ≥0) :
    MeasurableSet (prefixHitSet G ε c t) := by
  have he : prefixHitSet G ε c t =
      {p : RecData × (ℝ≥0 → ℝ) | c ≤ t} ∪
      ⋂ n : ℕ, ⋃ q : ℚ≥0, ⋃ (_ : (q : ℝ≥0) ≤ t),
        {p | G q p < ε p.1 + 1 / ((n : ℝ) + 1)} := by
    ext p
    simp only [prefixHitSet, mem_ofPred_eq, mem_union, mem_iInter, mem_iUnion, exists_prop]
  rw [he]
  exact (MeasurableSet.const _).union (MeasurableSet.iInter fun n =>
    MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun _ =>
      measurableSet_lt (hG q) ((hε.comp measurable_fst).add_const _))

theorem isDetUpTo_prefixHitSet {G : GaugeReadout} (hG : IsCausal G)
    (ε : RecData → ℝ) (c t : ℝ≥0) : IsDetUpTo t (prefixHitSet G ε c t) := by
  intro r w w' hw
  change (c ≤ t ∨ _) ↔ (c ≤ t ∨ _)
  apply or_congr_right
  apply forall_congr'
  intro n
  apply exists_congr
  intro q
  apply and_congr_right
  intro hq
  rw [hG q r w w' (fun u hu => hw u (hu.trans hq))]

/-- A continuous function admits rational times approaching any positive
prefix endpoint from the left. -/
theorem exists_nnrat_lt_of_continuous {g : ℝ≥0 → ℝ} (hg : Continuous g)
    {v : ℝ≥0} (hv : 0 < v) {a : ℝ} (ha : g v < a) :
    ∃ q : ℚ≥0, (q : ℝ≥0) < v ∧ g q < a := by
  have he : ∀ᶠ u in 𝓝 v, g u < a := hg.continuousAt.eventually (gt_mem_nhds ha)
  obtain ⟨δ, hδ, hb⟩ := Metric.mem_nhds_iff.1 he
  obtain ⟨q, hq0, hqv⟩ := exists_rat_btwn
    (show max (0 : ℝ) ((v : ℝ) - δ) < v from max_lt (by exact_mod_cast hv) (by linarith))
  have hqpos : (0 : ℝ) ≤ q := (le_max_left _ _).trans hq0.le
  have hcoe : (((q.toNNRat : ℚ≥0) : ℝ≥0) : ℝ) = q := by
    rw [coe_toNNRat_eq, Real.coe_toNNReal _ hqpos]
  refine ⟨q.toNNRat, ?_, hb ?_⟩
  · exact_mod_cast (hcoe ▸ hqv)
  · rw [mem_ball, NNReal.dist_eq, hcoe, abs_lt]
    have := le_max_right (0 : ℝ) ((v : ℝ) - δ)
    constructor <;> linarith

/-- The Borel prefix test gives the exact entrance event provided the readout
agrees with the scalar gauge through the stop. Values after the stop need not
agree and need not be continuous. -/
theorem mem_prefixHitSet_iff {G : GaugeReadout} {ε : RecData → ℝ}
    {r : RecData} {w : ℝ≥0 → ℝ} {g : ℝ≥0 → ℝ} (hg : Continuous g)
    {c : ℝ≥0} (hc : 0 < c) (h0 : ε r < g 0)
    (hread : ∀ u ≤ gaugeStop g (ε r) c, G u (r, w) = g u) (t : ℝ≥0) :
    (r, w) ∈ prefixHitSet G ε c t ↔ gaugeStop g (ε r) c ≤ t := by
  have hv : 0 < gaugeStop g (ε r) c := gaugeStop_pos hg hc h0
  change (c ≤ t ∨ _) ↔ _
  by_cases hct : c ≤ t
  · exact iff_of_true (Or.inl hct) ((gaugeStop_le _ _ _).trans hct)
  have htc : t < c := lt_of_not_ge hct
  constructor
  · rintro (h | h)
    · exact False.elim (hct h)
    · by_contra hn
      have htv : t < gaugeStop g (ε r) c := lt_of_not_ge hn
      obtain ⟨a, ha, hmin⟩ := isCompact_Icc.exists_isMinOn
        (show (Icc (0 : ℝ≥0) t).Nonempty from ⟨0, zero_le, zero_le⟩) hg.continuousOn
      have haε : ε r < g a := by
        by_contra hna
        have := (gaugeStop_le_of_le (ha.2.trans htc.le) (not_lt.1 hna)).trans ha.2
        exact (not_le.2 htv) this
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 haε)
      obtain ⟨q, hqt, hq⟩ := h n
      rw [hread q (hqt.trans htv.le)] at hq
      have hm : g a ≤ g q := hmin ⟨zero_le, hqt⟩
      change g q < ε r + 1 / ((n : ℝ) + 1) at hq
      linarith only [hn, hq, hm]
  · intro hvt
    right
    intro n
    have hhit := gaugeStop_mem hg (hvt.trans_lt htc)
    obtain ⟨q, hqv, hq⟩ := exists_nnrat_lt_of_continuous hg hv
      (show g (gaugeStop g (ε r) c) < ε r + 1 / ((n : ℝ) + 1) by
        exact lt_of_le_of_lt hhit (lt_add_of_pos_right _ (by positivity)))
    refine ⟨q, hqv.le.trans hvt, ?_⟩
    rw [hread q hqv.le]
    exact hq

section Measurable

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {g : ℝ≥0 → Ω → ℝ}

/-- Capped closed-level entrances of measurable continuous scalar gauges are
measurable, using the host library's continuous hitting-time theorem. -/
theorem measurable_gaugeStop (hg : ∀ t, Measurable (g t))
    (hc : ∀ ω, Continuous (fun t => g t ω)) {ε : Ω → ℝ} (hε : Measurable ε)
    (c : ℝ≥0) : Measurable fun ω => gaugeStop (g · ω) (ε ω) c := by
  let 𝓕 : Filtration ℝ≥0 mΩ := Filtration.const ℝ≥0 mΩ le_rfl
  have hs := QuantumZipper.ItoLite.isStoppingTime_hittingBtwn_of_isClosed
    (𝓕 := 𝓕) (U := fun t ω => g t ω - ε ω) (fun t => (hg t).sub hε)
    (fun ω => (hc ω).sub continuous_const) (K := Iic (0 : ℝ)) isClosed_Iic c
  have he : (fun ω => gaugeStop (g · ω) (ε ω) c) =
      fun ω => (hittingBtwn (fun t ω => g t ω - ε ω) (Iic 0) 0 c ω : ℝ≥0) := by
    funext ω
    rfl
  rw [he]
  exact ENNReal.measurable_toNNReal.comp hs.measurable'

end Measurable

end InteractingSLE.Supp8.GB6.RelDrv.Version
