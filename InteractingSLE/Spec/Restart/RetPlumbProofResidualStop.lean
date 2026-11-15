/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.RetPlumbProofInputsTrace

/-!
# Reading boundary survival from a closed past interval

Packet PROVE-RETPLUMB. For a closed contact set, survival at a positive
continuation time only requires the original lifetime and avoidance through
the current endpoint. The contact set is arbitrary, so the real line in
`retStopSet` is retained.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.Restart.RetAux79

open Supp7

/-- For a continuous path at the current endpoint and a closed contact set,
strict continuation survival is determined by the past including that endpoint. -/
theorem lt_contStop_iff_noContact_Ioc {η : ℝ≥0 → ℂ} {ζ : ℝ≥0∞}
    {a b : ℝ≥0} {K : Set ℂ} (hab : a < b) (hc : ContinuousAt η b) (hK : IsClosed K) :
    (b : ℝ≥0∞) < contStop η ζ a K ↔
      (b : ℝ≥0∞) < ζ ∧ ∀ s : ℝ≥0, a < s → s ≤ b → η s ∉ K := by
  constructor
  · intro hb
    refine ⟨hb.trans_le contStop_le, fun s has hsb => ?_⟩
    exact notMem_of_lt_contStop has ((ENNReal.coe_le_coe.2 hsb).trans_lt hb)
  · rintro ⟨hbζ, hno⟩
    have hη : ∀ᶠ s in 𝓝 b, η s ∈ Kᶜ :=
      hc.eventually (hK.isOpen_compl.mem_nhds (hno b hab le_rfl))
    have hζ : ∀ᶠ s : ℝ≥0 in 𝓝 b, (s : ℝ≥0∞) < ζ :=
      ENNReal.continuous_coe.continuousAt.eventually (Iio_mem_nhds hbζ)
    have hb : (b : ℝ≥0∞) < contStop η ζ b K :=
      lt_contStop_of_eventually ((hη.and hζ).filter_mono nhdsWithin_le_nhds |>.mono
        fun _ hs => ⟨hs.2.le, hs.1⟩)
    obtain ⟨s, hs, hbs⟩ := lt_biSup_iff.1 hb
    apply hbs.trans_le
    apply le_contStop
    refine ⟨hab.le.trans hs.1, hs.2.1, fun t hat hts => ?_⟩
    by_cases htb : t ≤ b
    · exact hno t hat htb
    · exact hs.2.2 t (lt_of_not_ge htb) hts

/-- Two endpoint-continuous paths with the same past and the same live record
have the same survival event, for any fixed closed contact set. -/
theorem lt_contStop_iff_of_prefix_eq {η η' : ℝ≥0 → ℂ} {ζ ζ' : ℝ≥0∞}
    {a b : ℝ≥0} {K : Set ℂ} (hab : a < b)
    (hc : ContinuousAt η b) (hc' : ContinuousAt η' b) (hK : IsClosed K)
    (he : ∀ s ≤ b, η s = η' s)
    (hζ : (b : ℝ≥0∞) < ζ ↔ (b : ℝ≥0∞) < ζ') :
    (b : ℝ≥0∞) < contStop η ζ a K ↔ (b : ℝ≥0∞) < contStop η' ζ' a K := by
  rw [lt_contStop_iff_noContact_Ioc hab hc hK,
    lt_contStop_iff_noContact_Ioc hab hc' hK, hζ]
  exact and_congr_right fun _ => forall_congr' fun s => imp_congr_right fun _ =>
    forall_congr' fun hs => by rw [he s hs]

end InteractingSLE.Restart.RetAux79
