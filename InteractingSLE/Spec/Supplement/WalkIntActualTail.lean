/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntFillRetained

/-!
# Selecting a finite prefix of a terminal infinite ordinary piece

Regularity gives a transient generating trace. The existing proper boundary
extension moves that trace a bounded distance, so its late physical tail
misses a fixed ball around any point. The selected prefix is an actual
own-time truncation; no chronological history certificate is assumed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.WalkIntActual

/-- A regular infinite piece in a proper boundary chart is locally already
contained in some finite own-time prefix, at every physical point. -/
theorem exists_tipSet_prefix_collar {c : Chart} {W : ℝ≥0 → ℝ}
    (hc : GW1P.HasProperBdryExt c) (hreg : GW1P.PieceRegular W ⊤) (p : ℂ) :
    ∃ τ : ℝ≥0, c.tipSet W ⊤ ∩ ball p 1 ⊆ c.tipSet W τ := by
  obtain ⟨f, C, hf, hC⟩ := hc
  obtain ⟨hW0, hWc, α, hα, htrans⟩ := hreg
  have hαH (t : ℝ≥0) : α t ∈ Hbar :=
    Sec7.IsGeneratingTrace.mem_Hbar hα
      (hWc.mono fun _ _ => mem_ofPred.2 le_top) hW0 le_top
  have hlim (t : ℝ≥0) :
      Tendsto (fun y : ℝ => c.2.1
        (QuantumZipper.fwdMapInv (fun r : ℝ => W r.toNNReal) t (y * I)))
        (𝓝[>] 0) (𝓝 (f (α t))) := by
    simpa only [min_top_right, ENNReal.toNNReal_coe] using
      CounterflowRange.tendsto_tip_stopped_of_tendsto hα hWc hW0
        (t := t) le_top (hf _ (hαH t))
  obtain ⟨τ, hτ⟩ := eventually_atTop.1
    ((htrans rfl).eventually_ge_atTop (‖p‖ + C + 1))
  refine ⟨τ, ?_⟩
  rintro z ⟨⟨t, _, htz⟩, hzp⟩
  have hzt : f (α t) = z := tendsto_nhds_unique (hlim t) htz
  have htτ : t ≤ τ := by
    apply le_of_not_gt
    intro hlate
    have hlarge := hτ t hlate.le
    have hdist := hC (α t) (hαH t)
    have hnorm := norm_sub_norm_le (α t) (f (α t))
    rw [norm_sub_rev, hzt] at hnorm
    rw [hzt] at hdist
    have hsmall : ‖z‖ < ‖p‖ + 1 := by
      have hb : ‖z - p‖ < 1 := by simpa only [mem_ball, dist_eq_norm] using hzp
      have hn := norm_add_le (z - p) p
      rw [sub_add_cancel] at hn
      linarith only [hb, hn]
    linarith only [hlarge, hdist, hnorm, hsmall]
  exact ⟨t, ENNReal.coe_le_coe.2 htτ, htz⟩

end InteractingSLE.Theorem14.WalkIntActual
