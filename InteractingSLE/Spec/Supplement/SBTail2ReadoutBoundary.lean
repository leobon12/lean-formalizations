/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB4SwitchRegularity
import InteractingSLE.Spec.Supplement.WalkStageLocalMeas

/-!
# Boundary readout of a finite physical schedule piece

Packet PROVE-T14-SBTAIL2, third continuation. A measurable approximation from
inside the upper half-plane reaches every boundary point of the closed upper
half-plane. The already measurable stopped-driver trace includes its finite
endpoint, so its inverse-chart boundary readout parametrizes the whole stopped
physical piece. This includes real contacts and zero-duration pieces.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Complex
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Readout

/-- Move a point into `ℍ`, retaining its real coordinate and clipping its
imaginary coordinate at zero before adding a positive height. -/
def raiseH (n : ℕ) (z : ℂ) : ℂ :=
  (z.re : ℂ) + ((max z.im 0 + 1 / ((n : ℝ) + 1) : ℝ) : ℂ) * I

theorem continuous_raiseH (n : ℕ) : Continuous (raiseH n) :=
  (continuous_ofReal.comp continuous_re).add
    ((continuous_ofReal.comp
      ((continuous_im.max continuous_const).add continuous_const)).mul_const I)

theorem raiseH_mem (n : ℕ) (z : ℂ) : raiseH n z ∈ H := by
  change 0 < (raiseH n z).im
  simp only [raiseH, add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re,
    mul_zero, add_zero, zero_add]
  exact add_pos_of_nonneg_of_pos (le_max_right _ _) (by positivity)

/-- The approximation tends to its boundary point from inside `ℍ`. -/
theorem tendsto_raiseH {z : ℂ} (hz : z ∈ Hbar) :
    Tendsto (fun n : ℕ => raiseH n z) atTop (𝓝[H] z) := by
  apply tendsto_nhdsWithin_iff.2
  refine ⟨?_, Eventually.of_forall fun n => raiseH_mem n z⟩
  have hi : Tendsto (fun n : ℕ => z.im + 1 / ((n : ℝ) + 1)) atTop (𝓝 z.im) := by
    simpa only [add_zero] using
      (tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ => z.im + 1 / ((n : ℝ) + 1)) atTop (𝓝 (z.im + 0)))
  simpa only [raiseH, max_eq_left (show 0 ≤ z.im from hz), re_add_im] using
    (tendsto_const_nhds.add (((continuous_ofReal.tendsto z.im).comp hi).mul_const I) :
      Tendsto (fun n : ℕ => (z.re : ℂ) + (z.im + 1 / ((n : ℝ) + 1) : ℝ) * I)
        atTop (𝓝 ((z.re : ℂ) + (z.im : ℂ) * I)))

/-- Any physical boundary readout of the measurable stopped-driver trace is
the continuous frozen physical path with exactly the full finite tip set. -/
theorem continuous_range_of_stopped_readout {c : Chart} {W : ℝ≥0 → ℝ} {T : ℝ≥0∞}
    {f : ℂ → ℂ} (hf : ∀ z ∈ Hbar, Tendsto c.2.1 (𝓝[H] z) (𝓝 (f z)))
    (hW : GW1P.PieceRegular W T) (hT : T ≠ ⊤) {a : ℝ≥0 → ℂ}
    (ha : ∀ t, a t = f ((LP.drivingTrace (T, W)).2 t)) :
    Continuous a ∧ range a = c.tipSet (fun r : ℝ≥0 => W (min (r : ℝ≥0∞) T).toNNReal) T := by
  obtain ⟨hW0, hWc, α, hα, _⟩ := hW
  have htr := LP.drivingTrace_eq hα
    (hWc.mono fun s ht => show (s : ℝ≥0∞) ≤ T from ht.le) hW0 (fun _ _ => rfl)
  have he : ∀ t, a t = f (α (min t T.toNNReal)) := by
    intro t
    rw [ha, htr]
    change f (α (min (t : ℝ≥0∞) T).toNNReal) = f (α (min t T.toNNReal))
    have he : min (t : ℝ≥0∞) T = ((min t T.toNNReal : ℝ≥0) : ℝ≥0∞) := by
      rw [ENNReal.coe_min, ENNReal.coe_toNNReal hT]
    rw [he, ENNReal.toNNReal_coe]
  have hm : ∀ t : ℝ≥0, ((min t T.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ T := fun t => by
    rw [ENNReal.coe_min, ENNReal.coe_toNNReal hT]
    exact min_le_right _ _
  have hH : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ T → α t ∈ Hbar := fun t ht =>
    Sec7.IsGeneratingTrace.mem_Hbar hα
      (hWc.mono fun s hs => show (s : ℝ≥0∞) ≤ T from hs.le) hW0 ht
  refine ⟨?_, ?_⟩
  · have hcont := (GW1P.continuousOn_of_tendsto hf).comp_continuous
      (hα.2.1.comp_continuous (continuous_id.min continuous_const) hm)
      (fun t => hH _ (hm t))
    exact hcont.congr fun t => (he t).symm
  · rw [CounterflowRange.tipSet_stopped_eq_of_tendsto hα hWc hW0
      (fun t ht => hf _ (hH t ht))]
    ext z
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨_, ⟨_, hm t, rfl⟩, (he t).symm⟩
    · rintro ⟨_, ⟨t, ht, rfl⟩, rfl⟩
      refine ⟨t, ?_⟩
      rw [he, min_eq_left (ENNReal.coe_le_coe.1 ?_)]
      rw [ENNReal.coe_toNNReal hT]
      exact ht

end InteractingSLE.Theorem14.SB.Readout
