import SupercriticalLQGUniqueness.B2.PfeAxioms.TightLiminfUpper

 


set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem uniform_upper_tail_of_ae_le_liminf
    {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Y : ι → ℕ → Ω → ℝ≥0∞) (Z : ι → Ω → ℝ≥0∞)
    (M η : ℝ) (hM : 0 < M)
    (hY : ∀ i n, P {ω | ENNReal.ofReal M < Y i n ω} ≤ ENNReal.ofReal η)
    (hZ : ∀ i, ∀ᵐ ω ∂P, Z i ω ≤ liminf (fun n => Y i n ω) atTop) :
    ∀ i, P {ω | ENNReal.ofReal (2 * M) < Z i ω} ≤ ENNReal.ofReal η := by
  intro i
  have hsub : ∀ᵐ ω ∂P,
      ENNReal.ofReal (2 * M) < Z i ω →
        ENNReal.ofReal (2 * M) < liminf (fun n => Y i n ω) atTop :=
    (hZ i).mono fun ω hω hlt => hlt.trans_le hω
  calc
    P {ω | ENNReal.ofReal (2 * M) < Z i ω}
      ≤ P {ω | ENNReal.ofReal (2 * M) <
          liminf (fun n => Y i n ω) atTop} := measure_mono_ae hsub
    _ ≤ ENNReal.ofReal η :=
      measure_liminf_gt_of_uniform_upper_tail P (Y i)
        (ENNReal.ofReal M) (ENNReal.ofReal (2 * M)) (ENNReal.ofReal η)
        ((ENNReal.ofReal_lt_ofReal_iff (by linarith : 0 < 2 * M)).mpr
          (by linarith)) (hY i)

end SupercriticalLQGUniqueness.B2.PfeAxioms
