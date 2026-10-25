import SupercriticalLQGUniqueness.B2.PfeAxioms.TightLiminfFinite

 

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Set Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem measure_liminf_gt_of_uniform_upper_tail
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Y : ℕ → Ω → ℝ≥0∞) (a b δ : ℝ≥0∞) (hab : a < b)
    (hY : ∀ n, P {ω | a < Y n ω} ≤ δ) :
    P {ω | b < liminf (fun n => Y n ω) atTop} ≤ δ := by
  let S (n : ℕ) : Set Ω := {ω | a < Y n ω}
  let T (N : ℕ) : Set Ω := ⋂ n ≥ N, S n
  have hTmono : Monotone T := by
    intro N N' hNN' ω hω
    simp only [T, mem_iInter] at hω ⊢
    intro n hn
    exact hω n (le_trans hNN' hn)
  have hsub : {ω | b < liminf (fun n => Y n ω) atTop} ⊆ ⋃ N, T N := by
    intro ω hω
    have ha : a < liminf (fun n => Y n ω) atTop := hab.trans hω
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (eventually_lt_of_lt_liminf ha)
    exact mem_iUnion.2 ⟨N, mem_iInter.2 fun n => mem_iInter.2 fun hn => hN n hn⟩
  have hTN : ∀ N, P (T N) ≤ δ := by
    intro N
    exact (measure_mono (by
      intro ω hω
      exact (mem_iInter.1 (mem_iInter.1 hω N) le_rfl))).trans (hY N)
  calc
    P {ω | b < liminf (fun n => Y n ω) atTop} ≤ P (⋃ N, T N) := measure_mono hsub
    _ = ⨆ N, P (T N) := hTmono.measure_iUnion
    _ ≤ δ := iSup_le hTN

end SupercriticalLQGUniqueness.B2.PfeAxioms
