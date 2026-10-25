import SupercriticalLQGUniqueness.B2.PfeAxioms.TightLiminfUpper

 


set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem measure_limsup_lt_of_uniform_lower_tail
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Y : ℕ → Ω → ℝ≥0∞) (a b δ : ℝ≥0∞) (hba : b < a)
    (hY : ∀ n, P {ω | Y n ω < a} ≤ δ) :
    P {ω | limsup (fun n => Y n ω) atTop < b} ≤ δ := by
  let S (n : ℕ) : Set Ω := {ω | Y n ω < a}
  let T (N : ℕ) : Set Ω := ⋂ n ≥ N, S n
  have hTmono : Monotone T := by
    intro N N' hNN' ω hω
    simp only [T, mem_iInter] at hω ⊢
    intro n hn
    exact hω n (le_trans hNN' hn)
  have hsub : {ω | limsup (fun n => Y n ω) atTop < b} ⊆ ⋃ N, T N := by
    intro ω hω
    have ha : limsup (fun n => Y n ω) atTop < a := hω.trans hba
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (eventually_lt_of_limsup_lt ha)
    exact mem_iUnion.2 ⟨N, mem_iInter.2 fun n => mem_iInter.2 fun hn => hN n hn⟩
  have hTN : ∀ N, P (T N) ≤ δ := by
    intro N
    exact (measure_mono (by
      intro ω hω
      exact (mem_iInter.1 (mem_iInter.1 hω N) le_rfl))).trans (hY N)
  calc
    P {ω | limsup (fun n => Y n ω) atTop < b} ≤ P (⋃ N, T N) := measure_mono hsub
    _ = ⨆ N, P (T N) := hTmono.measure_iUnion
    _ ≤ δ := iSup_le hTN

theorem uniform_lower_tail_of_ae_limsup_le
    {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Y : ι → ℕ → Ω → ℝ≥0∞) (Z : ι → Ω → ℝ≥0∞)
    (M η : ℝ) (hM : 0 < M)
    (hY : ∀ i n, P {ω | Y i n ω < ENNReal.ofReal M} ≤ ENNReal.ofReal η)
    (hZ : ∀ i, ∀ᵐ ω ∂P, limsup (fun n => Y i n ω) atTop ≤ Z i ω) :
    ∀ i, P {ω | Z i ω < ENNReal.ofReal (M / 2)} ≤ ENNReal.ofReal η := by
  intro i
  have hsub : ∀ᵐ ω ∂P,
      Z i ω < ENNReal.ofReal (M / 2) →
        limsup (fun n => Y i n ω) atTop < ENNReal.ofReal (M / 2) :=
    (hZ i).mono fun ω hω hlt => hω.trans_lt hlt
  calc
    P {ω | Z i ω < ENNReal.ofReal (M / 2)}
      ≤ P {ω | limsup (fun n => Y i n ω) atTop < ENNReal.ofReal (M / 2)} :=
        measure_mono_ae hsub
    _ ≤ ENNReal.ofReal η :=
      measure_limsup_lt_of_uniform_lower_tail P (Y i)
        (ENNReal.ofReal M) (ENNReal.ofReal (M / 2)) (ENNReal.ofReal η)
        ((ENNReal.ofReal_lt_ofReal_iff hM).mpr (by linarith)) (hY i)

end SupercriticalLQGUniqueness.B2.PfeAxioms
