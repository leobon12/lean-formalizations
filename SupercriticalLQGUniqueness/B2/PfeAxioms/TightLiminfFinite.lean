import SupercriticalLQGUniqueness.B2.Strong.Tight

 


set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Set Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem ae_liminf_lt_top_of_twoSidedTight
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Y : ℕ → Ω → ℝ≥0∞) (hY : IsTwoSidedTight P Y) :
    ∀ᵐ ω ∂P, liminf (fun n => Y n ω) atTop < ∞ := by
  have hbad : P {ω | liminf (fun n => Y n ω) atTop = ∞} = 0 := by
    apply le_antisymm _ bot_le
    refine ENNReal.le_of_forall_pos_le_add fun δ hδ _ => ?_
    obtain ⟨M, hM, htail⟩ := hY.2 (δ : ℝ) (by exact_mod_cast hδ)
    let S (n : ℕ) : Set Ω := {ω | ENNReal.ofReal M < Y n ω}
    let T (N : ℕ) : Set Ω := ⋂ n ≥ N, S n
    have hTmono : Monotone T := by
      intro N N' hNN' ω hω
      simp only [T, mem_iInter] at hω ⊢
      intro n hn
      exact hω n (le_trans hNN' hn)
    have hsub : {ω | liminf (fun n => Y n ω) atTop = ∞} ⊆ ⋃ N, T N := by
      intro ω hω
      change liminf (fun n => Y n ω) atTop = ∞ at hω
      have hMtop : ENNReal.ofReal M < liminf (fun n => Y n ω) atTop := by
        rw [hω]
        exact ENNReal.ofReal_ne_top.lt_top
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (eventually_lt_of_lt_liminf hMtop)
      exact mem_iUnion.2 ⟨N, mem_iInter.2 fun n => mem_iInter.2 fun hn => hN n hn⟩
    have hTN : ∀ N, P (T N) ≤ (δ : ℝ≥0∞) := by
      intro N
      calc
        P (T N) ≤ P (S N) := measure_mono (by
          intro ω hω
          exact (mem_iInter.1 (mem_iInter.1 hω N) le_rfl))
        _ ≤ ENNReal.ofReal (δ : ℝ) := (htail N).1
        _ = (δ : ℝ≥0∞) := by simp
    calc
      P {ω | liminf (fun n => Y n ω) atTop = ∞} ≤ P (⋃ N, T N) := measure_mono hsub
      _ = ⨆ N, P (T N) := hTmono.measure_iUnion
      _ ≤ (δ : ℝ≥0∞) := iSup_le hTN
      _ = 0 + (δ : ℝ≥0∞) := (zero_add _).symm
  apply ae_iff.mpr
  simpa only [not_lt, top_le_iff] using hbad

end SupercriticalLQGUniqueness.B2.PfeAxioms
