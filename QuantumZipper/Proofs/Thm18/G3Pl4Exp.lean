import QuantumZipper.Proofs.Thm18.G3Pl4Ptw

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18-G3 step 5T, (G-b), part (b): from pathwise to averaged locality

`g3pl4_expect_le`: if two families of `[0, c]`-valued random variables `F_L`, `G_L` (a.e.
measurable) satisfy, almost surely, `F_L ≤ G_L + ε` for all large `L` and every `ε > 0` (the form of
`g3pl4_phiCap_le_of_agree`), then `E F_L ≤ E G_L + ε` for all large `L`. Proof: dominated
convergence (bound `c`) for the truncated differences `F_L − G_L → 0`, and `F ≤ G + (F − G)`.
Own elementary argument (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace QuantumZipper
namespace R18

/-- **Averaged locality from pathwise locality.** -/
theorem g3pl4_expect_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {F G : ℝ → Ω → ℝ≥0∞} (hF : ∀ L, AEMeasurable (F L) P) (hG : ∀ L, AEMeasurable (G L) P)
    {c : ℝ≥0∞} (hc : c ≠ ⊤) (hbd : ∀ L, ∀ᵐ ω ∂P, F L ω ≤ c)
    (hlim : ∀ᵐ ω ∂P, ∀ ε : ℝ≥0∞, 0 < ε → ∀ᶠ L in atTop, F L ω ≤ G L ω + ε)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∀ᶠ L in atTop, ∫⁻ ω, F L ω ∂P ≤ ∫⁻ ω, G L ω ∂P + ε := by
  have hT : Tendsto (fun L => ∫⁻ ω, (F L ω - G L ω) ∂P) atTop (𝓝 (∫⁻ _, 0 ∂P)) := by
    refine tendsto_lintegral_filter_of_dominated_convergence' (fun _ => c)
      (Eventually.of_forall fun L => (hF L).sub (hG L))
      (Eventually.of_forall fun L => (hbd L).mono fun ω h => tsub_le_self.trans h) ?_ ?_
    · rw [lintegral_const]; exact ENNReal.mul_ne_top hc (measure_ne_top P univ)
    · filter_upwards [hlim] with ω hω
      refine ENNReal.tendsto_nhds_zero.2 fun e he => ?_
      filter_upwards [hω e he] with L hL
      exact tsub_le_iff_left.2 hL
  rw [lintegral_zero] at hT
  filter_upwards [(tendsto_order.1 hT).2 ε hε] with L hL
  calc ∫⁻ ω, F L ω ∂P ≤ ∫⁻ ω, (G L ω + (F L ω - G L ω)) ∂P :=
        lintegral_mono fun ω => le_add_tsub
    _ = ∫⁻ ω, G L ω ∂P + ∫⁻ ω, (F L ω - G L ω) ∂P := lintegral_add_left' (hG L) _
    _ ≤ ∫⁻ ω, G L ω ∂P + ε := add_le_add le_rfl hL.le

end R18
end QuantumZipper
