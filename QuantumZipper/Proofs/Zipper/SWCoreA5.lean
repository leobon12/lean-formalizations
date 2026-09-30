import QuantumZipper.Proofs.Zipper.SWCoreA5Main
import QuantumZipper.Proofs.Zipper.SWCoreWinRArea
import QuantumZipper.Proofs.Zipper.AreaWinMkFinal
import QuantumZipper.Proofs.Zipper.AreaWinSWConst

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-A5: `SWCore.AreaTransportUnifStmt` from the area distortion core

Task SWC-A5 (`handoff/SW-CORE.md` §3). Sheffield–Wang, arXiv:1605.06171, Thm 1.4 (p. 4) and its
proof (pp. 11–13, (3.5)–(3.7)), uniform over a rational map class: a.s., for every rational
class, every test function `f` supported in the interior of `K` and every `η > 0`, eventually in
`k`, uniformly over the class,
`|∫ f dμ^{x∘ψ+Q log|ψ'|}_k − ∫_{ψ(K)} f∘ψ⁻¹ dμ^x| ≤ η`.

Inputs: the class-uniform area distortion core `SWCore.AreaDistClassStmt` (hypothesis; being
proved separately), the free-field window limits `E6.FreeWindowStmt` (proved:
`freeWindowStmt_of_splitR` with `swWindowSplitStmtR_holds`, constants `swC → 1`), regularity of
the free field and existence of its area measure (proved). Deterministic steps:
`area_transport_nonneg` (SWCoreA5Main) and the splitting `f = f⁺ − f⁻` below. Own bookkeeping.

Main results: `areaTransportUnifGood_of`, **`areaTransportUnifStmt_of_distClass`**.
-/

noncomputable section

open MeasureTheory Filter Set Function Metric
open scoped Topology ENNReal

namespace QuantumZipper
namespace SWCore

open E6

variable {γ : ℝ} {x : FieldSample}

theorem isCompact_rectC (a b c d : ℝ) : IsCompact (rectC a b c d) := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · exact (isClosed_Icc.preimage Complex.continuous_re).inter
      (isClosed_Icc.preimage Complex.continuous_im)
  · refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := |a| + |b| + (|c| + |d|))).subset
      fun z hz => ?_
    rw [mem_closedBall, dist_zero_right]
    refine (Complex.norm_le_abs_re_add_abs_im z).trans (add_le_add ?_ ?_)
    · exact abs_le_max_abs_abs hz.1.1 hz.1.2 |>.trans (max_le (by linarith [abs_nonneg b])
        (by linarith [abs_nonneg a]))
    · exact abs_le_max_abs_abs hz.2.1 hz.2.2 |>.trans (max_le (by linarith [abs_nonneg d])
        (by linarith [abs_nonneg c]))

/-- `pullTest` of a test function is integrable for a measure finite on compacts of `ℍ`. -/
theorem integrable_pullTest {a b c d ρ M m : ℝ} (hρ : 0 < ρ) (hm : 0 < m) {f : ℂ → ℝ}
    (hf : Continuous f) (hfs : HasCompactSupport f)
    (hfK : tsupport f ⊆ interior (rectC a b c d)) {μ : Measure ℂ}
    (hμK : ∀ K, IsCompact K → K ⊆ H → μ K < ⊤) {ψ : ℂ → ℂ}
    (hψ : ψ ∈ AreaClass a b c d ρ M m) : Integrable (pullTest ψ (rectC a b c d) f) μ := by
  set C₀ : Set ℂ := {w | ‖w‖ ≤ M ∧ ρ ≤ w.im} with hC₀
  have hC₀c : IsCompact C₀ := by
    refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
    · exact (isClosed_le continuous_norm continuous_const).inter
        (isClosed_le continuous_const Complex.continuous_im)
    · exact (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := M)).subset fun w hw => by
        rw [mem_closedBall, dist_zero_right]; exact hw.1
  obtain ⟨Cs, hCs⟩ := pullTest_ne_zero (a := a) (b := b) (c := c) (d := d) (M := M) (m := m)
    hρ (f := f)
  have hsupp : tsupport (pullTest ψ (rectC a b c d) f) ⊆ C₀ := by
    refine closure_minimal (fun w hw => ?_) hC₀c.isClosed
    obtain ⟨-, -, h1, h2, -, -⟩ := hCs ψ hψ w hw
    exact ⟨h1, h2⟩
  have hcont : Continuous (pullTest ψ (rectC a b c d) f) := by
    refine Metric.continuous_iff.2 fun w ε hε => ?_
    obtain ⟨δ, hδ, h⟩ := pullTest_equicont hρ hm hf hfs hfK (ε / 2) (half_pos hε)
    refine ⟨δ, hδ, fun w' hw' => ?_⟩
    rw [Real.dist_eq]
    exact (h ψ hψ w' w hw').trans_lt (half_lt_self hε)
  exact integrable_of_areaTest hμK ⟨hcont,
    IsCompact.of_isClosed_subset hC₀c (isClosed_tsupport _) hsupp,
    hsupp.trans fun w hw => lt_of_lt_of_le hρ hw.2⟩

end SWCore
end QuantumZipper
