import QuantumZipper.Statements.Thm18Off
import QuantumZipper.Proofs.Thm18.Assembly

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# D74: the rational-time curve `curveOf W` is the curve `η([0,∞))`

Fidelity lemma for `Statements/Thm18Off.lean`: for a trace that is continuous on `[0,∞)` and
tends to `∞` (Sheffield's `η`, arXiv:1012.4797 p. 26; `IsSimpleChord`, Rohde–Schramm),
`curveOf W = closure (range (trace W ∘ ℚ≥0)) = trace W '' [0,∞)`.

**Own elementary argument** (no source needed; standard point-set topology): the nonnegative
rationals are dense in `[0,∞)`, so by continuity the two closures agree; the image is closed
because it is contained in the compact `trace W '' [0,N]` union the closed set
`{‖w‖ ≥ ‖z‖ + 1}` for large `N` (properness from `‖trace W t‖ → ∞`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace D74

theorem curveOf_eq_image {W : ℝ → ℝ} (hc : ContinuousOn (trace W) (Ici 0))
    (hinf : Tendsto (fun t => ‖trace W t‖) atTop atTop) : curveOf W = trace W '' Ici 0 := by
  set S := trace W '' Ici (0 : ℝ) with hSdef
  -- the image is closed
  have hS : IsClosed S := by
    refine isClosed_of_closure_subset fun z hz => ?_
    obtain ⟨N, hN⟩ := (tendsto_atTop.1 hinf (‖z‖ + 1)).exists_forall_of_atTop
    have hK : IsCompact (trace W '' Icc 0 (max N 0)) :=
      isCompact_Icc.image_of_continuousOn (hc.mono Icc_subset_Ici_self)
    have hsub : S ⊆ trace W '' Icc 0 (max N 0) ∪ {w | ‖z‖ + 1 ≤ ‖w‖} := by
      rintro _ ⟨t, ht, rfl⟩
      by_cases htN : t ≤ max N 0
      · exact Or.inl ⟨t, ⟨ht, htN⟩, rfl⟩
      · exact Or.inr (hN t ((le_max_left N 0).trans (not_le.1 htN).le))
    have hcl : IsClosed (trace W '' Icc 0 (max N 0) ∪ {w | ‖z‖ + 1 ≤ ‖w‖}) :=
      hK.isClosed.union (isClosed_le continuous_const continuous_norm)
    rcases closure_minimal hsub hcl hz with h | h
    · exact image_mono Icc_subset_Ici_self h
    · exfalso
      have h' : ‖z‖ + 1 ≤ ‖z‖ := h
      linarith
  have hrange : (range fun q : ℚ≥0 => trace W (q : ℝ)) ⊆ S := by
    rintro _ ⟨q, rfl⟩
    exact ⟨q, mem_Ici.2 (NNRat.cast_nonneg (α := ℝ) q), rfl⟩
  refine Subset.antisymm (closure_minimal hrange hS) ?_
  rintro _ ⟨t, ht, rfl⟩
  set R := {r : ℝ | 0 ≤ r ∧ ∃ q : ℚ, (q : ℝ) = r} with hR
  have hRsub : R ⊆ Ici 0 := fun r hr => hr.1
  have htR : t ∈ closure R := by
    refine Metric.mem_closure_iff.2 fun ε hε => ?_
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show t < t + ε by linarith)
    refine ⟨q, ⟨(le_of_lt (lt_of_le_of_lt ht hq1)), q, rfl⟩, ?_⟩
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith
  have himg : trace W '' R ⊆ range fun q : ℚ≥0 => trace W (q : ℝ) := by
    rintro _ ⟨r, ⟨hr0, q, rfl⟩, rfl⟩
    have hq : 0 ≤ q := by exact_mod_cast hr0
    exact ⟨⟨q, hq⟩, by simp⟩
  exact closure_mono himg (((hc t ht).mono hRsub).mem_closure_image htR)

/-- **The curve of the Theorem 1.8 sample**: a.s. `curveOf` of the SLE_{γ²} driver is the
trace image `η([0,∞))`. -/
theorem ae_curveOf_drive_eq {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} {Y : Ω → FieldSample}
    (hS : Thm18Setting γ P B Y) :
    ∀ᵐ ω ∂P, curveOf (drive (γ ^ 2) B ω) = sleTrace (γ ^ 2) B ω '' Ici 0 := by
  filter_upwards [(thm18Inputs_of_setting hS).2.2] with ω hω
  exact curveOf_eq_image hω.1.2.1 hω.1.2.2.2.2

end D74
end Thm18Asm
end QuantumZipper
