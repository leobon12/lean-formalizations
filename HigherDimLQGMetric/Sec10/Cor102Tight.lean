import HigherDimLQGMetric.Frozen.TightOver

/-!
# Tightness under deterministic reindexing

The sharp scale family after a fixed dilation is a subfamily of the original scale family.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory Set
open HigherDimLFPP (Rd)

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Restrict and reindex a tight family using almost-sure equalities at each index. -/
theorem s8c_tightOver_reindex {S T : Set ℝ}
    {X Y : ℝ → Ω → C(Rd d × Rd d, ℝ)} {b : ℝ → ℝ}
    (hT : TightOver P X T) (hb : ∀ r ∈ S, b r ∈ T)
    (heq : ∀ r ∈ S, Y r =ᵐ[P] X (b r)) : TightOver P Y S := by
  have hmap : ∀ r ∈ S, P.map (Y r) = P.map (X (b r)) :=
    fun r hr => Measure.map_congr (heq r hr)
  refine ⟨?_, ?_, ?_⟩
  · intro r hr
    exact (hT.1 (b r) (hb r hr)).congr (heq r hr).symm
  · exact hT.2.1.subset (by
      rintro μ ⟨r, hr, rfl⟩
      exact ⟨b r, hb r hr, hmap r hr⟩)
  · intro μ hμ
    apply hT.2.2 μ
    apply closure_mono (s := {ν : ProbabilityMeasure C(Rd d × Rd d, ℝ) |
      ∃ r ∈ S, (ν : Measure C(Rd d × Rd d, ℝ)) = P.map (Y r)})
      (t := {ν : ProbabilityMeasure C(Rd d × Rd d, ℝ) |
      ∃ t ∈ T, (ν : Measure C(Rd d × Rd d, ℝ)) = P.map (X t)})
    · rintro ν ⟨r, hr, hν⟩
      exact ⟨b r, hb r hr, hν.trans (hmap r hr)⟩
    · exact hμ

end HigherDimLQGMetric
