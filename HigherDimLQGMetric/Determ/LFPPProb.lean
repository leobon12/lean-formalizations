import HigherDimLQGMetric.Determ.StableLU
import HigherDimLQGMetric.LfppTight.LawInput
import HigherDimLQGMetric.Field.LGFPlusCont

/-!
# Convergence of a normalized LFPP subsequence once its limit is determined

This is the final probability-convergence implication in MA5 A20(c).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem determ_lfppSeq_prob_of_det {d : ℕ} (ξ : ℝ) (κ : Rd d → ℝ)
    (hB2 : ∃ Q : ℝ, DGZ.DGZHyp d κ ξ Q ∧ DGZ.RealEpsAdapterShape d κ ξ Q)
    (εs : ℕ → ℝ) (hε : ∀ n, 0 < εs n)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (Dh : Ω → ContMetric d) (hh : IsNormalizedLGF h P)
    (hstable : StablyTendstoLU P h (fun n ω => lfppSeq κ ξ εs (h ω) n)
      (fun ω => (Dh ω).1))
    (hdet : LQGMetric.AEDeterminedBy Dh h P) :
    TendstoInProbLU P (fun n ω => lfppSeq κ ξ εs (h ω) n) atTop
      (fun ω => (Dh ω).1) := by
  obtain ⟨Q, hDGZ, -⟩ := hB2
  have hm : ∀ n, AEMeasurable (fun ω => lfppSeq κ ξ εs (h ω) n) P := by
    intro n
    exact l6a_aemeasurable_normalized_lfpp hDGZ.dim κ hDGZ.kernel ξ (hε n)
      P h hh.1.isLGFPlusBddCont
  have hdet' : LQGMetric.AEDeterminedBy (fun ω => (Dh ω).1) h P := by
    obtain ⟨f, hf, heq⟩ := hdet
    exact ⟨(fun D : ContMetric d => D.1) ∘ f,
      measurable_subtype_coe.comp hf, heq.mono fun ω hω => congrArg Subtype.val hω⟩
  exact determ_tendstoInProbLU_of_stable P h
    (fun n ω => lfppSeq κ ξ εs (h ω) n) (fun ω => (Dh ω).1)
    hh.1.measurable hm hstable hdet'

end HigherDimLQGMetric
