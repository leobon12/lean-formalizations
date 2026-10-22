import HigherDimLQGMetric.Thm13.Translation
import HigherDimLQGMetric.LfppTight.LawInput

/-! Almost-sure CMap convergence gives the stable convergence interface. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l8_stablyTendstoLU_of_ae
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : Measurable h)
    (X : ℕ → Ω → C(Rd d × Rd d, ℝ))
    (Y : Ω → C(Rd d × Rd d, ℝ))
    (hX : ∀ n, AEMeasurable (X n) P) (hY : Measurable Y)
    (hae : ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop (𝓝 (Y ω))) :
    StablyTendstoLU P h X Y := by
  intro g hg hgb φ hφ hφb
  obtain ⟨Cg, hCg⟩ := hgb
  obtain ⟨Cφ, hCφ⟩ := hφb
  have hmeas (n : ℕ) : AEStronglyMeasurable
      (fun ω => g (h ω) * φ (X n ω)) P :=
    ((hg.comp hh).aemeasurable.mul
      (hφ.measurable.comp_aemeasurable (hX n))).aestronglyMeasurable
  have hYmeas : AEStronglyMeasurable
      (fun ω => g (h ω) * φ (Y ω)) P :=
    ((hg.comp hh).mul (hφ.measurable.comp hY)).aestronglyMeasurable
  have hbd (n : ℕ) : ∀ᵐ ω ∂P,
      ‖g (h ω) * φ (X n ω)‖ ≤ |Cg| * |Cφ| := by
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul ((hCg (h ω)).trans (le_abs_self _))
      ((hCφ (X n ω)).trans (le_abs_self _))
      (abs_nonneg _) (abs_nonneg _)
  have hlim : ∀ᵐ ω ∂P, Tendsto
      (fun n => g (h ω) * φ (X n ω)) atTop
      (𝓝 (g (h ω) * φ (Y ω))) := by
    filter_upwards [hae] with ω ht
    exact tendsto_const_nhds.mul (hφ.continuousAt.tendsto.comp ht)
  exact tendsto_integral_of_dominated_convergence
    (fun _ => |Cg| * |Cφ|) hmeas (integrable_const _) hbd hlim

end HigherDimLQGMetric
