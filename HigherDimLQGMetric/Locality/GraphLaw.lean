import HigherDimLQGMetric.Locality.StableGood
import HigherDimLQGMetric.Locality.StableJoint

/-! A measurable canonical-field graph version of every LFPP joint law. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory ProbabilityTheory

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- The finite-scale joint law depends only on the field law, even though
the raw LFPP map is initially only almost everywhere measurable. -/
theorem l7a_lfpp_joint_law_graph {d : ℕ} (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ)
    (εs : ℕ → ℝ) (hεs : ∀ n, 0 < εs n)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P) (n : ℕ) :
    ∃ F : DistRd d → C(Rd d × Rd d, ℝ), Measurable F ∧
      F =ᵐ[P.map h] (fun g => lfppSeq κ ξ εs g n) ∧
      P.map (fun ω => (pairJ ⊤ (h ω), lfppSeq κ ξ εs (h ω) n)) =
        (P.map h).map (fun g => (pairJ ⊤ g, F g)) := by
  let μ : Measure (DistRd d) := P.map h
  let raw : DistRd d → C(Rd d × Rd d, ℝ) :=
    fun g => lfppSeq κ ξ εs g n
  have hμ : IsProbabilityMeasure μ := inferInstance
  letI : IsProbabilityMeasure μ := hμ
  have hhμ : IsNormalizedLGF (id : DistRd d → DistRd d) μ := hh.map_id
  have hraw : AEMeasurable raw μ :=
    l6a_aemeasurable_normalized_lfpp hd κ hκ ξ (hεs n) μ id
      hhμ.1.isLGFPlusBddCont
  let F : DistRd d → C(Rd d × Rd d, ℝ) := hraw.mk raw
  have hFm : Measurable F := hraw.measurable_mk
  have hFe : F =ᵐ[μ] raw := (hraw.ae_eq_mk).symm
  refine ⟨F, hFm, hFe, ?_⟩
  have hmap : (P.map h).map (fun g => (pairJ ⊤ g, F g)) =
      P.map (fun ω => (pairJ ⊤ (h ω), F (h ω))) := by
    rw [Measure.map_map ((measurable_pairJ ⊤).prodMk hFm) hh.1.measurable]
    rfl
  rw [hmap]
  apply Measure.map_congr
  have he : ∀ᵐ ω ∂P, F (h ω) = raw (h ω) := by
    have hμe : F =ᵐ[P.map h] raw := hFe
    exact ae_of_ae_map hh.1.measurable.aemeasurable hμe
  filter_upwards [he] with ω hω
  exact Prod.ext rfl hω.symm

end HigherDimLQGMetric
