import HigherDimLQGMetric.Limits.CompareLimit
import LQGMetric.Meas.UM

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Set Topology Filter
namespace HigherDimLQGMetric

/-- On standard Borel spaces, an arbitrary almost-sure predicate pushes
forward along a measurable map. The Borel full-measure core has an analytic,
hence universally measurable, image. -/
theorem l6c_ae_map_of_ae_sb {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
    [StandardBorelSpace α] [StandardBorelSpace β]
    (μ : Measure α) [IsProbabilityMeasure μ] (f : α → β) (hf : Measurable f)
    (p : β → Prop) (hp : ∀ᵐ x ∂μ, p (f x)) :
    ∀ᵐ y ∂μ.map f, p y := by
  let S : Set α := {x | p (f x)}
  have hzero : μ Sᶜ = 0 := measure_eq_zero_iff_ae_notMem.mpr (by simpa [S] using hp)
  obtain ⟨N, hNS, hNm, hN0⟩ := exists_measurable_superset_of_null hzero
  let K : Set α := Nᶜ
  have hKm : MeasurableSet K := hNm.compl
  have hKS : K ⊆ S := by
    intro x hx
    by_contra hbad
    exact hx (hNS hbad)
  let U : Set β := f '' K
  have hU : LQGMetric.UMeasurableSet U := LQGMetric.UMeasurableSet.image hf hKm
  have hUn : NullMeasurableSet U (μ.map f) := hU _ inferInstance
  have hKmass : μ K = 1 := by
    rw [measure_compl hNm (measure_ne_top μ N), hN0, measure_univ]
    simp
  have hUmass : (μ.map f) U = 1 := by
    rw [Measure.map_apply₀ hf.aemeasurable hUn]
    apply le_antisymm prob_le_one
    exact hKmass ▸ measure_mono (fun x hx => ⟨x, hx, rfl⟩)
  have hUae : ∀ᵐ y ∂μ.map f, y ∈ U :=
    (ae_mem_iff_measure_eq hUn).2 (by simpa using hUmass)
  filter_upwards [hUae] with y ⟨x, hx, hxy⟩
  exact hxy ▸ hKS hx

end HigherDimLQGMetric
