import QuantumZipper.Proofs.Thm18.G1Side3A9
import Mathlib.MeasureTheory.Constructions.Polish.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-SIDE3 (13): the pullback of the quantum area measure by an injective map of `ℍ`

For a map `Φ` continuous and injective on `ℍ` and a measure `ν`, `pullMu ν Φ` is the measure on
`ℍ` with `pullMu ν Φ E = ν (Φ(E ∩ ℍ))` (`pullMu_apply`): the comap of `ν` by the measurable
embedding `Φ|ℍ` (Lusin–Souslin: `Continuous.measurableEmbedding`, `ℍ` Polish), pushed to `ℂ`.
Sheffield's side surface carries the area measure `Φ^*(μ_h|_D)` (arXiv:1012.4797, §1.6); the
test integrals are the `pullTest` integrals of Sheffield–Wang's transport (`integral_pullMu`).
Own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Metric Function
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace G1Side

open SWCore

theorem isOpen_H' : IsOpen H := isOpen_lt continuous_const Complex.continuous_im

instance polishSpace_H : PolishSpace H := isOpen_H'.polishSpace

/-- `Φ` restricted to `ℍ`. -/
def resH (Φ : ℂ → ℂ) : H → ℂ := fun u => Φ u

theorem measurableEmbedding_resH {Φ : ℂ → ℂ} (hc : ContinuousOn Φ H) (hi : InjOn Φ H) :
    MeasurableEmbedding (resH Φ) :=
  (hc.restrict).measurableEmbedding fun u v h => Subtype.ext (hi u.2 v.2 h)

/-- The pullback of `ν` by `Φ` on `ℍ`. -/
def pullMu (ν : Measure ℂ) (Φ : ℂ → ℂ) : Measure ℂ :=
  (ν.comap (resH Φ)).map Subtype.val

variable {Φ : ℂ → ℂ} {ν : Measure ℂ}

theorem pullMu_apply (hc : ContinuousOn Φ H) (hi : InjOn Φ H) {E : Set ℂ} (hE : MeasurableSet E) :
    pullMu ν Φ E = ν (Φ '' (E ∩ H)) := by
  unfold pullMu
  rw [Measure.map_apply measurable_subtype_coe hE,
    (measurableEmbedding_resH hc hi).comap_apply]
  congr 1
  ext v
  constructor
  · rintro ⟨u, hu, rfl⟩; exact ⟨u, ⟨hu, u.2⟩, rfl⟩
  · rintro ⟨u, ⟨hu, huH⟩, rfl⟩; exact ⟨⟨u, huH⟩, hu, rfl⟩

theorem pullMu_compl_H (hc : ContinuousOn Φ H) (hi : InjOn Φ H) : pullMu ν Φ Hᶜ = 0 := by
  rw [pullMu_apply hc hi isOpen_H'.measurableSet.compl]
  simp

/-- **Test integrals against the pullback.** -/
theorem integral_pullMu (hc : ContinuousOn Φ H) (hi : InjOn Φ H) {R : Set ℂ} (hRH : R ⊆ H)
    {f : ℂ → ℝ} (hf : Continuous f) (hfR : tsupport f ⊆ R) :
    ∫ z, f z ∂pullMu ν Φ = ∫ v, pullTest Φ R f v ∂ν := by
  have hE := measurableEmbedding_resH hc hi
  unfold pullMu
  rw [integral_map measurable_subtype_coe.aemeasurable hf.aestronglyMeasurable]
  have hcomp : (fun u : H => f u) = fun u : H => pullTest Φ R f (resH Φ u) := by
    funext u
    by_cases hu : (u : ℂ) ∈ R
    · have hmem : Φ u ∈ Φ '' R := mem_image_of_mem Φ hu
      have hinv : Function.invFunOn Φ R (Φ u) = u :=
        (hi.mono hRH) (Function.invFunOn_mem hmem) hu (Function.invFunOn_eq hmem)
      simp only [resH, pullTest, hinv]
      exact (if_pos hmem).symm
    · have h0 : f u = 0 := image_eq_zero_of_notMem_tsupport fun h => hu (hfR h)
      have hn : Φ u ∉ Φ '' R := by
        rintro ⟨v, hv, hvu⟩
        exact hu (hi (hRH hv) u.2 hvu ▸ hv)
      simp only [resH, pullTest, h0]
      exact (if_neg hn).symm
  rw [hcomp, ← hE.integral_map, hE.map_comap]
  refine setIntegral_eq_integral_of_forall_compl_eq_zero fun v hv => ?_
  unfold pullTest
  rw [if_neg]
  rintro ⟨u, hu, rfl⟩
  exact hv ⟨⟨u, hRH hu⟩, rfl⟩

end G1Side
end QuantumZipper
