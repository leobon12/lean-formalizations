import QuantumZipper.Proofs.LQG.CoordChangeAreaFree

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Coordinate change of the area measure (COORD-CHANGE, D98): regularity of the pushed averages

For the free-boundary GFF `X` on `ℍ` and one deterministic map `ψ` of an area class on a
rectangle `R`, almost surely, from some dyadic scale on, the regularized pairing of `X ω` with
the pushed circles `ψ_* fc(d, 2^{-k})` is (i) the limit of the dyadic smoothings, and (ii)
continuous in the centre `d ∈ R` (`CoordChangeArea.ae_pushed_regular`). This is the
finite-parameter primed core `SWCore.swcNA2I_primed` (Duplantier–Sheffield 2011, Prop. 3.1
(Kolmogorov continuity); Sheffield–Wang arXiv:1605.06171, Lemma 3.5) read along the constant
family `CoordChangeArea.constFam_unif`. Own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Function Metric
open scoped Topology ENNReal

namespace QuantumZipper
namespace CoordChangeArea

open SWCore E6 G1Side

/-- The parameter of the constant family at the centre `d` (radius factor `1`). -/
def qd (d : ℂ) : Fin 5 → ℝ := ![0, 0, d.re, d.im, 1]

theorem continuous_qd : Continuous qd := by
  refine continuous_pi fun i => ?_
  fin_cases i <;> simp [qd] <;> fun_prop

theorem a7Cen_qd {x₁ x₂ y₁ y₂ : ℝ} {d : ℂ} (hd : d ∈ rectC x₁ x₂ y₁ y₂) :
    a7Cen x₁ x₂ y₁ y₂ (qd d) = d := by
  apply Complex.ext
  · simp [qd, a7Cen, clampI_eq hd.1]
  · simp [qd, a7Cen, clampI_eq hd.2]

theorem a7Rad_qd (d : ℂ) : a7Rad (qd d) = 1 := by
  simp [qd, a7Rad, clampI]

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-- **Regularity of the pushed averages of the free field along one map.** -/
theorem ae_pushed_regular [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    {ψ : ℂ → ℂ} {x₁ x₂ y₁ y₂ ρ M m : ℝ} (hx : x₁ ≤ x₂) (hy0 : 0 < y₁) (hy : y₁ ≤ y₂)
    (hρ : 0 < ρ) (hm : 0 < m) (hψ : ψ ∈ AreaClass x₁ x₂ y₁ y₂ ρ M m) :
    ∃ k₀ : ℕ, ∀ᵐ ω ∂P, ∀ k : ℕ,
      (∀ d ∈ rectC x₁ x₂ y₁ y₂, Tendsto (fun j => ∫ u, avgReg (X ω) j u
          ∂((foldedCircle d (radius (k + k₀))).map ψ)) atTop
        (𝓝 (evalReg (X ω) ((foldedCircle d (radius (k + k₀))).map ψ)))) ∧
      ContinuousOn (fun d => evalReg (X ω) ((foldedCircle d (radius (k + k₀))).map ψ))
        (rectC x₁ x₂ y₁ y₂) := by
  obtain ⟨k₀, hae⟩ := swcNA2I_primed hX (constFam_unif hx hy0 hy hρ hm hψ)
  refine ⟨k₀, ?_⟩
  filter_upwards [hae] with ω hω k
  obtain ⟨hU, hC, -⟩ := hω
  have e : ∀ d ∈ rectC x₁ x₂ y₁ y₂,
      (foldedCircle (a7Cen x₁ x₂ y₁ y₂ (qd d)) (a7Rad (qd d) * radius (k + k₀))).map ψ =
        (foldedCircle d (radius (k + k₀))).map ψ := fun d hd => by
    rw [a7Cen_qd hd, a7Rad_qd, one_mul]
  refine ⟨fun d hd => ?_, ?_⟩
  · have h1 := (hU k {qd d} isCompact_singleton)
    rw [tendstoUniformlyOn_singleton_iff_tendsto] at h1
    simp only [e d hd] at h1
    exact h1
  · refine ((hC k).comp continuous_qd).continuousOn.congr fun d hd => ?_
    simp only [Function.comp_apply, e d hd]

end CoordChangeArea
end QuantumZipper
