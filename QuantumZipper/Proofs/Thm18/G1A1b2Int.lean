import QuantumZipper.Proofs.Thm18.G1A1b2Reg

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1A1b2 (int): the integrability clause of the side convergence node

For a good driver `W`, `t > 0` and any `F` continuous on `ℍ̄ × (0, ∞)`, `F(·, ρ)` is integrable
against the pushed side circle `(f_t ∘ ψ)_* fc(d, s)`: the measure lives on a compact subset of
`ℍ̄`, because

* `ψ = φ⁻¹` maps bounded subsets of `ℍ` to bounded sets (`φ` is proper at `∞`, the normalization
  in `IsNormalizedUniformizer`);
* `‖f_t(z)‖ ≤ ‖z‖ + C` off the hull (`G1ZA1a.exists_bound_fwdMapInv` and `f_t⁻¹ ∘ f_t = id`).

This removes the integrability clause of `G1A1b2SideConvStmt`: the remaining node
`G1A1b2SideTendstoStmt` is the convergence alone (`g1ZA1bSideExactArcStmt_of_tendsto`).

Own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace R18
namespace G1A1b

open Thm18Asm

/-- The inverse of a normalized uniformizer maps bounded subsets of `ℍ` to bounded sets. -/
theorem exists_bound_invFunOn {D : Set ℂ} {φ : ℂ → ℂ} (hφ : IsNormalizedUniformizer D φ)
    (R : ℝ) : ∃ R' : ℝ, ∀ w ∈ H, ‖w‖ ≤ R → ‖invFunOn φ D w‖ ≤ R' := by
  have h := hφ.2.2.2.eventually (eventually_gt_atTop R)
  rw [Filter.eventually_inf_principal] at h
  obtain ⟨R', -, hR'⟩ := (Metric.hasBasis_cobounded_compl_closedBall (0 : ℂ)).eventually_iff.1 h
  refine ⟨R', fun w hw hwR => ?_⟩
  have hz : invFunOn φ D w ∈ D := invFunOn_mem (hφ.1.surjOn hw)
  have hφz : φ (invFunOn φ D w) = w := invFunOn_eq (hφ.1.surjOn hw)
  by_contra hc
  have hmem : invFunOn φ D w ∈ (Metric.closedBall (0 : ℂ) R')ᶜ := by
    simp only [mem_compl_iff, Metric.mem_closedBall, dist_zero_right]
    linarith [not_le.1 hc]
  have := hR' hmem hz
  rw [hφz] at this
  linarith

/-- **Integrability along the pushed side circles.** -/
theorem integrable_sideFamily {W : ℝ → ℝ} (hG : G1zDrvGood W) {t : ℝ} (ht : 0 < t)
    (left : Bool) {F : ℂ × ℝ → ℝ} (hF : ContinuousOn F (Hbar ×ˢ Ioi 0)) (d : ℂ) {s : ℝ}
    (hs : 0 < s) {ρ : ℝ} (hρ : 0 < ρ) :
    Integrable (fun z => F (z, ρ))
      ((foldedCircle d s).map fun w => fwdMap W t (g1zSideMap left W w)) := by
  obtain ⟨hWc, hW0, hWm, hη, hK⟩ := hG
  set D := sideDom (trace W) left with hD
  have hU := G1ZA1a.isNormalizedUniformizer_sideDom hη left
  obtain ⟨-, -, -, hmaps⟩ := G1.invFunOn_props (G1ZA1a.isOpen_sideDom hη left) hU
  set h : ℂ → ℂ := fun w => fwdMap W t (g1zSideMap left W w) with hh
  by_cases hm : AEMeasurable h (foldedCircle d s)
  swap
  · rw [Measure.map_of_not_aemeasurable_of_ne_zero hm (IsProbabilityMeasure.ne_zero _)]
    exact integrable_dirac enorm_lt_top
  obtain ⟨R', hR'⟩ := exists_bound_invFunOn hU (‖d‖ + s)
  obtain ⟨C, hC⟩ := G1ZA1a.exists_bound_fwdMapInv ⟨hWc, hW0, hWm, hη, hK⟩ ht
  set K : Set ℂ := Hbar ∩ Metric.closedBall 0 (R' + C) with hKdef
  have hKc : IsCompact K :=
    (isCompact_closedBall 0 (R' + C)).inter_left
      (isClosed_le continuous_const Complex.continuous_im)
  have hKm : MeasurableSet K := hKc.isClosed.measurableSet
  -- the pushed points lie in `K`
  have hpt : ∀ w ∈ H, ‖w‖ ≤ ‖d‖ + s → h w ∈ K := by
    intro w hw hwR
    set z := g1zSideMap left W w with hz
    have hzD : z ∈ D := hmaps hw
    have hzH : z ∈ H := G1ZA1a.sideDom_subset_H _ left hzD
    have hzK : z ∉ fwdHull W t := by
      rw [hK t ht.le]
      rintro ⟨u, hu, hzu⟩
      have hnot : z ∉ trace W '' Ici (0 : ℝ) := by
        cases left
        · exact hzD.1.2
        · exact hzD.1.2
      exact hnot ⟨u, le_of_lt hu.1, hzu⟩
    have hv : fwdMap W t z ∈ H := FwdHolo.mapsTo_fwdMap hWc ht.le ⟨hzH, hzK⟩
    have hinv : fwdMapInv W t (fwdMap W t z) = z := RS.fwdMapInv_fwdMap hWc hW0 ht.le ⟨hzH, hzK⟩
    have h1 := hC _ hv
    rw [hinv] at h1
    have h2 : ‖fwdMap W t z‖ ≤ ‖z‖ + C := by
      have := norm_sub_norm_le (fwdMap W t z) z
      rw [norm_sub_rev] at h1
      linarith
    refine ⟨show 0 ≤ (h w).im from le_of_lt hv, ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    have h3 : ‖z‖ ≤ R' := hR' w hw hwR
    have h4 : h w = fwdMap W t z := rfl
    rw [h4]
    linarith
  have hae : ∀ᵐ z ∂((foldedCircle d s).map h), z ∈ K := by
    refine (ae_map_iff hm hKm).2 ?_
    filter_upwards [TwoPoint.foldedCircle_ae_mem_H d hs,
      TwoPoint.foldedCircle_ae_norm_le d hs.le] with w hw hwn
    exact hpt w hw hwn
  have hFK : ContinuousOn (fun z => F (z, ρ)) K :=
    (RegClosure.continuousOn_slice hF hρ).mono inter_subset_left
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn hFK
  haveI : IsProbabilityMeasure ((foldedCircle d s).map h) :=
    (Measure.isProbabilityMeasure_map_iff hm).2 inferInstance
  have hrest : ((foldedCircle d s).map h).restrict K = (foldedCircle d s).map h :=
    Measure.restrict_eq_self_of_ae_mem hae
  refine Integrable.of_bound ?_ M (hae.mono fun z hz => hM z hz)
  rw [← hrest]
  exact hFK.aestronglyMeasurable hKm

end G1A1b

open Thm18Asm

end R18
end QuantumZipper
