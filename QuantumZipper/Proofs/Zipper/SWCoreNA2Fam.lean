import QuantumZipper.Proofs.Thm18.G1FrostAlphaVar

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SW-CORE NA2: `FamilyBounds` for a generic Hölder parametrized family of circles

Generic version of `Thm18Asm.G1RC.pushFamBounds_of_regα` (G1FrostAlphaVar.lean) and of its
pieces (`kernelCov_pushFam_eqα`, `abs_kernelCov_pushFam_sub_leα`, `isFrostman_pushFamα`,
`abs_kernelCov2_pushFam_leα`, `pushVar_of_reg_α`, `pushFam_potα`, `pushFam_support`): the
specific map `pushPhi ψ` is replaced by an arbitrary jointly continuous family
`Φ : (Fin n → ℝ) → ℝ → ℂ` with values in `Hbar`, bounded, `α`-Frostman and `η`-Hölder in the
parameter, uniformly on boxes. The smoothed family `smoothFam circM Φ` then satisfies
`FamilyBounds` with exponent `β = η·α/2`.

Source: the proofs of G1FrostAlphaVar.lean / G1PathCoordFam.lean, copied line by line (the
repository's own energy estimates, Duplantier–Sheffield, Invent. Math. 185 (2011),
Prop. 3.1-type argument). Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Metric Set Function Real
open scoped ENNReal NNReal Topology

namespace QuantumZipper
namespace SWCore

open Thm18Asm Thm18Asm.G1RC CircleFubini KolmD TwoPoint RegCont

section NA2Fam

variable {n : ℕ}

/-- The smoothed generic family. -/
abbrev swcNA2Fam (Φ : (Fin n → ℝ) → ℝ → ℂ) : (Fin (n + 1) → ℝ) → Measure ℂ :=
  smoothFam circM Φ

theorem swcNA2_isProb (Φ : (Fin n → ℝ) → ℝ → ℂ) (p : Fin (n + 1) → ℝ) : IsProbabilityMeasure (swcNA2Fam Φ p) := by
  unfold swcNA2Fam smoothFam
  split_ifs with ht
  · exact ⟨by rw [bind_circle_univ]; exact measure_univ⟩
  · infer_instance

theorem swcNA2_init_mem_boxD {R : ℕ} {p : Fin (n + 1) → ℝ} (hp : p ∈ boxD (d := n + 1) R) :
    Fin.init p ∈ boxD (d := n) R := fun i => hp (Fin.castSucc i)

theorem swcNA2_norm_init_sub_le {p p' : Fin (n + 1) → ℝ} :
    ‖Fin.init p - Fin.init p'‖ ≤ ‖p - p'‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => by
    have := norm_le_pi_norm (p - p') (Fin.castSucc i)
    simpa [Fin.init] using this

theorem swcNA2_ae_norm_le {Φ : (Fin n → ℝ) → ℝ → ℂ} {B L : ℝ} {p : Fin (n + 1) → ℝ}
    (hΦm : Measurable (Φ (Fin.init p))) (hΦb : ∀ θ, ‖Φ (Fin.init p) θ‖ ≤ B)
    (hL : 0 ≤ L) (htL : p (Fin.last n) ≤ L) : ∀ᵐ y ∂swcNA2Fam Φ p, ‖y‖ ≤ B + L := by
  have hBμ : ∀ᵐ y ∂(circM.map (Φ (Fin.init p))), ‖y‖ ≤ B :=
    (ae_map_iff hΦm.aemeasurable (measurableSet_le measurable_norm measurable_const)).2
      (ae_of_all _ hΦb)
  unfold swcNA2Fam smoothFam
  split_ifs with ht
  · exact (ae_norm_bindFc_le ht.le hBμ).mono fun y hy => by linarith
  · exact hBμ.mono fun y hy => by linarith

/-- `∫ neuPot κ d(swcNA2Fam Φ p) = ∫ fcPot κ t⁺ (Φ_q θ) dcircM` (exponent `α`). -/
theorem swcNA2_kernelCov_eq {Φ : (Fin n → ℝ) → ℝ → ℂ} {α : ℝ} (hα : 0 < α)
    {p : Fin (n + 1) → ℝ} (hΦH : ∀ θ, Φ (Fin.init p) θ ∈ Hbar)
    (hΦc : Continuous (Φ (Fin.init p))) {B CF L : ℝ} (hB0 : 0 ≤ B) (hCF : 0 ≤ CF)
    (hL : 0 ≤ L) (hΦb : ∀ θ, ‖Φ (Fin.init p) θ‖ ≤ B) (htL : p (Fin.last n) ≤ L)
    (κ : Measure ℂ) [IsFiniteMeasure κ] (hFκ : TwoPoint.IsFrostman κ α CF)
    (hBκ : ∀ᵐ y ∂κ, ‖y‖ ≤ B + L) (hmκ : κ.real univ = 1) :
    kernelCov neumannH (swcNA2Fam Φ p) κ =
      ∫ θ, fcPot κ (max (p (Fin.last n)) 0) (Φ (Fin.init p) θ) ∂circM := by
  unfold swcNA2Fam smoothFam
  split_ifs with ht
  · rw [max_eq_left ht.le]
    have hBμ : ∀ᵐ y ∂(circM.map (Φ (Fin.init p))), ‖y‖ ≤ B :=
      (ae_map_iff hΦc.measurable.aemeasurable
        (measurableSet_le measurable_norm measurable_const)).2 (ae_of_all _ hΦb)
    rw [kernelCov_bindFc_eq_Lα hα hB0 hCF hL hBμ ht.le htL κ hFκ hBκ hmκ,
      integral_map hΦc.aemeasurable (measurable_fcPot κ _).aestronglyMeasurable]
  · rw [max_eq_right (not_lt.1 ht)]
    show ∫ x, neuPot κ x ∂(circM.map (Φ (Fin.init p))) = _
    rw [integral_map hΦc.aemeasurable (measurable_neuPot κ).aestronglyMeasurable]
    refine integral_congr_ae (ae_of_all _ fun θ => ?_)
    exact (fcPot_zero_of_mem_Hbar (hΦH θ)).symm

/-- The per-`κ` increment bound (exponent `α`). -/
theorem swcNA2_abs_kernelCov_sub_le {Φ : (Fin n → ℝ) → ℝ → ℂ} {α : ℝ} (hα : 0 < α)
    (hα1 : α ≤ 1) {p p' : Fin (n + 1) → ℝ}
    (hΦH : ∀ θ, Φ (Fin.init p) θ ∈ Hbar) (hΦH' : ∀ θ, Φ (Fin.init p') θ ∈ Hbar)
    (hΦc : Continuous (Φ (Fin.init p))) (hΦc' : Continuous (Φ (Fin.init p')))
    {B CF L Δ : ℝ} (hB0 : 0 ≤ B) (hCF : 0 ≤ CF) (hL : 0 ≤ L)
    (hΦb : ∀ θ, ‖Φ (Fin.init p) θ‖ ≤ B) (hΦb' : ∀ θ, ‖Φ (Fin.init p') θ‖ ≤ B)
    (htL : p (Fin.last n) ≤ L) (htL' : p' (Fin.last n) ≤ L)
    (hΔ : ∀ θ, ‖Φ (Fin.init p) θ - Φ (Fin.init p') θ‖ ≤ Δ)
    (κ : Measure ℂ) [IsFiniteMeasure κ] (hFκ : TwoPoint.IsFrostman κ α CF)
    (hBκ : ∀ᵐ y ∂κ, ‖y‖ ≤ B + L) (hmκ : κ.real univ = 1) :
    |kernelCov neumannH (swcNA2Fam Φ p) κ - kernelCov neumannH (swcNA2Fam Φ p') κ| ≤
      holderKα α CF (B + L) * (Δ + |p (Fin.last n) - p' (Fin.last n)|) ^ (α / 2) := by
  rw [swcNA2_kernelCov_eq hα hΦH hΦc hB0 hCF hL hΦb htL κ hFκ hBκ hmκ,
    swcNA2_kernelCov_eq hα hΦH' hΦc' hB0 hCF hL hΦb' htL' κ hFκ hBκ hmκ]
  set ρ := max (p (Fin.last n)) 0
  set ρ' := max (p' (Fin.last n)) 0
  have hρ : 0 ≤ ρ := le_max_right _ _
  have hρ' : 0 ≤ ρ' := le_max_right _ _
  have hρL : ρ ≤ L := max_le htL hL
  have hρL' : ρ' ≤ L := max_le htL' hL
  have hint : ∀ (σ : ℝ) (F : ℝ → ℂ), Continuous F → 0 ≤ σ → σ ≤ L → (∀ θ, ‖F θ‖ ≤ B) →
      Integrable (fun θ => fcPot κ σ (F θ)) circM := fun σ F hF hσ hσL hFb =>
    Integrable.of_bound ((measurable_fcPot κ σ).comp hF.measurable).aestronglyMeasurable
      (potMaxα α CF (B + L)) (ae_of_all _ fun θ => by
        rw [Real.norm_eq_abs]
        exact abs_fcPot_le_Lα hα hCF hB0 hL hFκ hBκ hmκ (hFb θ) hσ hσL)
  set d := holderKα α CF (B + L) * (Δ + |p (Fin.last n) - p' (Fin.last n)|) ^ (α / 2)
  have hpt : ∀ θ, |fcPot κ ρ (Φ (Fin.init p) θ) - fcPot κ ρ' (Φ (Fin.init p') θ)| ≤ d := by
    intro θ
    refine (abs_fcPot_sub_le_Lα hα hα1 hCF hB0 hL hFκ hBκ hmκ (hΦb θ) (hΦb' θ) hρ hρ' hρL
      hρL').trans ?_
    refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) ?_ (by linarith))
      (holderKα_nonneg hα hCF (by linarith))
    exact add_le_add (hΔ θ) (abs_max_sub_max_le_abs _ _ _)
  rw [← integral_sub (hint ρ _ hΦc hρ hρL hΦb) (hint ρ' _ hΦc' hρ' hρL' hΦb')]
  calc _ ≤ ∫ θ, |fcPot κ ρ (Φ (Fin.init p) θ) -
        fcPot κ ρ' (Φ (Fin.init p') θ)| ∂circM := abs_integral_le_integral_abs
    _ ≤ ∫ _θ, d ∂circM := integral_mono ((hint ρ _ hΦc hρ hρL hΦb).sub
        (hint ρ' _ hΦc' hρ' hρL' hΦb')).abs (integrable_const d) hpt
    _ = d := by simp

theorem swcNA2_isFrostman {Φ : (Fin n → ℝ) → ℝ → ℂ} {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {C : ℝ} (hC : 0 ≤ C) {p : Fin (n + 1) → ℝ}
    (hFq : TwoPoint.IsFrostman (circM.map (Φ (Fin.init p))) α C) :
    TwoPoint.IsFrostman (swcNA2Fam Φ p) α (24 * C) := by
  unfold swcNA2Fam smoothFam
  split_ifs with ht
  · exact isFrostman_bindFcα hα hα1 hFq ht.le
  · intro w r hr
    refine (hFq w r hr).trans ?_
    have := Real.rpow_nonneg hr.le α
    nlinarith

/-- **Energy increment of two members** of the smoothed generic family (exponent `α`). -/
theorem swcNA2_abs_kernelCov2_le {Φ : (Fin n → ℝ) → ℝ → ℂ} {α : ℝ} (hα : 0 < α)
    (hα1 : α ≤ 1) {p p' : Fin (n + 1) → ℝ}
    (hΦH : ∀ θ, Φ (Fin.init p) θ ∈ Hbar) (hΦH' : ∀ θ, Φ (Fin.init p') θ ∈ Hbar)
    (hΦc : Continuous (Φ (Fin.init p))) (hΦc' : Continuous (Φ (Fin.init p')))
    {B C L Δ : ℝ} (hB0 : 0 ≤ B) (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hF : TwoPoint.IsFrostman (circM.map (Φ (Fin.init p))) α C)
    (hF' : TwoPoint.IsFrostman (circM.map (Φ (Fin.init p'))) α C)
    (hΦb : ∀ θ, ‖Φ (Fin.init p) θ‖ ≤ B) (hΦb' : ∀ θ, ‖Φ (Fin.init p') θ‖ ≤ B)
    (htL : p (Fin.last n) ≤ L) (htL' : p' (Fin.last n) ≤ L)
    (hΔ : ∀ θ, ‖Φ (Fin.init p) θ - Φ (Fin.init p') θ‖ ≤ Δ) :
    |kernelCov2 neumannH (swcNA2Fam Φ p, swcNA2Fam Φ p')
        (swcNA2Fam Φ p, swcNA2Fam Φ p')| ≤
      2 * holderKα α (24 * C) (B + L) *
        (Δ + |p (Fin.last n) - p' (Fin.last n)|) ^ (α / 2) := by
  have := swcNA2_isProb Φ p
  have := swcNA2_isProb Φ p'
  have hC24 : 0 ≤ 24 * C := by positivity
  have h1 := swcNA2_abs_kernelCov_sub_le hα hα1 hΦH hΦH' hΦc hΦc' hB0 hC24 hL hΦb hΦb' htL
    htL' hΔ (swcNA2Fam Φ p) (swcNA2_isFrostman hα hα1 hC hF)
    (swcNA2_ae_norm_le hΦc.measurable hΦb hL htL) (by simp)
  have h2 := swcNA2_abs_kernelCov_sub_le hα hα1 hΦH hΦH' hΦc hΦc' hB0 hC24 hL hΦb hΦb' htL
    htL' hΔ (swcNA2Fam Φ p') (swcNA2_isFrostman hα hα1 hC hF')
    (swcNA2_ae_norm_le hΦc'.measurable hΦb' hL htL') (by simp)
  have e : kernelCov2 neumannH (swcNA2Fam Φ p, swcNA2Fam Φ p')
      (swcNA2Fam Φ p, swcNA2Fam Φ p') =
      (kernelCov neumannH (swcNA2Fam Φ p) (swcNA2Fam Φ p) -
        kernelCov neumannH (swcNA2Fam Φ p') (swcNA2Fam Φ p)) -
      (kernelCov neumannH (swcNA2Fam Φ p) (swcNA2Fam Φ p') -
        kernelCov neumannH (swcNA2Fam Φ p') (swcNA2Fam Φ p')) := by
    unfold kernelCov2; ring
  rw [e]
  refine (abs_sub _ _).trans ?_
  linarith

/-- **`FamilyBounds` for a generic Hölder family of `α`-Frostman circles**: generic version of
`Thm18Asm.G1RC.pushFamBounds_of_regα`, with `β = η·α/2`. -/
theorem swcNA2_familyBounds {Φ : (Fin n → ℝ) → ℝ → ℂ} (hΦ : Continuous (Function.uncurry Φ))
    (hΦH : ∀ q θ, Φ q θ ∈ Hbar) {α η : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hη : 0 < η)
    (hη1 : η ≤ 1)
    (hb : ∀ R : ℕ, ∃ B C H : ℝ, 0 ≤ B ∧ 0 ≤ C ∧ 0 ≤ H ∧ ∀ q ∈ KolmD.boxD (d := n) R,
      (∀ θ, ‖Φ q θ‖ ≤ B) ∧ TwoPoint.IsFrostman (Thm18Asm.G1RC.circM.map (Φ q)) α C ∧
      ∀ q' ∈ KolmD.boxD (d := n) R, ∀ θ, ‖Φ q θ - Φ q' θ‖ ≤ H * ‖q - q'‖ ^ η) :
    ∃ β : ℝ, 0 < β ∧
      Thm18Asm.G1RC.FamilyBounds (Thm18Asm.G1RC.smoothFam Thm18Asm.G1RC.circM Φ) β := by
  have hc : ∀ q, Continuous (Φ q) := fun q =>
    hΦ.comp (continuous_const.prodMk continuous_id)
  have hα2 : 0 ≤ α / 2 := by linarith
  refine ⟨η * (α / 2), mul_pos hη (by linarith),
    swcNA2_isProb Φ, fun R => ?_⟩
  obtain ⟨B, C, H, hB0, hC, hH0, hbR⟩ := hb R
  set Rr : ℝ := (R : ℝ) with hRrdef
  have hRr : 0 ≤ Rr := Nat.cast_nonneg R
  refine ⟨⟨B + Rr, fun p hp => ?_⟩, ?_, ?_⟩
  · -- support
    have hq := swcNA2_init_mem_boxD hp
    have h0 : (circM.map (Φ (Fin.init p))) (ballH B)ᶜ = 0 := by
      rw [Measure.map_apply (hc _).measurable (measurableSet_ballH B).compl]
      convert measure_empty (μ := circM)
      ext θ
      simp only [mem_preimage, mem_compl_iff, mem_empty_iff_false, iff_false, not_not]
      exact ⟨by rw [mem_closedBall, dist_zero_right]; exact (hbR _ hq).1 θ, hΦH _ θ⟩
    show smoothFam circM Φ p (ballH (B + Rr))ᶜ = 0
    unfold smoothFam
    split_ifs with ht
    · have htR : p (Fin.last n) ≤ Rr := (abs_le.1 (hp (Fin.last n))).2
      exact bind_circle_support _ ht.le h0 (R₀ := B) (fun z hz => by
        have := hz.1; rwa [mem_closedBall, dist_zero_right] at this) (by linarith)
    · refine measure_mono_null (compl_subset_compl.2 ?_) h0
      intro z hz
      exact ⟨by
        have := hz.1; rw [mem_closedBall, dist_zero_right] at this ⊢; linarith, hz.2⟩
  · -- potential
    set K := ENNReal.ofReal (2 * Real.log 2 + 2 * Real.posLog R)
    refine ⟨2 * ENNReal.ofReal (C / α) + 2 * K, by finiteness, fun q hq y => ?_⟩
    have hFq : TwoPoint.IsFrostman (circM.map (Φ (Fin.init q))) α C :=
      (hbR _ (swcNA2_init_mem_boxD hq)).2.1
    show ∫⁻ x, ENNReal.ofReal (-Real.log ‖x - y‖) ∂(smoothFam circM Φ q) ≤ _
    unfold smoothFam
    split_ifs with ht
    · exact bind_pot_le hFq hα hC ht (abs_le.1 (hq (Fin.last n))).2 y
    · refine (frostman_pot_le hFq hα hC y).trans ?_
      calc ENNReal.ofReal (C / α) ≤ 2 * ENNReal.ofReal (C / α) := by
            rw [two_mul]; exact le_self_add
        _ ≤ _ := le_self_add
  · -- variance
    set D := 2 * Rr
    have hD : 0 ≤ D := by positivity
    set K0 := H + D ^ (1 - η)
    have hK0 : 0 ≤ K0 := by positivity
    have hKH := holderKα_nonneg hα (by positivity : (0 : ℝ) ≤ 24 * C)
      (by positivity : 0 ≤ B + Rr)
    refine ⟨2 * holderKα α (24 * C) (B + Rr) * K0 ^ (α / 2),
      by have := Real.rpow_nonneg hK0 (α / 2); positivity, fun p hp p' hp' => ?_⟩
    have hq := swcNA2_init_mem_boxD hp
    have hq' := swcNA2_init_mem_boxD hp'
    set δ := ‖p - p'‖
    have hδ : 0 ≤ δ := norm_nonneg _
    have hδD : δ ≤ D := abs_apply_sub_le_of_boxD hp hp'
    set Δ := H * δ ^ η
    have hΔ : ∀ θ, ‖Φ (Fin.init p) θ - Φ (Fin.init p') θ‖ ≤ Δ := fun θ => by
      refine ((hbR _ hq).2.2 _ hq' θ).trans ?_
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (norm_nonneg _) swcNA2_norm_init_sub_le hη.le) hH0
    have htR : ∀ r : Fin (n + 1) → ℝ, r ∈ boxD (d := n + 1) R → r (Fin.last n) ≤ Rr :=
      fun r hr => (abs_le.1 (hr (Fin.last n))).2
    have hmain := swcNA2_abs_kernelCov2_le hα hα1 (hΦH _) (hΦH _) (hc _) (hc _) hB0 hC hRr
      (hbR _ hq).2.1 (hbR _ hq').2.1 (hbR _ hq).1 (hbR _ hq').1 (htR p hp) (htR p' hp') hΔ
    refine hmain.trans ?_
    have ht : |p (Fin.last n) - p' (Fin.last n)| ≤ δ := by
      have := norm_le_pi_norm (p - p') (Fin.last n)
      simpa using this
    have hE : Δ + |p (Fin.last n) - p' (Fin.last n)| ≤ K0 * δ ^ η := by
      have e1 : δ ≤ D ^ (1 - η) * δ ^ η := by
        have := rpow_le_bound_mul_rpow hδ hδD hη hη1
        rwa [Real.rpow_one] at this
      have e6 : K0 * δ ^ η = H * δ ^ η + D ^ (1 - η) * δ ^ η := by ring
      rw [e6]
      linarith
    calc 2 * holderKα α (24 * C) (B + Rr) *
          (Δ + |p (Fin.last n) - p' (Fin.last n)|) ^ (α / 2)
        ≤ 2 * holderKα α (24 * C) (B + Rr) * (K0 * δ ^ η) ^ (α / 2) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hE hα2)
            (by positivity)
      _ = 2 * holderKα α (24 * C) (B + Rr) * K0 ^ (α / 2) * δ ^ (η * (α / 2)) := by
          rw [Real.mul_rpow hK0 (Real.rpow_nonneg hδ _), ← Real.rpow_mul hδ]; ring

end NA2Fam

end SWCore
end QuantumZipper
