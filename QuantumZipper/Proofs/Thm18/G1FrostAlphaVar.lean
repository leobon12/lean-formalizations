import QuantumZipper.Proofs.Thm18.G1FrostAlphaPot
import QuantumZipper.Proofs.Thm18.G1FrostAlphaDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-FROST-B toolkit, part 2: the variance modulus for a general Frostman exponent `α`

Copy of the sections `Pot`, `Family` and of `pushVar_of_reg` of G1PushVar.lean, and of
`pushFam_pot`, `pushFamBounds_of_var` of G1PathCoordFam.lean, with the Frostman exponent
`1/3 ↦ α` (`0 < α ≤ 1`), using the `α`-toolkit of G1FrostAlphaPot.lean:

* `pushVar_of_reg_α`: for `ψ` continuous on `Hbar`, `ψ(Hbar) ⊆ Hbar`, locally Hölder on `Hbar`
  (exponent `α_H`) and with `α`-Frostman pushed folded circles (`PushFrostmanα α ψ`), the
  smoothed family has the Hölder variance modulus `PushVar ψ β`, `β = min(α_H, 1)·α/2`;
* `pushFam_potα`: the potential clause of `PushFamBounds`;
* `pushFamBounds_of_regα`: `PushFamBounds ψ β`.

Source: the repository's own energy estimates (`TwoPoint.abs_neuPot_le`,
`TwoPoint.abs_neuPot_sub_le`), the Duplantier–Sheffield, Invent. Math. 185 (2011),
Prop. 3.1-type argument. Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Metric Set Function Real
open scoped ENNReal NNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G1RC

open CircleFubini KolmD TwoPoint RegCont

section Potα

variable {ψ : ℂ → ℂ}

/-- `∫ neuPot κ d(pushFam ψ p) = ∫ fcPot κ t⁺ (Φ_q θ) dcircM` (exponent `α`). -/
theorem kernelCov_pushFam_eqα {α : ℝ} (hα : 0 < α) (hH : MapsTo ψ Hbar Hbar)
    {p : Fin (4 + 1) → ℝ}
    (hΦc : Continuous (pushPhi ψ (Fin.init p))) {B CF L : ℝ} (hB0 : 0 ≤ B) (hCF : 0 ≤ CF)
    (hL : 0 ≤ L) (hΦb : ∀ θ, ‖pushPhi ψ (Fin.init p) θ‖ ≤ B) (htL : p (Fin.last 4) ≤ L)
    (κ : Measure ℂ) [IsFiniteMeasure κ] (hFκ : TwoPoint.IsFrostman κ α CF)
    (hBκ : ∀ᵐ y ∂κ, ‖y‖ ≤ B + L) (hmκ : κ.real univ = 1) :
    kernelCov neumannH (pushFam ψ p) κ =
      ∫ θ, fcPot κ (max (p (Fin.last 4)) 0) (pushPhi ψ (Fin.init p) θ) ∂circM := by
  unfold pushFam smoothFam
  split_ifs with ht
  · rw [max_eq_left ht.le]
    have hBμ : ∀ᵐ y ∂(circM.map (pushPhi ψ (Fin.init p))), ‖y‖ ≤ B :=
      (ae_map_iff hΦc.measurable.aemeasurable
        (measurableSet_le measurable_norm measurable_const)).2 (ae_of_all _ hΦb)
    rw [kernelCov_bindFc_eq_Lα hα hB0 hCF hL hBμ ht.le htL κ hFκ hBκ hmκ,
      integral_map hΦc.aemeasurable (measurable_fcPot κ _).aestronglyMeasurable]
  · rw [max_eq_right (not_lt.1 ht)]
    show ∫ x, neuPot κ x ∂(circM.map (pushPhi ψ (Fin.init p))) = _
    rw [integral_map hΦc.aemeasurable (measurable_neuPot κ).aestronglyMeasurable]
    refine integral_congr_ae (ae_of_all _ fun θ => ?_)
    exact (fcPot_zero_of_mem_Hbar (pushPhi_mem_Hbar hH _ θ)).symm

/-- The per-`κ` increment bound (exponent `α`). -/
theorem abs_kernelCov_pushFam_sub_leα {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hH : MapsTo ψ Hbar Hbar) {p p' : Fin (4 + 1) → ℝ}
    (hΦc : Continuous (pushPhi ψ (Fin.init p))) (hΦc' : Continuous (pushPhi ψ (Fin.init p')))
    {B CF L Δ : ℝ} (hB0 : 0 ≤ B) (hCF : 0 ≤ CF) (hL : 0 ≤ L)
    (hΦb : ∀ θ, ‖pushPhi ψ (Fin.init p) θ‖ ≤ B) (hΦb' : ∀ θ, ‖pushPhi ψ (Fin.init p') θ‖ ≤ B)
    (htL : p (Fin.last 4) ≤ L) (htL' : p' (Fin.last 4) ≤ L)
    (hΔ : ∀ θ, ‖pushPhi ψ (Fin.init p) θ - pushPhi ψ (Fin.init p') θ‖ ≤ Δ)
    (κ : Measure ℂ) [IsFiniteMeasure κ] (hFκ : TwoPoint.IsFrostman κ α CF)
    (hBκ : ∀ᵐ y ∂κ, ‖y‖ ≤ B + L) (hmκ : κ.real univ = 1) :
    |kernelCov neumannH (pushFam ψ p) κ - kernelCov neumannH (pushFam ψ p') κ| ≤
      holderKα α CF (B + L) * (Δ + |p (Fin.last 4) - p' (Fin.last 4)|) ^ (α / 2) := by
  rw [kernelCov_pushFam_eqα hα hH hΦc hB0 hCF hL hΦb htL κ hFκ hBκ hmκ,
    kernelCov_pushFam_eqα hα hH hΦc' hB0 hCF hL hΦb' htL' κ hFκ hBκ hmκ]
  set ρ := max (p (Fin.last 4)) 0
  set ρ' := max (p' (Fin.last 4)) 0
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
  set d := holderKα α CF (B + L) * (Δ + |p (Fin.last 4) - p' (Fin.last 4)|) ^ (α / 2)
  have hpt : ∀ θ, |fcPot κ ρ (pushPhi ψ (Fin.init p) θ) - fcPot κ ρ' (pushPhi ψ (Fin.init p') θ)|
      ≤ d := by
    intro θ
    refine (abs_fcPot_sub_le_Lα hα hα1 hCF hB0 hL hFκ hBκ hmκ (hΦb θ) (hΦb' θ) hρ hρ' hρL
      hρL').trans ?_
    refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) ?_ (by linarith))
      (holderKα_nonneg hα hCF (by linarith))
    exact add_le_add (hΔ θ) (abs_max_sub_max_le_abs _ _ _)
  rw [← integral_sub (hint ρ _ hΦc hρ hρL hΦb) (hint ρ' _ hΦc' hρ' hρL' hΦb')]
  calc _ ≤ ∫ θ, |fcPot κ ρ (pushPhi ψ (Fin.init p) θ) -
        fcPot κ ρ' (pushPhi ψ (Fin.init p') θ)| ∂circM := abs_integral_le_integral_abs
    _ ≤ ∫ _θ, d ∂circM := integral_mono ((hint ρ _ hΦc hρ hρL hΦb).sub
        (hint ρ' _ hΦc' hρ' hρL' hΦb')).abs (integrable_const d) hpt
    _ = d := by simp

end Potα

section Familyα

variable {ψ : ℂ → ℂ}

theorem isFrostman_pushFamα {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {C : ℝ} (hC : 0 ≤ C)
    {p : Fin (4 + 1) → ℝ}
    (hFq : TwoPoint.IsFrostman (circM.map (pushPhi ψ (Fin.init p))) α C) :
    TwoPoint.IsFrostman (pushFam ψ p) α (24 * C) := by
  unfold pushFam smoothFam
  split_ifs with ht
  · exact isFrostman_bindFcα hα hα1 hFq ht.le
  · intro w r hr
    refine (hFq w r hr).trans ?_
    have := Real.rpow_nonneg hr.le α
    nlinarith

/-- **Energy increment of two members** of the smoothed pushed-circle family (exponent `α`). -/
theorem abs_kernelCov2_pushFam_leα {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hH : MapsTo ψ Hbar Hbar) {p p' : Fin (4 + 1) → ℝ}
    (hΦc : Continuous (pushPhi ψ (Fin.init p))) (hΦc' : Continuous (pushPhi ψ (Fin.init p')))
    {B C L Δ : ℝ} (hB0 : 0 ≤ B) (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hF : TwoPoint.IsFrostman (circM.map (pushPhi ψ (Fin.init p))) α C)
    (hF' : TwoPoint.IsFrostman (circM.map (pushPhi ψ (Fin.init p'))) α C)
    (hΦb : ∀ θ, ‖pushPhi ψ (Fin.init p) θ‖ ≤ B) (hΦb' : ∀ θ, ‖pushPhi ψ (Fin.init p') θ‖ ≤ B)
    (htL : p (Fin.last 4) ≤ L) (htL' : p' (Fin.last 4) ≤ L)
    (hΔ : ∀ θ, ‖pushPhi ψ (Fin.init p) θ - pushPhi ψ (Fin.init p') θ‖ ≤ Δ) :
    |kernelCov2 neumannH (pushFam ψ p, pushFam ψ p') (pushFam ψ p, pushFam ψ p')| ≤
      2 * holderKα α (24 * C) (B + L) *
        (Δ + |p (Fin.last 4) - p' (Fin.last 4)|) ^ (α / 2) := by
  have := isProbabilityMeasure_pushFam ψ p
  have := isProbabilityMeasure_pushFam ψ p'
  have hC24 : 0 ≤ 24 * C := by positivity
  have h1 := abs_kernelCov_pushFam_sub_leα hα hα1 hH hΦc hΦc' hB0 hC24 hL hΦb hΦb' htL htL' hΔ
    (pushFam ψ p) (isFrostman_pushFamα hα hα1 hC hF)
    (ae_norm_pushFam_le hΦc.measurable hΦb hL htL) (by simp)
  have h2 := abs_kernelCov_pushFam_sub_leα hα hα1 hH hΦc hΦc' hB0 hC24 hL hΦb hΦb' htL htL' hΔ
    (pushFam ψ p') (isFrostman_pushFamα hα hα1 hC hF')
    (ae_norm_pushFam_le hΦc'.measurable hΦb' hL htL') (by simp)
  have e : kernelCov2 neumannH (pushFam ψ p, pushFam ψ p') (pushFam ψ p, pushFam ψ p') =
      (kernelCov neumannH (pushFam ψ p) (pushFam ψ p) -
        kernelCov neumannH (pushFam ψ p') (pushFam ψ p)) -
      (kernelCov neumannH (pushFam ψ p) (pushFam ψ p') -
        kernelCov neumannH (pushFam ψ p') (pushFam ψ p')) := by
    unfold kernelCov2; ring
  rw [e]
  refine (abs_sub _ _).trans ?_
  linarith

end Familyα

/-- **The variance clause of `PushFamBounds` from Hölder regularity and the `α`-Frostman
bound** (copy of `pushVar_of_reg` with `1/3 ↦ α`). -/
theorem pushVar_of_reg_α {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {ψ : ℂ → ℂ}
    (hc : ContinuousOn ψ Hbar) (hH : MapsTo ψ Hbar Hbar) (hHol : LocHolderHbar ψ)
    (hF : PushFrostmanα α ψ) : ∃ β : ℝ, 0 < β ∧ PushVar ψ β := by
  obtain ⟨αH, hαH, hHα⟩ := hHol
  set a := min αH 1 with ha
  have ha0 : 0 < a := lt_min hαH one_pos
  have hα2 : 0 ≤ α / 2 := by linarith
  refine ⟨a * (α / 2), mul_pos ha0 (by linarith), fun R => ?_⟩
  set Rr : ℝ := (R : ℝ) with hRrdef
  have hRr : 0 ≤ Rr := Nat.cast_nonneg R
  set eR := Real.exp Rr
  have heR : 0 < eR := Real.exp_pos _
  set R1 := 2 * Rr + eR
  have hR1 : 0 ≤ R1 := by positivity
  obtain ⟨C0, hC0⟩ := hHα R1
  set CH := max C0 0
  have hCH : 0 ≤ CH := le_max_right _ _
  have hHCH : ∀ z ∈ Hbar, ∀ w ∈ Hbar, ‖z‖ ≤ R1 → ‖w‖ ≤ R1 →
      ‖ψ z - ψ w‖ ≤ CH * ‖z - w‖ ^ αH := fun z hz w hw hzR hwR =>
    (hC0 z hz w hw hzR hwR).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (norm_nonneg _) _))
  set M := ‖ψ 0‖ + CH * R1 ^ αH
  have h0H : (0 : ℂ) ∈ Hbar := by show (0 : ℝ) ≤ (0 : ℂ).im; simp
  have hM : ∀ z ∈ Hbar, ‖z‖ ≤ R1 → ‖ψ z‖ ≤ M := fun z hz hzR => by
    have h1 := hHCH z hz 0 h0H hzR (by simpa using hR1)
    rw [sub_zero] at h1
    have h2 : ‖z‖ ^ αH ≤ R1 ^ αH := Real.rpow_le_rpow (norm_nonneg _) hzR hαH.le
    have h3 := norm_sub_norm_le (ψ z) (ψ 0)
    have h4 := mul_le_mul_of_nonneg_left h2 hCH
    linarith
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 h0H (by simpa using hR1))
  set B := eR * M
  have hB0 : 0 ≤ B := by positivity
  obtain ⟨C, hC, hCF⟩ := hF R
  set D := 2 * Rr
  set K0 := (eR * M + 1) * D ^ (1 - a) + eR * CH * (2 + eR) ^ αH * D ^ (αH - a)
  have hK0 : 0 ≤ K0 := by positivity
  have hKH := holderKα_nonneg hα (by positivity : (0 : ℝ) ≤ 24 * C) (by positivity : 0 ≤ B + Rr)
  refine ⟨2 * holderKα α (24 * C) (B + Rr) * K0 ^ (α / 2),
    by have := Real.rpow_nonneg hK0 (α / 2); positivity, fun p hp p' hp' => ?_⟩
  have hq := init_mem_boxD hp
  have hq' := init_mem_boxD hp'
  have hΦc : ∀ q : Fin 4 → ℝ, Continuous (pushPhi ψ q) := fun q =>
    (continuous_pushPhi hc).comp (continuous_const.prodMk continuous_id)
  set δ := ‖p - p'‖
  have hδ : 0 ≤ δ := norm_nonneg _
  have hδD : δ ≤ D := abs_apply_sub_le_of_boxD hp hp'
  set Δ := eR * M * δ + eR * CH * ((2 + eR) * δ) ^ αH
  have hΔ : ∀ θ, ‖pushPhi ψ (Fin.init p) θ - pushPhi ψ (Fin.init p') θ‖ ≤ Δ := fun θ => by
    refine (norm_pushPhi_sub_le hCH hM hHCH hαH hq hq' θ).trans ?_
    have hi := norm_init_sub_le (p := p) (p' := p')
    have h1 : eR * M * ‖Fin.init p - Fin.init p'‖ ≤ eR * M * δ :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    have h2 : ((2 + eR) * ‖Fin.init p - Fin.init p'‖) ^ αH ≤ ((2 + eR) * δ) ^ αH :=
      Real.rpow_le_rpow (by positivity) (mul_le_mul_of_nonneg_left hi (by positivity)) hαH.le
    have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ eR * CH)
    linarith
  have htR : ∀ r : Fin (4 + 1) → ℝ, r ∈ boxD (d := 4 + 1) R → r (Fin.last 4) ≤ Rr :=
    fun r hr => (abs_le.1 (hr (Fin.last 4))).2
  have hmain := abs_kernelCov2_pushFam_leα hα hα1 hH (hΦc _) (hΦc _) hB0 hC hRr
    (hCF _ hq) (hCF _ hq') (fun θ => norm_pushPhi_le hM hq θ) (fun θ => norm_pushPhi_le hM hq' θ)
    (htR p hp) (htR p' hp') hΔ
  refine hmain.trans ?_
  have ht : |p (Fin.last 4) - p' (Fin.last 4)| ≤ δ := by
    have := norm_le_pi_norm (p - p') (Fin.last 4)
    simpa using this
  have hE : Δ + |p (Fin.last 4) - p' (Fin.last 4)| ≤ K0 * δ ^ a := by
    have e1 : δ ≤ D ^ (1 - a) * δ ^ a := by
      have := rpow_le_bound_mul_rpow hδ hδD ha0 (min_le_right αH 1)
      rwa [Real.rpow_one] at this
    have e2 : δ ^ αH ≤ D ^ (αH - a) * δ ^ a :=
      rpow_le_bound_mul_rpow hδ hδD ha0 (min_le_left αH 1)
    have e3 : ((2 + eR) * δ) ^ αH = (2 + eR) ^ αH * δ ^ αH := Real.mul_rpow (by positivity) hδ
    have e4 := mul_le_mul_of_nonneg_left e1 (by positivity : 0 ≤ eR * M + 1)
    have e5 := mul_le_mul_of_nonneg_left e2 (by positivity : 0 ≤ eR * CH * (2 + eR) ^ αH)
    have e6 : Δ = eR * M * δ + eR * CH * (2 + eR) ^ αH * δ ^ αH := by
      simp only [Δ, e3]; ring
    rw [e6]
    nlinarith
  calc 2 * holderKα α (24 * C) (B + Rr) *
        (Δ + |p (Fin.last 4) - p' (Fin.last 4)|) ^ (α / 2)
      ≤ 2 * holderKα α (24 * C) (B + Rr) * (K0 * δ ^ a) ^ (α / 2) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hE hα2)
          (by positivity)
    _ = 2 * holderKα α (24 * C) (B + Rr) * K0 ^ (α / 2) * δ ^ (a * (α / 2)) := by
        rw [Real.mul_rpow hK0 (Real.rpow_nonneg hδ _), ← Real.rpow_mul hδ]; ring

/-- **Potential clause** of `PushFamBounds`, from `PushFrostmanα` (copy of `pushFam_pot`). -/
theorem pushFam_potα {α : ℝ} (hα : 0 < α) {ψ : ℂ → ℂ} (hF : PushFrostmanα α ψ) (R : ℕ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ q ∈ KolmD.boxD (d := 4 + 1) R, ∀ y : ℂ,
      ∫⁻ x, ENNReal.ofReal (-Real.log ‖x - y‖) ∂(pushFam ψ q) ≤ C := by
  obtain ⟨C, hC0, hC⟩ := hF R
  set K := ENNReal.ofReal (2 * Real.log 2 + 2 * Real.posLog R)
  refine ⟨2 * ENNReal.ofReal (C / α) + 2 * K, by finiteness, fun q hq y => ?_⟩
  have hFq : TwoPoint.IsFrostman (circM.map (pushPhi ψ (Fin.init q))) α C :=
    hC _ (init_mem_boxD hq)
  unfold pushFam smoothFam
  split_ifs with ht
  · exact bind_pot_le hFq hα hC0 ht (abs_le.1 (hq (Fin.last 4))).2 y
  · refine (frostman_pot_le hFq hα hC0 y).trans ?_
    calc ENNReal.ofReal (C / α) ≤ 2 * ENNReal.ofReal (C / α) := by
          rw [two_mul]; exact le_self_add
      _ ≤ _ := le_self_add

/-- **`PushFamBounds` from continuity, Hölder regularity and the `α`-Frostman bound.** -/
theorem pushFamBounds_of_regα {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {ψ : ℂ → ℂ}
    (hc : ContinuousOn ψ Hbar) (hH : MapsTo ψ Hbar Hbar) (hHol : LocHolderHbar ψ)
    (hF : PushFrostmanα α ψ) : ∃ β : ℝ, 0 < β ∧ PushFamBounds ψ β := by
  obtain ⟨β, hβ, hV⟩ := pushVar_of_reg_α hα hα1 hc hH hHol hF
  exact ⟨β, hβ, isProbabilityMeasure_pushFam ψ,
    fun R => ⟨pushFam_support hc hH R, pushFam_potα hα hF R, hV R⟩⟩

end G1RC
end Thm18Asm
end QuantumZipper
