import QuantumZipper.Proofs.Thm18.ASepCentre
import QuantumZipper.Proofs.Thm18.ExclModPt

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ASEP (mod A): the A-sep family at `τ' = 0` and its energy modulus at radii `≥ r₀`

`muA0 W d r p ρ = (f_τ⁻¹)_* ((σ.map (w ↦ f_τ(a w))) ⋆ fc(·, ρ))`, `σ = fc(d, r)`, `p = (τ, a)`.

* `ae_mem_foldSph`: `σ` lives on the compact folded sphere `foldH '' sphere d r`;
* `exists_lower_foldSph`: the centre lower bound (C1) on `{a w : a ∈ [a₀,a₁], w ∈ foldH '' S}`;
* `energy_muA0_large` (regime (i) of the GENERIC-UC plan): for radii `ρ, ρ' ≥ r₀` the Neumann
  energy of `muA0 p ρ − muA0 p' ρ'` is bounded by the mixture modulus `G4Core.energy_mix_νT_le`
  with the centre modulus `Λ` of (C2) (`norm_fwdMap_sub_le`).

Sources: Hu–Miller–Peres, Ann. Probab. 38 (2010), Prop. 2.1 and Duplantier–Sheffield, Invent.
Math. 185 (2011), Prop. 3.1 (through `energy_mix_νT_le`); the rest is own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace QuantumZipper
namespace ASep

open RegCont RegUnif Thm18Asm.G4Core

/-- The A-sep family at `τ' = 0`. -/
def muA0 (W : ℝ → ℝ) (d : ℂ) (r : ℝ) (p : Fin 2 → ℝ) (ρ : ℝ) : Measure ℂ :=
  (bindFc ((foldedCircle d r).map fun w => fwdMap W (p 0) ((p 1 : ℂ) * w)) ρ).map
    (fwdMapInv W (p 0))

/-- The folded sphere, the support of `foldedCircle d r`. -/
def foldSph (d : ℂ) (r : ℝ) : Set ℂ := foldH '' sphere d r

theorem isCompact_foldSph (d : ℂ) (r : ℝ) : IsCompact (foldSph d r) :=
  (isCompact_sphere d r).image TwoPoint.continuous_foldH

theorem norm_foldH_eq (y : ℂ) : ‖foldH y‖ = ‖y‖ := by
  unfold foldH; split_ifs <;> simp

theorem norm_le_of_mem_foldSph {d : ℂ} {r : ℝ} {x : ℂ} (hx : x ∈ foldSph d r) :
    ‖x‖ ≤ ‖d‖ + r := by
  obtain ⟨y, hy, rfl⟩ := hx
  rw [norm_foldH_eq]
  have : ‖y - d‖ = r := by rw [← dist_eq_norm]; exact hy
  calc ‖y‖ = ‖d + (y - d)‖ := by ring_nf
    _ ≤ ‖d‖ + ‖y - d‖ := norm_add_le _ _
    _ = ‖d‖ + r := by rw [this]

theorem ae_mem_foldSph (d : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    ∀ᵐ x ∂foldedCircle d r, x ∈ foldSph d r := by
  have hc : IsClosed (foldSph d r) := (isCompact_foldSph d r).isClosed
  rw [ae_iff]
  show foldedCircle d r (foldSph d r)ᶜ = 0
  unfold foldedCircle circleUnif
  rw [Measure.map_apply measurable_foldH hc.measurableSet.compl, Measure.smul_apply,
    Measure.map_apply (continuous_circleMap d r).measurable
      (measurable_foldH hc.measurableSet.compl)]
  have : circleMap d r ⁻¹' (foldH ⁻¹' (foldSph d r)ᶜ) = ∅ := by
    ext θ
    simp only [mem_preimage, mem_compl_iff, mem_empty_iff_false, iff_false, not_not]
    exact ⟨circleMap d r θ, by
      rw [mem_sphere, dist_eq_norm, circleMap_sub_center, norm_circleMap_zero, abs_of_nonneg hr],
      rfl⟩
  rw [this]; simp

/-- `‖f_t(z)‖ ≤ ‖z‖ + |W t| + 2T/m` along a solution staying at distance `≥ m` from `0`. -/
theorem norm_fwdMap_le_any {W : ℝ → ℝ} {z : ℂ} {T m : ℝ} {u : ℝ → ℂ}
    (hu : IsForwardSol W z T u) (hm : 0 < m) (hlow : ∀ r ∈ Icc (0 : ℝ) T, m ≤ ‖u r‖)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    ‖fwdMap W t z‖ ≤ ‖z‖ + |W t| + 2 * T / m := by
  rw [fwdMap_eq_any hu ht, (hu.2 t ht).2]
  have hI : ‖∫ s in (0 : ℝ)..t, 2 / u s‖ ≤ 2 / m * |t - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun s hs => ?_
    have hsT : s ∈ Icc (0 : ℝ) T := by
      rw [uIoc_of_le ht.1] at hs; exact ⟨hs.1.le, hs.2.trans ht.2⟩
    rw [norm_div]
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    rw [h2]
    exact div_le_div_of_nonneg_left (by norm_num) hm (hlow s hsT)
  have hWn : ‖((W t : ℝ) : ℂ)‖ = |W t| := by rw [Complex.norm_real, Real.norm_eq_abs]
  have ht' : 2 / m * |t - 0| ≤ 2 * T / m := by
    rw [sub_zero, abs_of_nonneg ht.1, div_mul_eq_mul_div]
    gcongr; exact ht.2
  calc ‖z - (W t : ℂ) + ∫ s in (0 : ℝ)..t, 2 / u s‖
      ≤ ‖z - (W t : ℂ)‖ + ‖∫ s in (0 : ℝ)..t, 2 / u s‖ := norm_add_le _ _
    _ ≤ ‖z‖ + ‖((W t : ℝ) : ℂ)‖ + ‖∫ s in (0 : ℝ)..t, 2 / u s‖ := by
        gcongr; exact norm_sub_le _ _
    _ ≤ _ := by rw [hWn]; linarith

/-- The compact set of scaled folded-sphere points. -/
def scaledSph (d : ℂ) (r a₀ a₁ : ℝ) : Set ℂ :=
  (fun q : ℝ × ℂ => (q.1 : ℂ) * q.2) '' (Icc a₀ a₁ ×ˢ foldSph d r)

theorem isCompact_scaledSph (d : ℂ) (r a₀ a₁ : ℝ) : IsCompact (scaledSph d r a₀ a₁) :=
  (isCompact_Icc.prod (isCompact_foldSph d r)).image
    ((Complex.continuous_ofReal.comp continuous_fst).mul continuous_snd)

theorem mem_scaledSph {d : ℂ} {r a₀ a₁ a : ℝ} (ha : a ∈ Icc a₀ a₁) {x : ℂ}
    (hx : x ∈ foldSph d r) : (a : ℂ) * x ∈ scaledSph d r a₀ a₁ :=
  ⟨(a, x), ⟨ha, hx⟩, rfl⟩

/-- The centre map, made measurable off the folded sphere. -/
def gA (W : ℝ → ℝ) (d : ℂ) (r τ a : ℝ) : ℂ → ℂ :=
  by classical exact (foldSph d r).piecewise (fun x => fwdMap W τ ((a : ℂ) * x)) fun _ => 0

theorem gA_of_mem {W : ℝ → ℝ} {d : ℂ} {r τ a : ℝ} {x : ℂ} (hx : x ∈ foldSph d r) :
    gA W d r τ a x = fwdMap W τ ((a : ℂ) * x) := by
  classical
  unfold gA
  convert Set.piecewise_eq_of_mem _ _ _ hx

/-- Data of the regime-(i) estimate: a sup bound for the driver and the (C1) lower bound. -/
theorem measurable_gA {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {d : ℂ} {r a₀ a₁ T m : ℝ} (hm : 0 < m)
    (hgood0 : ∀ a ∈ Icc a₀ a₁, ∀ w ∈ foldSph d r, ∃ u, IsForwardSol W ((a : ℂ) * w) T u)
    (hlow : ∀ z ∈ scaledSph d r a₀ a₁, ∀ s ∈ Icc (0 : ℝ) T, m ≤ ‖fwdMap W s z‖)
    {τ a : ℝ} (hτ : τ ∈ Icc (0 : ℝ) T) (ha : a ∈ Icc a₀ a₁) :
    Measurable (gA W d r τ a) := by
  classical
  have hsol : ∀ z ∈ scaledSph d r a₀ a₁, ∃ u, IsForwardSol W z T u := by
    rintro _ ⟨q, hq, rfl⟩; exact hgood0 q.1 hq.1 q.2 hq.2
  have hc : ContinuousOn (fun x => fwdMap W τ ((a : ℂ) * x)) (foldSph d r) := by
    refine (LipschitzOnWith.of_dist_le' (K := Real.exp (2 * T / m ^ 2) * |a|)
      fun x hx y hy => ?_).continuousOn
    have h := norm_fwdMap_sub_le hW hW0 (hτ.1.trans hτ.2) hm hsol hlow
      (mem_scaledSph ha hx) (mem_scaledSph ha hy) hτ hτ
    simp only [sub_self, abs_zero, mul_zero, zero_div, add_zero] at h
    rw [dist_eq_norm, dist_eq_norm]
    refine h.trans (le_of_eq ?_)
    rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs]; ring
  exact hc.measurable_piecewise continuousOn_const (isCompact_foldSph d r).isClosed.measurableSet

end ASep
end QuantumZipper
