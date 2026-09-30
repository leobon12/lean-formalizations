import QuantumZipper.Proofs.Thm18.ASepModA

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ASEP (mod B): regime (i) — the energy modulus of `muA0` at radii `≥ r₀`

`energy_muA0_large`: for `p = (τ, a)`, `p' = (τ', a')` in `[0,T] × [a₀,a₁]` and radii
`ρ, ρ' ∈ [r₀, 1]`, the Neumann energy of `muA0 p ρ − muA0 p' ρ'` is at most
`2 timeK |τ − τ'|^{α/12} + 2 spaceK (Λ + |ρ − ρ'|)^{1/12}` with the centre modulus
`Λ = e^{2T/m²} |a − a'| (‖d‖ + r) + |W τ − W τ'| + 2|τ − τ'|/m` of (C2).

This is `G4Core.energy_mix_νT_le` (ExclModPt; Hu–Miller–Peres, Ann. Probab. 38 (2010),
Prop. 2.1; Duplantier–Sheffield, Invent. Math. 185 (2011), Prop. 3.1) with base `σ = fc(d, r)`
and centre maps `w ↦ f_τ(a w)` (made measurable off the folded sphere, `gA`), the bound `R` from
`norm_fwdMap_le_any` and `Λ` from `norm_fwdMap_sub_le`. Own bookkeeping.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace QuantumZipper
namespace ASep

open RegCont RegUnif Thm18Asm.G4Core

theorem norm_fwdMap_scaled_le {W : ℝ → ℝ} {d : ℂ} {r a₀ a₁ T m M : ℝ} (hm : 0 < m)
    (ha₀ : 0 < a₀)
    (hgood0 : ∀ a ∈ Icc a₀ a₁, ∀ w ∈ foldSph d r, ∃ u, IsForwardSol W ((a : ℂ) * w) T u)
    (hlow : ∀ z ∈ scaledSph d r a₀ a₁, ∀ s ∈ Icc (0 : ℝ) T, m ≤ ‖fwdMap W s z‖)
    (hM : ∀ t ∈ Icc (0 : ℝ) T, |W t| ≤ M)
    {τ a : ℝ} (hτ : τ ∈ Icc (0 : ℝ) T) (ha : a ∈ Icc a₀ a₁) {x : ℂ} (hx : x ∈ foldSph d r) :
    ‖fwdMap W τ ((a : ℂ) * x)‖ ≤ a₁ * (‖d‖ + r) + M + 2 * T / m := by
  obtain ⟨u, hu⟩ := hgood0 a ha x hx
  have hul : ∀ s ∈ Icc (0 : ℝ) T, m ≤ ‖u s‖ := fun s hs => by
    rw [← fwdMap_eq_any hu hs]; exact hlow _ (mem_scaledSph ha hx) s hs
  have h1 := norm_fwdMap_le_any hu hm hul hτ
  have ha0 : 0 ≤ a := ha₀.le.trans ha.1
  have hxn := norm_le_of_mem_foldSph hx
  have h2 : ‖(a : ℂ) * x‖ ≤ a₁ * (‖d‖ + r) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha0]
    exact mul_le_mul ha.2 hxn (norm_nonneg _) (ha0.trans ha.2)
  linarith [hM τ hτ]

/-- **Regime (i): the energy modulus of `muA0` at radii `≥ r₀`.** -/
theorem energy_muA0_large {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {T α CH : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hCH : 0 ≤ CH)
    (hH : ∀ t ∈ Icc (0 : ℝ) T, ∀ t' ∈ Icc (0 : ℝ) T, |t - t'| ≤ 1 / 2 →
      |W t - W t'| ≤ CH * |t - t'| ^ α)
    {d : ℂ} {r : ℝ} (hr : 0 < r) {a₀ a₁ : ℝ} (ha₀ : 0 < a₀)
    (hgood0 : ∀ a ∈ Icc a₀ a₁, ∀ w ∈ foldSph d r, ∃ u, IsForwardSol W ((a : ℂ) * w) T u)
    {m : ℝ} (hm : 0 < m)
    (hlow : ∀ z ∈ scaledSph d r a₀ a₁, ∀ s ∈ Icc (0 : ℝ) T, m ≤ ‖fwdMap W s z‖)
    {M : ℝ} (hM : ∀ t ∈ Icc (0 : ℝ) T, |W t| ≤ M) {r₀ : ℝ} (hr₀ : 0 < r₀)
    {p p' : Fin 2 → ℝ} (hp0 : p 0 ∈ Icc (0 : ℝ) T) (hp1 : p 1 ∈ Icc a₀ a₁)
    (hp0' : p' 0 ∈ Icc (0 : ℝ) T) (hp1' : p' 1 ∈ Icc a₀ a₁)
    {ρ ρ' : ℝ} (hρ : r₀ ≤ ρ) (hρ1 : ρ ≤ 1) (hρ' : r₀ ≤ ρ') (hρ1' : ρ' ≤ 1) :
    |kernelCov2 neumannH (muA0 W d r p ρ, muA0 W d r p' ρ') (muA0 W d r p ρ, muA0 W d r p' ρ')| ≤
      2 * (timeK M T r₀ (a₁ * (‖d‖ + r) + M + 2 * T / m + 1) CH * |p 0 - p' 0| ^ (α / 12)) +
        2 * (spaceK M T r₀ (a₁ * (‖d‖ + r) + M + 2 * T / m + 1) *
          (Real.exp (2 * T / m ^ 2) * (|p 1 - p' 1| * (‖d‖ + r)) + |W (p 0) - W (p' 0)| +
            2 * |p 0 - p' 0| / m + |ρ - ρ'|) ^ (1 / 12 : ℝ)) := by
  have hT : 0 ≤ T := hp0.1.trans hp0.2
  have hsol : ∀ z ∈ scaledSph d r a₀ a₁, ∃ u, IsForwardSol W z T u := by
    rintro _ ⟨q, hq, rfl⟩; exact hgood0 q.1 hq.1 q.2 hq.2
  have hae := ae_mem_foldSph d hr.le
  have e : ∀ q : Fin 2 → ℝ, ∀ s : ℝ, muA0 W d r q s =
      (bindFc ((foldedCircle d r).map (gA W d r (q 0) (q 1))) s).map (fwdMapInv W (q 0)) := by
    intro q s
    unfold muA0
    rw [Measure.map_congr (hae.mono fun x hx => (gA_of_mem (W := W) (τ := q 0) (a := q 1) hx).symm)]
  rw [e p ρ, e p' ρ']
  refine energy_mix_νT_le hW hW0 hr₀ hM hα hα1 hCH hH
    (measurable_gA hW hW0 hm hgood0 hlow hp0 hp1) (measurable_gA hW hW0 hm hgood0 hlow hp0' hp1')
    hρ hρ' ?_ ?_ hp0 hp0'
  · filter_upwards [hae] with x hx
    rw [gA_of_mem hx, gA_of_mem hx]
    have b1 := norm_fwdMap_scaled_le hm ha₀ hgood0 hlow hM hp0 hp1 hx
    have b2 := norm_fwdMap_scaled_le hm ha₀ hgood0 hlow hM hp0' hp1' hx
    constructor <;> linarith
  · filter_upwards [hae] with x hx
    rw [gA_of_mem hx, gA_of_mem hx]
    have h := norm_fwdMap_sub_le hW hW0 hT hm hsol hlow (mem_scaledSph hp1 hx)
      (mem_scaledSph hp1' hx) hp0 hp0'
    refine h.trans ?_
    have hxn := norm_le_of_mem_foldSph hx
    have hax : ‖(p 1 : ℂ) * x - (p' 1 : ℂ) * x‖ ≤ |p 1 - p' 1| * (‖d‖ + r) := by
      rw [← sub_mul, norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left hxn (abs_nonneg _)
    have := mul_le_mul_of_nonneg_left hax (Real.exp_pos (2 * T / m ^ 2)).le
    linarith

end ASep
end QuantumZipper
