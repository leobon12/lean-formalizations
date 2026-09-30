import QuantumZipper.Proofs.Thm18.A1RSFrostAll
import QuantumZipper.Proofs.Thm18.A1RSCouple

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# A1RS (10): the radius modulus of the smeared-loop family

For a probability measure `μ` on `ℍ̄` with support in `closedBall 0 R₁` and mass
`μ{Im ≤ δ} ≤ C_m δ^{1/2}` near `ℝ`, and smeared measures
`ν_ρ = (μ ⊗ angMeas).map (f_t⁻¹ ∘ U_ρ)` (`U_ρ(z, θ) = fold(z + ρ e^{iθ})`) that are `α`-Frostman
with one constant for `ρ ∈ [0, 1]`:

**`abs_kernelCov2_smeared_radius_le`**:
`|E(ν_ρ − ν_ρ')| ≤ C₁ |ρ − ρ'|^{min(α/4, 1/8)}` for `ρ, ρ' ∈ [0, 1]`, with an explicit `C₁`.

Coupling at the same `(z, θ)` (`abs_kernelCov2_map_le`, A1RSCouple.lean): `‖U_ρ − U_ρ'‖ ≤ |ρ − ρ'|`;
off the strips `{Im U_ρ ≤ τ} ∪ {Im U_ρ' ≤ τ}` (mass `≤ 2 (2C_m + 2) τ^{1/4}`, `prod_strip_le`) the
map `f_t⁻¹` is `M/τ`-Lipschitz (`norm_fwdMapInv_sub_mul_le`); take `τ = |ρ − ρ'|^{1/2}`. This is the
radius modulus of Duplantier–Sheffield, Invent. Math. 185 (2011), Prop. 3.1 (circle averages,
there in the flat chart), transported through the Loewner map; own elementary argument.
-/

noncomputable section

open MeasureTheory Set Filter Metric Complex
open scoped Topology ENNReal

namespace QuantumZipper
namespace R18
namespace A1RS

open Thm18Asm Thm18Asm.G1RC TwoPoint

/-- The smearing map at radius `ρ`. -/
abbrev smearF (W : ℝ → ℝ) (t ρ : ℝ) (p : ℂ × ℝ) : ℂ := fwdMapInv W t (foldH (circleMap p.1 ρ p.2))

theorem norm_circleMap_sub_radius (z : ℂ) (ρ ρ' θ : ℝ) :
    ‖circleMap z ρ θ - circleMap z ρ' θ‖ = |ρ - ρ'| := by
  have e : circleMap z ρ θ - circleMap z ρ' θ = ((ρ - ρ' : ℝ) : ℂ) * Complex.exp (θ * Complex.I) := by
    simp only [circleMap]; push_cast; ring
  rw [e, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs]

/-- **Radius modulus of the smeared measures.** -/
theorem abs_kernelCov2_smeared_radius_le {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    {t T : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) {μ : Measure ℂ} [IsProbabilityMeasure μ]
    {R₁ Cm α CF Bf : ℝ} (hR₁ : 0 ≤ R₁) (hCm : 0 ≤ Cm) (hα : 0 < α) (hα1 : α ≤ 1) (hCF : 0 ≤ CF)
    (hBf0 : 0 ≤ Bf) (hsupp : ∀ᵐ z ∂μ, 0 ≤ z.im ∧ ‖z‖ ≤ R₁)
    (hmass : ∀ δ : ℝ, 0 < δ → μ.real {z : ℂ | z.im ≤ δ} ≤ Cm * δ ^ (1 / 2 : ℝ))
    (hF : ∀ ρ ∈ Icc (0 : ℝ) 1,
      IsFrostman ((μ.prod E6.XAreaPC.angMeas).map (smearF W t ρ)) α CF)
    (hBf : ∀ u : ℂ, ‖u‖ ≤ R₁ + 1 → ‖fwdMapInv W t u‖ ≤ Bf)
    {ρ ρ' : ℝ} (hρ : ρ ∈ Icc (0 : ℝ) 1) (hρ' : ρ' ∈ Icc (0 : ℝ) 1) :
    |kernelCov2 neumannH ((μ.prod E6.XAreaPC.angMeas).map (smearF W t ρ),
        (μ.prod E6.XAreaPC.angMeas).map (smearF W t ρ'))
      ((μ.prod E6.XAreaPC.angMeas).map (smearF W t ρ),
        (μ.prod E6.XAreaPC.angMeas).map (smearF W t ρ'))| ≤
      2 * (holderKα α CF Bf * Real.sqrt ((R₁ + 1) ^ 2 + 4 * T) ^ (α / 2) +
        4 * potMaxα α CF Bf * (2 * Cm + 2)) * |ρ - ρ'| ^ min (α / 4) (1 / 8 : ℝ) := by
  set m := μ.prod E6.XAreaPC.angMeas with hm
  set Mb := Real.sqrt ((R₁ + 1) ^ 2 + 4 * T) with hMb
  have hT0 : 0 ≤ T := ht.trans htT
  have hMb0 : 0 < Mb := Real.sqrt_pos.2 (by nlinarith)
  have hgm : Measurable (fwdMapInv W t) := RTBeur.measurable_fwdMapInv_rt hW hW0 ht
  have hFm : ∀ σ : ℝ, Measurable (smearF W t σ) := fun σ => A1RF.measurable_smear hgm σ
  set KH := holderKα α CF Bf with hKH
  set Pm := potMaxα α CF Bf with hPm
  have hKH0 : 0 ≤ KH := holderKα_nonneg hα hCF hBf0
  have hPm0 : 0 ≤ Pm := potMaxα_nonneg hα hCF hBf0
  set h := |ρ - ρ'| with hh
  have hh0 : 0 ≤ h := abs_nonneg _
  have hh1 : h ≤ 1 := by
    rw [hh, abs_le]; constructor <;> linarith [hρ.1, hρ.2, hρ'.1, hρ'.2]
  set a₁ := min (α / 4) (1 / 8 : ℝ) with ha₁
  have ha₁0 : 0 < a₁ := lt_min (by linarith) (by norm_num)
  have hCnn : 0 ≤ 2 * (KH * Mb ^ (α / 2) + 4 * Pm * (2 * Cm + 2)) := by
    have := Real.rpow_nonneg hMb0.le (α / 2)
    positivity
  rcases eq_or_lt_of_le hh0 with h0 | hpos
  · -- equal radii
    have hρρ : ρ = ρ' := by
      have : |ρ - ρ'| = 0 := h0.symm
      linarith [abs_eq_zero.1 this]
    subst hρρ
    have hz : ∀ a b : Measure ℂ, a = b → kernelCov2 neumannH (a, b) (a, b) = 0 := by
      intro a b hab; subst hab; unfold kernelCov2; ring
    rw [hz _ _ rfl, abs_zero]
    exact mul_nonneg hCnn (Real.rpow_nonneg hh0 _)
  -- the far set is null
  set far : Set (ℂ × ℝ) := {p | R₁ < ‖p.1‖} with hfar
  have hfar0 : m far = 0 := by
    have e : far = {z : ℂ | R₁ < ‖z‖} ×ˢ (univ : Set ℝ) := by ext p; simp [hfar]
    rw [e, hm, Measure.prod_prod]
    have : μ {z : ℂ | R₁ < ‖z‖} = 0 := by
      have h2 := hsupp.mono fun z hz => hz.2
      rw [ae_iff] at h2
      simpa [not_le] using h2
    rw [this, zero_mul]
  have hnear : ∀ᵐ p ∂m, ‖p.1‖ ≤ R₁ := by
    rw [ae_iff]
    refine measure_mono_null (fun p hp => ?_) hfar0
    simpa [hfar, not_le] using hp
  have hbd : ∀ σ ∈ Icc (0 : ℝ) 1, ∀ᵐ p ∂m, ‖smearF W t σ p‖ ≤ Bf := fun σ hσ => by
    filter_upwards [hnear] with p hp
    apply hBf
    rw [norm_foldH]
    exact (norm_circleMap_le_add p.1 hσ.1 p.2).trans (by linarith [hσ.2])
  set τ := Real.sqrt h with hτ
  have hτ0 : 0 < τ := Real.sqrt_pos.2 hpos
  have hτ1 : τ ≤ 1 := by rw [hτ]; exact Real.sqrt_le_one.2 hh1
  set E := stripPar ρ τ ∪ stripPar ρ' τ ∪ far with hE
  have hEm : MeasurableSet E :=
    ((measurableSet_stripPar ρ τ).union (measurableSet_stripPar ρ' τ)).union
      (measurableSet_lt measurable_const (measurable_norm.comp measurable_fst))
  have hstrip := fun σ (hσ : σ ∈ Icc (0 : ℝ) 1) =>
    prod_strip_le (μ := μ) (hsupp.mono fun z hz => hz.1) hCm hmass hσ.1 hτ0 hτ1
  have hEε : m.real E ≤ 2 * ((2 * Cm + 2) * τ ^ (1 / 4 : ℝ)) := by
    have h3 : m.real far = 0 := by rw [measureReal_def, hfar0, ENNReal.toReal_zero]
    refine (measureReal_union_le _ _).trans ?_
    rw [h3, add_zero]
    refine (measureReal_union_le _ _).trans ?_
    linarith [hstrip ρ hρ, hstrip ρ' hρ']
  have hclose : ∀ᵐ p ∂m, p ∉ E → ‖smearF W t ρ p - smearF W t ρ' p‖ ≤ Mb * h / τ := by
    refine Eventually.of_forall fun p hp => ?_
    simp only [hE, mem_union, not_or] at hp
    obtain ⟨⟨h1, h2⟩, h3⟩ := hp
    simp only [stripPar, mem_setOf_eq, not_le] at h1 h2
    simp only [hfar, mem_setOf_eq, not_lt] at h3
    have hup : ∀ σ ∈ Icc (0 : ℝ) 1, (foldH (circleMap p.1 σ p.2)).im ≤ R₁ + 1 := fun σ hσ =>
      (le_abs_self _).trans ((Complex.abs_im_le_norm _).trans (by
        rw [norm_foldH]; exact (norm_circleMap_le_add p.1 hσ.1 p.2).trans (by linarith [hσ.2])))
    have key := norm_fwdMapInv_sub_mul_le hW hW0 ht hτ0 h1.le h2.le (hup ρ hρ) (hup ρ' hρ')
    have hU : ‖foldH (circleMap p.1 ρ p.2) - foldH (circleMap p.1 ρ' p.2)‖ ≤ h :=
      (norm_foldH_sub_le _ _).trans (le_of_eq (norm_circleMap_sub_radius _ _ _ _))
    have hsq : Real.sqrt ((R₁ + 1) ^ 2 + 4 * t) ≤ Mb := Real.sqrt_le_sqrt (by linarith)
    rw [le_div_iff₀ hτ0]
    calc ‖smearF W t ρ p - smearF W t ρ' p‖ * τ
        = τ * ‖fwdMapInv W t (foldH (circleMap p.1 ρ p.2)) -
            fwdMapInv W t (foldH (circleMap p.1 ρ' p.2))‖ := by rw [mul_comm]
      _ ≤ Real.sqrt ((R₁ + 1) ^ 2 + 4 * t) *
            ‖foldH (circleMap p.1 ρ p.2) - foldH (circleMap p.1 ρ' p.2)‖ := key
      _ ≤ Mb * h := mul_le_mul hsq hU (norm_nonneg _) hMb0.le
  have hδ : 0 ≤ Mb * h / τ := by positivity
  have hmain := abs_kernelCov2_map_le (m := m) (hFm ρ) (hFm ρ') hα hα1 (hF ρ hρ) (hF ρ' hρ') hCF
    hBf0 (hbd ρ hρ) (hbd ρ' hρ') hEm hδ hEε hclose
  refine hmain.trans ?_
  -- exponent bookkeeping: `Mb h / τ = Mb √h`, `τ^{1/4} = h^{1/8}`
  have hdiv : Mb * h / τ = Mb * h ^ (1 / 2 : ℝ) := by
    rw [hτ, mul_div_assoc, Real.div_sqrt, Real.sqrt_eq_rpow]
  have hτq : τ ^ (1 / 4 : ℝ) = h ^ (1 / 8 : ℝ) := by
    rw [hτ, Real.sqrt_eq_rpow, ← Real.rpow_mul hh0]; norm_num
  have hA : (Mb * h / τ) ^ (α / 2) = Mb ^ (α / 2) * h ^ (α / 4) := by
    rw [hdiv, Real.mul_rpow hMb0.le (Real.rpow_nonneg hh0 _), ← Real.rpow_mul hh0]
    ring_nf
  rw [hA, hτq]
  have e1 : h ^ (α / 4) ≤ h ^ a₁ := Real.rpow_le_rpow_of_exponent_ge hpos hh1 (min_le_left _ _)
  have e2 : h ^ (1 / 8 : ℝ) ≤ h ^ a₁ :=
    Real.rpow_le_rpow_of_exponent_ge hpos hh1 (min_le_right _ _)
  have hMbα : 0 ≤ Mb ^ (α / 2) := Real.rpow_nonneg hMb0.le _
  have f1 := mul_le_mul_of_nonneg_left e1 (mul_nonneg hKH0 hMbα)
  have f2 := mul_le_mul_of_nonneg_left e2 (by positivity : 0 ≤ 4 * Pm * (2 * Cm + 2))
  nlinarith

end A1RS
end R18
end QuantumZipper
