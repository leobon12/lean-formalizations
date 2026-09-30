import QuantumZipper.Proofs.Zipper.JointModAssembly
import QuantumZipper.Proofs.Zipper.Cor15RezipRegTame

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# UNZIP-EXPMOM, Gaussian part: exponential moments of the free-field part for a fixed driver

For a fixed good path `f` (continuous, vanishing at `0`, `1/3`-Hölder) with driver
`W = Wof κ 1 f`, `|W| ≤ M` on `[0,1]`, and a free-boundary GFF `X` pinned at the unit semicircle
(`X ω (fc(0,1)) = 0` for every `ω`), the free-field part `ZE(f, X ω)` of the raw value
`h⁰_t(fc(0,1))` (the continuous extension of `JointModRandom`) satisfies, for every `s ∈ ℝ`,

`E exp(s · ZE(f, X)(t, 0, 1)) ≤ exp(unzipVarC M · s² / 2)`       (`unzipExpMom_fixed_le`),

with `unzipVarC M = 4 · potMax (frostC 1 1 1) (revBound (2M) 1 1)`, a constant of order
`log (1 + M)` (`unzipExpMom_exp_varC_le`). Indeed a.s. `ZE(f, X) = X(ν) − X(fc(0,1))` with
`ν = (f_t⁻¹)_* fc(0,1)` (the fibre statement `ae_fibre4` and `ae_evalReg_eq_frostman`), a centred
Gaussian of variance `kernelCov2 neumannH (ν, fc(0,1))`, bounded by the uniform Frostman and
support bounds of the pushed circle (`abs_kernelCov2_le_four_potMax`).

Also: `unzipExpMom_lintegral_indep` (integrals of functions of independent variables, Fubini
over the product law), used to condition on the driver.

Sources: Gaussian moment generating function (mathlib `mgf_id_gaussianReal`); the variance
bound assembles the repository's Frostman/potential bounds (`JointModKolm`, which follow
Duplantier–Sheffield, Invent. Math. 185 (2011), Prop. 3.1). Own elementary assembly.
-/

noncomputable section

open Complex Filter MeasureTheory ProbabilityTheory Set
open scoped Topology Real ENNReal NNReal

namespace QuantumZipper
namespace RegUnif

open CharFun TwoPoint RegCont KolmD RegSample

/-- **Integrals over independent variables** (Fubini over the product law). -/
theorem unzipExpMom_lintegral_indep {α β Ω : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {g : Ω → α} {Y : Ω → β}
    (hg : Measurable g) (hY : Measurable Y) (hind : IndepFun g Y P) {F : α × β → ℝ≥0∞}
    (hF : Measurable F) :
    ∫⁻ ω, F (g ω, Y ω) ∂P = ∫⁻ ω, ∫⁻ ω', F (g ω, Y ω') ∂P ∂P := by
  have hprod := (indepFun_iff_map_prod_eq_prod_map_map hg.aemeasurable hY.aemeasurable).1 hind
  calc ∫⁻ ω, F (g ω, Y ω) ∂P = ∫⁻ p, F p ∂(P.map fun ω => (g ω, Y ω)) :=
        (lintegral_map hF (hg.prodMk hY)).symm
    _ = ∫⁻ p, F p ∂((P.map g).prod (P.map Y)) := by rw [hprod]
    _ = ∫⁻ a, ∫⁻ b, F (a, b) ∂(P.map Y) ∂(P.map g) := lintegral_prod _ hF.aemeasurable
    _ = ∫⁻ ω, ∫⁻ b, F (g ω, b) ∂(P.map Y) ∂P := lintegral_map hF.lintegral_prod_right' hg
    _ = ∫⁻ ω, ∫⁻ ω', F (g ω, Y ω') ∂P ∂P :=
        lintegral_congr fun ω => lintegral_map (hF.comp measurable_prodMk_left) hY

/-- The exponential moment of a centred Gaussian variable. -/
theorem unzipExpMom_lintegral_exp_gauss {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {U : Ω → ℝ} (hU : Measurable U) {v : ℝ≥0} (hlaw : P.map U = gaussianReal 0 v) (s : ℝ) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (s * U ω)) ∂P = ENNReal.ofReal (Real.exp (v * s ^ 2 / 2)) := by
  have hm : Measurable fun x : ℝ => ENNReal.ofReal (Real.exp (s * x)) := by fun_prop
  rw [← lintegral_map hm hU, hlaw, ← ofReal_integral_eq_lintegral_ofReal
    (integrable_exp_mul_gaussianReal s) (ae_of_all _ fun x => (Real.exp_pos _).le)]
  congr 1
  have h := congrFun (mgf_id_gaussianReal (μ := 0) (v := v)) s
  simp only [mgf, id] at h
  rw [h, zero_mul, zero_add]

/-- **Exponential moments of a GFF difference**, from a bound on its variance. -/
theorem unzipExpMom_lintegral_exp_diff_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → FieldSample} (hX : IsFreeGFFModConstH X P)
    {a b : Measure ℂ} (ha : IsAdmissibleH a) (hb : IsAdmissibleH b) (hmass : a univ = b univ)
    (s : ℝ) {V : ℝ} (hV : |kernelCov2 neumannH (a, b) (a, b)| ≤ V) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (s * (X ω a - X ω b))) ∂P ≤
      ENNReal.ofReal (Real.exp (V * s ^ 2 / 2)) := by
  have hg := unzipExpMom_lintegral_exp_gauss (U := fun ω => X ω a - X ω b)
    ((hX.measurable_coord _).sub (hX.measurable_coord _))
    (map_diff_eq_gaussianReal hX ha hb hmass) s
  refine le_of_eq_of_le hg ?_
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
  have hv : ((kernelCov2 neumannH (a, b) (a, b)).toNNReal : ℝ) ≤ V := by
    rw [Real.coe_toNNReal']
    exact max_le ((le_abs_self _).trans hV) ((abs_nonneg _).trans hV)
  have hs : 0 ≤ s ^ 2 := sq_nonneg s
  have := mul_le_mul_of_nonneg_right hv hs
  linarith

/-- The unit semicircle is `1/3`-Frostman with constant `frostC 1 1 1`. -/
theorem unzipExpMom_isFrostman_fc01 :
    TwoPoint.IsFrostman (foldedCircle 0 1) (1 / 3) (frostC 1 1 1) := by
  have hC : (6 : ℝ) ≤ frostC 1 1 1 := by
    unfold frostC
    rw [Real.sqrt_one]
    norm_num
    nlinarith [Real.sqrt_nonneg 5]
  intro w ρ hρ
  have h1 := Cor15Group.isFrostman_fc (0 : ℂ) one_pos w ρ hρ
  have hp : 0 ≤ ρ ^ (1 / 3 : ℝ) := Real.rpow_nonneg hρ.le _
  rcases le_total ρ 1 with h | h
  · refine h1.trans ?_
    have e : ρ ^ (1 : ℝ) ≤ ρ ^ (1 / 3 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge hρ h (by norm_num)
    have : 6 / (1 : ℝ) * ρ ^ (1 : ℝ) ≤ 6 * ρ ^ (1 / 3 : ℝ) := by linarith
    nlinarith
  · have hle : ((foldedCircle (0 : ℂ) 1) (Metric.closedBall w ρ)).toReal ≤ 1 :=
      ENNReal.toReal_le_of_le_ofReal zero_le_one (by rw [ENNReal.ofReal_one]; exact prob_le_one)
    have : 1 ≤ ρ ^ (1 / 3 : ℝ) := Real.one_le_rpow h (by norm_num)
    nlinarith

/-- The variance constant `4 · potMax (frostC 1 1 1) (revBound (2M) 1 1)`. -/
def unzipVarC (M : ℝ) : ℝ := 4 * potMax (frostC 1 1 1) (revBound (2 * M) 1 1)

/-- **Fixed driver:** exponential moments of the free-field part of `h⁰_t(fc(0,1))`. -/
theorem unzipExpMom_fixed_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → FieldSample} (hX : IsFreeGFFModConstH X P)
    (hN : ∀ ω, X ω (foldedCircle 0 1) = 0) (κ : ℝ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (s : ℝ)
    {f : C(Icc (0 : ℝ) 1, ℝ)} (hf : f ∈ GoodP zero_le_one (1 / 3)) {M : ℝ}
    (hM : ∀ u ∈ Icc (0 : ℝ) 1, |Wof κ 1 zero_le_one f u| ≤ M) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp
        (s * ZE zero_le_one κ (f, X ω) (pr4 (t, ((0 : ℂ), (1 : ℝ)))))) ∂P ≤
      ENNReal.ofReal (Real.exp (unzipVarC M * s ^ 2 / 2)) := by
  set W := Wof κ 1 zero_le_one f with hWdef
  have hf0 : W 0 = 0 := Wof_zero_of_GoodP zero_le_one κ hf
  have hWc : Continuous W := continuous_Wof κ 1 zero_le_one f
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 ⟨le_rfl, zero_le_one⟩)
  set q := pr4 (t, ((0 : ℂ), (1 : ℝ))) with hq
  have hp : (t, ((0 : ℂ), (1 : ℝ))) ∈ parSet 1 :=
    ⟨ht, show (0 : ℝ) ≤ (0 : ℂ).im by simp, show (0 : ℝ) < 1 from one_pos⟩
  have hν : ν4 W 1 q = νT W 0 1 t := ν4_pr4 W hp
  obtain ⟨i1, f1, b1⟩ := νT_box_facts (r₀ := 1) (R := 1) (w := (0 : ℂ)) (r := 1) hWc hf0 one_pos hM ht le_rfl
    (by simp)
  set ν := νT W 0 1 t with hνdef
  set Rb := revBound (2 * M) 1 1 with hRb
  have hRb1 : 1 ≤ Rb := by
    rw [hRb]; unfold revBound; rw [abs_one]; linarith
  have hsupp : ν (Metric.closedBall (0 : ℂ) Rb ∩ Hbar)ᶜ = 0 :=
    ae_iff.1 (b1.mono fun z hz =>
      ⟨mem_closedBall_zero_iff.2 hz.2, (show (0 : ℝ) < z.im from hz.1).le⟩)
  have hadν : IsAdmissibleH ν := FrostmanReg.isAdmissibleH_of_frostman hsupp f1 (by norm_num)
  have hbfc : ∀ᵐ y ∂foldedCircle (0 : ℂ) 1, ‖y‖ ≤ Rb :=
    (foldedCircle_ae_norm_le (0 : ℂ) zero_le_one).mono fun y hy => by
      rw [norm_zero, zero_add] at hy; linarith
  have hsuppfc : foldedCircle (0 : ℂ) 1 (Metric.closedBall (0 : ℂ) 1 ∩ Hbar)ᶜ = 0 := by
    refine ae_iff.1 ?_
    filter_upwards [foldedCircle_ae_norm_le (0 : ℂ) zero_le_one,
      foldedCircle_ae_mem_H (0 : ℂ) one_pos] with y hy hyH
    rw [norm_zero, zero_add] at hy
    exact ⟨mem_closedBall_zero_iff.2 hy, (show (0 : ℝ) < y.im from hyH).le⟩
  have hadfc : IsAdmissibleH (foldedCircle (0 : ℂ) 1) :=
    FrostmanReg.isAdmissibleH_of_frostman hsuppfc (Cor15Group.isFrostman_fc (0 : ℂ) one_pos)
      one_pos
  have hV : |kernelCov2 neumannH (ν, foldedCircle 0 1) (ν, foldedCircle 0 1)| ≤ unzipVarC M :=
    abs_kernelCov2_le_four_potMax (frostC_nonneg zero_le_one one_pos)
      (by linarith) f1 unzipExpMom_isFrostman_fc01 (b1.mono fun z hz => hz.2) hbfc
  have hmass : ν univ = foldedCircle (0 : ℂ) 1 univ := by
    rw [measure_univ, measure_univ]
  refine le_of_eq_of_le ?_ (unzipExpMom_lintegral_exp_diff_le hX hadν hadfc hmass s hV)
  refine lintegral_congr_ae ?_
  filter_upwards [ae_fibre4 hX one_pos κ q f,
    FrostmanReg.ae_evalReg_eq_frostman hX hsupp f1 (by norm_num)] with ω hE hev
  rcases hE with h | ⟨⟨hU, hext⟩, -⟩
  · exact absurd hf h.1
  have hU' : UCD (Gm zero_le_one κ (f, X ω)) := hU
  have hext' : extD (Gm zero_le_one κ (f, X ω)) q = Gm zero_le_one κ (f, X ω) q := hext
  have hZ : ZE zero_le_one κ (f, X ω) q = X ω ν - X ω (foldedCircle 0 1) := by
    simp only [ZE, hU', ↓reduceIte]
    rw [hext', Gm_eq zero_le_one κ q hf0, hν, hev, hN, sub_zero]
  rw [hZ]

/-- **The variance constant is logarithmic:** `exp(unzipVarC (a m) · s²/2) ≤ K · (1 + m)^{4s²}`
with `K = exp(12 s² frostC 1 1 1) (40 a + 21)^{4s²}`. -/
theorem unzipExpMom_exp_varC_le {a m : ℝ} (ha : 0 ≤ a) (hm : 0 ≤ m) (s : ℝ) :
    Real.exp (unzipVarC (a * m) * s ^ 2 / 2) ≤
      Real.exp (12 * s ^ 2 * frostC 1 1 1) * (40 * a + 21) ^ (4 * s ^ 2) *
        (1 + m) ^ (4 * s ^ 2) := by
  have hx : 0 < 40 * (a * m) + 21 := by positivity
  have hrev : revBound (2 * (a * m)) 1 1 + revBound (2 * (a * m)) 1 1 + 1 =
      40 * (a * m) + 21 := by
    unfold revBound; rw [abs_one]; ring
  have e : unzipVarC (a * m) * s ^ 2 / 2 =
      12 * s ^ 2 * frostC 1 1 1 + Real.log (40 * (a * m) + 21) * (4 * s ^ 2) := by
    unfold unzipVarC potMax; rw [hrev]; ring
  rw [e, Real.exp_add, ← Real.rpow_def_of_pos hx]
  have h2 : (40 * (a * m) + 21) ^ (4 * s ^ 2) ≤
      (40 * a + 21) ^ (4 * s ^ 2) * (1 + m) ^ (4 * s ^ 2) := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    exact Real.rpow_le_rpow hx.le (by nlinarith [mul_nonneg ha hm]) (by positivity)
  calc _ ≤ Real.exp (12 * s ^ 2 * frostC 1 1 1) *
        ((40 * a + 21) ^ (4 * s ^ 2) * (1 + m) ^ (4 * s ^ 2)) :=
        mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
    _ = _ := by ring

end RegUnif
end QuantumZipper
