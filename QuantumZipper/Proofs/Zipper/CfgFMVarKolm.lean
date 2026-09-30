import QuantumZipper.Proofs.Zipper.CfgFMVarRepr

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# CFG-FM-VAR (2): Kolmogorov assembly in time

`CfgFM.cfgFMVar_of_energy : (∀ f good, TEnergy (Wof κ T f) T) → CfgFMVarStmt κ T hT`, the time
analogue of `Thm18Asm.g1FMPushVar_of_nodes` (`G1FMVarKolm.lean`).

For fixed `m`, `n ≥ n₀`, `k`, put `Z q = X(P⁺_q) − X(P⁻_q)`, the pushed first-mode pair of
`ψ_t` at the clamped rescaled parameters (`w, τ, s` as in `D3Plus.fmCq/fmRq/fmSq`, and the time
`t = 2^{-3n} clamp_{[0, 2^{3n} T]}(q 4)`). `Z q − Z q'` is a centred Gaussian of variance its
Neumann energy (`RegCont.map_diff_eq_gaussianReal`), bounded by `10 c ‖q − q'‖^{1/3}`: for
`‖q − q'‖ ≤ 1` by the energy node (the time enters as `|Δt|^{1/3} ≤ 2^{-n} ‖Δq‖^{1/3}`), for
`‖q − q'‖ ≥ 1` by the parallelogram bound `G1FM2.kernelCov2_sub_le`. Kolmogorov in `d = 5`
(`p = 60`, `a = 10`) gives a continuous measurable modification, which equals the first mode of
`fZE` on a countable dense subset of the block a.s. (`tRepr`, the fibre identification
`ae_fZE_eq`), hence on the block.

Sources: Duplantier–Sheffield, Invent. Math. 185 (2011), Prop. 3.1; Revuz–Yor, Ch. I, Thm (2.1);
Hu–Miller–Peres, Ann. Probab. 38 (2010), Prop. 2.1 (pattern). Bookkeeping own.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Real ENNReal NNReal

namespace QuantumZipper.E6
namespace CfgFM

open D3Plus KolmD KolmG RegUnif RegCont CharFun RegSample Thm18Asm Thm18Asm.G1FM

/-! ## The time clamp -/

/-- Clamped rescaled time `∈ [0, T]`. -/
def fmTt (T : ℝ) (n : ℕ) (q : Fin 5 → ℝ) : ℝ :=
  (2 : ℝ)⁻¹ ^ (3 * n) * fmCl 0 ((2 : ℝ) ^ (3 * n) * T) (q 4)

theorem fmTt_mem {T : ℝ} (hT : 0 ≤ T) (n : ℕ) (q : Fin 5 → ℝ) : fmTt T n q ∈ Icc 0 T := by
  have h2 : (0 : ℝ) < (2 : ℝ)⁻¹ ^ (3 * n) := by positivity
  have hx : (0 : ℝ) ≤ 2 ^ (3 * n) * T := by positivity
  constructor
  · exact mul_nonneg h2.le (fmCl_ge _ _ _)
  · calc fmTt T n q ≤ (2 : ℝ)⁻¹ ^ (3 * n) * ((2 : ℝ) ^ (3 * n) * T) :=
          mul_le_mul_of_nonneg_left (fmCl_le hx _) h2.le
      _ = T := by rw [← mul_assoc, two_pow_mul_inv_pow, one_mul]

theorem fmTt_fmParamH {T : ℝ} {n : ℕ} {w : ℂ} {τ s t : ℝ} (ht : t ∈ Icc 0 T) :
    fmTt T n (fmParamH n w τ s t) = t := by
  unfold fmTt
  have hx : (0 : ℝ) < 2 ^ (3 * n) := by positivity
  rw [show fmParamH n w τ s t 4 = 2 ^ (3 * n) * t from rfl,
    fmCl_of_mem (mul_nonneg hx.le ht.1) (mul_le_mul_of_nonneg_left ht.2 hx.le),
    ← mul_assoc, two_pow_mul_inv_pow, one_mul]

theorem abs_fmTt_sub_le (T : ℝ) (n : ℕ) (q q' : Fin 5 → ℝ) :
    |fmTt T n q - fmTt T n q'| ≤ (2 : ℝ)⁻¹ ^ (3 * n) * ‖q - q'‖ := by
  have h2 : (0 : ℝ) < (2 : ℝ)⁻¹ ^ (3 * n) := by positivity
  unfold fmTt
  rw [← mul_sub, abs_mul, abs_of_pos h2]
  refine mul_le_mul_of_nonneg_left ((abs_fmCl_sub_le _ _ _ _).trans ?_) h2.le
  have := norm_le_pi_norm (q - q') 4
  simpa [Real.norm_eq_abs] using this

theorem fmPr_fmParamH (n : ℕ) (w : ℂ) (τ s t : ℝ) :
    fmPr (fmParamH n w τ s t) = fmParam n w τ s := by
  funext i; fin_cases i <;> rfl

theorem rpow_third_scale (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    ((2 : ℝ)⁻¹ ^ (3 * n) * x) ^ ((1 : ℝ) / 3) = (2 : ℝ)⁻¹ ^ n * x ^ ((1 : ℝ) / 3) := by
  rw [Real.mul_rpow (by positivity) hx, pow_mul', show (1 : ℝ) / 3 = ((3 : ℕ) : ℝ)⁻¹ by norm_num,
    Real.pow_rpow_inv_natCast (by positivity) (by norm_num)]

/-! ## The pairs -/

/-- Positive pushed first-mode measure at the rescaled parameter `q` (time version). -/
def tPos (W : ℝ → ℝ) (T : ℝ) (m n : ℕ) (k : Fin 2) (q : Fin 5 → ℝ) : Measure ℂ :=
  tfm W (fmTt T n q) (fmCq m n (fmPr q)) ((fmRq n (fmPr q) : ℂ) * fmDir k) (fmSq n (fmPr q))

/-- Negative pushed first-mode measure at the rescaled parameter `q` (time version). -/
def tNeg (W : ℝ → ℝ) (T : ℝ) (m n : ℕ) (k : Fin 2) (q : Fin 5 → ℝ) : Measure ℂ :=
  tfm W (fmTt T n q) (fmCq m n (fmPr q)) (-((fmRq n (fmPr q) : ℂ) * fmDir k))
    (fmSq n (fmPr q))

section Laws

variable {W : ℝ → ℝ} {T : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X : Ω → FieldSample}

theorem tPos_adm (hW : Continuous W) (hW0 : W 0 = 0) (hT : 0 ≤ T) {m n : ℕ}
    (hnm : 2 * (2 : ℝ)⁻¹ ^ n < 1 / ((m : ℝ) + 1)) (k : Fin 2) (q : Fin 5 → ℝ) :
    IsAdmissibleH (tPos W T m n k q) ∧ IsAdmissibleH (tNeg W T m n k q) := by
  have hψ := tpsi_psiGood hW hW0 (fmTt_mem hT n q).1
  have h1 : ‖(fmRq n (fmPr q) : ℂ) * fmDir k‖ + fmSq n (fmPr q) < (fmCq m n (fmPr q)).im := by
    rw [norm_fmRq_dir]
    have := fmRq_le n (fmPr q); have := fmSq_le n (fmPr q); have := fmCq_im_ge m n (fmPr q)
    linarith
  have hpos : 0 < ‖(fmRq n (fmPr q) : ℂ) * fmDir k‖ := by
    rw [norm_fmRq_dir]; exact fmRq_pos n _
  refine ⟨g1FMAdmStmt_holds _ hψ _ _ _ _ (fmSq_nonneg n _) hpos h1 one_pos,
    g1FMAdmStmt_holds _ hψ _ _ _ _ (fmSq_nonneg n _) ?_ ?_ one_pos⟩
  · rwa [norm_neg]
  · rwa [norm_neg]

theorem tPos_univ (hW : Continuous W) (hW0 : W 0 = 0) (hT : 0 ≤ T) {m n : ℕ} (k : Fin 2)
    (q q' : Fin 5 → ℝ) :
    tPos W T m n k q univ = tNeg W T m n k q' univ ∧ tNeg W T m n k q univ = tPos W T m n k q' univ
      ∧ tPos W T m n k q univ = tNeg W T m n k q univ := by
  have hm : ∀ q : Fin 5 → ℝ, Measurable (tpsi W (fmTt T n q)) := fun q =>
    (tpsi_psiGood hW hW0 (fmTt_mem hT n q).1).1
  simp only [tPos, tNeg, tfm, pfmMeas_univ (hm _), and_self]

theorem t_map_pt (hX : IsFreeGFFModConstH X P) (hW : Continuous W) (hW0 : W 0 = 0) (hT : 0 ≤ T)
    {m n : ℕ} (hnm : 2 * (2 : ℝ)⁻¹ ^ n < 1 / ((m : ℝ) + 1)) (k : Fin 2) (q : Fin 5 → ℝ) :
    P.map (fun ω => X ω (tPos W T m n k q) - X ω (tNeg W T m n k q)) =
      gaussianReal 0 (kernelCov2 neumannH (tPos W T m n k q, tNeg W T m n k q)
        (tPos W T m n k q, tNeg W T m n k q)).toNNReal := by
  obtain ⟨h1, h2⟩ := tPos_adm hW hW0 hT hnm k q
  exact RegCont.map_diff_eq_gaussianReal hX h1 h2 (tPos_univ hW hW0 hT k q q).2.2

theorem t_map_incr (hX : IsFreeGFFModConstH X P) (hW : Continuous W) (hW0 : W 0 = 0)
    (hT : 0 ≤ T) {m n : ℕ} (hnm : 2 * (2 : ℝ)⁻¹ ^ n < 1 / ((m : ℝ) + 1)) (k : Fin 2)
    (q q' : Fin 5 → ℝ) :
    P.map (fun ω => (X ω (tPos W T m n k q) - X ω (tNeg W T m n k q)) -
        (X ω (tPos W T m n k q') - X ω (tNeg W T m n k q'))) =
      gaussianReal 0 (kernelCov2 neumannH
        (tPos W T m n k q + tNeg W T m n k q', tNeg W T m n k q + tPos W T m n k q')
        (tPos W T m n k q + tNeg W T m n k q', tNeg W T m n k q + tPos W T m n k q')).toNNReal := by
  obtain ⟨h1, h2⟩ := tPos_adm hW hW0 hT hnm k q
  obtain ⟨h1', h2'⟩ := tPos_adm hW hW0 hT hnm k q'
  have hl1 := hX.linear _ _ h1 h2' 1 1
  have hl2 := hX.linear _ _ h2 h1' 1 1
  simp only [one_smul, NNReal.coe_one, one_mul] at hl1 hl2
  have hae : (fun ω => (X ω (tPos W T m n k q) - X ω (tNeg W T m n k q)) -
        (X ω (tPos W T m n k q') - X ω (tNeg W T m n k q'))) =ᵐ[P]
      fun ω => X ω (tPos W T m n k q + tNeg W T m n k q') -
        X ω (tNeg W T m n k q + tPos W T m n k q') := by
    filter_upwards [hl1, hl2] with ω e1 e2
    rw [e1, e2]; ring
  rw [Measure.map_congr hae]
  refine RegCont.map_diff_eq_gaussianReal hX (isAdmissibleH_add h1 h2')
    (isAdmissibleH_add h2 h1') ?_
  rw [Measure.add_apply, Measure.add_apply, (tPos_univ hW hW0 hT k q q).2.2,
    (tPos_univ hW hW0 hT k q' q').2.2]

/-- Energy bounds at the clamped parameters: `≤ c` for a pair, `≤ 10 c ‖q − q'‖^{1/3}` for an
increment. -/
theorem t_energy (hW : Continuous W) (hW0 : W 0 = 0) (hT : 0 ≤ T) (hE : TEnergy W T) (m : ℕ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∀ n : ℕ, (2 : ℝ)⁻¹ ^ n ≤ τ₀ →
      2 * (2 : ℝ)⁻¹ ^ n < 1 / ((m : ℝ) + 1) → ∀ (k : Fin 2) (q q' : Fin 5 → ℝ),
      kernelCov2 neumannH (tPos W T m n k q, tNeg W T m n k q)
        (tPos W T m n k q, tNeg W T m n k q) ≤ c ∧
      kernelCov2 neumannH
        (tPos W T m n k q + tNeg W T m n k q', tNeg W T m n k q + tPos W T m n k q')
        (tPos W T m n k q + tNeg W T m n k q', tNeg W T m n k q + tPos W T m n k q') ≤
        10 * c * ‖q - q'‖ ^ ((1 : ℝ) / 3) := by
  obtain ⟨c, hc, τ₀, hτ₀, hEm⟩ := hE m
  refine ⟨c, hc, τ₀, hτ₀, fun n hnτ hnm k => ?_⟩
  have raw : ∀ q q' : Fin 5 → ℝ,
      kernelCov2 neumannH (tPos W T m n k q, tNeg W T m n k q)
        (tPos W T m n k q, tNeg W T m n k q) ≤ c ∧
      kernelCov2 neumannH
        (tPos W T m n k q + tNeg W T m n k q', tNeg W T m n k q + tPos W T m n k q')
        (tPos W T m n k q + tNeg W T m n k q', tNeg W T m n k q + tPos W T m n k q') ≤
        c * (‖fmCq m n (fmPr q) - fmCq m n (fmPr q')‖ + |fmRq n (fmPr q) - fmRq n (fmPr q')| +
          |fmSq n (fmPr q) - fmSq n (fmPr q')| + |fmTt T n q - fmTt T n q'| ^ ((1 : ℝ) / 3)) /
          fmRq n (fmPr q) := fun q q' =>
    hEm (fmDir k) (norm_fmDir k) (fmCq m n (fmPr q)) (fmCq m n (fmPr q'))
      (norm_fmCq_le m n _) (norm_fmCq_le m n _) (fmCq_im_ge m n _) (fmCq_im_ge m n _)
      (fmRq n (fmPr q)) (fmRq n (fmPr q')) (fmRq_pos n _) ((fmRq_le n _).trans hnτ)
      (by linarith [fmRq_le n (fmPr q), fmRq_ge n (fmPr q')])
      (by linarith [fmRq_le n (fmPr q'), fmRq_ge n (fmPr q)]) (fmSq n (fmPr q))
      (fmSq n (fmPr q')) (fmSq_nonneg n _) (fmSq_le n _) (fmSq_nonneg n _) (fmSq_le n _)
      _ (fmTt_mem hT n q) _ (fmTt_mem hT n q')
  intro q q'
  refine ⟨(raw q q').1, ?_⟩
  set x := ‖q - q'‖ with hx
  set y := x ^ ((1 : ℝ) / 3) with hy
  have hx0 : 0 ≤ x := norm_nonneg _
  have hy0 : 0 ≤ y := Real.rpow_nonneg hx0 _
  rcases le_or_gt x 1 with hsm | hlg
  · have hτ := fmRq_pos n (fmPr q)
    refine (raw q q').2.trans ?_
    rw [div_le_iff₀ hτ]
    have hl := fmParams_lip m n (fmPr q) (fmPr q')
    have hpr := norm_fmPr_sub_le q q'
    have ha := two_pow_inv_pos n
    have hTt : |fmTt T n q - fmTt T n q'| ^ ((1 : ℝ) / 3) ≤ (2 : ℝ)⁻¹ ^ n * y := by
      rw [hy, ← rpow_third_scale n hx0]
      exact Real.rpow_le_rpow (abs_nonneg _) (abs_fmTt_sub_le T n q q') (by norm_num)
    have hxy : x ≤ y := Real.self_le_rpow_of_le_one hx0 hsm (by norm_num)
    have hg := fmRq_ge n (fmPr q)
    have e1 : 4 * (2 : ℝ)⁻¹ ^ n * ‖fmPr q - fmPr q'‖ ≤ 4 * (2 : ℝ)⁻¹ ^ n * y :=
      mul_le_mul_of_nonneg_left (hpr.trans hxy) (by positivity)
    have hay : (2 : ℝ)⁻¹ ^ n * y ≤ 2 * fmRq n (fmPr q) * y :=
      mul_le_mul_of_nonneg_right (by linarith) hy0
    have key : ‖fmCq m n (fmPr q) - fmCq m n (fmPr q')‖ + |fmRq n (fmPr q) - fmRq n (fmPr q')| +
        |fmSq n (fmPr q) - fmSq n (fmPr q')| + |fmTt T n q - fmTt T n q'| ^ ((1 : ℝ) / 3) ≤
        10 * fmRq n (fmPr q) * y := by nlinarith
    have := mul_le_mul_of_nonneg_left key hc
    linarith
  · obtain ⟨h1, h2⟩ := tPos_adm hW hW0 hT hnm k q
    obtain ⟨h1', h2'⟩ := tPos_adm hW hW0 hT hnm k q'
    have kk := G1FM2.kernelCov2_sub_le h1 h2 h1' h2' (tPos_univ hW hW0 hT k q q).2.2
      (tPos_univ hW hW0 hT k q' q').2.2
    have hy1 : 1 ≤ y := Real.one_le_rpow hlg.le (by norm_num)
    have p1 := (raw q q').1
    have p2 := (raw q' q).1
    have : 10 * c * 1 ≤ 10 * c * y := mul_le_mul_of_nonneg_left hy1 (by positivity)
    linarith

end Laws

end CfgFM
end QuantumZipper.E6
