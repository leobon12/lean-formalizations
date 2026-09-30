import QuantumZipper.Proofs.Zipper.Cor15Markov2Recon
import QuantumZipper.Proofs.GFF.Existence.AdmissibleAux
import QuantumZipper.Proofs.NonVacuityFinal

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# COR15-MARKOV (3): the circle-average smoothing converges in energy (`BindFcEnergyTendstoStmt`)

For an admissible measure `ν` (finite, compact support in `ℍ̄`, bounded logarithmic potential)
and `ν_k = ∫ foldedCircle(w, 2^{-k}) dν(w)`, the Neumann energy of `ν_k − ν` tends to `0`.
This is the circle-average approximation behind Duplantier–Sheffield, *Liouville quantum gravity
and KPZ*, Invent. Math. 185 (2011), §3.1 (Prop. 3.1), for the Neumann kernel of `ℍ`.

Proof (following the Frostman case of the repository, `FrostmanReg.abs_energy_frostman_le`, with
the Frostman rate replaced by dominated convergence):
* Newton's formula for circle averages (`SmoothConv.integral_bind_neumannH`) gives
  `K(p, ν_r) = K(p, ν) − Λ_r(p)`, `Λ_r(p) = ∫∫ L_r(w,x) dν(w) dp(x)`, where the smoothing defect
  satisfies `0 ≤ L_r(w,x) ≤ 2 log⁻ ‖w − x‖` for `r ≤ 1` and vanishes once `r ≤ ‖w − x‖`
  (`FrostmanReg.Lr_bounds_frostman`); the bounded potential makes `2 log⁻ ‖· − x‖` integrable
  with integral `≤ 2C` uniformly in `x`.
* Hence the energy is `Λ_r(ν) − Λ_r(ν_r) ≤ Λ_r(ν)`, and it is `≥ 0` since it is the variance of
  `X ν_r − X ν` for a free field `X` (which exists: `NonVacuity.exists_BM_indep_freeGFF_uncond`).
* `Λ_r(ν) → 0` by dominated convergence twice (`ν` has no atoms: `gffEx_measure_singleton`).

Own adaptation of the repository's Frostman argument (no rate is needed here).
-/

noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology ComplexConjugate

namespace QuantumZipper
namespace Cor15Group

open SmoothConv Regularization CircleFubini FrostmanReg

theorem cor15m2_radius_le_one (k : ℕ) : radius k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)

theorem cor15m2_tendsto_radius : Tendsto radius atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

/-- **The Neumann energy is nonnegative** at admissible pairs of equal mass: it is the variance
of `X a − X b` for a free field `X`, which exists. -/
theorem kernelCov2_self_nonneg_adm {a b : Measure ℂ} (ha : IsAdmissibleH a)
    (hb : IsAdmissibleH b) (hm : a Set.univ = b Set.univ) :
    0 ≤ kernelCov2 neumannH (a, b) (a, b) := by
  obtain ⟨Ω, _, P, -, X, hP, -, hX, -⟩ := NonVacuity.exists_BM_indep_freeGFF_uncond
  have c1 := hX.covariance_eq (a, b) (a, b) ha hb hm ha hb hm
  dsimp only at c1
  have hv := covariance_self (μ := P) (X := fun ω => X ω a - X ω b)
    ((hX.measurable_coord a).sub (hX.measurable_coord b)).aemeasurable
  rw [← c1, hv]
  exact variance_nonneg _ _

/-! ## Pointwise bounds on the smoothing defect -/

theorem Lr_le_logNeg_adm {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) {w x : ℂ} (hw : w ∈ Hbar)
    (hx : x ∈ Hbar) (hwx : w ≠ x) :
    0 ≤ Lr r w x ∧ Lr r w x ≤ 2 * (ENNReal.ofReal (-Real.log ‖w - x‖)).toReal := by
  obtain ⟨h0, h1⟩ := Lr_bounds_frostman hr hw hx hwx
  refine ⟨h0, h1.trans ?_⟩
  have ha : 0 < ‖w - x‖ := norm_pos_iff.2 (sub_ne_zero.2 hwx)
  rw [ENNReal.toReal_ofReal']
  refine mul_le_mul_of_nonneg_left (max_le (le_max_right _ _) (le_trans ?_ (le_max_left _ _)))
    (by norm_num)
  rw [Real.log_div ha.ne' hr.ne']
  linarith [Real.log_nonpos hr.le hr1]

theorem Lr_eq_zero_of_le_adm {r : ℝ} (hr : 0 < r) {w x : ℂ} (hw : w ∈ Hbar) (hx : x ∈ Hbar)
    (hwx : w ≠ x) (hrw : r ≤ ‖w - x‖) : Lr r w x = 0 := by
  obtain ⟨h0, h1⟩ := Lr_bounds_frostman hr hw hx hwx
  have hlog : 0 ≤ Real.log (‖w - x‖ / r) := Real.log_nonneg ((one_le_div hr).2 hrw)
  rw [max_eq_left (by linarith)] at h1
  linarith

/-! ## Almost-sure facts for admissible measures -/

theorem ae_ne_adm {ν : Measure ℂ} (hν : IsAdmissibleH ν) (x : ℂ) : ∀ᵐ w ∂ν, w ≠ x := by
  rw [ae_iff]
  have e : {a : ℂ | ¬a ≠ x} = {x} := by
    ext a; simp only [ne_eq, not_not, Set.mem_singleton_iff]; rfl
  rw [e]
  exact GFFExist.gffEx_measure_singleton hν x

theorem ae_mem_Hbar_adm {ν : Measure ℂ} (hν : IsAdmissibleH ν) : ∀ᵐ w ∂ν, w ∈ Hbar := by
  obtain ⟨K, -, hKH, hK⟩ := hν.2.1
  exact (ae_mem_of_compl_null_frostman hK).mono fun x hx => hKH hx

theorem measurable_logNeg_adm (x : ℂ) :
    Measurable fun w : ℂ => ENNReal.ofReal (-Real.log ‖w - x‖) :=
  (Real.measurable_log.comp (measurable_id.sub_const x).norm).neg.ennreal_ofReal

theorem integrable_logNeg_adm {ν : Measure ℂ} (hν : IsAdmissibleH ν) (x : ℂ) :
    Integrable (fun w => (ENNReal.ofReal (-Real.log ‖w - x‖)).toReal) ν := by
  obtain ⟨C, hC, hbd⟩ := hν.2.2
  exact integrable_toReal_of_lintegral_ne_top (measurable_logNeg_adm x).aemeasurable
    (ne_top_of_le_ne_top hC.ne (hbd x))

theorem integral_logNeg_le_adm {ν : Measure ℂ} {C : ℝ≥0∞} (hC : C < ⊤)
    (hbd : ∀ y : ℂ, ∫⁻ x, ENNReal.ofReal (-Real.log ‖x - y‖) ∂ν ≤ C) (x : ℂ) :
    ∫ w, (ENNReal.ofReal (-Real.log ‖w - x‖)).toReal ∂ν ≤ C.toReal := by
  rw [integral_toReal (measurable_logNeg_adm x).aemeasurable
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  exact ENNReal.toReal_mono hC.ne (hbd x)

/-- The `ν`-average of the smoothing defect at `x ∈ ℍ̄`: integrable, in `[0, 2C]`. -/
theorem integral_Lr_adm {ν : Measure ℂ} (hν : IsAdmissibleH ν) {C : ℝ≥0∞} (hC : C < ⊤)
    (hbd : ∀ y : ℂ, ∫⁻ x, ENNReal.ofReal (-Real.log ‖x - y‖) ∂ν ≤ C) {r : ℝ} (hr : 0 < r)
    (hr1 : r ≤ 1) {x : ℂ} (hx : x ∈ Hbar) :
    Integrable (fun w => Lr r w x) ν ∧ 0 ≤ ∫ w, Lr r w x ∂ν ∧
      ∫ w, Lr r w x ∂ν ≤ 2 * C.toReal := by
  have hb : ∀ᵐ w ∂ν, 0 ≤ Lr r w x ∧
      Lr r w x ≤ 2 * (ENNReal.ofReal (-Real.log ‖w - x‖)).toReal := by
    filter_upwards [ae_mem_Hbar_adm hν, ae_ne_adm hν x] with w hw hwx
    exact Lr_le_logNeg_adm hr hr1 hw hx hwx
  have hi : Integrable (fun w => Lr r w x) ν :=
    Integrable.mono' ((integrable_logNeg_adm hν x).const_mul 2)
      (measurable_Lr_left_frostman hr x).aestronglyMeasurable
      (hb.mono fun w hw => by rw [Real.norm_eq_abs, abs_of_nonneg hw.1]; exact hw.2)
  refine ⟨hi, integral_nonneg_of_ae (hb.mono fun w hw => hw.1), ?_⟩
  calc ∫ w, Lr r w x ∂ν ≤ ∫ w, 2 * (ENNReal.ofReal (-Real.log ‖w - x‖)).toReal ∂ν :=
        integral_mono_ae hi ((integrable_logNeg_adm hν x).const_mul 2) (hb.mono fun w hw => hw.2)
    _ = 2 * ∫ w, (ENNReal.ofReal (-Real.log ‖w - x‖)).toReal ∂ν := integral_const_mul _ _
    _ ≤ 2 * C.toReal :=
        mul_le_mul_of_nonneg_left (integral_logNeg_le_adm hC hbd x) (by norm_num)

/-! ## Smoothing the second argument of the Neumann kernel -/

theorem aesm_integral_Lr {p ν : Measure ℂ} [SFinite p] [SFinite ν] {r : ℝ} (hr : 0 < r) :
    AEStronglyMeasurable (fun x => ∫ w, Lr r w x ∂ν) p :=
  (((measurable_Lr hr).comp measurable_swap).aestronglyMeasurable
    (μ := p.prod ν)).integral_prod_right'

/-- `K(p, ν_r) = K(p, ν) − Λ_r(p)` for admissible `p`, `ν` and `0 < r ≤ 1`. -/
theorem kernelCov_bind_adm {p ν : Measure ℂ} (hp : IsAdmissibleH p) (hν : IsAdmissibleH ν)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    kernelCov neumannH p (ν.bind fun w => foldedCircle w r) =
      kernelCov neumannH p ν - ∫ x, ∫ w, Lr r w x ∂ν ∂p := by
  have hkA := K3.isAdmissibleH_bind hν hr
  haveI := hν.1
  haveI := hp.1
  haveI := isFiniteMeasure_bind_circle (r := r) ν
  obtain ⟨C, hC, hbd⟩ := hν.2.2
  have hpH := ae_mem_Hbar_adm hp
  have i1 := (integrable_neumannH_prod hp hkA).prod_right_ae
  have i2 := (integrable_neumannH_prod hp hν).prod_right_ae
  unfold kernelCov
  have h1 : ∀ᵐ x ∂p, ∫ y, neumannH x y ∂(ν.bind fun w => foldedCircle w r) =
      ∫ w, neumannH x w ∂ν - ∫ w, Lr r w x ∂ν := by
    filter_upwards [hpH, i1, i2] with x hx hi1 hi2
    rw [integral_bind_neumannH hr x hi1,
      ← integral_sub hi2 (integral_Lr_adm hν hC hbd hr hr1 hx).1]
    refine integral_congr_ae (ae_of_all _ fun w => ?_)
    simp only [Lr, neumannH_symm w x]; ring
  rw [integral_congr_ae h1]
  have hF : Integrable (fun x => ∫ w, neumannH x w ∂ν) p :=
    (integrable_neumannH_prod hp hν).integral_prod_left
  have hG : Integrable (fun x => ∫ w, Lr r w x ∂ν) p :=
    Integrable.of_bound (aesm_integral_Lr hr) (2 * C.toReal) (hpH.mono fun x hx => by
      obtain ⟨-, h0, h1⟩ := integral_Lr_adm hν hC hbd hr hr1 hx
      rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact h1)
  exact integral_sub hF hG

theorem Lam_nonneg_adm {p ν : Measure ℂ} (hp : IsAdmissibleH p) (hν : IsAdmissibleH ν)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) : 0 ≤ ∫ x, ∫ w, Lr r w x ∂ν ∂p := by
  obtain ⟨C, hC, hbd⟩ := hν.2.2
  exact integral_nonneg_of_ae ((ae_mem_Hbar_adm hp).mono fun x hx =>
    (integral_Lr_adm hν hC hbd hr hr1 hx).2.1)

/-- `Λ_{r_k}(ν) → 0` (dominated convergence twice). -/
theorem tendsto_Lam_adm {ν : Measure ℂ} (hν : IsAdmissibleH ν) :
    Tendsto (fun k => ∫ x, ∫ w, Lr (radius k) w x ∂ν ∂ν) atTop (𝓝 0) := by
  haveI := hν.1
  obtain ⟨C, hC, hbd⟩ := hν.2.2
  have hH := ae_mem_Hbar_adm hν
  have hpt : ∀ x ∈ Hbar, Tendsto (fun k => ∫ w, Lr (radius k) w x ∂ν) atTop (𝓝 0) := by
    intro x hx
    rw [show (0 : ℝ) = ∫ _w, (0 : ℝ) ∂ν by simp]
    refine tendsto_integral_of_dominated_convergence
      (fun w => 2 * (ENNReal.ofReal (-Real.log ‖w - x‖)).toReal)
      (fun k => (measurable_Lr_left_frostman (radius_pos k) x).aestronglyMeasurable)
      ((integrable_logNeg_adm hν x).const_mul 2) (fun k => ?_) ?_
    · filter_upwards [hH, ae_ne_adm hν x] with w hw hwx
      obtain ⟨h0, h1⟩ := Lr_le_logNeg_adm (radius_pos k) (cor15m2_radius_le_one k) hw hx hwx
      rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact h1
    · filter_upwards [hH, ae_ne_adm hν x] with w hw hwx
      have hpos : 0 < ‖w - x‖ := norm_pos_iff.2 (sub_ne_zero.2 hwx)
      have hev : ∀ᶠ k in atTop, radius k ≤ ‖w - x‖ :=
        cor15m2_tendsto_radius.eventually (ge_mem_nhds hpos)
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev] with k hk
      exact (Lr_eq_zero_of_le_adm (radius_pos k) hw hx hwx hk).symm
  rw [show (0 : ℝ) = ∫ _x, (0 : ℝ) ∂ν by simp]
  refine tendsto_integral_of_dominated_convergence (fun _ => 2 * C.toReal)
    (fun k => aesm_integral_Lr (radius_pos k)) (integrable_const _) (fun k => ?_) ?_
  · filter_upwards [hH] with x hx
    obtain ⟨-, h0, h1⟩ := integral_Lr_adm hν hC hbd (radius_pos k) (cor15m2_radius_le_one k) hx
    rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact h1
  · filter_upwards [hH] with x hx using hpt x hx

/-! ## The energy statement -/

/-- **`BindFcEnergyTendstoStmt` holds.** -/
theorem bindFcEnergyTendstoStmt_holds : BindFcEnergyTendstoStmt := by
  intro ν hν
  have hkA : ∀ k, IsAdmissibleH (fcSmooth ν k) := fun k =>
    K3.isAdmissibleH_bind hν (radius_pos k)
  have mk : ∀ k, (fcSmooth ν k) Set.univ = ν Set.univ := fun k => bind_fc_univ ν _
  have e : ∀ k, fcSmoothEnergy ν k = (∫ x, ∫ w, Lr (radius k) w x ∂ν ∂ν) -
      ∫ x, ∫ w, Lr (radius k) w x ∂ν ∂(fcSmooth ν k) := by
    intro k
    unfold fcSmoothEnergy kernelCov2
    simp only [fcSmooth]
    rw [kernelCov_bind_adm (hkA k) hν (radius_pos k) (cor15m2_radius_le_one k),
      kernelCov_bind_adm hν hν (radius_pos k) (cor15m2_radius_le_one k)]
    ring
  have hlow : ∀ k, 0 ≤ fcSmoothEnergy ν k := fun k =>
    kernelCov2_self_nonneg_adm (hkA k) hν (mk k)
  have hup : ∀ k, fcSmoothEnergy ν k ≤ ∫ x, ∫ w, Lr (radius k) w x ∂ν ∂ν := fun k => by
    rw [e k]
    linarith [Lam_nonneg_adm (hkA k) hν (radius_pos k) (cor15m2_radius_le_one k)]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (tendsto_Lam_adm hν)
    hlow hup

/-- **The reconstruction input holds** (body of `FreeCircleReconStmt`). -/
theorem freeCircleRecon_holds :
    ∃ R : (ℕ → ℝ) → FieldSample, (∀ μ : Measure ℂ, Measurable fun c => R c μ) ∧
      (∀ (x : FieldSample) (i : ℕ), R (CoordsFull.coordsFull x)
        (foldedCircle (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2) =
          x (foldedCircle (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2)) ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X : Ω → FieldSample), IsFreeGFFModConstH X P → ∀ μ : Measure ℂ, IsAdmissibleH μ →
        (fun ω => R (CoordsFull.coordsFull (X ω)) μ) =ᵐ[P] fun ω => X ω μ :=
  freeCircleRecon_of_energy bindFcEnergyTendstoStmt_holds

end Cor15Group
end QuantumZipper
