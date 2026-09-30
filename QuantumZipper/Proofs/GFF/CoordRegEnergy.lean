import QuantumZipper.Proofs.GFF.CoordRegEnergyBasic
import QuantumZipper.Proofs.GFF.CoordRegRandom

/-!
# RC3 for general measures: smoothing consistency of the pulled-back field

For a probability measure `ν` on `ℍ` with bounded support, Frostman, with `|log Im|` integrable and
a strip bound (`StripBound`), and with `f_* ν` Frostman, almost surely

`evalReg (coordChange x f Q) ν = evalReg x (f_* ν) + Q ∫ log ‖f'‖ dν`

(`ae_evalReg_coordChange_revMap_gen`). The energy estimates of `CoordRegEnergyBasic` give
`X (f_* ν_{r_k}) → X (f_* ν)` (`ae_tendsto_push_bind`); the deterministic part converges by
dominated convergence (`tendsto_integral_bind_fc`); the two are combined through the regular
witness `exists_regular_witness_revMap`. Own argument (no published treatment of circle-average
regularization of a pulled-back GFF found).
-/

set_option maxErrors 400

noncomputable section

open MeasureTheory Filter Metric Set
open scoped ENNReal Real ComplexConjugate Topology

namespace QuantumZipper
namespace CoordReg

open CircleFubini FrostmanReg SmoothConv

variable {W : ℝ → ℝ} {T : ℝ}

/-! ## RC3 for general measures -/

section RC3Gen

open RegSample ProbabilityTheory

theorem integrable_of_abs_le_logIm {ν : Measure ℂ} [IsFiniteMeasure ν] {G : ℂ → ℝ}
    (hGm : AEStronglyMeasurable G ν) {A B : ℝ} (hb : ∀ᵐ z ∂ν, |G z| ≤ A + B * |Real.log z.im|)
    (hlν : Integrable (fun z : ℂ => |Real.log z.im|) ν) : Integrable G ν :=
  ((integrable_const A).add (hlν.const_mul B)).mono' hGm (hb.mono fun z hz => by
    rw [Real.norm_eq_abs]; exact hz)

/-- Folded-circle averages of a function continuous on `ℍ` converge to the value at the centre. -/
theorem tendsto_integral_fc_of_continuousOn {G : ℂ → ℝ} (hGm : Measurable G)
    (hGc : ContinuousOn G H) {w : ℂ} (hw : w ∈ H)
    (hGi : ∀ r : ℝ, 0 < r → r ≤ 1 → Integrable G (foldedCircle w r)) :
    Tendsto (fun r => ∫ u, G u ∂foldedCircle w r) (𝓝[>] 0) (𝓝 (G w)) := by
  have hGw : ContinuousAt G w := hGc.continuousAt (isOpen_H.mem_nhds hw)
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hδG⟩ := Metric.continuousAt_iff.1 hGw (ε / 2) (by linarith)
  refine ⟨min δ (min w.im 1), lt_min hδ (lt_min hw one_pos), fun r hr hrd => ?_⟩
  have hr0 : 0 < r := hr
  rw [Real.dist_eq, sub_zero, abs_of_pos hr0] at hrd
  obtain ⟨hrδ, hrw, hr1⟩ : r < δ ∧ r < w.im ∧ r < 1 := by
    simp only [lt_min_iff] at hrd; exact hrd
  have hfc : foldedCircle w r = circleUnif w r :=
    foldedCircle_eq_circleUnif_sc hr0.le hrw.le
  have hpt : ∀ᵐ u ∂foldedCircle w r, ‖G u - G w‖ ≤ ε / 2 := by
    rw [hfc]
    filter_upwards [ae_circleUnif_sc w r] with u hu
    rw [← dist_eq_norm]
    exact (hδG (by rw [dist_eq_norm, hu, abs_of_pos hr0]; exact hrδ)).le
  have e : ∫ u, G u ∂foldedCircle w r - G w = ∫ u, (G u - G w) ∂foldedCircle w r := by
    rw [integral_sub (hGi r hr0 hr1.le) (integrable_const _), integral_const, probReal_univ, one_smul]
  have h := norm_integral_le_of_norm_le (integrable_const (ε / 2)) hpt
  rw [integral_const, probReal_univ, one_smul] at h
  rw [Real.dist_eq, ← Real.norm_eq_abs, e]
  linarith

/-- Integrability of `w ↦ ∫ G dfc(w, r)` for a function with a logarithmic bound near the real
line. -/
theorem integrable_integral_fc_of_bound {G : ℂ → ℝ} (hGm : Measurable G) {R A B : ℝ}
    (hGb : ∀ u ∈ H, ‖u‖ ≤ R + 1 → |G u| ≤ A + B * |Real.log u.im|)
    {ν : Measure ℂ} [IsFiniteMeasure ν] (hν : ∀ᵐ z ∂ν, z ∈ H ∧ ‖z‖ ≤ R)
    (hlν : Integrable (fun z : ℂ => |Real.log z.im|) ν) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    Integrable (fun w => ∫ u, G u ∂foldedCircle w r) ν := by
  obtain ⟨C₀, hC₀, hLA⟩ := integral_abs_log_im_fc_le (R + 1)
  have hLA' : ∀ z ∈ H, ‖z‖ ≤ R → ∀ r : ℝ, 0 < r → r ≤ 1 →
      ∫ u, |Real.log u.im| ∂foldedCircle z r ≤ C₀ + |Real.log z.im| :=
    fun z hz hzR => hLA z hz (by linarith)
  have := isFiniteMeasure_bind_circle (r := r) ν
  have hi : Integrable G (ν.bind fun w => foldedCircle w r) := by
    refine integrable_of_abs_le_logIm (A := A) (B := B) hGm.aestronglyMeasurable ?_
      (integrable_abs_log_im_bind hC₀ hLA' hν hlν hr hr1).1
    filter_upwards [bind_fc_mem_H_norm ν hr (hν.mono fun z hz => hz.2)] with u hu
    exact hGb u hu.1 (by linarith [hu.2])
  exact (integral_bind_circle ν hi).1

/-- Dominated convergence for the circle-smoothed integrals of a function with a logarithmic
bound near the real line. -/
theorem tendsto_integral_bind_fc {G : ℂ → ℝ} (hGm : Measurable G) (hGc : ContinuousOn G H)
    {R A B : ℝ} (hB : 0 ≤ B)
    (hGb : ∀ u ∈ H, ‖u‖ ≤ R + 1 → |G u| ≤ A + B * |Real.log u.im|)
    {ν : Measure ℂ} [IsFiniteMeasure ν] (hν : ∀ᵐ z ∂ν, z ∈ H ∧ ‖z‖ ≤ R)
    (hlν : Integrable (fun z : ℂ => |Real.log z.im|) ν) :
    Tendsto (fun k => ∫ w, (∫ u, G u ∂foldedCircle w (radius k)) ∂ν) atTop
      (𝓝 (∫ w, G w ∂ν)) := by
  obtain ⟨C₀, hC₀, hLA⟩ := integral_abs_log_im_fc_le (R + 1)
  have hrad1 : ∀ k, radius k ≤ 1 := fun k => by
    unfold radius; exact pow_le_one₀ (by norm_num) (by norm_num)
  have hfcb : ∀ w ∈ H, ‖w‖ ≤ R → ∀ r : ℝ, 0 < r → r ≤ 1 →
      ∀ᵐ u ∂foldedCircle w r, u ∈ H ∧ ‖u‖ ≤ R + 1 := fun w _ hwR r hr hr1 => by
    filter_upwards [TwoPoint.foldedCircle_ae_mem_H w hr,
      TwoPoint.foldedCircle_ae_norm_le w hr.le] with u h1 h2
    exact ⟨h1, by linarith⟩
  have hGi : ∀ w ∈ H, ‖w‖ ≤ R → ∀ r : ℝ, 0 < r → r ≤ 1 → Integrable G (foldedCircle w r) :=
    fun w hw hwR r hr hr1 => integrable_of_abs_le_logIm hGm.aestronglyMeasurable
      ((hfcb w hw hwR r hr hr1).mono fun u hu => hGb u hu.1 hu.2)
      (TwoPoint.integrable_log_im_foldedCircle w hr).abs
  have hLA' : ∀ z ∈ H, ‖z‖ ≤ R → ∀ r : ℝ, 0 < r → r ≤ 1 →
      ∫ u, |Real.log u.im| ∂foldedCircle z r ≤ C₀ + |Real.log z.im| :=
    fun z hz hzR => hLA z hz (by linarith)
  refine tendsto_integral_of_dominated_convergence (fun w => (|A| + B * C₀) + B * |Real.log w.im|)
    (fun k => (integrable_integral_fc_of_bound hGm hGb hν hlν (radius_pos k)
      (hrad1 k)).aestronglyMeasurable) ((integrable_const _).add (hlν.const_mul B))
    (fun k => ?_) ?_
  · filter_upwards [hν] with w hw
    rw [Real.norm_eq_abs]
    have hr := radius_pos k
    have hib : Integrable (fun u : ℂ => A + B * |Real.log u.im|) (foldedCircle w (radius k)) :=
      (integrable_const A).add ((TwoPoint.integrable_log_im_foldedCircle w hr).abs.const_mul B)
    have h := norm_integral_le_of_norm_le hib
      ((hfcb w hw.1 hw.2 _ hr (hrad1 k)).mono fun u hu => by
        rw [Real.norm_eq_abs]; exact hGb u hu.1 hu.2)
    rw [Real.norm_eq_abs, integral_add (integrable_const _)
      ((TwoPoint.integrable_log_im_foldedCircle w hr).abs.const_mul B), integral_const_mul,
      integral_const, probReal_univ, one_smul] at h
    have := mul_le_mul_of_nonneg_left (hLA' w hw.1 hw.2 _ hr (hrad1 k)) hB
    have hA := le_abs_self A
    nlinarith
  · filter_upwards [hν] with w hw
    exact (tendsto_integral_fc_of_continuousOn hGm hGc hw.1
      (hGi w hw.1 hw.2)).comp RegClosure.tendsto_radius_nhdsGT

variable (hW : Continuous W) (hT : 0 ≤ T)
include hW hT

theorem isAdmissibleH_bind_pK {ν : Measure ℂ} [IsFiniteMeasure ν] {R₁ : ℝ}
    (hsupp : ν (ballH R₁)ᶜ = 0) {ρ : ℝ} (hρ : 0 < ρ) :
    IsAdmissibleH (ν.bind (pK hW hT ρ)) := by
  have := isFiniteMeasure_bind_kernel ν (pK hW hT ρ)
  obtain ⟨Bf, hBf⟩ := norm_revMap_le' hW hT (R₁ + ρ)
  have hK' : ∀ z ∈ ballH R₁, ‖z‖ + ρ ≤ R₁ + ρ := fun z hz => by
    have := hz.1; rw [mem_closedBall, dist_zero_right] at this; linarith
  exact admissible_of_bounds
    (bind_kernel_support ν _ hsupp fun z hz => pushK_support hW hT hBf hρ (hK' z hz))
    (ENNReal.mul_ne_top (measure_ne_top _ _) ENNReal.ofReal_ne_top)
    (bind_kernel_pot ν _ hsupp fun z hz y => pushK_pot hW hT hρ le_rfl (hK' z hz) y)

theorem bind_pK_eq (ν : Measure ℂ) (ρ : ℝ) :
    ν.bind (pK hW hT ρ) = (ν.bind fun z => foldedCircle z ρ).map (revMap W T) :=
  bind_pushKernel _ _ _ _

omit hW hT in
theorem integrable_of_continuous_ballH {g : ℂ → ℝ} (hg : Continuous g) {ν : Measure ℂ}
    [IsFiniteMeasure ν] {R₁ : ℝ} (hsupp : ν (ballH R₁)ᶜ = 0) : Integrable g ν := by
  obtain ⟨M, hM⟩ := (isCompact_ballH R₁).exists_bound_of_continuousOn hg.continuousOn
  exact Integrable.of_bound hg.aestronglyMeasurable M
    ((ae_mem_of_compl_null_frostman hsupp).mono fun u hu => hM u hu)

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-- Stochastic Fubini for the pushed circles against a probability measure `ν`. -/
theorem ae_integral_Vhat_eq_gen (hX : IsFreeGFFModConstH X P) [IsProbabilityMeasure P]
    {Vh : (Fin 4 → ℝ) → Ω → ℝ} (hVc : ∀ ω, Continuous fun q => Vh q ω)
    (hVV : ∀ q, (fun ω => Vh q ω) =ᵐ[P] fun ω => X ω (pK hW hT (rad q) (cen q)))
    {ν : Measure ℂ} [IsProbabilityMeasure ν] {R₁ : ℝ} (hR₁ : 0 ≤ R₁)
    (hsupp : ν (ballH R₁)ᶜ = 0) {ρ : ℝ} (hρ : 0 < ρ) :
    ∀ᵐ ω ∂P, ∫ u, Vh (pr u ρ 0) ω ∂ν = X ω (ν.bind (pK hW hT ρ)) := by
  obtain ⟨Bf, hBf⟩ := norm_revMap_le' hW hT (R₁ + ρ)
  have hK' : ∀ z ∈ ballH R₁, ‖z‖ + ρ ≤ R₁ + ρ := fun z hz => by
    have := hz.1; rw [mem_closedBall, dist_zero_right] at this; linarith
  have h0H : (0 : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (0 : ℂ).im by simp
  have h0 : (0 : ℂ) ∈ ballH R₁ := ⟨by simpa using hR₁, h0H⟩
  have hpr : ∀ u ∈ Hbar, pK hW hT (rad (pr u ρ 0)) (cen (pr u ρ 0)) = pK hW hT ρ u :=
    fun u hu => by rw [cen_pr hu, rad_pr u hρ]
  have hYc : ∀ ω, ContinuousOn (fun u => Vh (pr u ρ 0) ω - Vh (pr 0 ρ 0) ω) Hbar := fun ω =>
    (((hVc ω).comp (continuous_pr_fst ρ 0)).sub continuous_const).continuousOn
  have hY : ∀ u ∈ Hbar, (fun ω => Vh (pr u ρ 0) ω - Vh (pr 0 ρ 0) ω) =ᵐ[P]
      fun ω => X ω (pK hW hT ρ u) - X ω (pK hW hT ρ 0) := by
    intro u hu
    filter_upwards [hVV (pr u ρ 0), hVV (pr 0 ρ 0)] with ω h1 h2
    beta_reduce at h1 h2 ⊢
    rw [h1, h2, hpr u hu, hpr 0 h0H]
  have hF := integral_kernelAvg_ae_eq_bind hX (pK hW hT ρ) (K' := ballH R₁) (R := Bf)
    ENNReal.ofReal_ne_top (fun z hz => pushK_support hW hT hBf hρ (hK' z hz))
    (fun z hz y => pushK_pot hW hT hρ le_rfl (hK' z hz) y) h0 hYc hY ν
    (isCompact_ballH R₁) inter_subset_right subset_rfl hsupp
  filter_upwards [hF, hVV (pr 0 ρ 0)] with ω h1 h2
  have hint : Integrable (fun u => Vh (pr u ρ 0) ω) ν :=
    integrable_of_continuous_ballH ((hVc ω).comp (continuous_pr_fst ρ 0)) hsupp
  rw [integral_sub hint (integrable_const _), integral_const, probReal_univ, one_smul,
    measure_univ, one_smul] at h1
  beta_reduce at h2
  rw [hpr 0 h0H] at h2
  linarith

/-- Almost sure convergence `X(f_* ν_{r_k}) → X(f_* ν)`, from the energy estimate. -/
theorem ae_tendsto_push_bind (hX : IsFreeGFFModConstH X P) [IsProbabilityMeasure P]
    {ν : Measure ℂ} [IsFiniteMeasure ν] {R α C c γ α' C' Rf : ℝ}
    (hsupp : ν (closedBall 0 R ∩ Hbar)ᶜ = 0) (hνH : ∀ᵐ z ∂ν, z ∈ H) (hF : IsFrostman ν α C)
    (hα : 0 < α) (hlν : Integrable (fun z : ℂ => |Real.log z.im|) ν) (hS : StripBound ν c γ)
    (hγ : 0 < γ) (hsuppf : (ν.map (revMap W T)) (closedBall 0 Rf ∩ Hbar)ᶜ = 0)
    (hFf : IsFrostman (ν.map (revMap W T)) α' C') (hα' : 0 < α') :
    ∀ᵐ ω ∂P, Tendsto (fun k => X ω (ν.bind (pK hW hT (radius k)))) atTop
      (𝓝 (X ω (ν.map (revMap W T)))) := by
  have hf := TwoPoint.measurable_revMap hW hT
  obtain ⟨M, hM0, hM⟩ := abs_energy_push_le hW hT hsupp hνH hF hα hlν hS
  have hc0 : 0 ≤ c := by have := strip_nonneg hS one_pos le_rfl; simpa using this
  have hBa := isAdmissibleH_of_frostman hsuppf hFf hα'
  have hC := frostman_const_nonneg hF
  have hrad1 : ∀ k, radius k ≤ 1 := fun k => by
    unfold radius; exact pow_le_one₀ (by norm_num) (by norm_num)
  set q := max ((2 : ℝ)⁻¹ ^ α) ((2 : ℝ)⁻¹ ^ γ) with hq
  have hq0 : 0 ≤ q := le_max_of_le_left (Real.rpow_nonneg (by norm_num) _)
  have hq1 : q < 1 := max_lt (Real.rpow_lt_one (by norm_num) (by norm_num) hα)
    (Real.rpow_lt_one (by norm_num) (by norm_num) hγ)
  have hAk : ∀ k, IsAdmissibleH (ν.bind (pK hW hT (radius k))) := fun k =>
    isAdmissibleH_bind_pK hW hT (R₁ := R) hsupp (radius_pos k)
  have hmk : ∀ k, (ν.bind (pK hW hT (radius k))) Set.univ = (ν.map (revMap W T)) Set.univ :=
    fun k => by
      rw [bind_pK_eq hW hT, Measure.map_apply hf MeasurableSet.univ,
        Measure.map_apply hf MeasurableSet.univ, preimage_univ, bind_fc_univ]
  set sd : ℕ → Ω → ℝ := fun k ω =>
    X ω (ν.bind (pK hW hT (radius k))) - X ω (ν.map (revMap W T)) with hsd
  have hmeas : ∀ k, Measurable (sd k) := fun k =>
    (hX.measurable_coord _).sub (hX.measurable_coord _)
  have hint : ∀ k, Integrable (fun ω => sd k ω ^ 2) P := fun k =>
    (memLp_pair_sc hX (hAk k) hBa (hmk k)).integrable_sq
  have hm0 : 0 ≤ (ν Set.univ).toReal := ENNReal.toReal_nonneg
  have hCa : 0 ≤ 2 * (C / α) * (ν Set.univ).toReal := by positivity
  have hA : 0 ≤ 2 * (C / α) * (ν Set.univ).toReal + M * c := by positivity
  have hb : ∀ k, ∫ ω, sd k ω ^ 2 ∂P ≤ (2 * (C / α) * (ν Set.univ).toReal + M * c) * q ^ k := by
    intro k
    have c1 := hX.covariance_eq (ν.bind (pK hW hT (radius k)), ν.map (revMap W T))
      (ν.bind (pK hW hT (radius k)), ν.map (revMap W T)) (hAk k) hBa (hmk k) (hAk k) hBa (hmk k)
    dsimp only at c1
    have hm := hX.centered _ _ (hAk k) hBa (hmk k)
    have key : ∫ ω, (X ω (ν.bind (pK hW hT (radius k))) - X ω (ν.map (revMap W T))) ^ 2 ∂P =
        cov[fun ω => X ω (ν.bind (pK hW hT (radius k))) - X ω (ν.map (revMap W T)),
          fun ω => X ω (ν.bind (pK hW hT (radius k))) - X ω (ν.map (revMap W T)); P] := by
      unfold covariance
      rw [hm]
      simp only [sub_zero, sq]
    show ∫ ω, (X ω (ν.bind (pK hW hT (radius k))) - X ω (ν.map (revMap W T))) ^ 2 ∂P ≤ _
    rw [key, c1, bind_pK_eq hW hT]
    refine (le_abs_self _).trans ((hM _ (radius_pos k) (hrad1 k)).trans ?_)
    have h1 : radius k ^ α ≤ q ^ k := by
      rw [radius_rpow_frostman]
      exact pow_le_pow_left₀ (Real.rpow_nonneg (by norm_num) _) (le_max_left _ _) k
    have h2 : radius k ^ γ ≤ q ^ k := by
      rw [radius_rpow_frostman]
      exact pow_le_pow_left₀ (Real.rpow_nonneg (by norm_num) _) (le_max_right _ _) k
    have e : 2 * (C * radius k ^ α / α) * (ν Set.univ).toReal =
        (2 * (C / α) * (ν Set.univ).toReal) * radius k ^ α := by ring
    rw [e]
    nlinarith [mul_le_mul_of_nonneg_left h1 hCa, mul_le_mul_of_nonneg_left h2 (mul_nonneg hM0 hc0)]
  filter_upwards [ae_tendsto_zero_of_sq_geom_frostman hmeas hint hA hq0 hq1 hb] with ω hω
  have h5 := hω.add_const (X ω (ν.map (revMap W T)))
  simp only [sd, sub_add_cancel, zero_add] at h5
  exact h5

/-- **RC3 for general measures** (smoothing consistency of the unzipped field). For a
probability measure `ν` on `ℍ` with bounded support, Frostman, with `|log Im|` integrable and a
strip bound, and with `f_* ν` Frostman (`f = revMap W T`), almost surely
`evalReg (coordChange x f Q) ν = evalReg x (f_* ν) + Q ∫ log ‖f'‖ dν`. -/
theorem ae_evalReg_coordChange_revMap_gen (hX : IsFreeGFFModConstH X P)
    [IsProbabilityMeasure P] (a : ℝ) {g₁ : ℂ → ℝ} (hg₁ : Continuous g₁) (Q : ℝ)
    {ν : Measure ℂ} [IsProbabilityMeasure ν] {R α C c γ α' C' : ℝ}
    (hsupp : ν (closedBall 0 R ∩ Hbar)ᶜ = 0) (hνH : ∀ᵐ z ∂ν, z ∈ H) (hF : IsFrostman ν α C)
    (hα : 0 < α) (hlν : Integrable (fun z : ℂ => |Real.log z.im|) ν) (hS : StripBound ν c γ)
    (hγ : 0 < γ) (hFf : IsFrostman (ν.map (revMap W T)) α' C') (hα' : 0 < α') :
    ∀ᵐ ω ∂P, evalReg (coordChange (ofFun (fun v => a * Real.log ‖v‖ + g₁ v) + X ω)
        (revMap W T) Q) ν =
      evalReg (ofFun (fun v => a * Real.log ‖v‖ + g₁ v) + X ω) (ν.map (revMap W T)) +
        Q * ∫ u, Real.log ‖deriv (revMap W T) u‖ ∂ν := by
  have hf := TwoPoint.measurable_revMap hW hT
  set R₁ := max R 0 with hR₁
  have hsupp1 : ν (ballH R₁)ᶜ = 0 :=
    measure_mono_null (compl_subset_compl.2 (inter_subset_inter_left _
      (closedBall_subset_closedBall (le_max_left _ _)))) hsupp
  have hsuppR₁ : ν (closedBall 0 R₁ ∩ Hbar)ᶜ = 0 := hsupp1
  have hν : ∀ᵐ z ∂ν, z ∈ H ∧ ‖z‖ ≤ R₁ := by
    filter_upwards [ae_mem_of_compl_null_frostman hsupp1, hνH] with z h1 h2
    exact ⟨h2, by simpa using h1.1⟩
  -- support of the pushforward
  obtain ⟨Bf, hBf⟩ := norm_revMap_le' hW hT R₁
  have hsuppf : (ν.map (revMap W T)) (closedBall 0 Bf ∩ Hbar)ᶜ = 0 := by
    have hae : ∀ᵐ z ∂ν, revMap W T z ∈ closedBall 0 Bf ∩ Hbar :=
      hν.mono fun z hz => ⟨by rw [mem_closedBall, dist_zero_right]; exact hBf z hz.1 hz.2,
        (TwoPoint.im_revMap_pos hW hz.1 hT).le⟩
    rw [Measure.map_apply hf (isClosed_closedBall.inter isClosed_Hbar).measurableSet.compl,
      show revMap W T ⁻¹' (closedBall 0 Bf ∩ Hbar)ᶜ =
        {z : ℂ | revMap W T z ∈ closedBall 0 Bf ∩ Hbar}ᶜ from rfl]
    exact mem_ae_iff.1 hae
  -- the random ingredients
  obtain ⟨Vh, hVc, hVV, hreg⟩ := exists_regular_witness_revMap hW hT hX
    (by norm_num : (0 : ℝ) < 1 / 12) (energyModulus_holds hW hT) a hg₁ Q
  have hfub : ∀ᵐ ω ∂P, ∀ k : ℕ, ∫ u, Vh (pr u (radius k) 0) ω ∂ν =
      X ω (ν.bind (pK hW hT (radius k))) :=
    ae_all_iff.2 fun k => ae_integral_Vhat_eq_gen hW hT hX hVc hVV (le_max_right _ _) hsupp1
      (radius_pos k)
  have hconv := ae_tendsto_push_bind hW hT hX hsuppR₁ hνH hF hα hlν hS hγ hsuppf hFf hα'
  have hrc1 := ae_evalReg_logAdd_eq_frostman hX hsuppf hFf hα' a hg₁.continuousOn
  -- the deterministic part
  have hL1 := logBounded_log_norm_revMap hW hT
  have hL2 := logBounded_comp_revMap hW hT hg₁
  have hL3 := logBounded_log_norm_deriv_revMap hW hT
  set Ψ : ℂ → ℝ := fun w => a * Real.log ‖revMap W T w‖ + g₁ (revMap W T w) +
    Q * Real.log ‖deriv (revMap W T) w‖ with hΨ
  have hDΨ : ∀ w (r : ℝ), 0 < r → Dfun W T a g₁ Q (w, r) = ∫ u, Ψ u ∂foldedCircle w r := by
    intro w r hr
    have j : Integrable (fun u => a * Real.log ‖revMap W T u‖ + g₁ (revMap W T u))
        (foldedCircle w r) := ((hL1.integrable w hr).const_mul a).add (hL2.integrable w hr)
    unfold Dfun
    rw [hΨ, integral_add j ((hL3.integrable w hr).const_mul Q),
      integral_add ((hL1.integrable w hr).const_mul a) (hL2.integrable w hr),
      integral_const_mul, integral_const_mul]
  obtain ⟨A1, hA1, hb1⟩ := hL1.2.2 (R₁ + 1)
  obtain ⟨A2, hA2, hb2⟩ := hL2.2.2 (R₁ + 1)
  obtain ⟨A3, hA3, hb3⟩ := hL3.2.2 (R₁ + 1)
  have hΨb : ∀ u ∈ H, ‖u‖ ≤ R₁ + 1 →
      |Ψ u| ≤ (|a| * A1 + A2 + |Q| * A3) + (|a| + 1 + |Q|) * |Real.log u.im| := by
    intro u hu huR
    have e1 := mul_le_mul_of_nonneg_left (hb1 u hu huR) (abs_nonneg a)
    have e2 := hb2 u hu huR
    have e3 := mul_le_mul_of_nonneg_left (hb3 u hu huR) (abs_nonneg Q)
    have t1 := abs_add_le (a * Real.log ‖revMap W T u‖ + g₁ (revMap W T u))
      (Q * Real.log ‖deriv (revMap W T) u‖)
    have t2 := abs_add_le (a * Real.log ‖revMap W T u‖) (g₁ (revMap W T u))
    rw [abs_mul] at t1 t2
    simp only [hΨ]
    linarith
  have hΨm : Measurable Ψ := ((hL1.1.const_mul a).add hL2.1).add (hL3.1.const_mul Q)
  have hΨc : ContinuousOn Ψ H :=
    ((continuousOn_const.mul hL1.2.1).add hL2.2.1).add (continuousOn_const.mul hL3.2.1)
  have hdet := tendsto_integral_bind_fc hΨm hΨc (by positivity) hΨb hν hlν
  have hrad1 : ∀ k, radius k ≤ 1 := fun k => by
    unfold radius; exact pow_le_one₀ (by norm_num) (by norm_num)
  have hDint : ∀ k : ℕ, Integrable (fun w => ∫ u, Ψ u ∂foldedCircle w (radius k)) ν := fun k =>
    integrable_integral_fc_of_bound hΨm hΨb hν hlν (radius_pos k) (hrad1 k)
  -- integrability of the pieces of `Ψ` against `ν`
  have hν1 : ∀ᵐ z ∂ν, z ∈ H ∧ ‖z‖ ≤ R₁ + 1 := hν.mono fun z hz => ⟨hz.1, by linarith [hz.2]⟩
  have i1 : Integrable (fun w => a * Real.log ‖revMap W T w‖ + g₁ (revMap W T w)) ν := by
    refine (integrable_of_abs_le_logIm (A := A1) (B := 1) hL1.1.aestronglyMeasurable
      (hν1.mono fun z hz => by rw [one_mul]; exact hb1 z hz.1 hz.2) hlν |>.const_mul a).add ?_
    exact integrable_of_abs_le_logIm (A := A2) (B := 1) hL2.1.aestronglyMeasurable
      (hν1.mono fun z hz => by rw [one_mul]; exact hb2 z hz.1 hz.2) hlν
  have i2 : Integrable (fun w => Real.log ‖deriv (revMap W T) w‖) ν :=
    integrable_of_abs_le_logIm (A := A3) (B := 1) hL3.1.aestronglyMeasurable
      (hν1.mono fun z hz => by rw [one_mul]; exact hb3 z hz.1 hz.2) hlν
  have hΨint : ∫ w, Ψ w ∂ν = ∫ w, (a * Real.log ‖revMap W T w‖ + g₁ (revMap W T w)) ∂ν +
      Q * ∫ u, Real.log ‖deriv (revMap W T) u‖ ∂ν := by
    rw [hΨ, integral_add i1 (i2.const_mul Q), integral_const_mul]
  have hGm : Measurable fun v : ℂ => a * Real.log ‖v‖ + g₁ v :=
    ((Real.measurable_log.comp measurable_norm).const_mul a).add hg₁.measurable
  have hGmap : ∫ z, (a * Real.log ‖z‖ + g₁ z) ∂(ν.map (revMap W T)) =
      ∫ w, (a * Real.log ‖revMap W T w‖ + g₁ (revMap W T w)) ∂ν :=
    integral_map hf.aemeasurable hGm.aestronglyMeasurable
  -- assembly
  filter_upwards [hreg, hfub, hconv, hrc1] with ω hω h1 h2 h3
  set y := coordChange (ofFun (fun v => a * Real.log ‖v‖ + g₁ v) + X ω) (revMap W T) Q with hy
  have hk : ∀ k : ℕ, ∫ z, avgReg y k z ∂ν =
      X ω (ν.bind (pK hW hT (radius k))) + ∫ w, (∫ u, Ψ u ∂foldedCircle w (radius k)) ∂ν := by
    intro k
    have hae : (fun z => avgReg y k z) =ᵐ[ν]
        fun z => Vh (pr z (radius k) 0) ω + ∫ u, Ψ u ∂foldedCircle z (radius k) := by
      filter_upwards [hν] with z hz
      rw [hω.avgReg_eq k (show (0 : ℝ) ≤ z.im from le_of_lt hz.1), hDΨ z _ (radius_pos k)]
    rw [integral_congr_ae hae,
      integral_add (f := fun z => Vh (pr z (radius k) 0) ω)
        (g := fun z => ∫ u, Ψ u ∂foldedCircle z (radius k))
        (integrable_of_continuous_ballH (g := fun z => Vh (pr z (radius k) 0) ω)
          ((hVc ω).comp (continuous_pr_fst (radius k) 0)) hsupp1) (hDint k), h1 k]
  have hlim : Tendsto (fun k => ∫ z, avgReg y k z ∂ν) atTop
      (𝓝 (X ω (ν.map (revMap W T)) + ∫ w, Ψ w ∂ν)) := by
    rw [show (fun k => ∫ z, avgReg y k z ∂ν) = fun k => X ω (ν.bind (pK hW hT (radius k))) +
      ∫ w, (∫ u, Ψ u ∂foldedCircle w (radius k)) ∂ν from funext hk]
    exact h2.add hdet
  have hev : evalReg y ν = X ω (ν.map (revMap W T)) + ∫ w, Ψ w ∂ν := hlim.limUnder_eq
  rw [hev, h3, hΨint, hGmap]
  ring

end RC3Gen

end CoordReg
end QuantumZipper
