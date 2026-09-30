import QuantumZipper.Proofs.Zipper.Cor15RezipRegTame
import QuantumZipper.Proofs.Zipper.Cor15ZipFixBasic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# COR15-ZIPCOORD (3): the convergence form of RC3 at the pushed folded circles

Sheffield, arXiv:1012.4797, Corollary 1.5; analytic input: Duplantier–Sheffield, *Liouville
quantum gravity and KPZ*, Invent. Math. 185 (2011), Prop. 3.1 (via RC3).

`zc_ae_ccGood_coordChange_revMap_gen` is `CoordReg.ae_evalReg_coordChange_revMap_gen`
(`CoordRegEnergy.lean`) with the conclusion replaced by what its proof establishes before
identifying the limit: the regularizing integrals are integrable and converge (`CCGoodAt`).
`zc_ae_ccGood_pushed_fc` is `ae_evalReg_coordChange_pushed_fc` (`Cor15RezipRegTame.lean`) in the
same form. The proofs are copied verbatim up to the last step (own bookkeeping).
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped ENNReal Real ComplexConjugate Topology NNReal

namespace QuantumZipper
namespace Cor15Group

section Gen

open CoordReg CircleFubini FrostmanReg SmoothConv RegSample ProbabilityTheory

theorem zc_ae_ccGood_coordChange_revMap_gen {W : ℝ → ℝ} {T : ℝ} (hW : Continuous W) (hT : 0 ≤ T)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}
    (hX : IsFreeGFFModConstH X P)
    [IsProbabilityMeasure P] (a : ℝ) {g₁ : ℂ → ℝ} (hg₁ : Continuous g₁) (Q : ℝ)
    {ν : Measure ℂ} [IsProbabilityMeasure ν] {R α C c γ α' C' : ℝ}
    (hsupp : ν (closedBall 0 R ∩ Hbar)ᶜ = 0) (hνH : ∀ᵐ z ∂ν, z ∈ H) (hF : IsFrostman ν α C)
    (hα : 0 < α) (hlν : Integrable (fun z : ℂ => |Real.log z.im|) ν) (hS : StripBound ν c γ)
    (hγ : 0 < γ) (hFf : IsFrostman (ν.map (revMap W T)) α' C') (hα' : 0 < α') :
    ∀ᵐ ω ∂P, (∀ k : ℕ, Integrable (fun z => avgReg (coordChange
        (ofFun (fun v => a * Real.log ‖v‖ + g₁ v) + X ω) (revMap W T) Q) k z) ν) ∧
      ∃ L, Tendsto (fun k => ∫ z, avgReg (coordChange
        (ofFun (fun v => a * Real.log ‖v‖ + g₁ v) + X ω) (revMap W T) Q) k z ∂ν) atTop (𝓝 L) := by
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
  refine ⟨fun k => ?_, _, hlim⟩
  have hae : (fun z => avgReg y k z) =ᵐ[ν]
      fun z => Vh (pr z (radius k) 0) ω + ∫ u, Ψ u ∂foldedCircle z (radius k) := by
    filter_upwards [hν] with z hz
    rw [hω.avgReg_eq k (show (0 : ℝ) ≤ z.im from le_of_lt hz.1), hDΨ z _ (radius_pos k)]
  exact ((integrable_of_continuous_ballH (g := fun z => Vh (pr z (radius k) 0) ω)
    ((hVc ω).comp (continuous_pr_fst (radius k) 0)) hsupp1).add (hDint k)).congr hae.symm

end Gen

section Pushed

theorem zc_ae_ccGood_pushed_fc {V : ℝ → ℝ} {t : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → FieldSample} (hX : IsFreeGFFModConstH X P) [IsProbabilityMeasure P]
    (κ Q : ℝ) (hV : Continuous V) (hV0 : V 0 = 0) (ht : 0 < t) {w₀ : ℂ} {r₀ : ℝ}
    (hr₀ : 0 < r₀) (hK : foldedCircle w₀ r₀ (H \ revMap V t '' H) = 0) {S : Set ℂ}
    (hS : H \ revMap V t '' H ⊆ S) {M : ℝ} (hM : ∀ r ∈ Icc (0 : ℝ) t, |V r| ≤ M) {C β : ℝ}
    (hC : 0 < C) (hβ : 0 < β)
    (hHol : ∀ z ∈ H, ∀ w ∈ H, ‖z‖ ≤ ‖w₀‖ + r₀ + (12 * M + 8 * Real.sqrt t) →
      ‖w‖ ≤ ‖w₀‖ + r₀ + (12 * M + 8 * Real.sqrt t) →
      ‖revMap V t z - revMap V t w‖ ≤ C * ‖z - w‖ ^ β)
    {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      foldedCircle w₀ r₀ {z | infDist z S ≤ ε} ≤ ENNReal.ofReal (c * ε ^ (1 / 8 : ℝ))) :
    ∀ᵐ ω ∂P, CCGoodAt (coordChange (ofFun (h0rev κ) + X ω) (revMap V t) Q) (revMapInv V t)
      (foldedCircle w₀ r₀) := by
  set ρ := ‖w₀‖ + r₀ + (12 * M + 8 * Real.sqrt t) with hρ
  set σ := foldedCircle w₀ r₀ with hσ
  have hσD := ae_mem_revMap_image_fc hr₀ hK
  have hσρ : ∀ᵐ z ∂σ, ‖revMapInv V t z‖ ≤ ρ := by
    filter_upwards [hσD, TwoPoint.foldedCircle_ae_norm_le w₀ hr₀.le] with z hz hzn
    exact (norm_revMapInv_le hV hV0 ht hM hz).trans (by rw [hρ]; linarith)
  set ν := σ.map (revMapInv V t) with hν
  have hνP : IsProbabilityMeasure ν :=
    (Measure.isProbabilityMeasure_map_iff (measurable_revMapInv hV ht.le).aemeasurable).2
      inferInstance
  have hsupp := map_revMapInv_compl_closedBall_Hbar hV ht.le hσD hσρ
  have hνH := ae_mem_H_map_revMapInv hV ht.le hσD
  have hF := isFrostman_map_revMapInv_fc hV ht.le hr₀ hC.le hβ hHol hσD hσρ
  have hpow := map_revMapInv_fc_im_lt_le hV ht.le hr₀ hS hC hβ hHol hσD hσρ hc0 hc
  have hA0 : 0 ≤ (18 * Real.sqrt (2 / r₀) + c + 1) * C ^ (1 / 8 : ℝ) := by positivity
  have hβ8 : 0 < β / 8 := by positivity
  have hSt := stripBound_of_pow hνH hA0 hβ8 hpow
  have hR : ∀ᵐ z ∂ν, z.im ≤ ρ := by
    filter_upwards [(mem_ae_iff.2 hsupp : ∀ᵐ z ∂ν, z ∈ closedBall (0 : ℂ) ρ ∩ Hbar)] with z hz
    have h1 := hz.1
    rw [mem_closedBall, dist_zero_right] at h1
    exact (Complex.im_le_norm z).trans h1
  have hlν := integrable_abs_log_im_of_pow hνH hR hA0 hβ8 hpow
  have hFf : IsFrostman (ν.map (revMap V t)) 1 (6 / r₀) := by
    rw [hν, map_revMap_map_revMapInv hV ht.le hσD]
    exact isFrostman_fc w₀ hr₀
  have hB := zc_ae_ccGood_coordChange_revMap_gen hV ht.le hX (P := P)
    (2 / Real.sqrt κ) (g₁ := fun _ => 0) continuous_const Q hsupp hνH hF hβ hlν hSt
    (by positivity) hFf one_pos
  rw [← CoordReg.h0rev_eq_logAdd κ] at hB
  exact hB

end Pushed

end Cor15Group
end QuantumZipper
