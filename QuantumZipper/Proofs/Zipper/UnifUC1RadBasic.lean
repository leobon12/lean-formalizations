import QuantumZipper.Proofs.Zipper.UnifUC1Push
import QuantumZipper.Proofs.Zipper.UnifRC3MixStab

/-!
# UNIF-RC3-E1 (decision D33), step 1: the radius modulus at radii `≥ r₀`

For `p = (u, s) ∈ tri T` and `r₀ ≤ ρ, ρ' ≤ 1` (`abs_kernelCov2_muUS_rad_le`):

`|E(muUS p ρ − muUS p ρ')| ≤ spaceK M T r₀ (Ra + 1) · |ρ − ρ'|^{1/12}`,

uniformly in `p` (`M = sup_{[0,T]} |W|`, `Ra = revBound (2M) T (‖d‖ + 2^{-k})`). Proof: `muUS p ρ` is
the mixture over `z ∼ α_{u,s}` of the pushed circles `ψ_u * fc(z, ρ)` (`ψ_u = revMap (vrev W u) u`
on `ℍ`), so the mixture bound `abs_kernelCov2_mix_le` (UNIF-RC3-MIX) and the JointMod space modulus
`abs_kernelCov2_νT_space_unif` (at `w = w' = z`) give the claim. The constant is polynomial in
`1/r₀`: `spaceK M T r₀ R · r₀² ≤ spaceKs M T R` (`spaceK_mul_sq_le`, own elementary computation).

Also: `muUS p 0 = (ψ_{u+s})_* fc(d, 2^{-k})` is admissible (`admissible_muUS_zero`), using the
cocycle `ψ_u ∘ R_{u,s} = ψ_{u+s}` (`revMap_vrev_split`).

Sources: Hu–Miller–Peres, Ann. Probab. 38 (2010), Prop. 2.1; Duplantier–Sheffield, Invent. Math.
185 (2011), Prop. 3.1 (through the JointMod moduli); the bookkeeping is own elementary argument.
-/

noncomputable section

open MeasureTheory Filter Metric Set
open scoped ENNReal Real Topology

namespace QuantumZipper
namespace RegUnif

open RegCont B2

variable {W : ℝ → ℝ}

/-! ## The space constant is polynomial in `1/r₀` -/

/-- The `r₀`-free majorant of `spaceK M T r₀ R · r₀²`. -/
def spaceKs (M T R : ℝ) : ℝ :=
  2 * (2 + 24 * (18 + 12 * Real.sqrt (R ^ 2 + 4 * T)) +
      2 * (6 * (18 + 12 * Real.sqrt (R ^ 2 + 4 * T)) +
        2 * Real.log (revBound (2 * M) T R + revBound (2 * M) T R + 1))) *
      Real.sqrt (R ^ 2 + 4 * T) ^ ((1 / 3 : ℝ) / 2) +
    148 * (6 * (18 + 12 * Real.sqrt (R ^ 2 + 4 * T)) +
      2 * Real.log (revBound (2 * M) T R + revBound (2 * M) T R + 1))

theorem frostC_mul_le {T r₀ R : ℝ} (hr₀ : 0 < r₀) (hr₁ : r₀ ≤ 1) :
    frostC T r₀ R * r₀ ≤ 18 + 12 * Real.sqrt (R ^ 2 + 4 * T) := by
  have hs : 0 < Real.sqrt r₀ := Real.sqrt_pos.2 hr₀
  have hs1 : Real.sqrt r₀ ≤ 1 := by
    have := Real.sqrt_le_sqrt hr₁; rwa [Real.sqrt_one] at this
  have hss : Real.sqrt r₀ * Real.sqrt r₀ = r₀ := Real.mul_self_sqrt hr₀.le
  have e1 : 18 / Real.sqrt r₀ * r₀ = 18 * Real.sqrt r₀ := by
    rw [div_mul_eq_mul_div, mul_div_assoc, Real.div_sqrt]
  have e2 : 12 * Real.sqrt (R ^ 2 + 4 * T) / r₀ * r₀ = 12 * Real.sqrt (R ^ 2 + 4 * T) :=
    div_mul_cancel₀ _ hr₀.ne'
  unfold frostC
  rw [add_mul, e1, e2]
  linarith

theorem potMax_eq (CF Bf : ℝ) : TwoPoint.potMax CF Bf = 6 * CF + 2 * Real.log (Bf + Bf + 1) := by
  unfold TwoPoint.potMax; ring

theorem holderK_eq (CF Bf : ℝ) :
    TwoPoint.holderK CF Bf = 2 + 24 * CF + 2 * (6 * CF + 2 * Real.log (Bf + Bf + 1)) := by
  unfold TwoPoint.holderK; rw [potMax_eq]; ring

theorem spaceK_mul_sq_le {M T r₀ R : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T) (hr₀ : 0 < r₀)
    (hr₁ : r₀ ≤ 1) : spaceK M T r₀ R * r₀ ^ 2 ≤ spaceKs M T R := by
  have hBf0 : 0 ≤ revBound (2 * M) T R := revBound_nonneg (by linarith) hT
  have hLg : 0 ≤ Real.log (revBound (2 * M) T R + revBound (2 * M) T R + 1) :=
    Real.log_nonneg (by linarith)
  have hCF0 : 0 ≤ frostC T r₀ R := by unfold frostC; positivity
  have hCFr := frostC_mul_le (T := T) (R := R) hr₀ hr₁
  have hs : 0 < Real.sqrt r₀ := Real.sqrt_pos.2 hr₀
  have hs1 : Real.sqrt r₀ ≤ 1 := by
    have := Real.sqrt_le_sqrt hr₁; rwa [Real.sqrt_one] at this
  have hss : Real.sqrt r₀ * Real.sqrt r₀ = r₀ := Real.mul_self_sqrt hr₀.le
  have hS6 : 0 ≤ Real.sqrt (R ^ 2 + 4 * T) ^ ((1 / 3 : ℝ) / 2) := by positivity
  unfold spaceK spaceConst potC spaceKs
  rw [potMax_eq, holderK_eq]
  generalize Real.sqrt (R ^ 2 + 4 * T) ^ ((1 / 3 : ℝ) / 2) = S6 at hS6 ⊢
  generalize Real.log (revBound (2 * M) T R + revBound (2 * M) T R + 1) = Lg at hLg ⊢
  generalize frostC T r₀ R = CF at hCF0 hCFr ⊢
  generalize Real.sqrt (R ^ 2 + 4 * T) = Q at hCFr ⊢
  generalize Real.sqrt r₀ = s at hs hs1 hss ⊢
  subst hss
  have eK : (2 * (2 + 24 * CF + 2 * (6 * CF + 2 * Lg)) * S6 + 144 * (6 * CF + 2 * Lg) / s +
      4 * (6 * CF + 2 * Lg)) * (s * s) ^ 2 =
      2 * ((2 + 24 * CF + 2 * (6 * CF + 2 * Lg)) * (s * s) ^ 2) * S6 +
        144 * ((6 * CF + 2 * Lg) * (s * s)) * s + 4 * ((6 * CF + 2 * Lg) * (s * s) ^ 2) := by
    field_simp
  rw [eK]
  set F := 18 + 12 * Q with hF
  have hr2 : (s * s) ^ 2 ≤ s * s := by nlinarith [mul_pos hs hs]
  have hP : (6 * CF + 2 * Lg) * (s * s) ≤ 6 * F + 2 * Lg := by nlinarith [mul_pos hs hs]
  have hP2 : (6 * CF + 2 * Lg) * (s * s) ^ 2 ≤ (6 * CF + 2 * Lg) * (s * s) :=
    mul_le_mul_of_nonneg_left hr2 (by positivity)
  have hH : (2 + 24 * CF + 2 * (6 * CF + 2 * Lg)) * (s * s) ^ 2 ≤
      2 + 24 * F + 2 * (6 * F + 2 * Lg) := by
    have h1 : (s * s) ^ 2 ≤ 1 := by nlinarith [mul_pos hs hs]
    have h2 : CF * (s * s) ^ 2 ≤ F := by nlinarith [mul_pos hs hs]
    nlinarith
  have hPs : (6 * CF + 2 * Lg) * (s * s) * s ≤ 6 * F + 2 * Lg := by
    have h0 : 0 ≤ (6 * CF + 2 * Lg) * (s * s) := by positivity
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hH hS6]

/-! ## The pushed circle and its smoothings -/

theorem measurableSet_H_norm_le (B : ℝ) : MeasurableSet {x : ℂ | x ∈ H ∧ ‖x‖ ≤ B} :=
  isOpen_H.measurableSet.inter (isClosed_le continuous_norm continuous_const).measurableSet

theorem isProbabilityMeasure_alphaUS (hW : Continuous W) (d : ℂ) (k : ℕ) {T : ℝ} {p : ℝ × ℝ}
    (hp : p ∈ tri T) : IsProbabilityMeasure (alphaUS W d k p) := by
  have hRm := TwoPoint.measurable_revMap (continuous_vrev hW (p.1 + p.2)) hp.2.1
  unfold alphaUS; infer_instance

theorem alphaUS_ae_H_norm (hW : Continuous W) {T Mw : ℝ} (hMw : ∀ t ∈ Icc (0 : ℝ) T, |W t| ≤ Mw)
    (d : ℂ) (k : ℕ) {p : ℝ × ℝ} (hp : p ∈ tri T) :
    ∀ᵐ x ∂alphaUS W d k p, x ∈ H ∧ ‖x‖ ≤ revBound (2 * Mw) T (‖d‖ + radius k) := by
  have hRm := TwoPoint.measurable_revMap (continuous_vrev hW (p.1 + p.2)) hp.2.1
  exact (ae_map_iff hRm.aemeasurable (measurableSet_H_norm_le _)).2
    ((alphaUS_ae_facts hW hMw d k hp).mono fun z hz => ⟨hz.2.2.2.1, hz.2.2.2.2⟩)

theorem muUS_eq_map (hW : Continuous W) (hW0 : W 0 = 0) {T Mw : ℝ}
    (hMw : ∀ t ∈ Icc (0 : ℝ) T, |W t| ≤ Mw) (d : ℂ) (k : ℕ) {p : ℝ × ℝ} (hp : p ∈ tri T)
    {ρ : ℝ} (hρ : 0 < ρ) :
    muUS W d k p ρ = (bindFc (alphaUS W d k p) ρ).map (revMap (vrev W p.1) p.1) := by
  have := isProbabilityMeasure_alphaUS hW d k hp
  refine Measure.map_congr ?_
  filter_upwards [CoordReg.bind_fc_mem_H_norm _ hρ
    ((alphaUS_ae_H_norm hW hMw d k hp).mono fun x hx => hx.2)] with x hx
  exact fwdMapInv_eq_revMap_vrev hW hW0 hp.1 hx.1

/-- `muUS p 0 = (ψ_{u+s})_* fc(d, 2^{-k})` (cocycle `ψ_u ∘ R_{u,s} = ψ_{u+s}`). -/
theorem muUS_zero_eq (hW : Continuous W) (hW0 : W 0 = 0) {T Mw : ℝ}
    (hMw : ∀ t ∈ Icc (0 : ℝ) T, |W t| ≤ Mw) (d : ℂ) (k : ℕ) {p : ℝ × ℝ} (hp : p ∈ tri T) :
    muUS W d k p 0 = (foldedCircle d (radius k)).map (revMap (vrev W (p.1 + p.2)) (p.1 + p.2)) := by
  have := isProbabilityMeasure_alphaUS hW d k hp
  have hαH := (alphaUS_ae_H_norm hW hMw d k hp).mono fun x hx => hx.1
  have hRm := TwoPoint.measurable_revMap (continuous_vrev hW (p.1 + p.2)) hp.2.1
  have hψm := TwoPoint.measurable_revMap (continuous_vrev hW p.1) hp.1
  show (bindFc (alphaUS W d k p) 0).map (fwdMapInv W p.1) = _
  rw [bindFc_zero_of_ae_H hαH]
  have e1 : (alphaUS W d k p).map (fwdMapInv W p.1) =
      (alphaUS W d k p).map (revMap (vrev W p.1) p.1) := by
    refine Measure.map_congr ?_
    filter_upwards [hαH] with x hx
    exact fwdMapInv_eq_revMap_vrev hW hW0 hp.1 hx
  rw [e1]
  unfold alphaUS
  rw [Measure.map_map hψm hRm]
  refine Measure.map_congr ?_
  filter_upwards [TwoPoint.foldedCircle_ae_mem_H d (radius_pos k)] with z hz
  exact (revMap_vrev_split hW hp.1 hp.1 hp.2.1 le_rfl hz).symm

theorem admissible_muUS_zero (hW : Continuous W) (hW0 : W 0 = 0) {T Mw : ℝ}
    (hMw : ∀ t ∈ Icc (0 : ℝ) T, |W t| ≤ Mw) (d : ℂ) (k : ℕ) {p : ℝ × ℝ} (hp : p ∈ tri T) :
    IsAdmissibleH (muUS W d k p 0) ∧ muUS W d k p 0 univ = 1 := by
  rw [muUS_zero_eq hW hW0 hMw d k hp]
  have hV := continuous_vrev hW (p.1 + p.2)
  have ht : 0 ≤ p.1 + p.2 := add_nonneg hp.1 hp.2.1
  have hRm := TwoPoint.measurable_revMap hV ht
  have hrk := radius_pos k
  have hG : GoodM ((foldedCircle d (radius k)).map (revMap (vrev W (p.1 + p.2)) (p.1 + p.2)))
      (1 / 3) (frostC T (radius k) (‖d‖ + radius k)) (revBound (2 * Mw) T (‖d‖ + radius k)) := by
    refine ⟨by infer_instance, isFrostman_pfc_frostC hV ht hp.2.2 hrk le_rfl le_rfl, ?_⟩
    refine ae_iff.1 ((ae_map_iff hRm.aemeasurable (measurableSet_closedBall_inter_Hbar _)).2 ?_)
    filter_upwards [TwoPoint.foldedCircle_ae_mem_H d hrk,
      TwoPoint.foldedCircle_ae_norm_le d hrk.le] with z hz hzn
    refine ⟨mem_closedBall_zero_iff.2 ((norm_revMap_le_revBound hV ht
      (fun r _ => abs_vrev_le hMw ⟨ht, hp.2.2⟩ r) _ hzn).trans (revBound_mono hp.2.2)),
      show (0 : ℝ) ≤ _ from le_of_lt (TwoPoint.im_revMap_pos hV hz ht)⟩
  exact ⟨hG.admissible (by norm_num), hG.prob.measure_univ⟩

/-! ## One pushed circle -/

theorem goodM_pushed_circle (hW : Continuous W) (hW0 : W 0 = 0) {T Mw : ℝ}
    (hMw : ∀ t ∈ Icc (0 : ℝ) T, |W t| ≤ Mw) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) T) {z : ℂ}
    {r₀ ρ R : ℝ} (hr₀ : 0 < r₀) (hρ : r₀ ≤ ρ) (hzR : ‖z‖ + ρ ≤ R) :
    νT W z ρ u = (foldedCircle z ρ).map (revMap (vrev W u) u) ∧
      GoodM ((foldedCircle z ρ).map (revMap (vrev W u) u)) (1 / 3) (frostC T r₀ R)
        (revBound (2 * Mw) T R) := by
  have hρ0 : 0 < ρ := hr₀.trans_le hρ
  have e : νT W z ρ u = (foldedCircle z ρ).map (revMap (vrev W u) u) := by
    refine Measure.map_congr ?_
    filter_upwards [TwoPoint.foldedCircle_ae_mem_H z hρ0] with y hy
    exact fwdMapInv_eq_revMap_vrev hW hW0 hu.1 hy
  obtain ⟨h1, h2, h3⟩ := νT_box_facts hW hW0 hr₀ hMw hu hρ hzR
  rw [e] at h1 h2 h3
  refine ⟨e, h1, fun w r hr => h2 w r hr, ae_iff.1 (h3.mono fun x hx => ?_)⟩
  exact ⟨mem_closedBall_zero_iff.2 hx.2, show (0 : ℝ) ≤ _ from le_of_lt hx.1⟩

/-! ## The radius modulus at radii `≥ r₀` -/

/-- **Radius modulus at radii `≥ r₀`, uniform in `p`.** -/
theorem abs_kernelCov2_muUS_rad_le (hW : Continuous W) (hW0 : W 0 = 0) {T Mw : ℝ}
    (hMw : ∀ t ∈ Icc (0 : ℝ) T, |W t| ≤ Mw) (d : ℂ) (k : ℕ) {p : ℝ × ℝ} (hp : p ∈ tri T)
    {r₀ ρ ρ' : ℝ} (hr₀ : 0 < r₀) (hρ : r₀ ≤ ρ) (hρ' : r₀ ≤ ρ') (hρ1 : ρ ≤ 1) (hρ1' : ρ' ≤ 1) :
    |kernelCov2 neumannH (muUS W d k p ρ, muUS W d k p ρ') (muUS W d k p ρ, muUS W d k p ρ')| ≤
      spaceK Mw T r₀ (revBound (2 * Mw) T (‖d‖ + radius k) + 1) *
        |ρ - ρ'| ^ (1 / 12 : ℝ) := by
  have hT : 0 ≤ T := hp.1.trans (by linarith [hp.2.1, hp.2.2])
  have hMw0 : 0 ≤ Mw := (abs_nonneg _).trans (hMw 0 ⟨le_rfl, hT⟩)
  set Ra := revBound (2 * Mw) T (‖d‖ + radius k) with hRa
  have hu : p.1 ∈ Icc (0 : ℝ) T := ⟨hp.1, by linarith [hp.2.1, hp.2.2]⟩
  have := isProbabilityMeasure_alphaUS hW d k hp
  have hψm := TwoPoint.measurable_revMap (continuous_vrev hW p.1) hp.1
  rw [muUS_eq_map hW hW0 hMw d k hp (hr₀.trans_le hρ), muUS_eq_map hW hW0 hMw d k hp
    (hr₀.trans_le hρ')]
  have hα := alphaUS_ae_H_norm hW hMw d k hp
  refine abs_kernelCov2_mix_le hψm (α := 1 / 3) (C := frostC T r₀ (Ra + 1))
    (B := revBound (2 * Mw) T (Ra + 1)) (by norm_num) (by unfold frostC; positivity)
    (revBound_nonneg (by linarith) hT) ?_ ?_
  · filter_upwards [hα] with z hz
    exact ⟨(goodM_pushed_circle hW hW0 hMw hu hr₀ hρ (by linarith [hz.2])).2,
      (goodM_pushed_circle hW hW0 hMw hu hr₀ hρ' (by linarith [hz.2])).2⟩
  · filter_upwards [hα] with z hz
    obtain ⟨e, -⟩ := goodM_pushed_circle hW hW0 hMw hu hr₀ hρ (R := Ra + 1) (by linarith [hz.2])
    obtain ⟨e', -⟩ := goodM_pushed_circle hW hW0 hMw hu hr₀ hρ' (R := Ra + 1)
      (by linarith [hz.2])
    have h := abs_kernelCov2_νT_space_unif hW hW0 hr₀ hMw (β := 1 / 12) (by norm_num) le_rfl hu
      hρ hρ' (w := z) (w' := z) (R := Ra + 1) (by linarith [hz.2]) (by linarith [hz.2])
    rw [e, e', sub_self, norm_zero, zero_add] at h
    exact (le_abs_self _).trans h

end RegUnif
end QuantumZipper
