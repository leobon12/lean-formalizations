import HigherDimLQGMetric.LogEnergy.DecayScale
set_option autoImplicit false
noncomputable section
open MeasureTheory
open HigherDimLFPP (Rd)
namespace HigherDimLQGMetric

theorem logCov_decay {d : ℕ} (hd : 1 ≤ d) {a b : ℝ}
    (ha : 0 < a) (hab : a < b) :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ r r' : ℝ, 0 < r' → r' ≤ ε₀ * r →
      ∀ φ ψ : TestRd0 d, tsupport φ.1 ⊆ ann 0 (a * r) (b * r) →
        tsupport ψ.1 ⊆ ann 0 (a * r') (b * r') →
        |logCovRd φ.1 ψ.1| ≤ C * (r' / r) * (logNorm φ.1 * logNorm ψ.1) := by
  let ε₀ : ℝ := a/(8*b)
  have hε₀ : 0 < ε₀ := div_pos ha (mul_pos (by norm_num) (ha.trans hab))
  obtain ⟨C,hC,hunit⟩ := logCovRd_decay_unit hd ha hab
  refine ⟨C,ε₀,hC,hε₀,?_⟩
  intro r r' hr' hrr φ ψ hφ hψ
  have hr : 0 < r := by
    by_contra hnot
    have hnonpos : r ≤ 0 := le_of_not_gt hnot
    have hmul : ε₀ * r ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hε₀.le hnonpos
    linarith
  let ε : ℝ := r'/r
  have hεpos : 0 < ε := div_pos hr' hr
  have hεle : ε ≤ ε₀ := (div_le_iff₀ hr).2 (by simpa [mul_comm,ε₀] using hrr)
  have hε : ε ∈ Set.Icc (0:ℝ) ε₀ := ⟨hεpos.le,hεle⟩
  let Φ : TestRd0 d := ⟨testAffinePull r⁻¹ 0 φ.1,
    integral_testAffinePull_eq_zero r⁻¹ 0 φ.2⟩
  let Ψ : TestRd0 d := ⟨testAffinePull r'⁻¹ 0 ψ.1,
    integral_testAffinePull_eq_zero r'⁻¹ 0 ψ.2⟩
  have hΦann : tsupport Φ.1 ⊆ ann 0 a b :=
    testAffinePull_inv_tsupport_ann hr φ.1 hφ
  have hΨann : tsupport Ψ.1 ⊆ ann 0 a b :=
    testAffinePull_inv_tsupport_ann hr' ψ.1 hψ
  have hΨball : tsupport Ψ.1 ⊆ Metric.closedBall 0 b := by
    intro u hu
    have hu' := hΨann hu
    change a < ‖u - 0‖ ∧ ‖u - 0‖ < b at hu'
    simpa [Metric.mem_closedBall, dist_eq_norm] using hu'.2.le
  have hφeq : testAffinePull r 0 Φ.1 = φ.1 :=
    testAffinePull_inv_inv hr φ.1
  have hre : r*ε = r' := by
    dsimp [ε]
    field_simp
  have hψeq : testAffinePull r 0 (testAffinePull ε 0 Ψ.1) = ψ.1 := by
    rw [testAffinePull_testAffinePull]
    rw [hre, smul_zero, zero_add]
    exact testAffinePull_inv_inv hr' ψ.1
  have hmean : ∫ y : Rd d, (testAffinePull ε 0 Ψ.1) y = 0 :=
    integral_testAffinePull_eq_zero ε 0 Ψ.2
  have hcov : logCovRd φ.1 ψ.1 =
      r^(2*d)*logCovRd Φ.1 (testAffinePull ε 0 Ψ.1) := by
    rw [←hφeq, ←hψeq]
    exact logCovRd_testAffinePull Φ.1 (testAffinePull ε 0 Ψ.1) hmean hr 0
  have hφnorm : logNorm φ.1 = r^d*logNorm Φ.1 := by
    rw [←hφeq]
    exact logNorm_testAffinePull_eq Φ hr
  have hψnorm : logNorm ψ.1 = r'^d*logNorm Ψ.1 := by
    rw [←testAffinePull_inv_inv hr' ψ.1]
    exact logNorm_testAffinePull_eq Ψ hr'
  have hpow : r^(2*d)*ε^d = r^d*r'^d := by
    have h := congrArg (fun t : ℝ => t^d) hre
    rw [mul_pow] at h
    calc
      r^(2*d)*ε^d = r^d*(r^d*ε^d) := by
        rw [show 2*d = d+d by omega, pow_add]
        ring
      _ = r^d*r'^d := by rw [h]
  rw [hcov, abs_mul, abs_of_nonneg (pow_nonneg hr.le _)]
  have hbnd := hunit ε (by simpa [ε₀] using hε) hεpos Φ Ψ hΦann hΨball
  calc
    r^(2*d)*|logCovRd Φ.1 (testAffinePull ε 0 Ψ.1)| ≤
      r^(2*d)*(((C*ε)*ε^d)*(logNorm Φ.1*logNorm Ψ.1)) :=
        mul_le_mul_of_nonneg_left hbnd (pow_nonneg hr.le _)
    _ = C*(r'/r)*(logNorm φ.1*logNorm ψ.1) := by
      rw [hφnorm,hψnorm]
      change r^(2*d) * ((C*ε)*ε^d*(logNorm Φ.1*logNorm Ψ.1)) =
        C*ε*((r^d*logNorm Φ.1)*(r'^d*logNorm Ψ.1))
      calc
        _ = C*ε*((r^(2*d)*ε^d)*(logNorm Φ.1*logNorm Ψ.1)) := by ring
        _ = _ := by rw [hpow]; ring
end HigherDimLQGMetric
