import SupercriticalConformalCovariance.Markov.SignedEnergy
import LQGMetric.Field.MarkovGermVer3E

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric TopologicalSpace
open scoped RealInnerProductSpace

namespace SupercriticalConformalCovariance.Markov

open LQGMetric LQGMetric.MarkovGauss LQGMetric.MarkovZB LQGMetric.MarkovGerm
  LQGMetric.MarkovGermVer QuantumZipper QuantumZipper.K3

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistC}

/-- The Schur constant for a ball of arbitrary radius. -/
def schurLR (R : ℝ) : ℝ :=
  2 * (2 * R * (Real.pi * (2 * R) ^ 2) + logBallConst)

lemma schurLR_nonneg {R : ℝ} (hR : 0 ≤ R) : 0 ≤ schurLR R := by
  have := logBallConst_nonneg
  unfold schurLR
  positivity

lemma hasCompactSupport_of_ball {R : ℝ} (_hR : 0 ≤ R) {ζ : ℂ → ℝ}
    (hζR : ∀ x, R < ‖x‖ → ζ x = 0) : HasCompactSupport ζ :=
  HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) R) fun x hx => by
    simp only [mem_closedBall, dist_zero_right, not_le] at hx
    exact hζR x hx

set_option maxHeartbeats 1000000 in
/-- **Poincaré inequality from the Schur bound** -/
theorem sq_dev_le_schur_general (hh : IsWholePlaneGFF h P) {R : ℝ} (hR : 0 ≤ R) {ζ : ℂ → ℝ}
    (hζs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ζ) (hζ01 : ∀ x, 0 ≤ ζ x ∧ ζ x ≤ 1)
    (hζR : ∀ x, R < ‖x‖ → ζ x = 0) (g : zsSub ((⊤ : Opens ℂ) : Set ℂ)) :
    ∫ x, (ζ x * (g.1 x - zmean ζ g.1)) ^ 2 ≤ schurLR R * ‖cmLin hh ⊤ g‖ ^ 2 := by
  have hζc := hasCompactSupport_of_ball hR hζR
  have hfs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g.1 := g.2.1
  set e := ‖cmLin hh ⊤ g‖
  have hζ2i : Integrable fun x => ζ x * ζ x :=
    integrable_of_cs (hζs.continuous.mul hζs.continuous) hζc.mul_right
  have hζfi : Integrable fun x => ζ x * ζ x * g.1 x :=
    integrable_of_cs ((hζs.continuous.mul hζs.continuous).mul hfs.continuous)
      hζc.mul_right.mul_right
  set A := ∫ x, ζ x * ζ x
  set B := ∫ x, ζ x * ζ x * g.1 x
  set c := zmean ζ g.1
  have hcBA : c = B / A := rfl
  have hBA : B - c * A = 0 := by
    by_cases hA : A = 0
    · have hz := (integral_eq_zero_iff_of_nonneg (fun x => mul_self_nonneg (ζ x)) hζ2i).1 hA
      have hB : B = 0 := integral_eq_zero_of_ae (by
        filter_upwards [hz] with x hx
        simp only [Pi.zero_apply] at hx ⊢
        rw [hx, zero_mul])
      rw [hB, hA]; ring
    · rw [hcBA]; field_simp; ring
  set F : ℂ → ℝ := fun x => g.1 x - c with hF
  have hFs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F := hfs.sub contDiff_const
  set pf : ℂ → ℝ := fun x => ζ x * (ζ x * F x) with hpf
  have hps : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) pf := hζs.mul (hζs.mul hFs)
  have hpc : HasCompactSupport pf := hζc.mul_right
  have hpi : Integrable pf := integrable_of_cs hps.continuous hpc
  have hp0 : ∫ x, pf x = 0 := by
    have e1 : pf = fun x => ζ x * ζ x * g.1 x - c * (ζ x * ζ x) := funext fun x => by
      simp only [pf, F]; ring
    rw [e1, integral_sub hζfi (hζ2i.const_mul c), integral_const_mul]
    linarith [hBA]
  set p : TestC0 := ⟨tC hps hpc, hp0⟩
  have hpfun : (p.1 : ℂ → ℝ) = pf := rfl
  set X := ∫ x, (ζ x * F x) ^ 2
  have hXi : Integrable fun x => (ζ x * F x) ^ 2 :=
    integrable_of_cs ((hζs.continuous.mul hFs.continuous).pow 2)
      (hcs_of_vanish hζc fun x hx => by simp [hx])
  have hX0 : 0 ≤ X := integral_nonneg fun x => sq_nonneg _
  have hXp : ⟪cmLin hh ⊤ g, (memLp_pair hh p).toLp (pairProc h p)⟫ = X := by
    rw [inner_cmLin_pair, hpfun]
    have e1 : (fun x => pf x * g.1 x) = fun x => (ζ x * F x) ^ 2 + c * pf x := funext fun x => by
      simp only [pf, F]; ring
    rw [e1, integral_add hXi (hpi.const_mul c), integral_const_mul, hp0, mul_zero, add_zero]
  have hMp : ‖(memLp_pair hh p).toLp (pairProc h p)‖ ^ 2 ≤ schurLR R * X := by
    rw [norm_pair_sq hh, hpfun]
    have hL := logCov_self_le_schur (R := R) hR hps.continuous
      fun x hx => by simp [pf, hζR x hx]
    refine hL.trans (mul_le_mul_of_nonneg_left (integral_mono_of_nonneg
      (ae_of_all _ fun x => sq_nonneg _) hXi (ae_of_all _ fun x => ?_)) (schurLR_nonneg hR))
    have h1 := hζ01 x
    change (ζ x * (ζ x * F x)) ^ 2 ≤ (ζ x * F x) ^ 2
    rw [mul_pow]
    nlinarith [sq_nonneg (ζ x * F x), (pow_le_one₀ h1.1 h1.2 : ζ x ^ 2 ≤ 1)]
  have he0 : 0 ≤ e := norm_nonneg _
  set M := ‖(memLp_pair hh p).toLp (pairProc h p)‖
  have h1 : X ≤ e * M := hXp ▸ real_inner_le_norm _ _
  have hM0 : 0 ≤ M := norm_nonneg _
  have h2 : X * X ≤ X * (schurLR R * e ^ 2) := by
    have h3 : X * X ≤ (e * M) ^ 2 := by nlinarith
    have h4 : (e * M) ^ 2 ≤ e ^ 2 * (schurLR R * X) := by
      rw [mul_pow]; exact mul_le_mul_of_nonneg_left hMp (sq_nonneg e)
    nlinarith
  change X ≤ schurLR R * e ^ 2
  rcases hX0.lt_or_eq with hpos | h0
  · exact le_of_mul_le_mul_left h2 hpos
  · rw [← h0]; have := schurLR_nonneg hR; positivity

/-- A smooth cutoff equal to one on any prescribed compact set, with a finite ball support. -/
theorem exists_global_cutoff (K : Set ℂ) (hK : IsCompact K) :
    ∃ (R : ℝ) (ζ : ℂ → ℝ), 0 ≤ R ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ζ ∧
      (∀ x, 0 ≤ ζ x ∧ ζ x ≤ 1) ∧
      (∀ x, R < ‖x‖ → ζ x = 0) ∧
      ∀ x ∈ K, ζ x = 1 := by
  obtain ⟨r, hr⟩ := hK.isBounded.subset_ball (0 : ℂ)
  let R : ℝ := max r 0 + 1
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hKR : K ⊆ ball (0 : ℂ) R := by
    intro x hx
    have h := hr hx
    rw [mem_ball, dist_zero_right] at h ⊢
    have : r ≤ R := by dsimp [R]; linarith [le_max_left r 0]
    exact h.trans_le this
  obtain ⟨ζ, hs, hv, hsupp, hone⟩ := exists_contDiff_support_eq_eq_one_iff
    (n := (⊤ : ℕ∞)) (s := ball (0 : ℂ) R) (t := K)
    isOpen_ball hK.isClosed hKR
  refine ⟨R, ζ, hR, hs, fun x => hv (mem_range_self x), fun x hx => ?_, fun x hx => ?_⟩
  · by_contra hne
    have hm : x ∈ Function.support ζ := hne
    rw [hsupp] at hm
    have := mem_ball.mp hm
    rw [dist_zero_right] at this
    linarith
  · exact (hone x).1 hx

end SupercriticalConformalCovariance.Markov
