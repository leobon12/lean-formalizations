import HigherDimLQGMetric.LogEnergy.DecayPair
set_option autoImplicit false
noncomputable section
open MeasureTheory
open HigherDimLFPP (Rd)
namespace HigherDimLQGMetric

theorem decayKernelXDeriv_isCMBounded {d : ℕ} (hd : 1 ≤ d)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε ∈ Set.Icc (0:ℝ) (a/(8*b)),
      ∀ (x : Rd d) (L : (Rd d [×n]→L[ℝ] ℝ) →L[ℝ] ℝ),
        IsCMBounded (fun u : Rd d =>
          L (decayKernelXDeriv ha (ha.trans hab) ε n (x,u)))
          ((C*ε)*‖L‖) := by
  let Ku : Set (Rd d) := Metric.closedBall 0 (2*b)
  obtain ⟨Ccm, hCcm, hCM⟩ := exists_isCMBounded_quantDeriv hd Ku
    measurableSet_closedBall (isCompact_closedBall 0 (2*b)).measure_lt_top.ne
  obtain ⟨C₀,hC₀,hzero⟩ := decayKernelXDeriv_u_global_deriv_bound (d:=d) ha hab n 0
  obtain ⟨Cₙ,hCₙ,hderiv⟩ := decayKernelXDeriv_u_global_deriv_bound
    (d:=d) ha hab n (2*(d/2+1))
  let B : ℝ := 1 + max C₀ Cₙ
  have hB : 0 < B := by dsimp [B]; linarith [le_max_left C₀ Cₙ, hC₀]
  let C : ℝ := Ccm*B
  refine ⟨C, mul_pos hCcm hB, ?_⟩
  intro ε hε x L
  let A : Rd d → (Rd d [×n]→L[ℝ] ℝ) :=
    fun u => decayKernelXDeriv ha (ha.trans hab) ε n (x,u)
  let F : Rd d → ℝ := L ∘ A
  have hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A :=
    decayKernelXDeriv_u_contDiff ha hab hε n x
  have hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F :=
    L.contDiff.comp hA
  have hAts : tsupport A ⊆ Ku :=
    decayKernelXDeriv_u_tsupport_subset ha hab hε n x
  have hFts : tsupport F ⊆ Ku :=
    (tsupport_comp_subset (map_zero L) A).trans hAts
  have hc : HasCompactSupport F :=
    (isCompact_closedBall 0 (2*b)).of_isClosed_subset (isClosed_tsupport _) hFts
  let M : ℝ := (B*ε)*‖L‖
  have hM : 0 ≤ M := mul_nonneg (mul_nonneg hB.le hε.1) (norm_nonneg L)
  have h0 : ∀ u, |F u| ≤ M := by
    intro u
    have h := hzero ε hε x u
    rw [norm_iteratedFDeriv_zero] at h
    calc
      |F u| = ‖L (A u)‖ := by simp [F]
      _ ≤ ‖L‖ * ‖A u‖ := L.le_opNorm _
      _ ≤ ‖L‖ * (C₀*ε) := mul_le_mul_of_nonneg_left h (norm_nonneg L)
      _ ≤ M := by
        dsimp [M, B]
        have hle : C₀ ≤ B := by dsimp [B]; linarith [le_max_left C₀ Cₙ]
        nlinarith [mul_le_mul_of_nonneg_right hle hε.1, norm_nonneg L]
  have hm : ∀ u, ‖iteratedFDeriv ℝ (2*(d/2+1)) F u‖ ≤ M := by
    intro u
    have h := hderiv ε hε x u
    have hle : Cₙ ≤ B := by dsimp [B]; linarith [le_max_right C₀ Cₙ]
    calc
      _ ≤ ‖L‖ * ‖iteratedFDeriv ℝ (2*(d/2+1)) A u‖ :=
        L.norm_iteratedFDeriv_comp_left hA.contDiffAt
          (WithTop.coe_le_coe.mpr le_top)
      _ ≤ ‖L‖ * (Cₙ*ε) := mul_le_mul_of_nonneg_left h (norm_nonneg L)
      _ ≤ M := by
        dsimp [M]
        nlinarith [mul_le_mul_of_nonneg_right hle hε.1, norm_nonneg L]
  have h := hCM hF hc hFts hM h0 hm
  simpa [C, M, mul_assoc, mul_comm, mul_left_comm, F, A, Function.comp_def] using h
end HigherDimLQGMetric
