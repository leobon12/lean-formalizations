import HigherDimLQGMetric.LogEnergy.DecayPotential
set_option autoImplicit false
noncomputable section
open MeasureTheory
open HigherDimLFPP (Rd)
namespace HigherDimLQGMetric

theorem decayKernelPotential_tsupport_subset {d : ℕ} {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (ε : ℝ) (ψ : TestRd d) :
    tsupport (decayKernelPotential ha hb ε ψ) ⊆ annCl 0 (a/2) (2*b) := by
  have hsupp : Function.support (decayKernelPotential ha hb ε ψ) ⊆
      annCl 0 (a/2) (2*b) := by
    intro x hx
    by_contra hnot
    have hzero : ∀ u : Rd d, decayLocalKernelSpatial ha hb ε (x,u) = 0 := by
      intro u
      have hts : (x,u) ∉ tsupport (decayLocalKernelSpatial ha hb ε) :=
        fun hm => hnot (decayLocalKernelSpatial_tsupport_subset ha hb ε hm).1
      exact image_eq_zero_of_notMem_tsupport hts
    exact hx (by simp [decayKernelPotential, hzero])
  exact closure_minimal hsupp (isClosed_annCl 0 (a/2) (2*b))

theorem decayKernelPotential_hasCompactSupport {d : ℕ} {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (ε : ℝ) (ψ : TestRd d) :
    HasCompactSupport (decayKernelPotential ha hb ε ψ) := by
  have hK : IsCompact (annCl (0:Rd d) (a/2) (2*b)) := by
    apply IsCompact.of_isClosed_subset (isCompact_closedBall (0 : Rd d) (2*b))
      (isClosed_annCl 0 (a/2) (2*b))
    intro x hx
    change a/2 ≤ ‖x - 0‖ ∧ ‖x - 0‖ ≤ 2*b at hx
    simpa [Metric.mem_closedBall, dist_eq_norm] using hx.2
  exact hK.of_isClosed_subset (isClosed_tsupport _)
    (decayKernelPotential_tsupport_subset ha hb ε ψ)

theorem decayKernelPotential_isCMBounded {d : ℕ} (hd : 1 ≤ d)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε ∈ Set.Icc (0:ℝ) (a/(8*b)),
      ∀ ψ : TestRd0 d,
        IsCMBounded (decayKernelPotential ha (ha.trans hab) ε ψ.1)
          ((C*ε)*logNorm ψ.1) := by
  let Kx : Set (Rd d) := annCl 0 (a/2) (2*b)
  have hK : IsCompact Kx := by
    apply IsCompact.of_isClosed_subset (isCompact_closedBall (0 : Rd d) (2*b))
      (isClosed_annCl 0 (a/2) (2*b))
    intro x hx
    change a/2 ≤ ‖x - 0‖ ∧ ‖x - 0‖ ≤ 2*b at hx
    simpa [Metric.mem_closedBall, dist_eq_norm] using hx.2
  have hKmeas : MeasurableSet Kx := (isClosed_annCl 0 (a/2) (2*b)).measurableSet
  obtain ⟨Ccm,hCcm,hCM⟩ := exists_isCMBounded_quantDeriv hd Kx hKmeas hK.measure_lt_top.ne
  obtain ⟨C₀,hC₀,hzero⟩ := decayKernelPotential_deriv_bound hd ha hab 0
  obtain ⟨Cₙ,hCₙ,hderiv⟩ := decayKernelPotential_deriv_bound hd ha hab (2*(d/2+1))
  let B : ℝ := 1 + max C₀ Cₙ
  have hB : 0 < B := by dsimp [B]; linarith [le_max_left C₀ Cₙ, hC₀.le]
  let C : ℝ := Ccm*B
  refine ⟨C, mul_pos hCcm hB, ?_⟩
  intro ε hε ψ
  let F := decayKernelPotential ha (ha.trans hab) ε ψ.1
  have hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F :=
    decayKernelPotential_contDiff ha hab hε ψ.1
  have hc : HasCompactSupport F :=
    decayKernelPotential_hasCompactSupport ha (ha.trans hab) ε ψ.1
  have hs : tsupport F ⊆ Kx :=
    decayKernelPotential_tsupport_subset ha (ha.trans hab) ε ψ.1
  let M : ℝ := (B*ε)*logNorm ψ.1
  have hM : 0 ≤ M := mul_nonneg (mul_nonneg hB.le hε.1) (logNorm_nonneg ψ.1)
  have h0 : ∀ x, |F x| ≤ M := by
    intro x
    have h := hzero ε hε ψ x
    rw [norm_iteratedFDeriv_zero] at h
    rw [Real.norm_eq_abs] at h
    calc
      |F x| ≤ (C₀*ε)*logNorm ψ.1 := h
      _ ≤ M := by
        dsimp [M]
        have hle : C₀ ≤ B := by dsimp [B]; linarith [le_max_left C₀ Cₙ]
        nlinarith [mul_le_mul_of_nonneg_right hle hε.1, logNorm_nonneg ψ.1]
  have hm : ∀ x, ‖iteratedFDeriv ℝ (2*(d/2+1)) F x‖ ≤ M := by
    intro x
    have h := hderiv ε hε ψ x
    calc
      _ ≤ (Cₙ*ε)*logNorm ψ.1 := h
      _ ≤ M := by
        dsimp [M]
        have hle : Cₙ ≤ B := by dsimp [B]; linarith [le_max_right C₀ Cₙ]
        nlinarith [mul_le_mul_of_nonneg_right hle hε.1, logNorm_nonneg ψ.1]
  have h := hCM hF hc hs hM h0 hm
  simpa [C, M, mul_assoc, mul_comm, mul_left_comm, F] using h
end HigherDimLQGMetric
