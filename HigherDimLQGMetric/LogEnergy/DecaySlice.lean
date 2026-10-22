import HigherDimLQGMetric.LogEnergy.DecayLocalized
set_option autoImplicit false
noncomputable section
open MeasureTheory
open HigherDimLFPP (Rd)
namespace HigherDimLQGMetric

theorem iteratedFDeriv_prod_slice_right_norm_le
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E × F → ℝ) (x : E) (y : F) (n : ℕ)
    (hf : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f (x,y)) :
    ‖iteratedFDeriv ℝ n (fun v : F => f (x,v)) y‖ ≤
      ‖iteratedFDeriv ℝ n f (x,y)‖ := by
  let g : F →L[ℝ] (E × F) :=
    (LinearIsometry.inr ℝ E F).toContinuousLinearMap
  have hchain := iteratedFDeriv_comp_affine_local f g (x, (0:F)) y n
    (by simpa [g] using hf)
  have heq : iteratedFDeriv ℝ n (fun v : F => f (x,v)) y =
      (iteratedFDeriv ℝ n f (x,y)).compContinuousLinearMap (fun _ => g) := by
    simpa [g] using hchain
  rw [heq]
  simpa [g] using ContinuousMultilinearMap.norm_compContinuous_linearIsometry_le
    (iteratedFDeriv ℝ n f (x,y)) (fun _ => LinearIsometry.inr ℝ E F)

theorem iteratedFDeriv_prod_slice_left_norm_le
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E × F → ℝ) (x : E) (y : F) (n : ℕ)
    (hf : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f (x,y)) :
    ‖iteratedFDeriv ℝ n (fun v : E => f (v,y)) x‖ ≤
      ‖iteratedFDeriv ℝ n f (x,y)‖ := by
  let g : E →L[ℝ] (E × F) :=
    (LinearIsometry.inl ℝ E F).toContinuousLinearMap
  have hchain := iteratedFDeriv_comp_affine_local f g ((0:E),y) x n
    (by simpa [g] using hf)
  have heq : iteratedFDeriv ℝ n (fun v : E => f (v,y)) x =
      (iteratedFDeriv ℝ n f (x,y)).compContinuousLinearMap (fun _ => g) := by
    simpa [g] using hchain
  rw [heq]
  simpa [g] using ContinuousMultilinearMap.norm_compContinuous_linearIsometry_le
    (iteratedFDeriv ℝ n f (x,y)) (fun _ => LinearIsometry.inl ℝ E F)

theorem decayLocalKernel_u_contDiff {d : ℕ} {a b : ℝ}
    (ha : 0 < a) (hab : a < b) {ε : ℝ}
    (hε : ε ∈ Set.Icc (0:ℝ) (a/(8*b))) (x : Rd d) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u : Rd d => decayLocalKernelSpatial ha (ha.trans hab) ε (x,u)) := by
  rw [contDiff_iff_contDiffAt]
  intro u
  have hmap : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun v : Rd d => (x,v)) u := by fun_prop
  exact ((decayLocalKernelSpatial_contDiff ha hab hε).contDiffAt).comp u hmap

theorem decayLocalKernel_u_tsupport_subset {d : ℕ} {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (ε : ℝ) (x : Rd d) :
    tsupport (fun u : Rd d => decayLocalKernelSpatial ha hb ε (x,u)) ⊆
      Metric.closedBall 0 (2*b) := by
  have hsupp : Function.support
      (fun u : Rd d => decayLocalKernelSpatial ha hb ε (x,u)) ⊆
      Metric.closedBall 0 (2*b) := by
    intro u hu
    by_contra hnot
    have hu' : u ∉ tsupport (decayOuterCutoff hb) :=
      fun hmem => hnot (decayOuterCutoff_tsupport_subset hb hmem)
    have h0 := image_eq_zero_of_notMem_tsupport hu'
    exact hu (by simp [decayLocalKernelSpatial, decayLocalKernel, h0])
  exact closure_minimal hsupp Metric.isClosed_closedBall

theorem decayLocalKernel_u_hasCompactSupport {d : ℕ} {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (ε : ℝ) (x : Rd d) :
    HasCompactSupport (fun u : Rd d => decayLocalKernelSpatial ha hb ε (x,u)) :=
  (isCompact_closedBall 0 (2*b)).of_isClosed_subset (isClosed_tsupport _)
    (decayLocalKernel_u_tsupport_subset ha hb ε x)

theorem decayLocalKernel_u_isCMBounded {d : ℕ} (hd : 1 ≤ d)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε ∈ Set.Icc (0:ℝ) (a/(8*b)),
      ∀ x : Rd d,
        IsCMBounded
          (fun u : Rd d => decayLocalKernelSpatial ha (ha.trans hab) ε (x,u))
          (C*ε) := by
  let m := d/2+1
  let Ku : Set (Rd d) := Metric.closedBall 0 (2*b)
  have hb : 0 < b := ha.trans hab
  obtain ⟨Ccm, hCcm, hCM⟩ := exists_isCMBounded_quantDeriv hd Ku
    measurableSet_closedBall (isCompact_closedBall 0 (2*b)).measure_lt_top.ne
  obtain ⟨C₀, hC₀, hzero⟩ := decayLocalKernelSpatial_global_deriv_bound (d:=d) ha hab 0
  obtain ⟨Cₙ, hCₙ, hderiv⟩ := decayLocalKernelSpatial_global_deriv_bound (d:=d) ha hab (2*m)
  let B : ℝ := 1 + max C₀ Cₙ
  have hB : 0 < B := by dsimp [B]; linarith [le_max_left C₀ Cₙ, hC₀]
  let C : ℝ := Ccm*B
  refine ⟨C, mul_pos hCcm hB, ?_⟩
  intro ε hε x
  let F : Rd d → ℝ := fun u => decayLocalKernelSpatial ha hb ε (x,u)
  have hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F :=
    decayLocalKernel_u_contDiff ha hab hε x
  have hc : HasCompactSupport F := decayLocalKernel_u_hasCompactSupport ha hb ε x
  have hs : tsupport F ⊆ Ku := decayLocalKernel_u_tsupport_subset ha hb ε x
  have hM : 0 ≤ B*ε := mul_nonneg hB.le hε.1
  have h0 : ∀ u, |F u| ≤ B*ε := by
    intro u
    have h := hzero ε hε (x,u)
    rw [norm_iteratedFDeriv_zero] at h
    rw [Real.norm_eq_abs] at h
    exact h.trans (mul_le_mul_of_nonneg_right
      ((le_max_left C₀ Cₙ).trans (le_add_of_nonneg_left (by norm_num))) hε.1)
  have hm : ∀ u, ‖iteratedFDeriv ℝ (2*m) F u‖ ≤ B*ε := by
    intro u
    have hsmooth : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (decayLocalKernelSpatial ha hb ε) (x,u) :=
      (decayLocalKernelSpatial_contDiff (d:=d) ha hab hε).contDiffAt
    calc
      _ ≤ ‖iteratedFDeriv ℝ (2*m)
          (decayLocalKernelSpatial ha hb ε) (x,u)‖ :=
        iteratedFDeriv_prod_slice_right_norm_le _ x u (2*m) hsmooth
      _ ≤ Cₙ*ε := hderiv ε hε (x,u)
      _ ≤ B*ε := mul_le_mul_of_nonneg_right
        ((le_max_right C₀ Cₙ).trans (le_add_of_nonneg_left (by norm_num))) hε.1
  have h := hCM hF hc hs hM h0 hm
  simpa [C, mul_assoc, F, hb] using h
end HigherDimLQGMetric
