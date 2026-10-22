import HigherDimLQGMetric.LogEnergy.DecayMixed
set_option autoImplicit false
noncomputable section
open MeasureTheory
open HigherDimLFPP (Rd)
namespace HigherDimLQGMetric

theorem decayKernelXDeriv_zero_outside {d : ℕ} {a b : ℝ}
    (ha : 0 < a) (hab : a < b) {ε : ℝ}
    (hε : ε ∈ Set.Icc (0:ℝ) (a/(8*b))) (n : ℕ)
    (z : Rd d × Rd d)
    (hz : z ∉ annCl 0 (a/2) (2*b) ×ˢ Metric.closedBall 0 (2*b)) :
    decayKernelXDeriv ha (ha.trans hab) ε n z = 0 := by
  rw [decayKernelXDeriv_eq_full ha hab hε]
  have hts : z ∉ tsupport (decayLocalKernelSpatial ha (ha.trans hab) ε) :=
    fun hmem => hz (decayLocalKernelSpatial_tsupport_subset ha (ha.trans hab) ε hmem)
  have hzero : iteratedFDeriv ℝ n
      (decayLocalKernelSpatial ha (ha.trans hab) ε) z = 0 := by
    by_contra hne
    exact hts (support_iteratedFDeriv_subset n (by simpa [Function.mem_support] using hne))
  rw [hzero]
  ext v
  simp [ContinuousMultilinearMap.compContinuousLinearMap_apply]

theorem decayKernelXDeriv_u_contDiff {d : ℕ} {a b : ℝ}
    (ha : 0 < a) (hab : a < b) {ε : ℝ}
    (hε : ε ∈ Set.Icc (0:ℝ) (a/(8*b))) (n : ℕ) (x : Rd d) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u : Rd d => decayKernelXDeriv ha (ha.trans hab) ε n (x,u)) := by
  rw [contDiff_iff_contDiffAt]
  intro u
  have hmap : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun v : Rd d => (ε,x,v)) u := by fun_prop
  have h := (decayKernelXFull_contDiffAt ha hab n (ε,x,u) hε).comp u hmap
  convert h using 1
  funext v
  exact (decayKernelXFull_eq ha hab hε n x v).symm

theorem decayKernelXDeriv_u_tsupport_subset {d : ℕ} {a b : ℝ}
    (ha : 0 < a) (hab : a < b) {ε : ℝ}
    (hε : ε ∈ Set.Icc (0:ℝ) (a/(8*b))) (n : ℕ) (x : Rd d) :
    tsupport (fun u : Rd d => decayKernelXDeriv ha (ha.trans hab) ε n (x,u)) ⊆
      Metric.closedBall 0 (2*b) := by
  have hsupp : Function.support
      (fun u : Rd d => decayKernelXDeriv ha (ha.trans hab) ε n (x,u)) ⊆
      Metric.closedBall 0 (2*b) := by
    intro u hu
    by_contra hnot
    exact hu (decayKernelXDeriv_zero_outside ha hab hε n (x,u) (by
      intro hmem
      exact hnot hmem.2))
  exact closure_minimal hsupp Metric.isClosed_closedBall

theorem decayKernelXDeriv_u_global_deriv_bound {d : ℕ} {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (n m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε ∈ Set.Icc (0:ℝ) (a/(8*b)),
      ∀ x u : Rd d,
        ‖iteratedFDeriv ℝ m
          (fun v : Rd d => decayKernelXDeriv ha (ha.trans hab) ε n (x,v)) u‖ ≤ C*ε := by
  obtain ⟨C, hC, hbound⟩ := decayKernelXDeriv_u_deriv_bound (d:=d) ha hab n m
  refine ⟨C, hC, ?_⟩
  intro ε hε x u
  let F : Rd d → (Rd d [×n]→L[ℝ] ℝ) :=
    fun v => decayKernelXDeriv ha (ha.trans hab) ε n (x,v)
  by_cases hx : x ∈ annCl 0 (a/2) (2*b)
  · by_cases hu : u ∈ Metric.closedBall 0 (2*b)
    · exact hbound ε hε x u hx hu
    have hts : u ∉ tsupport F :=
      fun hmem => hu (decayKernelXDeriv_u_tsupport_subset ha hab hε n x hmem)
    have hzero : iteratedFDeriv ℝ m F u = 0 := by
      by_contra hne
      exact hts (support_iteratedFDeriv_subset m (by simpa [Function.mem_support] using hne))
    rw [hzero, norm_zero]
    exact mul_nonneg hC hε.1
  · have hF : F = 0 := by
      funext v
      exact decayKernelXDeriv_zero_outside ha hab hε n (x,v) (by
        intro hmem
        exact hx hmem.1)
    change ‖iteratedFDeriv ℝ m F u‖ ≤ _
    rw [hF]
    have hz : iteratedFDeriv ℝ m (0 : Rd d → (Rd d [×n]→L[ℝ] ℝ)) u = 0 :=
      congrFun (iteratedFDeriv_fun_zero (𝕜:=ℝ) (E:=Rd d)
        (F:=Rd d [×n]→L[ℝ] ℝ) (n:=m)) u
    rw [hz, norm_zero]
    exact mul_nonneg hC hε.1
end HigherDimLQGMetric
