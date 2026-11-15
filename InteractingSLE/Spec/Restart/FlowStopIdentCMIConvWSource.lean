/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FlowStopIdentCMIConvVProof
import InteractingSLE.Spec.Sec7.LocalExtDStep5

/-! # Energy-Cauchy subsequences for any dominated CMCut source approximation -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
universe u
namespace InteractingSLE.Restart.FlowStopIdentCMI
open QuantumZipper (H greenH)
open LQGMetric (TestOn DistOn)
open LocalExt
namespace CMCut
variable (F : CMCut)

/-- The existing dominated-energy argument applies to any dominated source approximants. -/
theorem tendsto_greenEnergy_sub_of_dominated
    {s : ℕ → TestOn upperHalfPlaneOpens} (hs : ∀ n z, |s n z| ≤ |F.src z|)
    (hlim : ∀ z, Tendsto (fun n => s n z) atTop (𝓝 (F.src z))) :
    Tendsto (fun p : ℕ × ℕ => greenEnergy (fun z => s p.1 z - s p.2 z)
      (fun z => s p.1 z - s p.2 z)) (atTop ×ˢ atTop) (𝓝 0) := by
  have hdom := F.integrable_abs_mul_greenH.abs.const_mul 4
  have hmeasA : ∀ n, Measurable (s n) := fun n => (s n).contDiff.continuous.measurable
  have hmeasF : ∀ p : ℕ × ℕ, Measurable fun q : ℂ × ℂ =>
      (s p.1 q.1 - s p.2 q.1) * (s p.1 q.2 - s p.2 q.2) * greenH q.1 q.2 :=
    fun p => ((((hmeasA p.1).comp measurable_fst).sub ((hmeasA p.2).comp measurable_fst)).mul
      (((hmeasA p.1).comp measurable_snd).sub ((hmeasA p.2).comp measurable_snd))).mul
        QuantumZipper.measurable_greenH
  have key := tendsto_integral_filter_of_dominated_convergence (μ := (volume : Measure ℂ).prod volume)
    (l := atTop ×ˢ atTop)
    (F := fun (p : ℕ × ℕ) (q : ℂ × ℂ) => (s p.1 q.1 - s p.2 q.1) *
      (s p.1 q.2 - s p.2 q.2) * greenH q.1 q.2)
    (f := fun _ => 0) _
    (Eventually.of_forall fun p => (hmeasF p).aestronglyMeasurable)
    (Eventually.of_forall fun p => ae_of_all _ fun q => ?_) hdom (ae_of_all _ fun q => ?_)
  · simpa [greenEnergy] using key
  · simp only [Real.norm_eq_abs, abs_mul]
    have a1 := hs p.1 q.1
    have a2 := hs p.2 q.1
    have a3 := hs p.1 q.2
    have a4 := hs p.2 q.2
    have h1 : |s p.1 q.1 - s p.2 q.1| ≤ 2 * |F.src q.1| := (abs_sub _ _).trans (by linarith)
    have h2 : |s p.1 q.2 - s p.2 q.2| ≤ 2 * |F.src q.2| := (abs_sub _ _).trans (by linarith)
    calc |s p.1 q.1 - s p.2 q.1| * |s p.1 q.2 - s p.2 q.2| * |greenH q.1 q.2|
        ≤ (2 * |F.src q.1|) * (2 * |F.src q.2|) * |greenH q.1 q.2| := by gcongr
      _ = 4 * (|(|F.src q.1|)| * |(|F.src q.2|)| * |greenH q.1 q.2|) := by rw [abs_abs, abs_abs]; ring
  · have h1 : Tendsto (fun p : ℕ × ℕ => s p.1 q.1 - s p.2 q.1) (atTop ×ˢ atTop) (𝓝 0) := by
      have t1 := hlim q.1
      simpa using (t1.comp tendsto_fst).sub (t1.comp tendsto_snd)
    have h2 : Tendsto (fun p : ℕ × ℕ => s p.1 q.2 - s p.2 q.2) (atTop ×ˢ atTop) (𝓝 0) := by
      have t2 := hlim q.2
      simpa using (t2.comp tendsto_fst).sub (t2.comp tendsto_snd)
    simpa using (h1.mul h2).mul_const (greenH q.1 q.2)

/-- Any dominated source approximation has a subsequence satisfying the local-set tilt's covariance bound. -/
theorem exists_covCauchy_subseq {s : ℕ → TestOn upperHalfPlaneOpens}
    (hs : ∀ n z, |s n z| ≤ |F.src z|)
    (hlim : ∀ z, Tendsto (fun n => s n z) atTop (𝓝 (F.src z))) :
    ∃ a : ℕ → ℕ, StrictMono a ∧ LocalExt.IsCovCauchy (fun n => s (a n)) := by
  have he : ∀ k, ∀ᶠ N in atTop, ∀ n m : ℕ, N ≤ n → N ≤ m →
      LocalExt.greenEnergy (s n - s m) (s n - s m) < (1 / 16 : ℝ) ^ k := by
    intro k
    have h := (tendsto_order.1 (F.tendsto_greenEnergy_sub_of_dominated hs hlim)).2
      ((1 / 16 : ℝ) ^ k) (by positivity)
    rw [prod_atTop_atTop_eq, eventually_atTop_prod_self'] at h
    obtain ⟨a, ha⟩ := h
    filter_upwards [eventually_ge_atTop a] with N hN n m hn hm
    exact ha n (hN.trans hn) m (hN.trans hm)
  obtain ⟨a, ha, hb⟩ := extraction_forall_of_eventually he
  refine ⟨a, ha, fun N n m hn hm => ?_⟩
  rw [LocalExt.zeroGFFTestCov_H_eq_greenEnergy]
  exact (hb N (a n) (a m) (ha.monotone hn) (ha.monotone hm)).le

end CMCut
end InteractingSLE.Restart.FlowStopIdentCMI
