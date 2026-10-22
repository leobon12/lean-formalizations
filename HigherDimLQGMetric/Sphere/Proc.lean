import HigherDimLQGMetric.Sphere.Conv

/-!
# The mollified sphere-average process `sphProc g ε r z`

Packet F3 (Phase A, block A1), targets 2 and 4 (preparation). MA0 Details (a) D-F3.

`sphProc g ε r z` is `⟨g, σ_{r,z} * ψ_ε⟩ = g (sphMol ε z r)` for `ε ≠ 0` and the sphere average
`g_r(z) = sphereAvg g r z` for `ε = 0`. For an LGF `h`, `d ≥ 2`, `ε ≥ 0`, `r > 0`, it is the a.s.
limit of the pairings `h (sphMol (approxScale n ε) z r)` (`approxScale n ε = 2^{-n}` if `ε = 0`,
`= ε` otherwise; `IsWholeSpaceLGF.ae_tendsto_sphProc`), so its increments are a.s. limits of
mean-zero pairings, with `logCov` of the laws `sphLaw r z (approxScale n ε)` as covariances.

This file also records the four-slot algebra of HigherDimLFPP's `logCov` (`logCov_sub_first` …,
pure algebra on the definition) and the continuity of `logCov` of sphere laws in the scales
(`tendsto_logCov_sphLaw`, `tendsto_logCov_sphLaw_posM`), both from the transport bound
`exists_abs_logCov_sphLaw_le` (`Sphere/Law.lean`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ}

/-! ### Four-slot algebra of `logCov` -/

section LogCovAlgebra

variable (μ μ' ν ν' α α' β β' : Measure (Rd d))

theorem logCov_sub_first :
    HigherDimLFPP.logCov μ ν α β - HigherDimLFPP.logCov μ' ν α β =
      HigherDimLFPP.logCov μ μ' α β := by
  unfold HigherDimLFPP.logCov; ring

theorem logCov_sub_second :
    HigherDimLFPP.logCov μ ν α β - HigherDimLFPP.logCov μ ν' α β =
      -HigherDimLFPP.logCov ν ν' α β := by
  unfold HigherDimLFPP.logCov; ring

theorem logCov_sub_third :
    HigherDimLFPP.logCov μ ν α β - HigherDimLFPP.logCov μ ν α' β =
      HigherDimLFPP.logCov μ ν α α' := by
  unfold HigherDimLFPP.logCov; ring

theorem logCov_sub_fourth :
    HigherDimLFPP.logCov μ ν α β - HigherDimLFPP.logCov μ ν α β' =
      -HigherDimLFPP.logCov μ ν β β' := by
  unfold HigherDimLFPP.logCov; ring

/-- Telescoping all four slots. -/
theorem logCov_sub_logCov :
    HigherDimLFPP.logCov μ ν α β - HigherDimLFPP.logCov μ' ν' α' β' =
      HigherDimLFPP.logCov μ μ' α β - HigherDimLFPP.logCov ν ν' α β +
        HigherDimLFPP.logCov μ' ν' α α' - HigherDimLFPP.logCov μ' ν' β β' := by
  unfold HigherDimLFPP.logCov; ring

/-- Scaling of the second pair. -/
theorem logCov_smul_right [SFinite α] [SFinite β] (c : ℝ≥0∞) :
    HigherDimLFPP.logCov μ ν (c • α) (c • β) = c.toReal * HigherDimLFPP.logCov μ ν α β := by
  unfold HigherDimLFPP.logCov
  simp only [Measure.prod_smul_right, integral_smul_measure, smul_eq_mul]
  ring

theorem logCov_zero_right : HigherDimLFPP.logCov μ ν (0 : Measure (Rd d)) 0 = 0 := by
  simp only [HigherDimLFPP.logCov, Measure.prod_zero, integral_zero_measure, sub_self, add_zero]

end LogCovAlgebra

/-! ### Continuity of `logCov` of sphere laws in the scales -/

theorem abs_sub_add_sub_le (a b c e : ℝ) : |a - b + c - e| ≤ |a| + |b| + |c| + |e| := by
  rw [abs_le]
  constructor <;> linarith [neg_abs_le a, le_abs_self a, neg_abs_le b, le_abs_self b,
    neg_abs_le c, le_abs_self c, neg_abs_le e, le_abs_self e]

theorem tendsto_mul_sqrt_mul_div (C R : ℝ) {u v : ℕ → ℝ} {v₀ : ℝ}
    (hu : Tendsto u atTop (𝓝 0)) (hv : Tendsto v atTop (𝓝 v₀)) :
    Tendsto (fun n => C * Real.sqrt (u n * v n) / R) atTop (𝓝 0) := by
  have h1 : Tendsto (fun n => u n * v n) atTop (𝓝 0) := by
    have := hu.mul hv
    rwa [zero_mul] at this
  have h2 := ((Real.continuous_sqrt.tendsto 0).comp h1).const_mul C
  rw [Real.sqrt_zero, mul_zero] at h2
  have h3 := h2.div_const R
  rwa [zero_div] at h3

theorem tendsto_dist_triple {z z' : Rd d} {r r' : ℝ} {s s' : ℕ → ℝ} {ε ε' : ℝ}
    (hs : Tendsto s atTop (𝓝 ε)) (hs' : Tendsto s' atTop (𝓝 ε')) :
    Tendsto (fun n => ‖z - z'‖ + |r - r'| + |s n - s' n|) atTop
      (𝓝 (‖z - z'‖ + |r - r'| + |ε - ε'|)) :=
  tendsto_const_nhds.add ((continuous_abs.tendsto _).comp (hs.sub hs'))

theorem tendsto_dist_triple_zero {z : Rd d} {r : ℝ} {s : ℕ → ℝ} {ε : ℝ}
    (hs : Tendsto s atTop (𝓝 ε)) :
    Tendsto (fun n => ‖z - z‖ + |r - r| + |s n - ε|) atTop (𝓝 0) := by
  have := tendsto_dist_triple (z := z) (z' := z) (r := r) (r' := r) hs
    (tendsto_const_nhds (x := ε))
  simpa only [sub_self, norm_zero, abs_zero, add_zero] using this

/-- **`logCov` of sphere laws is continuous in the four scales** (`d ≥ 2`, positive radii). -/
theorem tendsto_logCov_sphLaw (hd : 2 ≤ d) {r₁ r₂ r₃ r₄ : ℝ} (h₁ : 0 < r₁) (h₂ : 0 < r₂)
    (h₃ : 0 < r₃) (h₄ : 0 < r₄) (z₁ z₂ z₃ z₄ : Rd d) {s₁ s₂ s₃ s₄ : ℕ → ℝ} {ε₁ ε₂ ε₃ ε₄ : ℝ}
    (t₁ : Tendsto s₁ atTop (𝓝 ε₁)) (t₂ : Tendsto s₂ atTop (𝓝 ε₂))
    (t₃ : Tendsto s₃ atTop (𝓝 ε₃)) (t₄ : Tendsto s₄ atTop (𝓝 ε₄)) :
    Tendsto (fun n => HigherDimLFPP.logCov (sphLaw r₁ z₁ (s₁ n)) (sphLaw r₂ z₂ (s₂ n))
        (sphLaw r₃ z₃ (s₃ n)) (sphLaw r₄ z₄ (s₄ n))) atTop
      (𝓝 (HigherDimLFPP.logCov (sphLaw r₁ z₁ ε₁) (sphLaw r₂ z₂ ε₂) (sphLaw r₃ z₃ ε₃)
        (sphLaw r₄ z₄ ε₄))) := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_logCov_sphLaw_le hd
  rw [tendsto_iff_norm_sub_tendsto_zero]
  set b : ℕ → ℝ := fun n =>
    C * Real.sqrt ((‖z₁ - z₁‖ + |r₁ - r₁| + |s₁ n - ε₁|) *
        (‖z₃ - z₄‖ + |r₃ - r₄| + |s₃ n - s₄ n|)) / min r₁ r₁ +
      C * Real.sqrt ((‖z₂ - z₂‖ + |r₂ - r₂| + |s₂ n - ε₂|) *
        (‖z₃ - z₄‖ + |r₃ - r₄| + |s₃ n - s₄ n|)) / min r₂ r₂ +
      C * Real.sqrt ((‖z₁ - z₂‖ + |r₁ - r₂| + |ε₁ - ε₂|) *
        (‖z₃ - z₃‖ + |r₃ - r₃| + |s₃ n - ε₃|)) / min r₁ r₂ +
      C * Real.sqrt ((‖z₁ - z₂‖ + |r₁ - r₂| + |ε₁ - ε₂|) *
        (‖z₄ - z₄‖ + |r₄ - r₄| + |s₄ n - ε₄|)) / min r₁ r₂ with hb
  have hb0 : Tendsto b atTop (𝓝 0) := by
    have e1 := tendsto_mul_sqrt_mul_div C (min r₁ r₁) (tendsto_dist_triple_zero (z := z₁)
      (r := r₁) t₁) (tendsto_dist_triple (z := z₃) (z' := z₄) (r := r₃) (r' := r₄) t₃ t₄)
    have e2 := tendsto_mul_sqrt_mul_div C (min r₂ r₂) (tendsto_dist_triple_zero (z := z₂)
      (r := r₂) t₂) (tendsto_dist_triple (z := z₃) (z' := z₄) (r := r₃) (r' := r₄) t₃ t₄)
    have e3 := tendsto_mul_sqrt_mul_div C (min r₁ r₂)
      (tendsto_dist_triple_zero (z := z₃) (r := r₃) t₃)
      (tendsto_const_nhds (x := ‖z₁ - z₂‖ + |r₁ - r₂| + |ε₁ - ε₂|))
    have e4 := tendsto_mul_sqrt_mul_div C (min r₁ r₂)
      (tendsto_dist_triple_zero (z := z₄) (r := r₄) t₄)
      (tendsto_const_nhds (x := ‖z₁ - z₂‖ + |r₁ - r₂| + |ε₁ - ε₂|))
    have := ((e1.add e2).add e3).add e4
    simp only [add_zero] at this
    refine this.congr fun n => ?_
    simp only [hb]
    rw [mul_comm (‖z₁ - z₂‖ + |r₁ - r₂| + |ε₁ - ε₂|), mul_comm (‖z₁ - z₂‖ + |r₁ - r₂| + |ε₁ - ε₂|)]
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hb0
  rw [Real.norm_eq_abs, logCov_sub_logCov]
  have k1 := hC r₁ r₁ r₃ r₄ h₁ h₁ h₃ h₄ z₁ z₁ z₃ z₄ (s₁ n) ε₁ (s₃ n) (s₄ n)
  have k2 := hC r₂ r₂ r₃ r₄ h₂ h₂ h₃ h₄ z₂ z₂ z₃ z₄ (s₂ n) ε₂ (s₃ n) (s₄ n)
  have k3 := hC r₁ r₂ r₃ r₃ h₁ h₂ h₃ h₃ z₁ z₂ z₃ z₃ ε₁ ε₂ (s₃ n) ε₃
  have k4 := hC r₁ r₂ r₄ r₄ h₁ h₂ h₄ h₄ z₁ z₂ z₄ z₄ ε₁ ε₂ (s₄ n) ε₄
  calc |HigherDimLFPP.logCov (sphLaw r₁ z₁ (s₁ n)) (sphLaw r₁ z₁ ε₁) (sphLaw r₃ z₃ (s₃ n))
          (sphLaw r₄ z₄ (s₄ n)) -
        HigherDimLFPP.logCov (sphLaw r₂ z₂ (s₂ n)) (sphLaw r₂ z₂ ε₂) (sphLaw r₃ z₃ (s₃ n))
          (sphLaw r₄ z₄ (s₄ n)) +
        HigherDimLFPP.logCov (sphLaw r₁ z₁ ε₁) (sphLaw r₂ z₂ ε₂) (sphLaw r₃ z₃ (s₃ n))
          (sphLaw r₃ z₃ ε₃) -
        HigherDimLFPP.logCov (sphLaw r₁ z₁ ε₁) (sphLaw r₂ z₂ ε₂) (sphLaw r₄ z₄ (s₄ n))
          (sphLaw r₄ z₄ ε₄)|
      ≤ |HigherDimLFPP.logCov (sphLaw r₁ z₁ (s₁ n)) (sphLaw r₁ z₁ ε₁) (sphLaw r₃ z₃ (s₃ n))
          (sphLaw r₄ z₄ (s₄ n))| +
        |HigherDimLFPP.logCov (sphLaw r₂ z₂ (s₂ n)) (sphLaw r₂ z₂ ε₂) (sphLaw r₃ z₃ (s₃ n))
          (sphLaw r₄ z₄ (s₄ n))| +
        |HigherDimLFPP.logCov (sphLaw r₁ z₁ ε₁) (sphLaw r₂ z₂ ε₂) (sphLaw r₃ z₃ (s₃ n))
          (sphLaw r₃ z₃ ε₃)| +
        |HigherDimLFPP.logCov (sphLaw r₁ z₁ ε₁) (sphLaw r₂ z₂ ε₂) (sphLaw r₄ z₄ (s₄ n))
          (sphLaw r₄ z₄ ε₄)| := by
        exact abs_sub_add_sub_le _ _ _ _
    _ ≤ b n := by
        simp only [hb]
        exact add_le_add (add_le_add (add_le_add k1 k2) k3) k4

/-! ### The process -/

/-- `⟨g, σ_{r,z} * ψ_ε⟩` for `ε ≠ 0`, and the sphere average `g_r(z)` for `ε = 0`. -/
def sphProc (g : DistRd d) (ε r : ℝ) (z : Rd d) : ℝ :=
  if ε = 0 then sphereAvg g r z else g (sphMol ε z r)

theorem sphProc_zero (g : DistRd d) (r : ℝ) (z : Rd d) : sphProc g 0 r z = sphereAvg g r z :=
  ite_eq_left_iff.2 fun h => absurd rfl h

theorem sphProc_of_ne (g : DistRd d) {ε : ℝ} (hε : ε ≠ 0) (r : ℝ) (z : Rd d) :
    sphProc g ε r z = g (sphMol ε z r) :=
  ite_eq_right_iff.2 fun h => absurd h hε

theorem measurable_sphProc (ε r : ℝ) (z : Rd d) :
    Measurable fun g : DistRd d => sphProc g ε r z := by
  by_cases hε : ε = 0
  · subst hε
    simp only [sphProc_zero]
    exact measurable_sphereAvg_left r z
  · simp only [sphProc_of_ne _ hε]
    exact measurable_distOn_apply _

/-- The scale used at step `n` to approximate `sphProc g ε r z`. -/
def approxScale (n : ℕ) (ε : ℝ) : ℝ := if ε = 0 then ((2 : ℝ) ^ n)⁻¹ else ε

theorem approxScale_zero (n : ℕ) : approxScale n 0 = ((2 : ℝ) ^ n)⁻¹ :=
  ite_eq_left_iff.2 fun h => absurd rfl h

theorem approxScale_of_ne (n : ℕ) {ε : ℝ} (hε : ε ≠ 0) : approxScale n ε = ε :=
  ite_eq_right_iff.2 fun h => absurd h hε

theorem approxScale_pos {ε : ℝ} (hε : 0 ≤ ε) (n : ℕ) : 0 < approxScale n ε := by
  unfold approxScale
  split_ifs with h
  · positivity
  · exact lt_of_le_of_ne hε (Ne.symm h)

theorem tendsto_approxScale (ε : ℝ) : Tendsto (fun n => approxScale n ε) atTop (𝓝 ε) := by
  unfold approxScale
  split_ifs with h
  · subst h
    simp_rw [← inv_pow]
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  · exact tendsto_const_nhds

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistRd d}

/-- **`sphProc` of an LGF is the a.s. limit of its approximating pairings** (`d ≥ 2`,
`ε ≥ 0`, `r > 0`). -/
theorem IsWholeSpaceLGF.ae_tendsto_sphProc (hd : 2 ≤ d) (hh : IsWholeSpaceLGF h P) {ε r : ℝ}
    (hε : 0 ≤ ε) (hr : 0 < r) (z : Rd d) :
    ∀ᵐ ω ∂P, Tendsto (fun n => h ω (sphMol (approxScale n ε) z r)) atTop
      (𝓝 (sphProc (h ω) ε r z)) := by
  by_cases h0 : ε = 0
  · subst h0
    filter_upwards [hh.ae_exists_tendsto_sphereAvgSeq hd hr z] with ω hω
    rw [sphProc_zero]
    refine (tendsto_sphereAvgSeq_sphereAvg hω).congr fun n => ?_
    rw [sphereAvgSeq_eq_apply_sphMol, approxScale_zero]
  · refine ae_of_all _ fun ω => ?_
    rw [sphProc_of_ne _ h0]
    refine tendsto_const_nhds.congr fun n => ?_
    rw [approxScale_of_ne n h0]

end HigherDimLQGMetric
