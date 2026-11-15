/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WholeField9Prob
import InteractingSLE.GFF.LocalSets.GermVersion

/-!
# The conditional means form a random distribution (any σ-algebra with Gaussian conditional laws)

Packet PROVE-WHOLEFIELD9 (follow-up note C.3/C.5: "The same Fourier argument as at birth supplies the distribution
version of `M_τ` (equivalently it is the distribution-valued conditional mean)"; specification Aux. lemma 16, p. 91:
"These random linear functionals have simultaneous distribution-valued versions").

PROVE-LS-C's construction for the germ σ-algebra (`LocalSets.exists_germVersion`, `LocalSets.ae_mem_rangeSet_germMean`)
uses only two properties of the conditional means `M(ψ) = E[h(ψ) | 𝒜]`: linearity, and the **median bound**
`P(G) ≤ 2 P(G ∩ {|M(ψ)| ≤ |h(ψ)|})`, `G ∈ 𝒜`, which follows from Gaussian conditional characteristic functions. Here the
same argument is run for an arbitrary σ-algebra `𝒜` (the stopped driving σ-algebra), with the median bound of
`WholeField9Prob`:

* `ae_mem_rangeSet_condMean`: almost surely the conditional means are additive, consistent and of finite order on each
  compact `K_n` (LQGMetric's `rangeSet`);
* **`exists_condMean_version`**: there is an `𝒜`-measurable random distribution `h₁` with `h₁(ψ) = E[h(ψ) | 𝒜]` almost
  surely for every test `ψ` (LQGMetric `exists_version`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace Metric Complex
open scoped RealInnerProductSpace ENNReal

namespace InteractingSLE

namespace WholeField

open QuantumZipper QuantumZipper.K3 QuantumZipper.Thm11Asm LQGMetric LQGMetric.MarkovZB LocalSets

section Version

variable {Ω : Type*} {𝒜 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens}

/-- **Admissibility of the conditional means**, for any σ-algebra `𝒜` with Gaussian conditional characteristic
functions of every pairing. -/
theorem ae_mem_rangeSet_condMean (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P) (h𝒜 : 𝒜 ≤ mΩ)
    {q : TestOn upperHalfPlaneOpens → Ω → ℝ}
    (hcf : ∀ (ψ : TestOn upperHalfPlaneOpens) (t : ℝ),
      P[fun ω => cexp (I * ((t * h ω ψ : ℝ) : ℂ)) | 𝒜] =ᵐ[P]
        fun ω => cexp (I * ((t * (P[fun ω => h ω ψ | 𝒜]) ω : ℝ) : ℂ)) *
          ((Real.exp (-(1 / 2) * (t ^ 2 * q ψ ω)) : ℝ) : ℂ)) :
    ∀ᵐ ω ∂P, (fun c => (P[fun ω => h ω (comb upperHalfPlaneOpens c) | 𝒜]) ω) ∈ rangeSet upperHalfPlaneOpens := by
  have hhm := hh.measurable
  have hint : ∀ ψ, Integrable (fun ω => h ω ψ) P := fun ψ =>
    (hh.process.gaussian.hasGaussianLaw_eval ψ).memLp_two.integrable one_le_two
  set M : TestOn upperHalfPlaneOpens → Ω → ℝ := fun ψ => P[fun ω => h ω ψ | 𝒜] with hMdef
  have hMm : ∀ ψ, Measurable[𝒜] (M ψ) := fun ψ => stronglyMeasurable_condExp.measurable
  -- additivity
  have hadd : ∀ᵐ ω ∂P, ∀ c c' : CoordJ, M (comb upperHalfPlaneOpens (c + c')) ω =
      M (comb upperHalfPlaneOpens c) ω + M (comb upperHalfPlaneOpens c') ω := by
    refine ae_all_iff.2 fun c => ae_all_iff.2 fun c' => ?_
    have e : (fun ω => h ω (comb upperHalfPlaneOpens (c + c'))) =
        (fun ω => h ω (comb upperHalfPlaneOpens c)) + fun ω => h ω (comb upperHalfPlaneOpens c') := by
      funext ω; simp [map_add]
    have hc := condExp_add (m := 𝒜) (hint (comb upperHalfPlaneOpens c)) (hint (comb upperHalfPlaneOpens c'))
    filter_upwards [hc] with ω h4
    simp only [hMdef]
    rw [e, h4, Pi.add_apply]
  -- the bounds
  have hbd : ∀ n : ℕ, ∀ᵐ ω ∂P, ∃ k : ℕ, ∀ c : {c : CoordJ // tsupport (comb upperHalfPlaneOpens c :
      ℂ → ℝ) ⊆ exhaustK upperHalfPlaneOpens n},
        |M (comb upperHalfPlaneOpens c.1) ω| ≤ k * coordSem n k c.1 c.2 := by
    intro n
    have hex := ae_exists_condExp_gt_half (P := P) h𝒜 (measurableSet_boundSet hhm n)
      (boundSet_mono h n) (iUnion_boundSet h n)
    have hk : ∀ k : ℕ, ∀ c : {c : CoordJ // tsupport (comb upperHalfPlaneOpens c : ℂ → ℝ) ⊆
        exhaustK upperHalfPlaneOpens n}, ∀ᵐ ω ∂P,
          1 / 2 < (P⟦boundSet h n k|𝒜⟧) ω →
            |M (comb upperHalfPlaneOpens c.1) ω| ≤ k * coordSem n k c.1 c.2 := by
      intro k c
      set ψ := comb upperHalfPlaneOpens c.1
      set G : Set Ω := {ω | 1 / 2 < (P⟦boundSet h n k|𝒜⟧) ω} ∩
        {ω | (k : ℝ) * coordSem n k c.1 c.2 < |M ψ ω|}
      have hG : MeasurableSet[𝒜] G :=
        (measurableSet_lt measurable_const stronglyMeasurable_condExp.measurable).inter
          (measurableSet_lt measurable_const (continuous_abs.measurable.comp (hMm ψ)))
      have hD : MeasurableSet {ω | |M ψ ω| ≤ |h ω ψ|} :=
        measurableSet_le (continuous_abs.measurable.comp ((hMm ψ).mono h𝒜 le_rfl))
          (continuous_abs.measurable.comp ((measurable_distOn_apply ψ).comp hhm))
      have h0 := measure_eq_zero_of_condExp_gt_half h𝒜 hG (measurableSet_boundSet hhm n k) hD
        (Set.eq_empty_of_forall_notMem fun ω ⟨⟨⟨_, h2⟩, h3⟩, h4⟩ => by
          have := h3 c
          simp only [mem_ofPred_eq] at h2 h4
          linarith)
        (measure_le_two_mul_abs_le_of_condCharFun h𝒜 ((measurable_distOn_apply ψ).comp hhm) (hMm ψ)
          (hcf ψ) hG) (fun ω hω => hω.1)
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with ω hω h1
      simp only [G, mem_inter_iff, mem_ofPred_eq, not_and, not_lt] at hω
      exact hω h1
    filter_upwards [hex, ae_all_iff.2 fun k => ae_all_iff.2 (hk k)] with ω ⟨k, hk1⟩ h2
    exact ⟨k, fun c => h2 k c hk1⟩
  filter_upwards [hadd, ae_all_iff.2 hbd] with ω h1 h2
  refine ⟨⟨h1, fun c c' e => congrArg (fun ψ => M ψ ω) e⟩, mem_iInter.2 fun n => ?_⟩
  obtain ⟨k, hk⟩ := h2 n
  exact mem_iUnion.2 ⟨k, mem_iUnion.2 ⟨k, fun c hc => hk ⟨c, hc⟩⟩⟩

/-- **The conditional mean is a random distribution**: for any σ-algebra `𝒜 ≤ mΩ` with Gaussian conditional
characteristic functions of every pairing of a zero-boundary GFF `h`, there is an `𝒜`-measurable random distribution
`h₁` with `h₁(ψ) = E[h(ψ) | 𝒜]` almost surely for every test `ψ`. -/
theorem exists_condMean_version (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P) (h𝒜 : 𝒜 ≤ mΩ)
    {q : TestOn upperHalfPlaneOpens → Ω → ℝ}
    (hcf : ∀ (ψ : TestOn upperHalfPlaneOpens) (t : ℝ),
      P[fun ω => cexp (I * ((t * h ω ψ : ℝ) : ℂ)) | 𝒜] =ᵐ[P]
        fun ω => cexp (I * ((t * (P[fun ω => h ω ψ | 𝒜]) ω : ℝ) : ℂ)) *
          ((Real.exp (-(1 / 2) * (t ^ 2 * q ψ ω)) : ℝ) : ℂ)) :
    ∃ h₁ : Ω → DistOn upperHalfPlaneOpens, Measurable[𝒜] h₁ ∧
      ∀ ψ, (fun ω => h₁ ω ψ) =ᵐ[P] P[fun ω => h ω ψ | 𝒜] := by
  set M : TestOn upperHalfPlaneOpens → Ω → ℝ := fun ψ => P[fun ω => h ω ψ | 𝒜] with hMdef
  have hMm : ∀ ψ, Measurable[𝒜] (M ψ) := fun ψ => stronglyMeasurable_condExp.measurable
  have hadm := ae_mem_rangeSet_condMean hh h𝒜 hcf
  have hS : MeasurableSet[𝒜]
      {ω | (fun c => M (comb upperHalfPlaneOpens c) ω) ∈ rangeSet upperHalfPlaneOpens} :=
    (@Measurable.of_eval Ω CoordJ (fun _ => ℝ) 𝒜 _ _
      fun c => hMm (comb upperHalfPlaneOpens c)) (measurableSet_rangeSet _)
  have hadm' : ∀ᵐ ω ∂(P.trim h𝒜),
      (fun c => M (comb upperHalfPlaneOpens c) ω) ∈ rangeSet upperHalfPlaneOpens := by
    rw [ae_iff]
    rw [show {a | ¬ (fun c => M (comb upperHalfPlaneOpens c) a) ∈ rangeSet upperHalfPlaneOpens} =
      {ω | (fun c => M (comb upperHalfPlaneOpens c) ω) ∈ rangeSet upperHalfPlaneOpens}ᶜ from rfl,
      trim_measurableSet_eq h𝒜 hS.compl]
    exact ae_iff.1 hadm
  -- continuity in probability
  have hcont : ∀ (φ : TestOn upperHalfPlaneOpens) (ψ : ℕ → TestOn upperHalfPlaneOpens),
      Tendsto ψ atTop (𝓝 φ) → TendstoInMeasure (P.trim h𝒜) (fun k => M (ψ k)) atTop (M φ) := by
    intro φ ψ hψ
    have hP : TendstoInMeasure P (fun k => M (ψ k)) atTop (M φ) := by
      refine tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num)
        (fun k => (hMm (ψ k)).mono h𝒜 le_rfl |>.aestronglyMeasurable)
        ((hMm φ).mono h𝒜 le_rfl |>.aestronglyMeasurable) ?_
      have hd : Tendsto (fun k => ψ k - φ) atTop (𝓝 0) := by
        simpa using hψ.sub_const φ
      have hv := tendsto_zeroGFFTestCov_of_tendsto hh hd
      have hbd : ∀ k, eLpNorm (M (ψ k) - M φ) 2 P ≤
          ENNReal.ofReal (Real.sqrt (zeroGFFTestCov H ⇑(ψ k - φ) ⇑(ψ k - φ))) := by
        intro k
        have hint : ∀ χ, Integrable (fun ω => h ω χ) P := fun χ =>
          (hh.process.gaussian.hasGaussianLaw_eval χ).memLp_two.integrable one_le_two
        have he : (M (ψ k) - M φ) =ᵐ[P] P[fun ω => h ω (ψ k - φ) | 𝒜] := by
          have e : (fun ω => h ω (ψ k - φ)) = (fun ω => h ω (ψ k)) - fun ω => h ω φ := by
            funext ω; simp [map_sub]
          rw [e]
          exact (condExp_sub (m := 𝒜) (hint (ψ k)) (hint φ)).symm
        rw [eLpNorm_congr_ae he]
        refine (eLpNorm_condExp_le_eLpNorm _ one_le_two).trans (le_of_eq ?_)
        rw [(hh.process.gaussian.hasGaussianLaw_eval (ψ k - φ)).memLp_two.eLpNorm_eq_integral_rpow_norm
          (by norm_num) (by norm_num)]
        congr 1
        have : ∫ ω, ‖h ω (ψ k - φ)‖ ^ (2 : ℝ≥0∞).toReal ∂P =
            zeroGFFTestCov H ⇑(ψ k - φ) ⇑(ψ k - φ) := by
          rw [← integral_sq_field hh (ψ k - φ)]
          refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
          simp only [Real.norm_eq_abs, ENNReal.toReal_ofNat]
          rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
        rw [this, Real.sqrt_eq_rpow, ENNReal.toReal_ofNat, one_div]
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun _ => zero_le) hbd
      have : Tendsto (fun k => ENNReal.ofReal (Real.sqrt (zeroGFFTestCov H ⇑(ψ k - φ) ⇑(ψ k - φ))))
          atTop (𝓝 (ENNReal.ofReal (Real.sqrt 0))) :=
        (ENNReal.continuous_ofReal.tendsto _).comp ((Real.continuous_sqrt.tendsto _).comp hv)
      simpa using this
    intro ε hε
    have hmeas : ∀ k, MeasurableSet[𝒜] {ω | ε ≤ edist (M (ψ k) ω) (M φ ω)} := fun k =>
      measurableSet_edist_ge (hMm (ψ k)) (hMm φ) ε
    simp_rw [trim_measurableSet_eq h𝒜 (hmeas _)]
    exact hP ε hε
  obtain ⟨h₁, hh₁, hh₁e⟩ := @LQGMetric.exists_version upperHalfPlaneOpens Ω 𝒜 (P.trim h𝒜) _ M hMm hadm' hcont
  exact ⟨h₁, hh₁, fun ψ => ae_eq_of_ae_eq_trim (hh₁e ψ)⟩

end Version

end WholeField

end InteractingSLE
