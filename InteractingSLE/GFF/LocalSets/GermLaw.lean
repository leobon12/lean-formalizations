import InteractingSLE.GFF.LocalSets.GermApprox

/-!
# The conditional law of the field given the germ σ-algebra (Lemma 3.6, (i) ⇒ (iii))

Specification §3.2, p. 53–54, (3.4)–(3.5) and the display after (3.5): for a set `A` satisfying
Lemma 3.6 (i), conditionally on the germ σ-algebra `𝒜`, `h(φ)` is Gaussian with mean
`E[h(φ) | 𝒜]` and variance `σ²_{ℍ∖A}(φ)`:

* `exists_germLimit` : the cover means `Q_j h(φ) = E[h(φ) | 𝒢_j]` (`coverProj_ae_eq_condExp`)
  converge in `L²` (decreasing `𝒢_j`) to a limit that is `𝒜_δ`-measurable for every `δ` (germ
  lemma), hence has an `𝒜`-measurable version `M` (QuantumZipper `GermZeroOne.exists_iInf_version`);
* `exists_condExp_germSigma` : `E[h(φ) | 𝒜] = M` and `E[e^{i h(φ)} | 𝒜] = e^{iM} e^{−σ²_{ℍ∖A}(φ)/2}`:
  every event of `𝒜` is an event of each `𝒢_j` up to a null set (`germSigmaAt_le_aeSigma`), the
  conditional law given `𝒢_j` is known (`setIntegral_coverSigma`), and `j → ∞` along an almost
  surely convergent subsequence, with `σ²_{W_j(A)}(φ) → σ²_{ℍ∖A}(φ)` (monotone Dirichlet-space
  approximation, `tendsto_zeroGFFTestCov_iUnion`) and dominated convergence.

The source uses reverse martingale convergence of conditional characteristic functions; here the
`L²` limit of the conditional means suffices, because the conditional law given each `𝒢_j` is
explicit.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace Metric
open scoped RealInnerProductSpace ENNReal

namespace InteractingSLE
namespace LocalSets

open QuantumZipper QuantumZipper.K3 QuantumZipper.Thm11Asm LQGMetric LQGMetric.MarkovZB

section L2Tools

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
/-- `L²` convergence gives an almost surely convergent subsequence. -/
theorem exists_seq_tendsto_ae_of_tendsto_integral_sq {f : Ω → ℝ} {F : ℕ → Ω → ℝ}
    (hF : ∀ n, AEStronglyMeasurable (F n) P) (hf : AEStronglyMeasurable f P)
    (hint : ∀ n, Integrable (fun ω => (f ω - F n ω) ^ 2) P)
    (hlim : Tendsto (fun n => ∫ ω, (f ω - F n ω) ^ 2 ∂P) atTop (𝓝 0)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ ω ∂P, Tendsto (fun i => F (ns i) ω) atTop (𝓝 (f ω)) := by
  have hmem : ∀ n, MemLp (F n - f) 2 P := fun n => by
    refine (memLp_two_iff_integrable_sq ((hF n).sub hf)).2 ((hint n).congr ?_)
    exact Eventually.of_forall fun ω => by simp only [Pi.sub_apply]; ring
  have hnorm : ∀ n, eLpNorm (F n - f) 2 P =
      ENNReal.ofReal ((∫ ω, (f ω - F n ω) ^ 2 ∂P) ^ (2 : ℝ)⁻¹) := fun n => by
    rw [(hmem n).eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
    congr 2
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    simp only [Pi.sub_apply, Real.norm_eq_abs, ENNReal.toReal_ofNat]
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
    ring
  have hmeas : TendstoInMeasure P F atTop f := by
    refine tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num) hF hf ?_
    simp_rw [hnorm]
    have h0 : ENNReal.ofReal ((0 : ℝ) ^ (2 : ℝ)⁻¹) = 0 := by simp
    rw [← h0]
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      ((Real.continuousAt_rpow_const _ _ (Or.inr (by norm_num))).tendsto.comp hlim)
  exact hmeas.exists_seq_tendsto_ae

/-- `L²` convergence gives convergence of set integrals. -/
theorem tendsto_setIntegral_of_tendsto_integral_sq {f : Ω → ℝ} {F : ℕ → Ω → ℝ}
    (hf : Integrable f P) (hF : ∀ n, Integrable (F n) P)
    (hmem : ∀ n, MemLp (fun ω => F n ω - f ω) 2 P)
    (hlim : Tendsto (fun n => ∫ ω, (F n ω - f ω) ^ 2 ∂P) atTop (𝓝 0)) (G : Set Ω) :
    Tendsto (fun n => ∫ ω in G, F n ω ∂P) atTop (𝓝 (∫ ω in G, f ω ∂P)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_)
    (((Real.continuous_sqrt.tendsto 0).comp hlim).trans (by simp))
  rw [← integral_sub (hF n).integrableOn hf.integrableOn]
  refine (norm_integral_le_integral_norm _).trans ?_
  refine (setIntegral_mono_set ((hF n).sub hf).norm.integrableOn
    (Eventually.of_forall fun _ => norm_nonneg _) (Eventually.of_forall (subset_univ G))).trans ?_
  rw [setIntegral_univ]
  have h := sq_integral_abs_le (P := P) (hmem n)
  simp only [Real.norm_eq_abs, Pi.sub_apply, Function.comp_apply]
  exact Real.le_sqrt_of_sq_le h

end L2Tools

section Limit

variable {Ω : Type u} {ℳ : MeasurableSpace Ω} {𝒮 : Set ℂ → MeasurableSpace Ω}
  [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {A : Ω → Set ℂ} {h : Ω → DistOn upperHalfPlaneOpens}

theorem integrable_coverProj (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hA : Measurable[mΩ, hittingSigma] A) (j : ℕ) (φ : TestOn upperHalfPlaneOpens) :
    Integrable (fun ω => coverProj j A h ω φ) P := by
  have hhi : Integrable (fun ω => h ω φ) P :=
    (hh.process.gaussian.hasGaussianLaw_eval φ).memLp_two.integrable one_le_two
  have hU : (univ : Set Ω) = ⋃ T ∈ (coverIdx j).powerset, coverAtom j A T := by
    simpa using eq_biUnion_coverAtom (A := A) j (univ : Set Ω)
  rw [← integrableOn_univ, hU]
  refine integrableOn_finset_iUnion.2 fun T _ => ?_
  have hXi : Integrable (fun ω => coverMarkov.{u} T (h ω) φ) P :=
    ((isMarkovDecomposition_coverMarkov hh T).isZBGFFExtOn.gaussian.hasGaussianLaw_eval
      φ).memLp_two.integrable one_le_two
  refine (hhi.sub hXi).integrableOn.congr_fun (fun ω hω => ?_) (measurableSet_coverAtom hA j T)
  simp only [coverProj_of_mem_coverAtom hω, markovCompl, sub_apply, Pi.sub_apply]

/-- `Q_j h(φ)` is the conditional mean of `h(φ)` given `𝒢_j`. -/
theorem coverProj_ae_eq_condExpM (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hA : Measurable[mΩ, hittingSigma] A) (hmk : IsCoverMarking A h P ℳ 𝒮) (j : ℕ)
    (φ : TestOn upperHalfPlaneOpens) :
    (fun ω => coverProj j A h ω φ) =ᵐ[P] P[fun ω => h ω φ | coverSigmaM ℳ j A h] := by
  have hhm := hh.measurable
  refine ae_eq_condExp_of_forall_setIntegral_eq (coverSigmaM_le hmk.le hA hhm j)
    ((hh.process.gaussian.hasGaussianLaw_eval φ).memLp_two.integrable one_le_two)
    (fun s _ _ => (integrable_coverProj hh hA j φ).integrableOn)
    (fun s hs _ => ((setIntegral_coverSigmaM hh hA hmk j hs φ).2).symm) ?_
  have hm : Measurable[coverSigmaM ℳ j A h] fun ω => coverProj j A h ω φ :=
    (measurable_distOn_apply φ).comp ((comap_measurable (coverProj j A h)).mono
      (le_sup_of_le_right (le_iSup₂_of_le (f := fun (k : ℕ) (_ : j ≤ k) =>
        MeasurableSpace.comap (coverProj k A h) inferInstance) j le_rfl le_rfl)) le_rfl)
  exact hm.stronglyMeasurable.aestronglyMeasurable

/-- **The limit of the cover means is `𝒜`-measurable**: there is a germ-measurable `M` with
`Q_j h(φ) → M` in `L²`. -/
theorem exists_germLimitM (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hA : Measurable[mΩ, hittingSigma] A) (hmk : IsCoverMarking A h P ℳ 𝒮)
    (φ : TestOn upperHalfPlaneOpens) :
    ∃ M : Ω → ℝ, Measurable[germSigma A h] M ∧ MemLp M 2 P ∧
      Tendsto (fun j => ∫ ω, (coverProj j A h ω φ - M ω) ^ 2 ∂P) atTop (𝓝 0) := by
  have hhm := hh.measurable
  have hf : MemLp (fun ω => h ω φ) 2 P := (hh.process.gaussian.hasGaussianLaw_eval φ).memLp_two
  obtain ⟨y, hy, hylim⟩ := exists_tendsto_condExp_antitone (coverSigmaM_le hmk.le hA hhm)
    (coverSigmaM_anti ℳ A h) hf
  have hcond := fun j => coverProj_ae_eq_condExpM hh hA hmk j φ
  -- `Q_j h(φ) → y` in `L²`
  have hQlim : Tendsto (fun j => ∫ ω, (coverProj j A h ω φ - y ω) ^ 2 ∂P) atTop (𝓝 0) := by
    refine hylim.congr fun j => integral_congr_ae ?_
    filter_upwards [hcond j] with ω hω
    rw [hω]
  have hQmem : ∀ j, MemLp (fun ω => coverProj j A h ω φ - y ω) 2 P := fun j =>
    ((hf.condExp (m := coverSigmaM ℳ j A h) one_le_two).sub hy).ae_eq
      (by filter_upwards [hcond j] with ω hω; simp only [Pi.sub_apply, hω])
  -- `y` is `𝒜_n`-measurable up to null sets for every `n`
  have hstep : ∀ n : ℕ, ∃ g : Ω → ℝ, StronglyMeasurable[germSigmaAt A h (1 / ((n : ℝ) + 1))] g ∧
      y =ᵐ[P] g := by
    intro n
    set δ : ℝ := 1 / ((n : ℝ) + 1)
    have hδ : 0 < δ := by positivity
    have hδ1 : δ ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    set J := ⌈6 / δ⌉₊
    have key := fun k : ℕ => exists_measurable_coverProj_germSigmaAt (P := P) (A := A) hh hδ hδ1
      (j := J + k) (Nat.le_add_right J k) φ
    choose Z hZm hZe using key
    have hint : ∀ k, Integrable (fun ω => (y ω - Z k ω) ^ 2) P := fun k => by
      refine ((hQmem (J + k)).integrable_sq).congr ?_
      filter_upwards [hZe k] with ω hω
      rw [← hω]
      ring
    have hlim : Tendsto (fun k => ∫ ω, (y ω - Z k ω) ^ 2 ∂P) atTop (𝓝 0) := by
      have := hQlim.comp (tendsto_add_atTop_iff_nat J |>.2 tendsto_id)
      refine this.congr fun k => integral_congr_ae ?_
      filter_upwards [hZe k] with ω hω
      show (coverProj (id (k + J)) A h ω φ - y ω) ^ 2 = (y ω - Z k ω) ^ 2
      rw [id, add_comm, hω]
      ring
    obtain ⟨g, hg, hge⟩ := exists_measurable_ae_eq_of_tendsto_integral_sq (P := P) (f := y)
      (F := Z) hZm (germSigmaAt_le' hA hhm hδ) hy.aestronglyMeasurable hint hlim
    exact ⟨g, hg.stronglyMeasurable, hge⟩
  have hanti : Antitone fun n : ℕ => germSigmaAt A h (1 / ((n : ℝ) + 1)) := by
    intro a b hab
    refine germSigmaAt_mono (by positivity) ?_
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hab 1)
  obtain ⟨M, hM, hyM⟩ := QuantumZipper.GermZeroOne.exists_iInf_version (P := P) hanti hstep
  refine ⟨M, hM, hy.ae_eq hyM, hQlim.congr fun j => integral_congr_ae ?_⟩
  filter_upwards [hyM] with ω hω
  rw [hω]

omit ℳ 𝒮 in
theorem coverProj_ae_eq_condExp (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hA : Measurable[mΩ, hittingSigma] A) (hloc : IsAvoidanceLocal A h P) (j : ℕ)
    (φ : TestOn upperHalfPlaneOpens) :
    (fun ω => coverProj j A h ω φ) =ᵐ[P] P[fun ω => h ω φ | coverSigma j A h] :=
  coverProj_ae_eq_condExpM hh hA (isCoverMarking_avoid hh hA hloc) j φ

end Limit

section CondLaw

lemma norm_exp_mul_exp_le (x : ℝ) {v : ℝ} (hv : 0 ≤ v) :
    ‖Complex.exp (Complex.I * (x : ℂ)) * ((Real.exp (-(1 / 2) * v) : ℝ) : ℂ)‖ ≤ 1 := by
  rw [norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
  linarith

variable {Ω : Type u} {ℳ 𝒦 : MeasurableSpace Ω} {𝒮 : Set ℂ → MeasurableSpace Ω}
  [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {A : Ω → Set ℂ} {h : Ω → DistOn upperHalfPlaneOpens}

omit [IsProbabilityMeasure P] in
/-- Monotone Dirichlet-space approximation along the covers: `σ²_{W_j(A)} → σ²_{ℍ∖A}`. -/
theorem ae_tendsto_zeroGFFTestCov_coverCompl (hAc : ∀ᵐ ω ∂P, A ω ⊆ H ∧ IsOpen (H \ A ω))
    (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, Tendsto (fun j => zeroGFFTestCov (coverCompl j (A ω)) φ φ) atTop
      (𝓝 (zeroGFFTestCov (H \ relClosureH (A ω)) φ φ)) := by
  filter_upwards [hAc] with ω ⟨hsub, hopen⟩
  have := tendsto_zeroGFFTestCov_iUnion (U := fun j => coverCompl j (A ω))
    (fun j => isOpen_coverOpen _) (fun a b hab => coverCompl_mono hab _)
    (fun j => coverCompl_subset_H j _) φ
  rw [relClosureH_eq hsub hopen]
  rwa [iUnion_coverCompl hopen] at this

omit mΩ [IsProbabilityMeasure P] in
lemma measurableSet_germSigmaAt_coverRad {G : Set Ω} (hG : MeasurableSet[germSigma A h] G)
    (j : ℕ) : MeasurableSet[germSigmaAt A h (coverRad j)] G := by
  have := iInf_le (fun n : ℕ => germSigmaAt A h (1 / ((n : ℝ) + 1))) (j + 1) G hG
  rwa [← coverRad_eq] at this

/-- **The conditional law given any σ-algebra `𝒦 ⊇ 𝒜` contained (up to null sets) in every
cover σ-algebra `𝒢_j`**: the same germ-measurable mean `M` and variance `σ²_{ℍ∖A}`. -/
theorem exists_condExp_germSigmaK
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hA : Measurable[mΩ, hittingSigma] A) (hmk : IsCoverMarking A h P ℳ 𝒮)
    (hAc : ∀ᵐ ω ∂P, A ω ⊆ H ∧ IsOpen (H \ A ω)) (h𝒦A : germSigma A h ≤ 𝒦) (hle : 𝒦 ≤ mΩ)
    (h𝒦tr : ∀ j, 𝒦 ≤ aeSigma (coverSigmaM ℳ j A h) P) (φ : TestOn upperHalfPlaneOpens) :
    ∃ M : Ω → ℝ, Measurable[germSigma A h] M ∧
      Tendsto (fun j => ∫ ω, (coverProj j A h ω φ - M ω) ^ 2 ∂P) atTop (𝓝 0) ∧
      M =ᵐ[P] P[fun ω => h ω φ | 𝒦] ∧
      (fun ω => Complex.exp (Complex.I * (M ω : ℂ)) *
          ((Real.exp (-(1 / 2) * zeroGFFTestCov (H \ relClosureH (A ω)) φ φ) : ℝ) : ℂ)) =ᵐ[P]
        P[fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) | 𝒦] := by
  have hhm := hh.measurable
  obtain ⟨M, hM0, hM2, hMlim⟩ := exists_germLimitM hh hA hmk φ
  have hM : Measurable[𝒦] M := hM0.mono h𝒦A le_rfl
  have hhi : Integrable (fun ω => h ω φ) P :=
    (hh.process.gaussian.hasGaussianLaw_eval φ).memLp_two.integrable one_le_two
  have hQi := fun j => integrable_coverProj hh hA j φ
  have hf2 : MemLp (fun ω => h ω φ) 2 P := (hh.process.gaussian.hasGaussianLaw_eval φ).memLp_two
  have hQmem : ∀ j, MemLp (fun ω => coverProj j A h ω φ - M ω) 2 P := fun j =>
    ((hf2.condExp (m := coverSigmaM ℳ j A h) one_le_two).ae_eq
      (coverProj_ae_eq_condExpM hh hA hmk j φ).symm).sub hM2
  have hMi : Integrable M P := hM2.integrable one_le_two
  have hMm : StronglyMeasurable[𝒦] M := hM.stronglyMeasurable
  -- every germ event is, up to a null set, an event of `𝒢_j`
  have htrace : ∀ G, MeasurableSet[𝒦] G → ∀ j,
      ∃ G', MeasurableSet[coverSigmaM ℳ j A h] G' ∧ G =ᵐ[P] G' := fun G hG j => h𝒦tr j G hG
  refine ⟨M, hM0, hMlim, ?_, ?_⟩
  · refine ae_eq_condExp_of_forall_setIntegral_eq hle hhi (fun s _ _ => hMi.integrableOn)
      (fun G hG _ => ?_) hMm.aestronglyMeasurable
    have hconst : ∀ j, ∫ ω in G, h ω φ ∂P = ∫ ω in G, coverProj j A h ω φ ∂P := fun j => by
      obtain ⟨G', hG', he⟩ := htrace G hG j
      rw [setIntegral_congr_set he, setIntegral_congr_set he]
      exact ((setIntegral_coverSigmaM hh hA hmk j hG' φ).2)
    have hlim := tendsto_setIntegral_of_tendsto_integral_sq hMi hQi hQmem hMlim G
    simp_rw [← hconst] at hlim
    exact (tendsto_nhds_unique tendsto_const_nhds hlim).symm
  · have hint : ∀ j, Integrable (fun ω => (M ω - coverProj j A h ω φ) ^ 2) P := fun j =>
      ((hQmem j).integrable_sq).congr (Eventually.of_forall fun ω => by ring)
    have hlim : Tendsto (fun j => ∫ ω, (M ω - coverProj j A h ω φ) ^ 2 ∂P) atTop (𝓝 0) :=
      hMlim.congr fun j => integral_congr_ae (Eventually.of_forall fun ω => by
        simp only; ring)
    obtain ⟨ns, hns, hnsae⟩ := exists_seq_tendsto_ae_of_tendsto_integral_sq (P := P) (f := M)
      (F := fun j ω => coverProj j A h ω φ)
      (fun j => ((measurable_distOn_apply φ).comp (measurable_coverProj hA hhm j)).aestronglyMeasurable)
      (hM.mono hle le_rfl).aestronglyMeasurable hint hlim
    have hvar := ae_tendsto_zeroGFFTestCov_coverCompl hAc φ
    have hsm : Measurable[𝒦] fun ω =>
        zeroGFFTestCov (H \ relClosureH (A ω)) φ φ :=
      (measurable_comap_zeroGFFTestCov_compl A φ φ).mono
        ((comap_le_germSigma A h).trans h𝒦A) le_rfl
    have hgm : StronglyMeasurable[𝒦] fun ω =>
        Complex.exp (Complex.I * (M ω : ℂ)) *
        ((Real.exp (-(1 / 2) * zeroGFFTestCov (H \ relClosureH (A ω)) φ φ) : ℝ) : ℂ) :=
      ((@GFF.measurable_exp_I_mul Ω 𝒦 _ hM).mul (Complex.measurable_ofReal.comp
        (Real.measurable_exp.comp (measurable_const.mul hsm)))).stronglyMeasurable
    have hnn : ∀ ω, 0 ≤ zeroGFFTestCov (H \ relClosureH (A ω)) φ φ := fun ω =>
      zeroGFFTestCov_self_nonneg (isOpen_H_diff_relClosureH _) sdiff_subset φ
    have hgi : Integrable (fun ω => Complex.exp (Complex.I * (M ω : ℂ)) *
        ((Real.exp (-(1 / 2) * zeroGFFTestCov (H \ relClosureH (A ω)) φ φ) : ℝ) : ℂ)) P :=
      Integrable.of_bound (hgm.mono hle).aestronglyMeasurable 1
        (Eventually.of_forall fun ω => norm_exp_mul_exp_le _ (hnn ω))
    refine ae_eq_condExp_of_forall_setIntegral_eq hle
      (GFF.integrable_exp_I_mul ((measurable_distOn_apply φ).comp hhm))
      (fun s _ _ => hgi.integrableOn) (fun G hG _ => ?_) hgm.aestronglyMeasurable
    have hconst : ∀ j, ∫ ω in G, Complex.exp (Complex.I * (h ω φ : ℂ)) ∂P =
        ∫ ω in G, Complex.exp (Complex.I * (coverProj j A h ω φ : ℂ)) *
          ((Real.exp (-(1 / 2) * zeroGFFTestCov (coverCompl j (A ω)) φ φ) : ℝ) : ℂ) ∂P := fun j => by
      obtain ⟨G', hG', he⟩ := htrace G hG j
      rw [setIntegral_congr_set he, setIntegral_congr_set he]
      exact ((setIntegral_coverSigmaM hh hA hmk j hG' φ).1)
    have hdom : Tendsto (fun i => ∫ ω in G, Complex.exp (Complex.I * (coverProj (ns i) A h ω φ : ℂ)) *
        ((Real.exp (-(1 / 2) * zeroGFFTestCov (coverCompl (ns i) (A ω)) φ φ) : ℝ) : ℂ) ∂P) atTop
        (𝓝 (∫ ω in G, Complex.exp (Complex.I * (M ω : ℂ)) *
          ((Real.exp (-(1 / 2) * zeroGFFTestCov (H \ relClosureH (A ω)) φ φ) : ℝ) : ℂ) ∂P)) := by
      refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ)) (fun i => ?_)
        (integrable_const (1 : ℝ)) (fun i => ae_restrict_of_ae (Eventually.of_forall fun ω =>
          norm_exp_mul_exp_le _ (zeroGFFTestCov_self_nonneg (V := coverCompl (ns i) (A ω))
            (isOpen_coverOpen _) (coverCompl_subset_H _ _) φ))) ?_
      · exact (((GFF.measurable_exp_I_mul ((measurable_distOn_apply φ).comp
          (measurable_coverProj hA hhm (ns i))))).mul (Complex.measurable_ofReal.comp
          (Real.measurable_exp.comp (measurable_const.mul
            (measurable_coverVar hA (ns i) φ))))).aestronglyMeasurable
      · refine ae_restrict_of_ae ?_
        filter_upwards [hnsae, hvar] with ω h1 h2
        refine ((Complex.continuous_exp.tendsto _).comp (tendsto_const_nhds.mul
          ((Complex.continuous_ofReal.tendsto _).comp h1))).mul
          ((Complex.continuous_ofReal.tendsto _).comp ((Real.continuous_exp.tendsto _).comp
            (tendsto_const_nhds.mul (h2.comp hns.tendsto_atTop))))
    simp_rw [← hconst] at hdom
    exact (tendsto_nhds_unique tendsto_const_nhds hdom).symm

/-- `exists_condExp_germSigmaK` for `𝒦 = 𝒜 ∨ ℳ`. -/
theorem exists_condExp_germSigmaM (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hA : Measurable[mΩ, hittingSigma] A) (hmk : IsCoverMarking A h P ℳ 𝒮)
    (hAc : ∀ᵐ ω ∂P, A ω ⊆ H ∧ IsOpen (H \ A ω)) (φ : TestOn upperHalfPlaneOpens) :
    ∃ M : Ω → ℝ, Measurable[germSigma A h] M ∧
      Tendsto (fun j => ∫ ω, (coverProj j A h ω φ - M ω) ^ 2 ∂P) atTop (𝓝 0) ∧
      M =ᵐ[P] P[fun ω => h ω φ | germSigma A h ⊔ ℳ] ∧
      (fun ω => Complex.exp (Complex.I * (M ω : ℂ)) *
          ((Real.exp (-(1 / 2) * zeroGFFTestCov (H \ relClosureH (A ω)) φ φ) : ℝ) : ℂ)) =ᵐ[P]
        P[fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) | germSigma A h ⊔ ℳ] :=
  exists_condExp_germSigmaK hh hA hmk hAc le_sup_left (sup_le (germSigma_le hA hh.measurable) hmk.le)
    (fun j => sup_le (fun G hG => germSigmaAt_le_aeSigmaM hh hmk.comap_le j G
      (measurableSet_germSigmaAt_coverRad hG j))
      ((le_sup_left : ℳ ≤ coverSigmaM ℳ j A h).trans (le_aeSigma _ P))) φ

omit ℳ 𝒮 𝒦 in
/-- `exists_condExp_germSigmaM` for `ℳ = σ(A)`: the conditional law of `h(φ)` given the germ
σ-algebra (specification (3.4)–(3.5) and the display after (3.5), p. 54): with the germ-measurable
limit `M` of the cover means, `E[h(φ) | 𝒜] = M` and `E[e^{i h(φ)} | 𝒜] = e^{iM} e^{−σ²_{ℍ∖A}(φ)/2}`. -/
theorem exists_condExp_germSigma (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hA : Measurable[mΩ, hittingSigma] A) (hloc : IsAvoidanceLocal A h P)
    (hAc : ∀ᵐ ω ∂P, A ω ⊆ H ∧ IsOpen (H \ A ω)) (φ : TestOn upperHalfPlaneOpens) :
    ∃ M : Ω → ℝ, Measurable[germSigma A h] M ∧
      Tendsto (fun j => ∫ ω, (coverProj j A h ω φ - M ω) ^ 2 ∂P) atTop (𝓝 0) ∧
      M =ᵐ[P] P[fun ω => h ω φ | germSigma A h] ∧
      (fun ω => Complex.exp (Complex.I * (M ω : ℂ)) *
          ((Real.exp (-(1 / 2) * zeroGFFTestCov (H \ relClosureH (A ω)) φ φ) : ℝ) : ℂ)) =ᵐ[P]
        P[fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) | germSigma A h] := by
  have := exists_condExp_germSigmaM hh hA (isCoverMarking_avoid hh hA hloc) hAc φ
  rwa [sup_eq_left.2 (comap_le_germSigma A h)] at this

end CondLaw

end LocalSets
end InteractingSLE
