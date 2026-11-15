import InteractingSLE.GFF.LocalSets.GermMedian
import InteractingSLE.GFF.LocalSets.Unions

/-!
# Lemma 3.6, (i) ⇒ (iii), and the equivalence of the four characterizations of local sets

Specification §3.2, Lemma 3.6 (pp. 51–55; transcription `source/spec/p049-096.md#lem-3.6`), the
restatement of [SS13, Lemma 3.9]. The implications (iii) ⇒ (iv) ⇒ (ii) ⇒ (i) were proved by
PROVE-LS-B (`Characterization`, `MarkedAvoidance`); here (i) ⇒ (iii):

* `exists_germVersion` : the germ-measurable conditional means `M ψ = E[h(ψ) | 𝒜]` of
  `exists_condExp_germSigma` are almost surely the pairings of a germ-measurable random distribution
  `h₁` (LQGMetric `exists_version`, with admissibility from `ae_mem_rangeSet_germMean` and continuity
  in probability from the Gaussian variance bound);
* `ae_isHarmonicDistOn_germVersion` : `h₁` is almost surely harmonic on `ℍ ∖ A` (on each atom of the
  covers `h₁` annihilates the Laplacians of a countable generating family of `C_c^∞(W_T)`, since
  every finer cover mean is harmonic there; Weyl's lemma; `ℍ ∖ A = ⋃_j W_j(A)`);
* `isCondZeroBoundaryGFF_germVersion` : `E[e^{i(h − h₁)(φ)} | 𝒜] = e^{−σ²_{ℍ∖A}(φ)/2}`;
* `IsAvoidanceLocal.isGermConditionalLaw` : **(i) ⇒ (iii)**;
* `isLocalSet_tfae` : **Lemma 3.6** — (i), (ii), (iii), (iv) are equivalent for a zero-boundary GFF
  `h` on `ℍ` and an almost surely relatively closed random set `A ⊆ ℍ`.
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
  LQGMetric.MarkovAsm

section Aux

variable {Ω : Type*} {m : MeasurableSpace Ω}

lemma measurableSet_edist_ge {f g : Ω → ℝ} (hf : Measurable[m] f) (hg : Measurable[m] g)
    (ε : ℝ≥0∞) : MeasurableSet[m] {ω | ε ≤ edist (f ω) (g ω)} :=
  measurableSet_le measurable_const (hf.edist hg)

end Aux

section Version

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {A : Ω → Set ℂ} {h : Ω → DistOn upperHalfPlaneOpens}

/-- **The conditional mean is a random distribution**: there are germ-measurable versions `M ψ` of
`E[h(ψ) | 𝒜]` (with the conditional law of `exists_condExp_germSigma` and the `L²` approximation
by the cover means) and a germ-measurable random distribution `h₁` with `h₁(ψ) = M ψ` a.s. -/
theorem exists_germVersion (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hA : Measurable[mΩ, hittingSigma] A) (hloc : IsAvoidanceLocal A h P)
    (hAc : ∀ᵐ ω ∂P, A ω ⊆ H ∧ IsOpen (H \ A ω)) :
    ∃ (M : TestOn upperHalfPlaneOpens → Ω → ℝ) (h₁ : Ω → DistOn upperHalfPlaneOpens),
      IsGermMeanFamily A h P M ∧
      (∀ ψ, Tendsto (fun j => ∫ ω, (coverProj j A h ω ψ - M ψ ω) ^ 2 ∂P) atTop (𝓝 0)) ∧
      Measurable[germSigma A h] h₁ ∧ ∀ ψ, (fun ω => h₁ ω ψ) =ᵐ[P] M ψ := by
  have hhm := hh.measurable
  have hle := germSigma_le hA hhm
  choose M hMm hMlim hMc hMe using fun ψ => exists_condExp_germSigma hh hA hloc hAc ψ
  have hM : IsGermMeanFamily A h P M := fun ψ => ⟨hMm ψ, hMc ψ, hMe ψ⟩
  -- admissibility, transferred to the trimmed measure
  have hadm := ae_mem_rangeSet_germMean hh hA hM
  have hS : MeasurableSet[germSigma A h]
      {ω | (fun c => M (comb upperHalfPlaneOpens c) ω) ∈ rangeSet upperHalfPlaneOpens} :=
    (@Measurable.of_eval Ω CoordJ (fun _ => ℝ) (germSigma A h) _ _
      fun c => hMm (comb upperHalfPlaneOpens c)) (measurableSet_rangeSet _)
  have hadm' : ∀ᵐ ω ∂(P.trim hle),
      (fun c => M (comb upperHalfPlaneOpens c) ω) ∈ rangeSet upperHalfPlaneOpens := by
    rw [ae_iff]
    rw [show {a | ¬ (fun c => M (comb upperHalfPlaneOpens c) a) ∈ rangeSet upperHalfPlaneOpens} =
      {ω | (fun c => M (comb upperHalfPlaneOpens c) ω) ∈ rangeSet upperHalfPlaneOpens}ᶜ from rfl,
      trim_measurableSet_eq hle hS.compl]
    exact ae_iff.1 hadm
  -- continuity in probability
  have hcont : ∀ (φ : TestOn upperHalfPlaneOpens) (ψ : ℕ → TestOn upperHalfPlaneOpens),
      Tendsto ψ atTop (𝓝 φ) → TendstoInMeasure (P.trim hle) (fun k => M (ψ k)) atTop (M φ) := by
    intro φ ψ hψ
    have hP : TendstoInMeasure P (fun k => M (ψ k)) atTop (M φ) := by
      refine tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num)
        (fun k => (hMm (ψ k)).mono hle le_rfl |>.aestronglyMeasurable)
        ((hMm φ).mono hle le_rfl |>.aestronglyMeasurable) ?_
      have hd : Tendsto (fun k => ψ k - φ) atTop (𝓝 0) := by
        simpa using hψ.sub_const φ
      have hv := tendsto_zeroGFFTestCov_of_tendsto hh hd
      have hbd : ∀ k, eLpNorm (M (ψ k) - M φ) 2 P ≤
          ENNReal.ofReal (Real.sqrt (zeroGFFTestCov H ⇑(ψ k - φ) ⇑(ψ k - φ))) := by
        intro k
        have hint : ∀ χ, Integrable (fun ω => h ω χ) P := fun χ =>
          (hh.process.gaussian.hasGaussianLaw_eval χ).memLp_two.integrable one_le_two
        have he : (M (ψ k) - M φ) =ᵐ[P] P[fun ω => h ω (ψ k - φ) | germSigma A h] := by
          have e : (fun ω => h ω (ψ k - φ)) = (fun ω => h ω (ψ k)) - fun ω => h ω φ := by
            funext ω; simp [map_sub]
          rw [e]
          filter_upwards [hMc (ψ k), hMc φ, condExp_sub (m := germSigma A h) (hint (ψ k)) (hint φ)]
            with ω h1 h2 h3
          rw [Pi.sub_apply, h1, h2, h3, Pi.sub_apply]
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
    have hmeas : ∀ k, MeasurableSet[germSigma A h] {ω | ε ≤ edist (M (ψ k) ω) (M φ ω)} := fun k =>
      measurableSet_edist_ge (hMm (ψ k)) (hMm φ) ε
    simp_rw [trim_measurableSet_eq hle (hmeas _)]
    exact hP ε hε
  obtain ⟨h₁, hh₁, hh₁e⟩ := @LQGMetric.exists_version upperHalfPlaneOpens Ω (germSigma A h)
    (P.trim hle) _ M hMm hadm' hcont
  exact ⟨M, h₁, hM, hMlim, hh₁, fun ψ => ae_eq_of_ae_eq_trim (hh₁e ψ)⟩

end Version

section Harmonic

lemma isHarmonicDistOn_of_lapTest {T : DistOn upperHalfPlaneOpens} {U : Opens ℂ}
    (hU : U ≤ upperHalfPlaneOpens) (hT : ∀ k : ℕ × ℕ, T (lapTest U (toZs (distGen U k))) = 0) :
    IsHarmonicDistOn T U := by
  obtain ⟨g, hg, hgeq⟩ := GFF.exists_harmonic_of_distGen (GFF.restrictDist U T) fun k => by
    rw [GFF.restrictDist_apply]; exact hT k
  refine ⟨g, hg, fun φ hφ => ?_⟩
  have := hgeq (testOnOfSubset φ hφ)
  rw [GFF.restrictDist_apply, testIncl_testOnOfSubset hU] at this
  exact this

lemma lapTest_congr {U U' : Opens ℂ} (hU : U ≤ upperHalfPlaneOpens) (hU' : U' ≤ upperHalfPlaneOpens)
    (f : zsSub (U : Set ℂ)) (f' : zsSub (U' : Set ℂ)) (hff : f.1 = f'.1) :
    lapTest U f = lapTest U' f' := by
  ext z
  rw [coe_lapTest hU, coe_lapTest hU', cmTest_apply, cmTest_apply]
  have : (⇑(zsTest f.2) : ℂ → ℝ) = ⇑(zsTest f'.2) := funext fun w =>
    show f.1 w = f'.1 w by rw [hff]
  rw [this]

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {A : Ω → Set ℂ} {h : Ω → DistOn upperHalfPlaneOpens}

/-- On the atom `{W_j(A) = W_T}`, the conditional mean annihilates the Laplacians of the generators
of `C_c^∞(W_T)`: every finer cover mean `Q_{j'} h` (`j' ≥ j`) is harmonic on `W_{T'} ⊇ W_T`. -/
theorem ae_coverAtom_lapTest_eq_zero (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hA : Measurable[mΩ, hittingSigma] A) (hloc : IsAvoidanceLocal A h P)
    {M : TestOn upperHalfPlaneOpens → Ω → ℝ} (hM : IsGermMeanFamily A h P M)
    (hMlim : ∀ ψ, Tendsto (fun j => ∫ ω, (coverProj j A h ω ψ - M ψ ω) ^ 2 ∂P) atTop (𝓝 0))
    (j : ℕ) (T : Finset (ℕ × ℂ)) (k : ℕ × ℕ) :
    ∀ᵐ ω ∂P, ω ∈ coverAtom j A T →
      M (lapTest (markovOpen T) (toZs (distGen (markovOpen T) k))) ω = 0 := by
  have hhm := hh.measurable
  set U := markovOpen T
  have hUle : U ≤ upperHalfPlaneOpens := markovOpen_subset_H T
  set f := toZs (distGen U k)
  set ψ := lapTest U f
  -- every finer cover mean vanishes at `ψ` on the atom
  have hzero : ∀ᵐ ω ∂P, ∀ j' : ℕ, ∀ T' ∈ (coverIdx j').powerset, T ⊆ T' →
      markovCompl (coverMarkov.{u} T') (h ω) ψ = 0 := by
    refine ae_all_iff.2 fun j' => (eventually_all_finset _).2 fun T' _ => ?_
    filter_upwards [ae_isHarmonicDistOn_of_isMarkovDecomposition (markovOpen_subset_H T')
      (isMarkovDecomposition_coverMarkov hh T')] with ω hω hTT'
    exact IsHarmonicDistOn.apply_lapTest_eq_zero (markovOpen T').isOpen hω hUle
      (markovOpen_mono hTT') f
  -- the subsequence
  have hf2 : MemLp (fun ω => h ω ψ) 2 P := (hh.process.gaussian.hasGaussianLaw_eval ψ).memLp_two
  have hM2 : MemLp (M ψ) 2 P :=
    (hf2.condExp (m := germSigma A h) one_le_two).ae_eq (hM ψ).2.1.symm
  have hmem : ∀ j', MemLp (fun ω => coverProj j' A h ω ψ - M ψ ω) 2 P := fun j' =>
    ((hf2.condExp (m := coverSigma j' A h) one_le_two).ae_eq
      (coverProj_ae_eq_condExp hh hA hloc j' ψ).symm).sub hM2
  obtain ⟨ns, hns, hnsae⟩ := exists_seq_tendsto_ae_of_tendsto_integral_sq (P := P) (f := M ψ)
    (F := fun j' ω => coverProj j' A h ω ψ)
    (fun j' => ((measurable_distOn_apply ψ).comp (measurable_coverProj hA hhm j')).aestronglyMeasurable)
    hM2.aestronglyMeasurable (fun j' => ((hmem j').integrable_sq).congr
      (Eventually.of_forall fun ω => by ring))
    ((hMlim ψ).congr fun j' => integral_congr_ae (Eventually.of_forall fun ω => by ring))
  filter_upwards [hzero, hnsae] with ω h1 h2 hω
  have hω' : removedIdx j (A ω) = T := hω
  have hev : ∀ᶠ i in atTop, coverProj (ns i) A h ω ψ = 0 := by
    filter_upwards [hns.tendsto_atTop.eventually_ge_atTop j] with i hi
    rw [coverProj]
    exact h1 _ _ (mem_coverAtom_powerset ω) (hω' ▸ removedIdx_mono hi (A ω))
  exact tendsto_nhds_unique h2 (tendsto_const_nhds.congr' (hev.mono fun i hi => hi.symm))

end Harmonic

section Final

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {A : Ω → Set ℂ} {h : Ω → DistOn upperHalfPlaneOpens}

/-- **The conditional mean is harmonic off `A`** (specification p. 54: "The harmonicity of `M` on
`D ∖ A` follows from the coarse harmonic projections on each compact set disjoint from `A`"). -/
theorem ae_isHarmonicDistOn_germVersion (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hA : Measurable[mΩ, hittingSigma] A) (hloc : IsAvoidanceLocal A h P)
    (hAc : ∀ᵐ ω ∂P, A ω ⊆ H ∧ IsOpen (H \ A ω)) {M : TestOn upperHalfPlaneOpens → Ω → ℝ}
    (hM : IsGermMeanFamily A h P M)
    (hMlim : ∀ ψ, Tendsto (fun j => ∫ ω, (coverProj j A h ω ψ - M ψ ω) ^ 2 ∂P) atTop (𝓝 0))
    {h₁ : Ω → DistOn upperHalfPlaneOpens} (hh₁ : ∀ ψ, (fun ω => h₁ ω ψ) =ᵐ[P] M ψ) :
    ∀ᵐ ω ∂P, IsHarmonicDistOn (h₁ ω) (H \ A ω) := by
  have hall : ∀ᵐ ω ∂P, ∀ j : ℕ, ∀ T ∈ (coverIdx j).powerset, ∀ k : ℕ × ℕ,
      ω ∈ coverAtom j A T →
        h₁ ω (lapTest (markovOpen T) (toZs (distGen (markovOpen T) k))) = 0 := by
    refine ae_all_iff.2 fun j => (eventually_all_finset _).2 fun T _ => ae_all_iff.2 fun k => ?_
    filter_upwards [ae_coverAtom_lapTest_eq_zero hh hA hloc hM hMlim j T k, hh₁ _] with ω h1 h2 hω
    rw [h2]; exact h1 hω
  filter_upwards [hall, hAc] with ω hω ⟨hsub, hopen⟩
  have hW : ∀ j, IsHarmonicDistOn (h₁ ω) (markovOpen (removedIdx j (A ω))) := fun j =>
    isHarmonicDistOn_of_lapTest (markovOpen_subset_H _) fun k =>
      hω j _ (mem_coverAtom_powerset ω) k rfl
  set U' : Opens ℂ := ⟨H \ A ω, hopen⟩
  have hU' : U' ≤ upperHalfPlaneOpens := fun z hz => hz.1
  refine isHarmonicDistOn_of_lapTest (U := U') hU' fun k => ?_
  set f := toZs (distGen U' k)
  have hK : IsCompact (tsupport f.1) := f.2.2.1
  have hKU : tsupport f.1 ⊆ ⋃ j, coverCompl j (A ω) := by
    rw [iUnion_coverCompl hopen]; exact f.2.2.2
  obtain ⟨j, hj⟩ := hK.elim_directed_cover _ (fun j => isOpen_coverOpen _) hKU
    (Monotone.directed_le fun a b hab => coverCompl_mono hab (A ω))
  have hWset : (markovOpen (removedIdx j (A ω)) : Set ℂ) = coverCompl j (A ω) :=
    coe_markovOpen (removedIdx_subset j (A ω))
  let f' : zsSub (markovOpen (removedIdx j (A ω)) : Set ℂ) :=
    ⟨f.1, f.2.1, f.2.2.1, hj.trans hWset.symm.subset⟩
  rw [lapTest_congr hU' (markovOpen_subset_H _) f f' rfl]
  exact IsHarmonicDistOn.apply_lapTest_eq_zero (markovOpen _).isOpen (hW j)
    (markovOpen_subset_H _) subset_rfl f'

/-- **The residual is conditionally a zero-boundary GFF on `ℍ ∖ A`.** -/
theorem isCondZeroBoundaryGFF_germVersion (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hA : Measurable[mΩ, hittingSigma] A) (hAc : ∀ᵐ ω ∂P, A ω ⊆ H ∧ IsOpen (H \ A ω))
    {M : TestOn upperHalfPlaneOpens → Ω → ℝ} (hM : IsGermMeanFamily A h P M)
    {h₁ : Ω → DistOn upperHalfPlaneOpens} (hh₁m : Measurable[germSigma A h] h₁)
    (hh₁ : ∀ ψ, (fun ω => h₁ ω ψ) =ᵐ[P] M ψ) :
    IsCondZeroBoundaryGFF P (germSigma A h) (fun ω => H \ A ω) (fun ω => h ω - h₁ ω) := by
  intro φ
  have hhm := hh.measurable
  set W : Ω → ℂ := fun ω => Complex.exp (-(Complex.I * (h₁ ω φ : ℂ)))
  have hWm : StronglyMeasurable[germSigma A h] W :=
    (Complex.measurable_exp.comp ((measurable_const.mul (Complex.measurable_ofReal.comp
      ((measurable_distOn_apply φ).comp hh₁m))).neg)).stronglyMeasurable
  have hWb : ∀ ω, ‖W ω‖ ≤ 1 := fun ω => by
    simp only [W, neg_mul_eq_mul_neg, ← Complex.ofReal_neg, Complex.norm_exp_I_mul_ofReal]; rfl
  have hF : Integrable (fun ω => Complex.exp (Complex.I * (h ω φ : ℂ))) P :=
    GFF.integrable_exp_I_mul ((measurable_distOn_apply φ).comp hhm)
  have hle := germSigma_le hA hhm
  have hWF : Integrable (fun ω => W ω * Complex.exp (Complex.I * (h ω φ : ℂ))) P :=
    hF.bdd_mul (hWm.mono hle).aestronglyMeasurable (Eventually.of_forall hWb)
  have hpull := condExp_bilin_of_stronglyMeasurable_left (ContinuousLinearMap.mul ℝ ℂ) hWm
    (by simpa [ContinuousLinearMap.mul_apply'] using hWF) hF
  have e : (fun ω => Complex.exp (Complex.I * (((h ω - h₁ ω) φ : ℝ) : ℂ))) =
      fun ω => (ContinuousLinearMap.mul ℝ ℂ) (W ω) (Complex.exp (Complex.I * (h ω φ : ℂ))) := by
    funext ω
    simp only [W, ContinuousLinearMap.mul_apply', sub_apply, Complex.ofReal_sub, ← Complex.exp_add]
    congr 1; ring
  rw [e]
  filter_upwards [hpull, (hM φ).2.2, hh₁ φ, hAc] with ω h1 h2 h3 ⟨hsub, hopen⟩
  rw [h1, ContinuousLinearMap.mul_apply', ← h2]
  simp only [W, h3, germVar, relClosureH_eq hsub hopen, ← mul_assoc, ← Complex.exp_add,
    neg_add_cancel, Complex.exp_zero, one_mul]

/-- **Lemma 3.6, (i) ⇒ (iii)** (specification §3.2, pp. 52–54). For a zero-boundary GFF `h` on `ℍ`
and a random relatively closed `A ⊆ ℍ` satisfying the avoidance criterion (i), conditionally on
the germ σ-algebra `𝒜` the field is `h₁ + h₂` with `h₁` an `𝒜`-measurable random distribution,
almost surely harmonic on `ℍ ∖ A`, and `h₂` a zero-boundary GFF on `ℍ ∖ A`. -/
theorem IsAvoidanceLocal.isGermConditionalLaw (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hA : Measurable[mΩ, hittingSigma] A) (hAc : ∀ᵐ ω ∂P, A ω ⊆ H ∧ IsOpen (H \ A ω))
    (hloc : IsAvoidanceLocal A h P) : IsGermConditionalLaw A h P := by
  obtain ⟨M, h₁, hM, hMlim, hh₁m, hh₁⟩ := exists_germVersion hh hA hloc hAc
  exact ⟨h₁, hh₁m, ae_isHarmonicDistOn_germVersion hh hA hloc hAc hM hMlim hh₁,
    isCondZeroBoundaryGFF_germVersion hh hA hAc hM hh₁m hh₁⟩

/-- **Lemma 3.6** (specification §3.2, p. 51, the restatement of [SS13, Lemma 3.9]): for a
zero-boundary GFF `h` on `ℍ` and a random relatively closed set `A ⊆ ℍ`, the characterizations
(i) avoidance, (ii) marked avoidance, (iii) germ conditional law and (iv) locality are
equivalent. -/
theorem isLocalSet_tfae (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hA : Measurable[mΩ, hittingSigma] A) (hAc : ∀ᵐ ω ∂P, A ω ⊆ H ∧ IsOpen (H \ A ω)) :
    [IsAvoidanceLocal A h P, IsMarkedAvoidanceLocal A h P, IsGermConditionalLaw A h P,
      IsLocalSet A h P].TFAE :=
  tfae_of_isAvoidanceLocal_imp_isGermConditionalLaw hh.measurable hA hAc
    fun hloc => hloc.isGermConditionalLaw hh hA hAc

end Final

end LocalSets
end InteractingSLE
