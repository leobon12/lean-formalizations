/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCRef
import InteractingSLE.GFF.LocalSets.AbsContBoundary

/-!
# Flow-line locality (named) and the Cameron–Martin shift of a GFF with piecewise constant data (proved)

Packet PROVE-RLC-D, part (1). Source: Lemma G3 and its proof (supplement §7.3, `source/spec/p481-528.md` L290–L320,
pp. 492–493) and the restricted-field locality argument of Aux. lemma 97's proof (`source/spec/p289-336.md` L556–L572,
pp. 326–327).

`RLC.G3ChartComparisonStatement` (PROVE-RLC-A's named input) has two halves:

* **the field half**, proved here: `exists_shift_isGFFWithBoundaryData` — for data `b`, `bR` agreeing on an open
  `O ⊆ ℝ` and a compact `K` whose real points lie over `O`, one Cameron–Martin density `Z` and one deterministic shift
  `T` vanishing near `K` turn a GFF with data `b` into a GFF with data `bR` (`H₀ + T` under `Z·Q₀`);
* **the path half**, the flow-line locality theorem, recorded as the named input `FlowLocalityStatement`: two GFFs on
  one space under equivalent laws, with data agreeing on `O` and fields agreeing near the closure of a bounded open
  buffer `V` (whose real points lie over `O`), have flow lines (same seed, same angle) that agree up to and including
  their common exit time from `V`.

`RLCDG3.lean` assembles G3 from the two halves and Theorems 1.2 (param) / 1.3 (realization of flow lines on the
shifted space through the canonical flow codes).

**Why `FlowLocalityStatement` is not proved here.** Its source proof (Aux. 97, pp. 326–327, as used in G3) needs (a)
that
a field-determined local set inside a deterministic closed set is measurable with respect to the field near that set
(Lemma 6.2's locality, landed as `Sec6.le_aeSigma_explored`, from the history locality of flow lines — Aux. 56,
`Restart.RetainedRangeEntranceStatement`, itself a named input); and (b) the identification of the stopped coupling
under
the change of measure — the weighted conditional mean is the reference canonical mean off the stopped hull (Aux. 61–63),
the stopped driving law is the reference word's (Girsanov with the landed drift identity
`Aux61Ident.srcDrift_eq_markDrift`
and uniqueness of the integrated driving equations), and a stopped flow-line coupling with these laws extends to a full
one (Aux. 54) so that Theorem 1.2 identifies its path with the field-determined reference path. The landed form of (b)
(PROVE-LOCEXT-A…O) covers only Aux. 55's seed ball of radius `r` with the two-seed reference, and even there rests on
the
named locality input `LocalExt.ExtLocalityLStatement`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open LQGMetric QuantumZipper.CameronMartin
open SupercriticalConformalCovariance.GM24 (smoothDist smoothDist_apply integrable_test_mul)
open QuantumZipper (H Hbar)

universe u

namespace InteractingSLE

namespace RLC

/-! ### The Cameron–Martin shift of a GFF with piecewise constant data -/

/-- The difference of two piecewise constant data that agree on an open set `O` is piecewise constant with jumps
off `O`. -/
theorem isPiecewiseConstant_sub_filter {b bR : ℝ → ℝ} {J Ĵ : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b J) (hbR : IsPiecewiseConstantBoundaryData bR Ĵ)
    {O : Set ℝ} (hO : IsOpen O) (hbO : ∀ x ∈ O, b x = bR x) [DecidablePred (· ∈ O)] :
    IsPiecewiseConstantBoundaryData (fun x => bR x - b x) ((J ∪ Ĵ).filter fun x => x ∉ O) := by
  intro y hy
  by_cases hyO : y ∈ O
  · filter_upwards [hO.mem_nhds hyO] with z hz
    rw [hbO z hz, hbO y hyO, sub_self, sub_self]
  · have hyJ : y ∉ J ∪ Ĵ := fun h => hy (Finset.mem_filter.2 ⟨h, hyO⟩)
    rw [Finset.mem_union, not_or] at hyJ
    filter_upwards [hb y hyJ.1, hbR y hyJ.2] with z h1 h2
    rw [h1, h2]

/-- A bounded harmonic extension off `S` is one off every larger set. -/
theorem isBoundedHarmonicExtension_mono {g : ℝ → ℝ} {S S' : Set ℝ} {u : ℂ → ℝ}
    (hu : IsBoundedHarmonicExtension g S u) (hSS' : S ⊆ S') : IsBoundedHarmonicExtension g S' u :=
  ⟨hu.1, hu.2.1, fun x hx => hu.2.2 x fun h => hx (hSS' h)⟩

/-- A real point of the frontier of `ℍ`. -/
theorem im_eq_zero_of_mem_frontier_H {z : ℂ} (hz : z ∈ frontier H) : z.im = 0 := by
  have h1 : z ∈ closure H := frontier_subset_closure hz
  have h2 : z ∉ H := by
    have := hz.2
    rwa [QuantumZipper.isOpen_H.interior_eq] at this
  have hcl : closure H ⊆ Hbar := closure_minimal (fun w hw => show (0 : ℝ) ≤ w.im from le_of_lt hw)
    QuantumZipper.isClosed_Hbar
  have h3 : (0 : ℝ) ≤ z.im := hcl h1
  have h4 : ¬ (0 : ℝ) < z.im := h2
  linarith [not_lt.1 h4]

/-- **Cameron–Martin shift of a GFF with piecewise constant data, localized away from a compact set** (the field half of
Lemma G3's proof, supplement p. 493: "`v = M̂ − M` extends harmonically across [the seed intervals] and is zero there
[…] The reflected cutoff construction therefore gives a single `f ∈ H₀¹(ℍ)` agreeing with `v` on `U` and on a
neighborhood of its closure. Use the one full Cameron–Martin density for adding `f` to the conditional field"). Let `b`
(jumps `J`) and `bR` (jumps `Ĵ`) be piecewise constant data that agree on an open set `O ⊆ ℝ`, let `K ⊆ ℂ` be compact
with real points only over `O`, and let `H₀` be a GFF with data `b` under `Q₀`. Then there are an open neighbourhood `N`
of `K` whose real points lie over `O`, a density `Z > 0` with `E Z = 1`, and a deterministic distribution `T` vanishing
on test functions supported in `N`, such that `H₀ + T` is a GFF with data `bR` under `Z·Q₀`.

Proof: `q` is the bounded harmonic extension of `bR − b` (piecewise constant with jumps off `O`), so `q → 0` at every
point of `O` and every bounded harmonic extension of `bR` is `u₀ + q` on `ℍ`. With a cutoff `χ = 1` near `K`
supported where `ℝ` meets only `O`, the shift `χ q` is a Dirichlet limit of test functions
(`GFF.exists_dirichlet_approx`),
so Cameron–Martin gives mutual absolute continuity of the laws of `X + χq` and `X` (`X` the centred field); `Z` is the
Radon–Nikodym derivative of the two path laws read off `X`, and `T = (1 − χ) q`. -/
theorem exists_shift_isGFFWithBoundaryData {b bR : ℝ → ℝ} {J Ĵ : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b J) (hbR : IsPiecewiseConstantBoundaryData bR Ĵ)
    {O : Set ℝ} (hO : IsOpen O) (hbO : ∀ x ∈ O, b x = bR x)
    {K : Set ℂ} (hK : IsCompact K) (hKO : ∀ z ∈ K, z.im = 0 → z.re ∈ O)
    {S : Type*} [MeasurableSpace S] (Q₀ : Measure S) [IsProbabilityMeasure Q₀]
    {H₀ : S → DistOn upperHalfPlaneOpens} (hH : IsGFFWithBoundaryData Q₀ H₀ b J) :
    ∃ (Z : S → ℝ) (T : DistOn upperHalfPlaneOpens) (N : Set ℂ), IsOpen N ∧ K ⊆ N ∧
      (∀ z ∈ N, z.im = 0 → z.re ∈ O) ∧ Measurable Z ∧ (∀ᵐ x ∂Q₀, 0 < Z x) ∧ ∫ x, Z x ∂Q₀ = 1 ∧
      IsGFFWithBoundaryData (Q₀.withDensity fun x => ENNReal.ofReal (Z x)) (fun x => H₀ x + T) bR Ĵ ∧
      ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ N → T φ = 0 := by
  classical
  -- the harmonic means
  set K' : Finset ℝ := (J ∪ Ĵ).filter fun x => x ∉ O with hK'
  have hD := isPiecewiseConstant_sub_filter hb hbR hO hbO
  set u₀ := (PiecewiseConstant.stepData b J).harmonicExtH with hu₀def
  have hu₀ := PiecewiseConstant.isBoundedHarmonicExtension_harmonicExtH_stepData hb
  set q := (PiecewiseConstant.stepData (fun x => bR x - b x) K').harmonicExtH with hqdef
  have hq := PiecewiseConstant.isBoundedHarmonicExtension_harmonicExtH_stepData hD
  have hK'J : (K' : Set ℝ) ⊆ ((J ∪ Ĵ : Finset ℝ) : Set ℝ) := fun x hx => (Finset.mem_filter.1 hx).1
  -- every bounded harmonic extension of `bR` is `u₀ + q` on `ℍ`
  have hsum : ∀ û : ℂ → ℝ, IsBoundedHarmonicExtension bR Ĵ û → EqOn û (fun z => u₀ z + q z) H := by
    intro û hû
    have h1 : IsBoundedHarmonicExtension bR ((J ∪ Ĵ : Finset ℝ) : Set ℝ) (fun z => u₀ z + q z) := by
      obtain ⟨C₀, hC₀⟩ := hu₀.2.1
      obtain ⟨C₁, hC₁⟩ := hq.2.1
      refine ⟨hu₀.1.add hq.1, ⟨C₀ + C₁, fun z hz => (abs_add_le _ _).trans (add_le_add (hC₀ z hz) (hC₁ z hz))⟩,
        fun x hx => ?_⟩
      have hxJ : x ∉ (J : Set ℝ) := fun h => hx (by simp only [Finset.coe_union]; exact Or.inl h)
      have hxK : x ∉ (K' : Set ℝ) := fun h => hx (hK'J h)
      have := (hu₀.2.2 x hxJ).add (hq.2.2 x hxK)
      simpa only [add_sub_cancel] using this
    have h2 : IsBoundedHarmonicExtension bR ((J ∪ Ĵ : Finset ℝ) : Set ℝ) û :=
      isBoundedHarmonicExtension_mono hû (by simp only [Finset.coe_union]; exact subset_union_right)
    exact PiecewiseConstant.eqOn_of_isBoundedHarmonicExtension (J ∪ Ĵ).finite_toSet h1 h2
  -- `q` vanishes on `O`
  have hqO : ∀ x ∈ O, Tendsto q (𝓝[H] (x : ℂ)) (𝓝 0) := by
    intro x hx
    have hxK : x ∉ K' := fun h => (Finset.mem_filter.1 h).2 hx
    have h := (PiecewiseConstant.stepData (fun x => bR x - b x) K').tendsto_harmonicExtH
      (t := x) fun j hj => hxK (hj ▸ PiecewiseConstant.stepData_x_mem _ K' j)
    rwa [PiecewiseConstant.bdry_stepData hD hxK, hbO x hx, sub_self] at h
  -- the buffer `U'` (no real point off `O`) and the cutoff
  set U' : Set ℂ := {z : ℂ | z.im = 0 ∧ z.re ∉ O}ᶜ with hU'def
  have hU'o : IsOpen U' :=
    ((isClosed_eq Complex.continuous_im continuous_const).inter
      (hO.isClosed_compl.preimage Complex.continuous_re)).isOpen_compl
  have hKU' : K ⊆ U' := fun z hz hz' => hz'.2 (hKO z hz hz'.1)
  obtain ⟨δ, hδ, hδU'⟩ := hK.exists_cthickening_subset_open hU'o hKU'
  have hδ2 : 0 < δ / 2 := half_pos hδ
  obtain ⟨χ, hχ, hχc, hχU, hχ1⟩ := GFF.exists_cutoff (hK.cthickening (r := δ / 2)) hU'o
    ((cthickening_mono (half_le_self hδ.le) K).trans hδU')
  set N : Set ℂ := thickening (δ / 2) K with hNdef
  have hNo : IsOpen N := isOpen_thickening
  have hKN : K ⊆ N := self_subset_thickening hδ2 K
  have hχN : ∀ z ∈ N, χ z = 1 := fun z hz => hχ1 (thickening_subset_cthickening _ _ hz)
  have hbd : ∀ z ∈ frontier (upperHalfPlaneOpens : Set ℂ) ∩ U',
      Tendsto q (𝓝[(upperHalfPlaneOpens : Set ℂ)] z) (𝓝 0) := by
    intro z ⟨hzf, hzU⟩
    have hz0 : z.im = 0 := im_eq_zero_of_mem_frontier_H hzf
    have hzO : z.re ∈ O := by
      by_contra h
      exact hzU ⟨hz0, h⟩
    have hz : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [hz0])
    rw [hz]
    exact hqO z.re hzO
  have hqh : InnerProductSpace.HarmonicOnNhd q (upperHalfPlaneOpens : Set ℂ) := hq.1
  obtain ⟨v, hv, hw, hpair⟩ := GFF.exists_dirichlet_approx upperHalfPlaneOpens.isOpen hqh hbd hχU hχ hχc
  have hcq : ContinuousOn q (upperHalfPlaneOpens : Set ℂ) :=
    (GFF.contDiffOn_of_harmonicOnNhd (n := 0) hqh).continuousOn
  let f : ℕ → MarkovZB.zsSub (upperHalfPlaneOpens : Set ℂ) := fun n =>
    ⟨GFF.truncCutoff upperHalfPlaneOpens q χ (GFF.epsSeq n),
      GFF.contDiff_truncCutoff upperHalfPlaneOpens.isOpen hqh hbd hχU hχ (GFF.epsSeq_pos n),
      GFF.hasCompactSupport_truncCutoff hχc _,
      GFF.tsupport_truncCutoff_subset upperHalfPlaneOpens.isOpen hcq hbd hχU (GFF.epsSeq_pos n)⟩
  -- the centred field and its Cameron–Martin vectors
  have hZ := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hH hu₀
  set X : TestOn upperHalfPlaneOpens → S → ℝ := fun φ ω => WholeField.centredField H₀ u₀ ω φ with hXdef
  have hX := hZ.process
  have hadm : ZBAdmissible upperHalfPlaneOpens := zbAdmissible_of_subset_H subset_rfl
  have hne : (upperHalfPlaneOpens : Set ℂ).Nonempty := ⟨Complex.I, show (0 : ℝ) < Complex.I.im by simp⟩
  set σ : ℕ → TestOn upperHalfPlaneOpens →₀ ℝ := fun n => MQ.cmSigma (f n)
  set c : TestOn upperHalfPlaneOpens → ℝ :=
    fun j => ∫ x, χ x * (upperHalfPlaneOpens : Set ℂ).indicator q x * j x with hcdef
  have hc : ∀ j, Tendsto (fun n => covShift X Q₀ (σ n) j) atTop (𝓝 (c j)) := fun j => by
    have e : ∀ n, covShift X Q₀ (σ n) j = ∫ x, GFF.truncCutoff upperHalfPlaneOpens q χ (GFF.epsSeq n) x * j x :=
      fun n => MQ.covShift_cmSigma hadm hne hX (f n) j
    simp only [e]
    exact hpair j j.continuous j.hasCompactSupport
  have hv' : Tendsto (fun n => covNorm X Q₀ (σ n)) atTop (𝓝 v) := by
    have e : ∀ n, covNorm X Q₀ (σ n) =
        QuantumZipper.dirichletEnergyOn upperHalfPlaneOpens (GFF.truncCutoff upperHalfPlaneOpens q χ (GFF.epsSeq n)) :=
      fun n => MQ.covNorm_cmSigma hadm hX (f n)
    simp only [e]
    exact hv
  have hw' : Tendsto (fun p : ℕ × ℕ => covNorm X Q₀ (σ p.1 - σ p.2)) atTop (𝓝 0) := by
    have e : ∀ p : ℕ × ℕ, covNorm X Q₀ (σ p.1 - σ p.2) = QuantumZipper.dirichletEnergyOn upperHalfPlaneOpens
        (GFF.truncCutoff upperHalfPlaneOpens q χ (GFF.epsSeq p.1) -
          GFF.truncCutoff upperHalfPlaneOpens q χ (GFF.epsSeq p.2)) :=
      fun p => GFF.covNorm_cmSigma_sub hadm hZ (f p.1) (f p.2)
    simp only [e]
    exact hw
  have hac := GFF.map_add_absolutelyContinuous_of_tendsto hX.gaussian hX.measurable hX.centered hv' hw' hc
  have hca := GFF.map_absolutelyContinuous_add_of_tendsto hX.gaussian hX.measurable hX.centered hv' hw' hc
  -- the density: the Radon–Nikodym derivative of the two path laws, read off the centred field
  set p : S → TestOn upperHalfPlaneOpens → ℝ := fun ω j => X j ω with hpdef
  set p₁ : S → TestOn upperHalfPlaneOpens → ℝ := fun ω j => X j ω + c j with hp₁def
  have hpm : Measurable p := measurable_pi_iff.2 hX.measurable
  have hp₁m : Measurable p₁ := measurable_pi_iff.2 fun j => (hX.measurable j).add_const _
  set μ₀ := Q₀.map p with hμ₀
  set μ₁ := Q₀.map p₁ with hμ₁
  set ρ := μ₁.rnDeriv μ₀ with hρ
  have hρm : Measurable ρ := Measure.measurable_rnDeriv _ _
  have hwd : μ₀.withDensity ρ = μ₁ := Measure.withDensity_rnDeriv_eq μ₁ μ₀ hac
  have hρtop : ∀ᵐ ω ∂Q₀, ρ (p ω) < ∞ := ae_of_ae_map hpm.aemeasurable (Measure.rnDeriv_lt_top μ₁ μ₀)
  have hρpos : ∀ᵐ ω ∂Q₀, 0 < ρ (p ω) := ae_of_ae_map hpm.aemeasurable (hca.ae_le (Measure.rnDeriv_pos hac))
  set Z : S → ℝ := fun ω => (ρ (p ω)).toReal with hZdef
  have hZm : Measurable Z := (hρm.comp hpm).ennreal_toReal
  have hZρ : (fun ω => ENNReal.ofReal (Z ω)) =ᵐ[Q₀] fun ω => ρ (p ω) := by
    filter_upwards [hρtop] with ω hω
    exact ENNReal.ofReal_toReal hω.ne
  set Q := Q₀.withDensity fun ω => ENNReal.ofReal (Z ω) with hQdef
  have hQmap : Q.map p = μ₁ := by
    rw [hQdef, withDensity_congr_ae hZρ, ← hwd]
    ext s hs
    rw [Measure.map_apply hpm hs, withDensity_apply _ (hpm hs), withDensity_apply _ hs,
      setLIntegral_map hs hρm hpm]
  have hQuniv : Q univ = 1 := by
    have h1 := congrArg (fun μ : Measure (TestOn upperHalfPlaneOpens → ℝ) => μ univ) hQmap
    rwa [Measure.map_apply hpm MeasurableSet.univ, preimage_univ, measure_univ (μ := μ₁)] at h1
  have hQprob : IsProbabilityMeasure Q := ⟨hQuniv⟩
  have hZ1 : ∫ ω, Z ω ∂Q₀ = 1 := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun ω => ENNReal.toReal_nonneg)
      hZm.aestronglyMeasurable]
    have : ∫⁻ ω, ENNReal.ofReal (Z ω) ∂Q₀ = 1 := by
      rw [← hQuniv, hQdef, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    rw [this, ENNReal.toReal_one]
  have hZpos : ∀ᵐ ω ∂Q₀, 0 < Z ω := by
    filter_upwards [hρtop, hρpos] with ω h1 h2
    exact ENNReal.toReal_pos h2.ne' h1.ne
  -- under `Q`, `X − c` has the law of `X` under `Q₀`
  set Y : TestOn upperHalfPlaneOpens → S → ℝ := fun φ ω => X φ ω - c φ with hYdef
  have hYm : ∀ φ, Measurable (Y φ) := fun φ => (hX.measurable φ).sub_const _
  have hYlaw : HasLaw (zbPath Y) (Q₀.map (zbPath X)) Q := by
    have hsub : Measurable fun g : TestOn upperHalfPlaneOpens → ℝ => fun j => g j - c j :=
      measurable_pi_iff.2 fun j => (measurable_pi_apply j).sub_const _
    refine ⟨(measurable_pi_iff.2 hYm).aemeasurable, ?_⟩
    have e1 : zbPath Y = (fun g : TestOn upperHalfPlaneOpens → ℝ => fun j => g j - c j) ∘ p := rfl
    have e2 : zbPath X = (fun g : TestOn upperHalfPlaneOpens → ℝ => fun j => g j - c j) ∘ p₁ := by
      funext ω j
      simp only [zbPath, Function.comp_apply, hp₁def, add_sub_cancel_right]
    rw [e1, ← Measure.map_map hsub hpm, hQmap, e2, ← Measure.map_map hsub hp₁m]
  have hYz : IsZBGFFProcess upperHalfPlaneOpens Y Q := Determination.isZBGFFProcess_of_hasLaw hX hYm hYlaw
  -- the deterministic shift `T = (1 − χ) q`
  have hcq' : ContinuousOn (fun z => (1 - χ z) * q z) (upperHalfPlaneOpens : Set ℂ) :=
    ((continuous_const.sub hχ.continuous).continuousOn).mul hcq
  set T : DistOn upperHalfPlaneOpens := smoothDist upperHalfPlaneOpens fun z => (1 - χ z) * q z with hTdef
  have hT0 : ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ N → T φ = 0 := by
    intro φ hφ
    rw [hTdef, smoothDist_apply hcq']
    refine integral_eq_zero_of_ae (ae_of_all _ fun z => ?_)
    by_cases hz : φ z = 0
    · simp [hz]
    · show φ z * ((1 - χ z) * q z) = 0
      rw [hχN z (hφ (subset_tsupport _ hz)), sub_self, zero_mul, mul_zero]
  -- the shifted field
  have hcu₀ : ContinuousOn u₀ (upperHalfPlaneOpens : Set ℂ) :=
    (GFF.contDiffOn_of_harmonicOnNhd (n := 0) hu₀.1).continuousOn
  have hχq : ContinuousOn (fun z => χ z * q z) (upperHalfPlaneOpens : Set ℂ) := hχ.continuous.continuousOn.mul hcq
  have hS : Measurable fun T' : DistOn upperHalfPlaneOpens => T' + T :=
    measurable_distOn_iff.2 fun φ => (measurable_distOn_apply φ).add_const _
  have hmeasT : Measurable fun x => H₀ x + T := hS.comp hH.1
  have hNO : ∀ z ∈ N, z.im = 0 → z.re ∈ O := by
    intro z hz hz0
    by_contra h
    exact hδU' (thickening_subset_cthickening_of_le (half_le_self hδ.le) K hz) ⟨hz0, h⟩
  refine ⟨Z, T, N, hNo, hKN, hNO, hZm, hZpos, hZ1, ⟨hmeasT, fun û hû => ?_⟩, hT0⟩
  have e : (fun (φ : TestOn upperHalfPlaneOpens) ω => (H₀ ω + T) φ - ∫ z, û z * φ z) = Y := by
    funext φ ω
    have hφH : ∀ z, φ z ≠ 0 → z ∈ H := fun z hz => φ.tsupport_subset (subset_tsupport _ hz)
    have I1 := integrable_test_mul hcu₀ φ
    have I2 := integrable_test_mul hcq φ
    have I3 := integrable_test_mul hχq φ
    have eT : T φ = (∫ x, φ x * q x) - ∫ x, φ x * (χ x * q x) := by
      rw [hTdef, smoothDist_apply hcq', ← integral_sub I2 I3]
      congr 1; funext x; ring
    have eU : ∫ z, û z * φ z = (∫ x, φ x * u₀ x) + ∫ x, φ x * q x := by
      rw [← integral_add I1 I2]
      refine integral_congr_ae (ae_of_all _ fun z => ?_)
      by_cases hz : φ z = 0
      · simp [hz]
      · show û z * φ z = φ z * u₀ z + φ z * q z
        rw [hsum û hû (hφH z hz)]; ring
    have eC : c φ = ∫ x, φ x * (χ x * q x) := by
      rw [hcdef]
      refine integral_congr_ae (ae_of_all _ fun z => ?_)
      by_cases hz : φ z = 0
      · simp [hz]
      · show χ z * (upperHalfPlaneOpens : Set ℂ).indicator q z * φ z = φ z * (χ z * q z)
        rw [Set.indicator_of_mem (show z ∈ (upperHalfPlaneOpens : Set ℂ) from hφH z hz)]; ring
    have eX : X φ ω = H₀ ω φ - ∫ x, φ x * u₀ x := by
      rw [hXdef]
      simp only
      rw [WholeField.centredField_apply H₀ hu₀.1 ω φ]
      congr 1; congr 1; funext x; ring
    simp only [hYdef, add_apply]
    rw [eT, eU, eC, eX]
    ring
  rw [e]
  exact hYz


/-! ### Flow-line locality -/

/-- **Named input: flow-line locality** (the restricted-field locality of Aux. lemma 97's proof, pp. 326–327, in the
form Lemma G3's proof uses it, p. 493: "the restricted-field locality argument written out in Aux. lemma 97 identify the
reference stopped paths as measurable functions of the field restricted to `U`", together with the identification of
the stopped coupling under the change of measure, Aux. lemmas 61–63). Fix `0 < κ < 4`. Let `b` (jumps `J`) and `bR`
(jumps `Ĵ`) be piecewise constant data agreeing on an open set `O ⊆ ℝ`; let `N ⊆ ℂ` be open with real points only over
`O`, and `V` a bounded open set with `closure V ⊆ N`. On one measurable space let `Q₀`, `Q` be equivalent probability
measures, `H₀` a GFF with data `b` under `Q₀` and `Ĥ` a GFF with data `bR` under `Q`, with `Ĥ = H₀` on every test
function
supported in `N` (pointwise in the sample). Then the angle-`θ` flow line `Γ` of `H₀` from `y` (under `Q₀`) and the
angle-`θ` flow line `α` of `Ĥ` from `y` (under `Q`) agree, `Q₀`-almost surely, up to and including their common exit
time
from `V` (`StoppedAgree`, lifetimes included). **Not proved in Lean** (see the module docstring). -/
def FlowLocalityStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b bR : ℝ → ℝ) (J Ĵ : Finset ℝ), IsPiecewiseConstantBoundaryData b J →
    IsPiecewiseConstantBoundaryData bR Ĵ → ∀ O : Set ℝ, IsOpen O → (∀ x ∈ O, b x = bR x) →
    ∀ N : Set ℂ, IsOpen N → (∀ z ∈ N, z.im = 0 → z.re ∈ O) →
    ∀ V : Set ℂ, IsOpen V → Bornology.IsBounded V → closure V ⊆ N → ∀ y θ : ℝ,
    ∀ {S : Type u} [MeasurableSpace S] (Q₀ Q : Measure S) [IsProbabilityMeasure Q₀] [IsProbabilityMeasure Q],
      Q₀ ≪ Q → Q ≪ Q₀ →
    ∀ (H₀ Ĥ : S → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData Q₀ H₀ b J →
      IsGFFWithBoundaryData Q Ĥ bR Ĵ →
      (∀ (x : S) (φ : TestOn upperHalfPlaneOpens), tsupport φ ⊆ N → Ĥ x φ = H₀ x φ) →
    ∀ (Γ α : S → ℝ≥0 → ℂ) (U ζ : S → ℝ≥0∞), IsFlowLine κ b J y θ Q₀ H₀ Γ U →
      IsFlowLine κ bR Ĵ y θ Q Ĥ α ζ → ∀ᵐ x ∂Q₀, StoppedAgree V (Γ x) (U x) (α x) (ζ x)

end RLC

end InteractingSLE
