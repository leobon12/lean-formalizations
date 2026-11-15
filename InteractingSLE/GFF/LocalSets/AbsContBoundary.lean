import InteractingSLE.GFF.LocalSets.AbsCont
import InteractingSLE.GFF.LocalSets.CMLimit
import InteractingSLE.GFF.LocalSets.Truncation

/-!
# Absolute continuity up to the boundary (specification Proposition 3.4 (ii), one domain)

Source: `source/spec/p001-048.md#prop-3.4` (ii) and its proof (pp. 46–48): if `U'` is a
neighbourhood of `cl U` with `D₁ ∩ U' = D₂ ∩ U'` and `F₁ − F₂ → 0` at the points of `∂Dᵢ ∩ U'`, the
laws of `(h₁ + F₁)|_U` and `(h₂ + F₂)|_U` are mutually absolutely continuous.

This file proves the case `D₁ = D₂ = D` (the case used throughout the specification, e.g. for
comparison fields on `ℍ` whose boundary data agree near a boundary point): then the random parts
have the same law, and the claim is a Cameron–Martin statement for the deterministic shift
`χ (F₁ − F₂)`, `χ ∈ C_c^∞(U')`, `χ = 1` on `cl U`. That shift is not compactly supported in `D`,
but it is the Dirichlet limit of the test functions `χ Φ_ε(F₁ − F₂)` (`Truncation.lean`, the
source's truncation and Caccioppoli argument), and Cameron–Martin passes to such limits
(`CMLimit.lean`).

## Main results

* `map_restrictAdd_absolutelyContinuous_of_tendsto_frontier` : for a zero-boundary GFF `Z` on an
  admissible `V`, bounded open `U ⊆ V`, open `U' ⊇ cl U`, harmonic `u₁, u₂` on `V` with
  `u₁ − u₂ → 0` at `∂V ∩ U'`: `law((Z + u₁)|_U) ≪ law((Z + u₂)|_U)`;
* **`map_restrictAdd_mutuallyAbsCont_boundary_of_eq`** : Proposition 3.4 (ii) for `D₁ = D₂`.

The case `D₁ ≠ D₂` additionally needs that the harmonic parts of the Markov decompositions of
`hᵢ` on `Dᵢ ∩ U'` tend to `0` at `∂Dᵢ ∩ U'` (Proposition 3.3); see the handoff.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set TopologicalSpace
open LQGMetric QuantumZipper.CameronMartin
open SupercriticalConformalCovariance.GM24 (smoothDist smoothDist_apply integrable_test_mul)

namespace InteractingSLE
namespace GFF

/-- `ρ_{f − g} = ρ_f − ρ_g` for `ρ_f = −Δf/(2π)`. -/
lemma cmTestOn_sub {V : Opens ℂ} (f g : MarkovZB.zsSub (V : Set ℂ)) :
    MarkovHarm.cmTestOn (f - g) = MarkovHarm.cmTestOn f - MarkovHarm.cmTestOn g := by
  ext x
  have hf : ContDiffAt ℝ 2 (f : ℂ → ℝ) x := (f.2.1.of_le (by norm_cast)).contDiffAt
  have hg : ContDiffAt ℝ 2 (g : ℂ → ℝ) x := (g.2.1.of_le (by norm_cast)).contDiffAt
  rw [FunLike.coe_sub, Pi.sub_apply]
  simp only [MarkovHarm.cmTestOn_apply, cmTest_apply]
  change -(2 * Real.pi)⁻¹ * Laplacian.laplacian ((f : ℂ → ℝ) - (g : ℂ → ℝ)) x =
    -(2 * Real.pi)⁻¹ * Laplacian.laplacian (f : ℂ → ℝ) x -
      -(2 * Real.pi)⁻¹ * Laplacian.laplacian (g : ℂ → ℝ) x
  rw [hf.laplacian_sub hg]
  ring

lemma comb_cmSigma {Ω : Type*} [MeasurableSpace Ω] {V : Opens ℂ} (X : TestOn V → Ω → ℝ)
    (f : MarkovZB.zsSub (V : Set ℂ)) (ω : Ω) :
    QuantumZipper.CameronMartin.comb X (MQ.cmSigma f) ω = X (MarkovHarm.cmTestOn f) ω := by
  simp [QuantumZipper.CameronMartin.comb, MQ.cmSigma, Finsupp.support_single]

/-- `K(σ_f − σ_g, σ_f − σ_g) = E(f − g)` for the Cameron–Martin vectors `σ_f = δ_{ρ_f}`. -/
lemma covNorm_cmSigma_sub {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {V : Opens ℂ}
    (hadm : ZBAdmissible V) {Z : Ω → DistOn V} (hZ : IsZeroBoundaryGFF V Z P)
    (f g : MarkovZB.zsSub (V : Set ℂ)) :
    covNorm (fun φ ω => Z ω φ) P (MQ.cmSigma f - MQ.cmSigma g) =
      QuantumZipper.dirichletEnergyOn V ((f : ℂ → ℝ) - g) := by
  have hX := hZ.process
  rw [show (f : ℂ → ℝ) - g = ((f - g : MarkovZB.zsSub (V : Set ℂ)) : ℂ → ℝ) from
    (Submodule.coe_sub _ _ _).symm]
  rw [← variance_comb hX.gaussian, ← MQ.covNorm_cmSigma hadm hX (f - g),
    ← variance_comb hX.gaussian]
  congr 1
  funext ω
  rw [comb_sub hX.gaussian, comb_cmSigma, comb_cmSigma, comb_cmSigma, cmTestOn_sub, map_sub]

/-- A distribution on an empty open set is zero. -/
lemma distOn_eq_zero_of_eq_empty {U : Opens ℂ} (hU : (U : Set ℂ) = ∅) (T : DistOn U) : T = 0 := by
  ext φ
  have : φ = 0 := by
    ext x
    exact image_eq_zero_of_notMem_tsupport fun hx => by simpa [hU] using φ.tsupport_subset hx
  simp [this]

/-- **Cameron–Martin shift by a harmonic function vanishing on part of the boundary.** Let `Z` be
a zero-boundary GFF on an admissible open `V`, `U ⊆ V` bounded open, `U'` open with `cl U ⊆ U'`,
and `u₁, u₂` harmonic on `V` with `u₁ − u₂ → 0` at the points of `∂V ∩ U'`. Then
`law((Z + u₁)|_U) ≪ law((Z + u₂)|_U)`. -/
theorem map_restrictAdd_absolutelyContinuous_of_tendsto_frontier {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {V U : Opens ℂ} {U' : Set ℂ} (hadm : ZBAdmissible V)
    (hUb : Bornology.IsBounded (U : Set ℂ)) (hUV : U ≤ V) (hU' : IsOpen U')
    (hUU' : closure (U : Set ℂ) ⊆ U') {Z : Ω → DistOn V} (hZ : IsZeroBoundaryGFF V Z P)
    {u₁ u₂ : ℂ → ℝ} (hu₁ : InnerProductSpace.HarmonicOnNhd u₁ V)
    (hu₂ : InnerProductSpace.HarmonicOnNhd u₂ V)
    (hbd : ∀ z ∈ frontier (V : Set ℂ) ∩ U', Tendsto (fun x => u₁ x - u₂ x) (𝓝[V] z) (𝓝 0)) :
    P.map (fun ω => restrictAdd U (Z ω) u₁) ≪ P.map (fun ω => restrictAdd U (Z ω) u₂) := by
  rcases (U : Set ℂ).eq_empty_or_nonempty with hUe | hUne
  · have e : ∀ F : ℂ → ℝ, (fun ω => restrictAdd U (Z ω) F) = fun _ => 0 := fun F =>
      funext fun ω => distOn_eq_zero_of_eq_empty hUe _
    rw [e, e]
  have hne : (V : Set ℂ).Nonempty := hUne.mono hUV
  set u : ℂ → ℝ := fun x => u₁ x - u₂ x with hudef
  have hu : InnerProductSpace.HarmonicOnNhd u V := hu₁.sub hu₂
  obtain ⟨χ, hχ, hχc, hχU, hχ1⟩ := exists_cutoff hUb.isCompact_closure hU' hUU'
  obtain ⟨v, hv, hw, hpair⟩ := exists_dirichlet_approx V.isOpen hu hbd hχU hχ hχc
  have hcu : ContinuousOn u V := (contDiffOn_of_harmonicOnNhd (n := 0) hu).continuousOn
  let f : ℕ → MarkovZB.zsSub (V : Set ℂ) := fun n =>
    ⟨truncCutoff V u χ (epsSeq n), contDiff_truncCutoff V.isOpen hu hbd hχU hχ (epsSeq_pos n),
      hasCompactSupport_truncCutoff hχc _,
      tsupport_truncCutoff_subset V.isOpen hcu hbd hχU (epsSeq_pos n)⟩
  set X : TestOn V → Ω → ℝ := fun φ ω => Z ω φ
  have hX := hZ.process
  set σ : ℕ → TestOn V →₀ ℝ := fun n => MQ.cmSigma (f n)
  set c : TestOn V → ℝ := fun j => ∫ x, χ x * (V : Set ℂ).indicator u x * j x
  have hc : ∀ j, Tendsto (fun n => covShift X P (σ n) j) atTop (𝓝 (c j)) := fun j => by
    have e : ∀ n, covShift X P (σ n) j = ∫ x, truncCutoff V u χ (epsSeq n) x * j x := fun n =>
      MQ.covShift_cmSigma hadm hne hX (f n) j
    simp only [e]
    exact hpair j j.continuous j.hasCompactSupport
  have hv' : Tendsto (fun n => covNorm X P (σ n)) atTop (𝓝 v) := by
    have e : ∀ n, covNorm X P (σ n) =
        QuantumZipper.dirichletEnergyOn V (truncCutoff V u χ (epsSeq n)) :=
      fun n => MQ.covNorm_cmSigma hadm hX (f n)
    simp only [e]
    exact hv
  have hw' : Tendsto (fun p : ℕ × ℕ => covNorm X P (σ p.1 - σ p.2)) atTop (𝓝 0) := by
    have e : ∀ p : ℕ × ℕ, covNorm X P (σ p.1 - σ p.2) = QuantumZipper.dirichletEnergyOn V
        (truncCutoff V u χ (epsSeq p.1) - truncCutoff V u χ (epsSeq p.2)) :=
      fun p => covNorm_cmSigma_sub hadm hZ (f p.1) (f p.2)
    simp only [e]
    exact hw
  have hac := map_add_absolutelyContinuous_of_tendsto hX.gaussian hX.measurable hX.centered hv' hw'
    hc
  -- lift to `𝒟'(V)`
  have hχG : Continuous fun x => χ x * (V : Set ℂ).indicator u x :=
    continuous_mul_indicator V.isOpen hu hbd hχU hχ.continuous
  set Tc : DistOn V := smoothDist V fun x => χ x * (V : Set ℂ).indicator u x
  have hTc : ∀ j : TestOn V, Tc j = c j := fun j => by
    rw [smoothDist_apply hχG.continuousOn]
    simp only [c, mul_comm]
  have hS : Measurable fun T : DistOn V => T + Tc :=
    measurable_distOn_iff.2 fun φ => (measurable_distOn_apply φ).add_const _
  have hZac : P.map (fun ω => Z ω + Tc) ≪ P.map Z := by
    refine absolutelyContinuous_of_map_distEval ?_
    rw [Measure.map_map (measurable_distEval V) (f := fun ω => Z ω + Tc) (hS.comp hZ.measurable),
      Measure.map_map (measurable_distEval V) hZ.measurable]
    have e1 : distEval V ∘ (fun ω => Z ω + Tc) = fun ω j => X j ω + c j := by
      funext ω j
      simp only [Function.comp_apply, distEval, add_apply, hTc, X]
    have e2 : distEval V ∘ Z = fun ω j => X j ω := rfl
    rw [e1, e2]
    exact hac
  -- restrict to `U` and add `u₂`
  have hc₁ : ContinuousOn u₁ U :=
    (contDiffOn_of_harmonicOnNhd (n := 0) hu₁).continuousOn.mono hUV
  have hc₂ : ContinuousOn u₂ U :=
    (contDiffOn_of_harmonicOnNhd (n := 0) hu₂).continuousOn.mono hUV
  set Ψ : DistOn V → DistOn U := fun T => restrictDist U T + smoothDist U u₂
  have hΨ : Measurable Ψ := measurable_distOn_iff.2 fun φ =>
    ((measurable_distOn_apply φ).comp (measurable_restrictDist U)).add_const _
  have key : ∀ T : DistOn V, Ψ (T + Tc) = restrictAdd U T u₁ := by
    intro T
    ext φ
    simp only [Ψ, restrictAdd, add_apply, restrictDist_apply]
    rw [smoothDist_apply hχG.continuousOn, smoothDist_apply hc₂, smoothDist_apply hc₁,
      coe_testIncl hUV, add_assoc, ← integral_add]
    · congr 1
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      by_cases hx : φ x = 0
      · simp [hx]
      · have hxU : x ∈ (U : Set ℂ) := φ.tsupport_subset (subset_tsupport _ hx)
        have h1 : χ x = 1 := hχ1 (subset_closure hxU)
        have h2 : (V : Set ℂ).indicator u x = u₁ x - u₂ x := indicator_of_mem (hUV hxU) u
        change φ x * (χ x * (V : Set ℂ).indicator u x) + φ x * u₂ x = φ x * u₁ x
        rw [h1, h2]
        ring
    · have := integrable_test_mul (B := V) hχG.continuousOn (testIncl U V φ)
      rwa [coe_testIncl hUV] at this
    · exact integrable_test_mul hc₂ φ
  calc P.map (fun ω => restrictAdd U (Z ω) u₁)
      = (P.map fun ω => Z ω + Tc).map Ψ := by
        rw [Measure.map_map hΨ (f := fun ω => Z ω + Tc) (hS.comp hZ.measurable)]
        congr 1
        funext ω
        exact (key (Z ω)).symm
    _ ≪ (P.map Z).map Ψ := hZac.map hΨ
    _ = P.map (fun ω => restrictAdd U (Z ω) u₂) := Measure.map_map hΨ hZ.measurable

/-- **Proposition 3.4 (ii) for `D₁ = D₂ = D`, general form.** Let `D` be an admissible open set,
`h₁, h₂` zero-boundary GFFs on `D` (on any probability spaces), `F₁, F₂` harmonic on `D`, `U ⊆ D`
bounded open, and `U'` an open neighbourhood of `cl U` such that `F₁ − F₂ → 0` at the points of
`∂D ∩ U'`. Then the laws of `(h₁ + F₁)|_U` and `(h₂ + F₂)|_U` are mutually absolutely
continuous. -/
theorem map_restrictAdd_mutuallyAbsCont_of_tendsto_frontier {D U : Opens ℂ} {U' : Set ℂ}
    (hD : ZBAdmissible D) (hUb : Bornology.IsBounded (U : Set ℂ)) (hUD : (U : Set ℂ) ⊆ D)
    (hU' : IsOpen U') (hUU' : closure (U : Set ℂ) ⊆ U') {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁]
    [MeasurableSpace Ω₂] {P₁ : Measure Ω₁} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₁]
    [IsProbabilityMeasure P₂] {h₁ : Ω₁ → DistOn D} {h₂ : Ω₂ → DistOn D}
    (hh₁ : IsZeroBoundaryGFF D h₁ P₁) (hh₂ : IsZeroBoundaryGFF D h₂ P₂) {F₁ F₂ : ℂ → ℝ}
    (hF₁ : InnerProductSpace.HarmonicOnNhd F₁ D) (hF₂ : InnerProductSpace.HarmonicOnNhd F₂ D)
    (hbd : ∀ z ∈ frontier (D : Set ℂ) ∩ U', Tendsto (fun x => F₁ x - F₂ x) (𝓝[D] z) (𝓝 0)) :
    P₁.map (fun ω => restrictAdd U (h₁ ω) F₁) ≪ P₂.map (fun ω => restrictAdd U (h₂ ω) F₂) ∧
      P₂.map (fun ω => restrictAdd U (h₂ ω) F₂) ≪ P₁.map (fun ω => restrictAdd U (h₁ ω) F₁) := by
  have hUD' : U ≤ D := hUD
  have hΦ : ∀ F : ℂ → ℝ, Measurable fun T : DistOn D => restrictAdd U T F := fun F =>
    measurable_distOn_iff.2 fun φ =>
      ((measurable_distOn_apply φ).comp (measurable_restrictDist U)).add_const _
  have hlaw : ∀ F : ℂ → ℝ, P₁.map (fun ω => restrictAdd U (h₁ ω) F) =
      P₂.map (fun ω => restrictAdd U (h₂ ω) F) := fun F => by
    calc P₁.map (fun ω => restrictAdd U (h₁ ω) F)
        = (P₁.map h₁).map (fun T => restrictAdd U T F) :=
          (Measure.map_map (hΦ F) hh₁.measurable).symm
      _ = (P₂.map h₂).map (fun T => restrictAdd U T F) := by rw [hh₁.map_eq hh₂]
      _ = _ := Measure.map_map (hΦ F) hh₂.measurable
  have hbd' : ∀ z ∈ frontier (D : Set ℂ) ∩ U', Tendsto (fun x => F₂ x - F₁ x) (𝓝[D] z) (𝓝 0) :=
    fun z hz => by simpa only [neg_sub, neg_zero] using (hbd z hz).neg
  have h12 := map_restrictAdd_absolutelyContinuous_of_tendsto_frontier hD hUb hUD' hU' hUU' hh₂
    hF₁ hF₂ hbd
  have h21 := map_restrictAdd_absolutelyContinuous_of_tendsto_frontier hD hUb hUD' hU' hUU' hh₂
    hF₂ hF₁ hbd'
  rw [hlaw F₁]
  exact ⟨h12, h21⟩

/-- **Proposition 3.4 (ii) (Absolute continuity, boundary) for `D₁ = D₂`.** Let `D ≠ ℂ` be a
simply connected domain, `h₁, h₂` zero-boundary GFFs on `D`, `F₁, F₂` harmonic on `D`, and
`U ⊆ D` a bounded simply connected domain. If some neighbourhood `U'` of `cl U` (here
`D ∩ U' = D ∩ U'` trivially) is such that `F₁ − F₂` tends to zero as one approaches the points of
`∂D ∩ U'`, then the laws of `(h₁ + F₁)|_U` and `(h₂ + F₂)|_U` are mutually absolutely continuous.
(The connectivity hypotheses on `U` are not used.) -/
theorem map_restrictAdd_mutuallyAbsCont_boundary_of_eq {D U : Opens ℂ} {U' : Set ℂ}
    (hDc : IsConnected (D : Set ℂ)) (hDs : IsSimplyConnected (D : Set ℂ))
    (hDne : (D : Set ℂ) ≠ univ) (hUb : Bornology.IsBounded (U : Set ℂ))
    (_hUc : IsConnected (U : Set ℂ)) (_hUs : IsSimplyConnected (U : Set ℂ))
    (hUD : (U : Set ℂ) ⊆ D) (hU' : U' ∈ 𝓝ˢ (closure (U : Set ℂ)))
    {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] {P₁ : Measure Ω₁}
    {P₂ : Measure Ω₂} [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
    {h₁ : Ω₁ → DistOn D} {h₂ : Ω₂ → DistOn D} (hh₁ : IsZeroBoundaryGFF D h₁ P₁)
    (hh₂ : IsZeroBoundaryGFF D h₂ P₂) {F₁ F₂ : ℂ → ℝ}
    (hF₁ : InnerProductSpace.HarmonicOnNhd F₁ D) (hF₂ : InnerProductSpace.HarmonicOnNhd F₂ D)
    (hbd : ∀ z ∈ frontier (D : Set ℂ) ∩ U', Tendsto (fun x => F₁ x - F₂ x) (𝓝[D] z) (𝓝 0)) :
    P₁.map (fun ω => restrictAdd U (h₁ ω) F₁) ≪ P₂.map (fun ω => restrictAdd U (h₂ ω) F₂) ∧
      P₂.map (fun ω => restrictAdd U (h₂ ω) F₂) ≪ P₁.map (fun ω => restrictAdd U (h₁ ω) F₁) := by
  have hint : closure (U : Set ℂ) ⊆ interior U' := subset_interior_iff_mem_nhdsSet.2 hU'
  exact map_restrictAdd_mutuallyAbsCont_of_tendsto_frontier
    (zbAdmissible_of_isSimplyConnected hDc hDs hDne) hUb hUD isOpen_interior hint hh₁ hh₂ hF₁ hF₂
    fun z hz => hbd z ⟨hz.1, interior_subset hz.2⟩

end GFF
end InteractingSLE
