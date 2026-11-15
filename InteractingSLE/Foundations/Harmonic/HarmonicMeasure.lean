import InteractingSLE.Foundations.Harmonic.PoissonH
import InteractingSLE.Foundations.PrimeEnd.Basic
import QuantumZipper.Proofs.Thm18.LWBeurlingMain
import QuantumZipper.Proofs.Thm18.LWHarmPoisson
import LQGMetric.Complex.HarmonicComp

/-!
# Harmonic measure of prime-end sets in simply connected domains

Design `planning/INFRA-GEO.md` §4, packet GEO-HM. For an open domain `D` with a half-plane chart
`ψ : D → ℍ` (`HChart D`), the harmonic measure from `z ∈ D` of a set `S` of prime ends of `D` is
the half-plane harmonic measure, seen from `ψ z`, of the boundary points of `ℍ` that `ψ` marks
by `S` (Garnett–Marshall, *Harmonic Measure*, Ch. I §1, eq. (1.6): `ω(z, E, D) = ω(ψ z, ψ E, ℍ)`).

## Main definitions

* `PrimeEnd.chartMeasure ψ z`: the image of `harmonicMeasureH (ψ z)` under `x ↦ mk ψ x`;
* `PrimeEnd.harmonicMeasure D z`: the common value of all chart measures (it exists by
  `PrimeEnd.chartMeasure_eq`, proved first; `0` if the charts disagree, which happens only off
  open domains or for `z ∉ D`);
* `PrimeEnd.impression p`: the cluster set at the marked point of the inverse of a chart
  (Pommerenke, *Boundary Behaviour of Conformal Maps*, §2.5: the impression of a prime end).

## Main results

* `PrimeEnd.chartMeasure_eq_of_eqOn`, `PrimeEnd.chartMeasure_eq` (**Möbius invariance**): two
  charts differ by a real Möbius map `m`, and `harmonicMeasureH_mobius` transports the harmonic
  measure through the boundary action of `m`;
* `PrimeEnd.harmonicMeasure_eq_chartMeasure`, `PrimeEnd.harmonicMeasure_apply`: the definition
  in any chart;
* `PrimeEnd.isProbabilityMeasure_harmonicMeasure`;
* `PrimeEnd.harmonicMeasure_eq_map_pullback` (**conformal invariance**): for a conformal
  bijection `f : D → E`, `ω_D(z, ·)` is the image of `ω_E(f z, ·)` under the induced map of
  prime ends;
* `PrimeEnd.harmonicOnNhd_harmonicMeasure`: `z ↦ ω_D(z, S)` is harmonic on `D`;
* `PrimeEnd.tendsto_harmonicMeasure_nhdsWithin`: `ω_D(z, S) → 0` as `z → x₀ ∈ ∂D`, when `S` is
  closed and no impression of a prime end of `S` contains `x₀`;
* `PrimeEnd.harmonicMeasure_le_beurling` (**Beurling estimate**, Garnett–Marshall Thm III.9.2;
  Lawler, *Conformally Invariant Processes in the Plane*, Thm 3.69): if a continuum outside `D`
  joins `closedBall w d` to the complement of `ball w ρ`, the harmonic measure from `w` of
  prime ends whose impressions avoid `ball w ρ` is at most `C (d/ρ)^{1/2}`. It is QuantumZipper's
  `Thm18Asm.LWFar.beurlingHarmStmt_holds` applied to `z ↦ ω_D(z, closure S)`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Function MeasureTheory
open scoped ENNReal NNReal Real
open SupercriticalConformalCovariance (IsConformalBijection)
open QuantumZipper (H Hbar)
open QuantumZipper.CA (realMobius)

namespace InteractingSLE

namespace PrimeEnd

variable {D : Set ℂ}

/-- The Borel σ-algebra of the prime-end topology. -/
instance : MeasurableSpace (PrimeEnd D) := borel _

instance : BorelSpace (PrimeEnd D) := ⟨rfl⟩

/-- The boundary map of a chart on the real points: `x ↦ mk ψ x`. -/
def chartBdry (ψ : HChart D) (x : ℝ) : PrimeEnd D := mk ψ (x : OnePoint ℝ)

theorem continuous_chartBdry (hD : IsOpen D) (ψ : HChart D) : Continuous (chartBdry ψ) :=
  (continuous_mk hD ψ).comp OnePoint.continuous_coe

theorem isOpenEmbedding_chartBdry (hD : IsOpen D) (ψ : HChart D) :
    Topology.IsOpenEmbedding (chartBdry ψ) :=
  (mkHomeomorph hD ψ).isOpenEmbedding.comp OnePoint.isOpenEmbedding_coe

theorem measurableEmbedding_chartBdry (hD : IsOpen D) (ψ : HChart D) :
    MeasurableEmbedding (chartBdry ψ) :=
  (isOpenEmbedding_chartBdry hD ψ).measurableEmbedding

/-- The harmonic measure seen through one chart: the image of `ω_ℍ(ψ z, ·)` under the boundary
map of `ψ`. -/
def chartMeasure (ψ : HChart D) (z : ℂ) : Measure (PrimeEnd D) :=
  (harmonicMeasureH (ψ.1 z)).map (chartBdry ψ)

theorem mobiusBdry_coe_of_ne {a b c d x : ℝ} (hx : c * x + d ≠ 0) :
    mobiusBdry a b c d (x : OnePoint ℝ) = (((a * x + b) / (c * x + d) : ℝ) : OnePoint ℝ) := by
  change (if c * x + d = 0 then OnePoint.infty else _) = _
  simp only [hx, ↓reduceIte]

/-- `ω_ℍ(z, ·)` is absolutely continuous with respect to Lebesgue measure. -/
theorem harmonicMeasureH_absolutelyContinuous (z : ℂ) :
    harmonicMeasureH z ≪ (volume : Measure ℝ) :=
  withDensity_absolutelyContinuous _ _

/-- **Möbius invariance**: if `φ = m ∘ ψ` on `D` for a real Möbius map `m` of positive
determinant, the two charts give the same harmonic measure (`harmonicMeasureH_mobius`; the pole
of `m` is a null boundary point). -/
theorem chartMeasure_eq_of_eqOn (hD : IsOpen D) {ψ φ : HChart D} {a b c d : ℝ}
    (hdet : 0 < a * d - b * c) (hEq : EqOn φ.1 (realMobius a b c d ∘ ψ.1) D) {z : ℂ}
    (hz : z ∈ D) : chartMeasure φ z = chartMeasure ψ z := by
  have hψz : ψ.1 z ∈ H := ψ.mapsTo hz
  have hm : Measurable fun x : ℝ => (a * x + b) / (c * x + d) := by fun_prop
  rw [chartMeasure, hEq hz, comp_apply, ← harmonicMeasureH_mobius hdet hψz,
    Measure.map_map (continuous_chartBdry hD φ).measurable hm, chartMeasure]
  refine Measure.map_congr ?_
  have hnull : ∀ᵐ x ∂(harmonicMeasureH (ψ.1 z)), c * x + d ≠ 0 := by
    refine harmonicMeasureH_absolutelyContinuous _ (measure_mono_null (fun x hx => ?_)
      (PoissonH.measure_setOf_mul_add_eq_zero hdet))
    simpa using hx
  filter_upwards [hnull] with x hx
  simp only [comp_apply, chartBdry]
  rw [← mobiusBdry_coe_of_ne hx, mk_mobiusBdry hdet hEq]

/-- **Chart independence** of the harmonic measure on an open domain. -/
theorem chartMeasure_eq (hD : IsOpen D) (ψ φ : HChart D) {z : ℂ} (hz : z ∈ D) :
    chartMeasure φ z = chartMeasure ψ z := by
  obtain ⟨a, b, c, d, hdet, hEq⟩ := ψ.exists_realMobius hD φ
  exact chartMeasure_eq_of_eqOn hD hdet hEq hz

/-- The chart measures of an open domain with a chart have exactly one common value. -/
theorem existsUnique_chartMeasure_eq (hD : IsOpen D) [Nonempty (HChart D)] {z : ℂ}
    (hz : z ∈ D) : ∃! μ : Measure (PrimeEnd D), ∀ ψ : HChart D, chartMeasure ψ z = μ := by
  obtain ⟨ψ₀⟩ := ‹Nonempty (HChart D)›
  exact ⟨chartMeasure ψ₀ z, fun φ => chartMeasure_eq hD ψ₀ φ hz, fun μ hμ => (hμ ψ₀).symm⟩

open scoped Classical in
/-- **Harmonic measure** from `z` of sets of prime ends of `D`: the common value of the chart
measures `chartMeasure ψ z` (Garnett–Marshall, Ch. I, eq. (1.6)). It is `0` when the charts
disagree (not the case for `z ∈ D` open: `harmonicMeasure_eq_chartMeasure`). -/
@[irreducible] def harmonicMeasure (D : Set ℂ) (z : ℂ) : Measure (PrimeEnd D) :=
  if h : ∃ μ : Measure (PrimeEnd D), ∀ ψ : HChart D, chartMeasure ψ z = μ then h.choose else 0

theorem harmonicMeasure_eq_chartMeasure (hD : IsOpen D) {z : ℂ} (hz : z ∈ D) (ψ : HChart D) :
    harmonicMeasure D z = chartMeasure ψ z := by
  have h : ∃ μ : Measure (PrimeEnd D), ∀ φ : HChart D, chartMeasure φ z = μ :=
    ⟨chartMeasure ψ z, fun φ => chartMeasure_eq hD ψ φ hz⟩
  rw [harmonicMeasure]
  simp only [h, ↓reduceDIte]
  exact (h.choose_spec ψ).symm

/-- The harmonic measure of any set of prime ends, in a chart. -/
theorem harmonicMeasure_apply (hD : IsOpen D) {z : ℂ} (hz : z ∈ D) (ψ : HChart D)
    (S : Set (PrimeEnd D)) :
    harmonicMeasure D z S = harmonicMeasureH (ψ.1 z) (chartBdry ψ ⁻¹' S) := by
  rw [harmonicMeasure_eq_chartMeasure hD hz ψ, chartMeasure,
    (measurableEmbedding_chartBdry hD ψ).map_apply]

theorem harmonicMeasure_chartBdry_image (hD : IsOpen D) {z : ℂ} (hz : z ∈ D) (ψ : HChart D)
    (T : Set ℝ) : harmonicMeasure D z (chartBdry ψ '' T) = harmonicMeasureH (ψ.1 z) T := by
  rw [harmonicMeasure_apply hD hz ψ,
    preimage_image_eq _ (measurableEmbedding_chartBdry hD ψ).injective]

/-- The prime end at the point `∞` of a chart is null. -/
theorem harmonicMeasure_mk_infty (hD : IsOpen D) {z : ℂ} (hz : z ∈ D) (ψ : HChart D) :
    harmonicMeasure D z {mk ψ OnePoint.infty} = 0 := by
  rw [harmonicMeasure_apply hD hz ψ]
  convert measure_empty (μ := harmonicMeasureH (ψ.1 z))
  ext x
  simp only [mem_preimage, mem_singleton_iff, chartBdry, mem_empty_iff_false, iff_false]
  intro h
  exact OnePoint.coe_ne_infty x (mk_injective ψ h)

/-- The identity chart of `ℍ`. -/
def chartH : HChart H := ⟨id, differentiableOn_id, bijOn_id H⟩

/-- On `ℍ` itself, in the identity chart, the prime-end harmonic measure is `ω_ℍ`. -/
theorem harmonicMeasure_H_chartBdry_image {z : ℂ} (hz : z ∈ H) (T : Set ℝ) :
    harmonicMeasure H z (chartBdry chartH '' T) = harmonicMeasureH z T :=
  harmonicMeasure_chartBdry_image QuantumZipper.isOpen_H hz chartH T

theorem isProbabilityMeasure_harmonicMeasure (hD : IsOpen D) [Nonempty (HChart D)] {z : ℂ}
    (hz : z ∈ D) : IsProbabilityMeasure (harmonicMeasure D z) := by
  obtain ⟨ψ⟩ := ‹Nonempty (HChart D)›
  have := isProbabilityMeasure_harmonicMeasureH (ψ.mapsTo hz)
  rw [harmonicMeasure_eq_chartMeasure hD hz ψ, chartMeasure]
  exact (Measure.isProbabilityMeasure_map_iff
    (continuous_chartBdry hD ψ).measurable.aemeasurable).2 this

/-- Without a chart there are no prime ends, and the harmonic measure is `0`. -/
theorem harmonicMeasure_eq_zero_of_isEmpty (h : IsEmpty (HChart D)) (z : ℂ) :
    harmonicMeasure D z = 0 := by
  have := isEmpty_of_isEmpty_hChart h
  exact Subsingleton.elim _ _

theorem harmonicMeasure_le_one (hD : IsOpen D) {z : ℂ} (hz : z ∈ D) (S : Set (PrimeEnd D)) :
    harmonicMeasure D z S ≤ 1 := by
  rcases isEmpty_or_nonempty (HChart D) with h | h
  · simp [harmonicMeasure_eq_zero_of_isEmpty h]
  · have := isProbabilityMeasure_harmonicMeasure hD hz
    exact prob_le_one

/-! ### Conformal invariance -/

section Conformal

variable {E : Set ℂ} {f : ℂ → ℂ}

/-- A chart of `E` composed with a conformal bijection `f : D → E` is a chart of `D`. -/
def _root_.InteractingSLE.HChart.comp (ψ : HChart E) (hf : IsConformalBijection f D E) :
    HChart D :=
  ⟨ψ.1 ∘ f, ψ.differentiableOn.comp hf.1 hf.2.mapsTo, ψ.bijOn.comp hf.2⟩

@[simp] theorem _root_.InteractingSLE.HChart.comp_apply (ψ : HChart E)
    (hf : IsConformalBijection f D E) (z : ℂ) : (ψ.comp hf).1 z = ψ.1 (f z) := rfl

/-- The map of prime ends induced by a conformal bijection `f : D → E`, in the direction
`PrimeEnd E → PrimeEnd D`: the prime end marked by `x` in the chart `ψ` of `E` goes to the one
marked by `x` in the chart `ψ ∘ f` of `D`. -/
def pullback (hf : IsConformalBijection f D E) : PrimeEnd E → PrimeEnd D :=
  Quot.lift (fun q : HChart E × OnePoint ℝ => mk (q.1.comp hf) q.2) fun p q hpq => by
    obtain ⟨a, b, c, d, hdet, hEq, hbd⟩ := hpq
    exact Quot.sound ⟨a, b, c, d, hdet, fun z hz => hEq (hf.2.mapsTo hz), hbd⟩

@[simp] theorem pullback_mk (hf : IsConformalBijection f D E) (ψ : HChart E) (x : OnePoint ℝ) :
    pullback hf (mk ψ x) = mk (ψ.comp hf) x := rfl

theorem continuous_pullback (hD : IsOpen D) (hE : IsOpen E) (hf : IsConformalBijection f D E) :
    Continuous (pullback hf) := by
  rcases isEmpty_or_nonempty (HChart E) with h | ⟨⟨ψ⟩⟩
  · have := isEmpty_of_isEmpty_hChart h
    exact continuous_of_discreteTopology
  · have heq : pullback hf = mk (ψ.comp hf) ∘ (mkHomeomorph hE ψ).symm := by
      funext p
      obtain ⟨x, rfl⟩ := mk_surjective_of_isOpen hE ψ p
      have : (mkHomeomorph hE ψ).symm (mk ψ x) = x := (mkHomeomorph hE ψ).symm_apply_apply x
      simp [this]
    rw [heq]
    exact (continuous_mk hD _).comp (mkHomeomorph hE ψ).symm.continuous

/-- **Conformal invariance of harmonic measure**: for a conformal bijection `f : D → E` of open
domains and `z ∈ D`, `ω_D(z, ·)` is the image of `ω_E(f z, ·)` under the induced map of prime
ends. -/
theorem harmonicMeasure_eq_map_pullback (hD : IsOpen D) (hE : IsOpen E)
    (hf : IsConformalBijection f D E) [Nonempty (HChart E)] {z : ℂ} (hz : z ∈ D) :
    harmonicMeasure D z = (harmonicMeasure E (f z)).map (pullback hf) := by
  obtain ⟨ψ⟩ := ‹Nonempty (HChart E)›
  rw [harmonicMeasure_eq_chartMeasure hE (hf.2.mapsTo hz) ψ,
    harmonicMeasure_eq_chartMeasure hD hz (ψ.comp hf), chartMeasure, chartMeasure,
    Measure.map_map (continuous_pullback hD hE hf).measurable
      (continuous_chartBdry hE ψ).measurable]
  rfl

theorem harmonicMeasure_preimage_pullback (hD : IsOpen D) (hE : IsOpen E)
    (hf : IsConformalBijection f D E) [Nonempty (HChart E)] {z : ℂ} (hz : z ∈ D)
    {S : Set (PrimeEnd D)} (hS : MeasurableSet S) :
    harmonicMeasure E (f z) (pullback hf ⁻¹' S) = harmonicMeasure D z S := by
  rw [harmonicMeasure_eq_map_pullback hD hE hf hz,
    Measure.map_apply (continuous_pullback hD hE hf).measurable hS]

end Conformal

/-! ### Harmonicity -/

section Harmonic

/-- `ω_ℍ(z, T)` as a real number is the integral of the Poisson kernel over `T`. -/
theorem toReal_harmonicMeasureH (T : Set ℝ) {z : ℂ} (hz : z ∈ H) :
    (harmonicMeasureH z T).toReal = ∫ x in T, poissonKernelH z x := by
  rw [harmonicMeasureH, withDensity_apply' _ T,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_poissonKernelH hz).integrableOn
      (ae_of_all _ fun x => (poissonKernelH_pos hz x).le),
    ENNReal.toReal_ofReal (setIntegral_nonneg_of_ae (ae_of_all _ fun x =>
      (poissonKernelH_pos hz x).le))]

/-- `ω_ℍ(z, T)` agrees with QuantumZipper's `lwHarmOm T z` on `ℍ`. -/
theorem toReal_harmonicMeasureH_eq_lwHarmOm (T : Set ℝ) {z : ℂ} (hz : z ∈ H) :
    (harmonicMeasureH z T).toReal = QuantumZipper.Thm18Asm.LWFar.lwHarmOm T z := by
  rw [toReal_harmonicMeasureH T hz, poissonKernelH_eq_cauchyPDFReal' hz]
  rfl

theorem memLp_top_indicator_one {T : Set ℝ} (hT : MeasurableSet T) :
    MemLp (T.indicator fun _ => (1 : ℝ)) ∞ (volume : Measure ℝ) :=
  memLp_top_of_bound ((measurable_const.indicator hT).aestronglyMeasurable) 1
    (ae_of_all _ fun x => by by_cases hx : x ∈ T <;> simp [Set.indicator, hx])

/-- The indicator of a measurable set as an element of `L^∞`. -/
def indicatorLpTop {T : Set ℝ} (hT : MeasurableSet T) : Lp ℝ ∞ (volume : Measure ℝ) :=
  (memLp_top_indicator_one hT).toLp _

theorem poissonIntegralH_indicatorLpTop {T : Set ℝ} (hT : MeasurableSet T) {z : ℂ}
    (hz : z ∈ H) : poissonIntegralH (indicatorLpTop hT) z = (harmonicMeasureH z T).toReal := by
  rw [toReal_harmonicMeasureH T hz, poissonIntegralH, ← integral_indicator hT]
  refine integral_congr_ae ?_
  filter_upwards [(memLp_top_indicator_one hT).coeFn_toLp] with x hx
  rw [indicatorLpTop, hx]
  by_cases hxT : x ∈ T <;> simp [Set.indicator, hxT]

/-- `z ↦ ω_ℍ(z, T)` is harmonic on `ℍ`. -/
theorem harmonicOnNhd_harmonicMeasureH {T : Set ℝ} (hT : MeasurableSet T) :
    InnerProductSpace.HarmonicOnNhd (fun z => (harmonicMeasureH z T).toReal) H := by
  intro z hz
  have hev : poissonIntegralH (indicatorLpTop hT) =ᶠ[𝓝 z]
      fun z => (harmonicMeasureH z T).toReal := by
    filter_upwards [QuantumZipper.isOpen_H.mem_nhds hz] with w hw
    exact poissonIntegralH_indicatorLpTop hT hw
  exact (InnerProductSpace.harmonicAt_congr_nhds hev).1
    (harmonicOnNhd_poissonIntegralH (indicatorLpTop hT) z hz)

/-- `z ↦ ω_D(z, S)` is harmonic on an open domain `D`, for measurable `S`. -/
theorem harmonicOnNhd_harmonicMeasure (hD : IsOpen D) {S : Set (PrimeEnd D)}
    (hS : MeasurableSet S) :
    InnerProductSpace.HarmonicOnNhd (fun z => (harmonicMeasure D z S).toReal) D := by
  rcases isEmpty_or_nonempty (HChart D) with h | ⟨⟨ψ⟩⟩
  · simp only [harmonicMeasure_eq_zero_of_isEmpty h, Measure.coe_zero, Pi.zero_apply,
      ENNReal.toReal_zero]
    intro z _
    exact InnerProductSpace.harmonicAt_const 0
  · have hT : MeasurableSet (chartBdry ψ ⁻¹' S) :=
      (continuous_chartBdry hD ψ).measurable hS
    have hcomp := LQGMetric.harmonicOnNhd_comp_holo QuantumZipper.isOpen_H hD
      (harmonicOnNhd_harmonicMeasureH hT) ψ.differentiableOn ψ.mapsTo
    intro z hz
    have hev : ((fun ζ => (harmonicMeasureH ζ (chartBdry ψ ⁻¹' S)).toReal) ∘ ψ.1) =ᶠ[𝓝 z]
        fun z => (harmonicMeasure D z S).toReal := by
      filter_upwards [hD.mem_nhds hz] with w hw
      simp only [comp_apply, harmonicMeasure_apply hD hw ψ]
    exact (InnerProductSpace.harmonicAt_congr_nhds hev).1 (hcomp z hz)

end Harmonic

/-! ### Impressions and boundary decay -/

section Decay

/-- The **impression** of a prime end: the cluster set of the inverse of a chart at the marked
boundary point (Pommerenke, *Boundary Behaviour of Conformal Maps*, §2.5). It does not depend on
the chart (`mem_impression_mk_iff`). -/
def impression (p : PrimeEnd D) : Set ℂ :=
  {w | ∃ ψ : HChart D, ∃ x : OnePoint ℝ, mk ψ x = p ∧
    MapClusterPt w (approachH x) (invFunOn ψ.1 D)}

/-- Chart independence of the impression (any `D`). -/
theorem mem_impression_mk_iff (ψ : HChart D) (x : OnePoint ℝ) (w : ℂ) :
    w ∈ (mk ψ x).impression ↔ MapClusterPt w (approachH x) (invFunOn ψ.1 D) := by
  refine ⟨fun ⟨φ, y, hφy, hcl⟩ => ?_, fun h => ⟨ψ, x, rfl, h⟩⟩
  obtain ⟨a, b, c, d, hdet, hEq, hbd⟩ := mk_eq_mk_iff.1 hφy
  have hev : invFunOn φ.1 D =ᶠ[approachH y] (invFunOn ψ.1 D ∘ realMobius a b c d) := by
    filter_upwards [H_mem_approachH y] with ζ hζ
    exact φ.invFunOn_eq_invFunOn_realMobius ψ hEq hζ
  have hle : map (invFunOn φ.1 D) (approachH y) ≤ map (invFunOn ψ.1 D) (approachH x) := by
    rw [map_congr hev, ← map_map]
    refine map_mono ?_
    have := tendsto_realMobius_approachH hdet y
    rwa [hbd] at this
  exact ClusterPt.mono hcl hle

/-- The inverse of a chart of an open domain is continuous on `ℍ`. -/
theorem continuousAt_invFunOn (hD : IsOpen D) (ψ : HChart D) {ζ : ℂ} (hζ : ζ ∈ H) :
    ContinuousAt (invFunOn ψ.1 D) ζ := by
  set e := QuantumZipper.CA.univalentOPH hD ψ.differentiableOn ψ.injOn
  have himg : ψ.1 '' D = H := ψ.bijOn.image_eq
  have htarget : e.target = H := by
    rw [QuantumZipper.CA.univalentOPH_target, himg]
  have hev : e.symm =ᶠ[𝓝 ζ] invFunOn ψ.1 D := by
    filter_upwards [QuantumZipper.isOpen_H.mem_nhds hζ] with ξ hξ
    have hξt : ξ ∈ e.target := htarget ▸ hξ
    have hmem : e.symm ξ ∈ D := e.map_target hξt
    have happ : ψ.1 (e.symm ξ) = ξ :=
      QuantumZipper.CA.univalentOPH_apply_symm_apply hD ψ.differentiableOn ψ.injOn
        (by rw [himg]; exact hξ)
    exact ψ.injOn hmem (ψ.invFunOn_mem hξ) (by rw [happ, ψ.apply_invFunOn hξ])
  exact (e.continuousAt_symm (htarget ▸ hζ)).congr hev

/-- Half-plane harmonic measure of the real points of a closed set of `ℝ ∪ {∞}` tends to `0` at
every boundary point outside it. -/
theorem tendsto_harmonicMeasureH_approachH {S' : Set (OnePoint ℝ)} (hS' : IsClosed S')
    {t : OnePoint ℝ} (ht : t ∉ S') :
    Tendsto (fun ζ => (harmonicMeasureH ζ (((↑) : ℝ → OnePoint ℝ) ⁻¹' S')).toReal)
      (approachH t) (𝓝 0) := by
  set T : Set ℝ := ((↑) : ℝ → OnePoint ℝ) ⁻¹' S' with hTdef
  have hTc : IsClosed T := hS'.preimage OnePoint.continuous_coe
  have hcongr : (fun ζ => QuantumZipper.Thm18Asm.LWFar.lwHarmOm T ζ) =ᶠ[approachH t]
      fun ζ => (harmonicMeasureH ζ T).toReal := by
    filter_upwards [H_mem_approachH t] with ζ hζ
    exact (toReal_harmonicMeasureH_eq_lwHarmOm T hζ).symm
  refine Tendsto.congr' hcongr ?_
  induction t using OnePoint.rec with
  | infty =>
    have hopen : IsOpen S'ᶜ := hS'.isOpen_compl
    have hcpt : IsCompact T := by
      have := ((OnePoint.isOpen_iff_of_mem ht).1 hopen).2
      simpa [hTdef] using this
    obtain ⟨r, hr⟩ := hcpt.isBounded.subset_closedBall 0
    set R := max r 1
    have hR : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
    have hTR : T ⊆ Icc (-R) R := fun x hx => by
      have := hr hx
      rw [Real.closedBall_eq_Icc, zero_sub, zero_add] at this
      exact ⟨le_trans (neg_le_neg (le_max_left _ _)) this.1, this.2.trans (le_max_left _ _)⟩
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨M, hM⟩ := QuantumZipper.Thm18Asm.LWFar.lwHarm_small_far hR hTR hε
    rw [approachH_infty]
    have h1 : ∀ᶠ ζ in Bornology.cobounded ℂ, M < ‖ζ‖ :=
      tendsto_norm_cobounded_atTop.eventually_gt_atTop M
    filter_upwards [inf_le_left (b := 𝓟 H) h1, inf_le_right (a := Bornology.cobounded ℂ)
      (mem_principal_self H)] with ζ hζM hζH
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (QuantumZipper.Thm18Asm.LWFar.lwHarm_nonneg _ _)]
    exact hM ζ hζH hζM
  | coe r =>
    have hr : r ∉ T := ht
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hTc.isOpen_compl r hr
    rw [approachH_coe]
    refine QuantumZipper.Thm18Asm.LWFar.lwHarm_tendsto_zero hTc.measurableSet hδ fun x hx => ?_
    by_contra hlt
    push Not at hlt
    exact hball (show dist x r < δ by rwa [Real.dist_eq]) hx

/-- **Boundary decay**: on an open domain, `ω_D(z, S) → 0` as `z → x₀ ∈ ∂D` inside `D`, if `S`
is closed and `x₀` lies in no impression of a prime end of `S`. -/
theorem tendsto_harmonicMeasure_nhdsWithin (hD : IsOpen D) {S : Set (PrimeEnd D)}
    (hS : IsClosed S) {x₀ : ℂ} (hx₀ : x₀ ∈ frontier D) (himp : ∀ p ∈ S, x₀ ∉ p.impression) :
    Tendsto (fun z => (harmonicMeasure D z S).toReal) (𝓝[D] x₀) (𝓝 0) := by
  rcases isEmpty_or_nonempty (HChart D) with h | ⟨⟨ψ⟩⟩
  · simp only [harmonicMeasure_eq_zero_of_isEmpty h, Measure.coe_zero, Pi.zero_apply,
      ENNReal.toReal_zero]
    exact tendsto_const_nhds
  have hx₀D : x₀ ∉ D := fun h => by
    rw [hD.frontier_eq] at hx₀
    exact hx₀.2 h
  set S' : Set (OnePoint ℝ) := mk ψ ⁻¹' S with hS'def
  have hS' : IsClosed S' := hS.preimage (continuous_mk hD ψ)
  set g : ℂ → ℂ → ℝ := fun _ ζ => (harmonicMeasureH ζ (((↑) : ℝ → OnePoint ℝ) ⁻¹' S')).toReal
  have hfun : ∀ z ∈ D, (harmonicMeasure D z S).toReal = g z (ψ.1 z) := fun z hz => by
    rw [harmonicMeasure_apply hD hz ψ]
    rfl
  set inv := invFunOn ψ.1 D
  have hinvψ : ∀ᶠ z in 𝓝[D] x₀, inv (ψ.1 z) = z := by
    filter_upwards [self_mem_nhdsWithin] with z hz using ψ.invFunOn_apply hz
  refine tendsto_order.2 ⟨fun a ha => Eventually.of_forall fun z => ha.trans_le
    ENNReal.toReal_nonneg, fun ε hε => ?_⟩
  by_contra hne
  rw [not_eventually] at hne
  set F := 𝓝[D] x₀ ⊓ 𝓟 {z | ¬ (harmonicMeasure D z S).toReal < ε} with hFdef
  have hF : F.NeBot := frequently_iff_neBot.1 hne
  have hFle : F ≤ 𝓝[D] x₀ := inf_le_left
  have hFD : D ∈ F := hFle self_mem_nhdsWithin
  have hmapH : H ∈ map ψ.1 F := mem_map.2 (mem_of_superset hFD fun z hz => ψ.mapsTo hz)
  have hinvF : map inv (map ψ.1 F) = F := by
    rw [map_map]
    refine (map_congr ?_).trans map_id
    filter_upwards [hFD] with z hz using ψ.invFunOn_apply hz
  -- a boundary point `t` of `ℍ` at which `ψ` accumulates along `F`
  obtain ⟨t, ht⟩ : ∃ t : OnePoint ℝ, (map ψ.1 F ⊓ approachH t).NeBot := by
    by_cases hc : (map ψ.1 F ⊓ Bornology.cobounded ℂ).NeBot
    · refine ⟨OnePoint.infty, ?_⟩
      rw [approachH_infty, ← inf_assoc, inf_right_comm, inf_of_le_left (le_principal_iff.2 hmapH)]
      exact hc
    · rw [not_neBot, inf_eq_bot_iff] at hc
      obtain ⟨U, hU, V, hV, hUV⟩ := hc
      have hVb : Bornology.IsBounded Vᶜ := Bornology.isBounded_compl_iff.2 hV
      have hUV' : U ⊆ closure Vᶜ := fun x hx => subset_closure fun hxV =>
        (Set.eq_empty_iff_forall_notMem.1 hUV) x ⟨hx, hxV⟩
      have hmapF : (map ψ.1 F).NeBot := hF.map _
      obtain ⟨ζ, -, hζ⟩ := hVb.isCompact_closure (f := map ψ.1 F)
        (le_principal_iff.2 (mem_of_superset hU hUV'))
      have hζim : 0 ≤ ζ.im := by
        have hcl := hζ.mem_closure_of_mem H hmapH
        have hsub : closure H ⊆ {w : ℂ | 0 ≤ w.im} :=
          closure_minimal (fun w (hw : w ∈ H) => show 0 ≤ w.im from le_of_lt hw)
            (isClosed_le continuous_const Complex.continuous_im)
        exact hsub hcl
      rcases hζim.lt_or_eq with hpos | hzero
      · exfalso
        have hcl := hζ.map (continuousAt_invFunOn hD ψ hpos) (tendsto_map (f := inv))
        rw [hinvF] at hcl
        have hcl' : ClusterPt (inv ζ) (𝓝 x₀) := hcl.mono (hFle.trans nhdsWithin_le_nhds)
        have heq : inv ζ = x₀ := by
          by_contra hneq
          exact (ClusterPt.neBot hcl').ne (disjoint_iff.1 (disjoint_nhds_nhds.2 hneq))
        exact hx₀D (heq ▸ ψ.invFunOn_mem hpos)
      · refine ⟨(ζ.re : OnePoint ℝ), ?_⟩
        have hζre : ((ζ.re : ℝ) : ℂ) = ζ := by
          apply Complex.ext <;> simp [hzero]
        rw [approachH_coe, hζre, nhdsWithin, ← inf_assoc, inf_right_comm,
          inf_of_le_left (le_principal_iff.2 hmapH), inf_comm]
        exact hζ
  by_cases hp : mk ψ t ∈ S
  · apply himp _ hp
    rw [mem_impression_mk_iff]
    refine NeBot.mono (ht.map inv) (le_inf ?_ (map_mono inf_le_right))
    calc map inv (map ψ.1 F ⊓ approachH t) ≤ map inv (map ψ.1 F) := map_mono inf_le_left
      _ = F := hinvF
      _ ≤ 𝓝 x₀ := hFle.trans nhdsWithin_le_nhds
  · have hlim := tendsto_harmonicMeasureH_approachH hS' (t := t) hp
    have h1 : ∀ᶠ ζ in approachH t, g x₀ ζ < ε := hlim.eventually (gt_mem_nhds hε)
    have h2 : ∀ᶠ ζ in map ψ.1 F, ¬ g x₀ ζ < ε := by
      rw [eventually_map]
      filter_upwards [hFD, inf_le_right (a := 𝓝[D] x₀) (mem_principal_self _)] with z hz hz'
      rw [← hfun z hz]
      exact hz'
    obtain ⟨ζ, hζ1, hζ2⟩ := ((h1.filter_mono inf_le_right).and
      (h2.filter_mono inf_le_left)).exists
    exact hζ2 hζ1

/-- The impression of a prime end with a Euclidean realization `w` is `{w}`. -/
theorem IsRealizedAt.impression_eq {p : PrimeEnd D} {w : ℂ} (hw : p.IsRealizedAt w) :
    p.impression = {w} := by
  obtain ⟨ψ, x, rfl, hT⟩ := hw
  have := approachH_neBot x
  ext y
  rw [mem_impression_mk_iff, mem_singleton_iff, MapClusterPt]
  refine ⟨fun hy => ?_, fun hy => hy ▸ ClusterPt.of_le_nhds hT⟩
  by_contra hne
  exact (ClusterPt.neBot (hy.mono hT)).ne (disjoint_iff.1 (disjoint_nhds_nhds.2 hne))

end Decay

/-! ### The Beurling estimate -/

/-- **Beurling estimate** in harmonic-measure form (Garnett–Marshall, *Harmonic Measure*,
Thm III.9.2; Lawler, *Conformally Invariant Processes in the Plane*, Thm 3.69): there is a
universal `C` such that, if `D` is open, `w ∈ D`, `0 < d ≤ ρ`, and a continuum `K` disjoint from
`D` meets `closedBall w d` and the complement of `ball w ρ`, then every set `S` of prime ends of
`D` whose closure has impressions disjoint from `ball w ρ` has harmonic measure
`ω_D(w, S) ≤ C (d/ρ)^{1/2}` from `w`. Proof: QuantumZipper's analytic Beurling estimate
`beurlingHarmStmt_holds` applied to `z ↦ ω_D(z, closure S)` (harmonic, in `[0, 1]`, and
vanishing at `∂D ∩ ball w ρ` by `tendsto_harmonicMeasure_nhdsWithin`). -/
theorem harmonicMeasure_le_beurling : ∃ C : ℝ, 0 ≤ C ∧ ∀ (D K : Set ℂ) (w : ℂ) (d ρ : ℝ)
    (S : Set (PrimeEnd D)), IsOpen D → w ∈ D → 0 < d → d ≤ ρ → IsConnected K →
    Disjoint K D → (K ∩ closedBall w d).Nonempty → (K \ ball w ρ).Nonempty →
    (∀ p ∈ closure S, Disjoint p.impression (ball w ρ)) →
    harmonicMeasure D w S ≤ ENNReal.ofReal (C * (d / ρ) ^ (1 / 2 : ℝ)) := by
  obtain ⟨C, hC, hB⟩ := QuantumZipper.Thm18Asm.LWFar.beurlingHarmStmt_holds
  refine ⟨C, hC, fun D K w d ρ S hD hw hd hdρ hK hKD hKd hKρ himp => ?_⟩
  set h : ℂ → ℝ := fun x => (harmonicMeasure D x (closure S)).toReal with hdef
  have hVD : connectedComponentIn (D ∩ ball w ρ) w ⊆ D :=
    (connectedComponentIn_subset _ _).trans inter_subset_left
  have hharm : InnerProductSpace.HarmonicOnNhd h (connectedComponentIn (D ∩ ball w ρ) w) :=
    fun x hx => harmonicOnNhd_harmonicMeasure hD isClosed_closure.measurableSet x (hVD hx)
  have hle1 : ∀ x ∈ D, harmonicMeasure D x (closure S) ≤ 1 := fun x hx =>
    harmonicMeasure_le_one hD hx _
  have hbnd : ∀ x ∈ connectedComponentIn (D ∩ ball w ρ) w, 0 ≤ h x ∧ h x ≤ 1 := fun x hx =>
    ⟨ENNReal.toReal_nonneg, ENNReal.toReal_le_of_le_ofReal zero_le_one
      (by rw [ENNReal.ofReal_one]; exact hle1 x (hVD hx))⟩
  have hdecay : ∀ x₀ ∈ frontier D ∩ ball w ρ, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ connectedComponentIn (D ∩ ball w ρ) w, dist x x₀ < δ → h x ≤ ε := by
    intro x₀ hx₀ ε hε
    have hlim := tendsto_harmonicMeasure_nhdsWithin hD isClosed_closure hx₀.1
      fun p hp hmem => Set.disjoint_left.1 (himp p hp) hmem hx₀.2
    obtain ⟨δ, hδ, hδ'⟩ := Metric.tendsto_nhdsWithin_nhds.1 hlim ε hε
    refine ⟨δ, hδ, fun x hx hxd => ?_⟩
    have := hδ' (hVD hx) hxd
    rw [Real.dist_eq, sub_zero] at this
    exact (le_abs_self _).trans this.le
  have hw' := hB D K w d ρ h hD hw hd hdρ hK hKD hKd hKρ hharm hbnd hdecay
  calc harmonicMeasure D w S ≤ harmonicMeasure D w (closure S) := measure_mono subset_closure
    _ = ENNReal.ofReal (h w) :=
      (ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top (hle1 w hw))).symm
    _ ≤ ENNReal.ofReal (C * (d / ρ) ^ (1 / 2 : ℝ)) := ENNReal.ofReal_le_ofReal hw'

end PrimeEnd

end InteractingSLE
