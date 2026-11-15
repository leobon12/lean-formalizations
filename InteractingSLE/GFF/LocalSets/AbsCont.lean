import InteractingSLE.GFF.LocalSets.Basic
import InteractingSLE.Foundations.Complex.RiemannMap
import SupercriticalConformalCovariance.ZBConformal.Covariance
import LQGMetric.Field.ZeroBoundaryAffine

/-!
# Absolute continuity of the GFF on subdomains (specification Proposition 3.4)

Source: `source/ig1-specification.pdf`, §3.1, Proposition 3.4 (p. 46; transcription
`source/spec/p001-048.md#prop-3.4`, proof `#prop-3.4-proof`, pp. 47–48): for simply connected
domains `D₁, D₂` with zero-boundary GFFs `hᵢ`, harmonic `Fᵢ` on `Dᵢ` and a bounded simply connected
open `U ⊆ D₁ ∩ D₂`,

(i) (interior) if `dist(U, ∂Dᵢ) > 0` for `i = 1, 2`, the laws of `(h₁ + F₁)|_U` and
`(h₂ + F₂)|_U` are mutually absolutely continuous.

## Main results

* `map_restrictAdd_absolutelyContinuous` : (i) for admissible open `D₁, D₂` (no simple
  connectivity needed) and bounded open `U` with `cl U ⊆ D₁ ∩ D₂`, one direction;
* `zbAdmissible_of_isSimplyConnected` : a simply connected domain `D ≠ ℂ` is admissible (Riemann
  map to the disk and conformal invariance of the dual Dirichlet norm), i.e. its zero-boundary GFF
  exists;
* `closure_subset_of_dist_frontier` : `dist(U, ∂D) > 0` and `U ⊆ D` give `cl U ⊆ D`;
* **`map_restrictAdd_mutuallyAbsCont_interior`** : Proposition 3.4 (i) with the source's hypotheses.

## Proof (the source's argument, with a deterministic shift)

`W = D₁ ∩ D₂`. By Proposition 3.1 (`InteractingSLE.GFF.exists_markovMap`), `(hᵢ + Fᵢ)|_U =
Zᵢ|_U + Yᵢ` with `Zᵢ` a zero-boundary GFF on `W` and `Yᵢ` independent of `Zᵢ`, almost surely a
harmonic function on `W`. The `Zᵢ` have the same law. For harmonic `u, u'` on `W` and a cut-off
`χ ∈ C_c^∞(W)`, `χ = 1` on `cl U`, the shift `χ (u − u')` is a Cameron–Martin shift, so
`law(Z|_U + u) ≪ law(Z|_U + u')`. Mixing over the independent `Yᵢ` (Fubini) gives the claim: an
event null for `(h₂ + F₂)|_U` is null for a translate `Z|_U + y₀`, hence for every harmonic
translate, hence for `(h₁ + F₁)|_U`. The source's random shift `g` is not needed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set TopologicalSpace Metric
open LQGMetric
open SupercriticalConformalCovariance.GM24 (smoothDist)

namespace InteractingSLE
namespace GFF

/-- **Proposition 3.4 (i) (interior absolute continuity), general form.** Let `D₁, D₂` be
admissible open sets (every test function has finite `H⁻¹` norm, e.g. any open subset of `ℍ`),
`hᵢ` a zero-boundary GFF on `Dᵢ`, `Fᵢ` harmonic on `Dᵢ`, and `U` a bounded open set with
`cl U ⊆ D₁ ∩ D₂`. Then the law of `(h₁ + F₁)|_U` is absolutely continuous with respect to the law
of `(h₂ + F₂)|_U`. -/
theorem map_restrictAdd_absolutelyContinuous {D₁ D₂ U : Opens ℂ} (hD₁ : ZBAdmissible D₁)
    (hD₂ : ZBAdmissible D₂) (hUb : Bornology.IsBounded (U : Set ℂ))
    (hU₁ : closure (U : Set ℂ) ⊆ D₁) (hU₂ : closure (U : Set ℂ) ⊆ D₂)
    {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] {P₁ : Measure Ω₁}
    {P₂ : Measure Ω₂} [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
    {h₁ : Ω₁ → DistOn D₁} {h₂ : Ω₂ → DistOn D₂} (hh₁ : IsZeroBoundaryGFF D₁ h₁ P₁)
    (hh₂ : IsZeroBoundaryGFF D₂ h₂ P₂) {F₁ F₂ : ℂ → ℝ}
    (hF₁ : InnerProductSpace.HarmonicOnNhd F₁ D₁) (hF₂ : InnerProductSpace.HarmonicOnNhd F₂ D₂) :
    P₁.map (fun ω => restrictAdd U (h₁ ω) F₁) ≪ P₂.map (fun ω => restrictAdd U (h₂ ω) F₂) := by
  set W : Opens ℂ := D₁ ⊓ D₂
  have hW : ZBAdmissible W := zbAdmissible_mono inf_le_left hD₁
  have hUW : closure (U : Set ℂ) ⊆ W := subset_inter hU₁ hU₂
  have hUW' : U ≤ W := fun x hx => hUW (subset_closure hx)
  obtain ⟨Z₁, Y₁, hZ₁, hY₁, hi₁, hS₁, he₁⟩ :=
    exists_restrictAdd_decomposition inf_le_left hUW' hD₁ hh₁ hF₁
  obtain ⟨Z₂, Y₂, hZ₂, hY₂, hi₂, hS₂, he₂⟩ :=
    exists_restrictAdd_decomposition inf_le_right hUW' hD₂ hh₂ hF₂
  have hR := measurable_restrictDist U (D := W)
  have hlaw : P₁.map (fun ω => restrictDist U (Z₁ ω)) =
      P₂.map (fun ω => restrictDist U (Z₂ ω)) := by
    calc P₁.map (fun ω => restrictDist U (Z₁ ω)) = (P₁.map Z₁).map (restrictDist U) :=
          (Measure.map_map hR hZ₁.measurable).symm
      _ = (P₂.map Z₂).map (restrictDist U) := by rw [hZ₁.map_eq hZ₂]
      _ = _ := Measure.map_map hR hZ₂.measurable
  have e₁ : (fun ω => restrictAdd U (h₁ ω) F₁) = fun ω => restrictDist U (Z₁ ω) + Y₁ ω :=
    funext he₁
  have e₂ : (fun ω => restrictAdd U (h₂ ω) F₂) = fun ω => restrictDist U (Z₂ ω) + Y₂ ω :=
    funext he₂
  rw [e₁, e₂]
  refine map_add_absolutelyContinuous_of_indepFun (measurable_add_distOn U)
    (hR.comp hZ₁.measurable) hY₁ (hR.comp hZ₂.measurable) hY₂ hi₁ hi₂ hlaw
    {y | ∃ u : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd u W ∧ y = smoothDist U u}
    ?_ hS₁ hS₂
  rintro _ ⟨u, hu, rfl⟩ _ ⟨u', hu', rfl⟩
  have hsh : ∀ y : DistOn U, Measurable fun x : DistOn U => x + y := fun y =>
    (measurable_add_distOn U).comp (measurable_id.prodMk measurable_const)
  have hZR : Measurable fun ω => restrictDist U (Z₁ ω) := hR.comp hZ₁.measurable
  rw [Measure.map_map (hsh _) hZR, Measure.map_map (hsh _) hZR]
  exact map_restrict_add_harmonic_absolutelyContinuous hW hUb hUW hZ₁ hu hu'

/-- A simply connected domain `D ≠ ℂ` is admissible: every test function has finite `H⁻¹(D)` norm,
so the zero-boundary GFF on `D` exists. -/
theorem zbAdmissible_of_isSimplyConnected {D : Opens ℂ} (hDc : IsConnected (D : Set ℂ))
    (hDs : IsSimplyConnected (D : Set ℂ)) (hDne : (D : Set ℂ) ≠ univ) : ZBAdmissible D := by
  obtain ⟨z₀, hz₀⟩ := hDc.nonempty
  obtain ⟨φ, hφ, -⟩ := exists_isConformalBijection_ball D.isOpen hDc hDs hDne hz₀
  exact SupercriticalConformalCovariance.ZBConformal.zbAdmissible_of_conf
    (V := ⟨ball 0 1, isOpen_ball⟩) hφ (zbAdmissible_of_isBounded isBounded_ball)

/-- If `U ⊆ D`, `D` open, and `U` has positive distance from `∂D`, then `cl U ⊆ D`. -/
theorem closure_subset_of_dist_frontier {U D : Set ℂ} (hD : IsOpen D) (hUD : U ⊆ D)
    (hdist : ∃ δ > 0, ∀ z ∈ U, ∀ w ∈ frontier D, δ ≤ dist z w) : closure U ⊆ D := by
  obtain ⟨δ, hδ, hd⟩ := hdist
  intro z hz
  by_contra hzD
  have hzf : z ∈ frontier D := by
    rw [frontier, hD.interior_eq]
    exact ⟨closure_mono hUD hz, hzD⟩
  obtain ⟨u, hu, hzu⟩ := Metric.mem_closure_iff.1 hz δ hδ
  have := hd u hu z hzf
  rw [dist_comm] at this
  linarith

/-- **Proposition 3.4 (i) (Absolute continuity, interior).** Let `D₁, D₂ ≠ ℂ` be simply connected
domains with `D₁ ∩ D₂ ≠ ∅`, `hᵢ` a zero-boundary GFF on `Dᵢ` (on any probability space), `Fᵢ`
harmonic on `Dᵢ`, and `U ⊆ D₁ ∩ D₂` a bounded simply connected domain with `dist(U, ∂Dᵢ) > 0`
for `i = 1, 2`. Then the laws of `(h₁ + F₁)|_U` and `(h₂ + F₂)|_U` (as random distributions on `U`)
are mutually absolutely continuous. (`Dᵢ ≠ ℂ` is the standing assumption of §3.1 under which the
zero-boundary GFF exists; the connectivity hypotheses and `D₁ ∩ D₂ ≠ ∅` are not used.) -/
theorem map_restrictAdd_mutuallyAbsCont_interior {D₁ D₂ U : Opens ℂ}
    (hD₁c : IsConnected (D₁ : Set ℂ)) (hD₁s : IsSimplyConnected (D₁ : Set ℂ))
    (hD₁ne : (D₁ : Set ℂ) ≠ univ) (hD₂c : IsConnected (D₂ : Set ℂ))
    (hD₂s : IsSimplyConnected (D₂ : Set ℂ)) (hD₂ne : (D₂ : Set ℂ) ≠ univ)
    (_h12 : ((D₁ : Set ℂ) ∩ D₂).Nonempty) (hUb : Bornology.IsBounded (U : Set ℂ))
    (_hUc : IsConnected (U : Set ℂ)) (_hUs : IsSimplyConnected (U : Set ℂ))
    (hUD : (U : Set ℂ) ⊆ (D₁ : Set ℂ) ∩ D₂)
    (hdist₁ : ∃ δ > 0, ∀ z ∈ (U : Set ℂ), ∀ w ∈ frontier (D₁ : Set ℂ), δ ≤ dist z w)
    (hdist₂ : ∃ δ > 0, ∀ z ∈ (U : Set ℂ), ∀ w ∈ frontier (D₂ : Set ℂ), δ ≤ dist z w)
    {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] {P₁ : Measure Ω₁}
    {P₂ : Measure Ω₂} [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
    {h₁ : Ω₁ → DistOn D₁} {h₂ : Ω₂ → DistOn D₂} (hh₁ : IsZeroBoundaryGFF D₁ h₁ P₁)
    (hh₂ : IsZeroBoundaryGFF D₂ h₂ P₂) {F₁ F₂ : ℂ → ℝ}
    (hF₁ : InnerProductSpace.HarmonicOnNhd F₁ D₁) (hF₂ : InnerProductSpace.HarmonicOnNhd F₂ D₂) :
    P₁.map (fun ω => restrictAdd U (h₁ ω) F₁) ≪ P₂.map (fun ω => restrictAdd U (h₂ ω) F₂) ∧
      P₂.map (fun ω => restrictAdd U (h₂ ω) F₂) ≪ P₁.map (fun ω => restrictAdd U (h₁ ω) F₁) := by
  have hA₁ := zbAdmissible_of_isSimplyConnected hD₁c hD₁s hD₁ne
  have hA₂ := zbAdmissible_of_isSimplyConnected hD₂c hD₂s hD₂ne
  have hU₁ := closure_subset_of_dist_frontier D₁.isOpen (hUD.trans inter_subset_left) hdist₁
  have hU₂ := closure_subset_of_dist_frontier D₂.isOpen (hUD.trans inter_subset_right) hdist₂
  exact ⟨map_restrictAdd_absolutelyContinuous hA₁ hA₂ hUb hU₁ hU₂ hh₁ hh₂ hF₁ hF₂,
    map_restrictAdd_absolutelyContinuous hA₂ hA₁ hUb hU₂ hU₁ hh₂ hh₁ hF₂ hF₁⟩

end GFF
end InteractingSLE
