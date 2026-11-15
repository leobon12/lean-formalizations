/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.MixtureA32Path
import InteractingSLE.Spec.Zhan.StripNoncollision

/-!
# A.3.2, (G3) for ordinary SLE in strip coordinates

Packet PROVE-ZHAN-A32. Source: Astra, *Follow-up proofs and dependency audit*, §A.3.2
(`source/external/AstraIG1/ig1_followup_proofs.txt` L657–L697, ruling R38): "By the target-change identity, ordinary
SLE stopped at `T_x` becomes the strip chain `ξ_t = √κ B_t + σ t`, `σ = 3 − κ/2 ∈ (−1, 1)`. The strip clock is
infinite … Consequently the original strip law is the mixture, with density `f(u)du`, of these forced laws."

In the R36 form a strip chain is the chordal evolution of the exponential image with an end mark `V` at `−1` (the image
of the left strip end; `Strip.IsStripSLEEvolution`). Ordinary chordal `SLE_κ` with the point `x = −1` (any `x < 0`
by scaling) is the strip evolution with no lower marks and end weight `τ₋ = 0`; its target charge is
`τ₊ = κ − 6`, so its strip driver is `√κ B̃ + (3 − κ/2) t` in strip time (PROVE-ZHAN-A2/A3's
`Zhan.exists_stripBrownian_of_prefixSums`, which also proves that the strip clock is infinite).

## Main results

* `mixLaw_eq_map_prod`, `mixLaw_eq_mixLaw`: the mixture of forced laws does not depend on the Brownian motion used to
  realize it (it is `(f(u) du ⊗ Wiener).map ξ̂`);
* `measure_stripPath_eq_zero_of_ae`: a measurable set of paths that is null for almost every forced law is null for the
  strip driver law (the form in which the mixture identity transfers almost-sure statements);
* **`exists_map_stripDriver_eq_mixLaw`**: for `4 < κ < 8` and every R36 strip evolution of ordinary `SLE_κ`
  (no lower marks, `τ₋ = 0`), the law of the strip driver path `t ↦ ξ_t` is the `f(u) du`-mixture of the forced laws.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.Mix

variable {κ σ : ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ}

/-- The mixture is the image of `f(u) du ⊗ Law(B)` under `(u, γ) ↦ ξ̂(u, γ)`. -/
theorem mixLaw_eq_map_prod {P : Measure Ω} [IsProbabilityMeasure P] (hκ : 0 < κ) (hσ : |σ| < 1)
    (hBm : ∀ t, Measurable (B t)) :
    mixLaw P κ σ B = ((mixMeasureU κ σ).prod (P.map (pathOf B))).map fun p => forcedPath κ σ p.1 p.2 := by
  have hU := isProbabilityMeasure_mixMeasureU hκ hσ
  have hpm := measurable_pathOf hBm
  rw [mixLaw, ← Measure.map_id (μ := mixMeasureU κ σ), Measure.map_prod_map _ _ measurable_id hpm,
    Measure.map_map measurable_forcedPath_uncurry (measurable_id.prodMap hpm), Measure.map_id]
  rfl

/-- **The mixture of forced laws is canonical**: it is the same for any two Brownian motions. -/
theorem mixLaw_eq_mixLaw {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P : Measure Ω} {P' : Measure Ω'}
    [IsProbabilityMeasure P] [IsProbabilityMeasure P'] {B' : ℝ≥0 → Ω' → ℝ} (hκ : 0 < κ) (hσ : |σ| < 1)
    (hB : IsPreBrownianReal B P) (hB' : IsPreBrownianReal B' P') (hBm : ∀ t, Measurable (B t))
    (hBm' : ∀ t, Measurable (B' t)) : mixLaw P κ σ B = mixLaw P' κ σ B' := by
  rw [mixLaw_eq_map_prod hκ hσ hBm, mixLaw_eq_map_prod hκ hσ hBm',
    map_pathOf_eq_of_isPreBrownianReal hB hB' hBm hBm']

/-- **Transfer of null sets**: if a measurable set `N` of paths is null for the forced law of almost every `u`, it is
null for the strip driver law. -/
theorem measure_stripPath_eq_zero_of_ae {𝓕 : Filtration ℝ≥0 mΩ} {P : Measure Ω} (hκ : 0 < κ) (hσ : |σ| < 1)
    (hB : IsFilteredBrownianReal 𝓕 B P) (hBc : ∀ ω, Continuous (B · ω)) (hB0 : ∀ ω, B 0 ω = 0)
    {N : Set (ℝ≥0 → ℝ)} (hN : MeasurableSet N)
    (h : ∀ᵐ u, P {ω | (fun t : ℝ≥0 => forcedDrv κ σ (fun _ => u) B t ω) ∈ N} = 0) :
    P {ω | (fun t : ℝ≥0 => stripDrv κ σ B ω t) ∈ N} = 0 := by
  rw [measure_stripPath_eq_lintegral hκ hσ hB hBc hB0 hN]
  have h0 : (fun u => ENNReal.ofReal (mixDensity κ σ u) *
      P {ω | (fun t : ℝ≥0 => forcedDrv κ σ (fun _ => u) B t ω) ∈ N}) =ᵐ[volume] fun _ => 0 := by
    filter_upwards [h] with u hu
    rw [hu, mul_zero]
  rw [lintegral_congr_ae h0, lintegral_zero]

/-- **(G3) for ordinary `SLE_κ`, `4 < κ < 8`, in strip coordinates.** For every R36 strip evolution with no lower
marks and end weight `τ₋ = 0` (ordinary chordal `SLE_κ` with the point `−1`, run until `−1` is swallowed), there is a
Brownian motion `B̃` (every path continuous, `B̃₀ = 0`) such that the law of the strip driver path `t ↦ ξ_t` is the
`f(u) du`-mixture of the forced laws `mixLaw P κ σ B̃`, `σ = 3 − κ/2`. -/
theorem exists_map_stripDriver_eq_mixLaw (hκ4 : 4 < κ) (hκ8 : κ < 8) {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin 1 → ℝ≥0 → Ω → ℝ} {VR : Fin 0 → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hE : Strip.IsStripSLEEvolution κ (![] : Fin 0 → ℝ) (![] : Fin 0 → ℝ) ![] ![] 0 P 𝓕 W VL VR B ζ) :
    ∃ (𝓗 : Filtration ℝ≥0 mΩ) (B' : ℝ≥0 → Ω → ℝ), IsFilteredBrownianReal 𝓗 B' P ∧ (∀ ω, Continuous (B' · ω)) ∧
      (∀ ω, B' 0 ω = 0) ∧
      P.map (fun ω (t : ℝ≥0) => Strip.stripDriver (Strip.extPath (W · ω)) (Strip.extPath (VL (Fin.last 0) · ω)) t) =
        mixLaw P κ (3 - κ / 2) B' := by
  have hκ : 0 < κ := by linarith
  have hσ : |3 - κ / 2| < 1 := by rw [abs_lt]; constructor <;> linarith
  have hsep : Strip.IsSeparatedStripWord (![] : Fin 0 → ℝ) (![] : Fin 0 → ℝ) :=
    ⟨fun a => a.elim0, fun i => i.elim0, fun a => a.elim0, fun i => i.elim0⟩
  have hpre : Strip.HasStripPrefixSums κ (![] : Fin 0 → ℝ) (![] : Fin 0 → ℝ) := ⟨fun j => j.elim0, fun j => j.elim0⟩
  obtain ⟨𝓗, B₁, hB₁, hae⟩ := Zhan.exists_stripBrownian_of_prefixSums hκ hsep hpre hE
  have hP : IsProbabilityMeasure P := hB₁.1.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  -- a version with every path continuous and `B₀ = 0`
  have hgood : ∀ᵐ ω ∂P, Continuous (B₁ · ω) ∧ B₁ 0 ω = 0 := by
    filter_upwards [hB₁.1.cont, hB₁.1.toIsPreBrownianReal.eval_zero_ae_eq_zero] with ω h1 h2 using ⟨h1, h2⟩
  set G : Set Ω := (toMeasurable P {ω | ¬ (Continuous (B₁ · ω) ∧ B₁ 0 ω = 0)})ᶜ with hGdef
  have hGm : MeasurableSet G := (measurableSet_toMeasurable _ _).compl
  have hGc : P Gᶜ = 0 := by rw [hGdef, compl_compl, measure_toMeasurable]; exact ae_iff.1 hgood
  have hGg : ∀ ω ∈ G, Continuous (B₁ · ω) ∧ B₁ 0 ω = 0 := fun ω hω => by
    by_contra h; exact hω (subset_toMeasurable _ _ h)
  obtain ⟨B₂, hB₂, hB₂c, hB₂0, hB₂eq⟩ : ∃ B₂ : ℝ≥0 → Ω → ℝ, IsFilteredBrownianReal (Ito.nullAugmented 𝓗 P) B₂ P ∧
      (∀ ω, Continuous (B₂ · ω)) ∧ (∀ ω, B₂ 0 ω = 0) ∧ ∀ ω ∈ G, ∀ t, B₂ t ω = B₁ t ω := by
    classical
    obtain ⟨hB, hBc⟩ := Ito.isFilteredBrownianReal_modify hB₁ hGm hGc fun ω hω => (hGg ω hω).1
    refine ⟨_, hB, hBc, fun ω => ?_, fun ω hω t => ?_⟩
    · by_cases hω : ω ∈ G
      · simp only [hω, ↓reduceIte]; exact (hGg ω hω).2
      · simp [hω]
    · simp only [hω, ↓reduceIte]
  refine ⟨_, B₂, hB₂, hB₂c, hB₂0, ?_⟩
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := ae_iff.2 hGc
  have hpath : (fun ω (t : ℝ≥0) => Strip.stripDriver (Strip.extPath (W · ω)) (Strip.extPath (VL (Fin.last 0) · ω)) t)
      =ᵐ[P] pathOf fun t ω => stripDrv κ (3 - κ / 2) B₂ ω t := by
    filter_upwards [hae, hGae] with ω hω hωG
    funext t
    rw [(hω t).2]
    simp only [pathOf, stripDrv, Real.toNNReal_coe, hB₂eq ω hωG, Finset.univ_eq_empty, Finset.sum_empty,
      Strip.tauPlus]
    ring
  rw [Measure.map_congr hpath]
  exact map_stripPath_eq_mixLaw hκ hσ hB₂ hB₂c hB₂0

end InteractingSLE.ZhanGT4.Mix
