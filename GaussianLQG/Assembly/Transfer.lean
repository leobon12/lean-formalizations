import GaussianLQG.Core.MainDefs
import GaussianLQG.Energy.Measures
import GaussianLQG.LQG.Bridge.Basic
import GaussianLQG.LQG.Scaling.Measurability
import LQGMetric.Field.MeasurableAvg
import LQGMetric.Papers.GM.S1.FieldAux
import LQGMetric.Meas.CR

/-!
# Transfer of law-level statements between realizations of the normalized GFF

Blueprint, the paragraph after Proposition `prop:realization`: every quantity in the main theorem is
a measurable function of the field, and the law of a whole-plane GFF normalized by `h_1(0) = 0`
is unique (`LQGMetric.GM.normGFFLaw_eq`). Hence convergence in probability, laws, medians and
moments are the same for any two normalized fields `h` (on `(Ω, P)`) and `h'` (on `(Ω', P')`),
for instance the coordinate field `h₀` on `(ℝ^ℕ, stdP)`.

## Measurability of the functionals of the field (all on `𝒟'(ℂ)` with the cylinder σ-algebra)

* `measurable_measPairing`: `g ↦ (g, μ)` for every s-finite `μ` (the mollified pairings are
  integrals of the Carathéodory function `(g, x) ↦ ⟨g, ψ_{n,x}⟩`, and `limUnder` of measurable
  functions is measurable); hence `measurable_segPairing` (`g ↦ H(s,t)`) and, since the dyadics
  are countable, `measurable_diagMin` (`g ↦ M`). These are full (not only a.e.) measurability.
* `measurable_canonical_dist_zero_one`: `g ↦ D^γ_g(0, 1)` for the canonical metrics, `γ ∈ (0,2)`
  (from `IsCanonicalLQGMetric.measurable_dist_comp`).
* The Hölder constant `A(K)` and the separated infimum `I(K, δ)` are measurable on
  `C(ℂ × ℂ, ℝ)`: `measurable_holderConst_cont`, `measurable_sepInf_cont`
  (`GaussianLQG/LQG/Scaling/Measurability.lean`).

## Transfer lemmas

For normalized `h` on `(Ω, P)` and `h'` on `(Ω', P')` (both probability spaces):
`map_eq_map_of_isNormalizedWPGFF` (`P.map h = P'.map h'`), `map_comp_eq_of_isNormalizedWPGFF`
(laws of measurable functionals), `isMedian_map_comp_iff` (medians),
`tendstoInMeasure_comp_iff` (convergence in probability), and the `normGFFLaw` forms
`lintegral_normGFFLaw`, `qConst_eq_lowerMedian`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace GaussianLQG

open LQGMetric

/-! ## Measurability of field functionals -/

/-- **`g ↦ (g, μ)` is measurable** on `𝒟'(ℂ)` for every s-finite measure `μ`. -/
theorem measurable_measPairing (μ : Measure ℂ) [SFinite μ] :
    Measurable fun g : DistC => measPairing g μ := by
  have hn : ∀ n : ℕ, StronglyMeasurable fun g : DistC => ∫ x, g (bumpTest n x) ∂μ := fun n =>
    (measurable_apply_bumpTest n).stronglyMeasurable.integral_prod_right'
  exact (StronglyMeasurable.limUnder (l := atTop) hn).measurable

/-- **`g ↦ H(s,t) = (g, λ_{is, 1+it})` is measurable** on `𝒟'(ℂ)`. -/
theorem measurable_segPairing (s t : ℝ) : Measurable fun g : DistC => segPairing g s t :=
  measurable_measPairing _

/-- The dyadic rationals in `[0,1]` form a countable set. -/
theorem countable_dyadicUnit : dyadicUnit.Countable := by
  refine (Set.countable_range fun p : ℕ × ℕ => (p.2 : ℝ) / 2 ^ p.1).mono ?_
  rintro y ⟨n, k, -, rfl⟩
  exact ⟨(n, k), rfl⟩

/-- **`g ↦ M = inf_{y dyadic} H(y,y)` is measurable** on `𝒟'(ℂ)`. -/
theorem measurable_diagMin : Measurable diagMin := by
  have : Countable dyadicUnit := countable_dyadicUnit.to_subtype
  show Measurable fun g : DistC => ⨅ y : dyadicUnit, segPairing g y y
  exact Measurable.iInf fun y => measurable_segPairing _ _

/-- **`g ↦ D^γ_g(0, 1)` is measurable** for the canonical metrics, `γ ∈ (0, 2)`. -/
theorem measurable_canonical_dist_zero_one {Dfam : ℝ → DistC → ContMetric}
    (hD : ∀ γ, 0 < γ → γ < 2 → IsCanonicalLQGMetric γ (Dfam γ)) {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) : Measurable fun g : DistC => (Dfam γ g).1 (0, 1) :=
  (hD γ hγ hγ2).measurable_dist_comp 0 1

/-! ## Medians and a.e. equality -/

/-- The lower median depends only on the a.e. class of the random variable. -/
theorem lowerMedian_congr_ae {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X Y : Ω → ℝ}
    (hXY : X =ᵐ[P] Y) : lowerMedian P X = lowerMedian P Y := by
  unfold lowerMedian
  congr 1
  ext m
  have hset : ({x | X x ≤ m} : Set Ω) =ᵐ[P] ({x | Y x ≤ m} : Set Ω) := hXY.mono fun ω hω => by
    change (X ω ≤ m) = (Y ω ≤ m)
    rw [hω]
  simp only [mem_ofPred_eq]
  rw [measure_congr hset]

/-! ## Transfer between two normalized fields -/

section Transfer

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω}
  {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P'] {h : Ω → DistC}
  {h' : Ω' → DistC}

/-- **Uniqueness of the law**: two whole-plane GFFs normalized by `h_1(0) = 0` have the same law
(both are `normGFFLaw`). -/
theorem map_eq_map_of_isNormalizedWPGFF (hh : IsNormalizedWPGFF h P)
    (hh' : IsNormalizedWPGFF h' P') : P.map h = P'.map h' :=
  (GM.normGFFLaw_eq hh).symm.trans (GM.normGFFLaw_eq hh')

/-- Events defined through the field have the same probability. -/
theorem measure_preimage_eq_of_isNormalizedWPGFF (hh : IsNormalizedWPGFF h P)
    (hh' : IsNormalizedWPGFF h' P') {A : Set DistC} (hA : MeasurableSet A) :
    P (h ⁻¹' A) = P' (h' ⁻¹' A) := by
  rw [← Measure.map_apply hh.1.measurable hA, ← Measure.map_apply hh'.1.measurable hA,
    map_eq_map_of_isNormalizedWPGFF hh hh']

/-- **Laws of measurable functionals** of the field agree. -/
theorem map_comp_eq_of_isNormalizedWPGFF {β : Type*} [MeasurableSpace β] {F : DistC → β}
    (hF : Measurable F) (hh : IsNormalizedWPGFF h P) (hh' : IsNormalizedWPGFF h' P') :
    P.map (fun ω => F (h ω)) = P'.map (fun ω => F (h' ω)) := by
  show P.map (F ∘ h) = P'.map (F ∘ h')
  rw [← Measure.map_map hF hh.1.measurable, ← Measure.map_map hF hh'.1.measurable,
    map_eq_map_of_isNormalizedWPGFF hh hh']

/-- **Medians** of measurable real functionals of the field agree. -/
theorem isMedian_map_comp_iff {G : DistC → ℝ} (hG : Measurable G) (hh : IsNormalizedWPGFF h P)
    (hh' : IsNormalizedWPGFF h' P') {m : ℝ} :
    IsMedian (P.map fun ω => G (h ω)) m ↔ IsMedian (P'.map fun ω => G (h' ω)) m := by
  rw [map_comp_eq_of_isNormalizedWPGFF hG hh hh']

/-- **Convergence in probability** of measurable functionals of the field transfers between
normalized fields. Measurability of `F i` is needed only eventually along `l`. -/
theorem tendstoInMeasure_comp_iff {ι : Type*} {l : Filter ι} {F : ι → DistC → ℝ}
    {G : DistC → ℝ} (hF : ∀ᶠ i in l, Measurable (F i)) (hG : Measurable G)
    (hh : IsNormalizedWPGFF h P) (hh' : IsNormalizedWPGFF h' P') :
    TendstoInMeasure P (fun i ω => F i (h ω)) l (G ∘ h) ↔
      TendstoInMeasure P' (fun i ω => F i (h' ω)) l (G ∘ h') := by
  have key : ∀ ε : ℝ≥0∞, ∀ᶠ i in l, P {ω | ε ≤ edist (F i (h ω)) ((G ∘ h) ω)} =
      P' {ω | ε ≤ edist (F i (h' ω)) ((G ∘ h') ω)} := by
    intro ε
    filter_upwards [hF] with i hFi
    exact measure_preimage_eq_of_isNormalizedWPGFF hh hh'
      (measurableSet_le measurable_const (hFi.edist hG) :
        MeasurableSet {g : DistC | ε ≤ edist (F i g) (G g)})
  constructor
  · intro H ε hε
    exact (H ε hε).congr' (key ε)
  · intro H ε hε
    exact (H ε hε).congr' ((key ε).mono fun i hi => hi.symm)

end Transfer

/-! ## `normGFFLaw` forms -/

section NormGFFLaw

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistC}

/-- Lebesgue integrals against `normGFFLaw` are expectations over any normalized field. -/
theorem lintegral_normGFFLaw {F : DistC → ℝ≥0∞} (hF : Measurable F)
    (hh : IsNormalizedWPGFF h P) : ∫⁻ g, F g ∂normGFFLaw = ∫⁻ ω, F (h ω) ∂P := by
  rw [GM.normGFFLaw_eq hh, lintegral_map hF hh.1.measurable]

/-- The lower median of a measurable functional under `normGFFLaw` is its lower median under any
normalized field. -/
theorem lowerMedian_normGFFLaw {G : DistC → ℝ} (hG : Measurable G)
    (hh : IsNormalizedWPGFF h P) : lowerMedian normGFFLaw G = lowerMedian P (fun ω => G (h ω)) := by
  unfold lowerMedian
  congr 1
  ext m
  simp only [mem_ofPred_eq]
  rw [GM.normGFFLaw_eq hh, Measure.map_apply hh.1.measurable (measurableSet_le hG measurable_const)]
  rfl

/-- `q = med M` computed on any normalized field. -/
theorem qConst_eq_lowerMedian (hh : IsNormalizedWPGFF h P) :
    qConst = lowerMedian P (fun ω => diagMin (h ω)) :=
  lowerMedian_normGFFLaw measurable_diagMin hh

end NormGFFLaw

/-! ## Compatibility names (cleanup W15)

The measurability of `A(K)` and `I(K, δ)` on `C(ℂ × ℂ, ℝ)` is proved in
`GaussianLQG/LQG/Scaling/Measurability.lean`; the old names are kept. -/

alias measurable_holderConst_continuousMap := measurable_holderConst_cont

alias measurable_sepInf_continuousMap := measurable_sepInf_cont

alias measurable_canonical_dist := IsCanonicalLQGMetric.measurable_dist_comp

end GaussianLQG
