import GaussianLQG.Assembly.Realize
import GaussianLQG.Assembly.Transfer
import GaussianLQG.Core.Setup
import GaussianLQG.Energy.Segments
import GaussianLQG.LQG.Dimension
import GaussianLQG.LQG.Bridge

/-!
# Instantiating `Setup` (blueprint Propositions `prop:realization` and `prop:S2-S5`)

Given the canonical γ-LQG metrics `Dfam γ` (`γ ∈ (0,2)`, `GaussianLQG.IsCanonicalLQGMetric`) and the
input (S6) (`UniformMomentInput Dfam`), `exists_setup` builds a `Setup` on the coordinate space
`(ℝ^ℕ, stdP)`:

* frame `e` and field `h₀` from the unconditional realization `exists_coordRealization`;
* `ξ = LQGMetric.xiGamma`, `D γ ω = D^γ_{h₀(ω)}` (for `γ ∉ (0,2)` the `γ = 1` metric is used, so
  that `D γ` is measurable for every `γ`; no property is claimed there);
* (S1) from `dimensionInput_holds` via `γ / ξ_γ = d_γ`;
* (S2)–(S3) (`good`): Axioms I and III of `IsStrongLQGMetric` at `h₀(ω)` (on a measurable
  full-measure subset of the a.s. event), combined with `h₀(ω + v) = h₀(ω) + f_v` on `Ω_W`;
* (S4) from `IsCanonicalLQGMetric.map_affine_eq`, after replacing the circle average
  `h_{|a|}(z)` by the coordinate pairing with `σ_{z,|a|}` (they agree a.s.);
* (S5) from `IsCanonicalLQGMetric.isMedian_crossFn`;
* (S6) from `UniformMomentInput` by transfer from `normGFFLaw = stdP.map h₀`, with `γ_p`
  replaced by `min γ_p 1`.

It also identifies the coordinate objects `H`, `M`, `q` of `Setup` with the field objects
`segPairing`, `diagMin`, `qConst` of the main theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace GaussianLQG

open LQGMetric

namespace Assembly

/-- The metric family used for every `γ`: the given metric for `γ ∈ (0, 2)`, and the `γ = 1`
metric otherwise (only to make `D γ` measurable for every `γ`). -/
def selD (Dfam : ℝ → DistC → ContMetric) (γ : ℝ) : DistC → ContMetric :=
  if γ ∈ Ioo (0 : ℝ) 2 then Dfam γ else Dfam 1

theorem selD_of_mem (Dfam : ℝ → DistC → ContMetric) {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) 2) :
    selD Dfam γ = Dfam γ :=
  ite_eq_left hγ

theorem isCanonicalLQGMetric_selD {Dfam : ℝ → DistC → ContMetric}
    (hD : ∀ γ, 0 < γ → γ < 2 → IsCanonicalLQGMetric γ (Dfam γ)) {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) : IsCanonicalLQGMetric γ (selD Dfam γ) := by
  rw [selD_of_mem Dfam ⟨hγ, hγ2⟩]
  exact hD γ hγ hγ2

theorem measurable_selD {Dfam : ℝ → DistC → ContMetric}
    (hD : ∀ γ, 0 < γ → γ < 2 → IsCanonicalLQGMetric γ (Dfam γ)) (γ : ℝ) :
    Measurable (selD Dfam γ) := by
  unfold selD
  split_ifs with hγ
  · exact (hD γ hγ.1 hγ.2).1.measurable
  · exact (hD 1 one_pos one_lt_two).1.measurable

/-- (S1) for `ξ = xiGamma`: `γ / ξ_γ = d_γ`, so this is `dimensionInput_holds`. -/
theorem xiGamma_S1 :
    ∃ γ₀ C₀ : ℝ, 0 < γ₀ ∧ ∀ γ ∈ Ioc (0 : ℝ) γ₀, |γ / xiGamma γ - 2| ≤ C₀ * γ := by
  obtain ⟨γ₀, C₀, hγ₀, h⟩ := dimensionInput_holds
  refine ⟨γ₀, C₀, hγ₀, fun γ hγ => ?_⟩
  rw [xiGamma, div_div_cancel₀ hγ.1.ne']
  exact h γ hγ

/-- (S2)–(S3) for a canonical metric on the realized field: on a measurable full-measure set,
`D_{h₀(ω)}` is a length metric and `D_{h₀(ω + v)} = e^{ξ f_v} · D_{h₀(ω)}` for every
finitely supported `v`. -/
theorem good_of_realization {γ : ℝ} {D : DistC → ContMetric} (hD : IsCanonicalLQGMetric γ D)
    {e : ℕ → ℂ → ℝ} (he : ∀ j, Continuous (e j)) {h₀ : Coord → DistC} {ΩW : Set Coord}
    (hh : IsNormalizedWPGFF h₀ stdP) (hΩWm : MeasurableSet ΩW) (hΩW0 : stdP ΩWᶜ = 0)
    (hshift : ∀ ω ∈ ΩW, ∀ v, h₀ (shiftBy ω v) = addFun (h₀ ω) (frameFunC e he v)) :
    ∃ Ωγ : Set Coord, MeasurableSet Ωγ ∧ stdP Ωγᶜ = 0 ∧
      ∀ ω ∈ Ωγ, (D (h₀ ω)).IsLength ∧
        ∀ (v : ℕ →₀ ℝ) (z w : ℂ), ENNReal.ofReal ((D (h₀ (shiftBy ω v))).1 (z, w)) =
          weylScale (xiGamma γ) (frameFunC e he v) (D (h₀ ω)) z w := by
  have hGFF : IsGFFPlusCont h₀ stdP := isGFFPlusCont_of_isWholePlaneGFF hh.1
  have hA := (hD.1.length stdP h₀ hGFF).and (hD.1.weyl stdP h₀ hGFF)
  obtain ⟨T, hTsub, hTm, hT0⟩ := exists_measurable_superset_of_null (ae_iff.1 hA)
  refine ⟨Tᶜ ∩ ΩW, hTm.compl.inter hΩWm, ?_, ?_⟩
  · rw [compl_inter, compl_compl]
    exact measure_union_null hT0 hΩW0
  · rintro ω ⟨hωT, hωW⟩
    have hgood : (D (h₀ ω)).IsLength ∧ ∀ (f : C(ℂ, ℝ)) (z w : ℂ),
        weylScale (xiGamma γ) f (D (h₀ ω)) z w =
          ENNReal.ofReal ((D (addFun (h₀ ω) f)).1 (z, w)) := by
      by_contra hc
      exact hωT (hTsub hc)
    refine ⟨hgood.1, fun v z w => ?_⟩
    rw [hshift ω hωW v]
    exact (hgood.2 _ z w).symm

/-- On the realized field, the frame pairing with the circle measure `σ_{z,r}` (`r > 0`) is a.s. the
circle average `h₀(ω)_r(z)`. -/
theorem pairing_circleMeasure_ae_eq {e : ℕ → ℂ → ℝ} {h₀ : Coord → DistC}
    (hpair : ∀ μ, IsRegular μ → ∀ᵐ ω ∂stdP,
      Tendsto (fun n => ∑ j ∈ Finset.range n, ω j * ∫ z, e j z ∂μ) atTop
        (𝓝 (measPairing (h₀ ω) μ)))
    (z : ℂ) {r : ℝ} (hr : 0 < r) :
    pairing e (circleMeasure z r) =ᵐ[stdP] fun ω => circleAvg (h₀ ω) r z := by
  filter_upwards [pairing_ae_eq_measPairing (hpair _ (isRegular_circleMeasure z hr))] with ω hω
  rw [hω, measPairing_circleMeasure]

/-- (S4) for a canonical metric on the realized field. -/
theorem S4_of_realization {γ : ℝ} {D : DistC → ContMetric} (hD : IsCanonicalLQGMetric γ D)
    {e : ℕ → ℂ → ℝ} {h₀ : Coord → DistC} (hh : IsNormalizedWPGFF h₀ stdP)
    (hpair : ∀ μ, IsRegular μ → ∀ᵐ ω ∂stdP,
      Tendsto (fun n => ∑ j ∈ Finset.range n, ω j * ∫ z, e j z ∂μ) atTop
        (𝓝 (measPairing (h₀ ω) μ)))
    (z a : ℂ) (ha : a ≠ 0) :
    stdP.map (fun ω => ((‖a‖ ^ (-(xiGamma γ * Q γ)) *
        Real.exp (-(xiGamma γ) * pairing e (circleMeasure z ‖a‖) ω)) •
          (D (h₀ ω)).1.comp (affinePair z a) : C(ℂ × ℂ, ℝ))) =
      stdP.map (fun ω => (D (h₀ ω)).1) := by
  have hae := pairing_circleMeasure_ae_eq hpair z (norm_pos_iff.2 ha)
  have hmap : (fun ω => ((‖a‖ ^ (-(xiGamma γ * Q γ)) *
      Real.exp (-(xiGamma γ) * pairing e (circleMeasure z ‖a‖) ω)) •
        (D (h₀ ω)).1.comp (affinePair z a) : C(ℂ × ℂ, ℝ))) =ᵐ[stdP]
      fun ω => (‖a‖ ^ (-(xiGamma γ * Q γ)) *
        Real.exp (-(xiGamma γ * circleAvg (h₀ ω) ‖a‖ z))) • (D (h₀ ω)).1.comp (affArgs z a) := by
    filter_upwards [hae] with ω hω
    rw [hω, neg_mul]
    rfl
  rw [Measure.map_congr hmap]
  exact hD.map_affine_eq hh z ha

/-- (S6) on the coordinate space, from the input (S6) under `normGFFLaw`. -/
theorem S6_of_input {Dfam : ℝ → DistC → ContMetric}
    (hD : ∀ γ, 0 < γ → γ < 2 → IsCanonicalLQGMetric γ (Dfam γ)) (hS6 : UniformMomentInput Dfam)
    {h₀ : Coord → DistC} (hh : IsNormalizedWPGFF h₀ stdP) :
    ∀ p : ℝ, 1 ≤ p → ∃ γp : ℝ, 0 < γp ∧ ∀ K : Set ℂ, IsCompact K → ∀ δ : ℝ, 0 < δ →
      ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ γ ∈ Ioc (0 : ℝ) γp,
        (∫⁻ ω, holderConst (selD Dfam γ (h₀ ω)).1 K ^ p ∂stdP) ≤ C ∧
        (∫⁻ ω, (sepInf (selD Dfam γ (h₀ ω)).1 K δ)⁻¹ ^ p ∂stdP) ≤ C := by
  intro p hp
  obtain ⟨γp, hγp, hK⟩ := hS6 p hp
  refine ⟨min γp 1, lt_min hγp one_pos, fun K hKc δ hδ => ?_⟩
  obtain ⟨C, hC, hCbd⟩ := hK K hKc δ hδ
  refine ⟨C, hC, fun γ hγ => ?_⟩
  have hγ' : γ ∈ Ioc (0 : ℝ) γp := ⟨hγ.1, hγ.2.trans (min_le_left _ _)⟩
  have hγ1 : γ ≤ 1 := hγ.2.trans (min_le_right _ _)
  have hγ2 : γ ∈ Ioo (0 : ℝ) 2 := ⟨hγ.1, by linarith⟩
  rw [selD_of_mem Dfam hγ2]
  obtain ⟨h1, h2⟩ := hCbd γ hγ'
  have hmD : Measurable fun g : DistC => (Dfam γ g).1 :=
    (hD γ hγ2.1 hγ2.2).measurable_coe_comp
  have hA : Measurable fun g : DistC => holderConst (Dfam γ g).1 K ^ p :=
    ((measurable_holderConst_cont K).comp hmD).pow_const p
  have hI : Measurable fun g : DistC => (sepInf (Dfam γ g).1 K δ)⁻¹ ^ p :=
    ((measurable_sepInf_cont K δ).comp hmD).inv.pow_const p
  exact ⟨(lintegral_normGFFLaw hA hh).symm.le.trans h1,
    (lintegral_normGFFLaw hI hh).symm.le.trans h2⟩

/-! ## Compatibility names (cleanup W15) -/

alias I_mul_ne_one_add_I_mul := sI_ne_one_add_tI

end Assembly

open Assembly

/-- **Instantiation of `Setup`** (blueprint Propositions `prop:realization` and `prop:S2-S5`, with
(S1) from `dimensionInput_holds` and (S6) from the input `UniformMomentInput`). For canonical
γ-LQG metrics `Dfam γ` (`γ ∈ (0,2)`) satisfying (S6), there are a `Setup` `S` and a measurable
normalized whole-plane GFF `h₀` on `(ℝ^ℕ, stdP)` such that, for `γ ∈ (0,2)`, `ξ_γ = γ / d_γ` and
`D^γ(ω) = D^γ_{h₀(ω)}`, and the coordinate objects `H`, `M`, `q` of `S` are the field objects
`segPairing`, `diagMin`, `qConst` of the main theorem (a.s., resp. exactly). -/
theorem exists_setup (Dfam : ℝ → DistC → ContMetric)
    (hD : ∀ γ, 0 < γ → γ < 2 → IsCanonicalLQGMetric γ (Dfam γ))
    (hS6 : UniformMomentInput Dfam) :
    ∃ (S : Setup) (h₀ : Coord → DistC),
      Measurable h₀ ∧ IsNormalizedWPGFF h₀ stdP ∧
      (∀ γ ∈ Ioo (0 : ℝ) 2, S.ξ γ = xiGamma γ ∧ ∀ ω, S.D γ ω = Dfam γ (h₀ ω)) ∧
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        S.H s t =ᵐ[stdP] fun ω => segPairing (h₀ ω) s t) ∧
      S.M =ᵐ[stdP] (fun ω => diagMin (h₀ ω)) ∧
      S.q = qConst := by
  obtain ⟨e, he, h₀, ΩW, hh₀m, hh, hΩWm, hΩW0, -, hshift, hpair⟩ := exists_coordRealization
  have hDs : ∀ γ, 0 < γ → γ < 2 → IsCanonicalLQGMetric γ (selD Dfam γ) := fun γ hγ hγ2 =>
    isCanonicalLQGMetric_selD hD hγ hγ2
  let S : Setup :=
    { e := e
      frame := he
      ξ := xiGamma
      ξ_pos := fun γ hγ _ => GM.xiGamma_pos hγ
      D := fun γ ω => selD Dfam γ (h₀ ω)
      S1 := xiGamma_S1
      measurable_D := fun γ => (measurable_selD hD γ).comp hh₀m
      good := fun γ hγ hγ2 => good_of_realization (hDs γ hγ hγ2) he.1 hh hΩWm hΩW0 hshift
      S4 := fun γ hγ hγ2 z a ha => S4_of_realization (hDs γ hγ hγ2) hh hpair z a ha
      S5 := fun γ hγ hγ2 => (hDs γ hγ hγ2).isMedian_crossFn hh
      S6 := S6_of_input hD hS6 hh }
  have hH : ∀ s t : ℝ, S.H s t =ᵐ[stdP] fun ω => segPairing (h₀ ω) s t := fun s t =>
    pairing_ae_eq_measPairing (hpair _ (isRegular_segMeasure (sI_ne_one_add_tI s t)))
  have hM : S.M =ᵐ[stdP] fun ω => diagMin (h₀ ω) := by
    have : Countable dyadicUnit := countable_dyadicUnit.to_subtype
    have hall : ∀ᵐ ω ∂stdP, ∀ y : dyadicUnit, S.H y y ω = segPairing (h₀ ω) y y :=
      ae_all_iff.2 fun y => hH y y
    filter_upwards [hall] with ω hω
    exact iInf_congr hω
  refine ⟨S, h₀, hh₀m, hh, fun γ hγ => ⟨rfl, fun ω => ?_⟩, fun s _ t _ => hH s t, hM, ?_⟩
  · show selD Dfam γ (h₀ ω) = Dfam γ (h₀ ω)
    rw [selD_of_mem Dfam hγ]
  · show lowerMedian stdP S.M = qConst
    rw [lowerMedian_congr_ae hM, qConst_eq_lowerMedian hh]

end GaussianLQG
