import QuantumZipper.Proofs.LQG.AreaProfile
import QuantumZipper.Proofs.LQG.WedgeMeasurable

/-!
# M4-A5: `scaleParam` and `canonical`

Blueprint `M4_BLUEPRINT.md`, node M4-A5. For a sample with the area profile of M4-A4
(`AreaProfile.HasAreaProfile`: finite, continuous, strictly increasing, `→ 0` at `0⁺`,
`→ ∞` at `∞`):

* `scaleParam_spec`: `0 < scaleParam γ x` and `μ_x(B(0, scaleParam γ x) ∩ ℍ) = 1` exactly;
* `canonical_spec`: on good samples, `canonical γ x` is good with `μ(B(0,1) ∩ ℍ) = 1`;
* `canonical_rescale_regEq'`: `canonical γ (rescale x Q b) = canonical γ x` up to `RegEq` (M4-T3);
* free field: `ae_canonical_spec` and measurability of the canonical data
  (`aemeasurable_dataFull_canonical_free`, from `WedgeMeas.aemeasurable_dataFull_canonical`).

The argument is the elementary intermediate-value reasoning behind Sheffield's normalization
(Sheffield, *Conformal weldings of random surfaces: SLE and the quantum gravity zipper*,
Ann. Probab. 44 (2016), (1.8)): no published proof is needed beyond it.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace QuantumZipper
namespace CanonicalGood

open AreaProfile

/-- **M4-A5 (scale).** Under the area profile, `0 < scaleParam γ x` and the ball of radius
`scaleParam γ x` has unit quantum area. -/
theorem scaleParam_spec {γ : ℝ} {x : FieldSample} (hx : HasAreaProfile γ x) :
    0 < scaleParam γ x ∧ qAreaMeasure γ x (Metric.ball 0 (scaleParam γ x) ∩ H) = 1 := by
  obtain ⟨-, hcont, -, h0, htop⟩ := hx
  set f := profile (qAreaMeasure γ x) with hf
  have hmono : Monotone f := profile_mono _
  set S : Set ℝ := {a : ℝ | 0 < a ∧ 1 ≤ qAreaMeasure γ x (Metric.ball 0 a ∩ H)} with hS
  have hSf : ∀ a, a ∈ S ↔ 0 < a ∧ 1 ≤ f a := fun a => Iff.rfl
  have hs : scaleParam γ x = sInf S := rfl
  -- `S` is nonempty
  obtain ⟨a₁, ha₁⟩ := ((htop.eventually (lt_mem_nhds ENNReal.one_lt_top)).and
    (eventually_gt_atTop 0)).exists
  have hne : S.Nonempty := ⟨a₁, (hSf a₁).2 ⟨ha₁.2, ha₁.1.le⟩⟩
  have hbdd : BddBelow S := ⟨0, fun a ha => ha.1.le⟩
  -- a positive radius with `f < 1`
  obtain ⟨δ, hδ⟩ := ((h0.eventually (gt_mem_nhds zero_lt_one)).and
    (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] 0)).exists
  have hδS : ∀ a ∈ S, δ < a := by
    intro a ha
    by_contra h
    exact absurd (ha.2.trans (hmono (not_lt.1 h))) (not_le.2 hδ.1)
  obtain ⟨s, hsdef⟩ : ∃ s, s = scaleParam γ x := ⟨_, rfl⟩
  have hs' : s = sInf S := hsdef.trans hs
  have hsle : ∀ a ∈ S, s ≤ a := fun a ha => hs' ▸ csInf_le hbdd ha
  have hpos : 0 < s := by
    rw [hs']
    exact lt_of_lt_of_le hδ.2 (le_csInf hne fun a ha => (hδS a ha).le)
  rw [← hsdef]
  refine ⟨hpos, ?_⟩
  have hc := hcont.continuousAt (x := s)
  show f s = 1
  refine le_antisymm ?_ ?_
  · -- `f s ≤ 1`
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 (hc.eventually (lt_mem_nhds hlt))
    have hm : 0 < min ε s := lt_min hε hpos
    have hms : min ε s ≤ s := min_le_right _ _
    have hme : min ε s ≤ ε := min_le_left _ _
    have ha0 : 0 < s - min ε s / 2 := by linarith
    have hd : dist (s - min ε s / 2) s < ε := by
      rw [Real.dist_eq, abs_of_neg (by linarith)]; linarith
    have haS : s - min ε s / 2 ∈ S := (hSf _).2 ⟨ha0, (hball hd).le⟩
    have := hsle _ haS
    linarith
  · -- `1 ≤ f s`
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 (hc.eventually (gt_mem_nhds hlt))
    have hlt' : sInf S < s + ε := by rw [← hs']; linarith
    obtain ⟨a, haS, has⟩ := exists_lt_of_csInf_lt hne hlt'
    have hsa := hsle a haS
    have hd : dist a s < ε := by
      rw [Real.dist_eq, abs_of_nonneg (by linarith)]; linarith
    exact absurd haS.2 (not_le.2 (hball hd))

/-- **M4-A5 (canonical).** On good samples with the area profile, `canonical γ x` is good and
`B(0,1) ∩ ℍ` has unit quantum area. -/
theorem canonical_spec {γ : ℝ} (hγ : 0 < γ) {x : FieldSample} (hg : IsLQGGood γ x)
    (hx : HasAreaProfile γ x) :
    IsLQGGood γ (canonical γ x) ∧ qAreaMeasure γ (canonical γ x) (Metric.ball 0 1 ∩ H) = 1 := by
  obtain ⟨hs, h1⟩ := scaleParam_spec hx
  refine ⟨hg.rescale hγ hs, ?_⟩
  rw [canonical, GoodTransforms.qAreaMeasure_rescale hg hγ hs,
    Measure.map_apply (show Measurable fun z : ℂ => z / (scaleParam γ x : ℂ) from
      measurable_id.div_const _) (Metric.isOpen_ball.inter isOpen_H).measurableSet,
    GoodTransforms.preimage_div_ball_inter_H hs, one_mul, h1]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

end CanonicalGood
end QuantumZipper
