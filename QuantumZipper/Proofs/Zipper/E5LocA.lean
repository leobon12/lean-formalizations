import QuantumZipper.Proofs.Zipper.E5Model3
import QuantumZipper.Proofs.Field.TRegE4Coll
import QuantumZipper.Proofs.Zipper.E4L3Basic

/-!
# E5-LOC2, part A: the pushed normalizer `ϖ_t` (Frostman, bounded support, positive radius)

Blueprint `blueprint/E_BRANCH_BLUEPRINT.md` §4 E5, step (1); Sheffield, arXiv:1012.4797, §5.4
(pp. 66–72). For a normalizer `ϖ` (`E1.IsNormalizer`: probability, compact support in `ℍ`,
Frostman) and a continuous driver `V`, the pushforward `ϖ_t = ϖ.map (revMap V t)`:

* is a probability measure carried by a compact subset of `ℍ` (`exists_compact_support_varpiT`);
* gives no mass to some ball `ball 0 r`, `r > 0` (`exists_radius_varpiT`): the image of the
  support is a compact subset of `ℍ`, so it has positive distance from `0`;
* has bounded support and is Frostman with an exponent in `(0, 1]` (`varpiT_frostman`, from
  `B2.isFrostman_map_revMap_of_compact` and `E4Grid.isFrostman_min_one`), hence is admissible
  (`isAdmissibleH_varpiT`) and its Neumann potential `k_{ϖ_t}` is continuous
  (`continuous_kPot_varpiT`, via `TRegE4.continuous_kPot`; cf. Ransford, *Potential Theory in the
  Complex Plane*, Thm 3.1.3 for continuity of potentials of measures with Hölder mass bounds);
* so the collision correction `locCorr` is folded-harmonic on every ball avoiding `supp ϖ_t`
  (`harmonicOnNhd_locCorr_foldH_of_normalizer`).

Also (item (iv), deterministic part): `X(μ) − X(ν)` is `outsideSigma X 0 r`-measurable (hence
`condSigma`-measurable) for admissible `μ, ν` of equal mass giving no mass to `ball 0 r`
(`measurable_condSigma_sub`); immediate from the definition of `outsideSigma`.

Own elementary arguments (compactness and definitions), assembling project lemmas.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace E5

open D3Plus E1 B2

variable {V : ℝ → ℝ} {t : ℝ} {ϖ : Measure ℂ}

theorem isProbabilityMeasure_varpiT (hϖ : IsNormalizer ϖ) (hV : Continuous V) (ht : 0 ≤ t) :
    IsProbabilityMeasure (varpiT V t ϖ) := by
  have := hϖ.prob
  exact (Measure.isProbabilityMeasure_map_iff (TwoPoint.measurable_revMap hV ht).aemeasurable).2
    inferInstance

/-- `ϖ_t` is carried by a compact subset of `ℍ` (the image of the support of `ϖ`). -/
theorem exists_compact_support_varpiT (hϖ : IsNormalizer ϖ) (hV : Continuous V) (ht : 0 ≤ t) :
    ∃ K' : Set ℂ, IsCompact K' ∧ K' ⊆ H ∧ varpiT V t ϖ K'ᶜ = 0 := by
  obtain ⟨K, hKc, hKH, hK0⟩ := hϖ.cpt
  have hFc : ContinuousOn (revMap V t) K :=
    (differentiableOn_revMap V hV ht).continuousOn.mono hKH
  have hK' : IsCompact (revMap V t '' K) := hKc.image_of_continuousOn hFc
  refine ⟨revMap V t '' K, hK', ?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact TwoPoint.im_revMap_pos hV (hKH hz) ht
  · rw [varpiT, Measure.map_apply (TwoPoint.measurable_revMap hV ht)
      hK'.isClosed.measurableSet.compl]
    exact measure_mono_null (fun z hz hzK => hz ⟨z, hzK, rfl⟩) hK0

/-- **`ϖ_t` avoids a ball around `0`.** -/
theorem exists_radius_varpiT (hϖ : IsNormalizer ϖ) (hV : Continuous V) (ht : 0 ≤ t) :
    ∃ r > 0, varpiT V t ϖ (ball (0 : ℂ) r) = 0 := by
  obtain ⟨K', hK'c, hK'H, hK'0⟩ := exists_compact_support_varpiT hϖ hV ht
  have h0 : (0 : ℂ) ∉ K' := fun h => by
    have h' : (0 : ℝ) < (0 : ℂ).im := hK'H h
    rw [Complex.zero_im] at h'
    exact lt_irrefl _ h'
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hK'c.isClosed.isOpen_compl 0 h0
  exact ⟨r, hr, measure_mono_null hball hK'0⟩

/-- **(i) Regularity of `ϖ_t`**: bounded support (`closedBall 0 B ∩ Hbar`) and a Frostman bound
with exponent in `(0, 1]`. -/
theorem varpiT_frostman (hϖ : IsNormalizer ϖ) (hV : Continuous V) (ht : 0 ≤ t) :
    ∃ B : ℝ, 0 ≤ B ∧ varpiT V t ϖ (closedBall 0 B ∩ Hbar)ᶜ = 0 ∧
      ∃ α C : ℝ, 0 < α ∧ α ≤ 1 ∧ TwoPoint.IsFrostman (varpiT V t ϖ) α C := by
  have := isProbabilityMeasure_varpiT hϖ hV ht
  have := hϖ.prob
  obtain ⟨K', hK'c, hK'H, hK'0⟩ := exists_compact_support_varpiT hϖ hV ht
  obtain ⟨B, hB⟩ := hK'c.isBounded.subset_closedBall (0 : ℂ)
  obtain ⟨K, hKc, hKH, hK0⟩ := hϖ.cpt
  obtain ⟨α, C, hα, hfr⟩ := hϖ.frost
  obtain ⟨C', hC'⟩ := isFrostman_map_revMap_of_compact hV ht hKc hKH hK0 hα.le hfr
  refine ⟨max B 0, le_max_right _ _, ?_, min α 1, _, lt_min hα one_pos, min_le_right _ _,
    E4Grid.isFrostman_min_one hα (fun p r hr => hC' p r hr)⟩
  refine measure_mono_null (compl_subset_compl.2 fun z hz => ⟨?_, H_subset_Hbar (hK'H hz)⟩) hK'0
  exact closedBall_subset_closedBall (le_max_left _ _) (hB hz)

theorem ae_norm_le_of_supp {μ : Measure ℂ} {B : ℝ} (h : μ (closedBall 0 B ∩ Hbar)ᶜ = 0) :
    ∀ᵐ v ∂μ, ‖v‖ ≤ B :=
  ae_iff.2 (measure_mono_null (fun v (hv : ¬ ‖v‖ ≤ B) (hvB : v ∈ closedBall (0 : ℂ) B ∩ Hbar) =>
    hv (by simpa using hvB.1)) h)

/-- `ϖ_t` is admissible. -/
theorem isAdmissibleH_varpiT (hϖ : IsNormalizer ϖ) (hV : Continuous V) (ht : 0 ≤ t) :
    IsAdmissibleH (varpiT V t ϖ) := by
  have := isProbabilityMeasure_varpiT hϖ hV ht
  obtain ⟨B, -, hsupp, α, C, hα, -, hF⟩ := varpiT_frostman hϖ hV ht
  exact FrostmanReg.isAdmissibleH_of_frostman hsupp (fun p r hr => hF p r hr) hα

/-- **(i) Continuity of `k_{ϖ_t}`.** -/
theorem continuous_kPot_varpiT (hϖ : IsNormalizer ϖ) (hV : Continuous V) (ht : 0 ≤ t) :
    Continuous (PalmNorm.kPot (varpiT V t ϖ)) := by
  have := isProbabilityMeasure_varpiT hϖ hV ht
  obtain ⟨B, hB0, hsupp, α, C, hα, hα1, hF⟩ := varpiT_frostman hϖ hV ht
  exact TRegE4.continuous_kPot hF hα hα1 hB0 (ae_norm_le_of_supp hsupp)

/-- **`Setup.harm` for the collision correction on a ball avoiding `ϖ_t`.** -/
theorem harmonicOnNhd_locCorr_foldH_of_normalizer (κ : ℝ) (ρ₀ : Measure ℂ) (x : FieldSample)
    (hϖ : IsNormalizer ϖ) (hV : Continuous V) (ht : 0 ≤ t) {r : ℝ}
    (hr : varpiT V t ϖ (ball (0 : ℂ) r) = 0) :
    InnerProductSpace.HarmonicOnNhd (fun z => locCorr κ V t ϖ ρ₀ x (foldH z)) (ball (0 : ℂ) r) := by
  have := isProbabilityMeasure_varpiT hϖ hV ht
  obtain ⟨B, -, hsupp, -⟩ := varpiT_frostman hϖ hV ht
  have h0 : ∀ᵐ v ∂(varpiT V t ϖ), r ≤ ‖v‖ :=
    ae_iff.2 (measure_mono_null (fun v hv => by
      simpa [mem_ball_zero_iff] using (not_le.1 hv)) hr)
  exact harmonicOnNhd_locCorr_foldH κ V t ϖ ρ₀ x (ae_norm_le_of_supp hsupp) h0
    (continuous_kPot_varpiT hϖ hV ht)

/-- **(iv), deterministic measures**: `X(μ) − X(ν)` is measurable for `outsideSigma X 0 r`. -/
theorem measurable_outsideSigma_sub {Ω : Type*} [MeasurableSpace Ω] (X : Ω → FieldSample)
    {r : ℝ} {μ ν : Measure ℂ} (hμ : IsAdmissibleH μ) (hν : IsAdmissibleH ν)
    (hm : μ univ = ν univ) (hμB : μ (ball (0 : ℂ) r) = 0) (hνB : ν (ball (0 : ℂ) r) = 0) :
    Measurable[K3.outsideSigma X 0 r] fun ω => X ω μ - X ω ν :=
  measurable_iff_comap_le.2 (le_iSup (fun p : K3.OutIdx 0 r =>
    MeasurableSpace.comap (fun ω => X ω p.1.1 - X ω p.1.2) inferInstance)
    ⟨(μ, ν), hμ, hν, hm, by simpa using hμB, by simpa using hνB⟩)

theorem measurable_condSigma_sub {Ω E' : Type*} [MeasurableSpace Ω] [MeasurableSpace E']
    (Ξ : Ω → E') (X : Ω → FieldSample) {r : ℝ} {μ ν : Measure ℂ} (hμ : IsAdmissibleH μ)
    (hν : IsAdmissibleH ν) (hm : μ univ = ν univ) (hμB : μ (ball (0 : ℂ) r) = 0)
    (hνB : ν (ball (0 : ℂ) r) = 0) :
    Measurable[condSigma Ξ X r] fun ω => X ω μ - X ω ν :=
  (measurable_outsideSigma_sub X hμ hν hm hμB hνB).mono le_sup_right le_rfl

end E5
end QuantumZipper
