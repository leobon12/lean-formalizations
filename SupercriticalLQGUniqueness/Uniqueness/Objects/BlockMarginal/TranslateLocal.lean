import SupercriticalLQGUniqueness.Uniqueness.Objects.BlockMarginal.ClauseLocalC
import SupercriticalLQGUniqueness.Uniqueness.Objects.BlockCoding.BlockEventUM
import SupercriticalLQGUniqueness.Uniqueness.Objects.CentreEvent.CentreLaw
import LQGMetric.Papers.CONF.S3D114S4




 











set_option autoImplicit false

noncomputable section

open Set MeasureTheory Metric Filter
open LQGMetric.Blueprint
open scoped ENNReal Topology

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BlockMarginal

open LQGMetric (DistC restrictTo addConst TestC TestC0)

 
def shiftSet (V : Set ℂ) (z : ℂ) : Set ℂ := {x | x - z ∈ V}

theorem tsupport_translate_subset (φ : TestC) (z : ℂ) :
    tsupport (fun x => φ (x - z)) ⊆ shiftSet (tsupport (φ : ℂ → ℝ)) z := by
  apply closure_minimal
  · intro x hx
    exact subset_tsupport _ hx
  · exact (isClosed_tsupport _).preimage (continuous_id.sub continuous_const)

 
def translate0 (z : ℂ) (ψ : TestC0) : TestC0 :=
  ⟨testTranslate z ψ.1, by
    change ∫ x, ψ.1 (x - z) = 0
    rw [integral_sub_right_eq_self (fun x => ψ.1 x)]
    exact ψ.2⟩

theorem normTranslate_apply0 (z : ℂ) (u : DistC) (ψ : TestC0) :
    Objects.Producer.normTranslate z u ψ.1 = u (translate0 z ψ).1 := by
  unfold Objects.Producer.normTranslate
  rw [LQGMetric.GFFInv.addConst_apply, ψ.2, zero_mul, add_zero]
  rfl

theorem measurable_normTranslate_sigma0 (z : ℂ) (V : Set ℂ) :
    @Measurable DistC DistC (fieldSigma0On (id : DistC → DistC) (shiftSet V z))
      (fieldSigma0On (id : DistC → DistC) V) (Objects.Producer.normTranslate z) := by
  let ΦV : DistC → ({ψ : TestC0 // tsupport (ψ.1 : ℂ → ℝ) ⊆ V} → ℝ) :=
    fun g ψ => g ψ.1.1
  let ΦW : DistC → ({ψ : TestC0 // tsupport (ψ.1 : ℂ → ℝ) ⊆ shiftSet V z} → ℝ) :=
    fun g ψ => g ψ.1.1
  have hΦW : @Measurable DistC _ (fieldSigma0On (id : DistC → DistC) (shiftSet V z))
      MeasurableSpace.pi ΦW := comap_measurable ΦW
  have hcomp : @Measurable DistC _ (fieldSigma0On (id : DistC → DistC) (shiftSet V z))
      MeasurableSpace.pi (ΦV ∘ Objects.Producer.normTranslate z) := by
    refine @measurable_pi_iff DistC _ _ (fieldSigma0On (id : DistC → DistC) (shiftSet V z)) _ _
      |>.2 fun ψ => ?_
    let ψ' : {ψ : TestC0 // tsupport (ψ.1 : ℂ → ℝ) ⊆ shiftSet V z} :=
      ⟨translate0 z ψ.1, (tsupport_translate_subset ψ.1.1 z).trans fun x hx => ψ.2 hx⟩
    have heq : (fun g : DistC => (ΦV ∘ Objects.Producer.normTranslate z) g ψ) = fun g => ΦW g ψ' := by
      funext g
      exact normTranslate_apply0 z g ψ.1
    rw [heq]
    exact (measurable_pi_apply ψ').comp hΦW
  intro S hS
  obtain ⟨S', hS', rfl⟩ := hS
  exact hcomp hS'

theorem shiftSet_thickening (K : Set ℂ) (z : ℂ) (ε : ℝ) :
    shiftSet (thickening ε K) z = thickening ε (shiftSet K z) := by
  ext x
  simp only [shiftSet, mem_ofPred_eq, mem_thickening_iff]
  constructor
  · rintro ⟨y, hy, hd⟩
    refine ⟨y + z, by simpa only [shiftSet, mem_ofPred_eq, add_sub_cancel_right] using hy, ?_⟩
    rwa [show x = (x - z) + z by ring, dist_add_right]
  · rintro ⟨y, hy, hd⟩
    refine ⟨y - z, hy, ?_⟩
    rwa [dist_sub_right]

theorem measurable_normTranslate_closed0 (z : ℂ) (K : Set ℂ) :
    @Measurable DistC DistC (fieldSigmaClosed0 (id : DistC → DistC) (shiftSet K z))
      (fieldSigmaClosed0 (id : DistC → DistC) K) (Objects.Producer.normTranslate z) := by
  intro S hS
  unfold fieldSigmaClosed0 at hS ⊢
  rw [MeasurableSpace.measurableSet_iInf] at hS ⊢
  intro ε
  have hSε := hS ε
  rw [MeasurableSpace.measurableSet_iInf] at hSε ⊢
  intro hε
  have h1 := measurable_normTranslate_sigma0 z (thickening ε K) (hSε hε)
  rwa [shiftSet_thickening] at h1

 
theorem aeEventIn_normTranslate_closed0 (μ : Measure DistC)
    (hμ : IsNormalizedWholePlaneGFF (id : DistC → DistC) μ) (z : ℂ) (K : Set ℂ) {E : Set DistC}
    (hE : AEEventIn μ (fieldSigmaClosed0 (id : DistC → DistC) K) E) :
    ∃ F : Set DistC, MeasurableSet[fieldSigmaClosed0 (id : DistC → DistC) (shiftSet K z)] F ∧
      F = Objects.Producer.normTranslate z ⁻¹' (Classical.choose hE) ∧
      Objects.Producer.normTranslate z ⁻¹' E =ᵐ[μ] F := by
  obtain ⟨hFm, hEF⟩ := Classical.choose_spec hE
  have hmap : μ.map (Objects.Producer.normTranslate z) = μ := by
    have := Objects.CentreEvent.map_normTranslate_fieldLaw_eq hμ z
    simpa only [Measure.map_id] using this
  have hmeas : Measurable (Objects.Producer.normTranslate z) := Objects.BlockCoding.measurable_normTranslate z
  have hqmp : Measure.QuasiMeasurePreserving (Objects.Producer.normTranslate z) μ μ :=
    (MeasurePreserving.mk hmeas hmap).quasiMeasurePreserving
  exact ⟨_, measurable_normTranslate_closed0 z K hFm, rfl, hqmp.preimage_ae_eq hEF⟩

theorem aeEventIn_normTranslate_sigma0 (μ : Measure DistC)
    (hμ : IsNormalizedWholePlaneGFF (id : DistC → DistC) μ) (z : ℂ) (V : Set ℂ) {E : Set DistC}
    (hE : AEEventIn μ (fieldSigma0On (id : DistC → DistC) V) E) :
    AEEventIn μ (fieldSigma0On (id : DistC → DistC) (shiftSet V z))
      (Objects.Producer.normTranslate z ⁻¹' E) := by
  obtain ⟨F, hFm, hEF⟩ := hE
  have hmap : μ.map (Objects.Producer.normTranslate z) = μ := by
    have := Objects.CentreEvent.map_normTranslate_fieldLaw_eq hμ z
    simpa only [Measure.map_id] using this
  have hmeas : Measurable (Objects.Producer.normTranslate z) := Objects.BlockCoding.measurable_normTranslate z
  have hqmp : Measure.QuasiMeasurePreserving (Objects.Producer.normTranslate z) μ μ :=
    (MeasurePreserving.mk hmeas hmap).quasiMeasurePreserving
  exact ⟨_, measurable_normTranslate_sigma0 z V hFm, hqmp.preimage_ae_eq hEF⟩

 
theorem fieldSigma0On_le_closed0 {V K : Set ℂ} (hVK : V ⊆ K) :
    fieldSigma0On (id : DistC → DistC) V ≤ fieldSigmaClosed0 (id : DistC → DistC) K := by
  unfold fieldSigmaClosed0
  refine le_iInf₂ fun ε hε => ?_
  exact LQGMetric.CONF.conf36_fieldSigma0On_mono id (hVK.trans (self_subset_thickening hε K))

 
theorem fieldSigmaClosed0_mono {K K' : Set ℂ} (hKK' : K ⊆ K') :
    fieldSigmaClosed0 (id : DistC → DistC) K ≤ fieldSigmaClosed0 (id : DistC → DistC) K' := by
  unfold fieldSigmaClosed0
  refine le_iInf₂ fun ε hε => ?_
  refine (iInf₂_le ε hε).trans ?_
  exact LQGMetric.CONF.conf36_fieldSigma0On_mono id (thickening_subset_of_subset ε hKK')

theorem fieldSigmaClosed0_le_borel (K : Set ℂ) :
    fieldSigmaClosed0 (id : DistC → DistC) K ≤ (inferInstance : MeasurableSpace DistC) := by
  unfold fieldSigmaClosed0
  refine (iInf₂_le 1 one_pos).trans ?_
  unfold fieldSigma0On
  exact Measurable.comap_le (measurable_pi_iff.2 fun ψ =>
    LQGMetric.measurable_distOn_apply ψ.1.1)

end SupercriticalLQGUniqueness.Uniqueness.Objects.BlockMarginal
