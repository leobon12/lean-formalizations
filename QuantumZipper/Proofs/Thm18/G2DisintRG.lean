import QuantumZipper.Proofs.Thm18.G2DisintRF
import QuantumZipper.Proofs.Thm18.G2DisintXG

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G2 disintegration, `R` side: `G2RootRDisintStmt` from zoom locality

Sheffield (arXiv:1012.4797, proof of Prop. 5.5, p. 66). With the Gaussian bump decomposition
(`g2BumpDecompStmt_holds`), the local rule (`g2_ae_bdryM_loc`), positivity (`g2_ae_pos_g3Hν`) and
the comparison bound `g2x_bound`, the only remaining input is zoom locality `G2ZoomLocStmt`
(the zoom at the root does not see a bump away from it once `C` is large).
Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm

local notation "Ω₀" => gffBase.Ω

open Classical in
/-- The Palm mass `ν[−δ, 0]` read from `h₀` (region 1 and the gap field do not see `φ₂`). -/
def g2rMfun (γ : ℝ) (i : G3Idx) (φ : ℂ → ℝ) (y : AdmIdx → ℝ) : ℝ≥0∞ :=
  (bdryM γ (restrictField (circIn i.t₁ i.r₁) (g2Field γ φ y 0)) +
    bdryM γ (restrictField (circOut i.t₁ i.r₁ i.t₂ i.r₂) (g2Field γ φ y 0))) (Icc (-i.δ) 0)

theorem measurable_restrictField_g2 (A : Set (Measure ℂ)) {E : Type*} [MeasurableSpace E]
    {F : E → FieldSample} (hF : Measurable F) : Measurable fun e => restrictField A (F e) := by
  classical
  refine measurable_pi_iff.2 fun μ => ?_
  by_cases h : μ ∈ A
  · simp only [restrictField, if_pos h]; exact (measurable_pi_apply μ).comp hF
  · simp only [restrictField, if_neg h]; exact measurable_const

theorem measurable_g2rMfun (γ : ℝ) (i : G3Idx) (φ : ℂ → ℝ) : Measurable (g2rMfun γ i φ) := by
  have hF : Measurable fun y : AdmIdx → ℝ => g2Field γ φ y 0 :=
    (measurable_g2Field γ φ).comp (measurable_id.prodMk measurable_const)
  exact (Measure.measurable_coe measurableSet_Icc).comp (measurable_measure_add
    ((measurable_bdryM γ).comp (measurable_restrictField_g2 _ hF))
    ((measurable_bdryM γ).comp (measurable_restrictField_g2 _ hF)))

theorem restrictField_g2_eq {γ : ℝ} {φ : ℂ → ℝ} (α : gffBase.Ω → ℝ) (ω : gffBase.Ω)
    {A : Set (Measure ℂ)} (hA : ∀ μ ∈ A, ∃ (d : ℂ) (r : ℝ), 0 < r ∧ μ = foldedCircle d r ∧
      ∫ z, φ z ∂μ = 0) :
    restrictField A (normField γ gffBase.X ω) = restrictField A (g2Field γ φ (g2Y φ α ω) 0) := by
  classical
  funext μ
  unfold restrictField
  split_ifs with h
  · obtain ⟨d, r, hr, rfl, hz⟩ := hA μ h
    rw [← g2Field_Y_prob γ φ α ω _ (D3Plus.isAdmissibleH_foldedCircle' d hr),
      g2Field_sub γ φ _ (α ω) 0, hz, mul_zero, add_zero]
  · rfl

theorem g3Mass_eq_g2rMfun {γ : ℝ} (i : G3Idx) {m : ℝ} (hm : 0 < m) (i₀ : G3Idx)
    (ht₁ : i.t₁ = i₀.t₁) (hr₁ : i.r₁ = i₀.r₁) (ht₂ : i.t₂ = i₀.t₂) (hr₂ : i.r₂ = i₀.r₂)
    (α : gffBase.Ω → ℝ) (ω : gffBase.Ω) :
    g3Mass γ i ω = g2rMfun γ i (g2rφ i₀ m) (g2Y (g2rφ i₀ m) α ω) := by
  have hz : ∀ μ : Measure ℂ, (∀ᵐ z ∂μ, g2rφ i₀ m z = 0) → ∫ z, g2rφ i₀ m z ∂μ = 0 :=
    fun μ h => integral_eq_zero_of_ae h
  unfold g3Mass g2rMfun g3ν₁ g3ν₀ regionField gapField
  rw [restrictField_g2_eq α ω (φ := g2rφ i₀ m) (fun μ hμ => ?_),
    restrictField_g2_eq α ω (φ := g2rφ i₀ m) (fun μ hμ => ?_)]
  · obtain ⟨d, r, hr, rfl, hnull⟩ := hμ
    refine ⟨d, r, hr, rfl, hz _ ?_⟩
    rw [ae_iff]
    refine measure_mono_null (fun z hz => ?_) (measure_mono_null subset_union_right hnull)
    by_contra hb
    rw [ht₂, hr₂] at hb
    exact hz (g2rφ_zero_off i₀ hm hb)
  · obtain ⟨d, r, hr, rfl, r', hr', hnull⟩ := hμ
    refine ⟨d, r, hr, rfl, hz _ ?_⟩
    rw [ae_iff]
    refine measure_mono_null (fun z hz => ?_) hnull
    by_contra hb
    rw [ht₁] at hb
    exact hz (g2rφ_zero_region1 i₀ hm (Metric.closedBall_subset_closedBall
      (by rw [← hr₁]; exact hr'.le) (not_not.1 hb)))

theorem g2OutV_eq_Psi₂ {φ : ℂ → ℝ} {t₁ r₁ t₂ r₂ : ℝ}
    (hφ : ∀ z, z ∉ Metric.ball (t₂ : ℂ) r₂ → φ z = 0) (α : gffBase.Ω → ℝ) (ω : gffBase.Ω) :
    g2OutV gffBase.X t₁ r₁ t₂ r₂ ω = g2Psi t₁ r₁ t₂ r₂ (g2Y φ α ω) := by
  funext p
  have hz : ∀ μ : Measure ℂ, μ (Metric.ball (t₁ : ℂ) r₁ ∪ Metric.ball (t₂ : ℂ) r₂) = 0 →
      ∫ z, φ z ∂μ = 0 := by
    intro μ hμ
    refine integral_eq_zero_of_ae ?_
    have h1 : μ (Metric.ball (t₂ : ℂ) r₂) = 0 := measure_mono_null subset_union_right hμ
    rw [Filter.EventuallyEq, ae_iff]
    refine measure_mono_null (fun z hz => ?_) h1
    by_contra hb
    exact hz (hφ z hb)
  simp only [g2OutV, g2Psi, g2Y, hz _ p.2.2.2.2.1, hz _ p.2.2.2.2.2, mul_zero, sub_zero]
  exact (normX_sub_of_mass_eq gffBase.X ω p.2.2.2.1).symm

/-- **`G2RootRDisintStmt` from zoom locality.** -/
theorem g2RootRDisintStmt_of_zoom {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hZ : G2ZoomLocStmt γ) :
    G2RootRDisintStmt γ := by
  intro t ht δ η m hm
  by_cases hex : ∃ i₀ : G3Idx, i₀.1.1 = δ ∧ i₀.1.2.1 = η
  swap
  · refine ⟨1, one_pos, fun ε _ => ⟨Unit, inferInstance, 0, inferInstance, gaussianReal 0 1,
      inferInstance, fun _ a => a, gaussianReal_absolutelyContinuous 0 one_ne_zero,
      measurable_snd, fun _ => differentiable_id, fun _ a => by simp, fun κ _ =>
      ⟨fun _ => 0, measurable_const, fun _ => le_rfl, Eventually.of_forall fun C i hi => ?_⟩⟩⟩
    exact absurd ⟨i, by rw [hi], by rw [hi]⟩ hex
  obtain ⟨i₀, hδ₀, hη₀⟩ := hex
  obtain ⟨hφ1, hφ2, hφ3, hφ4, hφ5⟩ := g2rφ_bump_hyps i₀ hm
  obtain ⟨α, v, hv, hαm, hlaw, hind⟩ := g2BumpDecompStmt_holds _ hφ1 hφ2 hφ3 hφ4 hφ5
  have hindY := indepFun_g2Y hind
  have hYm := measurable_g2Y (g2rφ i₀ m) hαm
  have : IsProbabilityMeasure (gffBase.P.map α) :=
    (Measure.isProbabilityMeasure_map_iff hαm.aemeasurable).2 inferInstance
  have hN : gffBase.P.map α ≪ volume := by
    rw [hlaw]; exact gaussianReal_absolutelyContinuous 0 hv.ne'
  have hQ : IsFiniteMeasure ((gffBase.P.map (g2Y (g2rφ i₀ m) α)) ⊗ₘ g2rκM γ i₀ m) := by
    refine ⟨?_⟩
    rw [← lintegral_one, Measure.lintegral_compProd measurable_const]
    simp only [lintegral_one]
    rw [lintegral_map (Kernel.measurable_coe _ MeasurableSet.univ) hYm]
    exact g2r_kernel_mass hγ hγ2 i₀ hm α
  refine ⟨g2rR i₀ m, g2rR_pos i₀ hm, fun ε hε => ⟨(AdmIdx → ℝ) × ℝ, inferInstance,
    (gffBase.P.map (g2Y (g2rφ i₀ m) α)) ⊗ₘ g2rκM γ i₀ m, hQ, gffBase.P.map α, inferInstance,
    g2rf γ i₀ m, hN, measurable_g2rf γ i₀ m, g2rf_differentiable hγ i₀ hm,
    g2rf_deriv_pos hγ i₀ hm, fun κ hκ => ⟨g2rgap γ i₀ m κ, measurable_g2rgap γ i₀ m κ,
    g2rgap_nonneg γ i₀ m hκ.1.le, ?_⟩⟩⟩
  have hzt := g2r_zoomErr_tendsto hγ hγ2 hZ i₀ hm hαm ht
  have hεpos : (0 : ℝ≥0∞) < ENNReal.ofReal ε := ENNReal.ofReal_pos.2 hε
  filter_upwards [hzt.eventually (gt_mem_nhds hεpos)] with C hC i hi G hG
  have hδi : i.δ = i₀.δ := by unfold G3Idx.δ; rw [hi]; exact hδ₀.symm
  have hηi : i.η = i₀.η := by unfold G3Idx.η; rw [hi]; exact hη₀.symm
  have hCi : i.C = C := by unfold G3Idx.C; rw [hi]
  have ht₁ : i.t₁ = i₀.t₁ := by unfold G3Idx.t₁; rw [hδi, hηi]
  have hr₁ : i.r₁ = i₀.r₁ := by unfold G3Idx.r₁; rw [hδi, hηi]
  have ht₂ : i.t₂ = i₀.t₂ := by unfold G3Idx.t₂; rw [hηi]
  have hr₂ : i.r₂ = i₀.r₂ := by unfold G3Idx.r₂; rw [hηi]
  obtain ⟨G', hG', hGeq⟩ := exists_outside_factor hG
  have hzoff : ∀ z, z ∉ Metric.ball (i.t₂ : ℂ) i.r₂ → g2rφ i₀ m z = 0 := fun z hz =>
    g2rφ_zero_off i₀ hm (by rwa [ht₂, hr₂] at hz)
  have hbound : (∫⁻ ω, ∫⁻ x, g2xZD γ C (g2rφ i₀ m) t (g2Y (g2rφ i₀ m) α ω, x, α ω)
      ∂(g2rκM γ i₀ m (g2Y (g2rφ i₀ m) α ω)) ∂gffBase.P).toReal ≤ ε :=
    ENNReal.toReal_le_of_le_ofReal hε.le hC.le
  have htm := measurableSet_lawCyl ht
  set Psi' : (AdmIdx → ℝ) → (OutIdx2 i.t₁ i.r₁ i.t₂ i.r₂ → ℝ) × ℝ≥0∞ :=
    fun y => (g2Psi i.t₁ i.r₁ i.t₂ i.r₂ y, g2rMfun γ i (g2rφ i₀ m) y) with hPsi'
  have hPsi : Measurable Psi' :=
    (measurable_g2Psi i.t₁ i.r₁ i.t₂ i.r₂).prodMk (measurable_g2rMfun γ i _)
  set G'' : Set (((OutIdx2 i.t₁ i.r₁ i.t₂ i.r₂ → ℝ) × ℝ≥0∞) × ℝ) :=
    {p | (p.1.1, p.2) ∈ G' ∧ ENNReal.ofReal p.2 ≤ p.1.2} with hG''def
  have hG'' : MeasurableSet G'' :=
    (((measurable_fst.comp measurable_fst).prodMk measurable_snd) hG').inter
      (measurableSet_le (ENNReal.measurable_ofReal.comp measurable_snd)
        (measurable_snd.comp measurable_fst))
  have hMass : ∀ ω, g3Mass γ i ω = g2rMfun γ i (g2rφ i₀ m) (g2Y (g2rφ i₀ m) α ω) :=
    fun ω => g3Mass_eq_g2rMfun i hm i₀ ht₁ hr₁ ht₂ hr₂ α ω
  have hidx : i.t₂ + i.r₂ = i₀.t₂ + i₀.r₂ := by rw [ht₂, hr₂]
  refine ⟨{q : ((AdmIdx → ℝ) × ℝ) × ℝ | zoomLaw γ C (g2Field γ (g2rφ i₀ m) q.1.1 0) q.1.2 ∈ t ∧
      (Psi' q.1.1, q.2) ∈ G''}, ?_, ?_, fun ρ hρ => ?_⟩
  · exact ((measurable_zoomLaw γ C).comp (((measurable_g2Field γ _).comp
      ((measurable_fst.comp measurable_fst).prodMk measurable_const)).prodMk
      (measurable_snd.comp measurable_fst)) htm).inter
      (((hPsi.comp (measurable_fst.comp measurable_fst)).prodMk measurable_snd) hG'')
  · rw [g3RootIntR_eq_of_idx hidx]
    refine (g2r_bound hγ hγ2 i₀ hm hαm hindY C htm _ hPsi hG'' (fun _ ℓ => ℓ)
      measurable_snd (g3RootEvR γ i t m G ∩ g3TM γ i) ?_).trans hbound
    · filter_upwards with ω h1 h2 h3 h4 x hx
      by_cases hxM : x ∈ g2rM i₀ m
      · rw [indicator_of_mem hxM]
        have hmarg : |x - i.t₂| + m < i.r₂ := by rw [ht₂, hr₂]; exact hxM.1
        have hiff : (ω, (g3Hν γ ω (Icc 0 x)).toReal, x) ∈ g3RootEvR γ i t m G ∩ g3TM γ i ↔
            (g2Y (g2rφ i₀ m) α ω, x, α ω) ∈ {p : (AdmIdx → ℝ) × ℝ × ℝ |
              zoomLaw γ C (g2Field γ (g2rφ i₀ m) p.1 p.2.2) p.2.1 ∈ t ∧
              (Psi' p.1, (fun _ ℓ => ℓ) (p.1, p.2.1)
                (g2rf γ i₀ m (p.1, p.2.1) p.2.2)) ∈ G''} := by
          simp only [g3RootEvR, g3TM, mem_inter_iff, mem_setOf_eq, hCi,
            zoomLaw_eq_g2Field γ (g2rφ i₀ m) α ω, h3 x hxM, hG''def, hPsi', hMass]
          rw [hGeq, mem_preimage, g2OutV_eq_Psi₂ hzoff α ω]
          exact ⟨fun h => ⟨h.1.1, h.1.2.2, h.2⟩, fun h => ⟨⟨h.1, hmarg, h.2.1⟩, h.2.2⟩⟩
        by_cases hmem : (ω, (g3Hν γ ω (Icc 0 x)).toReal, x) ∈ g3RootEvR γ i t m G ∩ g3TM γ i
        · rw [indicator_of_mem hmem, indicator_of_mem (hiff.1 hmem)]; rfl
        · rw [indicator_of_notMem hmem, indicator_of_notMem (mt hiff.2 hmem)]
      · rw [indicator_of_notMem hxM, indicator_of_notMem]
        intro hmem
        exact hxM ⟨by rw [← ht₂, ← hr₂]; exact hmem.1.2.1, hx⟩
  · rw [g3RootIntR_eq_of_idx hidx]
    have hΛ : Measurable (Function.uncurry fun (ξ : (AdmIdx → ℝ) × ℝ) (ℓ : ℝ) =>
        ℓ - min (g2rgap γ i₀ m κ ξ) ρ) :=
      measurable_snd.sub (((measurable_g2rgap γ i₀ m κ).comp measurable_fst).min measurable_const)
    refine (g2r_bound hγ hγ2 i₀ hm hαm hindY C htm _ hPsi hG''
      (fun ξ ℓ => ℓ - min (g2rgap γ i₀ m κ ξ) ρ) hΛ (g3RootEvRclip γ i t m κ ρ G) ?_).trans hbound
    filter_upwards with ω h1 h2 h3 h4 x hx
    by_cases hxM : x ∈ g2rM i₀ m
    · rw [indicator_of_mem hxM]
      have hmarg : |x - i.t₂| + m < i.r₂ := by rw [ht₂, hr₂]; exact hxM.1
      have hcut : max (g3CutLenR γ κ ω x) ((g3Hν γ ω (Icc 0 x)).toReal - ρ) =
          g2rf γ i₀ m (g2Y (g2rφ i₀ m) α ω, x) (α ω) -
            min (g2rgap γ i₀ m κ (g2Y (g2rφ i₀ m) α ω, x)) ρ := by
        rw [g3CutLenR, h4 κ hκ.1.le hκ.2 x hxM, ← h3 x hxM, g2_max_sub_min]
      have hiff : (ω, (g3Hν γ ω (Icc 0 x)).toReal, x) ∈ g3RootEvRclip γ i t m κ ρ G ↔
          (g2Y (g2rφ i₀ m) α ω, x, α ω) ∈ {p : (AdmIdx → ℝ) × ℝ × ℝ |
            zoomLaw γ C (g2Field γ (g2rφ i₀ m) p.1 p.2.2) p.2.1 ∈ t ∧
            (Psi' p.1, (fun ξ ℓ => ℓ - min (g2rgap γ i₀ m κ ξ) ρ) (p.1, p.2.1)
              (g2rf γ i₀ m (p.1, p.2.1) p.2.2)) ∈ G''} := by
        simp only [g3RootEvRclip, mem_setOf_eq, hCi, zoomLaw_eq_g2Field γ (g2rφ i₀ m) α ω, hcut,
          hG''def, hPsi', hMass]
        rw [hGeq, mem_preimage, g2OutV_eq_Psi₂ hzoff α ω]
        exact ⟨fun h => ⟨h.1, h.2.2.1, h.2.2.2⟩, fun h => ⟨h.1, hmarg, h.2.1, h.2.2⟩⟩
      by_cases hmem : (ω, (g3Hν γ ω (Icc 0 x)).toReal, x) ∈ g3RootEvRclip γ i t m κ ρ G
      · rw [indicator_of_mem hmem, indicator_of_mem (hiff.1 hmem)]; rfl
      · rw [indicator_of_notMem hmem, indicator_of_notMem (mt hiff.2 hmem)]
    · rw [indicator_of_notMem hxM, indicator_of_notMem]
      intro hmem
      exact hxM ⟨by rw [← ht₂, ← hr₂]; exact hmem.2.1, hx⟩

end Thm18Asm
end QuantumZipper
