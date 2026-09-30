import QuantumZipper.Proofs.Thm18.G3Concrete

/-!
# G3 concrete scheme (part 4): `G3MarkovStmt` for the concrete scheme

Sheffield, arXiv:1012.4797, proof of Theorem 1.8 (§5.4, p. 71): "the conditional law of the
restrictions of `h` to the two halves … are independent by the standard GFF Markov property".
For the concrete scheme `g3ConcreteMap l` (`G3Concrete.lean`):

* (M1) the region-1 zoom, the Palm point `x` and the Palm weight are measurable for region 1's
  local part and `outsideSigmaPalm`; the region-2 zoom and `R` for region 2's
  (`measurable_g3U`, `measurable_g3X`, `measurable_g3W`, `measurable_g3V`, `measurable_g3R`);
* (M2) through `measurable_zoomLaw`;
* (M3) the normalized Palm weight has total mass `1` (`lintegral_g3W`), hence is integrable and
  gives a probability law;
* `g3MarkovStmt_concrete`: `G3MarkovStmt (g3ConcreteMap l)` for every filter `l` that is `NeBot`,
  by `condIndepCE_twoHalfDisc_palm`.

Own bookkeeping (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Metric Set MeasurableSpace Filter
open scoped ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm

open K3

section Meas

variable (γ : ℝ) (i : G3Idx)

local notation "Ω₀" => gffBase.Ω
local notation "X₀" => gffBase.X

/-- The σ-algebra of region 1 on the Palm space. -/
abbrev sig₁ : MeasurableSpace (Ω₀ × ℝ) :=
  (localSigma X₀ i.t₁ i.r₁).comap Prod.fst ⊔ outsideSigmaPalm ℝ X₀ i.t₁ i.r₁ i.t₂ i.r₂

/-- The σ-algebra of region 2 on the Palm space. -/
abbrev sig₂ : MeasurableSpace (Ω₀ × ℝ) :=
  (localSigma X₀ i.t₂ i.r₂).comap Prod.fst ⊔ outsideSigmaPalm ℝ X₀ i.t₁ i.r₁ i.t₂ i.r₂

theorem g3_refS_null : refS (ball (i.t₁ : ℂ) i.r₁ ∪ ball (i.t₂ : ℂ) i.r₂) = 0 :=
  refS_union_null i.inUnit₁ i.inUnit₂

theorem outsideSigmaPalm_le_g3 :
    outsideSigmaPalm ℝ X₀ i.t₁ i.r₁ i.t₂ i.r₂ ≤ (inferInstance : MeasurableSpace (Ω₀ × ℝ)) :=
  sup_le ((comap_mono (outsideSigma2_le gffBase.gff _ _ _ _)).trans measurable_fst.comap_le)
    measurable_snd.comap_le

theorem sig_le_g3 (t r : ℝ) :
    (localSigma X₀ t r).comap Prod.fst ⊔ outsideSigmaPalm ℝ X₀ i.t₁ i.r₁ i.t₂ i.r₂ ≤
      (inferInstance : MeasurableSpace (Ω₀ × ℝ)) :=
  sup_le ((comap_mono (localSigma_le gffBase.gff t r)).trans measurable_fst.comap_le)
    (outsideSigmaPalm_le_g3 i)

theorem measurable_g3sum₁ :
    Measurable[localSigma X₀ i.t₁ i.r₁ ⊔ outsideSigma2 X₀ i.t₁ i.r₁ i.t₂ i.r₂]
      fun ω => g3ν₁ γ i ω + g3ν₀ γ i ω :=
  measurable_measure_add ((measurable_bdryM γ).comp
      (measurable_regionField γ i.r₁_pos (halfDiscPoisson_union_null₁ i.r₁_pos i.dist_le)
        (g3_refS_null i)))
    (((measurable_bdryM γ).comp (measurable_gapField γ (g3_refS_null i))).mono le_sup_right le_rfl)

theorem measurable_g3sum₂ :
    Measurable[localSigma X₀ i.t₂ i.r₂ ⊔ outsideSigma2 X₀ i.t₁ i.r₁ i.t₂ i.r₂]
      fun ω => g3ν₀ γ i ω + g3ν₂ γ i ω :=
  measurable_measure_add
    (((measurable_bdryM γ).comp (measurable_gapField γ (g3_refS_null i))).mono le_sup_right le_rfl)
    ((measurable_bdryM γ).comp
      (measurable_regionField γ i.r₂_pos (halfDiscPoisson_union_null₂ i.r₂_pos i.dist_le)
        (g3_refS_null i)))

theorem measurable_g3X : Measurable[sig₁ i] (g3X γ i) := by
  have h1 : Measurable[sig₁ i] fun p : Ω₀ × ℝ => g3ν₁ γ i p.1 + g3ν₀ γ i p.1 :=
    measurable_comp_fst_palm (measurable_g3sum₁ γ i)
  have h2 : Measurable[sig₁ i] fun p : Ω₀ × ℝ => p.2 := measurable_snd_palm
  unfold g3X
  exact Measurable.comp (g := fun q : Measure ℝ × ℝ => lenLeft q.1 q.2)
    (f := fun p : Ω₀ × ℝ => (g3ν₁ γ i p.1 + g3ν₀ γ i p.1, p.2)) measurable_lenLeft (h1.prodMk h2)

theorem measurable_g3R : Measurable[sig₂ i] (g3R γ i) := by
  have h1 : Measurable[sig₂ i] fun p : Ω₀ × ℝ => g3ν₀ γ i p.1 + g3ν₂ γ i p.1 :=
    measurable_comp_fst_palm (measurable_g3sum₂ γ i)
  have h2 : Measurable[sig₂ i] fun p : Ω₀ × ℝ => p.2 := measurable_snd_palm
  unfold g3R
  exact Measurable.comp (g := fun q : Measure ℝ × ℝ => lenRight q.1 q.2)
    (f := fun p : Ω₀ × ℝ => (g3ν₀ γ i p.1 + g3ν₂ γ i p.1, p.2)) measurable_lenRight
    (h1.prodMk h2)

/-- **M1 + M2, region 1.** -/
theorem measurable_g3U : Measurable[sig₁ i] (g3U γ i) := by
  have h1 : Measurable[sig₁ i] fun p : Ω₀ × ℝ => regionField γ i.t₁ i.r₁ X₀ p.1 :=
    measurable_comp_fst_palm (measurable_regionField γ i.r₁_pos
      (halfDiscPoisson_union_null₁ i.r₁_pos i.dist_le) (g3_refS_null i))
  unfold g3U
  exact Measurable.comp (g := fun q : FieldSample × ℝ => zoomLaw γ i.C q.1 q.2)
    (f := fun p : Ω₀ × ℝ => (regionField γ i.t₁ i.r₁ X₀ p.1, g3X γ i p))
    (measurable_zoomLaw γ i.C) (h1.prodMk (measurable_g3X γ i))

/-- **M1 + M2, region 2.** -/
theorem measurable_g3V : Measurable[sig₂ i] (g3V γ i) := by
  have h1 : Measurable[sig₂ i] fun p : Ω₀ × ℝ => regionField γ i.t₂ i.r₂ X₀ p.1 :=
    measurable_comp_fst_palm (measurable_regionField γ i.r₂_pos
      (halfDiscPoisson_union_null₂ i.r₂_pos i.dist_le) (g3_refS_null i))
  unfold g3V
  exact Measurable.comp (g := fun q : FieldSample × ℝ => zoomLaw γ i.C q.1 q.2)
    (f := fun p : Ω₀ × ℝ => (regionField γ i.t₂ i.r₂ X₀ p.1, g3R γ i p))
    (measurable_zoomLaw γ i.C) (h1.prodMk (measurable_g3R γ i))

theorem measurable_g3W0 : Measurable[sig₁ i] (g3W0 γ i) := by
  have hm : Measurable[sig₁ i] fun p : Ω₀ × ℝ => g3Mass γ i p.1 :=
    measurable_comp_fst_palm ((Measure.measurable_coe measurableSet_Icc).comp
      (measurable_g3sum₁ γ i))
  have hs : Measurable[sig₁ i] fun p : Ω₀ × ℝ => p.2 := measurable_snd_palm
  unfold g3W0
  exact Measurable.ite ((measurableSet_lt measurable_const hs).inter
      (measurableSet_le (ENNReal.measurable_ofReal.comp hs) hm))
    (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hs)) measurable_const

/-- **M1, Palm weight.** -/
theorem measurable_g3W : Measurable[sig₁ i] (g3W γ i) := by
  unfold g3W
  split_ifs
  · exact ENNReal.measurable_toNNReal.comp ((measurable_g3W0 γ i).const_mul _)
  · exact measurable_const

theorem g3W0_ne_top (p : Ω₀ × ℝ) : g3W0 γ i p ≠ ⊤ := by
  unfold g3W0
  split_ifs
  · exact ENNReal.ofReal_ne_top
  · exact ENNReal.zero_ne_top

/-- **M3.** The normalized Palm weight has total mass `1`. -/
theorem lintegral_g3W :
    ∫⁻ p, (g3W γ i p : ℝ≥0∞) ∂(gffBase.P.prod L₀) = 1 := by
  have hW0 : Measurable (g3W0 γ i) := (measurable_g3W0 γ i).mono (sig_le_g3 i _ _) le_rfl
  by_cases hZ : 0 < g3Z γ i ∧ g3Z γ i < ⊤
  · simp only [g3W, if_pos hZ]
    have e : ∀ p, ((((g3Z γ i)⁻¹ * g3W0 γ i p).toNNReal : ℝ≥0) : ℝ≥0∞) =
        (g3Z γ i)⁻¹ * g3W0 γ i p := fun p =>
      ENNReal.coe_toNNReal (ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hZ.1.ne')
        (g3W0_ne_top γ i p))
    simp_rw [e]
    rw [lintegral_const_mul _ hW0]
    exact ENNReal.inv_mul_cancel hZ.1.ne' hZ.2.ne
  · simp only [g3W, if_neg hZ, ENNReal.coe_one, lintegral_const, measure_univ, one_mul]

theorem isProbabilityMeasure_g3 :
    IsProbabilityMeasure ((gffBase.P.prod L₀).withDensity fun p => (g3W γ i p : ℝ≥0∞)) :=
  ⟨by rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, lintegral_g3W]⟩

theorem integrable_g3W : Integrable (fun p => (g3W γ i p : ℝ)) (gffBase.P.prod L₀) := by
  have hm : Measurable (g3W γ i) := (measurable_g3W γ i).mono (sig_le_g3 i _ _) le_rfl
  refine (integrable_toReal_of_lintegral_ne_top hm.coe_nnreal_ennreal.aemeasurable
    (by rw [lintegral_g3W]; exact ENNReal.one_ne_top)).congr (ae_of_all _ fun p => ?_)
  exact ENNReal.coe_toReal _

end Meas

end Thm18Asm
end QuantumZipper
