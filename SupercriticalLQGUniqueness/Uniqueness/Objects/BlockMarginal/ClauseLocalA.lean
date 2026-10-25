import SupercriticalLQGUniqueness.Uniqueness.Objects.BlockMarginal.ClauseTools
import SupercriticalLQGUniqueness.Uniqueness.Objects.ClauseMeasurability.EventMeas




 









set_option autoImplicit false

noncomputable section

open Set MeasureTheory Metric Filter
open LQGMetric.Blueprint
open scoped ENNReal Topology

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BlockMarginal

open LQGMetric (DistC restrictTo addConst)

 
def bigAnn (C : Objects.CorrectedEvent.Constants) : Set ℂ := Objects.CorrectedEvent.cann 0 C.r (4 * C.r)

theorem bigAnn_open_nonempty (C : Objects.CorrectedEvent.Constants) :
    (LQGMetric.Blueprint.annulus (0 : ℂ) C.r (4 * C.r) : Set ℂ).Nonempty := by
  have hr := C.rPos
  refine ⟨((2 * C.r : ℝ) : ℂ), ?_⟩
  change C.r < ‖((2 * C.r : ℝ) : ℂ) - 0‖ ∧ ‖((2 * C.r : ℝ) : ℂ) - 0‖ < 4 * C.r
  rw [sub_zero, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  constructor <;> linarith

theorem annulus_subset_bigAnn (C : Objects.CorrectedEvent.Constants) :
    (LQGMetric.Blueprint.annulus (0 : ℂ) C.r (4 * C.r) : Set ℂ) ⊆ bigAnn C := by
  intro x hx
  change C.r < ‖x - 0‖ ∧ ‖x - 0‖ < 4 * C.r at hx
  change C.r ≤ dist x 0 ∧ dist x 0 ≤ 4 * C.r
  rw [dist_eq_norm]
  exact ⟨hx.1.le, hx.2.le⟩

 
theorem exists_bigAnn_test (C : Objects.CorrectedEvent.Constants) :
    ∃ ψ : LQGMetric.TestC, tsupport (ψ : ℂ → ℝ) ⊆ bigAnn C ∧ ∫ x, ψ x = 1 := by
  obtain ⟨ψ, hψ, hψ1⟩ := LQGMetric.GermSplit.exists_test_unit (bigAnn_open_nonempty C)
  exact ⟨ψ, hψ.trans (annulus_subset_bigAnn C), hψ1⟩

theorem cann_subset_bigAnn (C : Objects.CorrectedEvent.Constants) {a b : ℝ} (ha : C.r ≤ a) (hb : b ≤ 4 * C.r) :
    Objects.CorrectedEvent.cann 0 a b ⊆ bigAnn C := by
  intro x hx
  exact ⟨ha.trans hx.1, hx.2.trans hb⟩

theorem ann_subset_bigAnn (C : Objects.CorrectedEvent.Constants) {a b : ℝ} (ha : C.r ≤ a) (hb : b ≤ 4 * C.r) :
    Objects.CorrectedEvent.ann 0 a b ⊆ bigAnn C := by
  intro x hx
  exact ⟨ha.trans hx.1.le, hx.2.le.trans hb⟩

theorem sphere_r_subset_bigAnn (C : Objects.CorrectedEvent.Constants) : sphere (0 : ℂ) |C.r| ⊆ bigAnn C := by
  intro x hx
  rw [mem_sphere, abs_of_pos C.rPos] at hx
  have hr := C.rPos
  exact ⟨hx.ge, by rw [hx]; linarith⟩

theorem thickening_subset_nbhdO {ε : ℝ} {S K : Set ℂ} (hSK : S ⊆ K) :
    thickening ε S ⊆ (nbhdO ε K : Set ℂ) :=
  thickening_subset_of_subset ε hSK

theorem subset_nbhdO {ε : ℝ} (hε : 0 < ε) {S K : Set ℂ} (hSK : S ⊆ K) :
    S ⊆ (nbhdO ε K : Set ℂ) :=
  hSK.trans (self_subset_thickening hε K)

 

theorem ae_scale_facts (μ : Measure DistC) [IsProbabilityMeasure μ]
    (hμ : IsNormalizedWholePlaneGFF (id : DistC → DistC) μ)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D)
    (c : DistC → ℝ) (C : Objects.CorrectedEvent.Constants) :
    ∀ᵐ g ∂μ, (∀ p : ℂ × ℂ, D (addConst g (c g)) p =
        ENNReal.ofReal (Real.exp ((ξ : ℝ) * c g)) * D g p) ∧
      LQGMetric.circleAvg (addConst g (c g)) C.r 0 = LQGMetric.circleAvg g C.r 0 + c g := by
  have hwhole : LQGMetric.IsGFFPlusCont (id : DistC → DistC) μ :=
    LQGMetric.GM.Tight.isGFFPlusCont_of_wp hμ.1
  filter_upwards [Positivity.Witnesses.ae_addConst_eq_mul μ id hwhole ξ Q D hD c,
    LQGMetric.CircleAvg.ae_circleAvg_addConst hμ.1 0 C.rPos] with g hg hc
  exact ⟨hg, hc (c g)⟩

 

theorem S1_iff_of_local (C : Objects.CorrectedEvent.Constants) (D₁ D₂ : LSCMetric) (g₁ g₂ : DistC)
    (hB₁ : BiLipschitz.Barrier.Barrier D₁) (hB₂ : BiLipschitz.Barrier.Barrier D₂) (hL₁ : D₁.IsLengthSpace) (hL₂ : D₂.IsLengthSpace)
    {ε : ℝ} (hε : 0 < ε)
    (hint : D₁.internal (thickening ε (bigAnn C)) = D₂.internal (thickening ε (bigAnn C)))
    (hres : restrictTo (nbhdO ε (bigAnn C)) g₁ = restrictTo (nbhdO ε (bigAnn C)) g₂) :
    Objects.CorrectedEvent.S1 C D₁ g₁ ↔ Objects.CorrectedEvent.S1 C D₂ g₂ := by
  have hr := C.rPos
  have h1 : Objects.CorrectedEvent.acr D₁ 0 C.r (1.5 * C.r) = Objects.CorrectedEvent.acr D₂ 0 C.r (1.5 * C.r) :=
    acr_eq_of_internal_eq D₁ D₂ hB₁ hB₂ hL₁ hL₂ _ hint 0 hr (by linarith)
      (subset_nbhdO hε (cann_subset_bigAnn C le_rfl (by linarith)))
  have h2 : Objects.CorrectedEvent.acr D₁ 0 (2.5 * C.r) (3 * C.r) = Objects.CorrectedEvent.acr D₂ 0 (2.5 * C.r) (3 * C.r) :=
    acr_eq_of_internal_eq D₁ D₂ hB₁ hB₂ hL₁ hL₂ _ hint 0 (by linarith) (by linarith)
      (subset_nbhdO hε (cann_subset_bigAnn C (by linarith) (by linarith)))
  have hN : Objects.CorrectedEvent.normalizer C g₁ C.r 0 = Objects.CorrectedEvent.normalizer C g₂ C.r 0 :=
    normalizer_eq_of_circleAvg_eq C (circleAvg_eq_of_restrictTo_eq hres hε
      (thickening_subset_nbhdO (sphere_r_subset_bigAnn C)))
  unfold Objects.CorrectedEvent.S1
  rw [h1, h2, hN]

theorem S1_iff_of_scale (C : Objects.CorrectedEvent.Constants) (D₁ D₂ : LSCMetric) (g₁ g₂ : DistC) {e : ℝ≥0∞}
    (he0 : e ≠ 0) (heTop : e ≠ ⊤) (hscale : ∀ x y : ℂ, D₂ (x, y) = e * D₁ (x, y))
    (hN : Objects.CorrectedEvent.normalizer C g₂ C.r 0 = e * Objects.CorrectedEvent.normalizer C g₁ C.r 0) :
    Objects.CorrectedEvent.S1 C D₂ g₂ ↔ Objects.CorrectedEvent.S1 C D₁ g₁ := by
  unfold Objects.CorrectedEvent.S1
  rw [Objects.ProbabilityS3.acr_eq_mul_of_dist_scale D₁ D₂ e he0 heTop hscale,
    Objects.ProbabilityS3.acr_eq_mul_of_dist_scale D₁ D₂ e he0 heTop hscale, hN,
    scale_le_iff he0 heTop, scale_le_iff he0 heTop]

theorem aeEventIn_S1 (μ : Measure DistC) [IsProbabilityMeasure μ]
    (hμ : IsNormalizedWholePlaneGFF (id : DistC → DistC) μ)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D)
    (C : Objects.CorrectedEvent.Constants) (hCξ : C.ξ = ξ) :
    AEEventIn μ (fieldSigmaClosed0 id (bigAnn C)) {g | Objects.CorrectedEvent.S1 C (D g) g} := by
  obtain ⟨ψ, hψK, hψ1⟩ := exists_bigAnn_test C
  refine aeEventIn_closed0_of_det μ hμ ξ Q D hD (bigAnn C) ψ hψK hψ1 _
    (Objects.ClauseMeasurability.measurableSet_S1 C D hD.measurable) ?_ ?_
  · intro ε hε g₁ g₂ hB₁ hB₂ hL₁ hL₂ hint hres h1
    exact (S1_iff_of_local C (D g₁) (D g₂) g₁ g₂ hB₁ hB₂ hL₁ hL₂ hε hint hres).mp h1
  · filter_upwards [ae_scale_facts μ hμ ξ Q D hD (fun g => -(g ψ)) C] with g hg
    obtain ⟨hs, hc⟩ := hg
    have he0 : ENNReal.ofReal (Real.exp ((ξ : ℝ) * -(g ψ))) ≠ 0 :=
      (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
    have hN := normalizer_addConst C hc
    rw [hCξ] at hN
    exact S1_iff_of_scale C (D g) (D (addConst g (-(g ψ)))) g (addConst g (-(g ψ))) he0
      ENNReal.ofReal_ne_top (fun x y => hs (x, y)) hN

 

theorem S2_iff_of_local (C : Objects.CorrectedEvent.Constants) (D₁ D₂ : LSCMetric) (g₁ g₂ : DistC)
    {ε : ℝ} (hε : 0 < ε)
    (hint : D₁.internal (thickening ε (bigAnn C)) = D₂.internal (thickening ε (bigAnn C)))
    (hres : restrictTo (nbhdO ε (bigAnn C)) g₁ = restrictTo (nbhdO ε (bigAnn C)) g₂) :
    Objects.CorrectedEvent.S2 C D₁ g₁ ↔ Objects.CorrectedEvent.S2 C D₂ g₂ := by
  have hr := C.rPos
  have h1 : Objects.CorrectedEvent.around D₁ 0 (3 * C.r) (4 * C.r) = Objects.CorrectedEvent.around D₂ 0 (3 * C.r) (4 * C.r) :=
    around_eq_of_internal_eq D₁ D₂ _ hint 0 (by linarith) (by linarith)
      (subset_nbhdO hε (ann_subset_bigAnn C (by linarith) le_rfl))
  have hN : Objects.CorrectedEvent.normalizer C g₁ C.r 0 = Objects.CorrectedEvent.normalizer C g₂ C.r 0 :=
    normalizer_eq_of_circleAvg_eq C (circleAvg_eq_of_restrictTo_eq hres hε
      (thickening_subset_nbhdO (sphere_r_subset_bigAnn C)))
  unfold Objects.CorrectedEvent.S2
  rw [h1, hN]

theorem S2_iff_of_scale (C : Objects.CorrectedEvent.Constants) (D₁ D₂ : LSCMetric) (g₁ g₂ : DistC) {e : ℝ≥0∞}
    (he0 : e ≠ 0) (heTop : e ≠ ⊤) (hscale : ∀ x y : ℂ, D₂ (x, y) = e * D₁ (x, y))
    (hN : Objects.CorrectedEvent.normalizer C g₂ C.r 0 = e * Objects.CorrectedEvent.normalizer C g₁ C.r 0) :
    Objects.CorrectedEvent.S2 C D₂ g₂ ↔ Objects.CorrectedEvent.S2 C D₁ g₁ := by
  unfold Objects.CorrectedEvent.S2
  rw [Objects.ProbabilityS3.around_eq_mul_of_dist_scale D₁ D₂ e he0 heTop hscale, hN,
    scale_le_iff' he0 heTop]

theorem aeEventIn_S2 (μ : Measure DistC) [IsProbabilityMeasure μ]
    (hμ : IsNormalizedWholePlaneGFF (id : DistC → DistC) μ)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D)
    (C : Objects.CorrectedEvent.Constants) (hCξ : C.ξ = ξ) :
    AEEventIn μ (fieldSigmaClosed0 id (bigAnn C)) {g | Objects.CorrectedEvent.S2 C (D g) g} := by
  obtain ⟨ψ, hψK, hψ1⟩ := exists_bigAnn_test C
  refine aeEventIn_closed0_of_det μ hμ ξ Q D hD (bigAnn C) ψ hψK hψ1 _
    (Objects.ClauseMeasurability.measurableSet_S2 C D hD.measurable) ?_ ?_
  · intro ε hε g₁ g₂ _ _ _ _ hint hres h1
    exact (S2_iff_of_local C (D g₁) (D g₂) g₁ g₂ hε hint hres).mp h1
  · filter_upwards [ae_scale_facts μ hμ ξ Q D hD (fun g => -(g ψ)) C] with g hg
    obtain ⟨hs, hc⟩ := hg
    have he0 : ENNReal.ofReal (Real.exp ((ξ : ℝ) * -(g ψ))) ≠ 0 :=
      (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
    have hN := normalizer_addConst C hc
    rw [hCξ] at hN
    exact S2_iff_of_scale C (D g) (D (addConst g (-(g ψ)))) g (addConst g (-(g ψ))) he0
      ENNReal.ofReal_ne_top (fun x y => hs (x, y)) hN

 

theorem aeEventIn_S9 (μ : Measure DistC) [IsProbabilityMeasure μ]
    (hμ : IsNormalizedWholePlaneGFF (id : DistC → DistC) μ)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D)
    (C : Objects.CorrectedEvent.Constants) (T : Objects.CorrectedEvent.TubeData)
    (hS9 : tsupport (T.bump : ℂ → ℝ) ⊆ bigAnn C) :
    AEEventIn μ (fieldSigmaClosed0 id (bigAnn C)) {g | Objects.CorrectedEvent.S9 C T g} := by
  obtain ⟨ψ, hψK, hψ1⟩ := exists_bigAnn_test C
  refine aeEventIn_closed0_of_det μ hμ ξ Q D hD (bigAnn C) ψ hψK hψ1 _
    (Objects.ProbabilityS7S9.measurableSet_S9 C T) ?_ ?_
  · intro ε hε g₁ g₂ _ _ _ _ _ hres h1
    have hp : LQGMetric.pair0 g₁ (LQGMetric.cmTest0 T.bump) =
        LQGMetric.pair0 g₂ (LQGMetric.cmTest0 T.bump) :=
      pair0_eq_of_restrictTo_eq hres _
        (subset_nbhdO hε ((tsupport_cmTest_subset T.bump).trans hS9))
    change |LQGMetric.pair0 g₂ (LQGMetric.cmTest0 T.bump)| ≤ C.A_RN
    rw [← hp]
    exact h1
  · refine Filter.Eventually.of_forall fun g => ?_
    change |LQGMetric.pair0 (addConst g (-(g ψ))) (LQGMetric.cmTest0 T.bump)| ≤ C.A_RN ↔
      |LQGMetric.pair0 g (LQGMetric.cmTest0 T.bump)| ≤ C.A_RN
    rw [pair0_cmTest0_addConst]

end SupercriticalLQGUniqueness.Uniqueness.Objects.BlockMarginal
