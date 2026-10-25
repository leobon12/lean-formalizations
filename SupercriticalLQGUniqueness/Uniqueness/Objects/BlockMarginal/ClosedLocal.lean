import SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS3.ModConstClosed




 












set_option autoImplicit false

noncomputable section

open Set MeasureTheory Metric
open LQGMetric.Blueprint
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BlockMarginal

open LQGMetric (DistC restrictTo addConst)

 

theorem aeEventIn_open_of_det
    (P : Measure DistC) [IsProbabilityMeasure P]
    (G : DistC → DistC) (hG : LQGMetric.IsGFFPlusCont G P)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D)
    (hBar : ∀ᵐ g ∂P, BiLipschitz.Barrier.Barrier (D (G g)))
    (U : TopologicalSpace.Opens ℂ) (B : Set DistC) (hBm : MeasurableSet B)
    (hdet : ∀ g₁ g₂ : DistC, BiLipschitz.Barrier.Barrier (D g₁) → BiLipschitz.Barrier.Barrier (D g₂) →
      (D g₁).IsLengthSpace → (D g₂).IsLengthSpace →
      (D g₁).internal (U : Set ℂ) = (D g₂).internal (U : Set ℂ) →
      restrictTo U g₁ = restrictTo U g₂ → g₁ ∈ B → g₂ ∈ B) :
    AEEventIn P (fieldSigma G U) {g | G g ∈ B} := by
  let B' : Set DistC := {g | G g ∈ B}
  obtain ⟨F, _, hLoc⟩ := hD.locality P G hG U
  have hLen := hD.length P G hG
  let Wraw : Set DistC := {g | BiLipschitz.Barrier.Barrier (D (G g)) ∧
    (D (G g)).IsLengthSpace ∧ (D (G g)).internal (U : Set ℂ) =
      F (restrictTo U (G g))}
  have hWraw : ∀ᵐ g ∂P, g ∈ Wraw := by
    filter_upwards [hBar, hLen, hLoc] with g hb hl hf
    exact ⟨hb, hl, hf⟩
  obtain ⟨W, hWae, hWm, hWsub⟩ := hWraw.exists_measurable_mem
  let R : DistC → (LQGMetric.CoordJ → ℝ) :=
    fun g => LQGMetric.pairJ U (restrictTo U (G g))
  have hRm : Measurable R :=
    (LQGMetric.measurable_pairJ U).comp
      ((LQGMetric.measurable_restrictTo U).comp hG.1)
  have hRfield : Measurable[fieldSigma G U] R :=
    (LQGMetric.measurable_pairJ U).comp (Measurable.of_comap_le le_rfl)
  have hSat : ∀ g₁ ∈ W, ∀ g₂ ∈ W, R g₁ = R g₂ → g₁ ∈ B' → g₂ ∈ B' := by
    intro g₁ hg₁ g₂ hg₂ hR h₁
    have hr : restrictTo U (G g₁) = restrictTo U (G g₂) :=
      LQGMetric.injective_pairJ U hR
    have hint : (D (G g₁)).internal (U : Set ℂ) =
        (D (G g₂)).internal (U : Set ℂ) := by
      calc
        _ = F (restrictTo U (G g₁)) := (hWsub g₁ hg₁).2.2
        _ = F (restrictTo U (G g₂)) := by rw [hr]
        _ = _ := ((hWsub g₂ hg₂).2.2).symm
    exact hdet (G g₁) (G g₂) (hWsub g₁ hg₁).1 (hWsub g₂ hg₂).1
      (hWsub g₁ hg₁).2.1 (hWsub g₂ hg₂).2.1 hint hr h₁
  have hBm' : NullMeasurableSet B' P := (hBm.preimage hG.1).nullMeasurableSet
  exact LQGMetric.LocalEvent.aeEventIn_of_saturated
    (Y := id) (R := R) (V := R) (B := B') (W := W)
    measurable_id hRm hRfield (Filter.Eventually.of_forall fun _ => rfl)
    hWm (by simpa only [Measure.map_id] using hBm') hWae hSat

 
theorem aeEventIn_closed0_of_det
    (μ : Measure DistC) [IsProbabilityMeasure μ]
    (hμ : IsNormalizedWholePlaneGFF (id : DistC → DistC) μ)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D)
    (K : Set ℂ) (ψ : LQGMetric.TestC) (hψK : tsupport (ψ : ℂ → ℝ) ⊆ K)
    (hψ1 : ∫ x, ψ x = 1)
    (B : Set DistC) (hBm : MeasurableSet B)
    (hdet : ∀ ε : ℝ, 0 < ε → ∀ g₁ g₂ : DistC, BiLipschitz.Barrier.Barrier (D g₁) → BiLipschitz.Barrier.Barrier (D g₂) →
      (D g₁).IsLengthSpace → (D g₂).IsLengthSpace →
      (D g₁).internal (thickening ε K) = (D g₂).internal (thickening ε K) →
      restrictTo (nbhdO ε K) g₁ = restrictTo (nbhdO ε K) g₂ → g₁ ∈ B → g₂ ∈ B)
    (hinv : ∀ᵐ g ∂μ, (addConst g (-(g ψ)) ∈ B ↔ g ∈ B)) :
    AEEventIn μ (fieldSigmaClosed0 id K) B := by
  have hwhole : LQGMetric.IsGFFPlusCont (id : DistC → DistC) μ :=
    LQGMetric.GM.Tight.isGFFPlusCont_of_wp hμ.1
  let G := LQGMetric.CONF.normIn (id : DistC → DistC) ψ
  have hG : LQGMetric.IsGFFPlusCont G μ := Toolkit.LocalEvents.isGFFPlusCont_normIn hwhole ψ
  have hQ : 0 < Q := Positivity.FromAxioms.axpos ξ Q D hD
  have hBar := BiLipschitz.Barrier.ae_barrier hD hQ μ id hμ
  have hscale := Positivity.Witnesses.ae_addConst_eq_mul μ id hwhole ξ Q D hD (fun g => -(g ψ))
  have hBG : ∀ᵐ g ∂μ, BiLipschitz.Barrier.Barrier (D (G g)) := by
    filter_upwards [hBar, hscale] with g hb hc
    let e : ℝ≥0∞ := ENNReal.ofReal (Real.exp ((ξ : ℝ) * -(g ψ)))
    exact Objects.ProbabilityS3.barrier_of_dist_scale (D g) (D (G g)) e
      (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
      ENNReal.ofReal_ne_top (fun x y => hc (x,y)) hb
  have hLocal (n : ℕ) : AEEventIn μ
      (fieldSigma G (nbhdO (1 / ((n : ℝ) + 1)) K)) {g | G g ∈ B} := by
    have hε : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    exact aeEventIn_open_of_det μ G hG ξ Q D hD hBG (nbhdO (1 / ((n : ℝ) + 1)) K) B hBm
      (fun g₁ g₂ hb₁ hb₂ hl₁ hl₂ hint hres hg =>
        hdet (1 / ((n : ℝ) + 1)) hε g₁ g₂ hb₁ hb₂ hl₁ hl₂ hint hres hg)
  have hLocal0 := Toolkit.LocalEvents.aeEventIn_fieldSigmaClosed0_of_normIn
    (id : DistC → DistC) ψ hψ1 K hψK hLocal
  obtain ⟨R, hRm, hGR⟩ := hLocal0
  refine ⟨R, hRm, ?_⟩
  filter_upwards [hinv, hGR] with g he hR
  exact propext (he.symm.trans (Iff.of_eq hR))

end SupercriticalLQGUniqueness.Uniqueness.Objects.BlockMarginal
