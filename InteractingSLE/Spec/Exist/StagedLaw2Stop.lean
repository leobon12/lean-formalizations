/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Exist.StagedLaw2Main
import InteractingSLE.Spec.Sec2.CriticalLifetime

/-!
# The single-stage law: the record of a finite stop is good

Packet PROVE-STAGEDLAW2. The named input `StopLawStatement` has two conjuncts. The first one — almost surely, a finite
stop `min t ζ` of a flow-line piece has a good record (its stopped driver is continuous on `[0, stop]`) — is proved here
(`ae_isDrvGood_of_isFlowLineDriver`): before the lifetime the driver is continuous, a zero lifetime gives a constant
record, and at a finite positive lifetime the driver has a left limit almost surely
(`IsIntegratedSLEEvolution.ae_tendsto_threshold`), which a regular driver takes as its value.
`StopLawStatement` therefore reduces to its conditional-law conjunct (`StopCondLawStatement`,
`stopLawStatement_of_stopCondLaw`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Exist

namespace StagedLaw

open LQGMetric Restart Staged

section Det

variable {t : ℝ≥0∞} {e : (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- A record whose stopped driver is continuous up to the finite stop is good. -/
theorem isDrvGood_of_continuousOn_retOf (he : IsRegularDriver e) (hfin : min t e.2 ≠ ⊤)
    (hc : ContinuousOn (retOf t e).1 (Icc 0 (min t e.2).toNNReal)) : LocalExt.IsDrvGood (recHist (recOf t e)) := by
  refine LocalExt.isDrvGood_of_continuousOn hc (fun q => ?_) ?_
  · rw [readRec_sample, retOf_eq_min hfin]
  · change e.1 (min ((0 : ℝ≥0) : ℝ≥0∞) (min t e.2)).toNNReal = 0
    rw [ENNReal.coe_zero, min_eq_left (zero_le (a := min _ _)), ENNReal.toNNReal_zero]
    exact he.2.1

/-- **A finite stop with a left limit of the driver at a positive lifetime has a good record.** -/
theorem isDrvGood_recOf_of_leftLim (he : IsRegularDriver e) (hfin : min t e.2 ≠ ⊤)
    (hlim : ∀ T : ℝ≥0, 0 < T → (T : ℝ≥0∞) = e.2 → ∃ w₀ : ℝ, Tendsto e.1 (𝓝[<] T) (𝓝 w₀)) :
    LocalExt.IsDrvGood (recHist (recOf t e)) := by
  refine isDrvGood_of_continuousOn_retOf he hfin ?_
  set Tn := (min t e.2).toNNReal with hTn
  have hTs : (Tn : ℝ≥0∞) = min t e.2 := ENNReal.coe_toNNReal hfin
  -- before the stop the stopped driver is the driver
  have heq : ∀ x : ℝ≥0, x < Tn → (retOf t e).1 x = e.1 x := fun x hx => by
    change e.1 (min (x : ℝ≥0∞) (min t e.2)).toNNReal = e.1 x
    rw [min_eq_left (by rw [← hTs]; exact_mod_cast hx.le), ENNReal.toNNReal_coe]
  have hlt : ∀ x : ℝ≥0, x < Tn → (x : ℝ≥0∞) < e.2 := fun x hx =>
    lt_of_lt_of_le (by rw [← hTs]; exact_mod_cast hx) (min_le_right _ _)
  have hcont : ∀ x : ℝ≥0, x < Tn → ContinuousAt e.1 x := fun x hx =>
    he.1.continuousAt ((isOpen_lt ENNReal.continuous_coe continuous_const).mem_nhds (hlt x hx))
  intro x hx
  rcases hx.2.lt_or_eq with hxT | hxT
  · -- strictly before the stop
    have hev : (retOf t e).1 =ᶠ[𝓝 x] e.1 := by
      filter_upwards [gt_mem_nhds hxT] with y hy using heq y hy
    exact ((hcont x hxT).congr hev.symm).continuousWithinAt
  · -- at the stop: continuity from the left
    subst hxT
    rcases eq_or_ne Tn 0 with h0 | h0
    · have : Icc (0 : ℝ≥0) Tn = {0} := by rw [h0, Icc_self]
      rw [this, h0]; exact continuousWithinAt_singleton
    have hpos : 0 < Tn := pos_iff_ne_zero.2 h0
    -- the left limit of the driver at the stop is its value there
    have hleft : Tendsto e.1 (𝓝[<] Tn) (𝓝 ((retOf t e).1 Tn)) := by
      by_cases hst : t < e.2
      · have hT : (Tn : ℝ≥0∞) < e.2 := by rw [hTs, min_eq_left hst.le]; exact hst
        have hc : ContinuousAt e.1 Tn :=
          he.1.continuousAt ((isOpen_lt ENNReal.continuous_coe continuous_const).mem_nhds hT)
        have hv : (retOf t e).1 Tn = e.1 Tn := by
          change e.1 (min (Tn : ℝ≥0∞) (min t e.2)).toNNReal = e.1 Tn
          rw [hTs, min_self, ← hTn]
        rw [hv]; exact hc.tendsto.mono_left nhdsWithin_le_nhds
      · have hζ : (Tn : ℝ≥0∞) = e.2 := by rw [hTs, min_eq_right (not_lt.1 hst)]
        obtain ⟨w₀, hw₀⟩ := hlim Tn hpos hζ
        have hne : e.2 ≠ ⊤ := by rw [← hζ]; exact ENNReal.coe_ne_top
        have he2 : e.2.toNNReal = Tn := by rw [← hζ, ENNReal.toNNReal_coe]
        have hval := he.2.2.2 hne (by rw [← hζ]; exact_mod_cast hpos) w₀ (by rw [he2]; exact hw₀)
        have hv : (retOf t e).1 Tn = w₀ := by
          change e.1 (min (Tn : ℝ≥0∞) (min t e.2)).toNNReal = w₀
          rw [hTs, min_self, ← hTn, ← he2]; exact hval
        rw [hv]; exact hw₀
    have hw : ContinuousWithinAt (retOf t e).1 (Iio Tn) Tn := by
      have hev : (retOf t e).1 =ᶠ[𝓝[<] Tn] e.1 := by
        filter_upwards [self_mem_nhdsWithin] with y hy using heq y hy
      exact (hleft.congr' hev.symm)
    exact (continuousWithinAt_Iio_iff_Iic.1 hw).mono fun y hy => hy.2

end Det

/-- **The first conjunct of `StopLawStatement`**: almost surely a finite stop of a flow-line piece has a good
record. -/
theorem ae_isDrvGood_of_isFlowLineDriver {κ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ} {J : Finset ℝ} {θ : ℝ} (t : ℝ≥0∞)
    {Ω : Type u} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q] {g : Ω → DistOn upperHalfPlaneOpens}
    {E : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hreg : ∀ ω, IsRegularDriver (E ω))
    (hfl : IsFlowLineDriver κ b J θ Q g (fun s ω => (E ω).1 s) (fun ω => (E ω).2)) :
    ∀ᵐ ω ∂Q, min t (E ω).2 ≠ ⊤ → LocalExt.IsDrvGood (recHist (recOf t (E ω))) := by
  obtain ⟨h', 𝓕, VL, VR, B, -, hC⟩ := hfl
  filter_upwards [hC.1.ae_tendsto_threshold hκ] with ω hω hfin
  refine isDrvGood_recOf_of_leftLim (hreg ω) hfin fun T hT hζ => ?_
  obtain ⟨w₀, vL₀, vR₀, hlim, -⟩ := hω T hT hζ
  exact ⟨w₀, (continuous_fst.tendsto _).comp hlim⟩

/-- The conditional-law conjunct of `StopLawStatement` (with the record of a finite stop good). -/
def StopCondLawStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 →
    ∃ β : BoundaryWord × ℝ × RecData → BoundaryWord, Measurable β ∧ (∀ x, (β x).IsSorted) ∧
      ∀ (c : BoundaryWord) (θ : ℝ) (t : ℝ≥0∞) {Ω : Type u} [MeasurableSpace Ω]
        [StandardBorelSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q] (g : Ω → DistOn upperHalfPlaneOpens)
        (E : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞), Measurable E → (∀ ω, IsRegularDriver (E ω)) →
        IsFlowLineDriver κ c.fn c.jumps θ Q g (fun s ω => (E ω).1 s) (fun ω => (E ω).2) →
        ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂Q, min t (E ω).2 ≠ ⊤ →
          Q[fun ω' => Complex.exp (Complex.I * (recField κ (recOf t (E ω')) (g ω') φ : ℂ)) |
              MeasurableSpace.comap (fun ω' => recOf t (E ω')) inferInstance] ω =
            gaussCF (β (c, θ, recOf t (E ω))) φ

/-- **`StopLawStatement` reduces to its conditional-law conjunct.** -/
theorem stopLawStatement_of_stopCondLaw (h : StopCondLawStatement.{u}) : StopLawStatement.{u} := by
  intro κ hκ hκ4
  obtain ⟨β, hβm, hβs, hβ⟩ := h κ hκ hκ4
  refine ⟨β, hβm, hβs, fun c θ t Ω _ _ Q _ g E hE hreg hfl => ⟨?_, hβ c θ t Q g E hE hreg hfl⟩⟩
  exact ae_isDrvGood_of_isFlowLineDriver hκ t hreg hfl

/-- **The staged conditional law from the conditional-law conjunct of the single-stage law.** -/
theorem stagedCondLawStatement_of_stopCondLaw (h : StopCondLawStatement.{u}) : StagedCondLawStatement.{u} :=
  stagedCondLawStatement_of_stopLaw (stopLawStatement_of_stopCondLaw h)

end StagedLaw

end Exist

end InteractingSLE
