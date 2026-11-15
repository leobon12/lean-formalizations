/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.RetPlumbProofResidualSurvival

/-!
# Boundary survival in the actual retained physical filtration

Packet PROVE-RETPLUMB. A live killing record and the current capped histories
suffice for the boundary-inclusive survival test. No future lifetime is read.
-/

set_option autoImplicit false
noncomputable section
open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.Restart.RetAux79
open Supp7 Sec7.Lemma76F LocalSets
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {η₁ η₂ η₁' η₂' : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
  {u r : ℝ≥0} {F : Set Ω}

/-- An ambient measurable version of a coordinate agrees with the physical
reader on a measurable event, and is therefore observable on that event. -/
theorem measurable_indicator_retSigma76_of_reader {f g : Ω → ℂ}
    (hF : MeasurableSet[retSigma76 P η₁ η₂ ζ₁ ζ₂ u r] F)
    (hf : Measurable f) (hg : Measurable[retSigma76 P η₁ η₂ ζ₁ ζ₂ u r] g)
    (he : ∀ᵐ ω ∂P, ω ∈ F → f ω = g ω) :
    Measurable[retSigma76 P η₁ η₂ ζ₁ ζ₂ u r] (F.indicator f) := by
  classical
  apply measurable_retSigma76_congr
    (hf.indicator (retSigma76_le P η₁ η₂ ζ₁ ζ₂ u r _ hF)) (hg.indicator hF)
  filter_upwards [he] with ω he
  by_cases hω : ω ∈ F <;> simp only [indicator_apply, hω, ↓reduceIte]
  exact he hω

/-- The physical boundary survival event is measurable in the actual current
killed histories. Continuous capped versions are the landed history readers. -/
theorem measurableSet_retLifeP_retPhysFiltration
    {G : ℝ≥0 → Set Ω} {x₁ x₂ : ℝ}
    (hd : (retFam G η₁' η₂' u r).IsMeasGood)
    (hF : MeasurableSet[retSigma76 P η₁ η₂ ζ₁ ζ₂ u r] F) (hG : F ⊆ G r)
    (hζ₂ : Measurable ζ₂)
    (ha₁ : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → η₁' ω s = η₁ ω s)
    (ha₂ : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₂ ω → η₂' ω s = η₂ ω s)
    (hp₁ : ∀ ω ∈ F, IsPathGood (η₁' ω) (ζ₁ ω) x₁)
    (hp₂ : ∀ ω ∈ F, IsPathGood (η₂' ω) (ζ₂ ω) x₂)
    (hpair : ∀ ω ∈ F,
      Sec7.Lemma76Exit.IsDisjointPair (η₁' ω) (ζ₁ ω) u (η₂' ω) (ζ₂ ω) r)
    (ηc₁ ηc₂ : ℝ≥0 → Ω → ℝ≥0 → ℂ)
    (hc₁ : ∀ t ω, Continuous (ηc₁ t ω)) (hc₂ : ∀ t ω, Continuous (ηc₂ t ω))
    (hm₁ : ∀ t s, Measurable fun ω => ηc₁ t ω s)
    (hm₂ : ∀ t s, Measurable fun ω => ηc₂ t ω s)
    (hag₁ : ∀ t, ∀ᵐ ω ∂P, ∀ s, ηc₁ t ω s =
      η₁ ω (capTime (capR u (r + t)) (ζ₁ ω) s))
    (hag₂ : ∀ t, ∀ᵐ ω ∂P, ∀ s, ηc₂ t ω s =
      η₂ ω (capTime (capR u (r + t)) (ζ₂ ω) s)) :
    ∀ t : ℝ≥0, MeasurableSet[retPhysFiltration P η₁ η₂ ζ₁ ζ₂ u r t]
      (F ∩ {ω | (t : ℝ≥0∞) < retLifeP η₁' η₂' ζ₂ u r ω}) := by
  intro t
  change MeasurableSet[retSigma76 P η₁ η₂ ζ₁ ζ₂ u (r + t)] _
  have hFt : MeasurableSet[retSigma76 P η₁ η₂ ζ₁ ζ₂ u (r + t)] F :=
    retSigma76_mono P η₁ η₂ ζ₁ ζ₂ le_rfl le_self_add _ hF
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with ht | ht
  · subst t
    have he : F ∩ {ω | ((0 : ℝ≥0) : ℝ≥0∞) < retLifeP η₁' η₂' ζ₂ u r ω} = F := by
      ext ω
      exact ⟨fun h => h.1, fun h => ⟨h,
        (retLife_pos_of_good_pair hd (hG h) (hp₂ ω h) (hpair ω h)).1⟩⟩
    rw [he]
    exact hFt
  have hrt : r < r + t := lt_add_of_pos_right r ht
  have hrec := measurable_lifeRec_retSigma76_right P η₁ η₂ ζ₁ ζ₂ hζ₂ u (r + t)
  have hA : MeasurableSet[retSigma76 P η₁ η₂ ζ₁ ζ₂ u (r + t)]
      (F ∩ {ω | ((r + t : ℝ≥0) : ℝ≥0∞) < ζ₂ ω}) := by
    have he : {ω | ((r + t : ℝ≥0) : ℝ≥0∞) < ζ₂ ω} =
        {ω | lifeRec (ζ₂ ω) (r + t) = ⊤} := by
      ext ω
      exact (lifeRec_eq_top_iff_of_ne_top ENNReal.coe_ne_top).symm
    rw [he]
    exact hFt.inter (hrec (measurableSet_singleton ⊤))
  have hread₁ : ∀ s ≤ u, Measurable[retSigma76 P η₁ η₂ ζ₁ ζ₂ u (r + t)]
      ((F ∩ {ω | ((r + t : ℝ≥0) : ℝ≥0∞) < ζ₂ ω}).indicator fun ω => η₁' ω s) := by
    intro s hs
    apply measurable_indicator_retSigma76_of_reader hA (hd.meas₁ s)
      (measurable_capped_left_retSigma76 (hc₁ t) (hm₁ t) (hag₁ t) hs)
    filter_upwards [ha₁, hag₁ t] with ω he hc hω
    rw [hc s, capTime_eq_of_lt (hpair ω hω.1).1 (lt_capR_left u (r + t)) hs]
    exact he s ((ENNReal.coe_le_coe.2 hs).trans (hpair ω hω.1).1.le)
  have hread₂ : ∀ s ≤ r + t, Measurable[retSigma76 P η₁ η₂ ζ₁ ζ₂ u (r + t)]
      ((F ∩ {ω | ((r + t : ℝ≥0) : ℝ≥0∞) < ζ₂ ω}).indicator fun ω => η₂' ω s) := by
    intro s hs
    apply measurable_indicator_retSigma76_of_reader hA (hd.meas₂ s)
      (measurable_capped_right_retSigma76 (hc₂ t) (hm₂ t) (hag₂ t) hs)
    filter_upwards [ha₂, hag₂ t] with ω he hc hω
    rw [hc s, capTime_eq_of_lt hω.2 (lt_capR_right u (r + t)) hs]
    exact he s ((ENNReal.coe_le_coe.2 hs).trans hω.2.le)
  have hm := @measurableSet_lt_contStop_of_prefix Ω
    (retSigma76 P η₁ η₂ ζ₁ ζ₂ u (r + t)) F η₂' η₁' η₂' ζ₂
    r (r + t) u r hrt hA hread₂ hread₁
    (fun s hs => hread₂ s (hs.trans le_self_add))
    (fun ω hω hζ => (hp₂ ω hω).continuousOn.mono fun s hs =>
      (ENNReal.coe_le_coe.2 hs).trans hζ.le)
    (fun ω hω hζ => isPathGood_continuousAt (hp₂ ω hω) hζ)
    (fun ω hω => (hp₁ ω hω).continuousOn.mono fun s hs =>
      (ENNReal.coe_le_coe.2 hs).trans (hpair ω hω).1.le)
    (fun ω hω => (hp₂ ω hω).continuousOn.mono fun s hs =>
      (ENNReal.coe_le_coe.2 hs).trans (hpair ω hω).2.1.le)
  have he : F ∩ {ω | (t : ℝ≥0∞) < retLifeP η₁' η₂' ζ₂ u r ω} =
      F ∩ {ω | ((r + t : ℝ≥0) : ℝ≥0∞) <
        contStop (η₂' ω) (ζ₂ ω) r (η₁' ω '' Icc 0 u ∪ η₂' ω '' Icc 0 r ∪ realLine)} := by
    ext ω
    exact and_congr_right fun _ => coe_add_lt_iff
  rw [he]
  exact hm

end InteractingSLE.Restart.RetAux79
