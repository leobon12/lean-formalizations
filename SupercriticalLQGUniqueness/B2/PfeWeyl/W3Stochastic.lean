import SupercriticalLQGUniqueness.B2.PfeWeyl.W3Sample
import SupercriticalLQGUniqueness.B2.PfeWeyl.InputsW3
import SupercriticalLQGUniqueness.B2.PfeAxioms.LocalObservableFiniteLimit
import SupercriticalLQGUniqueness.B2.PfeAxioms.BoundedFiniteWeyl
import SupercriticalLQGUniqueness.B2.PfeAxioms.BoundedShiftField
import SupercriticalLQGUniqueness.B2.LscTop.Metrizable

 





















set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal
open LQGMetric (DistC addFun IsGFFPlusBddCont)
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.PfeWeyl

 


theorem ae_acrossUnbounded_of_acrossTail {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Dω : Ω → LSCMetric)
    (hgeo : ∀ k : ℕ, AcrossTailInput P Dω ((k : ℝ) + 1) (Nat.cast_add_one_pos k)) :
    ∀ᵐ ω ∂P, AcrossUnbounded (Dω ω) := by
  have hkm : ∀ k m : ℕ, ∀ᵐ ω ∂P, ∃ R : Set.Ioi (2 * ((k : ℝ) + 1)),
      (m : ℝ≥0∞) < acrossDist (Dω ω) (outerAnnulus ((k : ℝ) + 1)
        (Nat.cast_add_one_pos k) R) := by
    intro k m
    rw [ae_iff]
    refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun η hη _ => ?_) bot_le
    have hev := hgeo k (m : ℝ≥0∞) (ENNReal.natCast_ne_top m) (η : ℝ≥0∞)
      (by exact_mod_cast hη)
    obtain ⟨R, hR⟩ := hev.exists
    refine (measure_mono ?_).trans (hR.trans (by simp))
    intro ω hω
    exact not_lt.1 fun hlt => hω ⟨R, hlt⟩
  have hall : ∀ᵐ ω ∂P, ∀ k m : ℕ, ∃ R : Set.Ioi (2 * ((k : ℝ) + 1)),
      (m : ℝ≥0∞) < acrossDist (Dω ω) (outerAnnulus ((k : ℝ) + 1)
        (Nat.cast_add_one_pos k) R) :=
    ae_all_iff.2 fun k => ae_all_iff.2 fun m => hkm k m
  filter_upwards [hall] with ω hω k T hT
  obtain ⟨m, hm⟩ := ENNReal.exists_nat_gt hT
  obtain ⟨R, hR⟩ := hω k m
  exact ⟨R, hm.trans hR⟩

 


theorem ae_weyl_scaling_all_bounded_of_tendsto
    (ξ : Set.Ioi (0 : ℝ)) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (ε : ℕ → Set.Ioi (0 : ℝ)) (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (Dω : Ω → LSCMetric) (X : Set.Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hconv : ∀ᵐ ω ∂P, Tendsto (fun n =>
      normalizedLFPPMetric (ξ : ℝ) (m (ε n)) (X (ε n) ω)) atTop (𝓝 (Dω ω)))
    (hlen : ∀ᵐ ω ∂P, (Dω ω).IsLengthSpace)
    (hctrl : ∀ᵐ ω ∂P, ∀ u : ℂ, ∀ δ : ℝ, 0 < δ → ∃ η : ℝ, 0 < η ∧
      ∀ v : ℂ, (Dω ω).1 (u, v) < ENNReal.ofReal η → dist u v < δ)
    (hgeo : ∀ k : ℕ, AcrossTailInput P Dω ((k : ℝ) + 1) (Nat.cast_add_one_pos k))
    (hsmall : ∀ k : ℕ, ∀ᵐ ω ∂P,
      SmallAnnulusCosts (fun n => normalizedLFPPMetric (ξ : ℝ) (m (ε n)) (X (ε n) ω))
        (Dω ω) (Metric.closedBall 0 k) (Metric.ball 0 ((k : ℝ) + 1))) :
    ∀ᵐ ω ∂P, ∀ (f : C(ℂ, ℝ)) (M : ℝ) (hM : ∀ z, |f z| ≤ M),
      ∃ E : LSCMetric, (∀ p, E p = weylScale (ξ : ℝ) f (Dω ω) p) ∧
        Tendsto (fun n => normalizedLFPPMetric (ξ : ℝ) (m (ε n))
          (X (ε n) ω + LQGMetric.LFPP.mollCont (ε n : ℝ) (ε n).property.ne' f M hM))
          atTop (𝓝 E) := by
  filter_upwards [hconv, hlen, hctrl, ae_acrossUnbounded_of_acrossTail P _ hgeo,
    ae_all_iff.2 hsmall] with ω hG hL hC hA hS f M hM
  exact weyl_scaling_sample (ξ : ℝ) (le_of_lt ξ.property) (fun n => m (ε n))
    (fun n => X (ε n) ω) (Dω ω) hG hL
    (B2.PfeLocal.continuous_euclidForget_of_small_metric _ hC) hA hS
    (fun n => (ε n : ℝ)) (fun n => (ε n).property.ne') hε f M hM

 

theorem ae_weyl_scaling_all_bounded
    (ξ : Set.Ioi (0 : ℝ)) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (ε : ℕ → Set.Ioi (0 : ℝ)) (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (D : DistC → LSCMetric) (hD : SubseqLimit ξ m ε D)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P)
    (X : Set.Ioi (0 : ℝ) → Ω → C(ℂ, ℝ)) (hX : ∀ δ, IsHeatSmoothing P h δ (X δ))
    (hlen : ∀ᵐ ω ∂P, (D (h ω)).IsLengthSpace)
    (hctrl : ∀ᵐ ω ∂P, ∀ u : ℂ, ∀ δ : ℝ, 0 < δ → ∃ η : ℝ, 0 < η ∧
      ∀ v : ℂ, (D (h ω)).1 (u, v) < ENNReal.ofReal η → dist u v < δ)
    (hgeo : ∀ k : ℕ, AcrossTailInput P (fun ω => D (h ω)) ((k : ℝ) + 1)
      (Nat.cast_add_one_pos k))
    (hsmall : ∀ k : ℕ, ∀ᵐ ω ∂P,
      SmallAnnulusCosts (fun n => normalizedLFPPMetric (ξ : ℝ) (m (ε n)) (X (ε n) ω))
        (D (h ω)) (Metric.closedBall 0 k) (Metric.ball 0 ((k : ℝ) + 1))) :
    ∀ᵐ ω ∂P, ∀ (f : C(ℂ, ℝ)) (M : ℝ) (hM : ∀ z, |f z| ≤ M),
      ∃ E : LSCMetric, (∀ p, E p = weylScale (ξ : ℝ) f (D (h ω)) p) ∧
        Tendsto (fun n => normalizedLFPPMetric (ξ : ℝ) (m (ε n))
          (X (ε n) ω + LQGMetric.LFPP.mollCont (ε n : ℝ) (ε n).property.ne' f M hM))
          atTop (𝓝 E) :=
  ae_weyl_scaling_all_bounded_of_tendsto ξ m ε hε P (fun ω => D (h ω)) X
    (PfeAxioms.ae_normalizedLFPPMetric_tendsto ξ m ε D hD P h hh X hX)
    hlen hctrl hgeo hsmall

 
theorem lscMetric_tendsto_unique {G : ℕ → LSCMetric} {E₁ E₂ : LSCMetric}
    (h₁ : Tendsto G atTop (𝓝 E₁)) (h₂ : Tendsto G atTop (𝓝 E₂)) : E₁ = E₂ :=
  tendsto_nhds_unique h₁ h₂

 

theorem ae_weylScale_eq_of_bounded_shift
    (ξ : Set.Ioi (0 : ℝ)) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (ε : ℕ → Set.Ioi (0 : ℝ)) (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (D : DistC → LSCMetric) (hD : SubseqLimit ξ m ε D)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P)
    (X : Set.Ioi (0 : ℝ) → Ω → C(ℂ, ℝ)) (hX : ∀ δ, IsHeatSmoothing P h δ (X δ))
    (hlen : ∀ᵐ ω ∂P, (D (h ω)).IsLengthSpace)
    (hctrl : ∀ᵐ ω ∂P, ∀ u : ℂ, ∀ δ : ℝ, 0 < δ → ∃ η : ℝ, 0 < η ∧
      ∀ v : ℂ, (D (h ω)).1 (u, v) < ENNReal.ofReal η → dist u v < δ)
    (hgeo : ∀ k : ℕ, AcrossTailInput P (fun ω => D (h ω)) ((k : ℝ) + 1)
      (Nat.cast_add_one_pos k))
    (hsmall : ∀ k : ℕ, ∀ᵐ ω ∂P,
      SmallAnnulusCosts (fun n => normalizedLFPPMetric (ξ : ℝ) (m (ε n)) (X (ε n) ω))
        (D (h ω)) (Metric.closedBall 0 k) (Metric.ball 0 ((k : ℝ) + 1)))
    (F : Ω → C(ℂ, ℝ)) (hF : Measurable F) (M : ℝ) (hFM : ∀ ω z, |F ω z| ≤ M) :
    ∀ᵐ ω ∂P, weylScale (ξ : ℝ) (F ω) (D (h ω)) = (D (addFun (h ω) (F ω))).1 := by
  have hb : IsGFFPlusBddCont (fun ω => addFun (h ω) (F ω)) P :=
    PfeAxioms.isGFFPlusBddCont_addFun_of_normalized P h hh F hF
      (fun ω => ⟨M, hFM ω⟩)
  have hYex : ∀ δ : Set.Ioi (0 : ℝ), ∃ Y : Ω → C(ℂ, ℝ),
      IsHeatSmoothing P (fun ω => addFun (h ω) (F ω)) δ Y :=
    fun δ => (PfeAxioms.exists_heatVersion_bdd hb δ).imp fun _ hY => hY.2
  choose Y hY using hYex
  have hshift := PfeAxioms.ae_bounded_shift_finiteLFPP_weyl (ξ : ℝ) m ε P h hh F M hFM hb
    X Y hX hY
  have hlimY := (hD P (fun ω => addFun (h ω) (F ω)) hb Y hY).1
  filter_upwards [ae_weyl_scaling_all_bounded ξ m ε hε D hD P h hh X hX hlen hctrl hgeo
    hsmall, hshift, hlimY] with ω hbase hω hY'
  obtain ⟨E, hE, hconv⟩ := hbase (F ω) M (hFM ω)
  have heqseq : (fun n => normalizedLFPPMetric (ξ : ℝ) (m (ε n))
      (X (ε n) ω + LQGMetric.LFPP.mollCont (ε n : ℝ) (ε n).property.ne' (F ω) M (hFM ω))) =
      fun n => normalizedLFPPMetric (ξ : ℝ) (m (ε n)) (Y (ε n) ω) := by
    funext n
    refine LSCMetric.ext fun p => ?_
    rw [normalizedLFPPMetric_add_eq_weylScale, hω n p]
  rw [heqseq] at hconv
  have hconvD : Tendsto (fun n => normalizedLFPPMetric (ξ : ℝ) (m (ε n)) (Y (ε n) ω))
      atTop (𝓝 (D (addFun (h ω) (F ω)))) := by
    rw [LSCMetric.isInducing_toLSCFun.tendsto_nhds_iff]
    apply LSCFun.tendsto_of_lscTendsto
    convert hY' using 1
    funext n
    funext p
    exact normalizedLFPPMetric_toLSCFun (ξ : ℝ) (m (ε n)) (Y (ε n) ω) p
  have hED := lscMetric_tendsto_unique hconv hconvD
  funext p
  rw [← hE p, hED]

 


theorem ae_weylScale_eq_of_measurable_shift
    (ξ : Set.Ioi (0 : ℝ)) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (ε : ℕ → Set.Ioi (0 : ℝ)) (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (D : DistC → LSCMetric) (hD : SubseqLimit ξ m ε D)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P)
    (X : Set.Ioi (0 : ℝ) → Ω → C(ℂ, ℝ)) (hX : ∀ δ, IsHeatSmoothing P h δ (X δ))
    (hlen : ∀ᵐ ω ∂P, (D (h ω)).IsLengthSpace)
    (hctrl : ∀ᵐ ω ∂P, ∀ u : ℂ, ∀ δ : ℝ, 0 < δ → ∃ η : ℝ, 0 < η ∧
      ∀ v : ℂ, (D (h ω)).1 (u, v) < ENNReal.ofReal η → dist u v < δ)
    (hgeo : ∀ k : ℕ, AcrossTailInput P (fun ω => D (h ω)) ((k : ℝ) + 1)
      (Nat.cast_add_one_pos k))
    (hsmall : ∀ k : ℕ, ∀ᵐ ω ∂P,
      SmallAnnulusCosts (fun n => normalizedLFPPMetric (ξ : ℝ) (m (ε n)) (X (ε n) ω))
        (D (h ω)) (Metric.closedBall 0 k) (Metric.ball 0 ((k : ℝ) + 1)))
    (F : Ω → C(ℂ, ℝ)) (hF : Measurable F) (hFb : ∀ ω, ∃ M : ℝ, ∀ z, |F ω z| ≤ M) :
    ∀ᵐ ω ∂P, weylScale (ξ : ℝ) (F ω) (D (h ω)) = (D (addFun (h ω) (F ω))).1 := by
  classical
  
  let S : ℕ → Set Ω := fun k => {ω | ∀ z, |F ω z| ≤ k}
  have hSmeas : ∀ k, MeasurableSet (S k) := by
    intro k
    have hset : S k = F ⁻¹' {g : C(ℂ, ℝ) | ∀ z, |g z| ≤ k} := rfl
    rw [hset]
    refine hF ?_
    have hcl : IsClosed {g : C(ℂ, ℝ) | ∀ z, |g z| ≤ k} := by
      have hset' : {g : C(ℂ, ℝ) | ∀ z, |g z| ≤ k} = ⋂ z, {g : C(ℂ, ℝ) | |g z| ≤ k} := by
        ext g
        simp
      rw [hset']
      exact isClosed_iInter fun z =>
        isClosed_le ((continuous_eval_const z).abs) continuous_const
    exact hcl.measurableSet
  let Fk : ℕ → Ω → C(ℂ, ℝ) := fun k ω => if ω ∈ S k then F ω else 0
  have hFk : ∀ k, Measurable (Fk k) := fun k =>
    Measurable.ite (hSmeas k) hF measurable_const
  have hFkM : ∀ k ω z, |Fk k ω z| ≤ k := by
    intro k ω z
    by_cases hω : ω ∈ S k
    · simp only [Fk, hω, ite_true]
      exact hω z
    · simp [Fk, hω]
  have hk : ∀ k : ℕ, ∀ᵐ ω ∂P, weylScale (ξ : ℝ) (Fk k ω) (D (h ω)) =
      (D (addFun (h ω) (Fk k ω))).1 := fun k =>
    ae_weylScale_eq_of_bounded_shift ξ m ε hε D hD P h hh X hX hlen hctrl hgeo hsmall
      (Fk k) (hFk k) k (hFkM k)
  filter_upwards [ae_all_iff.2 hk] with ω hω
  obtain ⟨M, hM⟩ := hFb ω
  obtain ⟨k, hkM⟩ := exists_nat_ge M
  have hmem : ω ∈ S k := fun z => (hM z).trans hkM
  have hFkω : Fk k ω = F ω := by simp [Fk, hmem]
  have := hω k
  rwa [hFkω] at this

end SupercriticalLQGUniqueness.B2.PfeWeyl
