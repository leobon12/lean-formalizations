import SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.OneScale.CanonicalLocal
import LQGMetric.Papers.DFGPS.L2_17Core2H
import LQGMetric.Field.GFFInvariance
import Mathlib.Probability.Distributions.Gaussian.Real




 


set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.OneScale

open LQGMetric (DistC IsWholePlaneGFF addConst)
open SupercriticalLQGUniqueness

def standardGaussian : Measure ℝ := gaussianReal 0 1

instance : IsProbabilityMeasure standardGaussian := inferInstanceAs
  (IsProbabilityMeasure (gaussianReal 0 1))

theorem gff_prod_fst {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h : Ω → DistC) (hh : IsWholePlaneGFF h P) :
    IsWholePlaneGFF (fun p : Ω × ℝ => h p.1) (P.prod ν) := by
  have hY : Measurable (fun p : Ω × ℝ => h p.1) := hh.measurable.comp measurable_fst
  have hlaw : (P.prod ν).map (fun p : Ω × ℝ => h p.1) = P.map h := by
    calc
      (P.prod ν).map (fun p : Ω × ℝ => h p.1) =
          ((P.prod ν).map Prod.fst).map h :=
        (Measure.map_map hh.measurable measurable_fst).symm
      _ = P.map h := by rw [Measure.map_fst_prod, measure_univ, one_smul]
  exact LQGMetric.DFGPS.L217.isWholePlaneGFF_of_map_eq hY hh hlaw

def gaussianShift {Ω : Type} (h : Ω → DistC) : Ω × ℝ → DistC :=
  fun p => addConst (h p.1) p.2

theorem gff_gaussianShift {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (hh : IsWholePlaneGFF h P) :
    IsWholePlaneGFF (gaussianShift h) (P.prod standardGaussian) := by
  exact (gff_prod_fst P standardGaussian h hh).addConst measurable_snd

 
theorem canonical_gaussianShift_isGFFPlusCont {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (hh : IsWholePlaneGFF h P) :
    LQGMetric.IsGFFPlusCont (id : DistC → DistC)
      ((P.prod standardGaussian).map (gaussianShift h)) := by
  exact LQGMetric.GM.Tight.isGFFPlusCont_of_wp
    (LQGMetric.GM.isWholePlaneGFF_id_map (gff_gaussianShift P h hh))

 
theorem barrier_of_scale (d e : LSCMetric) (c : ℝ≥0∞)
    (hc0 : c ≠ 0) (hcTop : c ≠ ∞)
    (hscale : ∀ n : ℕ, acrossDist e (BiLipschitz.Barrier.dyadicAnnulus n) =
      c * acrossDist d (BiLipschitz.Barrier.dyadicAnnulus n))
    (hd : BiLipschitz.Barrier.Barrier d) : BiLipschitz.Barrier.Barrier e := by
  intro n₀ M
  have hfin : c⁻¹ * (M : ℝ≥0∞) ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hc0) (ENNReal.natCast_ne_top M)
  obtain ⟨N, hN⟩ := ENNReal.exists_nat_gt hfin
  obtain ⟨n, hn₀, hn⟩ := hd n₀ N
  refine ⟨n, hn₀, ?_⟩
  rw [hscale n]
  have hlt : c * (c⁻¹ * (M : ℝ≥0∞)) <
      c * acrossDist d (BiLipschitz.Barrier.dyadicAnnulus n) :=
    ENNReal.mul_lt_mul_right hc0 hcTop (lt_trans hN hn)
  simpa only [ENNReal.mul_inv_cancel_left hc0 hcTop] using hlt

 
theorem canonical_gaussianShift_barrier {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : 0 < Q)
    (D : DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D) :
    ∀ᵐ g ∂(P.prod standardGaussian).map (gaussianShift h), BiLipschitz.Barrier.Barrier (D g) := by
  have hbase : ∀ᵐ ω ∂P, BiLipschitz.Barrier.Barrier (D (h ω)) := BiLipschitz.Barrier.ae_barrier hD hQ P h hh
  have hbaseSet : MeasurableSet {ω | BiLipschitz.Barrier.Barrier (D (h ω))} :=
    (BiLipschitz.Barrier.measurableSet_barrier hD.measurable).preimage hh.1.measurable
  have hfst : (P.prod standardGaussian).map Prod.fst = P := by
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  have hbaseProd : ∀ᵐ p ∂P.prod standardGaussian, BiLipschitz.Barrier.Barrier (D (h p.1)) := by
    have he := hbase
    rw [← hfst] at he
    exact (ae_map_iff measurable_fst.aemeasurable hbaseSet).1 he
  have hprod : LQGMetric.IsGFFPlusCont (fun p : Ω × ℝ => h p.1)
      (P.prod standardGaussian) :=
    LQGMetric.GM.Tight.isGFFPlusCont_of_wp
      (gff_prod_fst P standardGaussian h hh.1)
  have hweyl := Positivity.Witnesses.ae_annulus_addConst_eq_mul
    (P.prod standardGaussian) (fun p : Ω × ℝ => h p.1)
    hprod ξ Q D hD (fun p => p.2)
  have hshift : IsWholePlaneGFF (gaussianShift h) (P.prod standardGaussian) :=
    gff_gaussianShift P h hh.1
  have hbarProd : ∀ᵐ p ∂P.prod standardGaussian,
      BiLipschitz.Barrier.Barrier (D (gaussianShift h p)) := by
    filter_upwards [hbaseProd, hweyl] with p hp hw
    let c : ℝ≥0∞ := ENNReal.ofReal (Real.exp ((ξ : ℝ) * p.2))
    have hc0 : c ≠ 0 := (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
    have hcTop : c ≠ ∞ := ENNReal.ofReal_ne_top
    exact barrier_of_scale (D (h p.1)) (D (gaussianShift h p)) c hc0 hcTop
      (fun n => (hw (BiLipschitz.Barrier.dyadicAnnulus n)).1) hp
  have hbarSet : MeasurableSet {g : DistC | BiLipschitz.Barrier.Barrier (D g)} :=
    BiLipschitz.Barrier.measurableSet_barrier hD.measurable
  exact (ae_map_iff hshift.measurable.aemeasurable hbarSet).2 hbarProd

 
theorem ebl_canonical_local_event_of_e1a {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hAXPOS_Q_pos : 0 < Q)
    (D D' : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (hD' : IsWeakLQGMetric ξ Q D')
    (z : ℂ) (r : Ioi (0 : ℝ)) (A : ℝ)
    (hE1a_around : ∀ d e : LSCMetric,
      d.internal (collarOpen z r : Set ℂ) = e.internal (collarOpen z r : Set ℂ) →
      aroundDist d (separatorAt z r) = aroundDist e (separatorAt z r)) :
    ∃ S : Set (LQGMetric.DistOn (collarOpen z r)), MeasurableSet S ∧
      {p : Ω × ℝ | gaussianShift h p ∈ pairedRawEvent ξ Q D D' z r A} =ᵐ[P.prod standardGaussian]
      {p : Ω × ℝ | LQGMetric.restrictTo (collarOpen z r) (gaussianShift h p) ∈ S} := by
  let μH : Measure DistC := (P.prod standardGaussian).map (gaussianShift h)
  haveI : IsProbabilityMeasure μH :=
    (Measure.isProbabilityMeasure_map_iff
      (gff_gaussianShift P h hh.1).measurable.aemeasurable).2 inferInstance
  obtain ⟨S, hS, hAE⟩ := canonical_local_event_of_e1a ξ Q D D' hD hD'
    z r A μH (canonical_gaussianShift_isGFFPlusCont P h hh.1)
    (canonical_gaussianShift_barrier P h hh ξ Q hAXPOS_Q_pos D hD) hE1a_around
  refine ⟨S, hS, ?_⟩
  exact ae_of_ae_map (gff_gaussianShift P h hh.1).measurable.aemeasurable hAE


end SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.OneScale
