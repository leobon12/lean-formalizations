import SupercriticalLQGUniqueness.Uniqueness.TwoScale.Ratio.RatioCentered




 
set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.TwoScale.Ratio

open LQGMetric (DistC addConst circleAvg)
open LQGMetric.Blueprint

theorem collarOpen_zero_eq_annulus (r : Ioi (0 : ℝ)) :
    BiLipschitz.OneScale.collarOpen 0 r =
      annulus 0 ((r : ℝ) / 2) (4 * (r : ℝ)) := by
  apply SetLike.ext
  intro w
  change w ∈ Metric.ball 0 (4 * (r : ℝ)) \
      closure (Metric.ball 0 ((r : ℝ) / 2)) ↔
    ((r : ℝ) / 2 < ‖w - 0‖ ∧ ‖w - 0‖ < 4 * (r : ℝ))
  rw [closure_ball 0 ((div_pos r.2 (by norm_num)).ne')]
  simp only [Set.mem_sdiff, Metric.mem_ball, Metric.mem_closedBall, not_le,
    dist_eq_norm]
  tauto

theorem origin_ratio_local_version
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ)
    (D : DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D)
    (r : Ioi (0 : ℝ)) (c : ℝ≥0∞) :
    let R : ℝ := 5 * (r : ℝ)
    ∃ E : Set Ω,
      MeasurableSet[fieldSigma
        (fun ω => addConst (h ω) (-circleAvg (h ω) R 0))
        (annulus 0 ((1 / 10) * R) ((4 / 5) * R))] E ∧
      E =ᵐ[P] {ω | h ω ∈ rawRatioEvent D 0 r c} := by
  dsimp only
  have hr : 0 < (r : ℝ) := r.2
  let R : Ioi (0 : ℝ) := ⟨5 * (r : ℝ), mul_pos (by norm_num) hr⟩
  obtain ⟨S, hS, hE, heq⟩ := centered_ratio_local P h hh ξ Q D hD 0 r c R
  let E : Set Ω := {ω | BiLipschitz.OneScale.gaussianSmooth (BiLipschitz.OneScale.collarOpen 0 r) S
      (LQGMetric.restrictTo (BiLipschitz.OneScale.collarOpen 0 r)
        (addConst (h ω) (-circleAvg (h ω) R 0))) > 1 / 2}
  refine ⟨E, ?_, heq⟩
  have hcollar := collarOpen_zero_eq_annulus r
  have hrad₁ : ((1 / 10) : ℝ) * (R : ℝ) = (r : ℝ) / 2 := by
    dsimp [R]
    ring
  have hrad₂ : ((4 / 5) : ℝ) * (R : ℝ) = 4 * (r : ℝ) := by
    dsimp [R]
    ring
  rw [hrad₁, hrad₂, ← hcollar]
  exact hE

theorem rawRatio_marginal_uniform
    (ξ : Ioi (0 : ℝ)) (Q : ℝ)
    (D : DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    ∃ M : ℝ, 1 ≤ M ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (h : Ω → DistC),
        IsNormalizedWholePlaneGFF h P → ∀ r : Ioi (0 : ℝ),
        ENNReal.ofReal p ≤ P {ω |
          h ω ∈ rawRatioEvent D 0 r
            (ENNReal.ofReal M * ENNReal.ofReal M)} := by
  obtain ⟨M, hM, hprob⟩ := TwoScale.RatioMarginal.center_raw_ratio_uniform
    ξ Q D hD BiLipschitz.OneScale.crossingShape p hp0 hp1
  refine ⟨M, hM, ?_⟩
  intro Ω _ P _ h hh r
  have hm := hprob P h hh 0 r
  have hshape : Positivity.Witnesses.annulusTranslate (BiLipschitz.OneScale.crossingShape.dilate r r.2) 0 =
      BiLipschitz.OneScale.crossingAt 0 r := rfl
  rw [hshape] at hm
  exact hm

def ratioRadius (base : Ioi (0 : ℝ)) (k : ℕ) : Ioi (0 : ℝ) :=
  ⟨(base : ℝ) * (1 / 10 : ℝ) ^ k, by
    have hb : 0 < (base : ℝ) := base.2
    change 0 < (base : ℝ) * (1 / 10 : ℝ) ^ k
    exact mul_pos hb (pow_pos (by norm_num) k)⟩

def ratioReference (base : Ioi (0 : ℝ)) (k : ℕ) : ℝ :=
  (5 * (base : ℝ)) * (1 / 10 : ℝ) ^ k

theorem ratioReference_eq_five_radius (base : Ioi (0 : ℝ)) (k : ℕ) :
    ratioReference base k = 5 * (ratioRadius base k : ℝ) := by
  unfold ratioReference ratioRadius
  ring

 

theorem ratio_iteration_count_tail
    (ξ : Ioi (0 : ℝ)) (Q : ℝ)
    (D : DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D)
    (a : ℝ) (ha : 0 < a) :
    ∃ p c M : ℝ, 0 < p ∧ p < 1 ∧ 0 < c ∧ 1 ≤ M ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (h : Ω → DistC),
        IsNormalizedWholePlaneGFF h P →
        ∀ (base : Ioi (0 : ℝ)) (K : ℕ),
          P {ω | (countOcc
            (fun k => {ω | h ω ∈ rawRatioEvent D 0 (ratioRadius base k)
              (ENNReal.ofReal M * ENNReal.ofReal M)}) K ω : ℝ) <
              (1 / 2 : ℝ) * K} ≤
            ENNReal.ofReal (c * Real.exp (-a * K)) := by
  obtain ⟨p, c, hp0, hp1, hc, H⟩ :=
    LQGMetric.LM.lmLem3_1a (1 / 10) (4 / 5)
      (by norm_num) (by norm_num) (by norm_num)
      a ha (1 / 2) (by norm_num) (by norm_num)
  obtain ⟨M, hM, hmarg⟩ := rawRatio_marginal_uniform ξ Q D hD p hp0 hp1
  refine ⟨p, c, M, hp0, hp1, hc, hM, ?_⟩
  intro Ω _ P _ h hh base K
  let raw : ℕ → Set Ω := fun k =>
    {ω | h ω ∈ rawRatioEvent D 0 (ratioRadius base k)
      (ENNReal.ofReal M * ENNReal.ofReal M)}
  let version : ℕ → Set Ω := fun k =>
    Classical.choose (origin_ratio_local_version P h hh ξ Q D hD
      (ratioRadius base k) (ENNReal.ofReal M * ENNReal.ofReal M))
  have hv : ∀ k,
      MeasurableSet[fieldSigma
        (fun ω => addConst (h ω) (-circleAvg (h ω) (ratioReference base k) 0))
        (annulus 0 ((1 / 10) * ratioReference base k)
          ((4 / 5) * ratioReference base k))] (version k) ∧
      version k =ᵐ[P] raw k := by
    intro k
    have hs := Classical.choose_spec (origin_ratio_local_version P h hh ξ Q D hD
      (ratioRadius base k) (ENNReal.ofReal M * ENNReal.ofReal M))
    rw [ratioReference_eq_five_radius] 
    exact hs
  have hb : 0 < (base : ℝ) := base.2
  have hrad := BiLipschitz.GridCover.e1e_radii (5 * (base : ℝ))
    (mul_pos (by norm_num) hb)
  have hiter : AnnulusIterHyp h (1 / 10) (4 / 5)
      (ratioReference base) version := by
    refine ⟨hrad.1, hrad.2.1, hrad.2.2, ?_⟩
    intro k
    exact (hv k).1
  have hprob : ∀ k, ENNReal.ofReal p ≤ P (version k) := by
    intro k
    rw [measure_congr (hv k).2]
    exact hmarg P h hh (ratioRadius base k)
  have htail := H P h (isNormalizedWholePlaneGFF_iff_old.mp hh)
    (ratioReference base) version hiter hprob K
  have hae : ∀ᵐ ω ∂P, ∀ k, (ω ∈ version k) ↔ (ω ∈ raw k) := by
    apply ae_all_iff.mpr
    intro k
    filter_upwards [(hv k).2] with ω hω
    exact Iff.of_eq hω
  have heq : {ω | (countOcc version K ω : ℝ) < (1 / 2 : ℝ) * K} =ᵐ[P]
      {ω | (countOcc raw K ω : ℝ) < (1 / 2 : ℝ) * K} := by
    filter_upwards [hae] with ω hω
    classical
    have hfilter : (Finset.Icc 1 K).filter (fun k => ω ∈ version k) =
        (Finset.Icc 1 K).filter (fun k => ω ∈ raw k) := by
      ext k
      simp only [Finset.mem_filter]
      exact and_congr_right fun _ => hω k
    simp only [countOcc, hfilter]
  rw [measure_congr heq] at htail
  exact htail


end SupercriticalLQGUniqueness.Uniqueness.TwoScale.Ratio
