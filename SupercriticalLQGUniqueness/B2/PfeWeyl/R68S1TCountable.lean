import SupercriticalLQGUniqueness.B2.PfeWeyl.R68S1TCoupled
import SupercriticalLQGUniqueness.B2.PfeAxioms.S2CircLemProb

 









set_option autoImplicit false
set_option linter.style.haveILetI false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal
open LQGMetric (DistC normGFFLaw heatMollify CoordJ pairJ pairJInv addFun)
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.PfeWeyl

 

theorem exists_fixedField_weyl_rationalCircle_countable_of_coupling
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (e : ℕ → Ioi (0 : ℝ)) (c : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (V : Ioi (0 : ℝ) → DistC → C(ℂ, ℝ))
    {Ω' : Type} [MeasurableSpace Ω'] [StandardBorelSpace Ω']
    (P' : Measure Ω') [IsProbabilityMeasure P']
    (h' : Ω' → DistC) (hN : ℕ → Ω' → DistC) (L : Ω' → LSCMetric)
    (hB : Final.DG20CouplingData ξ Q m e c V P' h' hN L)
    (hSA : Final.CoupledSmallAnnuli ξ m e V P' hN L)
    (hAT : Final.CoupledAcrossTails P' L)
    (hCirc : CoupledAllRationalCircles ξ m e V P' hN L)
    (Φ : DistC → LSCMetric) (hΦm : Measurable Φ)
    (hII : ∀ᵐ ω ∂P', L ω = Φ (h' ω))
    (hWeyl : BoundedShiftWeyl ξ Φ)
    (f : ℕ → C(ℂ, ℝ)) (M : ℕ → ℝ) (hM : ∀ j z, |f j z| ≤ M j) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), IsNormalizedWholePlaneGFF h P →
        ∀ X : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ),
          (∀ δ, IsHeatSmoothing P h δ (X δ)) →
          ∀ᵐ ω ∂P, ∀ j : ℕ, ∀ O O' : B2.DG20Lim.RatCircle,
            Tendsto (fun n => setDistance
              (normalizedLFPPMetric (ξ : ℝ) (m (e (ψ n)))
                (X (e (ψ n)) ω + LQGMetric.LFPP.mollCont
                  (e (ψ n) : ℝ) (e (ψ n)).property.ne' (f j) (M j) (hM j)))
                O.toSet O'.toSet) atTop
              (𝓝 (setDistance (weylScale (ξ : ℝ) (f j) (Φ (h ω)))
                O.toSet O'.toSet)) := by
  letI : IsProbabilityMeasure normGFFLaw := PfeAxioms.normalized_canonical_model.1
  letI : IsProbabilityMeasure (normGFFLaw.map (pairJ ⊤)) :=
    (Measure.isProbabilityMeasure_map_iff (LQGMetric.measurable_pairJ ⊤).aemeasurable).2
      inferInstance
  letI : MetricSpace (ℕ → B2.DG20Lim.RatCircle × B2.DG20Lim.RatCircle → ℝ≥0∞) :=
    TopologicalSpace.metrizableSpaceMetric _
  let shifted (n : ℕ) (g : DistC) (j : ℕ) : LSCMetric :=
    normalizedLFPPMetric (ξ : ℝ) (m (e n))
      (V (e n) g + LQGMetric.LFPP.mollCont (e n : ℝ) (e n).property.ne'
        (f j) (M j) (hM j))
  let circleDist (D : LSCMetric) (q : B2.DG20Lim.RatCircle × B2.DG20Lim.RatCircle) : ℝ≥0∞ :=
    setDistance D q.1.toSet q.2.toSet
  have hcomp : ∀ q : B2.DG20Lim.RatCircle × B2.DG20Lim.RatCircle,
      Measurable fun D : LSCMetric => circleDist D q := fun q =>
    PfeLocal.l4_measurable_setDistance (isCompact_sphere _ _) (isCompact_sphere _ _)
  have hR : ∀ n, Measurable fun a : CoordJ → ℝ =>
      fun j : ℕ => fun q : B2.DG20Lim.RatCircle × B2.DG20Lim.RatCircle =>
        circleDist (shifted n (pairJInv ⊤ a) j) q := by
    intro n
    refine Measurable.of_eval fun j => Measurable.of_eval fun q => (hcomp q).comp ?_
    exact PfeAxioms.measurable_normalizedLFPPMetric_comp (ξ : ℝ) _
      (fun z => ((continuous_eval_const z).measurable.comp
        ((hB.heat_measurable (e n)).comp (LQGMetric.measurable_pairJInv ⊤))).add
          measurable_const)
  have hΦc : Measurable fun a : CoordJ → ℝ =>
      fun j : ℕ => fun q : B2.DG20Lim.RatCircle × B2.DG20Lim.RatCircle =>
        circleDist (Φ (addFun (pairJInv ⊤ a) (f j))) q := by
    refine Measurable.of_eval fun j => Measurable.of_eval fun q => (hcomp q).comp ?_
    exact hΦm.comp ((LQGMetric.measurable_addFun_left (f j)).comp
      (LQGMetric.measurable_pairJInv ⊤))
  have hh'm : Measurable h' := hB.limit_field.1.measurable
  have hXlaw : ∀ n, P'.map (fun ω => pairJ ⊤ (hN n ω)) =
      normGFFLaw.map (pairJ ⊤) := fun n => by
    change P'.map (pairJ ⊤ ∘ hN n) = _
    rw [← Measure.map_map (LQGMetric.measurable_pairJ ⊤) (hB.field_measurable n),
      hB.field_law n]
  have hXllaw : P'.map (fun ω => pairJ ⊤ (h' ω)) = normGFFLaw.map (pairJ ⊤) := by
    change P'.map (pairJ ⊤ ∘ h') = _
    rw [← Measure.map_map (LQGMetric.measurable_pairJ ⊤) hh'm,
      ← PfeAxioms.normGFFLaw_eq_of_normalized P' h' hB.limit_field]
  have hXconv : ∀ᵐ ω ∂P', Tendsto (fun n => pairJ ⊤ (hN n ω)) atTop
      (𝓝 (pairJ ⊤ (h' ω))) :=
    hB.field_tendsto.mono fun _ hw =>
      (PfeAxioms.continuous_pairJ_top.tendsto _).comp hw
  have hWcoupled : ∀ᵐ ω ∂P', ∀ j,
      (Φ (addFun (h' ω) (f j))).1 = weylScale (ξ : ℝ) (f j) (Φ (h' ω)) := by
    rw [ae_all_iff]
    intro j
    exact hWeyl P' h' hB.limit_field (fun _ => f j) measurable_const
      (fun _ => ⟨M j, hM j⟩)
  have hYconv : ∀ᵐ ω ∂P', Tendsto (fun n =>
      fun j : ℕ => fun q : B2.DG20Lim.RatCircle × B2.DG20Lim.RatCircle =>
        circleDist (shifted n (pairJInv ⊤ (pairJ ⊤ (hN n ω))) j) q) atTop
      (𝓝 (fun j : ℕ => fun q : B2.DG20Lim.RatCircle × B2.DG20Lim.RatCircle =>
        circleDist (Φ (addFun (pairJInv ⊤ (pairJ ⊤ (h' ω))) (f j))) q)) := by
    filter_upwards [ae_coupled_weyl_rationalCircle_all_bounded ξ Q m e c V P' h' hN L
      hB hSA hAT hCirc, hII, hWcoupled] with ω hc hL hW
    refine tendsto_pi_nhds.2 fun j => tendsto_pi_nhds.2 fun q => ?_
    simp only [LQGMetric.pairJInv_pairJ]
    have hq := hc (f j) (M j) (hM j) q.1.toSet q.2.toSet
      ⟨q.1.x, q.1.y, q.1.radius, q.1.radius_nonneg, rfl⟩
      ⟨q.2.x, q.2.y, q.2.radius, q.2.radius_nonneg, rfl⟩
    rw [hL, ← hW j] at hq
    exact hq
  obtain ⟨ψ, hψ, hae⟩ := PfeAxioms.exists_subseq_ae_of_coords_gen
    (T := ℕ → B2.DG20Lim.RatCircle × B2.DG20Lim.RatCircle → ℝ≥0∞)
    (normGFFLaw.map (pairJ ⊤))
    (fun n a j q => circleDist (shifted n (pairJInv ⊤ a) j) q)
    (fun a j q => circleDist (Φ (addFun (pairJInv ⊤ a) (f j))) q)
    hR hΦc P'
    (fun n ω => pairJ ⊤ (hN n ω)) (fun ω => pairJ ⊤ (h' ω))
    (fun n => (LQGMetric.measurable_pairJ ⊤).comp (hB.field_measurable n))
    ((LQGMetric.measurable_pairJ ⊤).comp hh'm)
    hXlaw hXllaw hXconv hYconv
  refine ⟨ψ, hψ, ?_⟩
  intro Ω _ P _ h hh X hX
  have hlaw : P.map (fun ω => pairJ ⊤ (h ω)) = normGFFLaw.map (pairJ ⊤) := by
    change P.map (pairJ ⊤ ∘ h) = _
    rw [← Measure.map_map (LQGMetric.measurable_pairJ ⊤) hh.1.measurable,
      ← PfeAxioms.normGFFLaw_eq_of_normalized P h hh]
  have h1 := hae P (fun ω => pairJ ⊤ (h ω))
    ((LQGMetric.measurable_pairJ ⊤).comp hh.1.measurable).aemeasurable hlaw
  have hXe := PfeAxioms.ae_heat_smoothing_sequence_eq P h hh (e ∘ ψ) X hX
  have hVe : ∀ᵐ ω ∂P, ∀ n z,
      V (e (ψ n)) (h ω) z = heatMollify (e (ψ n) : ℝ) (h ω) z := by
    rw [ae_all_iff]
    intro n
    have h2 := hB.heat_ae (e (ψ n))
    rw [PfeAxioms.normGFFLaw_eq_of_normalized P h hh] at h2
    exact ae_of_ae_map hh.1.measurable.aemeasurable h2
  have hWfixed : ∀ᵐ ω ∂P, ∀ j,
      (Φ (addFun (h ω) (f j))).1 = weylScale (ξ : ℝ) (f j) (Φ (h ω)) := by
    rw [ae_all_iff]
    intro j
    exact hWeyl P h hh (fun _ => f j) measurable_const (fun _ => ⟨M j, hM j⟩)
  filter_upwards [h1, hXe, hVe, hWfixed] with ω hω hXω hVω hW j O O'
  have heq : ∀ k, X (e (ψ k)) ω = V (e (ψ k)) (h ω) := fun k =>
    ContinuousMap.ext fun z => (hXω k z).trans (hVω k z).symm
  have hq := (tendsto_pi_nhds.1 ((tendsto_pi_nhds.1 hω) j)) (O, O')
  simp only [LQGMetric.pairJInv_pairJ, shifted, circleDist] at hq
  rw [hW j] at hq
  simpa only [heq] using hq

end SupercriticalLQGUniqueness.B2.PfeWeyl
