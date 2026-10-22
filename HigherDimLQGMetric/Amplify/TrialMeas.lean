import HigherDimLQGMetric.Amplify.Defs
import HigherDimLQGMetric.Events.WitnessMeas
import HigherDimLQGMetric.Events.AnalyticQuant

/-!
# Universal measurability of trial events

The path witness is projected from a Borel relation on continuous unit interval paths.
Internal distances are represented by the countable chain formula on length metrics.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory Set Metric LQGMetric
open HigherDimLFPP (Rd)
open scoped ENNReal

variable {d : ℕ}

private def trialRelBorel (D Dt : DistRd d → ContMetric d)
    (ξ Q c1 ℓ δ s : ℝ) (w : Rd d) :
    Set (DistRd d × C(unitInterval, Rd d)) :=
  {q | (∀ t : unitInterval, q.2 t ∈ annCl w s (2 * s)) ∧
    ENNReal.ofReal (Real.exp (-ξ * δ) * (ℓ / (2 * c1)) * sNorm ξ Q q.1 s w) ≤
      (D q.1).chainInf (ann w (3 * s / 4) (3 * s)) (q.2 0) (q.2 1) ∧
    (Dt q.1).len (pathExt q.2) 0 1 ≤
      ENNReal.ofReal (Real.exp (ξ * δ) * ℓ * sNorm ξ Q q.1 s w) ∧
    (Dt q.1).len (pathExt q.2) 0 1 ≤
      ENNReal.ofReal (Real.exp (2 * ξ * δ) * c1) *
        (D q.1).chainInf (ann w (3 * s / 4) (3 * s)) (q.2 0) (q.2 1)}

private theorem measurableSet_trialRelBorel
    {D Dt : DistRd d → ContMetric d} (hD : Measurable D) (hDt : Measurable Dt)
    (ξ Q c1 ℓ δ s : ℝ) (w : Rd d) :
    MeasurableSet (trialRelBorel D Dt ξ Q c1 ℓ δ s w) := by
  have heval (t : unitInterval) :
      Measurable fun q : DistRd d × C(unitInterval, Rd d) => q.2 t :=
    (continuous_eval_const t).measurable.comp measurable_snd
  have hn : Measurable fun q : DistRd d × C(unitInterval, Rd d) =>
      sNorm ξ Q q.1 s w := by
    exact (measurable_const.mul (Real.measurable_exp.comp
      (measurable_const.mul (measurable_sphereAvg_left s w)))).comp measurable_fst
  have hi : Measurable fun q : DistRd d × C(unitInterval, Rd d) =>
      (D q.1).chainInf (ann w (3 * s / 4) (3 * s)) (q.2 0) (q.2 1) :=
    (ContMetric.measurable_chainInf _).comp
      ((hD.comp measurable_fst).prodMk ((heval 0).prodMk (heval 1)))
  have hl : Measurable fun q : DistRd d × C(unitInterval, Rd d) =>
      (Dt q.1).len (pathExt q.2) 0 1 :=
    measurable_lenPath.comp ((hDt.comp measurable_fst).prodMk measurable_snd)
  have hpaths : MeasurableSet {q : DistRd d × C(unitInterval, Rd d) |
      ∀ t : unitInterval, q.2 t ∈ annCl w s (2 * s)} := by
    have hc : IsClosed {η : C(unitInterval, Rd d) |
        ∀ t : unitInterval, η t ∈ annCl w s (2 * s)} := by
      simp only [ofPred_forall]
      exact isClosed_iInter fun t => (isClosed_annCl w s (2 * s)).preimage
        (continuous_eval_const t)
    exact hc.measurableSet.preimage measurable_snd
  unfold trialRelBorel
  exact hpaths.inter ((measurableSet_le
    (ENNReal.measurable_ofReal.comp (measurable_const.mul hn)) hi).inter
    ((measurableSet_le hl
      (ENNReal.measurable_ofReal.comp (measurable_const.mul hn))).inter
      (measurableSet_le hl (measurable_const.mul hi))))

private def trialChainEvent (D Dt : DistRd d → ContMetric d)
    (ξ Q cs c1 ℓ δ s : ℝ) (w : Rd d) : Set (DistRd d) :=
  {X | ENNReal.ofReal (Real.exp (-ξ * δ) * (4 * max 1 cs⁻¹ * ℓ) *
      sNorm ξ Q X s w) <
      (⨅ u ∈ annCl w s (2 * s), ⨅ v ∈
        (sphere w (3 * s / 4) ∪ sphere w (3 * s)),
        (D X).chainInf (ann w (s / 2) (5 * s)) u v) ∧
    ∃ η : C(unitInterval, Rd d), (X, η) ∈ trialRelBorel D Dt ξ Q c1 ℓ δ s w}

private theorem uMeasurableSet_trialChainEvent
    {D Dt : DistRd d → ContMetric d} (hD : Measurable D) (hDt : Measurable Dt)
    (ξ Q cs c1 ℓ δ s : ℝ) (w : Rd d) :
    UMeasurableSet (trialChainEvent D Dt ξ Q cs c1 ℓ δ s w) := by
  have hn : Measurable fun X : DistRd d => sNorm ξ Q X s w :=
    measurable_const.mul (Real.measurable_exp.comp
      (measurable_const.mul (measurable_sphereAvg_left s w)))
  let K : Set (Rd d × Rd d) :=
    annCl w s (2 * s) ×ˢ (sphere w (3 * s / 4) ∪ sphere w (3 * s))
  have hK : MeasurableSet K :=
    (isClosed_annCl w s (2 * s)).measurableSet.prod
      ((isClosed_sphere.union isClosed_sphere).measurableSet)
  have hi : Measurable fun p : DistRd d × (Rd d × Rd d) =>
      (D p.1).chainInf (ann w (s / 2) (5 * s)) p.2.1 p.2.2 :=
    (ContMetric.measurable_chainInf _).comp
      ((hD.comp measurable_fst).prodMk measurable_snd)
  have hc : UMeasurableSet {X : DistRd d |
      ENNReal.ofReal (Real.exp (-ξ * δ) * (4 * max 1 cs⁻¹ * ℓ) *
        sNorm ξ Q X s w) <
        (⨅ u ∈ annCl w s (2 * s), ⨅ v ∈
          (sphere w (3 * s / 4) ∪ sphere w (3 * s)),
          (D X).chainInf (ann w (s / 2) (5 * s)) u v)} := by
    have hm := uMeasurableSet_lt_iInf K hK hi
      (c := fun X => ENNReal.ofReal (Real.exp (-ξ * δ) *
        (4 * max 1 cs⁻¹ * ℓ) * sNorm ξ Q X s w))
      (ENNReal.measurable_ofReal.comp (measurable_const.mul hn))
    convert hm using 1
    ext X
    simp only [K, biInf_prod]
  have hp : UMeasurableSet {X : DistRd d |
      ∃ η : C(unitInterval, Rd d), (X, η) ∈ trialRelBorel D Dt ξ Q c1 ℓ δ s w} :=
    UMeasurableSet.setOf_exists (measurableSet_trialRelBorel hD hDt ξ Q c1 ℓ δ s w)
  exact hc.inter hp

private theorem trialEvent_iff_chain (D Dt : DistRd d → ContMetric d)
    (ξ Q cs c1 ℓ δ s : ℝ) (w : Rd d) (X : DistRd d)
    (hD : (D X).IsLength) :
    X ∈ TrialEvent D Dt ξ Q cs c1 ℓ δ s w ↔
      X ∈ trialChainEvent D Dt ξ Q cs c1 ℓ δ s w := by
  have hJ : (D X).internal (ann w (s / 2) (5 * s)) =
      (D X).chainInf (ann w (s / 2) (5 * s)) := by
    funext u v
    exact (D X).internal_eq_chainInf hD (isOpen_ann _ _ _) u v
  have hO : (D X).internal (ann w (3 * s / 4) (3 * s)) =
      (D X).chainInf (ann w (3 * s / 4) (3 * s)) := by
    funext u v
    exact (D X).internal_eq_chainInf hD (isOpen_ann _ _ _) u v
  constructor
  · rintro ⟨hc, P, hPc, hPK, hlow, hhigh, hratio⟩
    obtain ⟨η, hηP, hlen⟩ := exists_pathContinuousMap hPc
    have he0 : η 0 = P 0 := by
      rw [← pathExt_zero η]
      exact hηP (by norm_num)
    have he1 : η 1 = P 1 := by
      rw [← pathExt_one η]
      exact hηP (by norm_num)
    refine ⟨?_, η, ?_⟩
    · simpa only [setDistIn, hJ, biInf_prod] using hc
    · dsimp only [trialRelBorel, mem_ofPred_eq]
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro t
        have he : η t = P t := by
          calc
            η t = pathExt η (t : ℝ) := by
              change η t = η (Set.projIcc 0 1 zero_le_one (t : ℝ))
              congr 1
              simpa only using (Set.projIcc_of_mem _ t.2).symm
            _ = P t := hηP t.2
        rw [he]
        exact hPK t t.2
      · simpa only [hO, he0, he1] using hlow
      · simpa only [hlen (Dt X)] using hhigh
      · simpa only [hO, he0, he1, hlen (Dt X)] using hratio
  · rintro ⟨hc, η, hrel⟩
    rcases hrel with ⟨hηK, hlow, hhigh, hratio⟩
    refine ⟨?_, pathExt η, pathExt_continuousOn η, ?_, ?_, ?_, ?_⟩
    · simpa only [setDistIn, hJ, biInf_prod] using hc
    · intro t ht
      exact hηK (Set.projIcc 0 1 zero_le_one t)
    · simpa only [hO, pathExt_zero, pathExt_one] using hlow
    · exact hhigh
    · simpa only [hO, pathExt_zero, pathExt_one] using hratio

/-- Trial events are measurable after completion under the law of an admissible field. -/
theorem amplify_nullMeasurableSet_trialEvent
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsLGFPlusCont h P)
    {ξ Q : ℝ} {D Dt : DistRd d → ContMetric d}
    (hD : IsSharpWeakExpMetric d ξ Q D)
    (_hDt : IsSharpWeakExpMetric d ξ Q Dt)
    (cs c1 ℓ δ s : ℝ) (w : Rd d) :
    NullMeasurableSet (h ⁻¹' TrialEvent D Dt ξ Q cs c1 ℓ δ s w) P := by
  have hchain : NullMeasurableSet
      (h ⁻¹' trialChainEvent D Dt ξ Q cs c1 ℓ δ s w) P :=
    (uMeasurableSet_trialChainEvent hD.measurable _hDt.measurable ξ Q cs c1 ℓ δ s w).nullMeasurableSet_preimage hh.measurable.aemeasurable
  have he : h ⁻¹' TrialEvent D Dt ξ Q cs c1 ℓ δ s w =ᵐ[P]
      h ⁻¹' trialChainEvent D Dt ξ Q cs c1 ℓ δ s w := by
    filter_upwards [hD.length P h hh] with ω hl
    exact propext (trialEvent_iff_chain D Dt ξ Q cs c1 ℓ δ s w (h ω) hl)
  exact hchain.congr he.symm

end HigherDimLQGMetric
