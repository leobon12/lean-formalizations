import SupercriticalLQGUniqueness.B2.DG20Lim.LimitRelations
import LQGMetric.Papers.DFGPS.L2_17CoreC
import Mathlib.Topology.Metrizable.Basic
import LQGMetric.Field.StandardBorelRange
import LQGMetric.Field.RandomDistVersion
import LQGMetric.Papers.DFGPS.L2_17Core3B

 





set_option autoImplicit false
noncomputable section

open scoped ENNReal
open MeasureTheory ProbabilityTheory Filter Topology Set TopologicalSpace

namespace SupercriticalLQGUniqueness.B2.DG20Lim

instance : Countable RatCircle := by
  classical
  have h : Function.Injective (fun O : RatCircle => (O.x, O.y, O.radius)) := by
    intro O P h
    cases O with
    | mk x y r hr =>
      cases P with
      | mk x' y' r' hr' =>
        simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        rfl
  simpa only [Set.preimage_univ, Set.countable_univ_iff] using
    (Set.countable_univ.preimage h)

instance : Countable RatAnnulus := by
  classical
  have h : Function.Injective (fun A : RatAnnulus => (A.inner, A.outer)) := by
    intro A B h
    cases A with
    | mk I O hI hO =>
      cases B with
      | mk I' O' hI' hO' =>
        simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rfl
  simpa only [Set.preimage_univ, Set.countable_univ_iff] using
    (Set.countable_univ.preimage h)

 
abbrev RatCoords :=
  ((RatCircle × RatCircle → ℝ≥0∞) × (RatAnnulus → ℝ≥0∞))

instance : CompactSpace RatCoords := inferInstance
instance : SecondCountableTopology RatCoords := inferInstance
instance : T2Space RatCoords := inferInstance
instance : TopologicalSpace.PseudoMetrizableSpace RatCoords := inferInstance
instance : PolishSpace RatCoords := inferInstance

 


theorem exists_joint_coord_limit
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → LQGMetric.DistC)
    (hh : Measurable h) (C : ℕ → Ω → RatCoords)
    (hC : ∀ n, Measurable (C n)) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∃ ρ : ProbabilityMeasure ((LQGMetric.CoordJ → ℝ) × RatCoords),
        Tendsto (β := ProbabilityMeasure ((LQGMetric.CoordJ → ℝ) × RatCoords))
          (fun n => (⟨P.map fun ω => (LQGMetric.pairJ ⊤ (h ω), C (ψ n) ω),
            (Measure.isProbabilityMeasure_map_iff
              (((LQGMetric.measurable_pairJ ⊤).comp hh).prodMk (hC (ψ n))).aemeasurable).2
                inferInstance⟩ :
              ProbabilityMeasure ((LQGMetric.CoordJ → ℝ) × RatCoords))) atTop (𝓝 ρ) ∧
        (ρ : Measure ((LQGMetric.CoordJ → ℝ) × RatCoords)).map Prod.fst =
          P.map (fun ω => LQGMetric.pairJ ⊤ (h ω)) := by
  exact LQGMetric.DFGPS.L217.exists_limit_coupling
    ((LQGMetric.measurable_pairJ ⊤).comp hh) hC
    (IsTightMeasureSet.of_compactSpace)

 

theorem exists_joint_coord_skorokhod
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → LQGMetric.DistC)
    (hh : Measurable h) (C : ℕ → Ω → RatCoords)
    (hC : ∀ n, Measurable (C n)) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∃ (Ω' : Type) (_ : MeasurableSpace Ω')
        (_ : StandardBorelSpace Ω') (P' : Measure Ω')
        (_ : IsProbabilityMeasure P')
        (Y : ℕ → Ω' → (LQGMetric.CoordJ → ℝ) × RatCoords)
        (Ylim : Ω' → (LQGMetric.CoordJ → ℝ) × RatCoords),
        (∀ n, Measurable (Y n)) ∧ Measurable Ylim ∧
        (∀ n, P'.map (Y n) = P.map
          (fun ω => (LQGMetric.pairJ ⊤ (h ω), C (ψ n) ω))) ∧
        (∀ ω, Tendsto (fun n => Y n ω) atTop (𝓝 (Ylim ω))) ∧
        P'.map (fun ω => LQGMetric.pairJInv ⊤ (Ylim ω).1) = P.map h := by
  obtain ⟨ψ, hψ, ρ, hlim, hmarg⟩ := exists_joint_coord_limit P h hh C hC
  obtain ⟨Ω', mΩ', sbΩ', P', hP', Y, Ylim, hY, hYlim, hYlaw, hYlimLaw, hYconv⟩ :=
    LQGMetric.DFGPS.L217.exists_skorokhod_representation_sb hlim
  refine ⟨ψ, hψ, Ω', mΩ', sbΩ', P', hP', Y, Ylim, hY, hYlim, ?_, hYconv, ?_⟩
  · intro n
    exact hYlaw n
  · have hm : Measurable (fun q : (LQGMetric.CoordJ → ℝ) × RatCoords =>
        LQGMetric.pairJInv ⊤ q.1) :=
      (LQGMetric.measurable_pairJInv ⊤).comp measurable_fst
    calc
      P'.map (fun ω => LQGMetric.pairJInv ⊤ (Ylim ω).1) =
          (P'.map Ylim).map (fun q => LQGMetric.pairJInv ⊤ q.1) :=
        (Measure.map_map hm hYlim).symm
      _ = (ρ : Measure ((LQGMetric.CoordJ → ℝ) × RatCoords)).map
          (fun q : (LQGMetric.CoordJ → ℝ) × RatCoords =>
            LQGMetric.pairJInv ⊤ q.1) := by
        rw [hYlimLaw]
      _ = ((ρ : Measure ((LQGMetric.CoordJ → ℝ) × RatCoords)).map Prod.fst).map
          (LQGMetric.pairJInv ⊤) :=
        by
          change Measure.map ((LQGMetric.pairJInv ⊤) ∘ Prod.fst)
              (ρ : Measure ((LQGMetric.CoordJ → ℝ) × RatCoords)) =
            Measure.map (LQGMetric.pairJInv ⊤)
              (Measure.map Prod.fst
                (ρ : Measure ((LQGMetric.CoordJ → ℝ) × RatCoords)))
          exact (Measure.map_map (LQGMetric.measurable_pairJInv ⊤)
            measurable_fst).symm
      _ = (P.map (fun ω => LQGMetric.pairJ ⊤ (h ω))).map
          (LQGMetric.pairJInv ⊤) := by rw [hmarg]
      _ = P.map h := by
        have hc : (fun ω => LQGMetric.pairJ ⊤ (h ω)) =
            LQGMetric.pairJ ⊤ ∘ h := rfl
        rw [hc, Measure.map_map (LQGMetric.measurable_pairJInv ⊤)
          ((LQGMetric.measurable_pairJ ⊤).comp hh)]
        exact Measure.map_congr (Filter.Eventually.of_forall fun ω => by
          exact LQGMetric.pairJInv_pairJ ⊤ (h ω))

 

theorem circle_coord_tendsto
    {Y : ℕ → (LQGMetric.CoordJ → ℝ) × RatCoords}
    {y : (LQGMetric.CoordJ → ℝ) × RatCoords}
    (hY : Tendsto Y atTop (𝓝 y)) (O P : RatCircle) :
    Tendsto (fun n => (Y n).2.1 (O, P)) atTop (𝓝 (y.2.1 (O, P))) := by
  exact (((continuous_apply (O, P)).comp
    (continuous_fst.comp continuous_snd)).tendsto y).comp hY

 
theorem around_coord_tendsto
    {Y : ℕ → (LQGMetric.CoordJ → ℝ) × RatCoords}
    {y : (LQGMetric.CoordJ → ℝ) × RatCoords}
    (hY : Tendsto Y atTop (𝓝 y)) (A : RatAnnulus) :
    Tendsto (fun n => (Y n).2.2 A) atTop (𝓝 (y.2.2 A)) := by
  exact (((continuous_apply A).comp
    (continuous_snd.comp continuous_snd)).tendsto y).comp hY

end SupercriticalLQGUniqueness.B2.DG20Lim
