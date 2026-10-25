import SupercriticalLQGUniqueness.B2.DG20Lim.UniversalCoordLaw
import SupercriticalLQGUniqueness.B2.DG20Lim.FieldCoordFromStationaryLaw
import SupercriticalLQGUniqueness.B2.DG20Lim.SkUpgradeCanonical
import SupercriticalLQGUniqueness.B2.DG20Lim.PolishEquicont

 


















set_option autoImplicit false
set_option linter.style.haveILetI false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology LQGMetric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

 
def prjCoords (y : FieldCoords × RatCoords) : (CoordJ → ℝ) × RatCoords := (y.1.1, y.2)

theorem measurable_prjCoords : Measurable prjCoords :=
  (measurable_fst.comp measurable_fst).prodMk measurable_snd

 

theorem exists_lfpp_joint_field_skorokhod_of_canonical_limit
    (ξ : ℝ) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (ε : ℕ → Set.Ioi (0 : ℝ))
    (ρ : ProbabilityMeasure (FieldCoords × RatCoords))
    (hlim : Tendsto (fun n => fieldLawSeq ξ m ε n) atTop (𝓝 ρ))
    (hmarg : (ρ : Measure (FieldCoords × RatCoords)).map Prod.fst =
      normGFFLaw.map fieldCoords)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (X : Set.Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ δ, IsHeatSmoothing P h δ (X δ)) :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω')
      (_ : StandardBorelSpace Ω') (P' : Measure Ω')
      (_ : IsProbabilityMeasure P')
      (Y : ℕ → Ω' → (CoordJ → ℝ) × RatCoords)
      (Ylim : Ω' → (CoordJ → ℝ) × RatCoords),
      (∀ n, Measurable (Y n)) ∧ Measurable Ylim ∧
      (∀ n, P'.map (Y n) = P.map (fun ω =>
        (pairJ ⊤ (h ω), measurableRatCoordsVersion
          (fun ω => normalizedContLFPP ξ (m (ε n)) (X (ε n) ω))
          (aemeasurable_normalizedContLFPP_heat_version P h hh
            (ε n) (m (ε n)) ξ (X (ε n)) (hX (ε n))) ω))) ∧
      IsNormalizedWholePlaneGFF
        (fun ω => pairJInv ⊤ (Ylim ω).1) P' ∧
      (∀ n, P'.map (fun ω =>
        (pairJInv ⊤ (Y n ω).1,
          finiteMetricE (circleCoordsInv (Y n ω).2.1))) =
        P.map (fun ω => (h ω,
          rescaledLFPP ξ (m (ε n)) (X (ε n) ω)))) ∧
      (∀ n ω, Continuous
        (finiteMetricE (circleCoordsInv (Y n ω).2.1))) ∧
      (∀ ω, Tendsto (fun n => Y n ω) atTop (𝓝 (Ylim ω))) ∧
      (∀ᵐ ω ∂P', Tendsto (fun n => pairJInv ⊤ (Y n ω).1) atTop
        (𝓝 (pairJInv ⊤ (Ylim ω).1))) := by
  letI : IsProbabilityMeasure normGFFLaw :=
    B2.PfeAxioms.normalized_canonical_model.1
  obtain ⟨Ω', mΩ', sbΩ', P', hP', Z, Zlim, hZm, hZlimm,
      hZlaw, hZlimLaw, hZConv⟩ :=
    LQGMetric.DFGPS.L217.exists_skorokhod_representation_sb hlim
  letI : MeasurableSpace Ω' := mΩ'
  letI : IsProbabilityMeasure P' := hP'
  let Y : ℕ → Ω' → (CoordJ → ℝ) × RatCoords := fun n ω => prjCoords (Z n ω)
  let Ylim : Ω' → (CoordJ → ℝ) × RatCoords := fun ω => prjCoords (Zlim ω)
  have hYm : ∀ n, Measurable (Y n) := fun n => measurable_prjCoords.comp (hZm n)
  have hYlimm : Measurable Ylim := measurable_prjCoords.comp hZlimm
  have hConv : ∀ ω, Tendsto (fun n => Y n ω) atTop (𝓝 (Ylim ω)) := fun ω =>
    (((continuous_fst.comp continuous_fst).prodMk continuous_snd).tendsto
      (Zlim ω)).comp (hZConv ω)
  have hG (n : ℕ) : Measurable
      (fun g => (fieldCoords g, canonicalCoordSeq ξ m ε n g)) :=
    measurable_fieldCoords.prodMk (measurable_canonicalCoordSeq ξ m ε n)
  have hYlaw (n : ℕ) : P'.map (Y n) = normGFFLaw.map (fun g =>
      (pairJ ⊤ g, canonicalCoordSeq ξ m ε n g)) := by
    calc P'.map (Y n) = (P'.map (Z n)).map prjCoords :=
          (Measure.map_map measurable_prjCoords (hZm n)).symm
      _ = (normGFFLaw.map (fun g =>
          (fieldCoords g, canonicalCoordSeq ξ m ε n g))).map prjCoords := by
        rw [hZlaw n, fieldLawSeq_coe]
      _ = _ := Measure.map_map measurable_prjCoords (hG n)
  let D : ℕ → Ω → ContMetric := fun n ω =>
    normalizedContLFPP ξ (m (ε n)) (X (ε n) ω)
  have hD : ∀ n, AEMeasurable (D n) P := by
    intro n
    exact aemeasurable_normalizedContLFPP_heat_version P h hh
      (ε n) (m (ε n)) ξ (X (ε n)) (hX (ε n))
  have hCoordLaw (n : ℕ) :
      P'.map (Y n) = P.map (fun ω =>
        (pairJ ⊤ (h ω), measurableRatCoordsVersion (D n) (hD n) ω)) := by
    calc
      P'.map (Y n) = normGFFLaw.map (fun g =>
          (pairJ ⊤ g, canonicalCoordSeq ξ m ε n g)) := hYlaw n
      _ = P.map (fun ω =>
          (pairJ ⊤ (h ω), measurableRatCoordsVersion (D n) (hD n) ω)) := by
        exact (joint_rat_coords_law_eq_canonical P h hh (ε n) (m (ε n))
          ξ (X (ε n)) (hX (ε n))).symm
  have hZlimFst : P'.map (fun ω => (Zlim ω).1) = normGFFLaw.map fieldCoords := by
    calc P'.map (fun ω => (Zlim ω).1) = (P'.map Zlim).map Prod.fst :=
          (Measure.map_map measurable_fst hZlimm).symm
      _ = normGFFLaw.map fieldCoords := by rw [hZlimLaw, hmarg]
  have hLm : Measurable (fun ω => pairJInv ⊤ (Ylim ω).1) :=
    (measurable_pairJInv ⊤).comp (measurable_fst.comp hYlimm)
  have hMarg : P'.map (fun ω => pairJInv ⊤ (Ylim ω).1) = normGFFLaw := by
    have hDecode : Measurable (fun q : FieldCoords => pairJInv ⊤ q.1) :=
      (measurable_pairJInv ⊤).comp measurable_fst
    calc
      P'.map (fun ω => pairJInv ⊤ (Ylim ω).1) =
          (P'.map (fun ω => (Zlim ω).1)).map (fun q : FieldCoords => pairJInv ⊤ q.1) :=
        (Measure.map_map hDecode (measurable_fst.comp hZlimm)).symm
      _ = (normGFFLaw.map fieldCoords).map (fun q : FieldCoords => pairJInv ⊤ q.1) := by
        rw [hZlimFst]
      _ = normGFFLaw := by
        rw [Measure.map_map hDecode measurable_fieldCoords]
        calc
          normGFFLaw.map ((fun q : FieldCoords => pairJInv ⊤ q.1) ∘ fieldCoords) =
              normGFFLaw.map id := Measure.map_congr
                (Filter.Eventually.of_forall fun g => pairJInv_pairJ ⊤ g)
          _ = normGFFLaw := Measure.map_id
  have hNorm : IsNormalizedWholePlaneGFF
      (fun ω => pairJInv ⊤ (Ylim ω).1) P' :=
    normalizedGFF_of_law_eq (id : DistC → DistC)
      B2.PfeAxioms.normalized_canonical_model.2 _ hLm
      (by simpa only [Measure.map_id] using hMarg)
  
  let V : ℕ → Ω → RatCoords := fun n => measurableRatCoordsVersion (D n) (hD n)
  have hField := ae_decoded_field_coords_tendsto_of_stationary_laws
    P P' h hh.1.measurable Y Ylim V hYm hYlimm
    (fun n => measurable_measurableRatCoordsVersion (D n) (hD n)) hCoordLaw hConv
  let S : Set (FieldCoords × RatCoords) :=
    {y | y.1.2 = ordCoords (pairJ ⊤ (pairJInv ⊤ y.1.1))}
  have hS : MeasurableSet S :=
    measurableSet_eq_fun (measurable_snd.comp measurable_fst)
      ((measurable_ordCoords.comp (measurable_pairJ ⊤)).comp
        ((measurable_pairJInv ⊤).comp (measurable_fst.comp measurable_fst)))
  have hOrd : ∀ n, ∀ᵐ ω ∂P', (Z n ω).1.2 =
      ordCoords (pairJ ⊤ (pairJInv ⊤ (Z n ω).1.1)) := by
    intro n
    have hlaw : ∀ᵐ y ∂(P'.map (Z n)), y ∈ S := by
      rw [hZlaw n, fieldLawSeq_coe]
      refine (ae_map_iff (p := fun y => y ∈ S) (hG n).aemeasurable hS).2 ?_
      exact Filter.Eventually.of_forall fun g => by
        simp only [S, Set.mem_ofPred_eq, fieldCoords, pairJInv_pairJ]
    exact (ae_map_iff (p := fun y => y ∈ S) (hZm n).aemeasurable hS).1 hlaw
  let Fin : Set FieldCoords := {q | ∀ k, ∃ N, q.2 (k, N) < ⊤}
  have hFinM : MeasurableSet Fin := by
    simp only [Fin, Set.ofPred_forall, Set.ofPred_exists]
    exact MeasurableSet.iInter fun k => MeasurableSet.iUnion fun N =>
      measurableSet_lt ((measurable_pi_apply (k, N)).comp measurable_snd)
        measurable_const
  have hFin : ∀ᵐ ω ∂P', (Zlim ω).1 ∈ Fin := by
    have hlaw : ∀ᵐ q ∂(P'.map (fun ω => (Zlim ω).1)), q ∈ Fin := by
      rw [hZlimFst]
      refine (ae_map_iff (p := fun q => q ∈ Fin) measurable_fieldCoords.aemeasurable hFinM).2 ?_
      exact Filter.Eventually.of_forall fun g k => exists_ordCoord_lt_top g k
    exact (ae_map_iff (p := fun q => q ∈ Fin)
      (measurable_fst.comp hZlimm).aemeasurable hFinM).1 hlaw
  have hFieldTop : ∀ᵐ ω ∂P', Tendsto (fun n => pairJInv ⊤ (Y n ω).1) atTop
      (𝓝 (pairJInv ⊤ (Ylim ω).1)) := by
    filter_upwards [hField, hFin, ae_all_iff.2 hOrd] with ω hF hFn hO
    exact tendsto_distC_of_ordCoords (u := fun n => (Z n ω).1.2)
      (u₀ := (Zlim ω).1.2) hO
      (((continuous_snd.comp continuous_fst).tendsto (Zlim ω)).comp (hZConv ω))
      hFn hF
  refine ⟨Ω', mΩ', sbΩ', P', hP', Y, Ylim,
    hYm, hYlimm, hCoordLaw, hNorm, ?_, ?_, hConv, hFieldTop⟩
  · intro n
    have hFinite := joint_finite_pair_law_of_coord_law h hh.1.measurable
      (D n) (hD n) (Y n) (hYm n) (hCoordLaw n)
    exact joint_law_rescaledLFPP_of_finite_law h hh.1.measurable
      (D n) (hD n) (Y n) (hYm n) hFinite ξ (m (ε n))
      (X (ε n)) (fun _ => rfl)
  · intro n ω
    exact continuous_finiteMetricE _

end SupercriticalLQGUniqueness.B2.DG20Lim
