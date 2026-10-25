import SupercriticalLQGUniqueness.B2.DG20Lim.ScaleCanonicalSubseq
import SupercriticalLQGUniqueness.B2.DG20Lim.FieldMarginal

 


set_option autoImplicit false
set_option linter.style.haveILetI false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology LQGMetric

namespace SupercriticalLQGUniqueness.B2.DG20Lim

 


theorem exists_lfpp_joint_coord_skorokhod_of_canonical_limit
    (ξ : ℝ) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (ε : ℕ → Set.Ioi (0 : ℝ))
    (ρ : ProbabilityMeasure ((CoordJ → ℝ) × RatCoords))
    (hlim : Tendsto (β := ProbabilityMeasure ((CoordJ → ℝ) × RatCoords))
      (fun n => (⟨normGFFLaw.map
          (fun g => (pairJ ⊤ g, canonicalCoordSeq ξ m ε n g)),
        (Measure.isProbabilityMeasure_map_iff
          (((measurable_pairJ ⊤).comp measurable_id).prodMk
            (measurable_canonicalCoordSeq ξ m ε n)).aemeasurable).2
            B2.PfeAxioms.normalized_canonical_model.1⟩ :
          ProbabilityMeasure ((CoordJ → ℝ) × RatCoords))) atTop (𝓝 ρ))
    (hmarg : (ρ : Measure ((CoordJ → ℝ) × RatCoords)).map Prod.fst =
      normGFFLaw.map (pairJ ⊤))
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
      IsNormalizedWholePlaneGFF
        (fun ω => pairJInv ⊤ (Ylim ω).1) P' ∧
      (∀ n, P'.map (fun ω =>
        (pairJInv ⊤ (Y n ω).1,
          finiteMetricE (circleCoordsInv (Y n ω).2.1))) =
        P.map (fun ω => (h ω,
          rescaledLFPP ξ (m (ε n)) (X (ε n) ω)))) ∧
      (∀ n ω, Continuous
        (finiteMetricE (circleCoordsInv (Y n ω).2.1))) ∧
      (∀ ω, Tendsto (fun n => Y n ω) atTop (𝓝 (Ylim ω))) := by
  obtain ⟨Ω', mΩ', sbΩ', P', hP', Y, Ylim, hYm, hYlimm,
      hYlaw, hYlimLaw, hConv⟩ :=
    LQGMetric.DFGPS.L217.exists_skorokhod_representation_sb hlim
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
  have hLm : Measurable (fun ω => pairJInv ⊤ (Ylim ω).1) :=
    (measurable_pairJInv ⊤).comp (measurable_fst.comp hYlimm)
  have hMarg : P'.map (fun ω => pairJInv ⊤ (Ylim ω).1) =
      normGFFLaw := by
    have hDecode : Measurable
        (fun q : (CoordJ → ℝ) × RatCoords => pairJInv ⊤ q.1) :=
      (measurable_pairJInv ⊤).comp measurable_fst
    calc
      P'.map (fun ω => pairJInv ⊤ (Ylim ω).1) =
          (P'.map Ylim).map (fun q : (CoordJ → ℝ) × RatCoords =>
            pairJInv ⊤ q.1) :=
        (Measure.map_map hDecode hYlimm).symm
      _ = (ρ : Measure ((CoordJ → ℝ) × RatCoords)).map
          (fun q : (CoordJ → ℝ) × RatCoords => pairJInv ⊤ q.1) := by
        rw [hYlimLaw]
      _ = ((ρ : Measure ((CoordJ → ℝ) × RatCoords)).map Prod.fst).map
          (pairJInv ⊤) := by
        exact (Measure.map_map (measurable_pairJInv ⊤) measurable_fst).symm
      _ = (normGFFLaw.map (pairJ ⊤)).map (pairJInv ⊤) := by rw [hmarg]
      _ = normGFFLaw := by
        rw [Measure.map_map (measurable_pairJInv ⊤) (measurable_pairJ ⊤)]
        calc
          normGFFLaw.map (pairJInv ⊤ ∘ pairJ ⊤) =
              normGFFLaw.map id := Measure.map_congr
                (Filter.Eventually.of_forall fun g => pairJInv_pairJ ⊤ g)
          _ = normGFFLaw := Measure.map_id
  have hNorm : IsNormalizedWholePlaneGFF
      (fun ω => pairJInv ⊤ (Ylim ω).1) P' := by
    letI : IsProbabilityMeasure normGFFLaw :=
      B2.PfeAxioms.normalized_canonical_model.1
    exact normalizedGFF_of_law_eq (id : DistC → DistC)
      B2.PfeAxioms.normalized_canonical_model.2 _ hLm
      (by simpa only [Measure.map_id] using hMarg)
  refine ⟨Ω', mΩ', sbΩ', P', hP', Y, Ylim,
    hYm, hYlimm, hNorm, ?_, ?_, hConv⟩
  · intro n
    have hFinite := joint_finite_pair_law_of_coord_law h hh.1.measurable
      (D n) (hD n) (Y n) (hYm n) (hCoordLaw n)
    exact joint_law_rescaledLFPP_of_finite_law h hh.1.measurable
      (D n) (hD n) (Y n) (hYm n) hFinite ξ (m (ε n))
      (X (ε n)) (fun _ => rfl)
  · intro n ω
    exact continuous_finiteMetricE _

end SupercriticalLQGUniqueness.B2.DG20Lim
