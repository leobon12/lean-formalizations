import SupercriticalLQGUniqueness.B2.DG20Lim.Section51
import LQGMetric.LFPP.Length
import LQGMetric.Papers.GM.S1.StrongWeak
import LQGMetric.Papers.LM.C1_8Len

 


set_option autoImplicit false
set_option linter.style.haveILetI false
noncomputable section

open MeasureTheory LQGMetric LQGMetric.LFPP

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem isLength_normalizedContLFPP (ξ : ℝ) (a : Set.Ioi (0 : ℝ))
    (φ : C(ℂ, ℝ)) : (normalizedContLFPP ξ a φ).IsLength := by
  exact ContMetric.isLength_smulPos (inv_pos.mpr a.property)
    (isLength_lfppContMetric φ.continuous)

 

theorem ae_isLength_of_finite_pair_law
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    (h : Ω → DistC) (hh : Measurable h)
    (D : Ω → ContMetric) (hD : AEMeasurable D P)
    (hLen : ∀ᵐ ω ∂P, (D ω).IsLength)
    (Y : Ω' → (CoordJ → ℝ) × RatCoords) (hY : Measurable Y)
    (hLaw : P'.map (fun ω => decodeFinitePair (Y ω)) =
      P.map (fun ω => (h ω, D ω))) :
    ∀ᵐ ω ∂P', (circleCoordsInv (Y ω).2.1).IsLength := by
  let D' : Ω' → ContMetric := fun ω => circleCoordsInv (Y ω).2.1
  have hD' : Measurable D' :=
    measurable_circleCoordsInv.comp (measurable_fst.comp (measurable_snd.comp hY))
  have hSource : AEMeasurable (fun ω => (h ω, D ω)) P :=
    hh.aemeasurable.prodMk hD
  have hTarget : Measurable (fun ω => decodeFinitePair (Y ω)) :=
    measurable_decodeFinitePair.comp hY
  have hMarg : P'.map D' = P.map D := by
    calc
      P'.map D' = (P'.map (fun ω => decodeFinitePair (Y ω))).map Prod.snd := by
        exact (Measure.map_map measurable_snd hTarget).symm
      _ = (P.map (fun ω => (h ω, D ω))).map Prod.snd := hLaw ▸ rfl
      _ = P.map D := by
        exact AEMeasurable.map_map_of_aemeasurable
          measurable_snd.aemeasurable hSource
  letI : IsProbabilityMeasure (P.map D) :=
    (Measure.isProbabilityMeasure_map_iff hD).2 inferInstance
  obtain ⟨M, hMS, hM, hMae⟩ :=
    (LQGMetric.LM.c18_uMeasurableSet_isLength (P.map D) inferInstance).exists_measurable_subset_ae_eq
  have hDM : ∀ᵐ ω ∂P, D ω ∈ M := by
    have hDiff : (P.map D) ({d : ContMetric | d.IsLength} \ M) = 0 :=
      ae_le_set.1 hMae.symm.le
    obtain ⟨N, hSN, hN, hN0⟩ := exists_measurable_superset_of_null hDiff
    have hN' : ∀ᵐ ω ∂P, D ω ∉ N := by
      rw [Measure.map_apply_of_aemeasurable hD hN] at hN0
      exact measure_eq_zero_iff_ae_notMem.1 hN0
    filter_upwards [hLen, hN'] with ω hω hωN
    by_contra hωM
    exact hωN (hSN ⟨hω, hωM⟩)
  have hDM' : ∀ᵐ d ∂P.map D, d ∈ M :=
    (ae_map_iff hD hM).2 hDM
  have hDM'' : ∀ᵐ d ∂P'.map D', d ∈ M := by rwa [hMarg]
  exact (ae_map_iff hD'.aemeasurable hM).1 hDM'' |>.mono
    (fun ω hω => hMS hω)

end SupercriticalLQGUniqueness.B2.DG20Lim
