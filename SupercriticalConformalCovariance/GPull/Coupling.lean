import SupercriticalConformalCovariance.GPull.GreenianMarkov
import SmallGammaGeodesics.CC.Extension
import LQGMetric.Field.StandardBorelRange
import LQGMetric.Field.ZeroBoundaryLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set TopologicalSpace
open LQGMetric SupercriticalConformalCovariance

namespace SupercriticalConformalCovariance.GPull

/-- Coupling a given zero-boundary GFF with a whole-plane reference field so that
the reference Markov zero part equals it on `U`. This is a general version of the
conditional-distribution construction in `SmallGammaGeodesics.CC.Extension`. -/
theorem exists_reference_coupling
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {U : Opens ℂ} {z : Ω → DistOn U}
    (hz : IsZeroBoundaryGFF U z P) (hU : IsGreenian U) :
    ∃ (P' : Measure (Ω × DistC)) (F : DistC → DistC) (H : DistC → ℂ → ℝ),
      IsProbabilityMeasure P' ∧
      MeasurePreserving (Prod.fst : Ω × DistC → Ω) P' P ∧
      IsWholePlaneGFF (fun p : Ω × DistC => p.2) P' ∧
      Measurable F ∧
      Measurable (fun p : DistC × ℂ => H p.1 p.2) ∧
      (∀ᵐ p ∂P', Continuous fun x : U => H p.2 x) ∧
      (∀ᵐ p ∂P', restrictTo U (F p.2) = z p.1) ∧
      (∀ᵐ p ∂P', ∀ ψ : TestOn U,
        restrictTo U (p.2 - F p.2) ψ = ∫ x, H p.2 x * ψ x) := by
  obtain ⟨Ω₀, mΩ₀, P₀, g, hP₀, hg⟩ := GFFExist.exists_wholePlaneGFF
  let ν : Measure DistC := P₀.map g
  haveI : IsProbabilityMeasure ν := by dsimp [ν]; infer_instance
  have hid : IsWholePlaneGFF (id : DistC → DistC) ν := by
    apply DFGPS.L217.isWholePlaneGFF_of_map_eq measurable_id hg
    simp [ν]
  obtain ⟨F, H, hFm, _, _, hzr, _, hHm, hHpair, _⟩ :=
    SupercriticalConformalCovariance.Markov.exists_generated_joint_markov_general hid hU
  let r : DistC → DistOn U := fun T => restrictTo U (F T)
  have hrm : Measurable r := (measurable_restrictTo U).comp hFm
  have hrz : IsZeroBoundaryGFF U r ν := hzr
  have hlaw : P.map z = ν.map r := hz.map_eq hrz
  let κ : Kernel (DistOn U) DistC := condDistrib id r ν
  let P' : Measure (Ω × DistC) := P ⊗ₘ κ.comap z hz.measurable
  have hpairlaw : P'.map (fun p => (z p.1, p.2)) =
      ν.map (fun T => (r T, T)) := by
    dsimp only [P']
    rw [SmallGammaGeodesics.CC.map_compProd_comap P κ hz.measurable,
      hlaw, compProd_map_condDistrib hrm.aemeasurable aemeasurable_id]
    rfl
  have hsnd : P'.map Prod.snd = ν := by
    have hpm : Measurable (fun p : Ω × DistC => (z p.1, p.2)) :=
      (hz.measurable.comp measurable_fst).prodMk measurable_snd
    have hrid : Measurable (fun T : DistC => (r T, T)) :=
      hrm.prodMk measurable_id
    calc
      P'.map Prod.snd =
          (P'.map (fun p => (z p.1, p.2))).map Prod.snd := by
            calc
              P'.map Prod.snd = P'.map (Prod.snd ∘ fun p => (z p.1, p.2)) := rfl
              _ = (P'.map (fun p => (z p.1, p.2))).map Prod.snd :=
                (Measure.map_map measurable_snd hpm).symm
      _ = (ν.map fun T => (r T, T)).map Prod.snd := by rw [hpairlaw]
      _ = ν := by
        rw [Measure.map_map measurable_snd hrid]
        exact Measure.map_id
  have hfst : MeasurePreserving (Prod.fst : Ω × DistC → Ω) P' P :=
    ⟨measurable_fst, Measure.fst_compProd P _⟩
  have hsndG : IsWholePlaneGFF (fun p : Ω × DistC => p.2) P' := by
    apply DFGPS.L217.isWholePlaneGFF_of_map_eq measurable_snd hid
    simpa only [Measure.map_id] using hsnd
  have heq : ∀ᵐ p ∂P', r p.2 = z p.1 := by
    let D : Set ((DistOn U) × DistC) := {q | r q.2 = q.1}
    have hDm : MeasurableSet D :=
      measurableSet_eq_fun (hrm.comp measurable_snd) measurable_fst
    have hfull : ∀ᵐ q ∂(ν.map fun T => (r T, T)), q ∈ D := by
      exact ae_map_iff (hrm.prodMk measurable_id).aemeasurable hDm |>.2
        (ae_of_all _ fun T => rfl)
    have hpre := (ae_map_iff
      ((hz.measurable.comp measurable_fst).prodMk measurable_snd).aemeasurable hDm).1
      (hpairlaw.symm ▸ hfull)
    exact hpre
  refine ⟨P', F, H, inferInstance, hfst, hsndG, hFm, hHm, ?_, ?_, ?_⟩
  · have href : ∀ᵐ T ∂ν, Continuous fun x : U => H T x := by
      filter_upwards [hHpair] with T hT
      exact continuousOn_iff_continuous_domRestrict.mp hT.1.continuousOn
    have href' : ∀ᵐ T ∂P'.map (Prod.snd : Ω × DistC → DistC),
        Continuous fun x : U => H T x := by rwa [hsnd]
    exact ae_of_ae_map measurable_snd.aemeasurable href'
  · exact heq
  · have href : ∀ᵐ T ∂ν, ∀ ψ : TestOn U,
        restrictTo U (T - F T) ψ = ∫ x, H T x * ψ x :=
      hHpair.mono fun T hT => hT.2
    have href' : ∀ᵐ T ∂P'.map (Prod.snd : Ω × DistC → DistC), ∀ ψ : TestOn U,
        restrictTo U (T - F T) ψ = ∫ x, H T x * ψ x := by
      rwa [hsnd]
    exact ae_of_ae_map measurable_snd.aemeasurable href'


end SupercriticalConformalCovariance.GPull
