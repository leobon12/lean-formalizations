import HigherDimLQGMetric.Locality.MarkovVersions

/-! Measurable Markov cutoff and residual versions for a witness already
chosen from `DMarkovRd`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open LQGMetric.GM.Bilip

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l7a_markov_fixed_measurable_versions {d : ℕ}
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsWholeSpaceLGF h P)
    (V : TopologicalSpace.Opens (Rd d)) (z₀ : Rd d) (ρ : ℝ)
    (H : Ω → Rd d → ℝ)
    (hHc : ∀ ω, ContinuousOn (H ω) (extOpen V))
    (hHm : ∃ G : Ω → Rd d → ℝ,
      Measurable[fieldSigmaRd
        (fun ω => addConst (h ω) (-sphereAvg (h ω) ρ z₀)) V] G ∧
      H =ᵐ[P] G)
    (hind : Indep (MeasurableSpace.comap
      (fun ω => restrictTo (extOpen V)
        (addConst (h ω) (-sphereAvg (h ω) ρ z₀)) -
          ofFunOn (extOpen V) (H ω)) inferInstance)
      (fieldSigmaRd (fun ω => addConst (h ω)
        (-sphereAvg (h ω) ρ z₀)) V) P)
    (φ : C(Rd d, ℝ)) (hφsup : tsupport φ ⊆ extOpen V)
    (hφc : HasCompactSupport φ) :
    let g : Ω → DistRd d := fun ω =>
      addConst (h ω) (-sphereAvg (h ω) ρ z₀)
    ∃ K : Set (Rd d), IsCompact K ∧
      ∃ F : Ω → C(Rd d, ℝ),
        Measurable[fieldSigmaRd g V] F ∧
        (∀ ω, tsupport (F ω) ⊆ K) ∧
        (∀ ω, ∃ B : ℝ, ∀ x, |F ω x| ≤ B) ∧
        (fun ω => (⟨fun x => φ x * H ω x,
          l7a_continuous_cutoffH (extOpen V).isOpen φ (H ω)
            (hHc ω) hφsup⟩ : C(Rd d, ℝ))) =ᵐ[P] F ∧
        ∃ R : Ω → DistOn (extOpen V),
          Measurable[fullSigmaRd h] R ∧ Measurable[mΩ] R ∧
          (fun ω => restrictTo (extOpen V) (g ω) -
            ofFunOn (extOpen V) (H ω)) =ᵐ[P] R ∧
          Indep (MeasurableSpace.comap R inferInstance)
            (fieldSigmaRd g V) P ∧
          ∃ Φ : (CoordJ → ℝ) → C(Rd d, ℝ) × DistOn (extOpen V),
            Measurable Φ ∧
            (fun ω => (F ω, R ω)) = Φ ∘
              (fun ω => pairJ ⊤ (h ω)) := by
  letI : MeasurableSpace Ω := mΩ
  dsimp only
  let g : Ω → DistRd d := fun ω =>
    addConst (h ω) (-sphereAvg (h ω) ρ z₀)
  have hg : Measurable g :=
    Measurable.addConst hh.measurable
      (((measurable_sphereAvg_left ρ z₀).comp hh.measurable).neg)
  have hfull : fullSigmaRd h ≤ mΩ := hh.measurable.comap_le
  have hgfield : Measurable[fullSigmaRd h] g := by
    letI : MeasurableSpace Ω := fullSigmaRd h
    exact Measurable.addConst (comap_measurable h)
      (((measurable_sphereAvg_left ρ z₀).comp (comap_measurable h)).neg)
  have hfieldfull : fieldSigmaRd g V ≤ fullSigmaRd h :=
    ((measurable_restrictTo V).comp hgfield).comap_le
  obtain ⟨G, hGm, hHG⟩ := hHm
  obtain ⟨K, hK, F, hFm, hFsup, hFb, hFae⟩ :=
    l7a_exists_bounded_measurable_cutoffH_version P (fieldSigmaRd g V)
      (extOpen V).isOpen φ hφsup hφc H G hHc hGm hHG
  obtain ⟨R, hRmfield, hRae⟩ :=
    l7a_exists_residual_version_in_sigma P (fullSigmaRd h) g hgfield
      (extOpen V) (fieldSigmaRd g V) hfieldfull H G hHc hGm hHG
  have hRm : Measurable[mΩ] R := hRmfield.mono hfull le_rfl
  have hRle : MeasurableSpace.comap R inferInstance ≤
      aeClosure P (MeasurableSpace.comap
        (fun ω => restrictTo (extOpen V) (g ω) -
          ofFunOn (extOpen V) (H ω)) inferInstance) :=
    LQGMetric.DFGPS.L219.comap_le_aeClosure_of_ae_eq
      (comap_measurable _) hRae.symm
  have hind' : Indep (MeasurableSpace.comap R inferInstance)
      (fieldSigmaRd g V) P :=
    LQGMetric.DFGPS.L217.indep_of_le_aeClosure hind hRle
      (le_aeClosure _)
  have hFfield : Measurable[fullSigmaRd h] F :=
    hFm.mono hfieldfull le_rfl
  obtain ⟨Φ, hΦm, hΦeq⟩ := l7a_factor_field_observation h
    (fun ω => (F ω, R ω)) (hFfield.prodMk hRmfield)
  exact ⟨K, hK, F, hFm, hFsup, hFb, hFae, R, hRmfield,
    hRm, hRae, hind', Φ, hΦm, hΦeq⟩

end HigherDimLQGMetric
