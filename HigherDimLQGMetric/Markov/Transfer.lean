import HigherDimLQGMetric.Markov.Meas

/-!
# Transfer of the Gaussian split to distribution-valued random variables

The cylinder sigma algebra of `DistOn O` has countable `pairJ` coordinates. Pairing-wise almost
sure identities therefore transfer independence without taking an uncountable intersection of
null sets.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped RealInnerProductSpace

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistRd d}

/-- A distribution whose pairings equal the orthogonal residual is independent of the interior
restriction. The countable `pairJ` coordinates avoid an invalid uncountable a.e. intersection. -/
theorem markov_indep_residual_dist (hh : IsWholeSpaceLGF h P) (V : Opens (Rd d))
    {ρ : TestRd d} (hρ : ∫ x, ρ x = 1)
    (R : Ω → DistOn (extOpen V)) (_hR : Measurable R)
    (hpair : ∀ ψ : TestOn (extOpen V),
      (fun ω => R ω ψ) =ᵐ[P] (fun ω => (markovResidualVec hh V hρ ψ : Ω → ℝ) ω)) :
    Indep (MeasurableSpace.comap R inferInstance)
      (fieldSigmaRd (fun ω => recenter ρ (h ω)) V) P := by
  let O := extOpen V
  let W : CoordJ → Lp ℝ 2 P := fun c => markovResidualVec hh V hρ (comb O c)
  have horth (c : CoordJ) (φ : TestOn V) :
      ⟪W c, markovInsideVec hh V hρ φ⟫ = 0 :=
    markov_residual_inner_inside hh V hρ (comb O c) φ
  have hind : IndepFun (fun ω (c : CoordJ) => (W c : Ω → ℝ) ω)
      (fun ω (φ : TestOn V) => markovPair h (markovInsideTest V hρ φ) ω) P :=
    LQGMetric.MarkovGauss.indepFun_of_inner_eq_zero hh.gaussian hh.centered
      (markov_memLp_pair hh) W
      (fun c => markov_residual_mem_global hh V hρ (comb O c))
      (markovInsideTest V hρ) horth
  have hae : (fun ω (c : CoordJ) => R ω (comb O c)) =ᵐ[P]
      (fun ω (c : CoordJ) => (W c : Ω → ℝ) ω) := by
    filter_upwards [ae_all_iff.mpr (fun c : CoordJ => hpair (comb O c))] with ω hω
    funext c
    exact hω c
  have he : (fun ω (φ : TestOn V) => markovPair h (markovInsideTest V hρ φ) ω) =
      (fun ω (φ : TestOn V) => restrictTo V (recenter ρ (h ω)) φ) := by
    funext ω φ
    rw [restrictTo_apply, recenter_apply]
    rfl
  have hind' := (IndepFun_iff_Indep _ _ P).mp
    (hind.congr hae.symm Filter.EventuallyEq.rfl)
  rw [he] at hind'
  have hRsig : MeasurableSpace.comap R (inferInstance : MeasurableSpace (DistOn O)) =
      MeasurableSpace.comap (fun ω => pairJ O (R ω)) MeasurableSpace.pi := by
    rw [show (inferInstance : MeasurableSpace (DistOn O)) = DistOn.measurableSpace O from rfl,
      distOn_measurableSpace_eq_comap_pairJ, MeasurableSpace.comap_comp]
    rfl
  have hVsig : fieldSigmaRd (fun ω => recenter ρ (h ω)) V =
      MeasurableSpace.comap
        (fun ω (φ : TestOn V) => restrictTo V (recenter ρ (h ω)) φ) MeasurableSpace.pi := by
    rw [fieldSigmaRd, DistOn.measurableSpace, MeasurableSpace.comap_comp]
    rfl
  rw [hRsig, hVsig]
  exact hind'

end HigherDimLQGMetric
