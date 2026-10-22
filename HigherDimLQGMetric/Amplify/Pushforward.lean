import HigherDimLQGMetric.Amplify.TrialPlusLocal
import HigherDimLQGMetric.LGF.Law

/-!
# Pushforward to a standard Borel realization of one white-noise split

For a fixed cutoff, the pair `(fine field, coarse continuous field)` takes
values in a standard Borel product. Pushing its law forward lets the shell
locality theorem apply even though `WhiteNoiseSplit` leaves its sample type
abstract.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory ProbabilityTheory
open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- Whole-space LGF structure transfers along a measurable random variable. -/
theorem amplify_lgf_pushforward
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {T : Ω → Ω'} (hT : Measurable T)
    {h' : Ω' → DistRd d} (hm : Measurable h')
    (hh : IsWholeSpaceLGF (fun ω => h' (T ω)) P) :
    IsWholeSpaceLGF h' (P.map T) where
  measurable := hm
  gaussian := by
    refine ⟨fun I => ?_⟩
    have hX : Measurable fun x : Ω' => I.restrict (fun φ : TestRd0 d => h' x φ.1) :=
      measurable_pi_iff.2 fun i => (measurable_distOn_apply _).comp hm
    have hG := hh.gaussian.hasGaussianLaw I
    refine ⟨hX.aemeasurable, ?_⟩
    rw [Measure.map_map hX hT]
    exact hG.isGaussian_map
  centered := fun φ => by
    have hme : Measurable (fun x : Ω' => h' x φ.1) :=
      (measurable_distOn_apply φ.1).comp hm
    change ∫ x : Ω', h' x φ.1 ∂(P.map T) = 0
    rw [integral_map hT.aemeasurable hme.aestronglyMeasurable]
    exact hh.centered φ
  covariance_eq := fun φ ψ => by
    have hmeφ : Measurable (fun x : Ω' => h' x φ.1) :=
      (measurable_distOn_apply φ.1).comp hm
    have hmeψ : Measurable (fun x : Ω' => h' x ψ.1) :=
      (measurable_distOn_apply ψ.1).comp hm
    change cov[fun x : Ω' => h' x φ.1, fun x : Ω' => h' x ψ.1; P.map T] = _
    rw [covariance_map hmeφ.aestronglyMeasurable hmeψ.aestronglyMeasurable hT.aemeasurable]
    exact hh.covariance_eq φ ψ

/-- The trial event for a fine field is shell-measurable whenever adding a
measurable continuous coarse field gives a whole-space LGF. -/
theorem amplify_aeEventIn_trialEvent_of_split
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Ω → DistRd d) (g : Ω → C(Rd d, ℝ))
    (hF : Measurable F) (hg : Measurable g)
    (hH : IsWholeSpaceLGF (fun ω => F ω + ofCont (g ω)) P)
    {ξ Q : ℝ} {D Dt : DistRd d → ContMetric d}
    (hD : IsSharpWeakExpMetric d ξ Q D)
    (hDt : IsSharpWeakExpMetric d ξ Q Dt)
    (hd : 2 ≤ d) (cs c1 ℓ δ : ℝ) {s : ℝ} (hs : 0 < s) (w : Rd d) :
    AEEventIn P (fieldSigma0 F (ann w (s / 2) (5 * s)))
      (F ⁻¹' TrialEvent D Dt ξ Q cs c1 ℓ δ s w) := by
  let T : Ω → DistRd d × C(Rd d, ℝ) := fun ω => (F ω, -g ω)
  have hT : Measurable T := hF.prodMk hg.neg
  let P' : Measure (DistRd d × C(Rd d, ℝ)) := P.map T
  have hH' : IsWholeSpaceLGF
      (fun q : DistRd d × C(Rd d, ℝ) => q.1 - ofCont q.2) P' := by
    have hpair : IsWholeSpaceLGF
        (fun ω => (fun q : DistRd d × C(Rd d, ℝ) => q.1 - ofCont q.2) (T ω)) P := by
      convert hH using 1
      funext ω
      simp only [T, ofCont_neg, sub_neg_eq_add]
    exact amplify_lgf_pushforward hT (measurable_fst.sub (Measurable.ofCont measurable_snd)) hpair
  have hFine : IsLGFPlusCont (fun q : DistRd d × C(Rd d, ℝ) => q.1) P' :=
    ⟨measurable_fst, fun q => q.2, measurable_snd, hH'⟩
  have hloc := amplify_aeEventIn_trialEvent_plus P'
    (fun q : DistRd d × C(Rd d, ℝ) => q.1) hFine hD hDt hd cs c1 ℓ δ hs w
  obtain ⟨A, hAm, hAE⟩ := hloc
  have hA : MeasurableSet[fieldSigma0 F (ann w (s / 2) (5 * s))] (T ⁻¹' A) := by
    have heq : fieldSigma0 F (ann w (s / 2) (5 * s)) =
        MeasurableSpace.comap T
          (fieldSigma0 (fun q : DistRd d × C(Rd d, ℝ) => q.1)
            (ann w (s / 2) (5 * s))) := by
      simp only [fieldSigma0, MeasurableSpace.comap_comp]
      rfl
    rw [heq]
    exact MeasurableSpace.measurableSet_comap.2 ⟨A, hAm, rfl⟩
  refine ⟨T ⁻¹' A, hA, ?_⟩
  have hpre := ae_of_ae_map hT.aemeasurable hAE
  change (∀ᵐ ω ∂P, (F ω ∈ TrialEvent D Dt ξ Q cs c1 ℓ δ s w) =
    (T ω ∈ A))
  exact hpre

end HigherDimLQGMetric
