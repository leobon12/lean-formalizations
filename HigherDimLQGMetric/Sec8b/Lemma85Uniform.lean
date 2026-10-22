import HigherDimLQGMetric.Sec8b.Lemma85Shifted
import HigherDimLQGMetric.Sec8b.Lemma84Uniform

/-! Countable simultaneous version of the shifted-label reduction. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory
open HigherDimLFPP (Rd)

variable {d : ℕ}

theorem s7b_shifted_fav_sites_ae_all_indexed
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsWholeSpaceLGF h P)
    (hd : 3 ≤ d)
    {ξ Q cs Cs R : ℝ}
    {D Dt : DistRd d → ContMetric d}
    (hD : IsSharpWeakExpMetric d ξ Q D)
    (hDt : IsSharpWeakExpMetric d ξ Q Dt)
    (T : Sec8TrapData d ξ cs Cs D Dt)
    (hR : 0 < R) (x y : Rd d) :
    ∀ᵐ ω ∂P,
      ∀ j i : ℤ, ∀ colour : Fin d → ℤ,
      ∀ W : Finset ((Fin d → ℤ) × ℕ),
        let r := (64 : ℝ) ^ j
        let q := (2 : ℝ) ^ i
        let Z := s7b_indexSites r W
        3 * r ≤ R →
        IsSec8LabeledSet d T.J r R x y colour Z →
        addFun (h ω) (F_Z T.f r Z) ∈
          FavEvent D Dt ξ Q Cs q R r T.b T.J T.N T.V T.f x y Z →
        ∀ site ∈ Z, S7bVeryGood T Q q R r x y (h ω) site := by
  classical
  apply ae_all_iff.mpr; intro j
  apply ae_all_iff.mpr; intro i
  apply ae_all_iff.mpr; intro colour
  apply ae_all_iff.mpr; intro W
  dsimp only
  by_cases hinputs : 3 * (64 : ℝ) ^ j ≤ R ∧
      IsSec8LabeledSet d T.J ((64 : ℝ) ^ j) R x y colour
        (s7b_indexSites ((64 : ℝ) ^ j) W)
  · obtain ⟨hrR, hZ⟩ := hinputs
    filter_upwards [s7b_shifted_fav_sites_ae P h hh hd hD hDt T
      (show 0 < (64 : ℝ) ^ j by positivity) hR hrR x y colour _ hZ]
      with ω hω
    exact fun _ _ => hω
  · exact Filter.Eventually.of_forall (fun _ hrR hZ _ =>
      False.elim (hinputs ⟨hrR, hZ⟩))

/-- The macroscopic normalizer is simultaneously unchanged by every finite
same-colour perturbation at all lattice scales. -/
theorem s7b_shifted_macro_ae_all_indexed
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsWholeSpaceLGF h P)
    (hd : 3 ≤ d)
    {ξ Q cs Cs R : ℝ}
    {D Dt : DistRd d → ContMetric d}
    (hD : IsSharpWeakExpMetric d ξ Q D)
    (hDt : IsSharpWeakExpMetric d ξ Q Dt)
    (T : Sec8TrapData d ξ cs Cs D Dt)
    (hR : 0 < R) (x y : Rd d) :
    ∀ᵐ ω ∂P,
      ∀ j : ℤ, ∀ colour : Fin d → ℤ,
      ∀ W : Finset ((Fin d → ℤ) × ℕ),
        let r := (64 : ℝ) ^ j
        let Z := s7b_indexSites r W
        3 * r ≤ R →
        IsSec8LabeledSet d T.J r R x y colour Z →
        macroS ξ Q (addFun (h ω) (F_Z T.f r Z)) R =
          macroS ξ Q (h ω) R := by
  classical
  apply ae_all_iff.mpr; intro j
  apply ae_all_iff.mpr; intro colour
  apply ae_all_iff.mpr; intro W
  dsimp only
  by_cases hinputs : 3 * (64 : ℝ) ^ j ≤ R ∧
      IsSec8LabeledSet d T.J ((64 : ℝ) ^ j) R x y colour
        (s7b_indexSites ((64 : ℝ) ^ j) W)
  · obtain ⟨hrR, hZ⟩ := hinputs
    have hsupp : ∀ t < T.J,
        tsupport (T.f t) ⊆ ann (0 : Rd d) 1 3 :=
      fun t ht => (T.bumps t ht).2.2.1
    filter_upwards [lemma82 P h hd hh hD hDt hsupp
      (show 0 < (64 : ℝ) ^ j by positivity) hR hrR hZ] with ω hω
    exact fun _ _ => hω.1
  · exact Filter.Eventually.of_forall (fun _ hrR hZ =>
      False.elim (hinputs ⟨hrR, hZ⟩))

end HigherDimLQGMetric
