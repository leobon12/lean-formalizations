import HigherDimLQGMetric.Markov.Glue

/-! The continuous exterior harmonic projection process. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric TopologicalSpace
open HigherDimLFPP (Rd)

namespace HigherDimLQGMetric

variable {d : ℕ} {Ω : Type} [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistRd d}

/-- The exterior point Riesz vectors admit a single continuous version on the entire exterior
open set, with measurable samples at every point. -/
theorem markov_exists_pointVersion (hd : 1 ≤ d) (hh : IsWholeSpaceLGF h P)
    (V : Opens (Rd d)) (hVb : Bornology.IsBounded (V : Set (Rd d)))
    {ρ : TestRd d} (hρ : ∫ y, ρ y = 1)
    (hρV : tsupport (ρ : Rd d → ℝ) ⊆ V) :
    ∃ Y : Ω → Rd d → ℝ,
      (∀ ω, ContinuousOn (Y ω) (extOpen V)) ∧ Measurable Y ∧
      ∀ x (hx : x ∈ extOpen V),
        (fun ω => Y ω x) =ᵐ[P]
          (markovPointVec hd hh V hVb hρ hρV x hx : Ω → ℝ) := by
  classical
  let Z : Rd d → Ω → ℝ := fun x ω =>
    if hx : x ∈ extOpen V then
      (markovPointVec hd hh V hVb hρ hρV x hx : Ω → ℝ) ω
    else 0
  have hLoc : ∀ x : extOpen V, ∃ r : ℝ, 0 < r ∧ ball (x : Rd d) r ⊆ extOpen V ∧
      ∃ H : Rd d → Ω → ℝ,
        (∀ ω, ContinuousOn (fun y => H y ω) (ball (x : Rd d) r)) ∧
        (∀ y, Measurable (H y)) ∧
        (∀ y ∈ ball (x : Rd d) r, (fun ω => H y ω) =ᵐ[P] Z y) := by
    intro x
    obtain ⟨r, hr, hball, H, hHc, hHm, hHa⟩ :=
      markov_exists_local_pointVersion hd hh V hVb hρ hρV x x.2
    refine ⟨r, hr, hball, H, hHc, hHm, ?_⟩
    intro y hy
    have hyo : y ∈ extOpen V := hball hy
    simpa only [Z, dite_eq_left hyo] using hHa y hy hyo
  obtain ⟨Y, hYc, hYm, hYae⟩ :=
    markov_glue_local_versions P (extOpen V) Z hLoc
  refine ⟨Y, hYc, hYm, ?_⟩
  intro x hx
  simpa only [Z, dite_eq_left hx] using hYae x hx

end HigherDimLQGMetric
