import HigherDimLQGMetric.Markov.Covariance

/-! The projected exterior pairing is the Bochner integral of exterior point vectors. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric TopologicalSpace
open scoped RealInnerProductSpace
open HigherDimLFPP (Rd)

namespace HigherDimLQGMetric

variable {d : ℕ} {Ω : Type} [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistRd d}

/-- The integral of interior point representatives lies in the closed interior Gaussian space. -/
theorem markov_integral_pointVec_mem (hd : 1 ≤ d) (hh : IsWholeSpaceLGF h P)
    (V : Opens (Rd d)) (hVb : Bornology.IsBounded (V : Set (Rd d)))
    {ρ : TestRd d} (hρ : ∫ y, ρ y = 1)
    (hρV : tsupport (ρ : Rd d → ℝ) ⊆ V)
    (ψ : TestOn (extOpen V)) :
    (∫ x, (testIncl (extOpen V) ψ) x •
      markovExteriorVec hd hh V hVb hρ hρV x) ∈ markovInsideSpace hh V hρ := by
  let K := markovInsideSpace hh V hρ
  let f : Rd d → Lp ℝ 2 P := fun x =>
    (testIncl (extOpen V) ψ) x • markovExteriorVec hd hh V hVb hρ hρV x
  have hf : Integrable f := markov_integrable_weightedExteriorVec hd hh V hVb hρ hρV ψ
  have hmem (x : Rd d) : f x ∈ K := by
    by_cases hx : x ∈ extOpen V
    · exact Submodule.smul_mem _ _ (by
        simpa only [f, markovExteriorVec_eq hd hh V hVb hρ hρV hx] using
          markovPointVec_mem hd hh V hVb hρ hρV x hx)
    · have hE : markovExteriorVec hd hh V hVb hρ hρV x = 0 := by
        simp [markovExteriorVec, hx]
      simp [f, hE, K]
  apply K.starProjection_eq_self_iff.mp
  calc
    K.starProjection (∫ x, f x) = ∫ x, K.starProjection (f x) :=
      (K.starProjection.integral_comp_comm hf).symm
    _ = ∫ x, f x := by
      apply integral_congr_ae
      exact ae_of_all _ fun x => K.starProjection_eq_self_iff.mpr (hmem x)

/-- Pairing the Bochner integral with one interior generator gives the integrated pointwise
logarithmic covariance. -/
theorem markov_integral_pointVec_inner (hd : 1 ≤ d) (hh : IsWholeSpaceLGF h P)
    (V : Opens (Rd d)) (hVb : Bornology.IsBounded (V : Set (Rd d)))
    {ρ : TestRd d} (hρ : ∫ y, ρ y = 1)
    (hρV : tsupport (ρ : Rd d → ℝ) ⊆ V)
    (ψ : TestOn (extOpen V)) (φ : TestOn V) :
    ⟪(∫ x, (testIncl (extOpen V) ψ) x •
      markovExteriorVec hd hh V hVb hρ hρV x),
      markovInsideVec hh V hρ φ⟫ =
      logCovRd (markovInsideTest (extOpen V) hρ ψ).1
        (markovInsideTest V hρ φ).1 := by
  let w : Rd d → ℝ := testIncl (extOpen V) ψ
  let E : Rd d → Lp ℝ 2 P := markovExteriorVec hd hh V hVb hρ hρV
  let c : Lp ℝ 2 P := markovInsideVec hh V hρ φ
  have hf : Integrable (fun x => w x • E x) :=
    markov_integrable_weightedExteriorVec hd hh V hVb hρ hρV ψ
  have hwV : tsupport w ⊆ extOpen V := by
    change tsupport ((testIncl (extOpen V) ψ : TestRd d) : Rd d → ℝ) ⊆ extOpen V
    rw [coe_testIncl]
    exact ψ.tsupport_subset
  have hdet := markov_logCovRd_recenter_outer hd
    (testIncl (extOpen V) ψ) ρ (markovInsideTest V hρ φ).1
  change logCovRd (markovInsideTest (extOpen V) hρ ψ).1
      (markovInsideTest V hρ φ).1 =
    ∫ x, w x * (∫ y,
      (-Real.log ‖x - y‖ - markovLogPot ρ y) *
        (markovInsideTest V hρ φ).1 y) at hdet
  rw [hdet]
  change ⟪∫ x, w x • E x, c⟫ =
    ∫ x, w x * (∫ y,
      (-Real.log ‖x - y‖ - markovLogPot ρ y) *
        (markovInsideTest V hρ φ).1 y)
  calc
    ⟪∫ x, w x • E x, c⟫ = ∫ x, ⟪c, w x • E x⟫ := by
      rw [real_inner_comm]
      exact (integral_inner hf c).symm
    _ = ∫ x, w x * (∫ y,
        (-Real.log ‖x - y‖ - markovLogPot ρ y) *
          (markovInsideTest V hρ φ).1 y) := by
      apply integral_congr_ae
      refine ae_of_all _ fun x => ?_
      by_cases hx : x ∈ extOpen V
      · change ⟪markovInsideVec hh V hρ φ,
            (testIncl (extOpen V) ψ) x •
              markovExteriorVec hd hh V hVb hρ hρV x⟫ =
          (testIncl (extOpen V) ψ) x * (∫ y,
            (-Real.log ‖x - y‖ - markovLogPot ρ y) *
              (markovInsideTest V hρ φ).1 y)
        rw [markovExteriorVec_eq hd hh V hVb hρ hρV hx]
        rw [real_inner_smul_right, real_inner_comm,
          markovPointVec_inner hd hh V hVb hρ hρV x hx φ]
      · have hw0 : w x = 0 :=
          image_eq_zero_of_notMem_tsupport (fun ht => hx (hwV ht))
        simp [hw0]

/-- **Projected-pairing identity**: the orthogonal projection of an exterior LGF pairing equals
the integral of the point Riesz representatives. -/
theorem markov_projOutside_eq_integral_pointVec (hd : 1 ≤ d)
    (hh : IsWholeSpaceLGF h P)
    (V : Opens (Rd d)) (hVb : Bornology.IsBounded (V : Set (Rd d)))
    {ρ : TestRd d} (hρ : ∫ y, ρ y = 1)
    (hρV : tsupport (ρ : Rd d → ℝ) ⊆ V)
    (ψ : TestOn (extOpen V)) :
    (markovInsideSpace hh V hρ).starProjection
      (markovOutsideVec hh (extOpen V) hρ ψ) =
      ∫ x, (testIncl (extOpen V) ψ) x •
        markovExteriorVec hd hh V hVb hρ hρV x := by
  let K := markovInsideSpace hh V hρ
  let Z : Lp ℝ 2 P := ∫ x, (testIncl (extOpen V) ψ) x •
    markovExteriorVec hd hh V hVb hρ hρV x
  have hZmem : Z ∈ K := markov_integral_pointVec_mem hd hh V hVb hρ hρV ψ
  have hPmem : K.starProjection (markovOutsideVec hh (extOpen V) hρ ψ) ∈ K :=
    K.starProjection_apply_mem _
  apply markov_insideVec_ext hh V hρ hPmem hZmem
  intro φ
  have horth := K.starProjection_inner_eq_zero
    (markovOutsideVec hh (extOpen V) hρ ψ)
    (markovInsideVec hh V hρ φ) (markov_insideVec_mem hh V hρ φ)
  rw [inner_sub_left] at horth
  have hproj : ⟪K.starProjection (markovOutsideVec hh (extOpen V) hρ ψ),
      markovInsideVec hh V hρ φ⟫ =
      ⟪markovOutsideVec hh (extOpen V) hρ ψ,
        markovInsideVec hh V hρ φ⟫ :=
    (sub_eq_zero.mp horth).symm
  rw [hproj]
  change ⟪(markov_memLp_pair hh (markovInsideTest (extOpen V) hρ ψ)).toLp
      (markovPair h (markovInsideTest (extOpen V) hρ ψ)),
    (markov_memLp_pair hh (markovInsideTest V hρ φ)).toLp
      (markovPair h (markovInsideTest V hρ φ))⟫ = _
  rw [markov_inner_pair_eq_logCovRd hh]
  exact (markov_integral_pointVec_inner hd hh V hVb hρ hρV ψ φ).symm

end HigherDimLQGMetric
