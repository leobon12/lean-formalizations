import HigherDimLQGMetric.Markov.StochId

/-! A continuous exterior Gaussian version integrates to the projected pairing. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric TopologicalSpace Filter
open scoped RealInnerProductSpace Topology
open HigherDimLFPP (Rd)

namespace HigherDimLQGMetric

variable {d : ℕ} {Ω : Type} [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistRd d}

/-- Stochastic Fubini identifies test integration of the continuous exterior version with
the orthogonal projection of the exterior recentered LGF pairing. -/
theorem markov_integral_version_ae_proj (hd : 1 ≤ d) (hh : IsWholeSpaceLGF h P)
    (V : Opens (Rd d)) (hVb : Bornology.IsBounded (V : Set (Rd d)))
    {ρ : TestRd d} (hρ : ∫ y, ρ y = 1)
    (hρV : tsupport (ρ : Rd d → ℝ) ⊆ V)
    (Y : Ω → Rd d → ℝ) (hYc : ∀ ω, ContinuousOn (Y ω) (extOpen V))
    (hYm : Measurable Y)
    (hYae : ∀ x (hx : x ∈ extOpen V),
      (fun ω => Y ω x) =ᵐ[P]
        (markovPointVec hd hh V hVb hρ hρV x hx : Ω → ℝ))
    (ψ : TestOn (extOpen V)) :
    (fun ω => ∫ x, (testIncl (extOpen V) ψ) x * Y ω x) =ᵐ[P]
      ((markovInsideSpace hh V hρ).starProjection
        (markovOutsideVec hh (extOpen V) hρ ψ) : Ω → ℝ) := by
  classical
  let w : Rd d → ℝ := testIncl (extOpen V) ψ
  let E : Rd d → Lp ℝ 2 P := markovExteriorVec hd hh V hVb hρ hρV
  let F : Rd d → Lp ℝ 2 P := fun x => w x • E x
  let Yw : Rd d → Ω → ℝ := fun x ω => w x * Y ω x
  let A : Ω → ℝ := fun ω => ∫ x, Yw x ω
  have hws : HasCompactSupport w := (testIncl (extOpen V) ψ).hasCompactSupport
  have hwo : tsupport w ⊆ extOpen V := by
    change tsupport ((testIncl (extOpen V) ψ : TestRd d) : Rd d → ℝ) ⊆ extOpen V
    rw [coe_testIncl]
    exact ψ.tsupport_subset
  obtain ⟨η, hηc, hηs, _, hη1⟩ := markov_exists_weightCutoff (extOpen V) hws hwo
  have hηw (x : Rd d) : η x * w x = w x := by
    by_cases hx : x ∈ tsupport w
    · rw [hη1 x hx, one_mul]
    · have hw0 : w x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [hw0]
  obtain ⟨hYwc, hYwm, hYwF, hYwL2, C, hC⟩ :=
    markov_weighted_version hd hh V hVb hρ hρV Y hYc hYm hYae ψ
  have hYb : ∀ R : ℝ, ∃ C' : ℝ, ∀ x : Rd d, ‖x‖ ≤ R →
      ∫ ω, Yw x ω ^ 2 ∂P ≤ C' := by
    intro R
    exact ⟨C, fun x _ => hC x⟩
  have hAeq (ω : Ω) : A ω = ∫ x, η x * Yw x ω := by
    apply integral_congr_ae
    refine ae_of_all _ fun x => ?_
    dsimp [Yw]
    rw [← mul_assoc, hηw]
  have hAL2 : MemLp A 2 P := by
    have h := markov_memLp_integral_mul_Y hYwc hYwm hYwL2 hYb hηc hηs
    exact h.ae_eq (Filter.Eventually.of_forall fun ω => (hAeq ω).symm)
  let A2 : Lp ℝ 2 P := hAL2.toLp A
  have hA2coe : (A2 : Ω → ℝ) =ᵐ[P] A := hAL2.coeFn_toLp
  have hFi : Integrable F := markov_integrable_weightedExteriorVec hd hh V hVb hρ hρV ψ
  have hFcov (x : Rd d) (T : Lp ℝ 2 P) :
      ∫ ω, Yw x ω * (T : Ω → ℝ) ω ∂P = ⟪F x, T⟫ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hYwF x, Lp.coeFn_smul (w x) (E x)] with ω hx hsm
    change Yw x ω = w x * (E x : Ω → ℝ) ω at hx
    change (F x : Ω → ℝ) ω = w x • (E x : Ω → ℝ) ω at hsm
    rw [hx, hsm]
    simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial, smul_eq_mul]
    ring
  have hAinner (T : Lp ℝ 2 P) : ⟪A2, T⟫ = ⟪∫ x, F x, T⟫ := by
    have hsf := markov_integral_integral_mul_Y_mul hYwc hYwm hYwL2 hYb
      hηc hηs (Lp.memLp T)
    have hL : ⟪A2, T⟫ = ∫ ω, A ω * (T : Ω → ℝ) ω ∂P := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hA2coe] with ω hω
      rw [hω]
      simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial]
      ring
    rw [hL]
    have hAeq' : (fun ω => (∫ x, η x * Yw x ω) * (T : Ω → ℝ) ω) =
        (fun ω => A ω * (T : Ω → ℝ) ω) := by
      funext ω
      rw [← hAeq]
    rw [← hAeq', hsf]
    calc
      (∫ x, η x * ∫ ω, Yw x ω * (T : Ω → ℝ) ω ∂P) =
          ∫ x, ⟪T, F x⟫ := by
            apply integral_congr_ae
            refine ae_of_all _ fun x => ?_
            change η x * (∫ ω, Yw x ω * (T : Ω → ℝ) ω ∂P) = ⟪T, F x⟫
            rw [hFcov x T, real_inner_comm]
            by_cases hx : x ∈ tsupport w
            · rw [hη1 x hx, one_mul]
            · have hw0 : w x = 0 := image_eq_zero_of_notMem_tsupport hx
              simp [F, hw0]
      _ = ⟪∫ x, F x, T⟫ := by
            exact (integral_inner hFi T).trans (real_inner_comm (∫ x, F x) T)
  have hA2eq : A2 = ∫ x, F x := ext_inner_right ℝ hAinner
  have hProj : (markovInsideSpace hh V hρ).starProjection
      (markovOutsideVec hh (extOpen V) hρ ψ) = ∫ x, F x :=
    markov_projOutside_eq_integral_pointVec hd hh V hVb hρ hρV ψ
  filter_upwards [hA2coe] with ω hω
  change A ω = _
  rw [← hω, hA2eq, ← hProj]

end HigherDimLQGMetric
