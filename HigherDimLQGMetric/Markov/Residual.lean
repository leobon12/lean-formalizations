import HigherDimLQGMetric.Markov.NormResidual

/-! Distribution-valued residual pairings after the normalization correction. -/

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

omit [MeasurableSpace Ω] in
/-- Subtracting the interior-measurable normalization correction turns an exterior sphere
pairing into the smooth-test-recentered mean-zero pairing. -/
theorem markov_spherePair_sub_correction (V : Opens (Rd d)) (z : Rd d) (r : ℝ)
    {ρ : TestRd d} (hρ : ∫ x, ρ x = 1)
    (ψ : TestOn (extOpen V)) (ω : Ω) :
    restrictTo (extOpen V) (markovSphereField h z r ω) ψ -
      markovSphereCorrection h z r ρ ω * ∫ x, ψ x =
        markovPair h (markovInsideTest (extOpen V) hρ ψ) ω := by
  let Z := markovSphereField h z r ω
  have hI : (∫ x, (testIncl (extOpen V) ψ) x) = ∫ x, ψ x := by
    simp only [testIncl_apply]
  calc
    restrictTo (extOpen V) Z ψ - markovSphereCorrection h z r ρ ω * ∫ x, ψ x =
        recenter ρ Z (testIncl (extOpen V) ψ) := by
          rw [recenter_apply, map_sub, map_smul, restrictTo_apply]
          simp only [markovSphereCorrection, Z, hI, smul_eq_mul]
          ring
    _ = recenter ρ (h ω) (testIncl (extOpen V) ψ) := by
          dsimp [Z, markovSphereField]
          rw [recenter_addConst hρ]
    _ = markovPair h (markovInsideTest (extOpen V) hρ ψ) ω := by
          rw [recenter_apply]
          rfl

/-- The distribution induced by the corrected harmonic process has the expected test
pairing, including the constant shift. -/
theorem markov_sphereHarmonic_pair (hd : 1 ≤ d) (hh : IsWholeSpaceLGF h P)
    (V : Opens (Rd d)) (hVb : Bornology.IsBounded (V : Set (Rd d)))
    {ρ : TestRd d} (hρ : ∫ y, ρ y = 1)
    (hρV : tsupport (ρ : Rd d → ℝ) ⊆ V)
    (Y : Ω → Rd d → ℝ) (hYc : ∀ ω, ContinuousOn (Y ω) (extOpen V))
    (hYm : Measurable Y)
    (hYae : ∀ x (hx : x ∈ extOpen V),
      (fun ω => Y ω x) =ᵐ[P]
        (markovPointVec hd hh V hVb hρ hρV x hx : Ω → ℝ))
    (z : Rd d) (r : ℝ) (ψ : TestOn (extOpen V)) (ω : Ω) :
    ofFunOn (extOpen V)
      (markovSphereHarmonic V Y (markovSphereCorrection h z r ρ) ω) ψ =
      (∫ x, (testIncl (extOpen V) ψ) x * Y ω x) +
        markovSphereCorrection h z r ρ ω * ∫ x, ψ x := by
  classical
  let O := extOpen V
  let q := markovSphereCorrection h z r ρ
  let H := markovSphereHarmonic V Y q
  have hYwc : Continuous fun x : Rd d => (testIncl O ψ) x * Y ω x :=
    (markov_weighted_version hd hh V hVb hρ hρV Y hYc hYm hYae ψ).1 ω
  have hYi : Integrable (fun x : Rd d => (testIncl O ψ) x * Y ω x) :=
    hYwc.integrable_of_hasCompactSupport
      (testIncl O ψ).hasCompactSupport.mul_right
  have hψi : Integrable (fun x : Rd d => ψ x) := integrable_testOn ψ
  have hHi : LocallyIntegrableOn (H ω) O volume :=
    (markovSphereHarmonic_continuousOn V Y q hYc ω).locallyIntegrableOn O.isOpen.measurableSet
  rw [ofFunOn, Distribution.ofFun_apply hHi]
  have hpoint (x : Rd d) : ψ x * H ω x = ψ x * (Y ω x + q ω) := by
    by_cases hx : x ∈ O
    · change ψ x * (if x ∈ extOpen V then Y ω x + q ω else 0) = _
      split_ifs with h
      · rfl
      · exact False.elim (h hx)
    · have hψ0 : ψ x = 0 :=
        image_eq_zero_of_notMem_tsupport (fun ht => hx (ψ.tsupport_subset ht))
      simp [hψ0]
  calc
    (∫ x, ψ x • H ω x) = ∫ x, ψ x * (Y ω x + q ω) := by
      apply integral_congr_ae
      exact ae_of_all _ fun x => by
        change ψ x • H ω x = ψ x * (Y ω x + q ω)
        simpa only [smul_eq_mul] using hpoint x
    _ = ∫ x, ((testIncl O ψ) x * Y ω x + q ω * ψ x) := by
      apply integral_congr_ae
      refine ae_of_all _ fun x => ?_
      change ψ x * (Y ω x + q ω) = (testIncl O ψ) x * Y ω x + q ω * ψ x
      rw [testIncl_apply]
      ring
    _ = (∫ x, (testIncl O ψ) x * Y ω x) + q ω * ∫ x, ψ x := by
      rw [integral_add hYi (hψi.const_mul _), integral_const_mul]

/-- The exterior residual distribution after sphere normalization. -/
def markovSphereResidual (V : Opens (Rd d)) (z : Rd d) (r : ℝ)
    (ρ : TestRd d) (Y : Ω → Rd d → ℝ) : Ω → DistOn (extOpen V) :=
  fun ω => restrictTo (extOpen V) (markovSphereField h z r ω) -
    ofFunOn (extOpen V)
      (markovSphereHarmonic V Y (markovSphereCorrection h z r ρ) ω)

omit [IsProbabilityMeasure P] in
theorem markov_measurable_sphereResidual (hh : IsWholeSpaceLGF h P)
    (V : Opens (Rd d)) (z : Rd d) (r : ℝ) (ρ : TestRd d)
    (Y : Ω → Rd d → ℝ)
    (hYc : ∀ ω, ContinuousOn (Y ω) (extOpen V)) (hYm : Measurable Y) :
    Measurable (markovSphereResidual (h := h) V z r ρ Y) := by
  let q := markovSphereCorrection h z r ρ
  let H := markovSphereHarmonic V Y q
  have hZm : Measurable (markovSphereField h z r) :=
    markov_measurable_sphereField hh z r
  have hqm : Measurable q := (measurable_distOn_apply ρ).comp hZm
  have hHm : Measurable H := markovSphereHarmonic_measurable V Y q hYm hqm
  have hHc (ω : Ω) : ContinuousOn (H ω) (extOpen V) :=
    markovSphereHarmonic_continuousOn V Y q hYc ω
  exact ((measurable_restrictTo (extOpen V)).comp hZm).sub
    (markov_measurable_ofFunOn (extOpen V) H hHc hHm)

/-- Every residual test pairing agrees almost surely with the Gaussian orthogonal residual
vector. -/
theorem markov_sphereResidual_pair_ae (hd : 1 ≤ d) (hh : IsWholeSpaceLGF h P)
    (V : Opens (Rd d)) (hVb : Bornology.IsBounded (V : Set (Rd d)))
    {ρ : TestRd d} (hρ : ∫ y, ρ y = 1)
    (hρV : tsupport (ρ : Rd d → ℝ) ⊆ V)
    (Y : Ω → Rd d → ℝ) (hYc : ∀ ω, ContinuousOn (Y ω) (extOpen V))
    (hYm : Measurable Y)
    (hYae : ∀ x (hx : x ∈ extOpen V),
      (fun ω => Y ω x) =ᵐ[P]
        (markovPointVec hd hh V hVb hρ hρV x hx : Ω → ℝ))
    (z : Rd d) (r : ℝ) (ψ : TestOn (extOpen V)) :
    (fun ω => markovSphereResidual (h := h) V z r ρ Y ω ψ) =ᵐ[P]
      (markovResidualVec hh V hρ ψ : Ω → ℝ) := by
  let Q : Lp ℝ 2 P := (markovInsideSpace hh V hρ).starProjection
    (markovOutsideVec hh (extOpen V) hρ ψ)
  have hA : (fun ω => ∫ x, (testIncl (extOpen V) ψ) x * Y ω x) =ᵐ[P]
      (Q : Ω → ℝ) :=
    markov_integral_version_ae_proj hd hh V hVb hρ hρV Y hYc hYm hYae ψ
  have hB : (markovOutsideVec hh (extOpen V) hρ ψ : Ω → ℝ) =ᵐ[P]
      (fun ω => markovPair h (markovInsideTest (extOpen V) hρ ψ) ω) := by
    exact (markov_memLp_pair hh (markovInsideTest (extOpen V) hρ ψ)).coeFn_toLp
  have hSub : (markovResidualVec hh V hρ ψ : Ω → ℝ) =ᵐ[P]
      (fun ω => (markovOutsideVec hh (extOpen V) hρ ψ : Ω → ℝ) ω -
        (Q : Ω → ℝ) ω) := by
    filter_upwards [Lp.coeFn_sub (markovOutsideVec hh (extOpen V) hρ ψ) Q] with ω hω
    simpa only [markovResidualVec, Q, Pi.sub_apply] using hω
  filter_upwards [hA, hB, hSub] with ω hAω hBω hSω
  change (restrictTo (extOpen V) (markovSphereField h z r ω) -
    ofFunOn (extOpen V)
      (markovSphereHarmonic V Y (markovSphereCorrection h z r ρ) ω)) ψ = _
  rw [sub_apply, markov_sphereHarmonic_pair hd hh V hVb hρ hρV
    Y hYc hYm hYae z r ψ ω]
  rw [hAω, hSω]
  have hNorm := markov_spherePair_sub_correction (h := h) V z r hρ ψ ω
  rw [← hBω] at hNorm
  linarith

end HigherDimLQGMetric
