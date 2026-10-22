import HigherDimLQGMetric.Markov.BoundaryVar
import Mathlib.MeasureTheory.Function.FactorsThrough

/-! Reconstructing recentered LGF pairings from the interior and residual distributions. -/

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

omit [IsProbabilityMeasure P] in
theorem markovPair_subMean_eq_recenter {ρ : TestRd d} (g : DistRd d)
    (φ : TestRd d) (hρ : ∫ x, ρ x = 1) :
    g (subMean hρ φ).1 = recenter ρ g φ := by
  rw [recenter_apply]
  rfl

omit [IsProbabilityMeasure P] in
theorem markov_boundary_pair_split (V : Opens (Rd d))
    (φ ρ : TestRd d) (hρ : ∫ x, ρ x = 1)
    (g : DistRd d) (n : ℕ) :
    g (subMean hρ φ).1 -
      g (subMean hρ (markovBoundaryError V φ n)).1 =
      g (subMean hρ
        (markovTestMul φ (markovExhaustCut V n))).1 +
      g (subMean hρ
        (markovTestMul φ (markovExhaustCut (extOpen V) n))).1 := by
  repeat' rw [markovPair_subMean_eq_recenter]
  rw [← map_sub]
  have he : φ - markovBoundaryError V φ n =
      markovTestMul φ (markovExhaustCut V n) +
      markovTestMul φ (markovExhaustCut (extOpen V) n) := by
    unfold markovBoundaryError
    abel
  rw [he, map_add]

/-- Every smooth-test-recentered LGF pairing is a.e. measurable from the interior restriction
and the exterior Gaussian residual when the frontier is null. -/
theorem markov_recenter_pair_ae_decompMeas (hd : 2 ≤ d) (hh : IsWholeSpaceLGF h P)
    (V : Opens (Rd d)) (hVb : Bornology.IsBounded (V : Set (Rd d)))
    (z : Rd d) (r : ℝ) {ρ : TestRd d} (hρ : ∫ x, ρ x = 1)
    (hρV : tsupport (ρ : Rd d → ℝ) ⊆ V)
    (Y : Ω → Rd d → ℝ) (hYc : ∀ ω, ContinuousOn (Y ω) (extOpen V))
    (hYm : Measurable Y)
    (hYae : ∀ x (hx : x ∈ extOpen V),
      (fun ω => Y ω x) =ᵐ[P]
        (markovPointVec (by omega : 1 ≤ d) hh V hVb hρ hρV x hx : Ω → ℝ))
    (hnull : volume (frontier (V : Set (Rd d))) = 0)
    (φ : TestRd d) :
    let R := markovSphereResidual (h := h) V z r ρ Y
    let X : Ω → DistOn V × DistOn (extOpen V) := fun ω =>
      (restrictTo V (markovSphereField h z r ω), R ω)
    AEStronglyMeasurable[MeasurableSpace.comap X inferInstance]
      (fun ω => (recenter ρ (h ω)) φ) P := by
  classical
  dsimp
  let R := markovSphereResidual (h := h) V z r ρ Y
  let X : Ω → DistOn V × DistOn (extOpen V) := fun ω =>
    (restrictTo V (markovSphereField h z r ω), R ω)
  have hZm : Measurable (markovSphereField h z r) :=
    markov_measurable_sphereField hh z r
  have hRm : Measurable R :=
    markov_measurable_sphereResidual hh V z r ρ Y hYc hYm
  have hXm : Measurable X :=
    ((measurable_restrictTo V).comp hZm).prodMk hRm
  have hs : MeasurableSpace.comap X inferInstance ≤
      (inferInstance : MeasurableSpace Ω) := hXm.comap_le
  have hVm : Measurable[MeasurableSpace.comap X inferInstance]
      (fun ω => restrictTo V (markovSphereField h z r ω)) :=
    measurable_fst.comp (comap_measurable X)
  have hRm' : Measurable[MeasurableSpace.comap X inferInstance] R :=
    measurable_snd.comp (comap_measurable X)
  have hsSphere : fieldSigmaRd (markovSphereField h z r) V ≤
      MeasurableSpace.comap X inferInstance := hVm.comap_le
  have hsSmooth : fieldSigmaRd (fun ω => recenter ρ (h ω)) V ≤
      MeasurableSpace.comap X inferInstance :=
    (markov_smoothSigma_le_sphereSigma V z r hρ hρV).trans hsSphere
  have hInside (τ : TestOn V) :
      AEStronglyMeasurable[MeasurableSpace.comap X inferInstance]
        (fun ω => markovPair h (markovInsideTest V hρ τ) ω) P := by
    have hm : AEStronglyMeasurable[MeasurableSpace.comap X inferInstance]
        (markovInsideVec hh V hρ τ : Ω → ℝ) P :=
      (markov_insideVec_aestronglyMeasurable hh V hρ τ).mono hsSmooth
    exact hm.congr
      (markov_memLp_pair hh (markovInsideTest V hρ τ)).coeFn_toLp
  have hOutside (τ : TestOn (extOpen V)) :
      AEStronglyMeasurable[MeasurableSpace.comap X inferInstance]
        (fun ω => markovPair h (markovInsideTest (extOpen V) hρ τ) ω) P := by
    let B : Lp ℝ 2 P := markovOutsideVec hh (extOpen V) hρ τ
    let Q : Lp ℝ 2 P := (markovInsideSpace hh V hρ).starProjection B
    let E : Lp ℝ 2 P := markovResidualVec hh V hρ τ
    have hQ : AEStronglyMeasurable[MeasurableSpace.comap X inferInstance]
        (Q : Ω → ℝ) P :=
      (markov_projection_aestronglyMeasurable hh V hρ τ).mono hsSmooth
    have hRτ : Measurable[MeasurableSpace.comap X inferInstance]
        (fun ω => R ω τ) :=
      (measurable_distOn_apply τ).comp hRm'
    have hRae : (fun ω => R ω τ) =ᵐ[P] (E : Ω → ℝ) :=
      markov_sphereResidual_pair_ae (by omega : 1 ≤ d) hh V hVb hρ hρV
        Y hYc hYm hYae z r τ
    have hSub : (E : Ω → ℝ) =ᵐ[P]
        (fun ω => (B : Ω → ℝ) ω - (Q : Ω → ℝ) ω) := by
      filter_upwards [Lp.coeFn_sub B Q] with ω hω
      simpa only [E, B, Q, markovResidualVec, Pi.sub_apply] using hω
    have hBae : (B : Ω → ℝ) =ᵐ[P]
        (fun ω => markovPair h (markovInsideTest (extOpen V) hρ τ) ω) :=
      (markov_memLp_pair hh (markovInsideTest (extOpen V) hρ τ)).coeFn_toLp
    have hE : (fun ω => R ω τ + (Q : Ω → ℝ) ω) =ᵐ[P]
        (fun ω => markovPair h (markovInsideTest (extOpen V) hρ τ) ω) := by
      filter_upwards [hRae, hSub, hBae] with ω hRω hSω hBω
      linarith
    exact (hRτ.aestronglyMeasurable.add hQ).congr hE
  let T : Lp ℝ 2 P :=
    (markov_memLp_pair hh (subMean hρ φ)).toLp (markovPair h (subMean hρ φ))
  let E : ℕ → Lp ℝ 2 P := fun n =>
    (markov_memLp_pair hh (subMean hρ (markovBoundaryError V φ n))).toLp
      (markovPair h (subMean hρ (markovBoundaryError V φ n)))
  have hEt : Tendsto E atTop (𝓝 0) :=
    markov_boundaryPair_L2_tendsto_zero (by omega : 1 ≤ d) hh V φ ρ hρ hnull
  have hApprox (n : ℕ) :
      AEStronglyMeasurable[MeasurableSpace.comap X inferInstance]
        ((T - E n : Lp ℝ 2 P) : Ω → ℝ) P := by
    let φV : TestRd d := markovTestMul φ (markovExhaustCut V n)
    let φO : TestRd d := markovTestMul φ (markovExhaustCut (extOpen V) n)
    have hφV : tsupport (φV : Rd d → ℝ) ⊆ V :=
      (markovTestMul_tsupport_right φ _).trans (markovExhaustCut_support V n)
    have hφO : tsupport (φO : Rd d → ℝ) ⊆ extOpen V :=
      (markovTestMul_tsupport_right φ _).trans
        (markovExhaustCut_support (extOpen V) n)
    let τV := testOnOf V φV hφV
    let τO := testOnOf (extOpen V) φO hφO
    have hτV : AEStronglyMeasurable[MeasurableSpace.comap X inferInstance]
        (fun ω => markovPair h (subMean hρ φV) ω) P := by
      simpa [τV, markovInsideTest] using hInside τV
    have hτO : AEStronglyMeasurable[MeasurableSpace.comap X inferInstance]
        (fun ω => markovPair h (subMean hρ φO) ω) P := by
      simpa [τO, markovInsideTest] using hOutside τO
    have hsplit : ((T - E n : Lp ℝ 2 P) : Ω → ℝ) =ᵐ[P]
        (fun ω => markovPair h (subMean hρ φV) ω +
          markovPair h (subMean hρ φO) ω) := by
      filter_upwards [(markov_memLp_pair hh (subMean hρ φ)).coeFn_toLp,
        (markov_memLp_pair hh (subMean hρ (markovBoundaryError V φ n))).coeFn_toLp,
        Lp.coeFn_sub T (E n)] with ω ht he hsub
      rw [hsub]
      change (T : Ω → ℝ) ω - (E n : Ω → ℝ) ω = _
      rw [ht, he]
      exact markov_boundary_pair_split V φ ρ hρ (h ω) n
    exact (hτV.add hτO).congr hsplit.symm
  have hTt : Tendsto (fun n => T - E n) atTop (𝓝 T) := by
    simpa only [sub_zero] using (tendsto_const_nhds.sub hEt)
  have hClosed : IsClosed {u : Lp ℝ 2 P |
      AEStronglyMeasurable[MeasurableSpace.comap X inferInstance]
        (u : Ω → ℝ) P} :=
    isClosed_aestronglyMeasurable hs
  have hTm : AEStronglyMeasurable[MeasurableSpace.comap X inferInstance]
      (T : Ω → ℝ) P :=
    hClosed.mem_of_tendsto hTt (Eventually.of_forall hApprox)
  have hTae : (T : Ω → ℝ) =ᵐ[P] (fun ω => (recenter ρ (h ω)) φ) := by
    filter_upwards [(markov_memLp_pair hh (subMean hρ φ)).coeFn_toLp] with ω hω
    rw [hω]
    exact markovPair_subMean_eq_recenter (h ω) φ hρ
  exact hTm.congr hTae

end HigherDimLQGMetric
