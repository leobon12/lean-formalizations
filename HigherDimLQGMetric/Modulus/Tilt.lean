import HigherDimLQGMetric.CM.SphereTilt
import HigherDimLQGMetric.LGF.Law

/-!
# The sphere-average tilt of an LGF is an LGF (packet W3b, [S] Lemma 2.6, Step 1)

Let `h` be a whole-space LGF under `P`, `X = h_r(z) − h_ρ(w)` (`r, ρ > 0`) and `a ∈ ℝ`. Under the
tilted probability measure `P' = e^{aX − a² Var X / 2} · P` the field `h − a k`, where
`k = F_{r,z} − F_{ρ,w}` is the logarithmic potential of `σ_{r,z} − σ_{ρ,w}` (F4's `sf4Potential`),
is again a whole-space LGF (`w3b_isWholeSpaceLGF_tilt`). This is F4's `sf4_tilt_pair0` read as an
equality of laws of the mean-zero pairings (`w3b_map_pairProc_tilt`), combined with the law transfer
`w3b_isWholeSpaceLGF_of_map_pairProc_eq`: `IsWholeSpaceLGF` depends only on the law of the process
of mean-zero pairings.

It is the form in which MA1 A8 uses the Gaussian tilting identity
`E[e^{λX} F(H)] = e^{λ² Var X/2} E[F(H + λk)]`: (E5) (`E5SharpMoment`) can be applied directly to
the LGF `h − a k` on the tilted space, so no measurability of the functional `F` is needed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open HigherDimLFPP (Rd)

namespace HigherDimLQGMetric

variable {d : ℕ}

/-! ## Law transfer -/

section LawTransfer

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω}
  {P' : Measure Ω'}

/-- `IsWholeSpaceLGF` depends only on the law of the process of mean-zero pairings: if a measurable
random distribution `h'` under `P'` has the same law of mean-zero pairings as an LGF `h` under `P`,
then `h'` is an LGF. -/
theorem w3b_isWholeSpaceLGF_of_map_pairProc_eq {h : Ω → DistRd d} {h' : Ω' → DistRd d}
    (hh : IsWholeSpaceLGF h P) (hm : Measurable h')
    (hmap : P'.map (pairProc h') = P.map (pairProc h)) : IsWholeSpaceLGF h' P' where
  measurable := hm
  gaussian := by
    refine ⟨fun I => ?_⟩
    have hR : Measurable (I.restrict : (TestRd0 d → ℝ) → (I → ℝ)) := Finset.measurable_restrict I
    have hX : Measurable fun ω => I.restrict fun φ : TestRd0 d => h' ω φ.1 :=
      hR.comp (measurable_pairProc hm)
    refine ⟨hX.aemeasurable, ?_⟩
    have h1 := (hh.gaussian.hasGaussianLaw I).isGaussian_map
    have e1 : P'.map (fun ω => I.restrict fun φ : TestRd0 d => h' ω φ.1) =
        (P'.map (pairProc h')).map I.restrict := by
      rw [Measure.map_map hR (measurable_pairProc hm)]
      rfl
    have e2 : P.map (fun ω => I.restrict fun φ : TestRd0 d => h ω φ.1) =
        (P.map (pairProc h)).map I.restrict := by
      rw [Measure.map_map hR (measurable_pairProc hh.measurable)]
      rfl
    rw [e1, hmap, ← e2]
    exact h1
  centered := fun φ => by
    have hev : Measurable fun f : TestRd0 d → ℝ => f φ := measurable_pi_apply φ
    calc ∫ ω, h' ω φ.1 ∂P' = ∫ f, f φ ∂(P'.map (pairProc h')) := by
          rw [integral_map (measurable_pairProc hm).aemeasurable hev.aestronglyMeasurable]
          rfl
      _ = ∫ f, f φ ∂(P.map (pairProc h)) := by rw [hmap]
      _ = ∫ ω, h ω φ.1 ∂P := by
          rw [integral_map (measurable_pairProc hh.measurable).aemeasurable
            hev.aestronglyMeasurable]
          rfl
      _ = 0 := hh.centered φ
  covariance_eq := fun φ ψ => by
    have hφ : Measurable fun f : TestRd0 d → ℝ => f φ := measurable_pi_apply φ
    have hψ : Measurable fun f : TestRd0 d → ℝ => f ψ := measurable_pi_apply ψ
    have e1 := covariance_map (μ := P') (X := fun f : TestRd0 d → ℝ => f φ)
      (Y := fun f : TestRd0 d → ℝ => f ψ) hφ.aestronglyMeasurable hψ.aestronglyMeasurable
      (measurable_pairProc hm).aemeasurable
    have e2 := covariance_map (μ := P) (X := fun f : TestRd0 d → ℝ => f φ)
      (Y := fun f : TestRd0 d → ℝ => f ψ) hφ.aestronglyMeasurable hψ.aestronglyMeasurable
      (measurable_pairProc hh.measurable).aemeasurable
    rw [hmap] at e1
    calc cov[fun ω => h' ω φ.1, fun ω => h' ω ψ.1; P'] =
        cov[fun f : TestRd0 d → ℝ => f φ, fun f : TestRd0 d → ℝ => f ψ; P.map (pairProc h)] :=
          e1.symm
      _ = cov[fun ω => h ω φ.1, fun ω => h ω ψ.1; P] := e2
      _ = logCovRd φ.1 ψ.1 := hh.covariance_eq φ ψ

end LawTransfer

/-! ## The tilted measure -/

section Tilt

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistRd d}

/-- The tilt density `exp(a X − a² Var X / 2)` of `X = h_r(z) − h_ρ(w)` (MA1 A8, Step 1). -/
def w3bTiltDensity (h : Ω → DistRd d) (P : Measure Ω) (r ρ : ℝ) (z w : Rd d) (a : ℝ)
    (ω : Ω) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (a * (sphereAvg (h ω) r z - sphereAvg (h ω) ρ w) -
    a ^ 2 * Var[fun ω => sphereAvg (h ω) r z - sphereAvg (h ω) ρ w; P] / 2))

theorem measurable_w3bTiltDensity (hm : Measurable h) (r ρ : ℝ) (z w : Rd d) (a : ℝ) :
    Measurable (w3bTiltDensity h P r ρ z w a) := by
  have hX : Measurable fun ω => sphereAvg (h ω) r z - sphereAvg (h ω) ρ w :=
    ((measurable_sphereAvg_left r z).comp hm).sub ((measurable_sphereAvg_left ρ w).comp hm)
  exact (Real.measurable_exp.comp ((hX.const_mul a).sub_const _)).ennreal_ofReal

theorem w3bTiltDensity_lt_top (r ρ : ℝ) (z w : Rd d) (a : ℝ) (ω : Ω) :
    w3bTiltDensity h P r ρ z w a ω < ∞ :=
  ENNReal.ofReal_lt_top

/-- The tilt density has total mass `P univ`. -/
theorem w3b_lintegral_tiltDensity (hd : 2 ≤ d) (hh : IsWholeSpaceLGF h P) {r ρ : ℝ} (hr : 0 < r)
    (hρ : 0 < ρ) (z w : Rd d) (a : ℝ) :
    ∫⁻ ω, w3bTiltDensity h P r ρ z w a ω ∂P = P univ := by
  have key := sf4_tilt_pair0 hd hh hr hρ z w a (fun _ => (1 : ℝ≥0∞)) measurable_const
  simp only [one_mul, lintegral_const] at key
  rw [key]
  rfl

/-- The tilted measure is a probability measure. -/
theorem w3b_isProbabilityMeasure_tilt (hd : 2 ≤ d) (hh : IsWholeSpaceLGF h P)
    [IsProbabilityMeasure P] {r ρ : ℝ} (hr : 0 < r) (hρ : 0 < ρ) (z w : Rd d) (a : ℝ) :
    IsProbabilityMeasure (P.withDensity (w3bTiltDensity h P r ρ z w a)) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    w3b_lintegral_tiltDensity hd hh hr hρ z w a, measure_univ]

/-- The mean-zero pairings of `h − a k` under the tilted measure have the law of those of `h`
under `P` (SF4, read as an equality of laws). -/
theorem w3b_map_pairProc_tilt (hd : 2 ≤ d) (hh : IsWholeSpaceLGF h P) {r ρ : ℝ} (hr : 0 < r)
    (hρ : 0 < ρ) (z w : Rd d) (a : ℝ) :
    (P.withDensity (w3bTiltDensity h P r ρ z w a)).map
        (pairProc fun ω => addFun (h ω) (-(a • sf4Potential hd hr hρ z w))) =
      P.map (pairProc h) := by
  set k := sf4Potential hd hr hρ z w with hk
  set F : C(Rd d, ℝ) := -(a • k) with hF
  have hm' : Measurable fun ω => addFun (h ω) F := (measurable_addFun_left F).comp hh.measurable
  have hpm' := measurable_pairProc hm'
  have hpm := measurable_pairProc hh.measurable
  have hdens := measurable_w3bTiltDensity (P := P) hh.measurable r ρ z w a
  ext S hS
  rw [Measure.map_apply hpm' hS, Measure.map_apply hpm hS, withDensity_apply _ (hpm' hS)]
  let Φ : (TestRd0 d → ℝ) → ℝ≥0∞ := fun f => S.indicator (fun _ => (1 : ℝ≥0∞)) (cmShiftPath F f)
  have hΦ : Measurable Φ :=
    (measurable_const.indicator hS).comp (measurable_cmShiftPath F)
  have key := sf4_tilt_pair0 hd hh hr hρ z w a Φ hΦ
  have hint : ∀ φ : TestRd0 d, ∫ x, F x * φ.1 x = -(a * ∫ x, k x * φ.1 x) := by
    intro φ
    rw [← integral_const_mul, ← integral_neg]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hF, ContinuousMap.neg_apply, ContinuousMap.smul_apply, smul_eq_mul]
    ring
  have hL : ∀ ω, Φ (fun φ => pair0Rd (h ω) φ + a * ∫ x, k x * φ.1 x) =
      S.indicator (fun _ => (1 : ℝ≥0∞)) (pairProc h ω) := by
    intro ω
    have e : cmShiftPath F (fun φ => pair0Rd (h ω) φ + a * ∫ x, k x * φ.1 x) = pairProc h ω := by
      funext φ
      simp only [cmShiftPath, hint φ]
      rw [pair0Rd]
      simp only [pairProc]
      ring
    simp only [Φ, e]
  have hR : ∀ ω, Φ (pair0Rd (h ω)) * w3bTiltDensity h P r ρ z w a ω =
      (pairProc (fun ω => addFun (h ω) F) ⁻¹' S).indicator (w3bTiltDensity h P r ρ z w a) ω := by
    intro ω
    have e : cmShiftPath F (pair0Rd (h ω)) = pairProc (fun ω => addFun (h ω) F) ω := by
      rw [cmShiftPath_pair0]
      rfl
    simp only [Φ, e]
    by_cases hω : pairProc (fun ω => addFun (h ω) F) ω ∈ S
    · simp [indicator_of_mem hω, indicator_of_mem (show ω ∈ pairProc (fun ω => addFun (h ω) F) ⁻¹' S
        from hω)]
    · simp [indicator_of_notMem hω, indicator_of_notMem (show ω ∉ pairProc
        (fun ω => addFun (h ω) F) ⁻¹' S from hω)]
  calc ∫⁻ ω in pairProc (fun ω => addFun (h ω) F) ⁻¹' S, w3bTiltDensity h P r ρ z w a ω ∂P
      = ∫⁻ ω, (pairProc (fun ω => addFun (h ω) F) ⁻¹' S).indicator
          (w3bTiltDensity h P r ρ z w a) ω ∂P := (lintegral_indicator (hpm' hS) _).symm
    _ = ∫⁻ ω, Φ (pair0Rd (h ω)) * w3bTiltDensity h P r ρ z w a ω ∂P :=
          lintegral_congr fun ω => (hR ω).symm
    _ = ∫⁻ ω, Φ (fun φ => pair0Rd (h ω) φ + a * ∫ x, k x * φ.1 x) ∂P := key.symm
    _ = ∫⁻ ω, (pairProc h ⁻¹' S).indicator 1 ω ∂P := by
          refine lintegral_congr fun ω => ?_
          rw [hL ω]
          by_cases hω : pairProc h ω ∈ S
          · simp [indicator_of_mem hω, indicator_of_mem (show ω ∈ pairProc h ⁻¹' S from hω)]
          · simp [indicator_of_notMem hω,
              indicator_of_notMem (show ω ∉ pairProc h ⁻¹' S from hω)]
    _ = P (pairProc h ⁻¹' S) := lintegral_indicator_one (hpm hS)

/-- **Tilted LGF.** Under `P' = e^{aX − a² Var X/2} · P` (`X = h_r(z) − h_ρ(w)`), the field
`h − a k` (`k = sf4Potential`, the log potential of `σ_{r,z} − σ_{ρ,w}`) is a whole-space LGF. -/
theorem w3b_isWholeSpaceLGF_tilt (hd : 2 ≤ d) (hh : IsWholeSpaceLGF h P) {r ρ : ℝ} (hr : 0 < r)
    (hρ : 0 < ρ) (z w : Rd d) (a : ℝ) :
    IsWholeSpaceLGF (fun ω => addFun (h ω) (-(a • sf4Potential hd hr hρ z w)))
      (P.withDensity (w3bTiltDensity h P r ρ z w a)) :=
  w3b_isWholeSpaceLGF_of_map_pairProc_eq hh ((measurable_addFun_left _).comp hh.measurable)
    (w3b_map_pairProc_tilt hd hh hr hρ z w a)

end Tilt

end HigherDimLQGMetric
