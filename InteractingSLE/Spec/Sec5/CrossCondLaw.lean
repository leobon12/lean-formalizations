/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossCond
import InteractingSLE.Spec.Sec5.GlueCondPath

/-!
# The cross-conditioning law at general `κ`: the conditional Gaussian law given both stopped records (Astra's E.3)

Packet PROVE-GLUECOND5. Astra's follow-up note, Part E.3 (lines 1126–1158) at general `κ`, on the glued space of
`Prop411Q.CfGlueAE`: "Fix an original deterministic rational forward time `t`. The reverse prefix through its own `σ`
and the forward prefix through `t` are conditionally independent given `h` … Proposition 3.7 supplies their full
marked Gaussian law. Proposition 3.8 … identif[ies] the union mean with the corresponding individual mean along each
exposed slit side, and with the original boundary mean on the remaining original boundary."

**`ae_condExp_cfGlue`**: almost surely on the glued space, for a test function `φ` supported off `A ∪ G`
(`A = K_q` the flow hull, `G = R(K′_t)` the reflected counterflow hull, both read from the histories), given the germ
of `A ∪ G` and both stopped histories:

* the conditional mean of the centred field `h − 𝔥₀` tested against `φ` is `∫ w φ`, and
* the conditional characteristic function of `h` is `exp(i ∫ (w + 𝔥₀) φ) · exp(−½ G_{ℍ∖(A∪G)}(φ, φ))`,

for a harmonic `w` on `ℍ ∖ (A ∪ G)` with `w − (𝔥_q − 𝔥₀) → 0` near `A ∪ ℝ` away from `G` (the flow line's own mean)
and `w − cfMeanQ → 0` near `G ∪ ℝ` away from `A` (the counterflow's own mean). This is the field side of both
cross-conditionings at deterministic times; at general `κ` the union mean carries the `χ arg g′` term, which enters
only through the explicit single-curve means (the image-chart identification of `w` is PROVE-GLUECOND4's).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal Real
open QuantumZipper (H chiC fwdHull)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Sec5.CrossCond

open WangWu hiding ratPt exists_ratPt_dist_lt
open LawUnique Cond44Ref GlueCond WholeField LocalSets
open SupercriticalConformalCovariance.GM24 (smoothDist)

section Law

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}
  {Ω₂ : Type u} {mΩ₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
  {h₂ : Ω₂ → DistOn upperHalfPlaneOpens} {W₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞}
  {k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)} [IsMarkovKernel k] {u₀ : ℂ → ℝ}

/-- The flow hull and the reflected counterflow hull together are relatively closed in `ℍ`. -/
theorem union_relClosed (q t : ℝ≥0) (y : HistorySpace nL nR) (y₂ : HistorySpace 0 0) :
    hullAt q y ∪ cfHullQ t y₂ ⊆ H ∧ IsOpen (H \ (hullAt q y ∪ cfHullQ t y₂)) := by
  obtain ⟨h1, h2⟩ := hullAt_relClosed q y
  obtain ⟨h3, h4⟩ := cfHullQ_relClosed t y₂
  refine ⟨union_subset h1 h3, ?_⟩
  have e : H \ (hullAt q y ∪ cfHullQ t y₂) = (H \ hullAt q y) ∩ (H \ cfHullQ t y₂) := by
    ext z; simp only [Set.mem_sdiff, mem_inter_iff, mem_union]; tauto
  rw [e]
  exact h2.inter h4

/-- The centred glued field is a zero-boundary GFF on the glued space. -/
theorem isZeroBoundaryGFF_cenT_glue (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀) :
    LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (fun p : Ω × HistorySpace 0 0 => cenT κ u₀ (cfField κ (h p.1)))
      (glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1)) := by
  have hXm₀ : Measurable fun ω => cfField κ (h ω) := (measurable_cfField κ).comp hC.2.1
  have e : (fun p : Ω × HistorySpace 0 0 => cenT κ u₀ (cfField κ (h p.1))) =
      fun p => centredField h u₀ p.1 := funext fun p => cenT_cfField κ u₀ (h p.1)
  rw [e]
  exact isZeroBoundaryGFF_comp_of_map_eq (g := fun ω => centredField h u₀ ω) (f := Prod.fst) measurable_fst
    (glueMeasure_fst (μ := P) k hXm₀) (isZeroBoundaryGFF_centredField hC hu₀)

/-- **E.3: the conditional Gaussian law given the germ of the revealed union and both stopped records, at general
`κ`.** In the setting of `isHistoryAvoidanceLocal_cfGlue` (bounded harmonic extensions `u′` of the counterflow word's
data and `u ω` of the flow word's data at time `q`), for every test function `φ`: almost surely on the glued space,
if `φ` is supported off `A ∪ G` (`A = K_q`, `G = R(K′_t)`), there is a harmonic `w` on `ℍ ∖ (A ∪ G)` with

* `w − (𝔥_q − 𝔥₀) → 0` at every point of `A ∪ ℝ` near which `G ⊆ A`, and `w − cfMeanQ u′ t → 0` at every point of
  `G ∪ ℝ` near which `A ⊆ G` (the boundary data of the two single-curve conditional laws),
* `E[(h − 𝔥₀, φ) | 𝒜 ∨ ℋ] = ∫ w φ` and
* `E[e^{i (h, φ)} | 𝒜 ∨ ℋ] = exp(i ∫ (w + 𝔥₀) φ) · exp(−½ G_{ℍ∖(A∪G)}(φ, φ))`,

where `𝒜` is the germ σ-algebra of `A ∪ G` for the centred field and `ℋ = cfGlueMarks` (both stopped histories). -/
theorem ae_condExp_cfGlue (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hκ : 0 < κ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂)
    (hreg₂ : ∀ᵐ ω ∂P₂, ζ₂ ω = ⊤ ∧ W₂ 0 ω = 0 ∧ Continuous fun t => W₂ t ω)
    (hlaw : P.map (fun ω => cfField κ (h ω)) = P₂.map h₂)
    (hk : P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k)
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀) (q t : ℝ≥0)
    {u' : ℂ → ℝ}
    (hu' : IsBoundedHarmonicExtension
      (cfWordData κ (fun x => forceBoundaryData κ ρL ρR xL xR x + -(π / 2 * chiC κ)) (forceJumpFinset xL xR))
      (cfWordJumps κ (fun x => forceBoundaryData κ ρL ρR xL xR x + -(π / 2 * chiC κ)) (forceJumpFinset xL xR)) u')
    {u : Ω → ℂ → ℝ}
    (hu : ∀ ω, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i q ω - W q ω) (fun i => VR i q ω - W q ω))
      (forceJumpSet (fun i => VL i q ω - W q ω) (fun i => VR i q ω - W q ω)) (u ω))
    (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ p ∂(glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1)),
      tsupport φ ⊆ H \ (hullAt q (killedHistory W VL VR ζ p.1) ∪ cfHullQ t p.2) →
      ∃ w : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w (H \ (hullAt q (killedHistory W VL VR ζ p.1) ∪ cfHullQ t p.2)) ∧
        (∀ z₀ ∈ hullAt q (killedHistory W VL VR ζ p.1) ∪ {z : ℂ | z.im = 0},
          (∃ r > 0, cfHullQ t p.2 ∩ ball z₀ r ⊆ hullAt q (killedHistory W VL VR ζ p.1)) →
          Tendsto (fun z => w z - (couplingMean κ (fun s : ℝ => W s.toNNReal p.1) q (u p.1) z - u₀ z))
            (𝓝[H \ (hullAt q (killedHistory W VL VR ζ p.1) ∪ cfHullQ t p.2)] z₀) (𝓝 0)) ∧
        (∀ z₀ ∈ cfHullQ t p.2 ∪ {z : ℂ | z.im = 0},
          (∃ r > 0, hullAt q (killedHistory W VL VR ζ p.1) ∩ ball z₀ r ⊆ cfHullQ t p.2) →
          Tendsto (fun z => w z - cfMeanQ κ (fun x => forceBoundaryData κ ρL ρR xL xR x + -(π / 2 * chiC κ))
              (forceJumpFinset xL xR) u' t p.2 z)
            (𝓝[H \ (hullAt q (killedHistory W VL VR ζ p.1) ∪ cfHullQ t p.2)] z₀) (𝓝 0)) ∧
        (glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1))[
            fun p' => cenT κ u₀ (cfField κ (h p'.1)) φ |
            germSigma (fun p : Ω × HistorySpace 0 0 => hullAt q (killedHistory W VL VR ζ p.1) ∪ cfHullQ t p.2)
              (fun p => cenT κ u₀ (cfField κ (h p.1))) ⊔ cfGlueMarks W VL VR ζ q t] p = ∫ z, w z * φ z ∧
        (glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1))[
            fun p' => Complex.exp (Complex.I * (h p'.1 φ : ℂ)) |
            germSigma (fun p : Ω × HistorySpace 0 0 => hullAt q (killedHistory W VL VR ζ p.1) ∪ cfHullQ t p.2)
              (fun p => cenT κ u₀ (cfField κ (h p.1))) ⊔ cfGlueMarks W VL VR ζ q t] p =
          Complex.exp (Complex.I * ((∫ z, (w z + u₀ z) * φ z : ℝ) : ℂ)) *
            ((Real.exp (-(1 / 2) * QuantumZipper.zeroGFFTestCov
              (H \ (hullAt q (killedHistory W VL VR ζ p.1) ∪ cfHullQ t p.2)) φ φ) : ℝ) : ℂ) := by
  set μ := glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1) with hμ
  have hX := hC.2.2.2.1
  have hYm : Measurable (killedHistory W VL VR ζ) := measurable_killedHistory hX
  have hF := isZeroBoundaryGFF_cenT_glue (k := k) hC hu₀
  have hAm : Measurable[_, hittingSigma] fun p : Ω × HistorySpace 0 0 =>
      hullAt q (killedHistory W VL VR ζ p.1) ∪ cfHullQ t p.2 :=
    measurable_union_hitting (((measurable_hullAt q).comp hYm).comp measurable_fst)
      ((measurable_cfHullQ t).comp measurable_snd)
  have hmark := isHistoryAvoidanceLocal_cfGlue hC hκ hζ hcf hreg₂ hlaw hk hu₀ q t
  have hloc := (isLocalSet_union_glue (k := k) hC hζ hcf hreg₂ hlaw hk hu₀ q t).2.2
  obtain ⟨M, -, hM1, hM2⟩ := exists_condExp_germSigma_history hF hAm (cfGlueMarks_le q t hX) hmark
    (Eventually.of_forall fun p => union_relClosed q t _ p.2) φ
  obtain ⟨g, hg⟩ := IsLocalSet.exists_isLocalSetMean hF hAm hloc
  have hgM := IsLocalSetMean.ae_eq_condExp_germSigma_sup hF hAm hloc (cfGlueMarks_le q t hX) hmark hg φ
  have hU := ae_union_mean_cfGlue hC hκ hζ hcf hreg₂ hlaw hk hu₀ q t hu' hu hg
  -- pulling out the harmonic shift
  set c : ℂ := Complex.exp (Complex.I * ((∫ z, u₀ z * φ z : ℝ) : ℂ)) with hc
  have e : (fun p : Ω × HistorySpace 0 0 => Complex.exp (Complex.I * (h p.1 φ : ℂ))) =
      c • fun p => Complex.exp (Complex.I * (cenT κ u₀ (cfField κ (h p.1)) φ : ℂ)) := by
    funext p
    simp only [Pi.smul_apply, smul_eq_mul, hc, cenT_cfField, ← Complex.exp_add]
    rw [show h p.1 - smoothDist upperHalfPlaneOpens u₀ = centredField h u₀ p.1 from rfl,
      centredField_apply h hu₀.1 p.1 φ]
    congr 1
    push_cast
    ring
  have hpull := condExp_smul (μ := μ) c (fun p : Ω × HistorySpace 0 0 =>
    Complex.exp (Complex.I * (cenT κ u₀ (cfField κ (h p.1)) φ : ℂ)))
    (germSigma (fun p : Ω × HistorySpace 0 0 => hullAt q (killedHistory W VL VR ζ p.1) ∪ cfHullQ t p.2)
      (fun p => cenT κ u₀ (cfField κ (h p.1))) ⊔ cfGlueMarks W VL VR ζ q t)
  rw [← e] at hpull
  filter_upwards [hM1, hM2, hgM, hU, hpull] with p h1 h2 h3 h4 h5 hsupp
  obtain ⟨w, hw, hgw, hlimA, hlimG⟩ := h4
  have hMp : M p = ∫ z, w z * φ z := by rw [h1, ← h3, hgw φ hsupp]
  refine ⟨w, hw, hlimA, hlimG, by rw [← h3, hgw φ hsupp], ?_⟩
  obtain ⟨hsub, hopen⟩ := union_relClosed q t (killedHistory W VL VR ζ p.1) p.2
  rw [h5, Pi.smul_apply, ← h2, smul_eq_mul, hMp, relClosureH_eq hsub hopen]
  have hwi : Integrable fun z => w z * φ z :=
    Coupling.MartMeans2.integrable_mul_test_of_continuousOn
      (fun z hz => (hw z hz).1.continuousAt.continuousWithinAt) φ hsupp
  have hui : Integrable fun z => u₀ z * φ z :=
    Coupling.MartMeans2.integrable_mul_test_of_continuousOn
      (fun z hz => (hu₀.1 z hz).1.continuousAt.continuousWithinAt) φ φ.tsupport_subset
  have hint : (∫ z, (w z + u₀ z) * φ z) = (∫ z, w z * φ z) + ∫ z, u₀ z * φ z := by
    rw [← integral_add hwi hui]
    exact integral_congr_ae (Eventually.of_forall fun z => by simp only; ring)
  rw [hint, hc, ← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

end Law

/-! ### What the two stopped histories know -/

section Marks

variable {nL nR : ℕ}

theorem stopHistory_const_stopHistory_const (t : ℝ≥0) (y : HistorySpace nL nR) :
    Sec4.stopHistory (fun _ => t) (Sec4.stopHistory (fun _ => t) y) = Sec4.stopHistory (fun _ => t) y := by
  simp only [Sec4.stopHistory, Prod.mk.injEq, true_and]
  funext p
  split_ifs <;> rfl

/-- **The hull at time `t` is known to the history stopped at `t`.** -/
theorem measurable_hullAt_stopSigma (t : ℝ≥0) :
    Measurable[stopSigma t, hittingSigma] (hullAt (nL := nL) (nR := nR) t) := by
  have e : hullAt (nL := nL) (nR := nR) t = hullAt t ∘ Sec4.stopHistory (fun _ => t) := by
    funext y
    simp only [Function.comp_apply, hullAt]
    exact congrArg Sec4.regHull (stopHistory_const_stopHistory_const t y).symm
  rw [e]
  exact (measurable_hullAt t).comp (comap_measurable _)

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

omit mΩ in
/-- **The revealed union is known to the two stopped histories.** -/
theorem measurable_union_cfGlueMarks (q t : ℝ≥0) :
    Measurable[cfGlueMarks W VL VR ζ q t, hittingSigma] fun p : Ω × HistorySpace 0 0 =>
      hullAt q (killedHistory W VL VR ζ p.1) ∪ cfHullQ t p.2 := by
  have h1 : Measurable[cfGlueMarks W VL VR ζ q t, hittingSigma] fun p : Ω × HistorySpace 0 0 =>
      hullAt q (killedHistory W VL VR ζ p.1) :=
    ((measurable_hullAt_stopSigma q).comp (comap_measurable _)).mono le_sup_left le_rfl
  have h2 : Measurable[cfGlueMarks W VL VR ζ q t, hittingSigma] fun p : Ω × HistorySpace 0 0 => cfHullQ t p.2 :=
    ((measurable_image_negInv.comp (measurable_hullAt_stopSigma t)).comp (comap_measurable _)).mono le_sup_right
      le_rfl
  exact @measurable_union_hitting _ (cfGlueMarks W VL VR ζ q t) _ _ h1 h2

omit mΩ in
/-- The conditional Green variance of the revealed union is known to the two stopped histories. -/
theorem measurable_zeroGFFTestCov_cfGlueMarks (q t : ℝ≥0) (φ ψ : TestOn upperHalfPlaneOpens) :
    Measurable[cfGlueMarks W VL VR ζ q t] fun p : Ω × HistorySpace 0 0 =>
      QuantumZipper.zeroGFFTestCov (H \ relClosureH (hullAt q (killedHistory W VL VR ζ p.1) ∪ cfHullQ t p.2))
        φ ψ :=
  (measurable_zeroGFFTestCov_compl φ ψ).comp (measurable_union_cfGlueMarks q t)

omit mΩ in
/-- Avoiding a compact subset of `ℍ` is an event of the two stopped histories. -/
theorem measurableSet_disjoint_cfGlueMarks (q t : ℝ≥0) {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ H) :
    MeasurableSet[cfGlueMarks W VL VR ζ q t] {p : Ω × HistorySpace 0 0 |
      Disjoint K (relClosureH (hullAt q (killedHistory W VL VR ζ p.1) ∪ cfHullQ t p.2))} :=
  measurable_union_cfGlueMarks q t (measurableSet_disjoint_relClosureH hK hKH)

end Marks

/-! ### From the germ to the histories alone (the tower step) -/

section Tower

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **The tower step on an event of the coarse σ-algebra.** If `ℋ ≤ 𝒢 ≤ mΩ`, `D ∈ ℋ`, `X` is integrable and
`E[X | 𝒢] = R` almost surely on `D` for an `ℋ`-measurable `R`, then `E[X | ℋ] = R` almost surely on `D`. -/
theorem ae_condExp_eq_of_le_of_ae {ℋ 𝒢 : MeasurableSpace Ω} (hℋ𝒢 : ℋ ≤ 𝒢) (h𝒢 : 𝒢 ≤ mΩ) {D : Set Ω}
    (hD : MeasurableSet[ℋ] D) {X R : Ω → ℂ} (hX : Integrable X μ) (hR : StronglyMeasurable[ℋ] R)
    (hXR : ∀ᵐ ω ∂μ, ω ∈ D → μ[X | 𝒢] ω = R ω) : ∀ᵐ ω ∂μ, ω ∈ D → μ[X | ℋ] ω = R ω := by
  have hℋ : ℋ ≤ mΩ := hℋ𝒢.trans h𝒢
  have hD𝒢 : MeasurableSet[𝒢] D := hℋ𝒢 D hD
  -- `1_D R = 1_D E[X | 𝒢]` almost surely, so `1_D R` is integrable
  have hDR : D.indicator R =ᵐ[μ] D.indicator (μ[X | 𝒢]) := by
    filter_upwards [hXR] with ω hω
    by_cases hωD : ω ∈ D
    · rw [indicator_of_mem hωD, indicator_of_mem hωD, hω hωD]
    · rw [indicator_of_notMem hωD, indicator_of_notMem hωD]
  have hDRi : Integrable (D.indicator R) μ :=
    ((integrable_condExp (m := 𝒢) (f := X)).indicator (hℋ D hD)).congr hDR.symm
  have h1 : μ[D.indicator X | ℋ] =ᵐ[μ] D.indicator (μ[X | ℋ]) := condExp_indicator hX hD
  have h2 : μ[μ[D.indicator X | 𝒢] | ℋ] =ᵐ[μ] μ[D.indicator X | ℋ] := condExp_condExp_of_le hℋ𝒢 h𝒢
  have h3 : μ[D.indicator X | 𝒢] =ᵐ[μ] D.indicator (μ[X | 𝒢]) := condExp_indicator hX hD𝒢
  have h4 : μ[μ[D.indicator X | 𝒢] | ℋ] =ᵐ[μ] μ[D.indicator R | ℋ] :=
    condExp_congr_ae (h3.trans hDR.symm)
  have h5 : μ[D.indicator R | ℋ] = D.indicator R :=
    condExp_of_stronglyMeasurable hℋ (hR.indicator hD) hDRi
  filter_upwards [h1, h2, h4] with ω e1 e2 e4 hωD
  have := e4.symm.trans (e2.trans e1)
  rw [h5, indicator_of_mem hωD, indicator_of_mem hωD] at this
  exact this.symm

end Tower

section MarksLaw

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}
  {Ω₂ : Type u} {mΩ₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
  {h₂ : Ω₂ → DistOn upperHalfPlaneOpens} {W₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞}
  {k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)} [IsMarkovKernel k] {u₀ : ℂ → ℝ}

/-- **The conditional Gaussian law given the two stopped histories alone** (conditional helper: Astra's E.3, last
paragraph, "Both are functions of the two stopped histories. Forgetting the additional germs therefore preserves the
same Gaussian kernel"). In the setting of `isHistoryAvoidanceLocal_cfGlue`, let `m` be measurable for the two stopped
histories (`cfGlueMarks`) and suppose that some local-set mean `g` of the revealed union `A ∪ G` satisfies,
almost surely when `φ` is supported off `A ∪ G`, `g(φ) + ∫ 𝔥₀ φ = m` (this is what an explicit identification of the
union mean, as a function of the two stopped histories, provides). Then almost surely, when `φ` is supported off
`A ∪ G`, `E[e^{i (h, φ)} | σ(flow history stopped at q) ∨ σ(counterflow history stopped at t)]` equals
`e^{i m} · e^{−½ G_{ℍ∖(A∪G)}(φ, φ)}`. -/
theorem ae_condExp_cexp_cfGlueMarks (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hκ : 0 < κ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂)
    (hreg₂ : ∀ᵐ ω ∂P₂, ζ₂ ω = ⊤ ∧ W₂ 0 ω = 0 ∧ Continuous fun t => W₂ t ω)
    (hlaw : P.map (fun ω => cfField κ (h ω)) = P₂.map h₂)
    (hk : P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k)
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀) (q t : ℝ≥0)
    (φ : TestOn upperHalfPlaneOpens) {m : Ω × HistorySpace 0 0 → ℝ}
    (hm : Measurable[cfGlueMarks W VL VR ζ q t] m)
    (hid : ∃ g, IsLocalSetMean (fun p : Ω × HistorySpace 0 0 => hullAt q (killedHistory W VL VR ζ p.1) ∪
        cfHullQ t p.2) (fun p => cenT κ u₀ (cfField κ (h p.1)))
        (glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1)) g ∧
      ∀ᵐ p ∂(glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1)),
        tsupport φ ⊆ H \ (hullAt q (killedHistory W VL VR ζ p.1) ∪ cfHullQ t p.2) →
        g p φ + ∫ z, u₀ z * φ z = m p) :
    ∀ᵐ p ∂(glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1)),
      tsupport φ ⊆ H \ (hullAt q (killedHistory W VL VR ζ p.1) ∪ cfHullQ t p.2) →
      (glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1))[
          fun p' => Complex.exp (Complex.I * (h p'.1 φ : ℂ)) | cfGlueMarks W VL VR ζ q t] p =
        Complex.exp (Complex.I * (m p : ℂ)) *
          ((Real.exp (-(1 / 2) * QuantumZipper.zeroGFFTestCov
            (H \ (hullAt q (killedHistory W VL VR ζ p.1) ∪ cfHullQ t p.2)) φ φ) : ℝ) : ℂ) := by
  set μ := glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1) with hμ
  set U : Ω × HistorySpace 0 0 → Set ℂ := fun p => hullAt q (killedHistory W VL VR ζ p.1) ∪ cfHullQ t p.2
    with hUdef
  set F : Ω × HistorySpace 0 0 → DistOn upperHalfPlaneOpens := fun p => cenT κ u₀ (cfField κ (h p.1)) with hFdef
  have hX := hC.2.2.2.1
  have hYm : Measurable (killedHistory W VL VR ζ) := measurable_killedHistory hX
  have hF := isZeroBoundaryGFF_cenT_glue (k := k) hC hu₀
  have hAm : Measurable[_, hittingSigma] U :=
    measurable_union_hitting (((measurable_hullAt q).comp hYm).comp measurable_fst)
      ((measurable_cfHullQ t).comp measurable_snd)
  have hmark := isHistoryAvoidanceLocal_cfGlue hC hκ hζ hcf hreg₂ hlaw hk hu₀ q t
  have hloc := (isLocalSet_union_glue (k := k) hC hζ hcf hreg₂ hlaw hk hu₀ q t).2.2
  have hℋ := cfGlueMarks_le (Ω := Ω) q t hX
  obtain ⟨M, -, hM1, hM2⟩ := exists_condExp_germSigma_history hF hAm hℋ hmark
    (Eventually.of_forall fun p => union_relClosed q t _ p.2) φ
  obtain ⟨g, hg, hgm⟩ := hid
  have hgM := IsLocalSetMean.ae_eq_condExp_germSigma_sup hF hAm hloc hℋ hmark hg φ
  -- the explicit right side, measurable for the histories
  set v : Ω × HistorySpace 0 0 → ℝ := fun p => QuantumZipper.zeroGFFTestCov (H \ relClosureH (U p)) φ φ with hvdef
  set R : Ω × HistorySpace 0 0 → ℂ := fun p =>
    Complex.exp (Complex.I * (m p : ℂ)) * ((Real.exp (-(1 / 2) * v p) : ℝ) : ℂ) with hRdef
  have hvm : Measurable[cfGlueMarks W VL VR ζ q t] v := measurable_zeroGFFTestCov_cfGlueMarks q t φ φ
  have hRm : StronglyMeasurable[cfGlueMarks W VL VR ζ q t] R := by
    refine Measurable.stronglyMeasurable ?_
    exact (Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp hm))).mul
      (Complex.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul hvm)))
  -- the avoidance event of the histories
  set D : Set (Ω × HistorySpace 0 0) := {p | Disjoint (tsupport φ) (relClosureH (U p))} with hDdef
  have hD : MeasurableSet[cfGlueMarks W VL VR ζ q t] D :=
    measurableSet_disjoint_cfGlueMarks q t φ.hasCompactSupport.isCompact φ.tsupport_subset
  have hDiff : ∀ p, p ∈ D ↔ tsupport φ ⊆ H \ U p := by
    intro p
    obtain ⟨hsub, hopen⟩ := union_relClosed q t (killedHistory W VL VR ζ p.1) p.2
    have e : relClosureH (U p) = U p := relClosureH_eq hsub hopen
    show Disjoint (tsupport φ) (relClosureH (U p)) ↔ _
    rw [e, subset_sdiff]
    exact ⟨fun h => ⟨φ.tsupport_subset, h⟩, fun h => h.2⟩
  -- the law given the germ and the histories, pulled back to the uncentred field
  set c : ℂ := Complex.exp (Complex.I * ((∫ z, u₀ z * φ z : ℝ) : ℂ)) with hc
  have e : (fun p : Ω × HistorySpace 0 0 => Complex.exp (Complex.I * (h p.1 φ : ℂ))) =
      c • fun p => Complex.exp (Complex.I * (F p φ : ℂ)) := by
    funext p
    simp only [Pi.smul_apply, smul_eq_mul, hc, hFdef, cenT_cfField, ← Complex.exp_add]
    rw [show h p.1 - smoothDist upperHalfPlaneOpens u₀ = centredField h u₀ p.1 from rfl,
      centredField_apply h hu₀.1 p.1 φ]
    congr 1
    push_cast
    ring
  have hpull := condExp_smul (μ := μ) c (fun p : Ω × HistorySpace 0 0 => Complex.exp (Complex.I * (F p φ : ℂ)))
    (germSigma U F ⊔ cfGlueMarks W VL VR ζ q t)
  rw [← e] at hpull
  have hgerm : ∀ᵐ p ∂μ, p ∈ D → μ[fun p' => Complex.exp (Complex.I * (h p'.1 φ : ℂ)) |
      germSigma U F ⊔ cfGlueMarks W VL VR ζ q t] p = R p := by
    filter_upwards [hM1, hM2, hgM, hgm, hpull] with p h1 h2 h3 h4 h5 hpD
    rw [h5, Pi.smul_apply, ← h2, smul_eq_mul, hRdef]
    simp only
    have hMp : M p = m p - ∫ z, u₀ z * φ z := by
      rw [h1, ← h3, ← h4 ((hDiff p).1 hpD)]
      ring
    rw [hMp, hc, ← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have hXi : Integrable (fun p : Ω × HistorySpace 0 0 => Complex.exp (Complex.I * (h p.1 φ : ℂ))) μ :=
    Integrable.of_bound (GFF.measurable_exp_I_mul ((Sobolev.measurable_distOn_apply φ).comp
      (hC.2.1.comp measurable_fst))).aestronglyMeasurable 1
      (Eventually.of_forall fun p => (Complex.norm_exp_I_mul_ofReal _).le)
  have htow := ae_condExp_eq_of_le_of_ae le_sup_right (sup_le (germSigma_le hAm hF.measurable) hℋ) hD hXi hRm hgerm
  filter_upwards [htow] with p hp hsupp
  rw [hp ((hDiff p).2 hsupp), hRdef]
  obtain ⟨hsub, hopen⟩ := union_relClosed q t (killedHistory W VL VR ζ p.1) p.2
  simp only [hvdef, hUdef, relClosureH_eq hsub hopen]

end MarksLaw

/-! ### The two enlarged filtrations -/

section Filt

variable {nL nR : ℕ}

theorem stopHistory_const_comp_le {r r' : ℝ≥0} (hr : r ≤ r') (y : HistorySpace nL nR) :
    Sec4.stopHistory (fun _ => r) (Sec4.stopHistory (fun _ => r') y) = Sec4.stopHistory (fun _ => r) y := by
  simp only [Sec4.stopHistory, Prod.mk.injEq, true_and]
  funext p
  by_cases h1 : dyadicTime p ≤ r
  · simp only [h1, ↓reduceIte, h1.trans hr]
  · simp only [h1, ↓reduceIte]

/-- The σ-algebras of the stopped histories increase with the stopping time. -/
theorem stopSigma_mono {r r' : ℝ≥0} (hr : r ≤ r') :
    stopSigma (nL := nL) (nR := nR) r ≤ stopSigma r' := by
  have e : Sec4.stopHistory (nL := nL) (nR := nR) (fun _ => r) =
      Sec4.stopHistory (fun _ => r) ∘ Sec4.stopHistory (fun _ => r') :=
    funext fun y => (stopHistory_const_comp_le hr y).symm
  rw [stopSigma, e, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono (Sec4.measurable_stopHistory measurable_const).comap_le

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

omit mΩ in
theorem cfGlueMarks_mono {q q' t t' : ℝ≥0} (hq : q ≤ q') (ht : t ≤ t') :
    cfGlueMarks W VL VR ζ q t ≤ cfGlueMarks W VL VR ζ q' t' :=
  sup_le_sup (MeasurableSpace.comap_mono (stopSigma_mono hq)) (MeasurableSpace.comap_mono (stopSigma_mono ht))

/-- **The enlarged filtration of the counterflow given the flow prefix** (Lemma 4.7's direction): the flow history
stopped at the fixed time `q`, and the counterflow history up to time `t`. -/
def cfFilt47 (hX : IsMeasurableKilledDriving W VL VR ζ) (q : ℝ≥0) :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace (Ω × HistorySpace 0 0)) where
  seq t := cfGlueMarks W VL VR ζ q t
  mono' _ _ ht := cfGlueMarks_mono le_rfl ht
  le' t := cfGlueMarks_le q t hX

/-- **The enlarged filtration of the flow line given the counterflow prefix** (Proposition 4.9's direction): the
counterflow history stopped at the fixed time `s`, and the flow history up to time `q`. -/
def cfFilt49 (hX : IsMeasurableKilledDriving W VL VR ζ) (s : ℝ≥0) :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace (Ω × HistorySpace 0 0)) where
  seq q := cfGlueMarks W VL VR ζ q s
  mono' _ _ hq := cfGlueMarks_mono hq le_rfl
  le' q := cfGlueMarks_le q s hX

theorem cfFilt47_apply (hX : IsMeasurableKilledDriving W VL VR ζ) (q t : ℝ≥0) :
    cfFilt47 hX q t = cfGlueMarks W VL VR ζ q t := rfl

theorem cfFilt49_apply (hX : IsMeasurableKilledDriving W VL VR ζ) (s q : ℝ≥0) :
    cfFilt49 hX s q = cfGlueMarks W VL VR ζ q s := rfl

end Filt

end InteractingSLE.Sec5.CrossCond
