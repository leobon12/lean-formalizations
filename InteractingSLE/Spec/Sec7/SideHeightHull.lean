/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideHeightShift
import InteractingSLE.Spec.Sec7.SideHeightGeom
import InteractingSLE.Spec.Coupling.WholeField2Kernel
import InteractingSLE.WangWu.PrefixLocalMean

/-!
# A flow line's hull mean in the original coordinate

Packet PROVE-SIDEHEIGHT, item (a) of `planning/handoffs/PROVE-PRIMEEND2.md` ("single flow-line means in pointwise
form"). For a coupling `(W, V)` of the force word of a flow line from `x` with the translated field
`h' = h(· + x) + c` (frozen `IsOptionalHullCoupling`, `IsTranslateAddConst`), a stopping time `τ < ζ` of the frozen
driving filtration and the translated hull `A = x + K_τ`:

* `A` is a local set of the centred original field `h⁰ = h − 𝔥₀` (`isLocalSet_flowHull`, through
  `IsLocalSet.translate`), with the history marking of the frozen driving filtration
  (`isHistoryAvoidanceLocal_flowHull`,
  the capacity coding theorem `WholeField.isHistoryAvoidanceLocal_of_capacity` with the translated clock);
* **`ae_apply_eq_of_isLocalSetMean_flowHull`**: for every local-set mean `g` of `A`, almost surely, for every test
  function `φ` supported in `ℍ \ A`, `g(φ) = ∫ (𝔥_τ(· − x) − c − 𝔥₀) φ`, with `𝔥_τ` the frozen coupling mean
  (`couplingMean`).

No germ σ-algebra is translated: the frozen kernel is transported to `h⁰` at the level of the stopped history `𝓕_τ`
(`h⁰(φ) = h'(φ(· + x)) − c∫φ − ∫ 𝔥₀ φ`), and the germ step (`WholeField.ae_condExp_germSigma_history_eq`) is run in
the original coordinate (`ae_condExp_germSigma_eq_of_freq`, the second half of `WholeField.ae_condExp_germSigma_hull_eq`
for an arbitrary kernel).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Sec7

namespace SideHeight

open QuantumZipper (H fwdMap fwdHull)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open LocalSets

/-! ### The germ-and-history mean from a kernel at all frequencies -/

section Generic

variable {Ω : Type u} {ℋ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {A : Ω → Set ℂ} {h : Ω → DistOn upperHalfPlaneOpens}

/-- **The germ-and-history conditional mean from a frequency kernel.** Let `A` satisfy the history-marked avoidance
criterion for the marks `ℋ`. If, on the event `{supp φ ∩ A = ∅}` (almost surely an event `G` of `ℋ`), the conditional
characteristic function of `(h, φ)` given `ℋ` is Gaussian with mean `M` and variance `σ²_{ℍ∖A}(φ)` at every frequency,
then `E[(h, φ) | 𝒜 ∨ ℋ] = M` there. (`M` need not be measurable: an `ℋ`-measurable version is recovered from the
conditional characteristic functions, `WholeField.meanOfCharFun`.) -/
theorem ae_condExp_germSigma_eq_of_freq (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hA : Measurable[mΩ, hittingSigma] A) (hℋ : ℋ ≤ mΩ) (hloc : WholeField.IsHistoryAvoidanceLocal ℋ A h P)
    (hAc : ∀ᵐ ω ∂P, A ω ⊆ H ∧ IsOpen (H \ A ω)) (φ : TestOn upperHalfPlaneOpens) {G : Set Ω}
    (hG : MeasurableSet[ℋ] G) (hGiff : ∀ᵐ ω ∂P, (ω ∈ G ↔ Disjoint (tsupport φ) (A ω))) {M : Ω → ℝ}
    (hfreq : ∀ c : ℝ, ∀ᵐ ω ∂P, Disjoint (tsupport φ) (A ω) →
      (P[fun ω' => Complex.exp (Complex.I * ((c * h ω' φ : ℝ) : ℂ)) | ℋ]) ω =
        Complex.exp (Complex.I * ((c * M ω : ℝ) : ℂ)) *
          ((Real.exp (-(1 / 2) * (c ^ 2 * QuantumZipper.zeroGFFTestCov (H \ A ω) φ φ)) : ℝ) : ℂ)) :
    ∀ᵐ ω ∂P, Disjoint (tsupport φ) (A ω) → (P[fun ω' => h ω' φ | germSigma A h ⊔ ℋ]) ω = M ω := by
  set ψ : ℕ → Ω → ℂ := fun n =>
    P[fun ω' => Complex.exp (Complex.I * ((1 / ((n : ℝ) + 1) * h ω' φ : ℝ) : ℂ)) | ℋ] with hψ_def
  have hψm : ∀ n, StronglyMeasurable[ℋ] (ψ n) := fun n => stronglyMeasurable_condExp
  have hmm : Measurable[ℋ] (WholeField.meanOfCharFun ψ) := WholeField.measurable_meanOfCharFun hψm
  have hmeq : ∀ᵐ ω ∂P, Disjoint (tsupport φ) (A ω) → WholeField.meanOfCharFun ψ ω = M ω := by
    filter_upwards [ae_all_iff.2 fun n : ℕ => hfreq (1 / ((n : ℝ) + 1))] with ω hω hdis
    exact WholeField.meanOfCharFun_eq fun n => hω n hdis
  have hkern : ∀ c : ℝ, ∀ᵐ ω ∂P, ω ∈ G →
      (P[fun ω' => Complex.exp (Complex.I * ((c * h ω' φ : ℝ) : ℂ)) | ℋ]) ω =
        Complex.exp (Complex.I * ((c * WholeField.meanOfCharFun ψ ω : ℝ) : ℂ)) *
          ((Real.exp (-(1 / 2) * (c ^ 2 * QuantumZipper.zeroGFFTestCov (H \ A ω) φ φ)) : ℝ) : ℂ) := by
    intro c
    filter_upwards [hfreq c, hmeq, hGiff] with ω h1 h2 h3 hωG
    have hdis : Disjoint (tsupport φ) (A ω) := h3.1 hωG
    rw [h2 hdis]
    exact h1 hdis
  obtain ⟨k1, -⟩ := WholeField.ae_condExp_germSigma_history_eq hh hA hℋ hloc hAc φ hG hmm hkern
  filter_upwards [k1, hmeq, hGiff] with ω h1 h2 h3 hdis
  rw [h1 (h3.2 hdis), h2 hdis]

end Generic

/-! ### The coupling mean is harmonic off the hull -/

section Harmonic

variable {κ : ℝ} {u : ℂ → ℝ}

/-- `𝔥_t = 𝔥⁰_t ∘ f_t − χ arg f_t′` is harmonic off the hull, for a continuous driver. -/
theorem harmonicOnNhd_couplingMean {W : ℝ → ℝ} (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t)
    (hu : InnerProductSpace.HarmonicOnNhd u H) :
    InnerProductSpace.HarmonicOnNhd (couplingMean κ W t u) (H \ fwdHull W t) := by
  intro z hz
  have hU : IsOpen (H \ fwdHull W t) := QuantumZipper.FwdHolo.isOpen_compl_fwdHull hW ht
  have hfa : AnalyticAt ℂ (fwdMap W t) z :=
    (QuantumZipper.FwdHolo.differentiableOn_fwdMap hW ht).analyticAt (hU.mem_nhds hz)
  have hLa : AnalyticAt ℂ (QuantumZipper.logDerivFwd W t) z :=
    (isDerivLog_fwdMap hW ht).1.analyticAt (hU.mem_nhds hz)
  have h1 : InnerProductSpace.HarmonicAt (fun z => u (fwdMap W t z)) z :=
    QuantumZipper.FieldLawler.fl_harmonicAt_comp hfa (hu _ (QuantumZipper.FwdHolo.mapsTo_fwdMap hW ht hz))
  have h2 : InnerProductSpace.HarmonicAt (fun z => QuantumZipper.chiC κ * (QuantumZipper.logDerivFwd W t z).im) z := by
    have := hLa.harmonicAt_im.const_smul (c := QuantumZipper.chiC κ)
    have e : (QuantumZipper.chiC κ • fun z => (QuantumZipper.logDerivFwd W t z).im) =
        fun z => QuantumZipper.chiC κ * (QuantumZipper.logDerivFwd W t z).im := by
      funext z; rw [Pi.smul_apply, smul_eq_mul]
    rwa [e] at this
  exact h1.sub h2

/-- `𝔥_t` is harmonic off the hull for a driver continuous before the lifetime, at times `t < ζ`. -/
theorem harmonicOnNhd_couplingMean_rpath {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} (hwc : ContinuousOn w {t | (t : ℝ≥0∞) < ζ})
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) (hu : InnerProductSpace.HarmonicOnNhd u H) :
    InnerProductSpace.HarmonicOnNhd (couplingMean κ (fun s : ℝ => w s.toNNReal) t u)
      (H \ fwdHull (fun s : ℝ => w s.toNNReal) t) := by
  obtain ⟨t₂, htt₂, ht₂⟩ := exists_real_btwn_of_lt ht
  have hW : Continuous (frozenDrive w t₂) := continuous_frozenDrive_of_lt hwc ht₂
  have heq : EqOn (fun s : ℝ => w s.toNNReal) (frozenDrive w t₂) (Icc 0 t) := fun r hr =>
    (frozenDrive_eq ⟨hr.1, hr.2.trans htt₂.le⟩).symm
  have hK : fwdHull (fun s : ℝ => w s.toNNReal) t = fwdHull (frozenDrive w t₂) t :=
    fwdHull_eq_of_eqOn t.coe_nonneg htt₂ fun r hr => (frozenDrive_eq hr).symm
  have hcm : couplingMean κ (fun s : ℝ => w s.toNNReal) t u = couplingMean κ (frozenDrive w t₂) t u := by
    funext z
    unfold couplingMean
    rw [Ito.fwdMap_congr_of_eqOn_of_le heq le_rfl, Ito.logDerivFwd_congr_of_eqOn heq t.coe_nonneg le_rfl]
  rw [hcm, hK]
  exact harmonicOnNhd_couplingMean hW t.coe_nonneg hu

/-- The translated coupling mean `𝔥_t(· − x) − c − 𝔥₀` is harmonic off the translated hull. -/
theorem harmonicOnNhd_flowMean {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} (hwc : ContinuousOn w {t | (t : ℝ≥0∞) < ζ})
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) (hu : InnerProductSpace.HarmonicOnNhd u H) (x c : ℝ) {u₀ : ℂ → ℝ}
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H) :
    InnerProductSpace.HarmonicOnNhd
      (fun z => couplingMean κ (fun s : ℝ => w s.toNNReal) t u (z - x) - c - u₀ z)
      (H \ (fun z : ℂ => z + x) '' fwdHull (fun s : ℝ => w s.toNNReal) t) := by
  intro z hz
  have hz' : z - x ∈ H \ fwdHull (fun s : ℝ => w s.toNNReal) t := by
    refine ⟨?_, fun hK => hz.2 ⟨z - x, hK, by ring⟩⟩
    have := add_real_mem_H' hz.1 (-x)
    simpa [sub_eq_add_neg] using this
  have h1 := Exist.harmonicAt_comp_add_const (a := ((-x : ℝ) : ℂ))
    (f := couplingMean κ (fun s : ℝ => w s.toNNReal) t u) (z := z)
    (by rw [show z + ((-x : ℝ) : ℂ) = z - x by push_cast; ring]
        exact harmonicOnNhd_couplingMean_rpath hwc ht hu _ hz')
  have e : (fun w' => couplingMean κ (fun s : ℝ => w s.toNNReal) t u (w' + ((-x : ℝ) : ℂ))) =
      fun w' => couplingMean κ (fun s : ℝ => w s.toNNReal) t u (w' - x) := by
    funext w'
    congr 1
    push_cast
    ring
  rw [e] at h1
  exact (h1.sub (InnerProductSpace.harmonicAt_const _)).sub (hu₀ z hz.1)

end Harmonic

/-! ### The coupling of a flow line, read in the original coordinate -/

section Flow

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {h h' : Ω → DistOn upperHalfPlaneOpens} {x c : ℝ} {u₀ u₀' : ℂ → ℝ}

/-- The test function `φ(· + x)` has support `supp φ − x`. -/
theorem tsupport_shiftTest (x : ℝ) (φ : TestOn upperHalfPlaneOpens) :
    tsupport (WholeField.shiftTest x φ) = (fun z : ℂ => z + x) ⁻¹' tsupport φ := by
  have e : ⇑(WholeField.shiftTest x φ) = fun z => φ (z + x) := funext (WholeField.shiftTest_apply x φ)
  rw [e]
  exact tsupport_comp_eq_preimage (⇑φ) (Homeomorph.addRight (x : ℂ))

theorem disjoint_tsupport_shiftTest_iff (x : ℝ) (φ : TestOn upperHalfPlaneOpens) (K : Set ℂ) :
    Disjoint (tsupport (WholeField.shiftTest x φ)) K ↔ Disjoint (tsupport φ) ((fun z : ℂ => z + x) '' K) := by
  rw [tsupport_shiftTest]
  constructor
  · intro hd
    refine Set.disjoint_left.2 fun z hz ⟨w, hw, e⟩ => Set.disjoint_left.1 hd (show w + x ∈ tsupport φ from ?_) hw
    simp only at e
    rwa [e]
  · intro hd
    exact Set.disjoint_left.2 fun w hw hwK => Set.disjoint_left.1 hd hw ⟨w, hwK, rfl⟩

omit mΩ in
/-- **The centred original field is the translate of the centred coupling field**: `h⁰ = h'⁰(· − x)` when
`h' = h(· + x) + c` and `𝔥₀′ = 𝔥₀(· + x) + c` on `ℍ`. -/
theorem centredField_eq_flowField (htrans : ∀ ω, IsTranslateAddConst x c (h ω) (h' ω))
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H) (hu₀' : InnerProductSpace.HarmonicOnNhd u₀' H)
    (hrel : EqOn u₀' (fun z => u₀ (z + x) + c) H) (ω : Ω) :
    WholeField.centredField h u₀ ω = Exist.flowField (-x) 0 (WholeField.centredField h' u₀' ω) := by
  ext φ
  set ψ := WholeField.shiftTest x φ with hψ
  have hψf : ⇑ψ = fun z => φ (z + x) := funext (WholeField.shiftTest_apply x φ)
  rw [flowField_neg_apply, WholeField.centredField_apply h hu₀ ω φ, WholeField.centredField_apply h' hu₀' ω ψ,
    htrans ω φ ψ (WholeField.shiftTest_apply x φ)]
  have hu₀c : ContinuousOn (fun z => u₀ (z + x)) H := fun z hz =>
    ((hu₀ _ (add_real_mem_H' hz x)).1.continuousAt.comp (f := fun w : ℂ => w + x)
      (by fun_prop : Continuous fun w : ℂ => w + x).continuousAt).continuousWithinAt
  have hi1 : Integrable fun z => u₀ (z + x) * ψ z := WholeField.integrable_mul_testOn hu₀c ψ ψ.tsupport_subset
  have hi2 : Integrable fun z => c * ψ z :=
    (ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport).const_mul c
  have h1 : ∫ z, u₀' z * ψ z = ∫ z, (u₀ (z + x) * ψ z + c * ψ z) := by
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    by_cases hz : z ∈ H
    · simp only
      rw [hrel hz]
      ring
    · have : ψ z = 0 := ψ.zero_on_compl hz
      simp [this]
  have h2 : ∫ z, u₀ (z + x) * ψ z = ∫ z, u₀ z * φ z := by
    rw [hψf]
    exact integral_add_right_eq_self (fun z => u₀ z * φ z) (x : ℂ)
  rw [h1, integral_add hi1 hi2, h2, integral_const_mul]
  ring

omit [IsProbabilityMeasure P] in
/-- **The translated hull is a local set of the centred original field.** -/
theorem isLocalSet_flowHull (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h')
    (htrans : ∀ ω, IsTranslateAddConst x c (h ω) (h' ω)) (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hu₀' : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀')
    (hrel : EqOn u₀' (fun z => u₀ (z + x) + c) H) (hX : IsMeasurableKilledDriving W VL VR ζ)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime (drivingFiltration P hX) τ)
    (hτζ : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζ ω) :
    IsLocalSet (fun ω => (fun z : ℂ => z + x) '' fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0))
      (WholeField.centredField h u₀) P := by
  obtain ⟨-, -, -, hX', hker⟩ := hC
  have h1 := WholeField.IsLocalSet.sub_dist (hker τ hτ hτζ).1 (WholeField.isHarmonicDistOn_smoothDist hu₀'.1)
  have h2 := IsLocalSet.translate h1 x
  have e : (fun ω => Exist.flowField (-x) 0 (h' ω - SupercriticalConformalCovariance.GM24.smoothDist
      upperHalfPlaneOpens u₀')) = WholeField.centredField h u₀ :=
    funext fun ω => (centredField_eq_flowField htrans hu₀ hu₀'.1 hrel ω).symm
  rwa [e] at h2

/-- **History marking of the translated hull** for the marks `𝓕_τ` of the frozen driving filtration (the capacity
coding theorem with the translated clock `S ↦ hcap(S − x)/2`). -/
theorem isHistoryAvoidanceLocal_flowHull (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h')
    (hκ : 0 < κ) (htrans : ∀ ω, IsTranslateAddConst x c (h ω) (h' ω))
    (hh0 : IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField h u₀) P)
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hu₀' : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀')
    (hrel : EqOn u₀' (fun z => u₀ (z + x) + c) H) (hX : IsMeasurableKilledDriving W VL VR ζ)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime (drivingFiltration P hX) τ)
    (hτζ : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζ ω) {A : Ω → Set ℂ} (hA : Measurable[mΩ, hittingSigma] A)
    (hAK : ∀ᵐ ω ∂P, A ω =
      (fun z : ℂ => z + x) '' fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)) :
    WholeField.IsHistoryAvoidanceLocal hτ.measurableSpace A (WholeField.centredField h u₀) P := by
  have hh0m := hh0.measurable
  have hE := hC.1
  by_cases hseed : ForceWord.ThresholdCondition ρL ρR 0 xL xR
  · exfalso
    have hF : ∀ᵐ ω ∂P, False := by
      filter_upwards [hE.2.2.2.2, hτζ] with ω hp hlt
      rw [WangWu.IsIntegratedSLEPath.lifetime_eq_zero_of_threshold hp hseed] at hlt
      exact ENNReal.not_lt_zero hlt
    obtain ⟨_, h⟩ := hF.exists
    exact h
  have : (drivingFiltration P hX).IsRightContinuous := Ito.isRightContinuous_usualAugmentation _ _
  obtain ⟨σ, hσ, -⟩ := WholeField.exists_isAnnouncingSeq_of_adapted (𝓖 := drivingFiltration P hX)
    (B := B) (κ := κ) (xL := xL) (xR := xR) (fun s hs h0 => Ito.measurableSet_usualAugmentation_of_null hs h0 0)
    (Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (Coupling.adaptedBefore_killedDriving_W hX))
    (fun i => Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (Coupling.adaptedBefore_killedDriving_VL hX i))
    (fun i => Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (Coupling.adaptedBefore_killedDriving_VR hX i))
    hE.2.2.2.2 (hE.ae_tendsto_threshold hκ) hseed
  have hΦ : Measurable[hittingSigma] fun S : Set ℂ =>
      WholeField.hullClock ((fun z : ℂ => z + ((-x : ℝ) : ℂ)) '' S) :=
    @Measurable.comp _ _ _ hittingSigma hittingSigma _ _ _ WholeField.measurable_hullClock
      (measurable_image_add (-x))
  refine WholeField.isHistoryAvoidanceLocal_of_capacity
    (K := fun t ω => (fun z : ℂ => z + x) '' fwdHull (fun s : ℝ => W s.toNNReal ω) t) hh0m hΦ ?_ hσ ?_ hτ hτζ
    hA hAK
  · filter_upwards [hE.2.2.2.2] with ω hp t ht
    show WholeField.hullClock ((fun z : ℂ => z + ((-x : ℝ) : ℂ)) ''
      ((fun z : ℂ => z + x) '' fwdHull (fun s : ℝ => W s.toNNReal ω) t)) = t
    rw [image_add_neg_image_add]
    exact WholeField.hullClock_fwdHull_rpath hp.2.2.2.1 hp.1 ht
  · intro S hS hSζ
    have hloc := isLocalSet_flowHull hC htrans hu₀ hu₀' hrel hX hS hSζ
    obtain ⟨A', hA'm, hA'e, hA'loc⟩ := WholeField.IsLocalSet.exists_measurable_version hloc hh0m
    exact ⟨A', hA'm, hA'e, IsLocalSet.isMarkedAvoidanceLocal hh0m hA'm hA'loc⟩

/-- **The hull mean of a flow line in the original coordinate** (PRIMEEND2 item (a)). For a coupling of the force word
with the translated field `h' = h(· + x) + c`, a stopping time `τ < ζ` of the frozen driving filtration, a
hitting-measurable version `A` of the translated hull `x + K_τ`, every local-set mean `g` of `A` for the centred
original field `h⁰ = h − 𝔥₀` and bounded harmonic extensions `u ω` of the force data at `τ`: almost surely, for every
test function `φ` supported in `ℍ \ A`, `g(φ) = ∫ (𝔥_τ(· − x) − c − 𝔥₀) φ`. -/
theorem ae_apply_eq_of_isLocalSetMean_flowHull (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h')
    (hκ : 0 < κ) (htrans : ∀ ω, IsTranslateAddConst x c (h ω) (h' ω))
    (hh0 : IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField h u₀) P)
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hu₀' : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀')
    (hrel : EqOn u₀' (fun z => u₀ (z + x) + c) H) (hX : IsMeasurableKilledDriving W VL VR ζ)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime (drivingFiltration P hX) τ)
    (hτζ : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζ ω) {A : Ω → Set ℂ} (hA : Measurable[mΩ, hittingSigma] A)
    (hAK : ∀ᵐ ω ∂P, A ω =
      (fun z : ℂ => z + x) '' fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0))
    {g : Ω → DistOn upperHalfPlaneOpens} (hg : IsLocalSetMean A (WholeField.centredField h u₀) P g)
    {u : Ω → ℂ → ℝ}
    (hu : ∀ ω, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)
        (fun i => VR i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω))
      (forceJumpSet (fun i => VL i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)
        (fun i => VR i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)) (u ω)) :
    ∀ᵐ ω ∂P, ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A ω →
      g ω φ = ∫ z, (couplingMean κ (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0) (u ω) (z - x) - c -
        u₀ z) * φ z := by
  classical
  set h0 := WholeField.centredField h u₀ with hh0_def
  have hℋ : hτ.measurableSpace ≤ mΩ := hτ.measurableSpace_le
  have hloc : IsLocalSet A h0 P :=
    Coupling.IsLocalSet.congr_set (isLocalSet_flowHull hC htrans hu₀ hu₀' hrel hX hτ hτζ) hAK
  have hmark := isHistoryAvoidanceLocal_flowHull hC hκ htrans hh0 hu₀ hu₀' hrel hX hτ hτζ hA hAK
  have hE := hC.1
  obtain ⟨-, -, -, hX', hker⟩ := hC
  have hker' := hker τ hτ hτζ
  have hAc : ∀ᵐ ω ∂P, A ω ⊆ H ∧ IsOpen (H \ A ω) := hloc.2.1
  have hτζ' : ∀ᵐ ω ∂P, (((τ ω).untopD 0 : ℝ≥0) : ℝ≥0∞) < ζ ω :=
    hτζ.mono fun ω h => Coupling.coe_untopD_lt_zeta h
  -- the candidate mean
  set m : Ω → ℂ → ℝ := fun ω z =>
    couplingMean κ (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0) (u ω) (z - x) - c - u₀ z with hm_def
  have hmharm : ∀ᵐ ω ∂P, InnerProductSpace.HarmonicOnNhd (m ω) (H \ A ω) := by
    filter_upwards [hE.2.2.2.2, hτζ', hAK] with ω hp hlt hAω
    rw [hAω]
    exact harmonicOnNhd_flowMean hp.2.2.2.1 hlt (hu ω).1 x c hu₀
  refine WangWu.ae_forall_apply_eq_of_forall_ae (m := m) hg.2.1 (hAc.mono fun ω h => h.2) hmharm fun φ => ?_
  -- the seed is admissible (otherwise there is no stopping time below the lifetime)
  by_cases hseed : ForceWord.ThresholdCondition ρL ρR 0 xL xR
  · have hF : ∀ᵐ ω ∂P, False := by
      filter_upwards [hE.2.2.2.2, hτζ] with ω hp hlt
      rw [WangWu.IsIntegratedSLEPath.lifetime_eq_zero_of_threshold hp hseed] at hlt
      exact ENNReal.not_lt_zero hlt
    filter_upwards [hF] with ω hω
    exact hω.elim
  have : (drivingFiltration P hX).IsRightContinuous := Ito.isRightContinuous_usualAugmentation _ _
  obtain ⟨σ, hσ, -⟩ := WholeField.exists_isAnnouncingSeq_of_adapted (𝓖 := drivingFiltration P hX)
    (B := B) (κ := κ) (xL := xL) (xR := xR) (fun s hs h0 => Ito.measurableSet_usualAugmentation_of_null hs h0 0)
    (Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (Coupling.adaptedBefore_killedDriving_W hX))
    (fun i => Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (Coupling.adaptedBefore_killedDriving_VL hX i))
    (fun i => Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (Coupling.adaptedBefore_killedDriving_VR hX i))
    hE.2.2.2.2 (hE.ae_tendsto_threshold hκ) hseed
  -- the translated test function and the event `{supp φ ∩ A = ∅}` of `𝓕_τ`
  set ψ := WholeField.shiftTest x φ with hψ_def
  have hψf : ⇑ψ = fun z => φ (z + x) := funext (WholeField.shiftTest_apply x φ)
  obtain ⟨G, hGm, hGiff⟩ := WholeField.exists_measurableSet_ae_iff_disjoint hE hX hσ hτ hτζ
    ψ.hasCompactSupport.isCompact ψ.tsupport_subset
  have hGiff' : ∀ᵐ ω ∂P, (ω ∈ G ↔ Disjoint (tsupport φ) (A ω)) := by
    filter_upwards [hGiff, hAK] with ω h1 h2
    rw [h1, h2, disjoint_tsupport_shiftTest_iff]
  -- the field identity `h⁰(φ) = h'(ψ) − a`
  set a : ℝ := c * (∫ z, ψ z) + ∫ z, u₀ z * φ z with ha_def
  have hfield : ∀ ω, h0 ω φ = h' ω ψ - a := fun ω => by
    rw [hh0_def, WholeField.centredField_apply h hu₀ ω φ, htrans ω φ ψ (WholeField.shiftTest_apply x φ), ha_def]
    ring
  -- the kernel at every frequency
  have hfreq : ∀ c' : ℝ, ∀ᵐ ω ∂P, Disjoint (tsupport φ) (A ω) →
      (P[fun ω' => Complex.exp (Complex.I * ((c' * h0 ω' φ : ℝ) : ℂ)) | hτ.measurableSpace]) ω =
        Complex.exp (Complex.I * ((c' * ∫ z, m ω z * φ z : ℝ) : ℂ)) *
          ((Real.exp (-(1 / 2) * (c' ^ 2 * QuantumZipper.zeroGFFTestCov (H \ A ω) φ φ)) : ℝ) : ℂ) := by
    intro c'
    have hk := hker'.2 u hu (c' • ψ)
    have hsm := condExp_smul (μ := P) (Complex.exp (-(Complex.I * ((c' * a : ℝ) : ℂ))))
      (fun ω' => Complex.exp (Complex.I * (h' ω' (c' • ψ) : ℂ))) hτ.measurableSpace
    have e1 : (fun ω' => Complex.exp (Complex.I * ((c' * h0 ω' φ : ℝ) : ℂ))) =
        Complex.exp (-(Complex.I * ((c' * a : ℝ) : ℂ))) •
          fun ω' => Complex.exp (Complex.I * (h' ω' (c' • ψ) : ℂ)) := by
      funext ω'
      rw [Pi.smul_apply, smul_eq_mul, ← Complex.exp_add, hfield, map_smul, smul_eq_mul]
      congr 1
      push_cast
      ring
    filter_upwards [hk, hsm, hAK, hE.2.2.2.2, hτζ', hmharm] with ω hkω hsmω hAω hp hsζ hmω hdis
    have hdisK : Disjoint (tsupport ψ) (fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)) := by
      rw [disjoint_tsupport_shiftTest_iff, ← hAω]
      exact hdis
    have hdisc := hdisK.mono_left (WholeField.tsupport_smul_testOn_subset c' ψ)
    have hen := WholeField.loewnerGreenEnergy_rpath_eq_zeroGFFTestCov hp.2.2.2.1 hp.1 hsζ ψ hdisK
    have hcov : QuantumZipper.zeroGFFTestCov
        (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)) ψ ψ =
        QuantumZipper.zeroGFFTestCov (H \ A ω) φ φ := by
      rw [hψf, hAω, ← WholeField.preimage_add_H_diff_image x]
      exact WholeField.zeroGFFTestCov_comp_add (x : ℂ) _ φ.continuous φ.continuous
    -- the mean
    have hsupp : tsupport φ ⊆ H \ A ω := fun z hz => ⟨φ.tsupport_subset hz, fun hzA =>
      Set.disjoint_left.1 hdis hz hzA⟩
    have hmc : ContinuousOn (m ω) (H \ A ω) := fun z hz => (hmω z hz).1.continuousAt.continuousWithinAt
    set cm := couplingMean κ (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0) (u ω) with hcm
    have hmean : ∫ z, m ω z * φ z = (∫ z, cm z * ψ z) - a := by
      have hcmc : ContinuousOn (fun z => cm (z - x)) (H \ A ω) := by
        have : ContinuousOn (fun z => m ω z + c + u₀ z) (H \ A ω) :=
          (hmc.add continuousOn_const).add fun z hz => (hu₀ z hz.1).1.continuousAt.continuousWithinAt
        refine this.congr fun z _ => ?_
        simp only [hm_def, hcm]
        ring
      have hi1 : Integrable fun z => cm (z - x) * φ z := WholeField.integrable_mul_testOn hcmc φ hsupp
      have hi2 : Integrable fun z => c * φ z :=
        (φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport).const_mul c
      have hi3 : Integrable fun z => u₀ z * φ z :=
        WholeField.integrable_mul_testOn (fun z hz => (hu₀ z hz).1.continuousAt.continuousWithinAt) φ
          φ.tsupport_subset
      have e2 : ∫ z, m ω z * φ z = (∫ z, cm (z - x) * φ z) - (∫ z, c * φ z) - ∫ z, u₀ z * φ z := by
        have hf : (fun z => m ω z * φ z) = fun z => (cm (z - x) * φ z - c * φ z) - u₀ z * φ z := by
          funext z
          simp only [hm_def, hcm]
          ring
        rw [hf, integral_sub (f := fun z => cm (z - x) * φ z - c * φ z) (hi1.sub hi2) hi3,
          integral_sub hi1 hi2]
      have e3 : ∫ z, cm z * ψ z = ∫ z, cm (z - x) * φ z := by
        rw [hψf]
        have := integral_sub_right_eq_self (μ := volume) (fun z => cm z * φ (z + x)) (x : ℂ)
        simp only [sub_add_cancel] at this
        exact this.symm
      have e4 : ∫ z, ψ z = ∫ z, φ z := by
        rw [hψf]; exact integral_add_right_eq_self (μ := volume) (fun z => φ z) (x : ℂ)
      rw [e2, e3, ha_def, e4, integral_const_mul]
      ring
    rw [e1, hsmω, Pi.smul_apply, smul_eq_mul, hkω hdisc, WholeField.integral_mul_smul, FunLike.coe_smul,
      WholeField.loewnerGreenEnergy_smul, hen, hcov, ← Complex.exp_add, Complex.ofReal_exp, ← Complex.exp_add,
      hmean]
    congr 1
    push_cast
    ring
  have k := ae_condExp_germSigma_eq_of_freq hh0 hA hℋ hmark hAc φ hGm hGiff' hfreq
  have e := WangWu.IsLocalSetMean.ae_eq_condExp_germSigma_sup hh0 hA hloc hℋ hmark hg φ
  filter_upwards [k, e] with ω hk he hsupp
  have hdis : Disjoint (tsupport φ) (A ω) := Set.disjoint_left.2 fun z hz hzA => (hsupp hz).2 hzA
  rw [he, hk hdis]

end Flow

end SideHeight

end Sec7

end InteractingSLE
