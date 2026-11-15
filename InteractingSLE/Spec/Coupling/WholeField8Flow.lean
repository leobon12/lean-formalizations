/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WholeField8Shift
import InteractingSLE.Spec.Coupling.WholeField8Path
import InteractingSLE.Spec.Exist.FlowField
import InteractingSLE.Spec.Coupling.WholeField2Hull

/-!
# The retained-range kernel (Aux. lemma 16, (WF2) for general `κ`) and its transport to a flow line

Packet PROVE-WHOLEFIELD8.

* **`HasRetainedRangeKernel`** (one coupling): at every bounded stop `τ < ζ` of the driving filtration there is a
  random distribution `M` such that, almost surely, for every continuous generating trace `η` through `τ`, `M` is
  harmonic on `Ω_τ = ℍ \ η[0, τ]` and `E[e^{i(h,φ)} | 𝓕_τ] = exp(i M(φ) − ½ G_{Ω_τ}(φ, φ))` (`rangeKerCF`), the
  covariance of a zero-boundary GFF on the possibly disconnected open set `Ω_τ` extended by zero. This is
  specification Aux. lemma 16's kernel ("`ℒ(h | 𝓕_τ) = ℒ(M_τ + h^{Ω_τ} | 𝓕_τ)` … `M_τ` is `𝓕_τ`-measurable and
  harmonic in `Ω_τ`", p. 90) and the follow-up note's (WF2) (`ig1_followup_proofs.txt` L1405–1420), with the
  mean's description in each pocket ("the harmonic limit of `m_s` … thereafter frozen") not recorded.
* **`RetainedRangeKernelStatement`** (named input, not proved): every frozen coupling with `0 < κ < 4` and an ordered
  force word has it — specification Aux. lemma 56 (p. 249: "the coupling has, through `S`, the canonical
  retained-range conditional laws of Aux. lemma 16"), equivalently the follow-up note's Part C (C.0–C.5) for
  `0 < κ < 4`. The `κ = 4` instance with Wang–Wu's frozen mean is PROVE-WHOLEFIELD7's
  `WholeField.hasWholeFieldKernels_of_isCompleteForceWord`.
* **`exists_flowKernel`**: for a flow line from `x` (the coupling field is `h(· + x) + θχ`), the kernel transported to
  the centred field `h − 𝔥₀` of the original field, with the translated range `x + η[0, τ]`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace WholeField

open LQGMetric QuantumZipper LocalSets
open SupercriticalConformalCovariance.GM24 (smoothDist smoothDist_apply)

/-! ### The retained-range kernel -/

section Def

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {nL nR : ℕ}

/-- **The retained-range kernel of one coupling** (specification Aux. lemma 16; follow-up note (WF2)): at every bounded
stop `τ < ζ` of the driving filtration there is a random distribution `M`, almost surely harmonic on `ℍ \ η[0, τ]` for
every continuous generating trace `η` through `τ`, with `E[e^{i(h,φ)} | 𝓕_τ] = exp(i M(φ) − ½ G_{ℍ∖η[0,τ]}(φ, φ))`. -/
def HasRetainedRangeKernel (P : Measure Ω) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
    (VR : Fin nR → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (h : Ω → DistOn upperHalfPlaneOpens)
    (hX : IsMeasurableKilledDriving W VL VR ζ) : Prop :=
  ∀ (τ : Ω → ℝ≥0) (hτ : IsStoppingTime (drivingFiltration P hX) fun ω => (τ ω : WithTop ℝ≥0)),
    (∃ N : ℝ≥0, ∀ ω, τ ω ≤ N) → (∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζ ω) →
    ∃ M : Ω → DistOn upperHalfPlaneOpens,
      (∀ᵐ ω ∂P, ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (τ ω) η →
        IsHarmonicDistOn (M ω) (H \ η '' Icc 0 (τ ω))) ∧
      ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ∀ η : ℝ≥0 → ℂ,
        IsGeneratingTrace (fun t => W t ω) (τ ω) η →
          (P[fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ)) | hτ.measurableSpace]) ω =
            rangeKerCF (M ω) (H \ η '' Icc 0 (τ ω)) φ

end Def

/-- **Named input: the retained-range kernels for `0 < κ < 4`** (specification Aux. lemma 56 with Aux. lemma 16's
kernel, pp. 249, 90; follow-up note Part C for `0 < κ ≤ 4`, ruling R38). Every coupling satisfying the frozen optional
hull specification of Theorem 1.1 with `0 < κ < 4` and an ordered force word has the retained-range kernel at every
bounded stop before its lifetime. **Not proved in Lean.** -/
def RetainedRangeKernelStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ)
    (ρR : Fin nR → ℝ), IsOrderedForceWord xL xR →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P] (𝓕 : Filtration ℝ≥0 mΩ)
      (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ)
      (ζ : Ω → ℝ≥0∞) (h : Ω → DistOn upperHalfPlaneOpens),
      IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h →
        ∀ hX : IsMeasurableKilledDriving W VL VR ζ, HasRetainedRangeKernel P W VL VR ζ h hX

/-! ### Transport to the original field of a flow line -/

section Flow

/-- The real translation of test functions `χ ↦ χ(· + x)`. -/
def shiftTest (x : ℝ) : TestOn upperHalfPlaneOpens →L[ℝ] TestOn upperHalfPlaneOpens :=
  Chart.pushTest (Exist.isConformal_shiftChart (-x))

theorem shiftTest_apply (x : ℝ) (χ : TestOn upperHalfPlaneOpens) (z : ℂ) : shiftTest x χ z = χ (z + x) := by
  rw [shiftTest, Exist.pushTest_shiftChart_apply]
  congr 1
  push_cast
  ring

/-- A continuous function on an open set containing the support of a test function, times the test function, is
integrable. -/
theorem integrable_mul_testOn {f : ℂ → ℝ} {D : Set ℂ} (hf : ContinuousOn f D) (φ : TestOn upperHalfPlaneOpens)
    (hφD : tsupport φ ⊆ D) : Integrable fun z => f z * φ z := by
  have hK : IsCompact (tsupport φ) := φ.hasCompactSupport.isCompact
  have hcont : ContinuousOn (fun z => f z * φ z) (tsupport φ) :=
    (hf.mono hφD).mul φ.continuous.continuousOn
  refine (hcont.integrableOn_compact hK).integrable_of_forall_notMem_eq_zero fun z hz => ?_
  rw [image_eq_zero_of_notMem_tsupport hz, mul_zero]

/-- **The translated harmonic mean**: if `M` is represented on `ℍ \ S` by a harmonic `v`, then
`χ ↦ M(χ(· + x)) − c ∫ χ − ∫ u₀ χ` is represented on `ℍ \ (S + x)` by the harmonic `v(· − x) − c − u₀`. -/
theorem isHarmonicDistOn_shift {M : DistOn upperHalfPlaneOpens} {S : Set ℂ} {x c : ℝ} {u₀ : ℂ → ℝ}
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H) (hM : IsHarmonicDistOn M (H \ S)) :
    IsHarmonicDistOn (Exist.flowField (-x) (-c) M - smoothDist upperHalfPlaneOpens u₀)
      (H \ (fun z => z + x) '' S) := by
  obtain ⟨v, hv, hMv⟩ := hM
  have hpre : ∀ w, w ∈ H \ (fun z => z + x) '' S → w - x ∈ H \ S := by
    rintro w ⟨hwH, hwS⟩
    refine ⟨?_, fun hS => hwS ⟨w - x, hS, by ring⟩⟩
    have := Exist.add_real_mem_H hwH (-x)
    simpa [sub_eq_add_neg] using this
  refine ⟨fun w => v (w - x) - c - u₀ w, ?_, fun φ hφ => ?_⟩
  · intro w hw
    have h1 : InnerProductSpace.HarmonicAt (fun w => v (w + (-x : ℂ))) w := by
      refine Exist.harmonicAt_comp_add_const ?_
      rw [← sub_eq_add_neg]; exact hv _ (hpre w hw)
    have h1' : InnerProductSpace.HarmonicAt (fun w => v (w - x)) w := by
      simpa [sub_eq_add_neg] using h1
    exact (h1'.sub (InnerProductSpace.harmonicAt_const _)).sub (hu₀ w hw.1)
  · have hu₀c : ContinuousOn u₀ H := fun z hz => (hu₀ z hz).1.continuousAt.continuousWithinAt
    have hvc : ContinuousOn (fun w => v (w - x)) (H \ (fun z => z + x) '' S) := fun w hw =>
      ((hv _ (hpre w hw)).1.continuousAt.comp (g := v) (f := fun w : ℂ => w - x)
        (continuous_sub_right _).continuousAt).continuousWithinAt
    have hsupp : tsupport (shiftTest x φ) ⊆ H \ S := by
      intro z hz
      have hz' : z + x ∈ tsupport φ := by
        have e : ⇑(shiftTest x φ) = fun z => φ (z + x) := funext (shiftTest_apply x φ)
        have : tsupport (fun z : ℂ => φ (z + x)) = (fun z : ℂ => z + (x : ℂ)) ⁻¹' tsupport ⇑φ :=
          tsupport_comp_eq_preimage (⇑φ) (Homeomorph.addRight (x : ℂ))
        rw [e, this] at hz
        exact hz
      have := hpre _ (hφ hz')
      simpa using this
    have hM1 : M (shiftTest x φ) = ∫ w, v (w - x) * φ w := by
      rw [hMv _ hsupp]
      have e : (fun z => v z * shiftTest x φ z) = fun z => (fun w => v (w - x) * φ w) (z + x) := by
        funext z; rw [shiftTest_apply]; simp
      rw [e, integral_add_right_eq_self (fun w => v (w - x) * φ w)]
    have hu₀φ : Integrable fun z => u₀ z * φ z :=
      integrable_mul_testOn hu₀c φ (φ.tsupport_subset)
    have hvφ : Integrable fun z => v (z - x) * φ z := integrable_mul_testOn hvc φ hφ
    have hφi : Integrable fun z => φ z := φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
    have hsd : smoothDist upperHalfPlaneOpens u₀ φ = ∫ z, u₀ z * φ z := by
      rw [smoothDist_apply hu₀c]; congr 1; funext z; ring
    rw [sub_apply, Exist.flowField_apply, hsd,
      show Chart.pushTest (Exist.isConformal_shiftChart (-x)) φ = shiftTest x φ from rfl, hM1]
    rw [← integral_const_mul, ← integral_add hvφ (hφi.const_mul (-c))]
    have h2 : Integrable (fun a => v (a - x) * φ a + -c * φ a) := hvφ.add (hφi.const_mul (-c))
    rw [← integral_sub h2 hu₀φ]
    congr 1
    funext z
    push_cast
    ring

/-- The complement of a translated range is the translate of the complement of the range. -/
theorem preimage_add_H_diff_image (x : ℝ) (S : Set ℂ) :
    (fun z => z + (x : ℂ)) ⁻¹' (H \ (fun z => z + (x : ℂ)) '' S) = H \ S := by
  ext z
  simp only [mem_preimage, Set.mem_sdiff, mem_image, add_left_inj, exists_eq_right]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    have := Exist.add_real_mem_H h1 (-x)
    simpa using this
  · rintro ⟨h1, h2⟩
    exact ⟨Exist.add_real_mem_H h1 x, h2⟩

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {nL nR : ℕ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h h' : Ω → DistOn upperHalfPlaneOpens}
  {hX : IsMeasurableKilledDriving W VL VR ζ}

/-- **The retained-range kernel of a flow line, in the original coordinate.** If the coupling field `h'` is
`h(· + x) + c` and has the retained-range kernel, then the centred original field `h − 𝔥₀` has, at every bounded stop
`τ < ζ`, a mean harmonic on `ℍ \ (x + η[0, τ])` and the kernel with the covariance of `ℍ \ (x + η[0, τ])`. -/
theorem exists_flowKernel (hK : HasRetainedRangeKernel P W VL VR ζ h' hX) {x c : ℝ}
    (htrans : ∀ ω, IsTranslateAddConst x c (h ω) (h' ω)) {u₀ : ℂ → ℝ}
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H) (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (drivingFiltration P hX) fun ω => (τ ω : WithTop ℝ≥0)) (hτN : ∃ N : ℝ≥0, ∀ ω, τ ω ≤ N)
    (hτζ : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζ ω) :
    ∃ M : Ω → DistOn upperHalfPlaneOpens,
      (∀ᵐ ω ∂P, ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (τ ω) η →
        IsHarmonicDistOn (M ω) (H \ (fun z => z + (x : ℂ)) '' (η '' Icc 0 (τ ω)))) ∧
      ∀ χ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ∀ η : ℝ≥0 → ℂ,
        IsGeneratingTrace (fun t => W t ω) (τ ω) η →
          (P[fun ω' => Complex.exp (Complex.I * (centredField h u₀ ω' χ : ℂ)) | hτ.measurableSpace]) ω =
            rangeKerCF (M ω) (H \ (fun z => z + (x : ℂ)) '' (η '' Icc 0 (τ ω))) χ := by
  obtain ⟨M', hharm, hker⟩ := hK τ hτ hτN hτζ
  refine ⟨fun ω => Exist.flowField (-x) (-c) (M' ω) - smoothDist upperHalfPlaneOpens u₀, ?_, fun χ => ?_⟩
  · filter_upwards [hharm] with ω hω η hη
    exact isHarmonicDistOn_shift hu₀ (hω η hη)
  · set χ' := shiftTest x χ with hχ'
    have hχ'f : ⇑χ' = fun z => χ (z + x) := funext (shiftTest_apply x χ)
    have hint : (∫ z, χ' z) = ∫ z, χ z := by rw [hχ'f, integral_add_right_eq_self (fun z => χ z)]
    set K : ℝ := c * (∫ z, χ z) + ∫ z, u₀ z * χ z with hK
    have hfield : ∀ ω, centredField h u₀ ω χ = h' ω χ' - K := fun ω => by
      have h1 := htrans ω χ χ' (shiftTest_apply x χ)
      rw [centredField_apply h hu₀ ω χ, h1, hint, hK]
      ring
    have hfun : (fun ω' => Complex.exp (Complex.I * (centredField h u₀ ω' χ : ℂ))) =
        Complex.exp (-(Complex.I * (K : ℂ))) • fun ω' => Complex.exp (Complex.I * (h' ω' χ' : ℂ)) := by
      funext ω'
      rw [Pi.smul_apply, smul_eq_mul, ← Complex.exp_add, hfield]
      congr 1
      push_cast
      ring
    have hsm := condExp_smul (μ := P) (Complex.exp (-(Complex.I * (K : ℂ))))
      (fun ω' => Complex.exp (Complex.I * (h' ω' χ' : ℂ))) hτ.measurableSpace
    filter_upwards [hker χ', hsm] with ω hω hsω η hη
    rw [hfun, hsω, Pi.smul_apply, hω η hη, smul_eq_mul]
    simp only [rangeKerCF]
    have hcov : zeroGFFTestCov (H \ η '' Icc 0 (τ ω)) χ' χ' =
        zeroGFFTestCov (H \ (fun z => z + (x : ℂ)) '' (η '' Icc 0 (τ ω))) χ χ := by
      rw [hχ'f, ← preimage_add_H_diff_image x (η '' Icc 0 (τ ω))]
      exact zeroGFFTestCov_comp_add (x : ℂ) _ χ.continuous χ.continuous
    have hM : (Exist.flowField (-x) (-c) (M' ω) - smoothDist upperHalfPlaneOpens u₀) χ = M' ω χ' - K := by
      have hu₀c : ContinuousOn u₀ H := fun z hz => (hu₀ z hz).1.continuousAt.continuousWithinAt
      have hsd : smoothDist upperHalfPlaneOpens u₀ χ = ∫ z, u₀ z * χ z := by
        rw [smoothDist_apply hu₀c]; congr 1; funext z; ring
      rw [sub_apply, Exist.flowField_apply, hsd,
        show Chart.pushTest (Exist.isConformal_shiftChart (-x)) χ = χ' from rfl, hK]
      ring
    rw [hcov, hM, ← Complex.exp_add]
    congr 1
    push_cast
    ring

end Flow

end WholeField

end InteractingSLE
