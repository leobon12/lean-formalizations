/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.GlueCond

/-!
# The cross-curve conditioning on the glued space, field side: the counterflow hull's explicit mean

Packet PROVE-GLUECOND. Specification §4.2, proof of Lemma 4.7 (`source/spec/p097-144.md#lem-4.7-proof`, p. 118):
the boundary data of the conditional law of `h` given both prefixes "along `∂_U𝒮 ∪ η′([0, t])` agree with those of
the conditional law of `h` given just `η′|_{[0,t]}`". This file makes the latter explicit, in the chart `Q`, for the
centred counterflow coupling of `IsCenteredCounterflowDriver` (frozen): in the chart `R` the counterflow is the
flow line, at parameter `κ′ = 16/κ`, of the word of `counterflowData κ b`, so its hull `K′_t` has the frozen coupling
mean `𝔥′_t`; reflecting by `R(z) = −1/z` gives the mean of `R(K′_t)`.

* `eqOn_returnBHE_counterflow`: **the two centrings agree.** If `u_b` is the bounded harmonic extension of the data
  `b` of `h₂` and `u′` that of the counterflow word in the chart `R`, then `−u′(R z) + (a + k · lift z) = u_b(z)` on
  `ℍ` (`a = −πχ`, `k = χ(16/κ)`): both are bounded harmonic extensions of `b` off a finite set
  (`returnData_inverseData`, `Sec4.forceBoundaryData_flowLine`), hence equal.
* `cenT_eq_reflectField_centred`: hence the centred chart-`Q` field `cenT κ u₀ h₂ = h₂ − u_b` is the reflection of the
  centred chart-`R` field `h₂′ − u′`.
* `exists_isLocalSetMean_cfHullQ`: **the counterflow hull's mean on `Ω₂`, explicit**: a local-set mean of
  `R(K′_t)` (read from the history) for `cenT κ u₀ h₂`, equal off `R(K′_t)` to `z ↦ −𝔥′_t(R z) + u′(R z)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal Real
open QuantumZipper (H chiC fwdHull)
open LQGMetric (DistOn TestOn)
open SupercriticalConformalCovariance.GM24 (smoothDist smoothDist_apply)

universe u

namespace InteractingSLE.Sec5.GlueCond

open WangWu hiding ratPt exists_ratPt_dist_lt continuousAt_negInv
open LawUnique Cond44Ref Sec7.StripSysField
open LocalSets (IsLocalSetMean)

/-! ### The two centrings of the counterflow field agree -/

section Centring

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- The data of the counterflow word in the chart `R` (the word of `counterflowData κ b` at parameter `16/κ`). -/
abbrev cfWordData (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) : ℝ → ℝ :=
  forceBoundaryData (16 / κ) (flowLineRhoL (16 / κ) (counterflowData κ b) (counterflowJumps jumps) 0 0)
    (flowLineRhoR (16 / κ) (counterflowData κ b) (counterflowJumps jumps) 0 0)
    (flowLineXL (counterflowData κ b) (counterflowJumps jumps) 0)
    (flowLineXR (counterflowData κ b) (counterflowJumps jumps) 0)

/-- The jump set of the counterflow word in the chart `R`. -/
abbrev cfWordJumps (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) : Finset ℝ :=
  forceJumpFinset (flowLineXL (counterflowData κ b) (counterflowJumps jumps) 0)
    (flowLineXR (counterflowData κ b) (counterflowJumps jumps) 0)

/-- **The two centrings of the counterflow field agree**: the return of the chart-`R` harmonic extension of the
counterflow word is the harmonic extension of the chart-`Q` data `b`. -/
theorem eqOn_returnBHE_counterflow (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps) {u_b : ℂ → ℝ}
    (hu_b : IsBoundedHarmonicExtension b jumps u_b) {u' : ℂ → ℝ}
    (hu' : IsBoundedHarmonicExtension (cfWordData κ b jumps) (cfWordJumps κ b jumps) u') :
    EqOn (fun z => -u' (negInv z) + retShift (cfOffset κ) (cfCoeff κ) z) u_b H := by
  have hk : 0 < 16 / κ := by positivity
  have hb'' := isPiecewiseConstant_counterflowData κ hb
  have hF := isBoundedHarmonicExtension_return (cfOffset κ) (cfCoeff κ) hu'
  set T : Finset ℝ := jumps ∪ returnExcept (cfWordJumps κ b jumps) ∪ returnExcept (counterflowJumps jumps)
    with hT
  have hdata : ∀ x ∉ T, returnData (cfOffset κ) (cfCoeff κ) (cfWordData κ b jumps) x = b x := by
    intro x hx
    have hx' : x ∉ returnExcept (counterflowJumps jumps) := fun h => hx (Finset.mem_union_right _ h)
    have hx0 : x ≠ 0 := ne_zero_of_notMem_returnExcept hx'
    have hyJ := negInv_notMem_of_notMem_returnExcept hx'
    have hy0 : -x⁻¹ ≠ 0 := neg_ne_zero.2 (inv_ne_zero hx0)
    have e : cfWordData κ b jumps (-x⁻¹) = counterflowData κ b (-x⁻¹) :=
      Sec4.forceBoundaryData_flowLine hk hb'' hy0 hyJ
    have e2 := returnData_inverseData (cfOffset κ) (cfCoeff κ) b hx0
    simp only [returnData] at e2 ⊢
    rw [e]
    exact e2
  have hF' : IsBoundedHarmonicExtension b (T : Set ℝ)
      (fun z => -u' (-z⁻¹) + cfOffset κ + cfCoeff κ * infinitySourceChart.2.2 z) := by
    refine ⟨hF.1, hF.2.1, fun x hx => ?_⟩
    have hxT : x ∉ T := hx
    rw [← hdata x hxT]
    exact hF.2.2 x fun h => hxT (Finset.mem_union_left _ (Finset.mem_union_right _ (by exact_mod_cast h)))
  have hu_b' : IsBoundedHarmonicExtension b (T : Set ℝ) u_b :=
    ⟨hu_b.1, hu_b.2.1, fun x hx => hu_b.2.2 x fun h =>
      hx (Finset.mem_union_left _ (Finset.mem_union_left _ (by exact_mod_cast h)))⟩
  have hbT : IsPiecewiseConstantBoundaryData b T := fun y hy =>
    hb y fun h => hy (Finset.mem_union_left _ (Finset.mem_union_left _ h))
  obtain ⟨v, -, huniq⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hbT
  intro z hz
  have h1 := huniq _ hF' hz
  have h2 := huniq _ hu_b' hz
  simp only at h1 h2 ⊢
  rw [h2, ← h1]
  simp only [retShift, negInv]
  ring

/-- **The centred chart-`Q` field is the reflection of the centred chart-`R` field**: if `h₂ = returnField a k h₂′`
(the frozen chart transport of the centred counterflow), then `h₂ − u_b = R_*(h₂′ − u′)`. -/
theorem eq_reflectField_centred (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps) {u_b : ℂ → ℝ}
    (hu_b : IsBoundedHarmonicExtension b jumps u_b) {u' : ℂ → ℝ}
    (hu' : IsBoundedHarmonicExtension (cfWordData κ b jumps) (cfWordJumps κ b jumps) u')
    {f f' : DistOn upperHalfPlaneOpens} (hff' : f = returnField (cfOffset κ) (cfCoeff κ) f') :
    f - smoothDist upperHalfPlaneOpens u_b = reflectField (f' - smoothDist upperHalfPlaneOpens u') := by
  have hc' : ContinuousOn u' H := fun z hz => (hu'.1 z hz).1.continuousAt.continuousWithinAt
  have hcb : ContinuousOn u_b H := fun z hz => (hu_b.1 z hz).1.continuousAt.continuousWithinAt
  have hcr : ContinuousOn (fun z => -u' (negInv z)) H :=
    (hc'.comp continuousOn_negInv fun z hz => WangWu.negInv_mem_H hz).neg
  rw [hff', returnField_eq_reflectField_add, reflectField_sub, reflectField_smoothDist hc']
  have e : smoothDist upperHalfPlaneOpens (retShift (cfOffset κ) (cfCoeff κ)) =
      smoothDist upperHalfPlaneOpens u_b - smoothDist upperHalfPlaneOpens (fun z => -u' (negInv z)) := by
    ext φ
    rw [sub_apply, Coupling.smoothDist_apply_eq (continuousOn_retShift _ _), Coupling.smoothDist_apply_eq hcr,
      Coupling.smoothDist_apply_eq hcb, ← integral_sub
        (Coupling.MartMeans2.integrable_mul_test_of_continuousOn hcb φ φ.tsupport_subset)
        (Coupling.MartMeans2.integrable_mul_test_of_continuousOn hcr φ φ.tsupport_subset)]
    refine integral_congr_ae (ae_of_all _ fun w => ?_)
    dsimp only
    by_cases hw : w ∈ H
    · have := eqOn_returnBHE_counterflow hκ hb hu_b hu' hw
      simp only at this
      rw [← this]
      ring
    · have : φ w = 0 := image_eq_zero_of_notMem_tsupport fun h => hw (φ.tsupport_subset h)
      rw [this]
      ring
  rw [e]
  abel

end Centring

/-! ### The counterflow hull's mean on the counterflow's space -/

section Omega2

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω₂ : Type u} {mΩ₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂}
  [IsProbabilityMeasure P₂] {h₂ : Ω₂ → DistOn upperHalfPlaneOpens} {W₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞}

/-- The weights of the counterflow word (chart `R`, parameter `16/κ`), left side. -/
abbrev cfRhoL (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) :
    Fin (flowLineNL (counterflowData κ b) (counterflowJumps jumps) 0) → ℝ :=
  flowLineRhoL (16 / κ) (counterflowData κ b) (counterflowJumps jumps) 0 0

/-- The weights of the counterflow word (chart `R`, parameter `16/κ`), right side. -/
abbrev cfRhoR (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) :
    Fin (flowLineNR (counterflowData κ b) (counterflowJumps jumps) 0) → ℝ :=
  flowLineRhoR (16 / κ) (counterflowData κ b) (counterflowJumps jumps) 0 0

/-- **The centred left force positions of the counterflow word at time `t`, read from the driver `w`**: the geometric
images of the initial marks (`WangWu.vL_eq_neg_rightImg`), minus `w t`. -/
def cfPosL (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (w : ℝ≥0 → ℝ) (t : ℝ≥0)
    (i : Fin (flowLineNL (counterflowData κ b) (counterflowJumps jumps) 0)) : ℝ :=
  -MartChar.RealFlow.rightImg (fun s => -Ito.rpath w s)
    (-flowLineXL (counterflowData κ b) (counterflowJumps jumps) 0 i) t - w t

/-- **The centred right force positions of the counterflow word at time `t`, read from the driver `w`**
(`WangWu.vR_eq_rightImg`). -/
def cfPosR (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (w : ℝ≥0 → ℝ) (t : ℝ≥0)
    (i : Fin (flowLineNR (counterflowData κ b) (counterflowJumps jumps) 0)) : ℝ :=
  MartChar.RealFlow.rightImg (Ito.rpath w) (flowLineXR (counterflowData κ b) (counterflowJumps jumps) 0 i) t - w t

/-- **The counterflow hull's mean on the counterflow's space, explicit, in the chart `Q`** (the conditional law of
`h` given `η′|_{[0,t]}` alone). For a centred counterflow coupling of a GFF `h₂` with piecewise constant data `b`,
of infinite lifetime with a continuous driver from `0`, and bounded harmonic extensions `u_b` of `b`, `u′` of the
counterflow word's data in the chart `R`, and `uG ω` of the word's data at the force positions at time `t` read from
the driver: the reflected hull `R(K′_t)` read from the history has a local-set mean `g` of `h₂ − u_b`, and almost
surely, off `R(K′_t)`, `g = −𝔥′_t ∘ R + u′ ∘ R` with `𝔥′_t = couplingMean (16/κ) W₂ t (uG ω)`. -/
theorem exists_isLocalSetMean_cfHullQ (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh₂ : IsGFFWithBoundaryData P₂ h₂ b jumps) (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂)
    (hreg₂ : ∀ᵐ ω ∂P₂, ζ₂ ω = ⊤ ∧ W₂ 0 ω = 0 ∧ Continuous fun t => W₂ t ω)
    {u_b : ℂ → ℝ} (hu_b : IsBoundedHarmonicExtension b jumps u_b) {u' : ℂ → ℝ}
    (hu' : IsBoundedHarmonicExtension (cfWordData κ b jumps) (cfWordJumps κ b jumps) u') (t : ℝ≥0)
    {uG : Ω₂ → ℂ → ℝ}
    (huG : ∀ ω, IsBoundedHarmonicExtension (forceBoundaryData (16 / κ) (cfRhoL κ b jumps) (cfRhoR κ b jumps)
        (cfPosL κ b jumps (W₂ · ω) t) (cfPosR κ b jumps (W₂ · ω) t))
      (forceJumpSet (cfPosL κ b jumps (W₂ · ω) t) (cfPosR κ b jumps (W₂ · ω) t)) (uG ω)) :
    ∃ g : Ω₂ → DistOn upperHalfPlaneOpens,
      IsLocalSetMean (fun ω => cfHullQ t (cfHistory W₂ ζ₂ ω))
        (fun ω => h₂ ω - smoothDist upperHalfPlaneOpens u_b) P₂ g ∧
      ∀ᵐ ω ∂P₂, ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ cfHullQ t (cfHistory W₂ ζ₂ ω) →
        g ω φ = ∫ z, (-couplingMean (16 / κ) (fun s : ℝ => W₂ s.toNNReal ω) t (uG ω) (negInv z) +
          u' (negInv z)) * φ z := by
  classical
  have hk : 0 < 16 / κ := by positivity
  obtain ⟨h', htr, hfl⟩ := Theorem14.GW2Cone.isFlowLineDriver_counterflowData hκ hb hh₂ hcf
  obtain ⟨h'', 𝓕₂, VL₂, VR₂, B₂, htac, hC₂⟩ := hfl
  have e : h'' = h' := funext fun ω =>
    Theorem14.GW2Cone.eq_of_isTranslateAddConst_zero (zero_mul _) (htac ω)
  subst e
  obtain ⟨hX₂, hker⟩ := hC₂.2.2.2
  have hu'' := hu'
  rw [cfWordJumps, coe_forceJumpFinset] at hu''
  have hAm : Measurable[mΩ₂, hittingSigma] fun ω => hullAt t (cfHistory W₂ ζ₂ ω) :=
    (measurable_hullAt t).comp (measurable_cfHistory (isMeasurableKilledDriving_of_isCenteredCounterflowDriver hcf))
  have hh0 := WholeField.isZeroBoundaryGFF_centredField hC₂ hu''
  have hτζ : ∀ᵐ ω ∂P₂, (((fun _ : Ω₂ => ((t : ℝ≥0) : WithTop ℝ≥0)) ω : WithTop ℝ≥0) : ℝ≥0∞) < ζ₂ ω := by
    filter_upwards [hreg₂] with ω hω
    rw [hω.1]
    exact ENNReal.coe_lt_top
  have hAK : ∀ᵐ ω ∂P₂, hullAt t (cfHistory W₂ ζ₂ ω) =
      (fun z : ℂ => z + ((0 : ℝ) : ℂ)) '' fwdHull (fun s : ℝ => W₂ s.toNNReal ω)
        (((fun _ : Ω₂ => ((t : ℝ≥0) : WithTop ℝ≥0)) ω).untopD 0 : ℝ≥0) := by
    filter_upwards [hreg₂] with ω hω
    rw [WithTop.untopD_coe, hullAt_cfHistory hω.1 hω.2.1 hω.2.2]
    simp only [Complex.ofReal_zero, add_zero, image_id']
  have hK := (hker (fun _ => ((t : ℝ≥0) : WithTop ℝ≥0)) (isStoppingTime_const _ t) hτζ).1
  have hloc : IsLocalSet (fun ω => hullAt t (cfHistory W₂ ζ₂ ω)) (WholeField.centredField h'' u') P₂ := by
    have h1 := WholeField.IsLocalSet.sub_dist hK (WholeField.isHarmonicDistOn_smoothDist hu'.1)
    refine Coupling.IsLocalSet.congr_set h1 ?_
    filter_upwards [hAK] with ω hω
    rw [hω]
    simp only [Complex.ofReal_zero, add_zero, image_id']
  obtain ⟨g', hg'⟩ := LocalSets.IsLocalSet.exists_isLocalSetMean hh0 hAm hloc
  -- the coupling's force positions are the positions read from the driver, almost surely
  have hpos : ∀ᵐ ω ∂P₂, (fun i => VL₂ i t ω - W₂ t ω) = cfPosL κ b jumps (W₂ · ω) t ∧
      (fun i => VR₂ i t ω - W₂ t ω) = cfPosR κ b jumps (W₂ · ω) t := by
    filter_upwards [hC₂.1.2.2.2.2, hreg₂] with ω hp hω
    have ht : ((t : ℝ≥0) : ℝ≥0∞) < ζ₂ ω := by rw [hω.1]; exact ENNReal.coe_lt_top
    refine ⟨funext fun i => ?_, funext fun i => ?_⟩
    · rw [cfPosL, WangWu.vL_eq_neg_rightImg hp hω.2.2 ht i]
    · rw [cfPosR, WangWu.vR_eq_rightImg hp hω.2.2 ht i]
  -- a family of extensions at the coupling's positions, equal to `uG` almost surely
  set u₂ : Ω₂ → ℂ → ℝ := fun ω =>
    if (fun i => VL₂ i t ω - W₂ t ω) = cfPosL κ b jumps (W₂ · ω) t ∧
        (fun i => VR₂ i t ω - W₂ t ω) = cfPosR κ b jumps (W₂ · ω) t then uG ω
    else Classical.choose (WholeField.exists_bhe (16 / κ) (cfRhoL κ b jumps) (cfRhoR κ b jumps)
      (fun i => VL₂ i t ω - W₂ t ω) (fun i => VR₂ i t ω - W₂ t ω)) with hu₂def
  have hu₂ : ∀ ω, IsBoundedHarmonicExtension
      (forceBoundaryData (16 / κ) (cfRhoL κ b jumps) (cfRhoR κ b jumps)
        (fun i => VL₂ i (((fun _ : Ω₂ => ((t : ℝ≥0) : WithTop ℝ≥0)) ω).untopD 0) ω -
          W₂ (((fun _ : Ω₂ => ((t : ℝ≥0) : WithTop ℝ≥0)) ω).untopD 0) ω)
        (fun i => VR₂ i (((fun _ : Ω₂ => ((t : ℝ≥0) : WithTop ℝ≥0)) ω).untopD 0) ω -
          W₂ (((fun _ : Ω₂ => ((t : ℝ≥0) : WithTop ℝ≥0)) ω).untopD 0) ω))
      (forceJumpSet (fun i => VL₂ i (((fun _ : Ω₂ => ((t : ℝ≥0) : WithTop ℝ≥0)) ω).untopD 0) ω -
          W₂ (((fun _ : Ω₂ => ((t : ℝ≥0) : WithTop ℝ≥0)) ω).untopD 0) ω)
        (fun i => VR₂ i (((fun _ : Ω₂ => ((t : ℝ≥0) : WithTop ℝ≥0)) ω).untopD 0) ω -
          W₂ (((fun _ : Ω₂ => ((t : ℝ≥0) : WithTop ℝ≥0)) ω).untopD 0) ω)) (u₂ ω) := by
    intro ω
    simp only [WithTop.untopD_coe]
    by_cases hω : (fun i => VL₂ i t ω - W₂ t ω) = cfPosL κ b jumps (W₂ · ω) t ∧
        (fun i => VR₂ i t ω - W₂ t ω) = cfPosR κ b jumps (W₂ · ω) t
    · rw [hu₂def]
      simp only [hω, and_self, ↓reduceIte]
      exact huG ω
    · rw [hu₂def]
      simp only [hω, ↓reduceIte]
      exact Classical.choose_spec (WholeField.exists_bhe (16 / κ) (cfRhoL κ b jumps) (cfRhoR κ b jumps)
        (fun i => VL₂ i t ω - W₂ t ω) (fun i => VR₂ i t ω - W₂ t ω))
  have hid := Sec7.SideHeight.ae_apply_eq_of_isLocalSetMean_flowHull (x := 0) (c := 0) hC₂ hk
    (fun ω => by simpa only [zero_mul] using Sec7.StripSysField.isTranslateAddConst_zero_self (h'' ω) 0) hh0
    hu'.1 hu'' (fun z _ => by simp only [Complex.ofReal_zero, add_zero]) hX₂ (isStoppingTime_const _ t) hτζ hAm
    hAK hg' hu₂
  -- reflect
  have hrefl := IsLocalSetMean.reflect (fun ω => hullAt_relClosed t (cfHistory W₂ ζ₂ ω)) hg'
  have hfield : (fun ω => reflectField (WholeField.centredField h'' u' ω)) =
      fun ω => h₂ ω - smoothDist upperHalfPlaneOpens u_b := by
    funext ω
    exact (eq_reflectField_centred hκ hb hu_b hu' (Theorem14.GW2Cone.eq_returnField_of_isChartTransport (htr ω))).symm
  rw [hfield] at hrefl
  refine ⟨fun ω => reflectField (g' ω), hrefl, ?_⟩
  filter_upwards [hid, hpos] with ω hω hpω φ hφ
  have hu₂ω : u₂ ω = uG ω := by
    rw [hu₂def]
    simp only [hpω, and_self, ↓reduceIte]
  set K := hullAt t (cfHistory W₂ ζ₂ ω) with hK
  set ψ := Chart.pushTest Sec7.StripSysField.isConformal_infinityReturnChart φ with hψ
  have hψs : tsupport ψ ⊆ H \ K := by
    refine (tsupport_pushTest_return_subset φ).trans ?_
    rintro _ ⟨z, hz, rfl⟩
    have h1 := hφ hz
    rw [cfHullQ, H_diff_image_negInv] at h1
    obtain ⟨w, hw, hwz⟩ := h1
    rw [← hwz, WangWu.negInv_negInv]
    exact hw
  rw [reflectField_apply, hω ψ hψs]
  simp only [WithTop.untopD_coe, Complex.ofReal_zero, sub_zero, hu₂ω]
  have h1 := Chart.integral_mul_pushTest Sec7.StripSysField.isConformal_infinityReturnChart φ
    (fun z => couplingMean (16 / κ) (fun s : ℝ => W₂ s.toNNReal ω) t (uG ω) z - u' z)
  rw [h1, ← integral_neg]
  refine integral_congr_ae (ae_of_all _ fun w => ?_)
  simp only [infinityReturnChart_inv_eq]
  ring

end Omega2

/-! ### The counterflow hull's mean on the glued space -/

section GlueMean

/-- **The canonical space of the counterflow**: a field and a counterflow history, lifted to the universe `u`. -/
abbrev CfSpace : Type u := ULift.{u} (DistOn upperHalfPlaneOpens × HistorySpace 0 0)

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}
  {Ω₂ : Type u} {mΩ₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
  {h₂ : Ω₂ → DistOn upperHalfPlaneOpens} {W₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞}
  {k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)} [IsMarkovKernel k] {u₀ : ℂ → ℝ}

/-- The counterflow coupling read on the canonical space. -/
def cfProj (h₂ : Ω₂ → DistOn upperHalfPlaneOpens) (W₂ : ℝ≥0 → Ω₂ → ℝ) (ζ₂ : Ω₂ → ℝ≥0∞) (ω : Ω₂) :
    CfSpace.{u} :=
  ULift.up (h₂ ω, cfHistory W₂ ζ₂ ω)

/-- The glued space read on the canonical space. -/
def glueProjCf (X : Ω → DistOn upperHalfPlaneOpens) (p : Ω × HistorySpace 0 0) : CfSpace.{u} :=
  ULift.up (X p.1, p.2)

theorem measurable_glueProjCf {X : Ω → DistOn upperHalfPlaneOpens} (hX : Measurable X) :
    Measurable (glueProjCf.{u} X) :=
  measurable_up.comp ((hX.comp measurable_fst).prodMk measurable_snd)

omit [IsProbabilityMeasure P₂] in
/-- **The glued space and the counterflow coupling have the same law on the canonical space.** -/
theorem glueMeasure_map_cfProj {X : Ω → DistOn upperHalfPlaneOpens} (hX : Measurable X) (hh₂ : Measurable h₂)
    (hD : Measurable (cfHistory W₂ ζ₂)) (hlaw : P.map X = P₂.map h₂)
    (hk : P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k) :
    (glueMeasure P k X hX).map (glueProjCf X) = P₂.map (cfProj h₂ W₂ ζ₂) := by
  have h1 : glueProjCf.{u} X = ULift.up ∘ fun p : Ω × HistorySpace 0 0 => (X p.1, p.2) := rfl
  have h2 : cfProj.{u} h₂ W₂ ζ₂ = ULift.up ∘ fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω) := rfl
  have hm1 : Measurable fun p : Ω × HistorySpace 0 0 => (X p.1, p.2) :=
    (hX.comp measurable_fst).prodMk measurable_snd
  rw [h1, h2, ← Measure.map_map measurable_up hm1, ← Measure.map_map measurable_up (hh₂.prodMk hD),
    glueMeasure_map_pair hX k, hk, hlaw]

/-- A bounded harmonic extension shifted by a constant extends the shifted data. -/
theorem isBoundedHarmonicExtension_add_const {g : ℝ → ℝ} {S : Set ℝ} {v : ℂ → ℝ}
    (hv : IsBoundedHarmonicExtension g S v) (c : ℝ) :
    IsBoundedHarmonicExtension (fun x => g x + c) S (fun z => v z + c) := by
  obtain ⟨hharm, ⟨C, hC⟩, hlim⟩ := hv
  refine ⟨fun z hz => (hharm z hz).add (InnerProductSpace.harmonicAt_const _), ⟨C + |c|, fun z hz => ?_⟩,
    fun x hx => (hlim x hx).add tendsto_const_nhds⟩
  exact (abs_add_le _ _).trans (by linarith [hC z hz])

/-- `cenT κ u₀ f = f − (u₀ − π/2 χ)`. -/
theorem cenT_eq_sub (κ : ℝ) {u₀ : ℂ → ℝ} (hu₀ : ContinuousOn u₀ H) (f : DistOn upperHalfPlaneOpens) :
    cenT κ u₀ f = f - smoothDist upperHalfPlaneOpens (fun z => u₀ z + -(π / 2 * chiC κ)) := by
  rw [cenT_eq_add_sub]
  ext φ
  have hc : ContinuousOn (fun z => u₀ z + -(π / 2 * chiC κ)) H := hu₀.add continuousOn_const
  rw [sub_apply, add_apply, sub_apply, Coupling.smoothDist_apply_eq continuousOn_const,
    Coupling.smoothDist_apply_eq hu₀, Coupling.smoothDist_apply_eq hc]
  have h1 := Coupling.MartMeans2.integrable_mul_test_of_continuousOn hu₀ φ φ.tsupport_subset
  have h2 := Coupling.MartMeans2.integrable_mul_test_of_continuousOn (f := fun _ => π / 2 * chiC κ)
    continuousOn_const φ φ.tsupport_subset
  have e : (∫ z, (u₀ z + -(π / 2 * chiC κ)) * φ z) =
      (∫ z, u₀ z * φ z) - ∫ z, (π / 2 * chiC κ) * φ z := by
    rw [← integral_sub h1 h2]
    exact integral_congr_ae (ae_of_all _ fun z => by ring)
  rw [e]
  ring

/-- **The counterflow hull's mean on the glued space** (Lemma 4.7's "boundary conditions along `∂_U𝒮 ∪ η′([0, t])`
… of the conditional law of `h` given just `η′|_{[0,t]}`", chart `Q`). In the setting of `isLocalSet_union_glue`, with
`b = 𝔟_F − π/2 χ` the data of `h − π/2 χ` and `u′`, `uG` the chart-`R` extensions of `exists_isLocalSetMean_cfHullQ`:
there is a mean `ĝ` on the canonical space such that `p ↦ ĝ(h p.1 − π/2 χ, p.2)` is a local-set mean of
`R(K′_t)` (read from the history) for the centred field `h − 𝔥₀` on the glued space, and, test function by test
function, `ĝ(h₂ ω, history) = −𝔥′_t ∘ R + u′ ∘ R` off `R(K′_t)` almost surely on the counterflow's space. -/
theorem exists_isLocalSetMean_cfHullQ_glue (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hκ : 0 < κ) (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂)
    (hreg₂ : ∀ᵐ ω ∂P₂, ζ₂ ω = ⊤ ∧ W₂ 0 ω = 0 ∧ Continuous fun t => W₂ t ω)
    (hlaw : P.map (fun ω => cfField κ (h ω)) = P₂.map h₂)
    (hk : P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k)
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀) (t : ℝ≥0)
    {u' : ℂ → ℝ}
    (hu' : IsBoundedHarmonicExtension
      (cfWordData κ (fun x => forceBoundaryData κ ρL ρR xL xR x + -(π / 2 * chiC κ)) (forceJumpFinset xL xR))
      (cfWordJumps κ (fun x => forceBoundaryData κ ρL ρR xL xR x + -(π / 2 * chiC κ)) (forceJumpFinset xL xR)) u')
    {uG : Ω₂ → ℂ → ℝ}
    (huG : ∀ ω, IsBoundedHarmonicExtension
      (forceBoundaryData (16 / κ)
        (cfRhoL κ (fun x => forceBoundaryData κ ρL ρR xL xR x + -(π / 2 * chiC κ)) (forceJumpFinset xL xR))
        (cfRhoR κ (fun x => forceBoundaryData κ ρL ρR xL xR x + -(π / 2 * chiC κ)) (forceJumpFinset xL xR))
        (cfPosL κ (fun x => forceBoundaryData κ ρL ρR xL xR x + -(π / 2 * chiC κ)) (forceJumpFinset xL xR)
          (W₂ · ω) t)
        (cfPosR κ (fun x => forceBoundaryData κ ρL ρR xL xR x + -(π / 2 * chiC κ)) (forceJumpFinset xL xR)
          (W₂ · ω) t))
      (forceJumpSet
        (cfPosL κ (fun x => forceBoundaryData κ ρL ρR xL xR x + -(π / 2 * chiC κ)) (forceJumpFinset xL xR)
          (W₂ · ω) t)
        (cfPosR κ (fun x => forceBoundaryData κ ρL ρR xL xR x + -(π / 2 * chiC κ)) (forceJumpFinset xL xR)
          (W₂ · ω) t)) (uG ω)) :
    ∃ g : CfSpace.{u} → DistOn upperHalfPlaneOpens,
      IsLocalSetMean (fun p : Ω × HistorySpace 0 0 => cfHullQ t p.2) (fun p => cenT κ u₀ (cfField κ (h p.1)))
        (glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1))
        (fun p => g (glueProjCf (fun ω => cfField κ (h ω)) p)) ∧
      ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P₂, tsupport φ ⊆ H \ cfHullQ t (cfHistory W₂ ζ₂ ω) →
        g (cfProj h₂ W₂ ζ₂ ω) φ = ∫ z, (-couplingMean (16 / κ) (fun s : ℝ => W₂ s.toNNReal ω) t (uG ω) (negInv z) +
          u' (negInv z)) * φ z := by
  let _ : MeasurableSpace (Set ℂ) := hittingSigma
  set c : ℝ := -(π / 2 * chiC κ) with hc
  set b : ℝ → ℝ := fun x => forceBoundaryData κ ρL ρR xL xR x + c with hbdef
  have hb : IsPiecewiseConstantBoundaryData b (forceJumpFinset xL xR) := isPiecewiseConstant_forceData κ ρL ρR xL xR c
  have hXm : Measurable fun ω => cfField κ (h ω) := (measurable_cfField κ).comp hC.2.1
  have hh₂m := CfRegQ.measurable_of_isCenteredCounterflowDriver hcf
  have hDm := measurable_cfHistory (isMeasurableKilledDriving_of_isCenteredCounterflowDriver hcf)
  have hhh : IsGFFWithBoundaryData P h (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) := ⟨hC.2.1, hC.2.2.1⟩
  have hh' := isGFFWithBoundaryData_flowField_zero hhh c
  rw [← coe_forceJumpFinset] at hh'
  have hh₂ : IsGFFWithBoundaryData P₂ h₂ b (forceJumpFinset xL xR) :=
    CfRegQ.isGFFWithBoundaryData_of_map_eq hh' hh₂m hlaw
  have hu_b : IsBoundedHarmonicExtension b (forceJumpFinset xL xR) (fun z => u₀ z + c) := by
    rw [coe_forceJumpFinset]
    exact isBoundedHarmonicExtension_add_const hu₀ c
  have hu₀c : ContinuousOn u₀ H := fun z hz => (hu₀.1 z hz).1.continuousAt.continuousWithinAt
  have hπ₂ : Measurable (cfProj.{u} h₂ W₂ ζ₂) := measurable_up.comp (hh₂m.prodMk hDm)
  set μ := P₂.map (cfProj.{u} h₂ W₂ ζ₂) with hμdef
  have hglue := glueMeasure_map_cfProj hXm hh₂m hDm hlaw hk
  set slit : CfSpace.{u} → Set ℂ := fun q => cfHullQ t q.down.2 with hslit
  set fld : CfSpace.{u} → DistOn upperHalfPlaneOpens := fun q => cenT κ u₀ q.down.1 with hfld
  have hslitm : Measurable[_, hittingSigma] slit := (measurable_cfHullQ t).comp (measurable_snd.comp measurable_down)
  have hfldm : Measurable fld := (measurable_cenT κ u₀).comp (measurable_fst.comp measurable_down)
  -- the counterflow hull is local on the canonical space
  have hG₂ := isLocalSet_cfHullQ_cenT hcf hreg₂ hu₀.1 t
  have hpairm : Measurable fun q : CfSpace.{u} => (slit q, fld q) := hslitm.prodMk hfldm
  have hloc : IsLocalSet slit fld μ := by
    refine IsLocalSet.of_map_eq hG₂ hpairm.aemeasurable (ae_of_all _ fun q => cfHullQ_relClosed t q.down.2) ?_
    rw [hμdef, Measure.map_map hpairm hπ₂]
    rfl
  -- the centred field is a zero-boundary GFF on the canonical space
  have hZglue : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens
      (fun p : Ω × HistorySpace 0 0 => cenT κ u₀ (cfField κ (h p.1)))
      (glueMeasure P k (fun ω => cfField κ (h ω)) hXm) := by
    have e : (fun p : Ω × HistorySpace 0 0 => cenT κ u₀ (cfField κ (h p.1))) =
        fun p => WholeField.centredField h u₀ p.1 := funext fun p => cenT_cfField κ u₀ (h p.1)
    rw [e]
    exact isZeroBoundaryGFF_comp_of_map_eq (g := WholeField.centredField h u₀) (f := Prod.fst) measurable_fst
      (glueMeasure_fst (μ := P) k hXm) (WholeField.isZeroBoundaryGFF_centredField hC hu₀)
  have hZ : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens fld μ := by
    refine ⟨hfldm, ?_⟩
    rw [hμdef, ← hglue]
    exact Restart.isZBGFFProcess_map (measurable_glueProjCf hXm)
      (fun φ => (LQGMetric.measurable_distOn_apply φ).comp hfldm) hZglue.process
  obtain ⟨g, hg⟩ := LocalSets.IsLocalSet.exists_isLocalSetMean hZ hslitm hloc
  refine ⟨g, ?_, fun φ => ?_⟩
  · exact IsLocalSetMean.comp (measurable_glueProjCf hXm) hglue hslitm hfldm hg
  · obtain ⟨g₂, hg₂, hid₂⟩ := exists_isLocalSetMean_cfHullQ hκ hb hh₂ hcf hreg₂ hu_b hu' t huG
    have hgc : IsLocalSetMean (fun ω => cfHullQ t (cfHistory W₂ ζ₂ ω)) (fun ω => cenT κ u₀ (h₂ ω)) P₂
        (fun ω => g (cfProj h₂ W₂ ζ₂ ω)) :=
      IsLocalSetMean.comp hπ₂ rfl hslitm hfldm hg
    have e : (fun ω => cenT κ u₀ (h₂ ω)) = fun ω => h₂ ω - smoothDist upperHalfPlaneOpens (fun z => u₀ z + c) :=
      funext fun ω => cenT_eq_sub κ hu₀c (h₂ ω)
    rw [e] at hgc
    have hAm : Measurable[mΩ₂, hittingSigma] fun ω => cfHullQ t (cfHistory W₂ ζ₂ ω) :=
      (measurable_cfHullQ t).comp hDm
    have hFm : Measurable fun ω => h₂ ω - smoothDist upperHalfPlaneOpens (fun z => u₀ z + c) :=
      (WholeField.measurable_sub_dist _).comp hh₂m
    have heq := LocalSets.IsLocalSetMean.ae_apply_eq hAm hFm hgc hg₂ φ
    filter_upwards [heq, hid₂] with ω e1 e2 hφ
    exact e1.trans (e2 φ hφ)

end GlueMean

end InteractingSLE.Sec5.GlueCond
