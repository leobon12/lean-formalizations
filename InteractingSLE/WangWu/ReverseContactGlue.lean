/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.ReverseContactLocal
import InteractingSLE.WangWu.PrefixLocal
import InteractingSLE.Spec.Coupling.WholeField7Main
import InteractingSLE.Spec.Coupling.WholeField2Kernel

/-!
# Proposition 4.18, step (S2): the two stopped slits are a local set on the glued space

Packet PROVE-WW-B11. Wang–Wu (`source/external/WW17LP/wang_wu_lean_preprocessed.pdf`, ruling R31), proof of
Proposition 4.18 (text dump L1604–1611):

> Conditionally on `h`, sample a forward line `α` and a reverse line `β` independently. Fix a finite positive stopping
> time `s` for `β`. For each deterministic forward time before contact, the independent-union lemma makes the two
> stopped slits a local set.

This is step (S2) of PROVE-WW-B10's obstruction for `ReverseTipContactStatement`. In the setting of that statement
(a forward coupling of the two-seed word `(r_L; r_R)`, a reverse coupling of `(r_R; r_L)` whose reflected field has the
forward law, and a regular conditional law `k` of the reverse history given the reflected field), at deterministic
rational times `t, s > 0`:

* `histHull t y = ℍ ∩ closure (histLine y '' ([0, t] ∩ ℚ))` is the stopped hull read from a dyadic history `y`; it is
  hitting-measurable and relatively closed for **every** `y` (`measurable_histHull`, `histHull_relClosed`), and it is
  the Loewner hull `η(0, t]` almost surely (`ae_histHull_eq_fwdHull`);
* `isFullLevelLineCoupling_twoSeed`: a frozen coupling of a nonnegative two-seed word is a full level-line coupling
  (whole-field identification, rulings R38 Part C and R40);
* **`isLocalSet_twoSlit_glue`**: on the glued space `P ⊗ k(h)`, `α(0, t] ∪ R(β(0, s])` is a local set of the centred
  field `h − u₀` (`u₀` the bounded harmonic extension of the forward boundary data).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE.WangWu

open QuantumZipper (H fwdHull)
open LQGMetric (DistOn TestOn)
open LawUnique

universe u

/-! ### The stopped hull read from a history -/

section HistHull

variable {nL nR : ℕ}

/-- **The stopped hull read from a dyadic history**: `ℍ ∩ closure (histLine y '' ([0, t] ∩ ℚ))`. For the history of a
simple trace it is the hull `η(0, t]`; for every `y` it is relatively closed in `ℍ` and hitting-measurable. -/
def histHull (t : ℚ) (y : HistorySpace nL nR) : Set ℂ := H ∩ closure (histLine y '' ratWindow 0 t)

theorem histHull_relClosed (t : ℚ) (y : HistorySpace nL nR) :
    histHull t y ⊆ H ∧ IsOpen (H \ histHull t y) := by
  refine ⟨inter_subset_left, ?_⟩
  have e : H \ histHull t y = H \ closure (histLine y '' ratWindow 0 t) := by
    ext z
    constructor
    · rintro ⟨hzH, hz⟩
      exact ⟨hzH, fun hc => hz ⟨hzH, hc⟩⟩
    · rintro ⟨hzH, hz⟩
      exact ⟨hzH, fun hc => hz hc.2⟩
  rw [e]
  exact QuantumZipper.isOpen_H.sdiff isClosed_closure

/-- **The stopped hull read from a history is hitting-measurable.** -/
theorem measurable_histHull (t : ℚ) :
    Measurable[_, hittingSigma] fun y : HistorySpace nL nR => histHull t y := by
  refine measurable_generateFrom ?_
  rintro _ ⟨U, hUo, hUH, rfl⟩
  have e : (fun y : HistorySpace nL nR => histHull t y) ⁻¹' {A | (A ∩ U).Nonempty} =
      ⋃ q : ℚ, {y | (0 : ℚ) ≤ q ∧ q ≤ t} ∩ (fun y : HistorySpace nL nR => histLine y q) ⁻¹' U := by
    ext y
    simp only [mem_preimage, mem_ofPred_eq, mem_iUnion, mem_inter_iff]
    have e1 : (histHull t y ∩ U).Nonempty ↔ (closure (histLine y '' ratWindow 0 t) ∩ U).Nonempty := by
      constructor
      · rintro ⟨z, ⟨-, hz⟩, hzU⟩
        exact ⟨z, hz, hzU⟩
      · rintro ⟨z, hz, hzU⟩
        exact ⟨z, ⟨hUH hzU, hz⟩, hzU⟩
    rw [e1, closure_inter_open_nonempty_iff hUo]
    constructor
    · rintro ⟨_, ⟨_, ⟨q, rfl, hq0, hqt⟩, rfl⟩, hU⟩
      exact ⟨q, ⟨hq0, hqt⟩, hU⟩
    · rintro ⟨q, ⟨hq0, hqt⟩, hU⟩
      exact ⟨_, ⟨_, ⟨q, rfl, hq0, hqt⟩, rfl⟩, hU⟩
  rw [e]
  exact MeasurableSet.iUnion fun q => (MeasurableSet.const _).inter (measurable_histLine (q : ℝ) hUo.measurableSet)

/-- The rational times of `[0, t]` are dense in `[0, t]`. -/
theorem Icc_subset_closure_ratWindow {t : ℚ} : Icc (0 : ℝ) t ⊆ closure (ratWindow 0 t) := by
  intro s hs
  rcases eq_or_lt_of_le hs.2 with h | h
  · exact subset_closure ⟨t, h.symm, by exact_mod_cast hs.1.trans h.le, le_rfl⟩
  · exact mem_closure_ratWindow (by exact_mod_cast hs.1) h

theorem ratWindow_subset_Icc (t : ℚ) : ratWindow 0 t ⊆ Icc (0 : ℝ) t := by
  rintro _ ⟨q, rfl, hq0, hqt⟩
  exact ⟨by exact_mod_cast hq0, by exact_mod_cast hqt⟩

/-- For a curve continuous on `[0, t]`, the closure of its rational-time points is its image. -/
theorem closure_image_ratWindow {γ : ℝ → ℂ} {t : ℚ} (hγ : ContinuousOn γ (Icc 0 t)) :
    closure (γ '' ratWindow 0 t) = γ '' Icc 0 t := by
  refine Subset.antisymm (closure_minimal (image_mono (ratWindow_subset_Icc t))
    (isCompact_Icc.image_of_continuousOn hγ).isClosed) ?_
  have hcl : closure (ratWindow 0 t) ⊆ Icc (0 : ℝ) t :=
    closure_minimal (ratWindow_subset_Icc t) isClosed_Icc
  calc γ '' Icc 0 t ⊆ γ '' closure (ratWindow 0 t) := image_mono Icc_subset_closure_ratWindow
    _ ⊆ closure (γ '' ratWindow 0 t) := (hγ.mono hcl).image_closure

/-- **The hull read from the history of a simple proper trace** is its initial piece without the start. -/
theorem histHull_eq_image_Ioc {y : HistorySpace nL nR} {t : ℚ} (hγ : IsProperArc (histLine y)) :
    histHull t y = histLine y '' Ioc 0 t := by
  rw [histHull, closure_image_ratWindow (hγ.cont.mono fun s hs => hs.1)]
  ext z
  constructor
  · rintro ⟨hzH, s, hs, rfl⟩
    refine ⟨s, ⟨lt_of_le_of_ne hs.1 fun h => ?_, hs.2⟩, rfl⟩
    rw [← h, hγ.zero] at hzH
    simp [H] at hzH
  · rintro ⟨s, hs, rfl⟩
    exact ⟨hγ.mem_H s hs.1, s, Ioc_subset_Icc_self hs, rfl⟩

end HistHull

/-! ### The two-seed couplings -/

section TwoSeed

variable {rL rR : ℝ}

/-- **Nonnegative two-seed words are complete at `κ = 4`**: every integrated evolution almost surely has a continuous
transient generating trace (Corollary 4.13 through `IsMarkedChain.ae_seedLine`). -/
theorem isCompleteForceWord_twoSeed (hL : 0 ≤ rL) (hR : 0 ≤ rR) :
    LP.IsCompleteForceWord.{u} 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) := by
  intro Ω mΩ P _ 𝓕 W VL VR B ζ hE
  filter_upwards [IsMarkedChain.ae_seedLine isOrderedForceWord_twoSeed (hasNonnegCumWeights_twoSeed hL hR) hE]
    with ω hω
  obtain ⟨hζ, ⟨η, hη, hline⟩, -, hprop, -⟩ := hω
  refine ⟨η, hζ ▸ hη, fun _ => ?_⟩
  have h1 := hprop.tendsto.comp (NNReal.tendsto_coe_atTop.2 tendsto_id)
  refine h1.congr fun t => ?_
  simp only [Function.comp_apply, hline, Real.toNNReal_coe, id]

/-- **A frozen coupling of a nonnegative two-seed word is a full level-line coupling** (Wang–Wu Definition 1.5),
by the whole-field identification (rulings R38 Part C, R40). -/
theorem isFullLevelLineCoupling_twoSeed {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens} (hL : 0 ≤ rL) (hR : 0 ≤ rR)
    (hC : IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ h) :
    IsFullLevelLineCoupling LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ h := by
  refine hC.isFullLevelLineCoupling (WholeField.hasWholeFieldKernels_of_isCompleteForceWord.{u}
    (isCompleteForceWord_twoSeed hL hR) P 𝓕 W VL VR B ζ h hC) ?_
  filter_upwards [IsMarkedChain.ae_seedLine isOrderedForceWord_twoSeed (hasNonnegCumWeights_twoSeed hL hR) hC.1]
    with ω hω
  obtain ⟨hζ, ⟨η, hη, -⟩, -⟩ := hω
  exact ⟨η, hζ ▸ hη⟩

/-- **The stopped hull read from the history is the Loewner hull** for a marked chain of a nonnegative two-seed word,
almost surely. -/
theorem ae_histHull_eq_fwdHull {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hL : 0 ≤ rL) (hR : 0 ≤ rR)
    (hE : IsMarkedChain LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ) {t : ℚ}
    (ht : 0 < t) :
    ∀ᵐ ω ∂P, histHull t (killedHistory W VL VR ζ ω) =
      fwdHull (fun s : ℝ => W s.toNNReal ω) ((Real.toNNReal t : ℝ≥0) : ℝ) := by
  filter_upwards [IsMarkedChain.ae_seedLine isOrderedForceWord_twoSeed (hasNonnegCumWeights_twoSeed hL hR) hE,
    hE.2.2.2.2] with ω hω hp
  obtain ⟨hζ, -, -, hprop, hhull⟩ := hω
  have hwc : Continuous fun t => W t ω := by
    have h := hp.2.2.2.1
    rw [hζ] at h
    exact continuousOn_univ.1 (h.mono fun t _ => show (t : ℝ≥0∞) < ⊤ from ENNReal.coe_lt_top)
  have hl := histLine_killedHistory (VL := VL) (VR := VR) hζ hwc
  rw [hhull, histHull_eq_image_Ioc (hl ▸ hprop), hl, Real.coe_toNNReal _ (by exact_mod_cast ht.le)]

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
  {h : Ω → DistOn upperHalfPlaneOpens}

/-- **The stopped hull of a two-seed coupling is a local set** of the field (Wang–Wu Corollary 3.9), read from the
history at a positive rational time. -/
theorem isLocalSet_histHull_twoSeed (hL : 0 ≤ rL) (hR : 0 ≤ rR)
    (hC : IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ h)
    {t : ℚ} (ht : 0 < t) :
    IsLocalSet (fun ω => histHull t (killedHistory W VL VR ζ ω)) h P := by
  obtain ⟨u₀, hu₀⟩ := WholeField.exists_bhe 4 (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) LP.twoSeedXL
    LP.twoSeedXR
  obtain ⟨hX, -⟩ := hC.2.2.2
  have hF := isFullLevelLineCoupling_twoSeed hL hR hC
  have hseed := IsMarkedChain.ae_seedLine isOrderedForceWord_twoSeed (hasNonnegCumWeights_twoSeed hL hR) hC.1
  have htr : ∀ᵐ ω ∂P, ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η := by
    filter_upwards [hseed] with ω hω
    obtain ⟨hζ, ⟨η, hη, -⟩, -⟩ := hω
    exact ⟨η, hζ ▸ hη⟩
  have hτζ : ∀ᵐ ω ∂P, ((Real.toNNReal t : WithTop ℝ≥0) : ℝ≥0∞) < ζ ω := by
    filter_upwards [hseed] with ω hω
    rw [hω.1]
    exact ENNReal.coe_lt_top
  have hloc := hF.isLocalSet_hull htr hu₀.1 (WholeField.isZeroBoundaryGFF_centredField hC hu₀) hX
    (isStoppingTime_const (drivingFiltration P hX) (Real.toNNReal t)) hτζ
  refine Coupling.IsLocalSet.congr_set hloc ?_
  filter_upwards [ae_histHull_eq_fwdHull hL hR hC.1 ht] with ω hω
  rw [hω]
  rfl

/-- **Proposition 4.18, step (S2): the two stopped slits are a local set on the glued space.** Let `hC` be a frozen
coupling of the two-seed word `(r_L; r_R)`, `r_L, r_R ≥ 0`, and `hC₂` one of `(r_R; r_L)` whose reflected field
`−h₂ ∘ R` has the law of `h`, and let `k` be a regular conditional law of the reverse killed history given the
reflected field. On the glued space `P ⊗ k(h)`, for rational `t, s > 0`, the union of the forward hull `α(0, t]` and
the reflected reverse hull `R(β(0, s])` (both read from the histories) is a local set of the centred field
`h − u₀`. -/
theorem isLocalSet_twoSlit_glue (hL : 0 ≤ rL) (hR : 0 ≤ rR)
    (hC : IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ h)
    {Ω₂ : Type u} {mΩ₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
    {𝓕₂ : Filtration ℝ≥0 mΩ₂} {W₂ : ℝ≥0 → Ω₂ → ℝ} {VL₂ VR₂ : Fin 1 → ℝ≥0 → Ω₂ → ℝ} {B₂ : ℝ≥0 → Ω₂ → ℝ}
    {ζ₂ : Ω₂ → ℝ≥0∞} {h₂ : Ω₂ → DistOn upperHalfPlaneOpens}
    (hC₂ : IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rR) (fun _ => rL) P₂ 𝓕₂ W₂ VL₂ VR₂ B₂
      ζ₂ h₂)
    (hlaw : P.map h = P₂.map (fun ω => reflectField (h₂ ω)))
    (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 1 1)) [IsMarkovKernel k]
    (hk : P₂.map (fun ω => (reflectField (h₂ ω), killedHistory W₂ VL₂ VR₂ ζ₂ ω)) =
      P₂.map (fun ω => reflectField (h₂ ω)) ⊗ₘ k)
    {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData 4 (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR)
      LP.twoSeedXL LP.twoSeedXR) (forceJumpSet LP.twoSeedXL LP.twoSeedXR) u₀)
    {t s : ℚ} (ht : 0 < t) (hs : 0 < s) :
    IsLocalSet (fun p : Ω × HistorySpace 1 1 => histHull t (killedHistory W VL VR ζ p.1) ∪ negInv '' histHull s p.2)
      (fun p => WholeField.centredField h u₀ p.1) (glueMeasure P k h hC.2.1) := by
  set D := SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀ with hD
  have hDh : IsHarmonicDistOn D H := WholeField.isHarmonicDistOn_smoothDist hu₀.1
  obtain ⟨hX, -⟩ := hC.2.2.2
  obtain ⟨hX₂, -⟩ := hC₂.2.2.2
  have hT : Measurable fun f : DistOn upperHalfPlaneOpens => f - D := WholeField.measurable_sub_dist D
  have hT' : Measurable fun f : DistOn upperHalfPlaneOpens => f + D := Coupling.measurable_add_distOnConst D
  -- the forward hull, on `Ω` and on the glued space
  have hA : IsLocalSet (fun ω => histHull t (killedHistory W VL VR ζ ω)) (fun ω => h ω - D) P :=
    WholeField.IsLocalSet.sub_dist (isLocalSet_histHull_twoSeed hL hR hC ht) hDh
  have hAm : Measurable[mΩ, hittingSigma] fun ω => histHull t (killedHistory W VL VR ζ ω) :=
    (measurable_histHull t).comp (measurable_killedHistory hX)
  have hAg := IsLocalSet.glue_fst hC.2.1 k (T := fun f => f - D) hA
  -- the reflected reverse hull, on `Ω₂` and on the glued space
  have hG₂ : IsLocalSet (fun ω => negInv '' histHull s (killedHistory W₂ VL₂ VR₂ ζ₂ ω))
      (fun ω => reflectField (h₂ ω) - D) P₂ :=
    WholeField.IsLocalSet.sub_dist (IsLocalSet.reflect (isLocalSet_histHull_twoSeed hR hL hC₂ hs)) hDh
  have hGm : Measurable[_, hittingSigma] fun y : HistorySpace 1 1 => negInv '' histHull s y :=
    measurable_image_negInv.comp (measurable_histHull s)
  have hGg := IsLocalSet.glue_snd hC.2.1 k (measurable_reflectField.comp hC₂.2.1)
    (measurable_killedHistory hX₂) hlaw hk hT hGm MeasurableSet.univ
    (fun y _ => image_negInv_relClosed (histHull_relClosed s y)) (Eventually.of_forall fun _ => mem_univ _) hG₂
  exact IsLocalSet.glue_union hC.2.1 k hT hT' (fun f => sub_add_cancel f D)
    (WholeField.isZeroBoundaryGFF_centredField hC hu₀) hAm hGm hAg hGg

end TwoSeed

end InteractingSLE.WangWu
