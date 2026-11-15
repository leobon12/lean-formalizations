/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB4RTrGood
import InteractingSLE.Spec.Supplement.SB4RSymStaged
import InteractingSLE.Spec.Supplement.FlowDilateFlow

/-!
# The translation symmetry of staged histories

Packet PROVE-T14-SB4LEAF (ruling R104, the initial-arc version). Under the translation `z ↦ z − v` a staged history
`D` of the field `h` (data `b`) is, **with the same drivers**, a staged history of the translated program
`trSpec v spec` for the translated field `affField (−v) h = h(· + v)` (data `affData 1 (−v) b = b(· + v)`), as soon
as the translated run is almost surely the translated run (`ae_run_trState` for regular pieces):

* **`isChartTransport_trChart`**: the chart transport of the translated chart and field;
* `pastMap_tr`, **`ae_condExpKernel_tr`**: the retained pasts are equal, hence the conditional laws agree a.s.;
* **`isStagedHistory_tr`**, **`stagedPiecesRegular_tr`**;
* **`isStagedHistory_tr_regHist`**: the regularized history of a `StagedPiecesRegular` staged history translates.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Complex Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H Hbar)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lf

open Exist.Staged Exist.StagedLaw FlowDilate

/-! ### The chart transport -/

/-- **The chart transport of a translated chart**: if `g` is the transport of `σ f + a` in `c`, it is the transport of
`σ f(· + v) + a` in `trChart v c` (same lift coefficient). -/
theorem isChartTransport_trChart {c : Chart} {σ a k : ℝ} {f g : DistOn upperHalfPlaneOpens}
    (hT : IsChartTransport c σ a k f g) (v : ℝ) :
    IsChartTransport (trChart v c) σ a k (affField (-v) one_pos f) g := by
  intro φ φ' hsupp hφ
  have hψs : tsupport (affTest (-v) one_pos φ) ⊆ c.2.1 '' H := by
    rw [tsupport_affTest]
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨w, hw, hwz⟩ := hsupp hz
    refine ⟨w, hw, ?_⟩
    have e : affInv 1 (-v) z = z + v := by simp [affInv, aff]
    rw [e, ← hwz]
    show c.2.1 w = c.2.1 w - v + v
    ring
  have hψ : ∀ z ∈ c.2.1 '' H, affTest (-v) one_pos φ z = φ' (c.1 z) * ‖deriv c.1 z‖ ^ 2 := by
    rintro _ ⟨w, hw, rfl⟩
    have hz : c.2.1 w - v ∈ (trChart v c).2.1 '' H := ⟨w, hw, rfl⟩
    have h1 := hφ _ hz
    have e1 : aff 1 (-v) (c.2.1 w) = c.2.1 w - v := by simp [aff, sub_eq_add_neg]
    have e2 : (trChart v c).1 (c.2.1 w - v) = c.1 (c.2.1 w) := by
      rw [trChart_fwd, sub_add_cancel]
    have e3 : deriv (trChart v c).1 (c.2.1 w - v) = deriv c.1 (c.2.1 w) := by
      show deriv (fun z => c.1 (z + v)) (c.2.1 w - v) = _
      rw [deriv_comp_add_const, sub_add_cancel]
    rw [affTest_apply, e1, h1, e2, e3, one_pow, one_mul]
  have := hT _ φ' hψs hψ
  rw [this, affField_apply]
  congr 2
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  show c.2.2 (c.2.1 w) * φ' w = c.2.2 (c.2.1 w - v + v) * φ' w
  rw [sub_add_cancel]

/-! ### Staged histories -/

section Staged

variable {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω]

omit mΩ in
/-- The translated retained past is the retained past. -/
theorem pastMap_tr (v : ℝ) {spec : ExplSpec} {D : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {ω : Ω} {k : ℕ}
    (h : ExplState.run κ (affData 1 (-v) b) (affJumps 1 (-v) J) (trSpec v spec) (fun i => D i ω) k =
      trState v (ExplState.run κ b J spec (fun i => D i ω) k)) :
    pastMap κ (affData 1 (-v) b) (affJumps 1 (-v) J) (trSpec v spec) D k ω = pastMap κ b J spec D k ω := by
  funext i
  simp only [pastMap]
  rw [h, trState_retained]

variable [StandardBorelSpace Ω] {P : Measure Ω} [IsFiniteMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}

/-- **The translated retained σ-algebra has almost surely the conditional laws of the original one.** -/
theorem ae_condExpKernel_tr (hb : IsPiecewiseConstantBoundaryData b J) (v : ℝ) {spec : ExplSpec}
    {D : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hD : ∀ k, Measurable (D k)) (hreg : ∀ k ω, IsRegularDriver (D k ω))
    (hpast : ∀ k, pastSigma κ b J spec D k ≤ mΩ)
    (hrel : ∀ᵐ ω ∂P, ∀ k, ExplState.run κ (affData 1 (-v) b) (affJumps 1 (-v) J) (trSpec v spec) (fun i => D i ω) k =
      trState v (ExplState.run κ b J spec (fun i => D i ω) k)) (k : ℕ) :
    ∀ᵐ ω₀ ∂P, condExpKernel P (pastSigma κ (affData 1 (-v) b) (affJumps 1 (-v) J) (trSpec v spec) D k) ω₀ =
      condExpKernel P (pastSigma κ b J spec D k) ω₀ := by
  have hb' := isPiecewiseConstantBoundaryData_affData one_pos (m := -v) hb
  have hpm' : Measurable (pastMap κ (affData 1 (-v) b) (affJumps 1 (-v) J) (trSpec v spec) D k) :=
    measurable_pastMap runMeasStatement hb' (trSpec v spec) (fun j _ => hD j) (fun j _ ω => hreg j ω) k le_rfl
  have hpm : Measurable (pastMap κ b J spec D k) := Measurable.of_comap_le (hpast k)
  have hae : pastMap κ (affData 1 (-v) b) (affJumps 1 (-v) J) (trSpec v spec) D k =ᵐ[P] pastMap κ b J spec D k :=
    hrel.mono fun ω hω => pastMap_tr v (hω k)
  filter_upwards [StagedReg.ae_condExpKernel_eq_of_ae_eq hpm' hpm hae] with ω₀ hK
  rw [pastSigma_eq_comap, hK, ← pastSigma_eq_comap]

/-- **The translation of a staged history** (same drivers), whose drivers are regular at every sample and whose
translated run is almost surely the translated run. -/
theorem isStagedHistory_tr (hb : IsPiecewiseConstantBoundaryData b J) (v : ℝ) {spec : ExplSpec}
    {D : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hD : IsStagedHistory κ b J P h spec D) (hreg : ∀ k ω, IsRegularDriver (D k ω))
    (hrel : ∀ᵐ ω ∂P, ∀ k, ExplState.run κ (affData 1 (-v) b) (affJumps 1 (-v) J) (trSpec v spec) (fun i => D i ω) k =
      trState v (ExplState.run κ b J spec (fun i => D i ω) k)) :
    IsStagedHistory κ (affData 1 (-v) b) (affJumps 1 (-v) J) P (fun ω => affField (-v) one_pos (h ω))
      (trSpec v spec) D := by
  have hb' := isPiecewiseConstantBoundaryData_affData one_pos (m := -v) hb
  refine ⟨hD.1, fun k => (measurable_pastMap runMeasStatement hb' (trSpec v spec) (fun j _ => hD.1 j)
    (fun j _ ω => hreg j ω) k le_rfl).comap_le, hD.2.2.1, fun k => ?_⟩
  filter_upwards [hD.2.2.2 k, ae_condExpKernel_tr hb v hD.1 hreg hD.2.1 hrel k, hrel] with ω₀ h4 hK hω c' θ hl'
  rw [hω (k + 1), trState_launches] at hl'
  obtain ⟨⟨c, θ₀⟩, hl, he⟩ := Option.map_eq_some_iff.1 hl'
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  obtain ⟨b', J', h', hb'', htr, hfl⟩ := h4 c θ₀ hl
  refine ⟨b', J', h', hb'', fun ω => isChartTransport_trChart (htr ω) v, ?_⟩
  rw [hK]
  exact hfl

omit [StandardBorelSpace Ω] [IsFiniteMeasure P] in
/-- **The translation of a staged history with regular pieces has regular pieces.** -/
theorem stagedPiecesRegular_tr (v : ℝ) {spec : ExplSpec} {D : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hR : StagedPiecesRegular κ b J P spec D)
    (hrel : ∀ᵐ ω ∂P, ∀ k, ExplState.run κ (affData 1 (-v) b) (affJumps 1 (-v) J) (trSpec v spec) (fun i => D i ω) k =
      trState v (ExplState.run κ b J spec (fun i => D i ω) k)) :
    StagedPiecesRegular κ (affData 1 (-v) b) (affJumps 1 (-v) J) P (trSpec v spec) D := by
  filter_upwards [hR, hrel] with ω hω hr
  intro k θ t c' hk hl'
  rw [getElem?_trSpec] at hk
  obtain ⟨i, hi, hie⟩ := Option.map_eq_some_iff.1 hk
  have hi' : spec.2.2[k]? = some (.inl (θ, t)) := by
    rcases i with ⟨θ', t'⟩ | pref | ⟨w, pref⟩
    · rw [hi]; exact congrArg some hie
    · simp [trInstr] at hie
    · simp [trInstr] at hie
  rw [hr (k + 1), trState_launches] at hl'
  obtain ⟨⟨c, θ₀⟩, hl, he⟩ := Option.map_eq_some_iff.1 hl'
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  exact hω k θ₀ t c hi' hl

/-- **The regularized history of a `StagedPiecesRegular` staged history translates**: it is, with the same drivers,
a `StagedPiecesRegular` staged history of the translated program for the translated field, and its translated runs
are the translated runs almost surely. -/
theorem isStagedHistory_tr_regHist (hb : IsPiecewiseConstantBoundaryData b J) (v : ℝ) {spec : ExplSpec}
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hE : IsStagedHistory κ b J P h spec E)
    (hR : StagedPiecesRegular κ b J P spec E) :
    IsStagedHistory κ (affData 1 (-v) b) (affJumps 1 (-v) J) P (fun ω => affField (-v) one_pos (h ω))
        (trSpec v spec) (StagedReg.regHist spec E) ∧
      StagedPiecesRegular κ (affData 1 (-v) b) (affJumps 1 (-v) J) P (trSpec v spec) (StagedReg.regHist spec E) ∧
      ∀ᵐ ω ∂P, ∀ k, ExplState.run κ (affData 1 (-v) b) (affJumps 1 (-v) J) (trSpec v spec)
        (fun i => StagedReg.regHist spec E i ω) k = trState v (ExplState.run κ b J spec (fun i => E i ω) k) := by
  have hS := StagedReg.isStagedHistory_regHist hb hE hR
  have hR' := WalkLaw.stagedPiecesRegular_regHist hR
  have hreg : ∀ k ω, IsRegularDriver (StagedReg.regHist spec E k ω) := fun k ω => StagedReg.isRegularDriver_regHist k ω
  have hrel := ae_run_trState (κ := κ) hb v hR' hreg
  refine ⟨isStagedHistory_tr hb v hS hreg hrel, stagedPiecesRegular_tr v hR' hrel, ?_⟩
  filter_upwards [hrel, StagedReg.ae_run_regHist hR] with ω h1 h2 k
  rw [h1 k, h2 k]

end Staged

end InteractingSLE.Theorem14.SB.Lf
