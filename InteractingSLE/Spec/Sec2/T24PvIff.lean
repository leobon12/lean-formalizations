import InteractingSLE.Spec.Sec2.T24BrV2Forward
import InteractingSLE.Spec.Sec2.T24BrConverse
import InteractingSLE.Spec.Sec2.T2426Cert

/-!
# Theorem 2.4 (statement v2, frozen): the closed iff

The frozen anchor `InteractingSLE.exists_isIntegratedSLEEvolution_iff_forall_isContLocalMartingaleBefore`
(`InteractingSLE/Frozen/Spec/…`, ruling R109) is proved here with no additional hypotheses, from its frozen
definitions (`IsLeftForceImage`, `IsRightForceImage`, `continuationThreshold`, `IsContLocalMartingaleBefore`,
`usualAugmentation`, `couplingMean`).

* **Forward** (`forward24`, SLE side ⇒ martingale side): the landed `Sec2.T24Bridge.V2.forward24`, whose scoped image
  predicates, threshold and local-martingale predicate are the frozen ones (`Iff.rfl`/`rfl` adapters
  `isLeftForceImage_iff_v2`, `isRightForceImage_iff_v2`, `continuationThreshold_eq_v2`,
  `isContLocalMartingaleBefore_iff_v2`).
* **Converse** (`converse24`): restrict to a measurable conull set `G` of samples on which the driver is continuous,
  starts at `0`, generates the curve, and the given force processes are the geometric images. On the subtype `G` the
  driver is everywhere continuous (bridge (M) is not needed: no modification of the driver), it is adapted to the
  pulled-back augmented curve filtration (bridge (A): `T24Bridge.stronglyAdapted_driver_curveFiltration`), and the
  given force processes are the landed `geomLW`/`geomRW`. The martingale hypothesis, read with the explicit harmonic
  extension `MartChar.meanExt` and modified off `G` (so that its initial value is the constant
  `MartChar.meanExt κ ρL ρR 0 xL xR z`), becomes the landed `MartChar.IsLocalMartingaleBefore` and pulls back to `G`.
  The landed `Restart.ConverseBefore.isRandomWordEvolution_prod` then gives the evolution on `G × (ℕ → ℝ)`, and
  `π = (↑) ∘ Prod.fst` returns exactly the given driver, force processes and threshold.
* `Seal.exists_isIntegratedSLEEvolution_iff_forall_isContLocalMartingaleBefore`: the anchor's type with all arguments
  implicit and its hypotheses auto-parameters (provider convention), so the anchor's body is the bare `by exact`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Sec2.T24Pv

open Sec7.PocketTraversal

/-! ### The frozen definitions are the scoped implementation copies of `Sec2.T24Bridge` -/

/-- The frozen left image is the scoped v2 copy (the bodies agree). -/
theorem isLeftForceImage_iff_v2 {w : ℝ≥0 → ℝ} {x : ℝ} {v : ℝ≥0 → ℝ} :
    IsLeftForceImage w x v ↔ T24Bridge.V2.IsLeftForceImage w x v :=
  Iff.rfl

/-- The frozen right image is the scoped v2 copy (the bodies agree). -/
theorem isRightForceImage_iff_v2 {w : ℝ≥0 → ℝ} {x : ℝ} {v : ℝ≥0 → ℝ} :
    IsRightForceImage w x v ↔ T24Bridge.V2.IsRightForceImage w x v :=
  Iff.rfl

/-- The frozen continuation threshold is the scoped v2 copy (the bodies agree). -/
theorem continuationThreshold_eq_v2 {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (w : ℝ≥0 → ℝ)
    (vL : Fin nL → ℝ≥0 → ℝ) (vR : Fin nR → ℝ≥0 → ℝ) :
    continuationThreshold ρL ρR w vL vR = T24Bridge.V2.continuationThreshold ρL ρR w vL vR :=
  rfl

/-- The frozen local-martingale predicate is the scoped v2 copy (the bodies agree). -/
theorem isContLocalMartingaleBefore_iff_v2 {Ω : Type*} {mΩ : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 mΩ)
    (P : Measure Ω) (ζ : Ω → WithTop ℝ≥0) (X : ℝ≥0 → Ω → ℝ) :
    IsContLocalMartingaleBefore 𝓕 P ζ X ↔ T24Bridge.IsContLocalMartingaleBeforeV2 𝓕 P ζ X :=
  Iff.rfl

/-- **Theorem 2.4, forward implication** (SLE side ⇒ martingale side) with the frozen definitions: the landed
`T24Bridge.V2.forward24` through the adapters above. -/
theorem forward24 {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
    {P : Measure Ω} [IsProbabilityMeasure P] {Q : Measure Ω'} {π : Ω' → Ω}
    {𝓕' : Filtration ℝ≥0 mΩ'} {κ : ℝ} (hκ : 0 < κ) {nL nR : ℕ}
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hF : IsOrderedForceWord xL xR) {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω' → ℝ} {η : ℝ≥0 → Ω → ℂ}
    (hη : ∀ t, StronglyMeasurable (η t)) (hW : ∀ t, Measurable (W t))
    (hgen : ∀ᵐ ω ∂P, Continuous (W · ω) ∧ IsGeneratingTrace (W · ω) ⊤ (η · ω))
    (hV : ∀ᵐ ω ∂P, (∀ i, IsLeftForceImage (W · ω) (xL i) (VL i · ω)) ∧
      ∀ j, IsRightForceImage (W · ω) (xR j) (VR j · ω))
    (hπ : MeasurePreserving π Q P)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR Q 𝓕' (fun t ω => W t (π ω))
      (fun i t ω => VL i t (π ω)) (fun j t ω => VR j t (π ω)) B
      (fun ω => continuationThreshold ρL ρR (fun s => W s (π ω)) (fun i s => VL i s (π ω))
        (fun j s => VR j s (π ω))))
    (U : Ω → ℝ≥0 → ℂ → ℝ)
    (hu : ∀ ω t, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i t ω - W t ω) (fun j => VR j t ω - W t ω))
      (forceJumpSet (fun i => VL i t ω - W t ω) (fun j => VR j t ω - W t ω)) (U ω t))
    {z : ℂ} (hz : z ∈ QuantumZipper.H) :
    IsContLocalMartingaleBefore (usualAugmentation (Filtration.natural η hη) P) P
      (fun ω => ((min (QuantumZipper.swallowTime (fun s : ℝ => W s.toNNReal ω) z)
        (continuationThreshold ρL ρR (fun s => W s ω) (fun i s => VL i s ω)
          (fun j s => VR j s ω)) : ℝ≥0∞) : WithTop ℝ≥0))
      (fun t ω => couplingMean κ (fun s : ℝ => W s.toNNReal ω) t (U ω t) z) :=
  (isContLocalMartingaleBefore_iff_v2 _ _ _ _).2
    (T24Bridge.V2.forward24 hκ hF hη hW hgen
      (hV.mono fun _ h => ⟨fun i => isLeftForceImage_iff_v2.1 (h.1 i),
        fun j => isRightForceImage_iff_v2.1 (h.2 j)⟩) hπ hE U hu hz)

/-- **Theorem 2.4, converse** (martingale side ⇒ SLE side), with the frozen binders: if, for every family of bounded
harmonic extensions, every `𝔥_t(z)` is a continuous local martingale in the augmented curve filtration before
`min (τ_z, T_*)`, then the driver and the given force processes, on an extension `π : Ω' → Ω`, describe an
integrated `SLE_κ(ρ)` evolution up to the continuation threshold. -/
theorem converse24 {κ : ℝ} (hκ : 0 < κ)
    {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hF : IsOrderedForceWord xL xR) {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {η : ℝ≥0 → Ω → ℂ} (hη : ∀ t, StronglyMeasurable (η t))
    {W : ℝ≥0 → Ω → ℝ} (hW : ∀ t, Measurable (W t))
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    (hηW : ∀ᵐ ω ∂P, Continuous (fun t => W t ω) ∧ W 0 ω = 0 ∧
      IsGeneratingTrace (fun t => W t ω) ⊤ (fun t => η t ω) ∧
      (∀ t, η t ω ∈ closure QuantumZipper.H) ∧ Tendsto (fun t => ‖η t ω‖) atTop atTop)
    (hV : ∀ᵐ ω ∂P, (∀ i, IsLeftForceImage (fun t => W t ω) (xL i) (fun t => VL i t ω)) ∧
      ∀ j, IsRightForceImage (fun t => W t ω) (xR j) (fun t => VR j t ω))
    (hmart : ∀ u : Ω → ℝ≥0 → ℂ → ℝ,
        (∀ ω t, IsBoundedHarmonicExtension
          (forceBoundaryData κ ρL ρR (fun i => VL i t ω - W t ω) (fun j => VR j t ω - W t ω))
          (forceJumpSet (fun i => VL i t ω - W t ω) (fun j => VR j t ω - W t ω)) (u ω t)) →
        ∀ z ∈ QuantumZipper.H,
          IsContLocalMartingaleBefore (usualAugmentation (Filtration.natural η hη) P) P
            (fun ω => ((min (QuantumZipper.swallowTime (fun s : ℝ => W s.toNNReal ω) z)
              (continuationThreshold ρL ρR (fun s => W s ω) (fun i s => VL i s ω)
                (fun j s => VR j s ω)) : ℝ≥0∞) : WithTop ℝ≥0))
            (fun t ω => couplingMean κ (fun s : ℝ => W s.toNNReal ω) t (u ω t) z)) :
    ∃ (Ω' : Type u) (mΩ' : MeasurableSpace Ω') (P' : Measure Ω') (π : Ω' → Ω),
        MeasurePreserving π P' P ∧
        ∃ (𝓕' : Filtration ℝ≥0 mΩ') (B : ℝ≥0 → Ω' → ℝ),
          IsIntegratedSLEEvolution κ xL xR ρL ρR P' 𝓕' (fun t ω' => W t (π ω'))
            (fun i t ω' => VL i t (π ω')) (fun j t ω' => VR j t (π ω')) B
            (fun ω' => continuationThreshold ρL ρR (fun s => W s (π ω')) (fun i s => VL i s (π ω'))
              (fun j s => VR j s (π ω'))) := by
  classical
  set 𝓖 := usualAugmentation (Filtration.natural η hη) P
  have hgen : ∀ᵐ ω ∂P, Continuous (W · ω) ∧ IsGeneratingTrace (W · ω) ⊤ (η · ω) :=
    hηW.mono fun _ h => ⟨h.1, h.2.2.1⟩
  have hWa : StronglyAdapted 𝓖 W := T24Bridge.stronglyAdapted_driver_curveFiltration hη hW hgen
  have hall := hηW.and hV
  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hall)
  let G : Set Ω := Nᶜ
  have hGm : MeasurableSet G := hNm.compl
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by
    simpa only [G, mem_compl_iff] using measure_eq_zero_iff_ae_notMem.1 hN0
  have hgood : ∀ ω ∈ G, (Continuous (fun t => W t ω) ∧ W 0 ω = 0 ∧
      IsGeneratingTrace (fun t => W t ω) ⊤ (fun t => η t ω) ∧
      (∀ t, η t ω ∈ closure QuantumZipper.H) ∧ Tendsto (fun t => ‖η t ω‖) atTop atTop) ∧
      ((∀ i, IsLeftForceImage (fun t => W t ω) (xL i) (fun t => VL i t ω)) ∧
        ∀ j, IsRightForceImage (fun t => W t ω) (xR j) (fun t => VR j t ω)) := by
    intro ω hω
    by_contra hb
    exact hω (hNsub hb)
  let Q : Measure G := P.comap ((↑) : G → Ω)
  have hπ : MeasurePreserving ((↑) : G → Ω) Q P := T24Bridge.measurePreserving_conull_subtype hGm hGae
  have : IsProbabilityMeasure (Q.map ((↑) : G → Ω)) := hπ.map_eq.symm ▸ inferInstance
  have : IsProbabilityMeasure Q := Measure.isProbabilityMeasure_of_map hπ.measurable.aemeasurable
  let 𝓖g := T24Bridge.pullbackFiltration 𝓖 ((↑) : G → Ω) hπ.measurable
  let Wg : ℝ≥0 → G → ℝ := fun t ω => W t ω
  have hWgc : ∀ ω, Continuous (Wg · ω) := fun ω => (hgood ω ω.2).1.1
  have hWg0 : ∀ ω, Wg 0 ω = 0 := fun ω => (hgood ω ω.2).1.2.1
  have hWga : StronglyAdapted 𝓖g Wg := fun t =>
    (hWa t).comp_measurable (measurable_iff_comap_le.2 le_rfl)
  have hL : ∀ (ω : G) i t, VL i t ω = geomLW Wg (fun _ => xL) i t ω := fun ω i t =>
    T24Bridge.V2.left_eq_geom (W := Wg) (VL := fun i t (ω : G) => VL i t ω)
      ((hgood ω ω.2).2.1 i) t
  have hR : ∀ (ω : G) j t, VR j t ω = geomRW Wg (fun _ => xR) j t ω := fun ω j t =>
    T24Bridge.V2.right_eq_geom (W := Wg) (VR := fun j t (ω : G) => VR j t ω)
      ((hgood ω ω.2).2.2 j) t
  have hT : ∀ ω : G, continuationThreshold ρL ρR (fun s => W s (ω : Ω)) (fun i s => VL i s ω)
      (fun j s => VR j s ω) = MartChar.thresholdTime ρL ρR (Wg · ω)
        (fun i t => geomLW Wg (fun _ => xL) i t ω)
        (fun j t => geomRW Wg (fun _ => xR) j t ω) := fun ω => by
    rw [Certify2426.continuationThreshold_eq_thresholdTime]
    simp only [hL, hR]
    rfl
  have hVLa := fun i => stronglyAdapted_geomLW hWga hWgc
    (measurable_const : Measurable[𝓖g 0] (fun _ : G => xL)) i
  have hVRa := fun j => stronglyAdapted_geomRW hWga hWgc
    (measurable_const : Measurable[𝓖g 0] (fun _ : G => xR)) j
  have hTst : IsStoppingTime 𝓖g (fun ω => MartChar.thresholdTime ρL ρR (Wg · ω)
      (fun i t => geomLW Wg (fun _ => xL) i t ω)
      (fun j t => geomRW Wg (fun _ => xR) j t ω)) := fun t =>
    MartChar.measurableSet_thresholdTime_le hWgc
      (fun i ω => (isForcePath_geomLW hWgc _ ω i).1)
      (fun j ω => (isForcePath_geomRW hWgc _ ω j).1) hWga hVLa hVRa
      (fun ω i j s t hst he => geomLW_merge hWgc _ ω i j s t hst he)
      (fun ω i j s t hst he => geomRW_merge hWgc _ ω i j s t hst he) t
  have hm : ∀ z ∈ QuantumZipper.H, MartChar.IsLocalMartingaleBefore 𝓖g Q
      (fun ω => min (QuantumZipper.swallowTime (MartChar.wpath Wg ω) z : WithTop ℝ≥0)
        (MartChar.thresholdTime ρL ρR (Wg · ω)
          (fun i t => geomLW Wg (fun _ => xL) i t ω)
          (fun j t => geomRW Wg (fun _ => xR) j t ω)))
      (MartChar.coupProc κ ρL ρR Wg (geomLW Wg (fun _ => xL))
        (geomRW Wg (fun _ => xR)) z) := by
    intro z hz
    let c : ℝ := MartChar.meanExt κ ρL ρR 0 xL xR z
    let U : Ω → ℝ≥0 → ℂ → ℝ := fun ω t =>
      MartChar.meanExt κ ρL ρR (W t ω) (fun i => VL i t ω) (fun j => VR j t ω)
    have h := hmart U (fun ω t => MartChar.isBoundedHarmonicExtension_meanExt _ _ _ _ _ _) z hz
    let X : ℝ≥0 → Ω → ℝ := fun t ω => couplingMean κ (fun s : ℝ => W s.toNNReal ω) t (U ω t) z
    let X' : ℝ≥0 → Ω → ℝ := fun t ω => if ω ∈ G then X t ω else c
    have h' := (Certify2426.isContLocalMartingaleBefore_congr_ae_usualAugmentation (X := X) (Y := X')
      (hGae.mono fun ω hω t _ => by simp only [X', hω, ite_true])).1 h
    have hX0 : X' 0 = fun _ => c := by
      funext ω
      by_cases hω : ω ∈ G
      · have hW0ω : W 0 ω = 0 := (hgood ω hω).1.2.1
        have hVL0 : (fun i => VL i 0 ω) = xL :=
          funext fun i => Certify2426.IsLeftForceImage.apply_zero ((hgood ω hω).2.1 i)
        have hVR0 : (fun j => VR j 0 ω) = xR :=
          funext fun j => Certify2426.IsRightForceImage.apply_zero ((hgood ω hω).2.2 j)
        have hz0 : z ≠ ((fun s : ℝ => W s.toNNReal ω) 0 : ℂ) := fun hzW => by
          have : (0 : ℝ) < z.im := hz
          rw [hzW] at this
          simp at this
        simp only [X', hω, ite_true, X, U, couplingMean, NNReal.coe_zero, QuantumZipper.logDerivFwd,
          intervalIntegral.integral_same, neg_zero, Complex.zero_im, mul_zero, sub_zero, hVL0, hVR0,
          hW0ω]
        rw [Certify2426.fwdMap_time_zero (fun s : ℝ => W s.toNNReal ω) hz0]
        simp [hW0ω, c]
      · simp only [X', hω, ite_false]
    have hloc := Certify2426.IsContLocalMartingaleBefore.isLocalMartingaleBefore h'
      (by rw [hX0]; exact stronglyMeasurable_const) (by rw [hX0]; exact integrable_const _)
    have hp := T24Bridge.isLocalMartingaleBefore_pullback hπ (MeasurableEmbedding.subtype_coe hGm) hloc
    have hXe : (fun t (ω : G) => X' t ω) = MartChar.coupProc κ ρL ρR Wg (geomLW Wg (fun _ => xL))
        (geomRW Wg (fun _ => xR)) z := by
      funext t ω
      simp only [X', ω.2, ite_true, X, U, MartChar.coupProc, hL ω]
      simp only [hR ω]
      rfl
    rw [← hXe]
    convert hp using 1
    funext ω
    exact (congrArg (min (QuantumZipper.swallowTime (MartChar.wpath Wg ω) z)) (hT ω)).symm
  obtain ⟨P₀, hP₀, 𝓦, B, hE, -, -⟩ := Restart.ConverseBefore.isRandomWordEvolution_prod
    (𝒢 := ⊥) (F := Set.univ) hκ bot_le MeasurableSet.univ measurable_const measurable_const
    (fun _ => hF.2.1) (fun _ => hF.2.2.2) (fun _ => hF.1) (fun _ => hF.2.2.1)
    hWg0 hWgc hWga hTst hm (ae_of_all _ fun _ _ => le_rfl)
  obtain ⟨-, -, -, -, hB, hWb, hVLb, hVRb, hpath⟩ := hE
  refine ⟨G × (ℕ → ℝ), inferInstance, Q.prod P₀, fun p => (p.1 : Ω),
    hπ.comp measurePreserving_fst, WholeField.prodFiltration 𝓖g 𝓦, B, ?_⟩
  have hVLe : (fun i t (p : G × (ℕ → ℝ)) => VL i t (p.1 : Ω)) =
      fun i t p => geomLW Wg (fun _ => xL) i t p.1 := by
    funext i t p
    exact hL p.1 i t
  have hVRe : (fun j t (p : G × (ℕ → ℝ)) => VR j t (p.1 : Ω)) =
      fun j t p => geomRW Wg (fun _ => xR) j t p.1 := by
    funext j t p
    exact hR p.1 j t
  have hTe : (fun p : G × (ℕ → ℝ) => continuationThreshold ρL ρR (fun s => W s (p.1 : Ω))
      (fun i s => VL i s (p.1 : Ω)) (fun j s => VR j s (p.1 : Ω))) =
      fun p => (MartChar.thresholdTime ρL ρR (Wg · p.1)
        (fun i t => geomLW Wg (fun _ => xL) i t p.1)
        (fun j t => geomRW Wg (fun _ => xR) j t p.1) : ℝ≥0∞) := by
    funext p
    exact hT p.1
  rw [hVLe, hVRe, hTe]
  exact ⟨hB, hWb, hVLb, hVRb, hpath.mono fun p hp => hp (mem_preimage.2 (mem_univ _))⟩

/-- **Theorem 2.4 (martingale characterization of `SLE_κ(ρ)`)**, Specification §2.3, pp. 34–35, with the horizon of
ruling R109: exactly the statement of the frozen anchor
`InteractingSLE.exists_isIntegratedSLEEvolution_iff_forall_isContLocalMartingaleBefore` (its binders verbatim; the
measurability binders `hVL`, `hVR` are not needed by the proof). -/
theorem exists_isIntegratedSLEEvolution_iff_forall_isContLocalMartingaleBefore {κ : ℝ} (hκ : 0 < κ)
    {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hF : IsOrderedForceWord xL xR) {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {η : ℝ≥0 → Ω → ℂ} (hη : ∀ t, StronglyMeasurable (η t))
    {W : ℝ≥0 → Ω → ℝ} (hW : ∀ t, Measurable (W t))
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    (_hVL : ∀ i t, Measurable (VL i t)) (_hVR : ∀ j t, Measurable (VR j t))
    (hηW : ∀ᵐ ω ∂P, Continuous (fun t => W t ω) ∧ W 0 ω = 0 ∧
      IsGeneratingTrace (fun t => W t ω) ⊤ (fun t => η t ω) ∧
      (∀ t, η t ω ∈ closure QuantumZipper.H) ∧ Tendsto (fun t => ‖η t ω‖) atTop atTop)
    (hV : ∀ᵐ ω ∂P, (∀ i, IsLeftForceImage (fun t => W t ω) (xL i) (fun t => VL i t ω)) ∧
      ∀ j, IsRightForceImage (fun t => W t ω) (xR j) (fun t => VR j t ω)) :
    (∃ (Ω' : Type u) (mΩ' : MeasurableSpace Ω') (P' : Measure Ω') (π : Ω' → Ω),
        MeasurePreserving π P' P ∧
        ∃ (𝓕' : Filtration ℝ≥0 mΩ') (B : ℝ≥0 → Ω' → ℝ),
          IsIntegratedSLEEvolution κ xL xR ρL ρR P' 𝓕' (fun t ω' => W t (π ω'))
            (fun i t ω' => VL i t (π ω')) (fun j t ω' => VR j t (π ω')) B
            (fun ω' => continuationThreshold ρL ρR (fun s => W s (π ω')) (fun i s => VL i s (π ω'))
              (fun j s => VR j s (π ω')))) ↔
      ∀ u : Ω → ℝ≥0 → ℂ → ℝ,
        (∀ ω t, IsBoundedHarmonicExtension
          (forceBoundaryData κ ρL ρR (fun i => VL i t ω - W t ω) (fun j => VR j t ω - W t ω))
          (forceJumpSet (fun i => VL i t ω - W t ω) (fun j => VR j t ω - W t ω)) (u ω t)) →
        ∀ z ∈ QuantumZipper.H,
          IsContLocalMartingaleBefore (usualAugmentation (Filtration.natural η hη) P) P
            (fun ω => ((min (QuantumZipper.swallowTime (fun s : ℝ => W s.toNNReal ω) z)
              (continuationThreshold ρL ρR (fun s => W s ω) (fun i s => VL i s ω)
                (fun j s => VR j s ω)) : ℝ≥0∞) : WithTop ℝ≥0))
            (fun t ω => couplingMean κ (fun s : ℝ => W s.toNNReal ω) t (u ω t) z) := by
  refine ⟨?_, converse24 hκ hF hη hW hηW hV⟩
  rintro ⟨Ω', mΩ', P', π, hπ, 𝓕', B, hE⟩ u hu z hz
  exact forward24 hκ hF hη hW (hηW.mono fun _ h => ⟨h.1, h.2.2.1⟩) hV hπ hE u hu hz

namespace Seal

/-- **Theorem 2.4**, closed provider of the frozen anchor
`InteractingSLE.exists_isIntegratedSLEEvolution_iff_forall_isContLocalMartingaleBefore`: exactly its type, all
arguments implicit, its hypotheses auto-parameters (provider convention). -/
theorem exists_isIntegratedSLEEvolution_iff_forall_isContLocalMartingaleBefore {κ : ℝ}
    (hκ : 0 < κ := by assumption)
    {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hF : IsOrderedForceWord xL xR := by assumption) {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {η : ℝ≥0 → Ω → ℂ} {hη : ∀ t, StronglyMeasurable (η t)}
    {W : ℝ≥0 → Ω → ℝ} (hW : ∀ t, Measurable (W t) := by assumption)
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    (hVL : ∀ i t, Measurable (VL i t) := by assumption) (hVR : ∀ j t, Measurable (VR j t) := by assumption)
    (hηW : ∀ᵐ ω ∂P, Continuous (fun t => W t ω) ∧ W 0 ω = 0 ∧
      IsGeneratingTrace (fun t => W t ω) ⊤ (fun t => η t ω) ∧
      (∀ t, η t ω ∈ closure QuantumZipper.H) ∧ Tendsto (fun t => ‖η t ω‖) atTop atTop := by assumption)
    (hV : ∀ᵐ ω ∂P, (∀ i, IsLeftForceImage (fun t => W t ω) (xL i) (fun t => VL i t ω)) ∧
      ∀ j, IsRightForceImage (fun t => W t ω) (xR j) (fun t => VR j t ω) := by assumption) :
    (∃ (Ω' : Type u) (mΩ' : MeasurableSpace Ω') (P' : Measure Ω') (π : Ω' → Ω),
        MeasurePreserving π P' P ∧
        ∃ (𝓕' : Filtration ℝ≥0 mΩ') (B : ℝ≥0 → Ω' → ℝ),
          IsIntegratedSLEEvolution κ xL xR ρL ρR P' 𝓕' (fun t ω' => W t (π ω'))
            (fun i t ω' => VL i t (π ω')) (fun j t ω' => VR j t (π ω')) B
            (fun ω' => continuationThreshold ρL ρR (fun s => W s (π ω')) (fun i s => VL i s (π ω'))
              (fun j s => VR j s (π ω')))) ↔
      ∀ u : Ω → ℝ≥0 → ℂ → ℝ,
        (∀ ω t, IsBoundedHarmonicExtension
          (forceBoundaryData κ ρL ρR (fun i => VL i t ω - W t ω) (fun j => VR j t ω - W t ω))
          (forceJumpSet (fun i => VL i t ω - W t ω) (fun j => VR j t ω - W t ω)) (u ω t)) →
        ∀ z ∈ QuantumZipper.H,
          IsContLocalMartingaleBefore (usualAugmentation (Filtration.natural η hη) P) P
            (fun ω => ((min (QuantumZipper.swallowTime (fun s : ℝ => W s.toNNReal ω) z)
              (continuationThreshold ρL ρR (fun s => W s ω) (fun i s => VL i s ω)
                (fun j s => VR j s ω)) : ℝ≥0∞) : WithTop ℝ≥0))
            (fun t ω => couplingMean κ (fun s : ℝ => W s.toNNReal ω) t (u ω t) z) :=
  T24Pv.exists_isIntegratedSLEEvolution_iff_forall_isContLocalMartingaleBefore hκ hF hη hW hVL hVR hηW hV

end Seal

end InteractingSLE.Sec2.T24Pv
