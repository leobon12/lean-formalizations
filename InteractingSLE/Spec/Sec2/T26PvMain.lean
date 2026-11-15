/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.T26PvCore
import InteractingSLE.Spec.Sec2.T24BrAdapted
import InteractingSLE.Spec.Sec2.T24BrLive
import InteractingSLE.Spec.Sec2.T24BrV2

/-!
# Theorem 2.6 (statement v2, frozen): the closed provider

Packet PROVE-T26-PROVIDER. The frozen anchor
`InteractingSLE.exists_isIntegratedSLEEvolution_eqOn_of_isContLocalMartingaleBefore_conformalRadius`
(`InteractingSLE/Frozen/Spec/…`, Specification §2.3, p. 40, `source/spec/p001-048.md` L970–L986; horizon of ruling
R109) is proved here with no additional hypotheses, from its frozen definitions.

Reduction to the core (`exists_evolution_eqOn_core`): choose a measurable conull set `G` of samples on which the driver
is continuous from `0`, generates the curve, and the given force processes are its geometric images. Modify the driver
off `G` (`Wc = W` on `G`, `0` off `G`): it is everywhere continuous from `0` and adapted to the augmented curve
filtration (`T24Bridge.stronglyAdapted_driver_curveFiltration`; `G` is in every usual augmentation). The martingale
hypothesis is read with the explicit harmonic extension `MartChar.meanExt`; the bracket is put in explicit Loewner form
(`Certify2426.isContLocalMartingaleBefore_sq_sub_iff`); both pass to the modified processes and the modified lifetime
(`T24Bridge.isContLocalMartingaleBeforeV2_of_ae_eq`), which agree with the given ones on `G`. The core gives the
evolution on `Ω × (ℕ → ℝ)` with `π = Prod.fst`; on `π⁻¹ G` (conull) the modified processes are the given ones.

* `exists_isIntegratedSLEEvolution_eqOn_of_isContLocalMartingaleBefore_conformalRadius`: the anchor's statement;
* `Seal.…`: the same with all arguments implicit and the hypotheses auto-parameters (provider convention), so the
  anchor's body is the bare `by exact`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Sec2.T26Pv

open Sec7 MartChar PocketTraversal

section MeasHelp2

variable {α : Type*} {m : MeasurableSpace α}

/-- `if · ∈ s then f else g` is measurable (binder σ-algebra, so that it applies to `Measurable[𝓖 t]`). -/
theorem measurable_ite_of {s : Set α} [DecidablePred (· ∈ s)] (hs : MeasurableSet s) {f g : α → ℝ}
    (hf : Measurable f) (hg : Measurable g) : Measurable fun a => if a ∈ s then f a else g a :=
  Measurable.ite hs hf hg

end MeasHelp2

/-- **Theorem 2.6 (one-point martingale characterization)**, Specification §2.3, p. 40: exactly the statement of
the frozen anchor `InteractingSLE.exists_isIntegratedSLEEvolution_eqOn_of_isContLocalMartingaleBefore_conformalRadius`
(binders verbatim; the measurability binders `hVL`, `hVR` are not needed by the proof). -/
theorem exists_isIntegratedSLEEvolution_eqOn_of_isContLocalMartingaleBefore_conformalRadius {κ : ℝ}
    (hκ : 0 < κ) {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hF : IsOrderedForceWord xL xR) {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {η : ℝ≥0 → Ω → ℂ} (hη : ∀ t, StronglyMeasurable (η t))
    {W : ℝ≥0 → Ω → ℝ} (hW : ∀ t, Measurable (W t))
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    (hVL : ∀ i t, Measurable (VL i t)) (hVR : ∀ j t, Measurable (VR j t))
    (hηW : ∀ᵐ ω ∂P, Continuous (fun t => W t ω) ∧ W 0 ω = 0 ∧
      IsGeneratingTrace (fun t => W t ω) ⊤ (fun t => η t ω) ∧
      (∀ t, η t ω ∈ closure QuantumZipper.H) ∧ Tendsto (fun t => ‖η t ω‖) atTop atTop)
    (hV : ∀ᵐ ω ∂P, (∀ i, IsLeftForceImage (fun t => W t ω) (xL i) (fun t => VL i t ω)) ∧
      ∀ j, IsRightForceImage (fun t => W t ω) (xR j) (fun t => VR j t ω))
    {z : ℂ} (hz : z ∈ QuantumZipper.H)
    (hmart : ∀ u : Ω → ℝ≥0 → ℂ → ℝ,
      (∀ ω t, IsBoundedHarmonicExtension
        (forceBoundaryData κ ρL ρR (fun i => VL i t ω - W t ω) (fun j => VR j t ω - W t ω))
        (forceJumpSet (fun i => VL i t ω - W t ω) (fun j => VR j t ω - W t ω)) (u ω t)) →
      IsContLocalMartingaleBefore (usualAugmentation (Filtration.natural η hη) P) P
          (fun ω => ((min (QuantumZipper.swallowTime (fun s : ℝ => W s.toNNReal ω) z)
            (continuationThreshold ρL ρR (fun s => W s ω) (fun i s => VL i s ω)
              (fun j s => VR j s ω)) : ℝ≥0∞) : WithTop ℝ≥0))
          (fun t ω => couplingMean κ (fun s : ℝ => W s.toNNReal ω) t (u ω t) z) ∧
        ∃ A : ℝ≥0 → Ω → ℝ,
          (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
            (t : ℝ≥0∞) < min (QuantumZipper.swallowTime (fun s : ℝ => W s.toNNReal ω) z)
              (continuationThreshold ρL ρR (fun s => W s ω) (fun i s => VL i s ω)
                (fun j s => VR j s ω)) →
            ∃ r₀ r : ℝ, IsConformalRadius QuantumZipper.H z r₀ ∧
              IsConformalRadius (connectedComponentIn (QuantumZipper.H \
                QuantumZipper.fwdHull (fun s : ℝ => W s.toNNReal ω) t) z) z r ∧
              A t ω = Real.log (r₀ / r)) ∧
          IsContLocalMartingaleBefore (usualAugmentation (Filtration.natural η hη) P) P
            (fun ω => ((min (QuantumZipper.swallowTime (fun s : ℝ => W s.toNNReal ω) z)
              (continuationThreshold ρL ρR (fun s => W s ω) (fun i s => VL i s ω)
                (fun j s => VR j s ω)) : ℝ≥0∞) : WithTop ℝ≥0))
            (fun t ω => couplingMean κ (fun s : ℝ => W s.toNNReal ω) t (u ω t) z ^ 2 - A t ω)) :
    ∃ (Ω' : Type u) (mΩ' : MeasurableSpace Ω') (P' : Measure Ω') (π : Ω' → Ω),
      MeasurePreserving π P' P ∧
      ∃ (𝓕' : Filtration ℝ≥0 mΩ') (W' : ℝ≥0 → Ω' → ℝ) (VL' : Fin nL → ℝ≥0 → Ω' → ℝ)
        (VR' : Fin nR → ℝ≥0 → Ω' → ℝ) (B : ℝ≥0 → Ω' → ℝ) (ζ : Ω' → ℝ≥0∞),
        IsIntegratedSLEEvolution κ xL xR ρL ρR P' 𝓕' W' VL' VR' B ζ ∧
          ∀ᵐ ω' ∂P', ∀ t : ℝ≥0,
            (t : ℝ≥0∞) < min (QuantumZipper.swallowTime (fun s : ℝ => W s.toNNReal (π ω')) z)
              (continuationThreshold ρL ρR (fun s => W s (π ω')) (fun i s => VL i s (π ω'))
                (fun j s => VR j s (π ω'))) →
            W' t ω' = W t (π ω') ∧ (∀ i, VL' i t ω' = VL i t (π ω')) ∧
              ∀ j, VR' j t ω' = VR j t (π ω') := by
  classical
  set 𝓖 := usualAugmentation (Filtration.natural η hη) P with h𝓖
  have hgen : ∀ᵐ ω ∂P, Continuous (W · ω) ∧ IsGeneratingTrace (W · ω) ⊤ (η · ω) :=
    hηW.mono fun _ h => ⟨h.1, h.2.2.1⟩
  have hWa : StronglyAdapted 𝓖 W := T24Bridge.stronglyAdapted_driver_curveFiltration hη hW hgen
  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 (hηW.and hV))
  set G : Set Ω := Nᶜ with hGd
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by
    simpa only [hGd, mem_compl_iff] using measure_eq_zero_iff_ae_notMem.1 hN0
  have hgood : ∀ ω ∈ G, (Continuous (fun t => W t ω) ∧ W 0 ω = 0 ∧
      IsGeneratingTrace (fun t => W t ω) ⊤ (fun t => η t ω) ∧
      (∀ t, η t ω ∈ closure QuantumZipper.H) ∧ Tendsto (fun t => ‖η t ω‖) atTop atTop) ∧
      ((∀ i, IsLeftForceImage (fun t => W t ω) (xL i) (fun t => VL i t ω)) ∧
        ∀ j, IsRightForceImage (fun t => W t ω) (xR j) (fun t => VR j t ω)) := by
    intro ω hω
    by_contra hb
    exact hω (hNsub hb)
  have hG𝓖 : ∀ t, MeasurableSet[𝓖 t] G := fun t =>
    (Ito.measurableSet_usualAugmentation_of_null hNm hN0 t).compl
  -- the modified driver
  set Wc : ℝ≥0 → Ω → ℝ := fun t ω => if ω ∈ G then W t ω else 0 with hWcd
  have hWcG : ∀ ω ∈ G, (fun t => Wc t ω) = fun t => W t ω := fun ω hω => funext fun t => by
    simp only [hWcd, hω, ite_true]
  have hWcc : ∀ ω, Continuous fun t => Wc t ω := fun ω => by
    by_cases hω : ω ∈ G
    · rw [hWcG ω hω]; exact (hgood ω hω).1.1
    · simp only [hWcd, hω, ite_false]; exact continuous_const
  have hWc0 : ∀ ω, Wc 0 ω = 0 := fun ω => by
    by_cases hω : ω ∈ G
    · simp only [hWcd, hω, ite_true]; exact (hgood ω hω).1.2.1
    · simp only [hWcd, hω, ite_false]
  have hWca : StronglyAdapted 𝓖 Wc := fun t =>
    (@measurable_ite_of Ω (𝓖 t) G _ (hG𝓖 t) _ _ (hWa t).measurable measurable_const).stronglyMeasurable
  set VLc := geomLW Wc (fun _ : Ω => xL) with hVLcd
  set VRc := geomRW Wc (fun _ : Ω => xR) with hVRcd
  have hVLe : ∀ ω ∈ G, ∀ i t, VL i t ω = VLc i t ω := fun ω hω i t => by
    have h := (hgood ω hω).2.1 i
    rw [← hWcG ω hω] at h
    exact T24Bridge.V2.left_eq_geom (W := Wc) (VL := VL) h t
  have hVRe : ∀ ω ∈ G, ∀ j t, VR j t ω = VRc j t ω := fun ω hω j t => by
    have h := (hgood ω hω).2.2 j
    rw [← hWcG ω hω] at h
    exact T24Bridge.V2.right_eq_geom (W := Wc) (VR := VR) h t
  have hwp : ∀ ω ∈ G, MartChar.wpath Wc ω = fun s : ℝ => W s.toNNReal ω := fun ω hω => funext fun s => by
    simp only [MartChar.wpath, hWcd, hω, ite_true]
  have hrp : ∀ ω ∈ G, Ito.rpath (Wc · ω) = fun s : ℝ => W s.toNNReal ω := fun ω hω => funext fun s => by
    simp only [Ito.rpath, hWcd, hω, ite_true]
  -- the lifetimes agree on `G`
  have hσeq : ∀ ω ∈ G, min (QuantumZipper.swallowTime (MartChar.wpath Wc ω) z : WithTop ℝ≥0)
      (thresholdTime ρL ρR (fun t => Wc t ω) (fun i t => VLc i t ω) (fun j t => VRc j t ω)) =
      ((min (QuantumZipper.swallowTime (fun s : ℝ => W s.toNNReal ω) z)
        (continuationThreshold ρL ρR (fun s => W s ω) (fun i s => VL i s ω)
          (fun j s => VR j s ω)) : ℝ≥0∞) : WithTop ℝ≥0) := fun ω hω => by
    rw [hwp ω hω, Certify2426.continuationThreshold_eq_thresholdTime, hWcG ω hω]
    have hL : (fun i s => VL i s ω) = fun i t => VLc i t ω := funext fun i => funext fun s => hVLe ω hω i s
    have hR : (fun j s => VR j s ω) = fun j t => VRc j t ω := funext fun j => funext fun s => hVRe ω hω j s
    rw [hL, hR]
  -- the martingale hypothesis with the explicit harmonic extension
  set U : Ω → ℝ≥0 → ℂ → ℝ := fun ω t =>
    MartChar.meanExt κ ρL ρR (W t ω) (fun i => VL i t ω) (fun j => VR j t ω) with hUd
  obtain ⟨h1, A, hA, h2⟩ := hmart U (fun ω t => MartChar.isBoundedHarmonicExtension_meanExt _ _ _ _ _ _)
  have hWae : ∀ᵐ ω ∂P, Continuous (fun t => W t ω) ∧ W 0 ω = 0 := hηW.mono fun _ h => ⟨h.1, h.2.1⟩
  have h2' := (Certify2426.isContLocalMartingaleBefore_sq_sub_iff (𝓗 := Filtration.natural η hη) hz hWae
    (ξ := fun ω => min (QuantumZipper.swallowTime (fun s : ℝ => W s.toNNReal ω) z)
      (continuationThreshold ρL ρR (fun s => W s ω) (fun i s => VL i s ω) (fun j s => VR j s ω)))
    (fun ω => min_le_left _ _) hA).1 h2
  -- the processes agree on `G`
  have hXeq : ∀ ω ∈ G, ∀ t : ℝ≥0, couplingMean κ (fun s : ℝ => W s.toNNReal ω) t (U ω t) z =
      coupProc κ ρL ρR Wc VLc VRc z t ω := fun ω hω t => by
    have e1 : W t ω = Wc t ω := by simp only [hWcd, hω, ite_true]
    have e2 : (fun i => VL i t ω) = fun i => VLc i t ω := funext fun i => hVLe ω hω i t
    have e3 : (fun j => VR j t ω) = fun j => VRc j t ω := funext fun j => hVRe ω hω j t
    simp only [coupProc, hUd, hwp ω hω]
    rw [e1, e2, e3]
  have hAeq : ∀ ω ∈ G, ∀ t : ℝ≥0, Real.log (2 * z.im / (2 * (QuantumZipper.fwdMap
      (fun s : ℝ => W s.toNNReal ω) t z).im / ‖deriv (QuantumZipper.fwdMap (fun s : ℝ => W s.toNNReal ω) t) z‖)) =
      Aexp Wc z t ω := fun ω hω t => by
    simp only [Aexp, hrp ω hω]
  have hXc : IsContLocalMartingaleBefore 𝓖 P
      (fun ω => min (QuantumZipper.swallowTime (MartChar.wpath Wc ω) z : WithTop ℝ≥0)
        (thresholdTime ρL ρR (fun t => Wc t ω) (fun i t => VLc i t ω) (fun j t => VRc j t ω)))
      (coupProc κ ρL ρR Wc VLc VRc z) :=
    T24Bridge.isContLocalMartingaleBeforeV2_of_ae_eq
      (hGae.mono fun ω hω => ⟨hσeq ω hω, fun t _ => hXeq ω hω t⟩) h1
  have hXAc : IsContLocalMartingaleBefore 𝓖 P
      (fun ω => min (QuantumZipper.swallowTime (MartChar.wpath Wc ω) z : WithTop ℝ≥0)
        (thresholdTime ρL ρR (fun t => Wc t ω) (fun i t => VLc i t ω) (fun j t => VRc j t ω)))
      (fun t ω => coupProc κ ρL ρR Wc VLc VRc z t ω ^ 2 - Aexp Wc z t ω) :=
    T24Bridge.isContLocalMartingaleBeforeV2_of_ae_eq
      (hGae.mono fun ω hω => ⟨hσeq ω hω, fun t _ => by rw [hXeq ω hω t, hAeq ω hω t]⟩) h2'
  -- the core
  obtain ⟨P₀, hP₀, 𝓕', W', VL', VR', B, ζ, hEv, hag⟩ :=
    exists_evolution_eqOn_core hκ hF hWcc hWc0 hWca hz hXc hXAc
  refine ⟨Ω × (ℕ → ℝ), inferInstance, P.prod P₀, Prod.fst, measurePreserving_fst, 𝓕', W', VL', VR', B, ζ,
    hEv, ?_⟩
  filter_upwards [hag, Measure.quasiMeasurePreserving_fst.ae hGae] with p hp hpG t ht
  have ht' : (t : WithTop ℝ≥0) < min (QuantumZipper.swallowTime (MartChar.wpath Wc p.1) z : WithTop ℝ≥0)
      (thresholdTime ρL ρR (fun t => Wc t p.1) (fun i t => VLc i t p.1) (fun j t => VRc j t p.1)) := by
    rw [hσeq p.1 hpG]
    exact ht
  obtain ⟨e1, e2, e3⟩ := hp t ht'
  refine ⟨?_, fun i => ?_, fun j => ?_⟩
  · rw [e1]; simp only [hWcd, hpG, ite_true]
  · rw [e2 i, hVLe p.1 hpG i t]
  · rw [e3 j, hVRe p.1 hpG j t]

namespace Seal

/-- **Theorem 2.6**, closed provider of the frozen anchor
`InteractingSLE.exists_isIntegratedSLEEvolution_eqOn_of_isContLocalMartingaleBefore_conformalRadius`: exactly its type,
all arguments implicit, its hypotheses auto-parameters (provider convention). -/
theorem exists_isIntegratedSLEEvolution_eqOn_of_isContLocalMartingaleBefore_conformalRadius {κ : ℝ}
    (hκ : 0 < κ := by assumption) {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hF : IsOrderedForceWord xL xR := by assumption) {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {η : ℝ≥0 → Ω → ℂ} {hη : ∀ t, StronglyMeasurable (η t)}
    {W : ℝ≥0 → Ω → ℝ} (hW : ∀ t, Measurable (W t) := by assumption)
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    (hVL : ∀ i t, Measurable (VL i t) := by assumption) (hVR : ∀ j t, Measurable (VR j t) := by assumption)
    (hηW : ∀ᵐ ω ∂P, Continuous (fun t => W t ω) ∧ W 0 ω = 0 ∧
      IsGeneratingTrace (fun t => W t ω) ⊤ (fun t => η t ω) ∧
      (∀ t, η t ω ∈ closure QuantumZipper.H) ∧ Tendsto (fun t => ‖η t ω‖) atTop atTop := by assumption)
    (hV : ∀ᵐ ω ∂P, (∀ i, IsLeftForceImage (fun t => W t ω) (xL i) (fun t => VL i t ω)) ∧
      ∀ j, IsRightForceImage (fun t => W t ω) (xR j) (fun t => VR j t ω) := by assumption)
    {z : ℂ} (hz : z ∈ QuantumZipper.H := by assumption)
    (hmart : ∀ u : Ω → ℝ≥0 → ℂ → ℝ,
      (∀ ω t, IsBoundedHarmonicExtension
        (forceBoundaryData κ ρL ρR (fun i => VL i t ω - W t ω) (fun j => VR j t ω - W t ω))
        (forceJumpSet (fun i => VL i t ω - W t ω) (fun j => VR j t ω - W t ω)) (u ω t)) →
      IsContLocalMartingaleBefore (usualAugmentation (Filtration.natural η hη) P) P
          (fun ω => ((min (QuantumZipper.swallowTime (fun s : ℝ => W s.toNNReal ω) z)
            (continuationThreshold ρL ρR (fun s => W s ω) (fun i s => VL i s ω)
              (fun j s => VR j s ω)) : ℝ≥0∞) : WithTop ℝ≥0))
          (fun t ω => couplingMean κ (fun s : ℝ => W s.toNNReal ω) t (u ω t) z) ∧
        ∃ A : ℝ≥0 → Ω → ℝ,
          (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
            (t : ℝ≥0∞) < min (QuantumZipper.swallowTime (fun s : ℝ => W s.toNNReal ω) z)
              (continuationThreshold ρL ρR (fun s => W s ω) (fun i s => VL i s ω)
                (fun j s => VR j s ω)) →
            ∃ r₀ r : ℝ, IsConformalRadius QuantumZipper.H z r₀ ∧
              IsConformalRadius (connectedComponentIn (QuantumZipper.H \
                QuantumZipper.fwdHull (fun s : ℝ => W s.toNNReal ω) t) z) z r ∧
              A t ω = Real.log (r₀ / r)) ∧
          IsContLocalMartingaleBefore (usualAugmentation (Filtration.natural η hη) P) P
            (fun ω => ((min (QuantumZipper.swallowTime (fun s : ℝ => W s.toNNReal ω) z)
              (continuationThreshold ρL ρR (fun s => W s ω) (fun i s => VL i s ω)
                (fun j s => VR j s ω)) : ℝ≥0∞) : WithTop ℝ≥0))
            (fun t ω => couplingMean κ (fun s : ℝ => W s.toNNReal ω) t (u ω t) z ^ 2 - A t ω) := by assumption) :
    ∃ (Ω' : Type u) (mΩ' : MeasurableSpace Ω') (P' : Measure Ω') (π : Ω' → Ω),
      MeasurePreserving π P' P ∧
      ∃ (𝓕' : Filtration ℝ≥0 mΩ') (W' : ℝ≥0 → Ω' → ℝ) (VL' : Fin nL → ℝ≥0 → Ω' → ℝ)
        (VR' : Fin nR → ℝ≥0 → Ω' → ℝ) (B : ℝ≥0 → Ω' → ℝ) (ζ : Ω' → ℝ≥0∞),
        IsIntegratedSLEEvolution κ xL xR ρL ρR P' 𝓕' W' VL' VR' B ζ ∧
          ∀ᵐ ω' ∂P', ∀ t : ℝ≥0,
            (t : ℝ≥0∞) < min (QuantumZipper.swallowTime (fun s : ℝ => W s.toNNReal (π ω')) z)
              (continuationThreshold ρL ρR (fun s => W s (π ω')) (fun i s => VL i s (π ω'))
                (fun j s => VR j s (π ω'))) →
            W' t ω' = W t (π ω') ∧ (∀ i, VL' i t ω' = VL i t (π ω')) ∧
              ∀ j, VR' j t ω' = VR j t (π ω')  :=
  T26Pv.exists_isIntegratedSLEEvolution_eqOn_of_isContLocalMartingaleBefore_conformalRadius hκ hF hη hW hVL hVR hηW hV
    hz hmart

end Seal

end InteractingSLE.Sec2.T26Pv
