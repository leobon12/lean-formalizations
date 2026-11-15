/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtHLaw
import InteractingSLE.Spec.Sec7.LocalExtHExt

/-!
# Aux. lemma 54: the kernel at the stop, read from the record, in the stopped coupling and in the reference

Packet PROVE-LOCEXT-H, item (M). The record law of `LocalExtHLaw` needs, on both sides, the conditional characteristic
functional of the field off the recorded hull as one fixed Borel functional of the recorded two-seed history
(`HasHistKernel`). That functional is `kerFun κ rL rR`: the Borel version of `Sec4.histCharFun` (Aux. lemma 23's
`Sec4.hasMeasurableHistCharFun`) for the two-seed weights `(rL, rR)`, read through `tsHist`.

* `IsStoppedSeedCoupling.exists_hasHistKernel`: for a stopped seed coupling, clause (e) at `τ = S`, with the bounded
  harmonic extension read from the history at the merged seed positions (`seedVal` centred, `seedVal_sub`);
* `IsStdReference.exists_hasHistKernel`: for a standard reference at its capped local stop, the frozen clause, with the
  history version `refVer = seedProj (histVersion …)`; on an empty seed side the weight is `0`, so the harmonic extension
  read at the normalized position `0` serves for the reference's own position (`isBoundedHarmonicExtension_left_zero`);
* **`map_record_eq`**: the record laws agree once the merged stopped history has the reference's law (input (U)).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology QuantumZipper
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace LocalExt

open Sec7 Sec4 LQGMetric Coupling

/-! ### The kernel functional -/

/-- **The kernel functional on two-seed histories**: a Borel functional that is `Sec4.histCharFun` (the right-hand side of
the frozen conditional-law clause at the recorded stop, two-seed weights `(rL, rR)`) on every continuous history whose
hull avoids `supp φ`. -/
def kerFun (κ rL rR : ℝ) (φ : TestOn upperHalfPlaneOpens) (y : TwoSeedHist) : ℂ :=
  (hasMeasurableHistCharFun κ (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR)).choose φ (tsHist y)

theorem measurable_kerFun (κ rL rR : ℝ) (φ : TestOn upperHalfPlaneOpens) : Measurable (kerFun κ rL rR φ) :=
  ((hasMeasurableHistCharFun κ (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR)).choose_spec.1 φ).comp
    measurable_tsHist

theorem kerFun_eq (κ rL rR : ℝ) {φ : TestOn upperHalfPlaneOpens} {y : TwoSeedHist} (hc : IsContHist (tsHist y))
    (hd : Disjoint (tsupport φ) (tsHull y)) :
    kerFun κ rL rR φ y = histCharFun κ (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) φ (tsHist y) :=
  (hasMeasurableHistCharFun κ (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR)).choose_spec.2 φ _ hc
    (by rwa [← hc.regHull_eq])

/-- **The frozen right-hand side along a driver agreeing with the history's on `[0, S]`** is `histCharFun`. -/
theorem histCharFun_tsOf_eq (κ rL rR : ℝ) {S : ℝ≥0} {X : ℝ≥0 → ℝ × (Fin 1 → ℝ) × (Fin 1 → ℝ)}
    (hX : ContinuousOn X (Iic S)) {w : ℝ≥0 → ℝ} (hwX : ∀ t ≤ S, (X t).1 = w t) (φ : TestOn upperHalfPlaneOpens) :
    histCharFun κ (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) φ (tsHist (tsOf S X)) =
      Complex.exp (Complex.I * ((∫ z, couplingMean κ (fun s : ℝ => w s.toNNReal) S
          (histHarm κ (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) (tsHist (tsOf S X))) z * φ z : ℝ) : ℂ) -
        (((1 / 2 : ℝ) * loewnerGreenEnergy (fun s : ℝ => w s.toNNReal) S φ : ℝ) : ℂ)) := by
  have hstop : (tsHist (tsOf S X)).1.toNNReal = S := histStop_tsHist_tsOf
  have heq : EqOn (fun s : ℝ => w s.toNNReal) (histDrive (tsHist (tsOf S X))) (Icc 0 (S : ℝ)) := by
    intro s hs
    rw [histDrive_tsHist_tsOf hX]
    have hsS : s.toNNReal ≤ S := Real.toNNReal_le_iff_le_coe.2 hs.2
    simp only [min_eq_left hsS, hwX _ hsS]
  have h1 : (∫ z, couplingMean κ (histDrive (tsHist (tsOf S X))) (S : ℝ)
      (histHarm κ (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) (tsHist (tsOf S X))) z * φ z) =
      ∫ z, couplingMean κ (fun s : ℝ => w s.toNNReal) (S : ℝ)
        (histHarm κ (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) (tsHist (tsOf S X))) z * φ z := by
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [couplingMean]
    rw [Ito.fwdMap_congr_of_eqOn heq.symm, Ito.logDerivFwd_congr_of_eqOn heq.symm (NNReal.coe_nonneg _) le_rfl]
  have h2 : loewnerGreenEnergy (histDrive (tsHist (tsOf S X))) (S : ℝ) φ =
      loewnerGreenEnergy (fun s : ℝ => w s.toNNReal) (S : ℝ) φ := by
    unfold loewnerGreenEnergy
    simp_rw [Ito.fwdMap_congr_of_eqOn heq.symm]
  unfold histCharFun
  rw [hstop, h1, h2]

/-- The hull of the driver at `S` lies in the recorded hull. -/
theorem fwdHull_subset_tsHull_tsOf {S : ℝ≥0} {X : ℝ≥0 → ℝ × (Fin 1 → ℝ) × (Fin 1 → ℝ)}
    (hX : ContinuousOn X (Iic S)) {w : ℝ≥0 → ℝ} {a : ℝ≥0∞} (hSa : (S : ℝ≥0∞) < a)
    (hw : ContinuousOn w {t : ℝ≥0 | (t : ℝ≥0∞) < a}) (hwX : ∀ t ≤ S, (X t).1 = w t) :
    fwdHull (fun r : ℝ => w r.toNNReal) S ⊆ tsHull (tsOf S X) := by
  rw [tsHull_tsOf_eq hX hSa hw hwX]
  exact fun z hz => ⟨subset_closure hz, (QuantumZipper.fwdHull_mono (W := fun r : ℝ => w r.toNNReal)).2 _ hz⟩

/-! ### Bounded harmonic extensions and weight-zero marks -/

theorem IsBoundedHarmonicExtension.mono_set {g : ℝ → ℝ} {S S' : Set ℝ} {u : ℂ → ℝ}
    (hu : IsBoundedHarmonicExtension g S u) (h : S ⊆ S') : IsBoundedHarmonicExtension g S' u :=
  ⟨hu.1, hu.2.1, fun x hx => hu.2.2 x fun h' => hx (h h')⟩

/-- A mark of weight `0` does not enter the boundary data, and its position is a possible jump point: a bounded harmonic
extension with the mark at `0` is one with the mark anywhere. -/
theorem isBoundedHarmonicExtension_left_zero {κ : ℝ} {ρR : Fin 1 → ℝ} {vR : Fin 1 → ℝ} {b : Fin 1 → ℝ} {u : ℂ → ℝ}
    (hu : IsBoundedHarmonicExtension (forceBoundaryData κ (fun _ : Fin 1 => (0 : ℝ)) ρR (fun _ => 0) vR)
      (forceJumpSet (fun _ : Fin 1 => (0 : ℝ)) vR) u) :
    IsBoundedHarmonicExtension (forceBoundaryData κ (fun _ : Fin 1 => (0 : ℝ)) ρR b vR) (forceJumpSet b vR) u := by
  have hg : forceBoundaryData κ (fun _ : Fin 1 => (0 : ℝ)) ρR (fun _ => 0) vR =
      forceBoundaryData κ (fun _ : Fin 1 => (0 : ℝ)) ρR b vR := by
    funext x
    simp only [forceBoundaryData, Finset.sum_const_zero]
  rw [hg] at hu
  refine IsBoundedHarmonicExtension.mono_set hu fun x hx => ?_
  simp only [forceJumpSet, mem_insert_iff, mem_union, mem_range] at hx ⊢
  rcases hx with hx | ⟨_, hx⟩ | hx
  · exact Or.inl hx
  · exact Or.inl hx.symm
  · exact Or.inr (Or.inr hx)

theorem isBoundedHarmonicExtension_right_zero {κ : ℝ} {ρL : Fin 1 → ℝ} {vL : Fin 1 → ℝ} {b : Fin 1 → ℝ} {u : ℂ → ℝ}
    (hu : IsBoundedHarmonicExtension (forceBoundaryData κ ρL (fun _ : Fin 1 => (0 : ℝ)) vL (fun _ => 0))
      (forceJumpSet vL (fun _ : Fin 1 => (0 : ℝ))) u) :
    IsBoundedHarmonicExtension (forceBoundaryData κ ρL (fun _ : Fin 1 => (0 : ℝ)) vL b) (forceJumpSet vL b) u := by
  have hg : forceBoundaryData κ ρL (fun _ : Fin 1 => (0 : ℝ)) vL (fun _ => 0) =
      forceBoundaryData κ ρL (fun _ : Fin 1 => (0 : ℝ)) vL b := by
    funext x
    simp only [forceBoundaryData, Finset.sum_const_zero]
  rw [hg] at hu
  refine IsBoundedHarmonicExtension.mono_set hu fun x hx => ?_
  simp only [forceJumpSet, mem_insert_iff, mem_union, mem_range] at hx ⊢
  rcases hx with hx | hx | ⟨_, hx⟩
  · exact Or.inl hx
  · exact Or.inr (Or.inl hx)
  · exact Or.inl hx.symm

/-! ### The stopped coupling -/

section Stopped

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {r : ℝ}
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {Q : Measure Ω} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {S : Ω → WithTop ℝ≥0}
  {h : Ω → DistOn upperHalfPlaneOpens}

theorem seedVal_sub {n : ℕ} (x v : Fin n → ℝ) (w : ℝ) : seedVal x (fun i => v i - w) 0 = seedVal x v w - w := by
  unfold seedVal
  split_ifs <;> simp

/-- The merged two-seed state of an original driving state. -/
def stState (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
    (VR : Fin nR → ℝ≥0 → Ω → ℝ) (ω : Ω) : ℝ≥0 → ℝ × (Fin 1 → ℝ) × (Fin 1 → ℝ) :=
  fun t => (W t ω, fun _ => seedVal xL (fun i => VL i t ω) (W t ω), fun _ => seedVal xR (fun j => VR j t ω) (W t ω))

theorem twoSeedProj_stoppedHistory_eq_tsOf {ω : Ω} {S₀ : ℝ≥0} (hS : S ω = S₀) :
    twoSeedProj xL xR (stoppedHistory (drivingState W VL VR) S ω) = tsOf S₀ (stState xL xR W VL VR ω) := by
  refine Prod.ext hS (funext fun q => ?_)
  simp only [twoSeedProj, stoppedHistory, stopAt_of_eq_coe hS, drivingState, tsOf, stState]

theorem continuousOn_seedVal {n : ℕ} (x : Fin n → ℝ) {v : Fin n → ℝ≥0 → ℝ} {w : ℝ≥0 → ℝ} {s : Set ℝ≥0}
    (hv : ∀ i, ContinuousOn (v i) s) (hw : ContinuousOn w s) :
    ContinuousOn (fun t => seedVal x (fun i => v i t) (w t)) s := by
  unfold seedVal
  split_ifs with h
  · exact hv _
  · exact hw

theorem continuousOn_stState {ω : Ω} {S₀ : ℝ≥0}
    (hc : ContinuousOn (fun t => drivingState W VL VR t ω) (Iic S₀)) :
    ContinuousOn (stState xL xR W VL VR ω) (Iic S₀) := by
  have hW : ContinuousOn (fun t => W t ω) (Iic S₀) := continuous_fst.comp_continuousOn hc
  have hVL : ∀ i, ContinuousOn (fun t => VL i t ω) (Iic S₀) := fun i =>
    ((continuous_apply i).comp (continuous_fst.comp continuous_snd)).comp_continuousOn hc
  have hVR : ∀ j, ContinuousOn (fun t => VR j t ω) (Iic S₀) := fun j =>
    ((continuous_apply j).comp (continuous_snd.comp continuous_snd)).comp_continuousOn hc
  exact hW.prodMk ((continuousOn_pi.2 fun _ => continuousOn_seedVal xL hVL hW).prodMk
    (continuousOn_pi.2 fun _ => continuousOn_seedVal xR hVR hW))

/-- On a regular stop, the record history is the history of the merged state stopped at `S`. -/
theorem stRecHist_eq_tsOf {ω : Ω} (hω : IsRegularStop W VL VR S ω) {S₀ : ℝ≥0} (hS : S ω = S₀) :
    stRecHist xL xR W VL VR S ω = tsOf S₀ (stState xL xR W VL VR ω) := by
  rw [stRecHist, histVersion_eq hω.1 hω.2.1 hω.2.2, twoSeedProj_stoppedHistory_eq_tsOf hS]

theorem continuousOn_stState_of_regular {ω : Ω} (hω : IsRegularStop W VL VR S ω) {S₀ : ℝ≥0} (hS : S ω = S₀) :
    ContinuousOn (stState xL xR W VL VR ω) (Iic S₀) := by
  refine continuousOn_stState (hω.2.2.mono fun t ht => ?_)
  show (t : WithTop ℝ≥0) ≤ S ω
  rw [hS]
  exact WithTop.coe_le_coe.2 ht

/-- **The kernel of a stopped seed coupling at `S`, read from its record** (clause (e) at `τ = S`). -/
theorem IsStoppedSeedCoupling.exists_hasHistKernel (hr : 0 < r)
    (hc : IsStoppedSeedCoupling κ xL xR ρL ρR r Q W VL VR S h) :
    ∃ m : MeasurableSpace Ω, m ≤ mΩ ∧ Measurable[m] (stRecHist xL xR W VL VR S) ∧
      HasHistKernel Q m (stRecHist xL xR W VL VR S) h (kerFun κ (seedSumL xL ρL) (seedSumR xR ρR)) := by
  classical
  have hreg := hc.ae_isRegularStop hr
  obtain ⟨𝓓, hS, -, hb, hWa, hVLa, hVRa, -, -, he⟩ := hc
  refine ⟨hS.measurableSpace, hS.measurableSpace_le,
    (measurable_twoSeedProj xL xR).comp (measurable_histVersion hS hWa hVLa hVRa), fun φ => ?_⟩
  set ρ'L : Fin 1 → ℝ := fun _ => seedSumL xL ρL with hρ'L
  set ρ'R : Fin 1 → ℝ := fun _ => seedSumR xR ρR with hρ'R
  set u : Ω → ℂ → ℝ := fun ω => if IsRegularStop W VL VR S ω then
      histHarm κ ρ'L ρ'R (tsHist (stRecHist xL xR W VL VR S ω)) else
    Classical.choose (exists_isBoundedHarmonicExtension_forceBoundaryData κ ρ'L ρ'R
      (fun _ : Fin 1 => seedPosL xL W VL S ω) (fun _ : Fin 1 => seedPosR xR W VR S ω)) with hudef
  have hu : ∀ ω, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρ'L ρ'R (fun _ : Fin 1 => seedPosL xL W VL S ω) (fun _ : Fin 1 => seedPosR xR W VR S ω))
      (forceJumpSet (fun _ : Fin 1 => seedPosL xL W VL S ω) (fun _ : Fin 1 => seedPosR xR W VR S ω)) (u ω) := by
    intro ω
    by_cases hω : IsRegularStop W VL VR S ω
    · obtain ⟨S₀, hS₀⟩ := WithTop.ne_top_iff_exists.1 hω.2.1
      have hX := continuousOn_stState_of_regular (xL := xL) (xR := xR) hω hS₀.symm
      have hY := stRecHist_eq_tsOf (xL := xL) (xR := xR) hω hS₀.symm
      have hspec := histHarm_spec κ ρ'L ρ'R (tsHist (stRecHist xL xR W VL VR S ω))
      have hpL : (fun i => histVL (tsHist (stRecHist xL xR W VL VR S ω)) i -
          histPath (tsHist (stRecHist xL xR W VL VR S ω)) (tsHist (stRecHist xL xR W VL VR S ω)).1.toNNReal) =
          fun _ : Fin 1 => seedPosL xL W VL S ω := by
        funext i
        rw [hY, histVL_tsHist_tsOf hX, show (tsHist (tsOf S₀ (stState xL xR W VL VR ω))).1.toNNReal = S₀ from
          histStop_tsHist_tsOf, histPath_tsHist_tsOf hX, min_self]
        simp only [stState, seedPosL]
        rw [← seedVal_sub]
        unfold cposL
        rw [← hS₀, WithTop.untopD_coe]
      have hpR : (fun i => histVR (tsHist (stRecHist xL xR W VL VR S ω)) i -
          histPath (tsHist (stRecHist xL xR W VL VR S ω)) (tsHist (stRecHist xL xR W VL VR S ω)).1.toNNReal) =
          fun _ : Fin 1 => seedPosR xR W VR S ω := by
        funext i
        rw [hY, histVR_tsHist_tsOf hX, show (tsHist (tsOf S₀ (stState xL xR W VL VR ω))).1.toNNReal = S₀ from
          histStop_tsHist_tsOf, histPath_tsHist_tsOf hX, min_self]
        simp only [stState, seedPosR]
        rw [← seedVal_sub]
        unfold cposR
        rw [← hS₀, WithTop.untopD_coe]
      rw [hpL, hpR] at hspec
      simp only [hudef, hω, ↓reduceIte]
      exact hspec
    · simp only [hudef, hω, ↓reduceIte]
      exact Classical.choose_spec (exists_isBoundedHarmonicExtension_forceBoundaryData κ ρ'L ρ'R _ _)
  have he' := (he S hS (ae_of_all _ fun _ => le_rfl)).2 u hu φ
  filter_upwards [he', hreg, hb] with ω h1 hω hbω hdis
  obtain ⟨ζ₀, hSζ, -, hcont⟩ := hbω
  obtain ⟨S₀, hS₀⟩ := WithTop.ne_top_iff_exists.1 hω.2.1
  have hX := continuousOn_stState_of_regular (xL := xL) (xR := xR) hω hS₀.symm
  have hY := stRecHist_eq_tsOf (xL := xL) (xR := xR) hω hS₀.symm
  have hSζ' : (S₀ : ℝ≥0∞) < ζ₀ := by rw [← hS₀] at hSζ; exact hSζ
  have hWc : ContinuousOn (fun t => W t ω) {t : ℝ≥0 | (t : ℝ≥0∞) < ζ₀} := continuous_fst.comp_continuousOn hcont
  have hsub := fwdHull_subset_tsHull_tsOf hX hSζ' hWc (fun _ _ => rfl)
  have hun : ((S ω).untopD 0 : ℝ≥0) = S₀ := by rw [← hS₀, WithTop.untopD_coe]
  rw [hY] at hdis
  have hK : Disjoint (tsupport φ) (fwdHull (fun s : ℝ => W s.toNNReal ω) ((S ω).untopD 0 : ℝ≥0)) := by
    rw [hun]
    exact hdis.mono_right hsub
  rw [h1 hK, hY, kerFun_eq κ _ _ (isContHist_tsHist_tsOf hX) hdis,
    histCharFun_tsOf_eq κ _ _ hX (w := fun t => W t ω) (fun _ _ => rfl) φ, hun]
  have huω : u ω = histHarm κ ρ'L ρ'R (tsHist (tsOf S₀ (stState xL xR W VL VR ω))) := by
    simp only [hudef, hω, ↓reduceIte, hY]
  rw [huω]

end Stopped

/-! ### The reference -/

/-- **A bounded harmonic extension at the normalized positions** (an empty seed side, of weight `0`, read at `0`) is one
at the reference's positions. -/
theorem isBoundedHarmonicExtension_of_normalized {κ rL rR a b : ℝ} {pL pR : Prop} [Decidable pL] [Decidable pR]
    (hL : ¬ pL → rL = 0) (hR : ¬ pR → rR = 0) {u : ℂ → ℝ}
    (hu : IsBoundedHarmonicExtension (forceBoundaryData κ (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR)
      (fun _ => if pL then a else 0) (fun _ => if pR then b else 0))
      (forceJumpSet (fun _ : Fin 1 => if pL then a else 0) (fun _ : Fin 1 => if pR then b else 0)) u) :
    IsBoundedHarmonicExtension (forceBoundaryData κ (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) (fun _ => a)
      (fun _ => b)) (forceJumpSet (fun _ : Fin 1 => a) (fun _ : Fin 1 => b)) u := by
  by_cases hpL : pL <;> by_cases hpR : pR <;> simp only [hpL, hpR, ↓reduceIte] at hu
  · exact hu
  · obtain rfl := hR hpR
    exact isBoundedHarmonicExtension_right_zero hu
  · obtain rfl := hL hpL
    exact isBoundedHarmonicExtension_left_zero hu
  · obtain rfl := hL hpL
    obtain rfl := hR hpR
    exact isBoundedHarmonicExtension_right_zero (isBoundedHarmonicExtension_left_zero hu)

section Reference

variable {κ rL rR r : ℝ} {nL nR : ℕ} {Ωr : Type*} {mΩr : MeasurableSpace Ωr} {Pr : Measure Ωr}
  {𝓕r : Filtration ℝ≥0 mΩr} {Wr : ℝ≥0 → Ωr → ℝ} {VLr VRr : Fin 1 → ℝ≥0 → Ωr → ℝ} {Br : ℝ≥0 → Ωr → ℝ}
  {ζr : Ωr → ℝ≥0∞} {hr' : Ωr → DistOn upperHalfPlaneOpens} {Gr : Set Ωr}

/-- **The version of the reference's two-seed history at its capped local stop** that is measurable for the stopped
σ-algebra (empty seed sides normalized). -/
def refVer (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (r : ℝ) (Gr : Set Ωr) (Wr : ℝ≥0 → Ωr → ℝ)
    (VLr VRr : Fin 1 → ℝ≥0 → Ωr → ℝ) (ζr : Ωr → ℝ≥0∞) (ω : Ωr) : TwoSeedHist :=
  seedProj xL xR (histVersion Wr VLr VRr (capStop r Gr ζr Wr) ω)

theorem seedProj_stoppedHistory_drivingState_eq_tsOf (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) {ω : Ωr} {S₀ : ℝ≥0}
    (hS : capStop r Gr ζr Wr ω = S₀) :
    seedProj xL xR (stoppedHistory (drivingState Wr VLr VRr) (capStop r Gr ζr Wr) ω) =
      tsOf S₀ (refState xL xR Wr VLr VRr ω) := by
  classical
  refine Prod.ext hS (funext fun q => ?_)
  simp only [seedProj, stoppedHistory, stopAt_of_eq_coe hS, drivingState, tsOf, refState]

/-- **On the good event the history version is the reference's two-seed history at its capped local stop.** -/
theorem refVer_eq_tsOf (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (hL : -2 < rL) (hR : -2 < rR) (hr : 0 < r)
    (hG : ∀ ω ∈ Gr, IsGoodPath κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) Wr VLr VRr Br ζr ω)
    {ω : Ωr} (hω : ω ∈ Gr) :
    refVer xL xR r Gr Wr VLr VRr ζr ω =
      tsOf ((capStop r Gr ζr Wr ω).untopD 0) (refState xL xR Wr VLr VRr ω) := by
  obtain ⟨hS, hSζ⟩ := capStop_ref hL hR hr hG hω
  have hthr : ¬ ForceWord.ThresholdCondition (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) 0 LP.twoSeedXL
      LP.twoSeedXR := Sec2.Assembly2.not_thr_twoSeed hL hR 0 _ _
  have hpos : 0 < capStop r Gr ζr Wr ω := by
    rw [capStop_eq_localStop hG isOrderedForceWord_twoSeed' (isSeedRadius_twoSeed hr) hthr hω]
    exact localStop_pos hG hthr hr ω
  have hp := (hG ω hω).1
  have hcont : ContinuousOn (fun t => drivingState Wr VLr VRr t ω)
      {t : ℝ≥0 | (t : WithTop ℝ≥0) ≤ capStop r Gr ζr Wr ω} := by
    refine (hp.2.2.2.1.prodMk ((continuousOn_pi.2 fun i => hp.2.2.2.2.1 i).prodMk
      (continuousOn_pi.2 fun i => hp.2.2.2.2.2.1 i))).mono fun t ht => ?_
    have ht' : (t : WithTop ℝ≥0) ≤ (((capStop r Gr ζr Wr ω).untopD 0 : ℝ≥0) : WithTop ℝ≥0) := by
      rw [← hS]; exact ht
    exact lt_of_le_of_lt (show ((t : ℝ≥0) : ℝ≥0∞) ≤ (((capStop r Gr ζr Wr ω).untopD 0 : ℝ≥0) : ℝ≥0∞) from ht') hSζ
  rw [refVer, histVersion_eq hpos (by rw [hS]; exact WithTop.coe_ne_top) hcont,
    seedProj_stoppedHistory_drivingState_eq_tsOf xL xR hS]

/-- On the good event the history version is the record history of the reference. -/
theorem ae_refVer_eq (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (hL : -2 < rL) (hR : -2 < rR) (hr : 0 < r)
    (hG0 : Pr Grᶜ = 0)
    (hG : ∀ ω ∈ Gr, IsGoodPath κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) Wr VLr VRr Br ζr ω) :
    ∀ᵐ ω ∂Pr, refVer xL xR r Gr Wr VLr VRr ζr ω = refRecHist xL xR r Gr Wr VLr VRr ζr ω := by
  have hGP : ∀ᵐ ω ∂Pr, ω ∈ Gr := ae_iff.2 (by exact hG0)
  filter_upwards [hGP] with ω hω
  obtain ⟨hS, hSζ⟩ := capStop_ref hL hR hr hG hω
  rw [refVer_eq_tsOf xL xR hL hR hr hG hω, refRecHist_eq_tsOf xL xR hS hSζ]

/-- **The kernel of a two-seed coupling at its capped local stop, read from the history version** (the frozen clause
at the stop `capStop`; on an empty seed side the weight is `0`). -/
theorem exists_hasHistKernel_ref (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (hL : -2 < rL) (hR : -2 < rR) (hr : 0 < r)
    (hC : IsOptionalHullCoupling κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) Pr 𝓕r Wr VLr VRr Br ζr hr')
    (hGm : MeasurableSet Gr) (hG0 : Pr Grᶜ = 0)
    (hG : ∀ ω ∈ Gr, IsGoodPath κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) Wr VLr VRr Br ζr ω)
    (hrL : (¬ ∃ i, xL i = 0) → rL = 0) (hrR : (¬ ∃ j, xR j = 0) → rR = 0) :
    ∃ m : MeasurableSpace Ωr, m ≤ mΩr ∧ Measurable[m] (refVer xL xR r Gr Wr VLr VRr ζr) ∧
      HasHistKernel Pr m (refVer xL xR r Gr Wr VLr VRr ζr) hr' (kerFun κ rL rR) := by
  classical
  obtain ⟨hXr, hker⟩ := hC.2.2.2
  have hŜ := isStoppingTime_capStop hXr hGm hG0 hG r
  have hdl : killedDrivingFiltration hXr ≤ drivingFiltration Pr hXr := Ito.le_usualAugmentation _ Pr
  have hSle : ∀ s : ℝ≥0, MeasurableSet[drivingFiltration Pr hXr s]
      {ω | ((capStop r Gr ζr Wr ω : WithTop ℝ≥0) : ℝ≥0∞) ≤ (s : ℝ≥0∞)} := fun s => hŜ s
  have hSζ : ∀ ω, ((capStop r Gr ζr Wr ω : WithTop ℝ≥0) : ℝ≥0∞) ≤ ζr ω := fun ω => capStop_le r ω
  have hWa := (Ito.adaptedBefore_mono hdl (Coupling.adaptedBefore_killedDriving_W hXr)).of_le hSle hSζ
  have hVLa := fun i => (Ito.adaptedBefore_mono hdl (Coupling.adaptedBefore_killedDriving_VL hXr i)).of_le hSle hSζ
  have hVRa := fun j => (Ito.adaptedBefore_mono hdl (Coupling.adaptedBefore_killedDriving_VR hXr j)).of_le hSle hSζ
  refine ⟨hŜ.measurableSpace, hŜ.measurableSpace_le,
    (measurable_seedProj xL xR).comp (measurable_histVersion hŜ hWa hVLa hVRa), fun φ => ?_⟩
  set ρ'L : Fin 1 → ℝ := fun _ => rL with hρ'L
  set ρ'R : Fin 1 → ℝ := fun _ => rR with hρ'R
  set u : Ωr → ℂ → ℝ := fun ω => if ω ∈ Gr then histHarm κ ρ'L ρ'R (tsHist (refVer xL xR r Gr Wr VLr VRr ζr ω)) else
    Classical.choose (exists_isBoundedHarmonicExtension_forceBoundaryData κ ρ'L ρ'R
      (fun i => VLr i ((capStop r Gr ζr Wr ω).untopD 0) ω - Wr ((capStop r Gr ζr Wr ω).untopD 0) ω)
      (fun i => VRr i ((capStop r Gr ζr Wr ω).untopD 0) ω - Wr ((capStop r Gr ζr Wr ω).untopD 0) ω)) with hudef
  have hu : ∀ ω, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρ'L ρ'R
        (fun i => VLr i ((capStop r Gr ζr Wr ω).untopD 0) ω - Wr ((capStop r Gr ζr Wr ω).untopD 0) ω)
        (fun i => VRr i ((capStop r Gr ζr Wr ω).untopD 0) ω - Wr ((capStop r Gr ζr Wr ω).untopD 0) ω))
      (forceJumpSet
        (fun i => VLr i ((capStop r Gr ζr Wr ω).untopD 0) ω - Wr ((capStop r Gr ζr Wr ω).untopD 0) ω)
        (fun i => VRr i ((capStop r Gr ζr Wr ω).untopD 0) ω - Wr ((capStop r Gr ζr Wr ω).untopD 0) ω)) (u ω) := by
    intro ω
    by_cases hω : ω ∈ Gr
    · set S₀ : ℝ≥0 := (capStop r Gr ζr Wr ω).untopD 0 with hS₀
      obtain ⟨hS, hSζ'⟩ := capStop_ref hL hR hr hG hω
      have hX := continuousOn_refState xL xR (hG ω hω) hSζ'
      have hY := refVer_eq_tsOf xL xR hL hR hr hG hω
      have hspec := histHarm_spec κ ρ'L ρ'R (tsHist (refVer xL xR r Gr Wr VLr VRr ζr ω))
      have hstop : (tsHist (tsOf S₀ (refState xL xR Wr VLr VRr ω))).1.toNNReal = S₀ := histStop_tsHist_tsOf
      have hpL : (fun i => histVL (tsHist (refVer xL xR r Gr Wr VLr VRr ζr ω)) i -
          histPath (tsHist (refVer xL xR r Gr Wr VLr VRr ζr ω)) (tsHist (refVer xL xR r Gr Wr VLr VRr ζr ω)).1.toNNReal) =
          fun _ : Fin 1 => if ∃ i, xL i = 0 then VLr 0 S₀ ω - Wr S₀ ω else 0 := by
        funext i
        rw [hY, histVL_tsHist_tsOf hX, hstop, histPath_tsHist_tsOf hX, min_self]
        simp only [refState]
        split_ifs <;> first | rfl | exact sub_self _
      have hpR : (fun i => histVR (tsHist (refVer xL xR r Gr Wr VLr VRr ζr ω)) i -
          histPath (tsHist (refVer xL xR r Gr Wr VLr VRr ζr ω)) (tsHist (refVer xL xR r Gr Wr VLr VRr ζr ω)).1.toNNReal) =
          fun _ : Fin 1 => if ∃ j, xR j = 0 then VRr 0 S₀ ω - Wr S₀ ω else 0 := by
        funext i
        rw [hY, histVR_tsHist_tsOf hX, hstop, histPath_tsHist_tsOf hX, min_self]
        simp only [refState]
        split_ifs <;> first | rfl | exact sub_self _
      rw [hpL, hpR] at hspec
      have h' := isBoundedHarmonicExtension_of_normalized hrL hrR hspec
      have eL : (fun i : Fin 1 => VLr i S₀ ω - Wr S₀ ω) = fun _ => VLr 0 S₀ ω - Wr S₀ ω := by
        funext i; rw [Subsingleton.elim i 0]
      have eR : (fun i : Fin 1 => VRr i S₀ ω - Wr S₀ ω) = fun _ => VRr 0 S₀ ω - Wr S₀ ω := by
        funext i; rw [Subsingleton.elim i 0]
      simp only [hudef, hω, ↓reduceIte]
      rw [eL, eR]
      exact h'
    · simp only [hudef, hω, ↓reduceIte]
      exact Classical.choose_spec (exists_isBoundedHarmonicExtension_forceBoundaryData κ ρ'L ρ'R _ _)
  have hGP : ∀ᵐ ω ∂Pr, ω ∈ Gr := ae_iff.2 (by exact hG0)
  have hŜζ : ∀ᵐ ω ∂Pr, ((capStop r Gr ζr Wr ω : WithTop ℝ≥0) : ℝ≥0∞) < ζr ω := by
    filter_upwards [hGP] with ω hω
    obtain ⟨hS, hSζ'⟩ := capStop_ref hL hR hr hG hω
    rw [hS]
    exact hSζ'
  have hcl := (hker _ hŜ hŜζ).2 u hu φ
  filter_upwards [hcl, hGP] with ω h1 hω hdis
  set S₀ : ℝ≥0 := (capStop r Gr ζr Wr ω).untopD 0 with hS₀
  obtain ⟨hS, hSζ'⟩ := capStop_ref hL hR hr hG hω
  have hX := continuousOn_refState xL xR (hG ω hω) hSζ'
  have hY := refVer_eq_tsOf xL xR hL hR hr hG hω
  have hsub := fwdHull_subset_tsHull_tsOf hX hSζ' (hG ω hω).1.2.2.2.1 (w := fun t => Wr t ω) (fun _ _ => rfl)
  rw [hY] at hdis
  rw [h1 (hdis.mono_right hsub), hY, kerFun_eq κ _ _ (isContHist_tsHist_tsOf hX) hdis,
    histCharFun_tsOf_eq κ _ _ hX (w := fun t => Wr t ω) (fun _ _ => rfl) φ]
  have huω : u ω = histHarm κ ρ'L ρ'R (tsHist (tsOf S₀ (refState xL xR Wr VLr VRr ω))) := by
    simp only [hudef, hω, ↓reduceIte, hY]
    rfl
  rw [huω]

end Reference

end LocalExt

end InteractingSLE
