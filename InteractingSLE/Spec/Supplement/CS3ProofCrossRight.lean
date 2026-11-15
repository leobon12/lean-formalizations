/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.CS3ProofCross
import InteractingSLE.Spec.Sec4.RepulsionNoncollision

/-!
# The exact-extreme crossing of a rightward stage (reflection of `CS3ProofCross`)

Packet PROVE-T14-TIP7, ruling R53 (follow-up note A.3; "Reflection gives the rightward stage", shortcut note §1.2).
For a reflected GB8 word — right total `κ − 4`, left total `κ/2 − 2`, the outermost right label at `x₊ ≥ 3`, the
designated far right labels (`j ≥ m_R`) all starting at least `3`, and the far left label the junction alone
(`m_L = n_L − 1`) — the rightward reach event

  `{∃ t < n, W_t > 17/8, and on [0, t]: every coordinate in (−n, n), every far gap > 1/(n+1)}`

has probability tending to one. Proof: apply `CS3Cross` to the reflected evolution `(−W, −V^R, −V^L, −B)`
(`IsIntegratedSLEEvolution.reflect`, `LP.isGeneratingTrace_reflect`) and reflect the event back.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Finset Set
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Theorem14

namespace CS3Cross

open Supp12 Supp12.DS2 Supp12.DSReach Supp8.GB8

variable {nL nR : ℕ}

/-- The rightward target `{W > 17/8}`. -/
def rightTarget : Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)) := {p | 2 + 1 / 8 < p.1}

theorem isOpen_rightTarget : IsOpen (rightTarget : Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ))) :=
  isOpen_lt continuous_const continuous_fst

/-- The `n`-th inner buffer of the rightward stage: coordinates in `(−n, n)`, far gaps `> 1/(n+1)` for the right
labels of index `≥ m_R` and the last left label. -/
def rightBuf (nL : ℕ) (mR : ℕ) (n : ℕ) : Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)) :=
  {p | InBuffer (nL - 1) mR n (1 / ((n : ℝ) + 1)) p}

theorem rightBuf_mono (nL mR : ℕ) : Monotone (rightBuf (nR := nR) nL mR) := by
  intro n n' hnn' p hp
  refine inBuffer_mono (by exact_mod_cast hnn') ?_ hp
  have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  exact one_div_le_one_div_of_le h1 (by exact_mod_cast Nat.add_le_add_right hnn' 1)

theorem reachEvent_right_mono {Ω : Type*} (mR : ℕ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
    (VR : Fin nR → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) :
    Monotone fun n : ℕ => reachEvent (n : ℝ≥0) rightTarget (rightBuf nL mR n) W VL VR ζ := fun n n' h =>
  reachEvent_mono (by exact_mod_cast h) subset_rfl (rightBuf_mono nL mR h) W VL VR ζ

/-- The reflection of an ordered word is ordered. -/
theorem isOrderedForceWord_reflect {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} (hF : IsOrderedForceWord xL xR) :
    IsOrderedForceWord (-xR) (-xL) :=
  ⟨fun _ _ h => neg_le_neg (hF.2.2.1 h), fun i => neg_nonpos.2 (hF.2.2.2 i),
    fun _ _ h => neg_le_neg (hF.1 h), fun i => neg_nonneg.2 (hF.2.1 i)⟩

/-- The reflected leftward buffer is the rightward buffer. -/
theorem mem_leftBuf_reflect_iff {mR n : ℕ} {p : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)} :
    ((-p.1, fun j => -p.2.2 j, fun i => -p.2.1 i) : ℝ × (Fin nR → ℝ) × (Fin nL → ℝ)) ∈ leftBuf mR nL n ↔
      p ∈ rightBuf nL mR n := by
  simp only [leftBuf, rightBuf, mem_ofPred_eq, InBuffer, InBox, InFarBuffer, abs_neg]
  constructor
  · rintro ⟨⟨h1, h2, h3⟩, h4, h5⟩
    refine ⟨⟨h1, h3, h2⟩, fun j hj => ?_, fun i hi => ?_⟩
    · have := h5 j hj; linarith
    · have := h4 i hi; linarith
  · rintro ⟨⟨h1, h2, h3⟩, h4, h5⟩
    refine ⟨⟨h1, h3, h2⟩, fun i hi => ?_, fun j hj => ?_⟩
    · have := h5 i hi; linarith
    · have := h4 j hj; linarith

variable {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {Ω : Type u}
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **The exact-extreme crossing of a rightward stage, pathwise almost surely.** -/
theorem ae_exists_reachEvent_right (hGB8 : GB8Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4) (hnL : 0 < nL)
    (hnR : 0 < nR) (hF : IsOrderedForceWord xL xR) (hxm : xL ⟨nL - 1, Nat.sub_lt hnL one_pos⟩ < 0)
    (hxp : 3 ≤ xR ⟨nR - 1, Nat.sub_lt hnR one_pos⟩) (hsR : ∑ j, ρR j = κ - 4) (hsL : ∑ i, ρL i = κ / 2 - 2)
    (hpR : ∀ j : Fin nR, (j : ℕ) < nR - 1 → -2 < ∑ l ∈ univ.filter (fun l => l ≤ j), ρR l)
    (hpL : ∀ i : Fin nL, (i : ℕ) < nL - 1 → -2 < ∑ l ∈ univ.filter (fun l => l ≤ i), ρL l)
    {mR : ℕ} (hfar : ∀ j : Fin nR, mR ≤ (j : ℕ) → 3 ≤ xR j)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (htr : ∀ᵐ ω ∂P, ∃ γ : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) γ) :
    ∀ᵐ ω ∂P, ∃ n : ℕ, ω ∈ reachEvent (n : ℝ≥0) rightTarget (rightBuf nL mR n) W VL VR ζ := by
  have hEr := IsIntegratedSLEEvolution.reflect hE
  have htr' : ∀ᵐ ω ∂P, ∃ γ : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => (-W) t ω) (ζ ω) γ := by
    filter_upwards [htr] with ω ⟨γ, hγ⟩
    exact ⟨fun t => LP.reflectC (γ t), LP.isGeneratingTrace_reflect hγ⟩
  have hxm' : (-xR) ⟨nR - 1, Nat.sub_lt hnR one_pos⟩ ≤ -3 := by
    simp only [Pi.neg_apply]; linarith
  have hxp' : 0 < (-xL) ⟨nL - 1, Nat.sub_lt hnL one_pos⟩ := by
    simp only [Pi.neg_apply]; linarith
  have hfar' : ∀ j : Fin nR, mR ≤ (j : ℕ) → (-xR) j ≤ -3 := fun j hj => by
    simp only [Pi.neg_apply]; linarith [hfar j hj]
  have h := ae_exists_reachEvent_left (P := P) hGB8 hκ hκ4 hnR hnL (isOrderedForceWord_reflect hF) hxp' hxm' hsR
    hsL hpR hpL hfar' hEr htr'
  filter_upwards [h] with ω ⟨n, t, htn, htζ, hO, hB⟩
  refine ⟨n, t, htn, htζ, ?_, fun u hu => ?_⟩
  · have : -W t ω < -(2 + 1 / 8) := hO
    show 2 + 1 / 8 < W t ω
    linarith
  · exact mem_leftBuf_reflect_iff.1 (hB u hu)

/-- **A rightward buffer with crossing probability `> 1 − δ`.** -/
theorem exists_lt_measure_reachEvent_right [IsProbabilityMeasure P] (hGB8 : GB8Statement.{u}) (hκ : 0 < κ)
    (hκ4 : κ < 4) (hnL : 0 < nL) (hnR : 0 < nR) (hF : IsOrderedForceWord xL xR)
    (hxm : xL ⟨nL - 1, Nat.sub_lt hnL one_pos⟩ < 0) (hxp : 3 ≤ xR ⟨nR - 1, Nat.sub_lt hnR one_pos⟩)
    (hsR : ∑ j, ρR j = κ - 4) (hsL : ∑ i, ρL i = κ / 2 - 2)
    (hpR : ∀ j : Fin nR, (j : ℕ) < nR - 1 → -2 < ∑ l ∈ univ.filter (fun l => l ≤ j), ρR l)
    (hpL : ∀ i : Fin nL, (i : ℕ) < nL - 1 → -2 < ∑ l ∈ univ.filter (fun l => l ≤ i), ρL l)
    {mR : ℕ} (hfar : ∀ j : Fin nR, mR ≤ (j : ℕ) → 3 ≤ xR j)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (htr : ∀ᵐ ω ∂P, ∃ γ : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) γ) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ n : ℕ, 1 - δ < P (reachEvent (n : ℝ≥0) rightTarget (rightBuf nL mR n) W VL VR ζ) := by
  have hlim := tendsto_measure_iUnion_atTop (μ := P) (reachEvent_right_mono (nL := nL) (nR := nR) mR W VL VR ζ)
  have hae := ae_exists_reachEvent_right hGB8 hκ hκ4 hnL hnR hF hxm hxp hsR hsL hpR hpL hfar hE htr
  have hone : P (⋃ n : ℕ, reachEvent (n : ℝ≥0) rightTarget (rightBuf nL mR n) W VL VR ζ) = 1 := by
    refine le_antisymm prob_le_one ?_
    have hnull : P (⋃ n : ℕ, reachEvent (n : ℝ≥0) rightTarget (rightBuf nL mR n) W VL VR ζ)ᶜ = 0 := by
      rw [ae_iff] at hae
      refine measure_mono_null (fun ω hω => ?_) hae
      simp only [mem_compl_iff, mem_iUnion, not_exists] at hω
      simp only [mem_ofPred_eq, not_exists]
      exact hω
    calc (1 : ℝ≥0∞) = P univ := measure_univ.symm
      _ ≤ P (⋃ n : ℕ, reachEvent (n : ℝ≥0) rightTarget (rightBuf nL mR n) W VL VR ζ) +
          P (⋃ n : ℕ, reachEvent (n : ℝ≥0) rightTarget (rightBuf nL mR n) W VL VR ζ)ᶜ := by
            rw [← union_compl_self (⋃ n : ℕ, reachEvent (n : ℝ≥0) rightTarget (rightBuf nL mR n) W VL VR ζ)]
            exact measure_union_le _ _
      _ = _ := by rw [hnull, add_zero]
  rw [hone] at hlim
  have h1 : (1 : ℝ≥0∞) - δ < 1 := ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hδ.ne'
  exact (hlim.eventually (lt_mem_nhds h1)).exists

end CS3Cross

end Theorem14

end InteractingSLE
