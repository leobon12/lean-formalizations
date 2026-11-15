/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntRunChronClock

/-!
# Every finite own-time prefix appends a chronological arc

A prefix may end in H. Its endpoint is a physical complex point, not the
machine's real exit record. Use GW1's rescaled physical arc directly;
zero own time contributes only the already retained seed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.WalkIntRunChron

open GW1WalkChain GW1Bookkeep GW1X

/-- A finite prefix, including a full finite stop, has an actual
chronological carrier. No capped-run history is assumed. -/
theorem arcHistory_append_finite_tipSet {root : ℂ} {A : Set ℂ} {q₀ q₁ : ℝ}
    (hHist : ArcHistory root A (q₀ : ℂ)) {c : Chart} {W : ℝ≥0 → ℝ} {S : ℝ≥0∞}
    (hP : PieceSimpleAt c W S A q₀ q₁) {τ : ℝ≥0} (hτ : (τ : ℝ≥0∞) ≤ S) :
    ∃ q : ℂ, ArcHistory root
      (A ∪ c.tipSet (fun r => W (min (r : ℝ≥0∞) (τ : ℝ≥0∞)).toNNReal) τ) q := by
  obtain ⟨f, η, _, hf, _, hmaps, hW0, hW, hη, _, hi, hStart, _, hmeet⟩ := hP
  have hηH (t : ℝ≥0) (ht : (t : ℝ≥0∞) ≤ S) : η t ∈ Hbar :=
    Sec7.IsGeneratingTrace.mem_Hbar hη
      (hW.mono fun _ ht => mem_ofPred.2 ht.le) hW0 ht
  have hgen : IsGeneratingTrace W (τ : ℝ≥0∞) η := hη.mono_horizon hτ
  have hWτ : ContinuousOn W {t : ℝ≥0 | (t : ℝ≥0∞) ≤ (τ : ℝ≥0∞)} :=
    hW.mono (fun _ ht => ht.trans hτ)
  have hsmall : c.tipSet (fun r => W (min (r : ℝ≥0∞) (τ : ℝ≥0∞)).toNNReal) τ =
      (fun t => f (η t)) '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ (τ : ℝ≥0∞)} := by
    rw [CounterflowRange.tipSet_stopped_eq_of_tendsto hgen hWτ hW0
      (fun t ht => hf _ (hηH t (ht.trans hτ))), image_image]
  rcases eq_zero_or_pos τ with hzero | hpos
  · subst τ
    have htimes : {t : ℝ≥0 | (t : ℝ≥0∞) ≤ (0 : ℝ≥0∞)} = {0} := by
      ext t
      simp only [mem_ofPred_eq, le_zero_iff, ENNReal.coe_eq_zero, mem_singleton_iff]
    rw [hsmall, ENNReal.coe_zero, htimes, image_singleton, hStart,
      union_eq_left.2 (singleton_subset_iff.2 hHist.endpoint_mem)]
    exact ⟨q₀, hHist⟩
  · have hiτ : InjOn (f ∘ η) (Iic τ) := fun s hs t ht he =>
      hi ((ENNReal.coe_le_coe.2 hs).trans hτ) ((ENNReal.coe_le_coe.2 ht).trans hτ) he
    obtain ⟨hArc, hImage, h0, h1⟩ := exists_isArc_tipSet hf hpos hgen hWτ hW0 hiτ
    have hfull : c.tipSet (fun r => W (min (r : ℝ≥0∞) S).toNNReal) S =
        (fun t => f (η t)) '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ S} := by
      rw [CounterflowRange.tipSet_stopped_eq_of_tendsto hη hW hW0
        (fun t ht => hf _ (hηH t ht)), image_image]
    have hh := hHist.append (rescale (f ∘ η) τ) hArc (fun s hs => by
      change f (η (min s 1 * τ)) ∈ Hbar
      exact hmaps _ (hηH _ ((ENNReal.coe_le_coe.2
        (mul_le_of_le_one_left (zero_le (a := τ)) (min_le_right s 1))).trans hτ)))
      (h0.trans hStart) (fun s hs hmem => by
        apply hArc.2 hs (mem_Iic.2 zero_le)
        have hsFull : rescale (f ∘ η) τ s ∈
            c.tipSet (fun r => W (min (r : ℝ≥0∞) S).toNNReal) S := by
          have hsSmall := (Set.ext_iff.1 hImage _).1 ⟨s, hs, rfl⟩
          rw [hsmall] at hsSmall
          rw [hfull]
          exact (image_mono (fun _ ht => ht.trans hτ)) hsSmall
        have hs0 : rescale (f ∘ η) τ s = f (η 0) :=
          mem_singleton_iff.1 ((Set.ext_iff.1 hmeet _).1 ⟨hsFull, hmem⟩)
        exact hs0.trans h0.symm)
    rw [hImage, h1] at hh
    exact ⟨f (η τ), hh⟩

end InteractingSLE.Theorem14.WalkIntRunChron
