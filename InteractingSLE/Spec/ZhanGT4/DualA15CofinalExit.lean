/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualA15CofinalHull
import InteractingSLE.Spec.ZhanGT4.DualJointInst
import InteractingSLE.Spec.Ito.FiltrationBasic
import InteractingSLE.Spec.Supplement.GW4IdentHull

/-!
# Zhan's A.1.5: the first exit time of a hull from an enclosure

Packet PROVE-ZHAN-GT4-A15F. Source: Astra, *Follow-up proofs*, §A.1.3 (`source/external/AstraIG1/
ig1_followup_proofs.txt` L300–L305, R38): "Let `S_j` be the first exit of `K_j` from `H_j`."

`hullExit W E N = inf ({t | K_t ⊄ E} ∪ [N, ∞))` is the first exit of the hull of `W` from `E`, capped at `N`. For a
compact `ℍ`-hull `E` (`IsHPHull`):

* `fwdHull_hullExit_subset` (`fwdHull_hullExit_subset_add` for a driver started at `x`): the hull **at** the exit time
  is still in `E` (the deterministic step of `DualA15CofinalHull`);
* `le_hullExit`: a time `s ≤ N` all of whose earlier hulls lie in `E` is at most the exit time;
* `hullExit_pos`, `hullExit_pos_add`: the exit time is positive when `E` contains a relative neighbourhood of the
  source;
* **`isStoppingTime_hullExit`**, `isStoppingTime_hullExit_add`: the exit time of `√κ B` (resp. `√κ B + x`) is a
  stopping time of every **right-continuous** filtration to which `B` is adapted — `{S < u}` is the countable union
  over rational `q < u` of the events `{K_q ⊄ E}`, each a countable union of compact hits (A13's
  `measurableSet_hit_drive`). An exit time from an open-type condition is in general only an `𝓕_{t+}` stopping time;
  the usual augmentation (`usualAugmentation`, right-continuous by construction) carries the Brownian motion
  (`isFilteredBrownianReal_usualAugmentation`, R34), so it is the filtration used for the enclosure family.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4

open QuantumZipper (H fwdHull drive)

/-- **The first exit time of the hull of `W` from `E`, capped at `N`.** -/
def hullExit (W : ℝ → ℝ) (E : Set ℂ) (N : ℝ≥0) : ℝ≥0 :=
  sInf ({t : ℝ≥0 | ¬ fwdHull W t ⊆ E} ∪ Ici N)

section Det

variable {W : ℝ → ℝ} {E : Set ℂ} {N : ℝ≥0}

theorem hullExit_le : hullExit W E N ≤ N := csInf_le (OrderBot.bddBelow _) (Or.inr (Set.mem_Ici.2 le_rfl))

theorem fwdHull_subset_of_lt_hullExit {t : ℝ≥0} (ht : t < hullExit W E N) : fwdHull W t ⊆ E := by
  by_contra h
  exact notMem_of_lt_csInf ht (OrderBot.bddBelow _) (Or.inl h)

theorem le_hullExit {s : ℝ≥0} (hsN : s ≤ N) (hs : ∀ t : ℝ≥0, t < s → fwdHull W t ⊆ E) : s ≤ hullExit W E N :=
  le_csInf ⟨N, Or.inr (Set.mem_Ici.2 le_rfl)⟩ fun b hb => by
    rcases hb with hb | hb
    · by_contra hlt
      exact hb (hs b (not_le.1 hlt))
    · exact hsN.trans hb

theorem fwdHull_subset_of_lt_hullExit_real {t : ℝ} (ht0 : 0 ≤ t) (ht : t < hullExit W E N) : fwdHull W t ⊆ E := by
  have h := fwdHull_subset_of_lt_hullExit (W := W) (E := E) (N := N) (t := t.toNNReal)
    (by rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ ht0]; exact ht)
  rwa [Real.coe_toNNReal _ ht0] at h

/-- **The hull at the exit time is still in the enclosure.** -/
theorem fwdHull_hullExit_subset (hW : Continuous W) (hW0 : W 0 = 0) (hE : IsHPHull E) :
    fwdHull W (hullExit W E N) ⊆ E :=
  fwdHull_subset_of_forall_lt hW hW0 (hullExit W E N).coe_nonneg (IsHPHull.isOpen_H_diff hE)
    (IsHPHull.isPreconnected_H_diff hE) (IsHPHull.not_isBounded_H_diff hE) fun _ ht0 hts =>
      fwdHull_subset_of_lt_hullExit_real ht0 hts

/-- The hull of a driver started at `x` at its exit time is still in the enclosure. -/
theorem fwdHull_hullExit_subset_add (hW : Continuous W) (hW0 : W 0 = 0) (x : ℝ) (hE : IsHPHull E) :
    fwdHull (fun u => W u + x) (hullExit (fun u => W u + x) E N) ⊆ E :=
  fwdHull_subset_of_forall_lt_add hW hW0 x (hullExit _ E N).coe_nonneg (IsHPHull.isOpen_H_diff hE)
    (IsHPHull.isPreconnected_H_diff hE) (IsHPHull.not_isBounded_H_diff hE) fun _ ht0 hts =>
      fwdHull_subset_of_lt_hullExit_real ht0 hts

/-- **The exit time is positive** when `E` contains a relative neighbourhood of the source `0`. -/
theorem hullExit_pos (hW : Continuous W) (hW0 : W 0 = 0) (hN : 0 < N) {ε : ℝ} (hε : 0 < ε)
    (hE : ball (0 : ℂ) ε ∩ H ⊆ E) : 0 < hullExit W E N := by
  obtain ⟨δ, hδ, hδK⟩ := Theorem14.GW4Ident.eventually_fwdHull_subset_closedBall hW hW0 (half_pos hε)
  have hpos : 0 < min δ.toNNReal N := lt_min (Real.toNNReal_pos.2 hδ) hN
  refine hpos.trans_le (le_hullExit (min_le_right _ _) fun t ht => ?_)
  rcases (zero_le (a := t)).eq_or_lt with rfl | ht0
  · rw [NNReal.coe_zero, QuantumZipper.RS.fwdHull_zero_eq_empty hW]
    exact empty_subset E
  · have htδ : (t : ℝ) ≤ δ := by
      have := (ht.trans_le (min_le_left _ _)).le
      rwa [← NNReal.coe_le_coe, Real.coe_toNNReal _ hδ.le] at this
    intro z hz
    refine hE ⟨?_, (QuantumZipper.fwdHull_mono.2 _) hz⟩
    have := hδK t (NNReal.coe_pos.2 ht0) htδ hz
    rw [mem_closedBall] at this
    exact mem_ball.2 (this.trans_lt (half_lt_self hε))

/-- The exit time of `W + x` from `E` is that of `W` from `E - x`. -/
theorem hullExit_add_eq (x : ℝ) :
    hullExit (fun u => W u + x) E N = hullExit W ((fun z : ℂ => z + x) ⁻¹' E) N := by
  unfold hullExit
  congr 2
  ext t
  simp only [mem_ofPred_eq, ConformalImageFull.fwdHull_add_const, image_subset_iff]

/-- `ℍ \ (E - x)` is open when `ℍ \ E` is. -/
theorem isOpen_H_diff_preimage_add (hEo : IsOpen (H \ E)) (x : ℝ) :
    IsOpen (H \ ((fun z : ℂ => z + x) ⁻¹' E)) := by
  have hpre : H \ ((fun z : ℂ => z + x) ⁻¹' E) = (fun z : ℂ => z + x) ⁻¹' (H \ E) := by
    ext z
    simp only [Set.mem_sdiff, Set.mem_preimage, QuantumZipper.H, Set.mem_ofPred_eq, Complex.add_im,
      Complex.ofReal_im, add_zero]
  rw [hpre]
  exact hEo.preimage (continuous_id.add continuous_const)

/-- The exit time of a driver started at `x` is positive when `E` contains a relative neighbourhood of `x`. -/
theorem hullExit_pos_add (hW : Continuous W) (hW0 : W 0 = 0) (x : ℝ) (hN : 0 < N) {ε : ℝ} (hε : 0 < ε)
    (hE : ball (x : ℂ) ε ∩ H ⊆ E) : 0 < hullExit (fun u => W u + x) E N := by
  have hE' : ball (0 : ℂ) ε ∩ H ⊆ (fun z : ℂ => z + x) ⁻¹' E := by
    rintro z ⟨hzb, hzH⟩
    refine hE ⟨?_, ?_⟩
    · rw [mem_ball, dist_eq_norm] at hzb ⊢
      simpa using hzb
    · show 0 < (z + (x : ℂ)).im
      simp only [Complex.add_im, Complex.ofReal_im, add_zero]
      exact hzH
  rw [hullExit_add_eq]
  exact hullExit_pos (E := (fun z : ℂ => z + x) ⁻¹' E) hW hW0 hN hε hE'

end Det

/-! ### The exit time is a stopping time of a right-continuous filtration -/

section Stop

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {κ : ℝ} {B : ℝ≥0 → Ω → ℝ}

/-- `{K_s ⊄ E}` is measurable for every σ-algebra in which `B r`, `r ≤ s`, is measurable (`ℍ \ E` open). -/
theorem measurableSet_not_fwdHull_subset (hBc : ∀ ω, Continuous fun r => B r ω) {s : ℝ} (hs : 0 ≤ s)
    (hBm : ∀ r : ℝ≥0, (r : ℝ) ≤ s → Measurable (B r)) {E : Set ℂ} (hEo : IsOpen (H \ E)) :
    MeasurableSet {ω | ¬ fwdHull (drive κ B ω) s ⊆ E} := by
  obtain ⟨F, hFc, hFU, hFeq, hFmono⟩ := hEo.exists_iUnion_isClosed
  have e : {ω | ¬ fwdHull (drive κ B ω) s ⊆ E} =
      ⋃ n : ℕ, {ω | ((F n ∩ closedBall 0 n) ∩ fwdHull (drive κ B ω) s).Nonempty} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, not_subset]
    constructor
    · rintro ⟨z, hzK, hzE⟩
      have hz : z ∈ ⋃ n, F n := by rw [hFeq]; exact ⟨(QuantumZipper.fwdHull_mono.2 s) hzK, hzE⟩
      obtain ⟨n, hn⟩ := mem_iUnion.1 hz
      obtain ⟨m, hm⟩ := exists_nat_ge ‖z‖
      refine ⟨max n m, z, ⟨?_, mem_closedBall_zero_iff.2 (hm.trans (Nat.cast_le.2 (le_max_right n m)))⟩, hzK⟩
      exact (hFmono (le_max_left n m)) hn
    · rintro ⟨n, z, ⟨hzF, -⟩, hzK⟩
      exact ⟨z, hzK, (hFU n hzF).2⟩
  rw [e]
  exact MeasurableSet.iUnion fun n => measurableSet_hit_drive hBc hs hBm
    ((isCompact_closedBall (0 : ℂ) (n : ℝ)).inter_left (hFc n)) fun z hz => (hFU n hz.1).1

/-- **The exit time of `√κ B` from `E` is a stopping time of every right-continuous filtration** to which `B` is
adapted (`ℍ \ E` open). -/
theorem isStoppingTime_hullExit {𝓕 : Filtration ℝ≥0 mΩ} [𝓕.IsRightContinuous]
    (hBc : ∀ ω, Continuous fun r => B r ω) (hBa : ∀ r, Measurable[𝓕 r] (B r)) {E : Set ℂ}
    (hEo : IsOpen (H \ E)) (N : ℝ≥0) :
    IsStoppingTime 𝓕 fun ω => ((hullExit (drive κ B ω) E N : ℝ≥0) : WithTop ℝ≥0) := by
  refine isStoppingTime_of_measurableSet_lt_of_isRightContinuous fun u => ?_
  have hup : ∀ ω (b b' : ℝ≥0), b ≤ b' → b ∈ {t : ℝ≥0 | ¬ fwdHull (drive κ B ω) t ⊆ E} ∪ Ici N →
      b' ∈ {t : ℝ≥0 | ¬ fwdHull (drive κ B ω) t ⊆ E} ∪ Ici N := by
    rintro ω b b' hbb' (hb | hb)
    · exact Or.inl fun h => hb ((QuantumZipper.fwdHull_mono.1 (NNReal.coe_le_coe.2 hbb')).trans h)
    · exact Or.inr (le_trans hb hbb')
  have e : {ω | ((hullExit (drive κ B ω) E N : ℝ≥0) : WithTop ℝ≥0) < u} =
      ⋃ q : ℚ, ⋃ (_ : 0 ≤ (q : ℝ) ∧ (q : ℝ) < u),
        ({ω | ¬ fwdHull (drive κ B ω) ((q : ℝ).toNNReal : ℝ) ⊆ E} ∪ {_ω | N ≤ (q : ℝ).toNNReal}) := by
    ext ω
    simp only [mem_ofPred_eq, WithTop.coe_lt_coe, mem_iUnion, mem_union, exists_prop]
    unfold hullExit
    rw [csInf_lt_iff (OrderBot.bddBelow _) ⟨N, Or.inr (Set.mem_Ici.2 le_rfl)⟩]
    constructor
    · rintro ⟨b, hb, hbu⟩
      obtain ⟨q, hbq, hqu⟩ := exists_rat_btwn (show (b : ℝ) < u from hbu)
      have hq0 : 0 ≤ (q : ℝ) := b.coe_nonneg.trans hbq.le
      refine ⟨q, ⟨hq0, hqu⟩, hup ω b _ ?_ hb⟩
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hq0]
      exact hbq.le
    · rintro ⟨q, ⟨hq0, hqu⟩, hq⟩
      refine ⟨(q : ℝ).toNNReal, hq, ?_⟩
      rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hq0]
      exact hqu
  rw [e]
  refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun hq => MeasurableSet.union ?_ (MeasurableSet.const _)
  exact measurableSet_not_fwdHull_subset (mΩ := 𝓕 u) hBc (Real.toNNReal (q : ℝ)).coe_nonneg
    (fun r hr => (hBa r).mono (𝓕.mono (show r ≤ u by
      rw [← NNReal.coe_le_coe]; rw [Real.coe_toNNReal _ hq.1] at hr; exact hr.trans hq.2.le)) le_rfl) hEo

/-- The exit time of `√κ B + x` is a stopping time of every right-continuous filtration to which `B` is adapted. -/
theorem isStoppingTime_hullExit_add {𝓕 : Filtration ℝ≥0 mΩ} [𝓕.IsRightContinuous]
    (hBc : ∀ ω, Continuous fun r => B r ω) (hBa : ∀ r, Measurable[𝓕 r] (B r)) {E : Set ℂ}
    (hEo : IsOpen (H \ E)) (x : ℝ) (N : ℝ≥0) :
    IsStoppingTime 𝓕 fun ω => ((hullExit (fun u => drive κ B ω u + x) E N : ℝ≥0) : WithTop ℝ≥0) := by
  simp only [hullExit_add_eq]
  exact isStoppingTime_hullExit hBc hBa (isOpen_H_diff_preimage_add hEo x) N

/-- The usual augmentation is right-continuous. -/
instance isRightContinuous_usualAugmentation (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω) :
    (usualAugmentation 𝓕 P).IsRightContinuous := by
  unfold usualAugmentation
  infer_instance

end Stop

end InteractingSLE.ZhanGT4
