/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Zhan.SeparatedOneSided
import InteractingSLE.Spec.Sec4.RepulsionDrift

/-!
# Transience for two-group words (`κ ≤ 4`)

Packet PROVE-ZHAN-B3. The base of Astra's reduction "Chordal transience for an arbitrary finite word" (L1585–L1615,
"This reduces to the one- and two-group laws proved above when `κ ≤ 4`"): words whose left marks all sit at one point
`p_L < 0` and whose right marks all sit at one point `p_R > 0` (either side may be empty, not both).

Coincident marks stay coincident (`IsIntegratedSLEPath.vL_eq_of_xL_eq`), so on the infinite-lifetime event
(Aux. lemma 6) an evolution of such a word is an evolution of the word with one mark per nonempty side carrying the
total weight of its group (`IsIntegratedSLEEvolution.mergeLeft`, `mergeRight`; `ThresholdCondition` sees the whole
group at once). Admissibility gives total weights `≥ κ/2 − 2`, and the pair and one-sided results apply.

## Main results

* `IsIntegratedSLEEvolution.mergeLeft`, `IsIntegratedSLEEvolution.mergeRight`: merging a group of coincident marks.
* `IsIntegratedSLEEvolution.ae_tendsto_norm_trace_groups`: **transience for two-group words**.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Zhan

variable {κ : ℝ} {nL nR : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

theorem toNNReal_lt_of_mem_uIcc {T : ℝ≥0∞} {t : ℝ≥0} (ht : (t : ℝ≥0∞) < T) {s : ℝ} (hs : s ∈ uIcc (0 : ℝ) t) :
    (s.toNNReal : ℝ≥0∞) < T := by
  rw [uIcc_of_le t.coe_nonneg] at hs
  exact lt_of_le_of_lt (ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hs.2)) ht

/-- **Merging a group of coincident left marks** (infinite lifetime almost surely): if all left marks start at the
same point, the processes are an evolution of the word with one left mark carrying the total left weight. -/
theorem IsIntegratedSLEEvolution.mergeLeft {n : ℕ} {xL ρL : Fin (n + 1) → ℝ} {xR ρR : Fin nR → ℝ}
    {VL : Fin (n + 1) → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} (hxL : ∀ i, xL i = xL 0)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) :
    IsIntegratedSLEEvolution κ (fun _ : Fin 1 => xL 0) xR (fun _ : Fin 1 => ∑ i, ρL i) ρR P 𝓕 W
      (fun _ => VL 0) VR B ζ := by
  obtain ⟨hB, hW, hVL, hVR, hpath⟩ := hE
  refine ⟨hB, hW, fun _ => hVL 0, hVR, ?_⟩
  filter_upwards [hpath, hζ] with ω hp hζω
  have hco : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → ∀ i, VL i t ω = VL 0 t ω := fun t ht i =>
    hp.vL_eq_of_xL_eq ht (hxL i)
  obtain ⟨h1, h2, h3, h4, h5, h6, -, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, -, -⟩ := hp
  refine ⟨h1, fun _ => h2 0, h3, h4, fun _ => h5 0, h6, fun _ _ _ _ _ => le_rfl, fun t ht _ => h8 t ht 0, h9,
    h10, fun t ht _ => h11 t ht 0, h12, fun t ht => ?_, fun t ht _ => h14 t ht 0, h15, fun _ => h16 0, h17,
    fun t ht h => ?_, fun h => ?_, fun T _ hT => ?_⟩
  · have e := h13 t ht
    have hcg : ∀ i, ∫ s in (0 : ℝ)..t, ρL i / (W s.toNNReal ω - VL i s.toNNReal ω) =
        ∫ s in (0 : ℝ)..t, ρL i / (W s.toNNReal ω - VL 0 s.toNNReal ω) := fun i =>
      intervalIntegral.integral_congr fun s hs => by
        rw [hco _ (toNNReal_lt_of_mem_uIcc ht hs) i]
    have hint : ∀ i ∈ Finset.univ, IntervalIntegrable
        (fun s : ℝ => ρL i / (W s.toNNReal ω - VL 0 s.toNNReal ω)) volume 0 t := fun i _ =>
      ((h11 t ht 0).const_mul (ρL i)).congr fun s _ => (div_eq_mul_inv _ _).symm
    rw [Finset.sum_congr rfl fun i _ => hcg i, ← intervalIntegral.integral_finsetSum hint] at e
    simp only [← Finset.sum_div] at e
    rw [Fin.sum_univ_one]
    exact e
  · refine h18 t ht (h.imp (fun hl => ?_) id)
    by_cases hc : VL 0 t ω = W t ω
    · have hall : (Finset.univ.filter fun i => VL i t ω = W t ω) = Finset.univ :=
        Finset.filter_true_of_mem fun i _ => (hco t ht i).trans hc
      have hall' : (Finset.univ.filter fun _ : Fin 1 => VL 0 t ω = W t ω) = Finset.univ :=
        Finset.filter_true_of_mem fun _ _ => hc
      rw [hall', Fin.sum_univ_one] at hl
      rw [hall]
      exact hl
    · have hnone : (Finset.univ.filter fun _ : Fin 1 => VL 0 t ω = W t ω) = ∅ :=
        Finset.filter_false_of_mem fun _ _ => hc
      rw [hnone, Finset.sum_empty] at hl
      norm_num at hl
  · rw [hζω] at h; exact absurd h ENNReal.top_ne_zero
  · rw [hζω] at hT; exact absurd hT ENNReal.coe_ne_top

/-- **Merging a group of coincident right marks** (infinite lifetime almost surely). -/
theorem IsIntegratedSLEEvolution.mergeRight {n : ℕ} {xL ρL : Fin nL → ℝ} {xR ρR : Fin (n + 1) → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin (n + 1) → ℝ≥0 → Ω → ℝ} (hxR : ∀ i, xR i = xR 0)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) :
    IsIntegratedSLEEvolution κ xL (fun _ : Fin 1 => xR 0) ρL (fun _ : Fin 1 => ∑ i, ρR i) P 𝓕 W
      VL (fun _ => VR 0) B ζ := by
  obtain ⟨hB, hW, hVL, hVR, hpath⟩ := hE
  refine ⟨hB, hW, hVL, fun _ => hVR 0, ?_⟩
  filter_upwards [hpath, hζ] with ω hp hζω
  have hco : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → ∀ i, VR i t ω = VR 0 t ω := fun t ht i =>
    hp.vR_eq_of_xR_eq ht (hxR i)
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, -, h11, h12, h13, h14, h15, h16, h17, h18, -, -⟩ := hp
  refine ⟨h1, h2, fun _ => h3 0, h4, h5, fun _ => h6 0, h7, h8, fun t ht _ => h9 t ht 0,
    fun _ _ _ _ _ => le_rfl, h11, fun t ht _ => h12 t ht 0, fun t ht => ?_, h14, fun t ht _ => h15 t ht 0, h16,
    fun _ => h17 0, fun t ht h => ?_, fun h => ?_, fun T _ hT => ?_⟩
  · have e := h13 t ht
    have hcg : ∀ i, ∫ s in (0 : ℝ)..t, ρR i / (W s.toNNReal ω - VR i s.toNNReal ω) =
        ∫ s in (0 : ℝ)..t, ρR i / (W s.toNNReal ω - VR 0 s.toNNReal ω) := fun i =>
      intervalIntegral.integral_congr fun s hs => by
        rw [hco _ (toNNReal_lt_of_mem_uIcc ht hs) i]
    have hint : ∀ i ∈ Finset.univ, IntervalIntegrable
        (fun s : ℝ => ρR i / (W s.toNNReal ω - VR 0 s.toNNReal ω)) volume 0 t := fun i _ =>
      ((h12 t ht 0).const_mul (ρR i)).congr fun s _ => (div_eq_mul_inv _ _).symm
    rw [Finset.sum_congr rfl fun i _ => hcg i, ← intervalIntegral.integral_finsetSum hint] at e
    simp only [← Finset.sum_div] at e
    rw [Fin.sum_univ_one (f := fun i => ∫ s in (0 : ℝ)..t, (∑ i, ρR i) / _)]
    exact e
  · refine h18 t ht (h.imp id fun hr => ?_)
    by_cases hc : VR 0 t ω = W t ω
    · have hall : (Finset.univ.filter fun i => VR i t ω = W t ω) = Finset.univ :=
        Finset.filter_true_of_mem fun i _ => (hco t ht i).trans hc
      have hall' : (Finset.univ.filter fun _ : Fin 1 => VR 0 t ω = W t ω) = Finset.univ :=
        Finset.filter_true_of_mem fun _ _ => hc
      rw [hall', Fin.sum_univ_one] at hr
      rw [hall]
      exact hr
    · have hnone : (Finset.univ.filter fun _ : Fin 1 => VR 0 t ω = W t ω) = ∅ :=
        Finset.filter_false_of_mem fun _ _ => hc
      rw [hnone, Finset.sum_empty] at hr
      norm_num at hr
  · rw [hζω] at h; exact absurd h ENNReal.top_ne_zero
  · rw [hζω] at hT; exact absurd hT ENNReal.coe_ne_top

/-! ### Two-group words -/

theorem le_sum_left_of_group {k : ℝ} {n : ℕ} {xL ρL : Fin (n + 1) → ℝ} {xR ρR : Fin nR → ℝ}
    (hadm : Sec4.HasAdmissiblePartialSums k ρL ρR xL xR) (hxL : xL 0 < 0) (hg : ∀ i, xL i = xL 0) :
    k / 2 - 2 ≤ ∑ i, ρL i := by
  have h := hadm.1 (xL 0 - 1) (by linarith) ⟨0, by linarith⟩
  have e : (Finset.univ.filter fun i => xL 0 - 1 < xL i) = Finset.univ :=
    Finset.filter_true_of_mem fun i _ => by rw [hg i]; linarith
  rwa [e] at h

theorem le_sum_right_of_group {k : ℝ} {n : ℕ} {xL ρL : Fin nL → ℝ} {xR ρR : Fin (n + 1) → ℝ}
    (hadm : Sec4.HasAdmissiblePartialSums k ρL ρR xL xR) (hxR : 0 < xR 0) (hg : ∀ i, xR i = xR 0) :
    k / 2 - 2 ≤ ∑ i, ρR i := by
  have h := hadm.2 (xR 0) hxR.le ⟨0, le_rfl⟩
  have e : (Finset.univ.filter fun i => xR i ≤ xR 0) = Finset.univ :=
    Finset.filter_true_of_mem fun i _ => (hg i).le
  rwa [e] at h

/-- **Transience for two-group words** (`0 < κ ≤ 4`): an ordered word with admissible side partial sums, at least one
mark, whose left marks all sit at one point `< 0` and whose right marks all sit at one point `> 0`. Almost surely
every continuous generating trace on `[0, ∞)` tends to `∞`. -/
theorem IsIntegratedSLEEvolution.ae_tendsto_norm_trace_groups (hκ : 0 < κ) (hκ4 : κ ≤ 4)
    {xL ρL : Fin nL → ℝ} {xR ρR : Fin nR → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    (hF : IsOrderedForceWord xL xR) (hadm : Sec4.HasAdmissiblePartialSums κ ρL ρR xL xR)
    (hxL : ∀ i, xL i < 0) (hxR : ∀ j, 0 < xR j) (hgL : ∀ i j, xL i = xL j) (hgR : ∀ i j, xR i = xR j)
    (hn : 0 < nL + nR) (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η →
      Tendsto (fun t => ‖η t‖) atTop atTop := by
  have hζ : ∀ᵐ ω ∂P, ζ ω = ⊤ :=
    (Sec4.aux6Statement hκ xL xR ρL ρR P 𝓕 W VL VR B ζ hF hadm hE).mono fun ω h => h.1
  cases nL with
  | zero =>
    cases nR with
    | zero => exact absurd hn (lt_irrefl 0)
    | succ n =>
      have hE' := IsIntegratedSLEEvolution.mergeRight (fun i => hgR i 0) hE hζ
      exact IsIntegratedSLEEvolution.ae_tendsto_norm_trace_right hκ hκ4
        (le_sum_right_of_group hadm (hxR 0) fun i => hgR i 0) (hxR 0) hE'
  | succ m =>
    have hE₁ := IsIntegratedSLEEvolution.mergeLeft (fun i => hgL i 0) hE hζ
    have hρL := le_sum_left_of_group hadm (hxL 0) fun i => hgL i 0
    cases nR with
    | zero => exact IsIntegratedSLEEvolution.ae_tendsto_norm_trace_left hκ hκ4 hρL (hxL 0) hE₁
    | succ n =>
      have hE₂ := IsIntegratedSLEEvolution.mergeRight (fun i => hgR i 0) hE₁ hζ
      exact IsIntegratedSLEEvolution.ae_tendsto_norm_trace_pair hκ hκ4 hρL
        (le_sum_right_of_group hadm (hxR 0) fun i => hgR i 0) (hxL 0) (hxR 0) hE₂

end InteractingSLE.Zhan
