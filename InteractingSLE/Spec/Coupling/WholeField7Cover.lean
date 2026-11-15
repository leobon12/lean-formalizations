/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.NonBoundaryCover
import InteractingSLE.Spec.Dimension.Finite

/-!
# (WF1) at `κ = 4` for every force word: covering numbers of a stopped trace by finitely many localizations

Packet PROVE-WHOLEFIELD7 (follow-up note C.5, `source/external/AstraIG1/ig1_followup_proofs.txt` L1705–1760, the
covering input (WF1); ruling R38). For words whose curve hits the boundary, the landed bound for non-boundary-hitting
words (`WangWu.IsMarkedChain.ae_eventually_dyadicCount_trace_le`, one localization) does not apply. Here the visit
times `{t ≤ T : η(t) ∈ K}` of a compact `K ⊆ ℍ` form a compact set; at each of them the force gaps are nonzero (O2,
`IsIntegratedSLEEvolution.ae_forall_ne_of_mem_H`), so a localization (rational start `a`, rational length `m`, gaps
`≥ 1/(j+1)` on `[a, a+m]`) covers a neighbourhood of it; the localized trace is a simple κ = 4 chain (absolutely
continuous with respect to `SLE₄`), so the trace on that neighbourhood is the conformal image of a compact piece of
the localized trace inside `ℍ` and has `N_n ≤ (2ⁿ)^{15/8}` eventually; finitely many neighbourhoods cover the visit
times. This is the finite-localization form of the cover of Aux. lemma 15 (`Spec/Dimension/Finite.lean`).

## Main results

* `mem_image_of_localization`, `eventually_dyadicCount_piece_le`: one localization (deterministic);
* `exists_dyadicCount_trace_le`: the finite cover (deterministic);
* **`ae_tendsto_dyadicCount_trace_four`**: almost surely, for every continuous generating trace through the lifetime,
  every `T < ζ` and compact `K ⊆ ℍ`, `N_n(η[0,T] ∩ K) (n + 1) 4^{-n} → 0` — the covering hypothesis (R1.1)/(WF1) of
  the reconstruction.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal Real

namespace InteractingSLE

namespace WholeField

open QuantumZipper QuantumZipper.RS WangWu.TraceGlue Dimension

/-! ### One localization -/

section Piece

variable {nL nR : ℕ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {ζ : ℝ≥0∞}
  {η : ℝ≥0 → ℂ}

/-- The piece of the trace covered by one localization: the image under `f_a⁻¹` of the localized trace on
`[ε, m]`. -/
def tracePiece (w : ℝ≥0 → ℝ) (a : ℝ≥0) (x : CPath) (ε m : ℝ) : Set ℂ :=
  fwdMapInv (fun s : ℝ => w s.toNNReal) a '' (trace (drive 4 canonBM x) '' Icc ε m)

/-- **A trace point in a localization window is in the piece.** If `w` agrees with `2 X` after `a` on `[a, a + m]`
(`a + m < ζ`) and the driver of `X` is a simple chain, then `η(t) ∈ f_a⁻¹(trace_X[ε, m])` for `t ∈ [a + ε, a + m]`. -/
theorem mem_tracePiece (hη : IsGeneratingTrace w ζ η) (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ})
    (hw0 : w 0 = 0) {x : CPath} (hxc : Continuous (drive 4 canonBM x)) (hx0 : drive 4 canonBM x 0 = 0)
    (hxs : IsSimpleRadialChain (drive 4 canonBM x)) {a m : ℝ≥0} (ham : ((a + m : ℝ≥0) : ℝ≥0∞) < ζ)
    (hloc : ∀ t : ℝ≥0, t ≤ m → w (a + t) - w a = Real.sqrt 4 * x.1 t) {ε : ℝ} (hε : 0 < ε) {t : ℝ≥0}
    (ht1 : (a : ℝ) + ε ≤ t) (ht2 : t ≤ a + m) : η t ∈ tracePiece w a x ε m := by
  obtain ⟨t₂, hamt₂, ht₂ζ⟩ := exists_real_btwn_of_lt ham
  have ht₂ : 0 ≤ t₂ := (NNReal.coe_nonneg _).trans hamt₂.le
  set W' := frozenDrive w t₂ with hW'def
  have hW' : Continuous W' := continuous_frozenDrive_of_lt hw ht₂ζ
  have hW'0 : W' 0 = 0 := by rw [hW'def, frozenDrive_zero ht₂, hw0]
  have ha0 : (0 : ℝ) ≤ a := a.coe_nonneg
  have hat : (a : ℝ) < t := by linarith
  have hamt₂' : (a : ℝ) + m < t₂ := by exact_mod_cast hamt₂
  -- the shifted frozen driver is the localized driver on `[0, m]`
  have hEq : EqOn (shiftDrive W' a) (drive 4 canonBM x) (Icc 0 (m : ℝ)) := by
    intro r hr
    have hr0 : 0 ≤ r := hr.1
    have h1 : (a : ℝ) + r ∈ Icc (0 : ℝ) t₂ := ⟨add_nonneg ha0 hr0, by linarith [hr.2]⟩
    have h2 : (a : ℝ) ∈ Icc (0 : ℝ) t₂ := ⟨ha0, by linarith [hr.2, m.coe_nonneg]⟩
    have hrm : r.toNNReal ≤ m := Real.toNNReal_le_iff_le_coe.2 hr.2
    simp only [shiftDrive, drive, canonBM]
    rw [hW'def, frozenDrive_eq h1, frozenDrive_eq h2, Dimension.toNNReal_coe_add hr0, Real.toNNReal_coe]
    exact hloc _ hrm
  have hS : Continuous (shiftDrive W' a) := continuous_shiftDrive hW' a
  have hS0 : shiftDrive W' a 0 = 0 := shiftDrive_zero _ _
  have hsh : IsSimpleRadialChainOn (shiftDrive W' a) m :=
    (hxs m).congr hxc hx0 hS hS0 (fun r hr => (hEq hr).symm)
  have htam : (t : ℝ) - a ≤ m := by linarith
  obtain ⟨-, htip, -⟩ := tendsto_trace_of_shift hW' hW'0 ha0 hat (hsh.mono htam)
  have hL := hη.isLoewnerTraceLT ht₂ζ
  have htt₂ : (t : ℝ) < t₂ := by linarith
  have hηt : trace W' t = η t := by
    have := hL.trace_eq hW' hW'0 (NNReal.coe_nonneg t) htt₂
    simpa using this
  have hu0 : 0 ≤ (t : ℝ) - a := by linarith
  have htr : trace (shiftDrive W' a) ((t : ℝ) - a) = trace (drive 4 canonBM x) ((t : ℝ) - a) :=
    trace_congr_drive hS hS0 hxc hx0 hu0 (hEq.mono (Icc_subset_Icc_right htam))
  have hpH : trace (drive 4 canonBM x) ((t : ℝ) - a) ∈ H := by
    rw [← htr]; exact hsh.2.2.1 _ ⟨by linarith, htam⟩
  refine ⟨trace (drive 4 canonBM x) ((t : ℝ) - a), ⟨(t : ℝ) - a, ⟨by linarith, htam⟩, rfl⟩, ?_⟩
  rw [fwdMapInv_eq_of_eqOn (W := fun s : ℝ => w s.toNNReal) (W' := W') ha0
    (lt_of_le_of_lt (by linarith [m.coe_nonneg]) hamt₂') (fun r hr => (frozenDrive_eq hr).symm), ← htr,
    ← htip, hηt]

/-- **The covering numbers of one piece**: `N_n(f_a⁻¹(trace_X[ε, m])) ≤ (2ⁿ)^{15/8}` for all large `n`. -/
theorem eventually_dyadicCount_tracePiece_le (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) (hw0 : w 0 = 0)
    {x : CPath} (hxs : IsSimpleRadialChain (drive 4 canonBM x)) (hxd : HasInteriorDimBound (interiorDimBound 4)
      (drive 4 canonBM x)) {a : ℝ≥0} (ha : (a : ℝ≥0∞) < ζ) {ε m : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, (dyadicCount n (tracePiece w a x ε m) : ℝ) ≤ ((2 : ℝ) ^ n) ^ (15 / 8 : ℝ) := by
  obtain ⟨t₂, hat₂, ht₂ζ⟩ := exists_real_btwn_of_lt ha
  have ht₂ : 0 ≤ t₂ := (NNReal.coe_nonneg _).trans hat₂.le
  have hW' : Continuous (frozenDrive w t₂) := continuous_frozenDrive_of_lt hw ht₂ζ
  have hW'0 : frozenDrive w t₂ 0 = 0 := by rw [frozenDrive_zero ht₂, hw0]
  set E : Set ℂ := trace (drive 4 canonBM x) '' Icc ε m with hEdef
  have hsh := hxs (max m 0)
  have hEc : IsCompact E := by
    rcases le_or_gt ε m with hεm | hεm
    · exact isCompact_Icc.image_of_continuousOn (hsh.2.1.mono (Icc_subset_Icc hε.le (le_max_left _ _)))
    · rw [hEdef, Icc_eq_empty (not_le.2 hεm), image_empty]; exact isCompact_empty
  have hEH : E ⊆ H := by
    rintro _ ⟨u, hu, rfl⟩
    exact hsh.2.2.1 u ⟨hε.trans_le hu.1, hu.2.trans (le_max_left _ _)⟩
  have hbox : ∀ᶠ n in atTop, (dyadicCount n E : ℝ) ≤ ((2 : ℝ) ^ n) ^ interiorDimBound 4 := by
    filter_upwards [hxd.2 E hEc hEH] with n hn
    have hsub : trace (drive 4 canonBM x) '' Ici 0 ∩ E = E :=
      inter_eq_right.2 (image_mono fun u hu => le_trans hε.le hu.1)
    rw [hsub] at hn
    exact_mod_cast hn.2
  have hFd : DifferentiableOn ℂ (fwdMapInv (frozenDrive w t₂) a) H :=
    differentiableOn_fwdMapInv hW' hW'0 a.coe_nonneg
  have himg := WangWu.eventually_dyadicCount_image_le isOpen_H hFd hEc hEH
    (by rw [WangWu.interiorDimBound_four]; norm_num : interiorDimBound 4 < 15 / 8) hbox
  have heq : tracePiece w a x ε m = fwdMapInv (frozenDrive w t₂) a '' E := by
    rw [tracePiece, fwdMapInv_eq_of_eqOn (W := fun s : ℝ => w s.toNNReal) (W' := frozenDrive w t₂)
      a.coe_nonneg hat₂ (fun r hr => (frozenDrive_eq hr).symm)]
  rw [heq]
  exact himg

/-- A piece is compact. -/
theorem isCompact_tracePiece (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) (hw0 : w 0 = 0)
    {x : CPath} (hxs : IsSimpleRadialChain (drive 4 canonBM x)) {a : ℝ≥0} (ha : (a : ℝ≥0∞) < ζ) {ε m : ℝ}
    (hε : 0 < ε) : IsCompact (tracePiece w a x ε m) := by
  obtain ⟨t₂, hat₂, ht₂ζ⟩ := exists_real_btwn_of_lt ha
  have ht₂ : 0 ≤ t₂ := (NNReal.coe_nonneg _).trans hat₂.le
  have hW' : Continuous (frozenDrive w t₂) := continuous_frozenDrive_of_lt hw ht₂ζ
  have hW'0 : frozenDrive w t₂ 0 = 0 := by rw [frozenDrive_zero ht₂, hw0]
  set E : Set ℂ := trace (drive 4 canonBM x) '' Icc ε m with hEdef
  have hsh := hxs (max m 0)
  have hEc : IsCompact E := by
    rcases le_or_gt ε m with hεm | hεm
    · exact isCompact_Icc.image_of_continuousOn (hsh.2.1.mono (Icc_subset_Icc hε.le (le_max_left _ _)))
    · rw [hEdef, Icc_eq_empty (not_le.2 hεm), image_empty]; exact isCompact_empty
  have hEH : E ⊆ H := by
    rintro _ ⟨u, hu, rfl⟩
    exact hsh.2.2.1 u ⟨hε.trans_le hu.1, hu.2.trans (le_max_left _ _)⟩
  have heq : tracePiece w a x ε m = fwdMapInv (frozenDrive w t₂) a '' E := by
    rw [tracePiece, fwdMapInv_eq_of_eqOn (W := fun s : ℝ => w s.toNNReal) (W' := frozenDrive w t₂)
      a.coe_nonneg hat₂ (fun r hr => (frozenDrive_eq hr).symm)]
  rw [heq]
  exact hEc.image_of_continuousOn ((differentiableOn_fwdMapInv hW' hW'0 a.coe_nonneg).continuousOn.mono hEH)

end Piece

/-! ### Finitely many localizations -/

section Cover

variable {nL nR : ℕ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {ζ : ℝ≥0∞}
  {η : ℝ≥0 → ℂ}

/-- **A localization window around an interior visit** (proof of Aux. lemma 15, with an interval on both sides):
at a time `t₁ < ζ` with `η(t₁) ∈ ℍ` and nonzero gaps, there are a rational start `a`, a rational length `m` and `j`
with `a < t₁ < a + m < ζ` and all gaps `≥ 1/(j+1)` on `[a, a + m]`. -/
theorem exists_window (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ})
    (hvL : ∀ i, ContinuousOn (vL i) {t | (t : ℝ≥0∞) < ζ}) (hvR : ∀ i, ContinuousOn (vR i) {t | (t : ℝ≥0∞) < ζ})
    {t₁ : ℝ≥0} (ht₁ : 0 < t₁) (ht₁ζ : (t₁ : ℝ≥0∞) < ζ) (hgL : ∀ i, w t₁ ≠ vL i t₁)
    (hgR : ∀ i, w t₁ ≠ vR i t₁) :
    ∃ i : ℚ × ℚ × ℕ, ∃ ε : ℝ, 0 < ε ∧ ((i.1 : ℝ).toNNReal : ℝ) + ε < t₁ ∧
      (t₁ : ℝ) < (i.1 : ℝ).toNNReal + (i.2.1 : ℝ).toNNReal ∧
      ((((i.1 : ℝ).toNNReal + (i.2.1 : ℝ).toNNReal : ℝ≥0)) : ℝ≥0∞) < ζ ∧
      ∀ s : ℝ≥0, (i.1 : ℝ).toNNReal ≤ s → s ≤ (i.1 : ℝ).toNNReal + (i.2.1 : ℝ).toNNReal →
        GapsGE (1 / ((i.2.2 : ℝ) + 1)) (w s) (fun k => vL k s) (fun k => vR k s) := by
  obtain ⟨ε₀, hε₀, hεgap⟩ := exists_gap_half_lt hw hvL hvR ht₁ζ
  obtain ⟨t₂, ht₁t₂, ht₂ζ⟩ := exists_real_btwn_of_lt ht₁ζ
  have ht₁r : (0 : ℝ) < t₁ := by exact_mod_cast ht₁
  obtain ⟨q₁, hq1, hq2⟩ := exists_rat_btwn (show max ((t₁ : ℝ) - ε₀) 0 < t₁ from max_lt (by linarith) ht₁r)
  have hq0 : (0 : ℝ) < q₁ := lt_of_le_of_lt (le_max_right _ _) hq1
  have hq1' : (t₁ : ℝ) - ε₀ < q₁ := lt_of_le_of_lt (le_max_left _ _) hq1
  obtain ⟨q₂, hq3, hq4⟩ := exists_rat_btwn (show (t₁ : ℝ) - q₁ < min t₂ ((t₁ : ℝ) + ε₀) - q₁ by
    have : (t₁ : ℝ) < min t₂ ((t₁ : ℝ) + ε₀) := lt_min ht₁t₂ (by linarith)
    linarith)
  have hq20 : (0 : ℝ) < q₂ := by linarith
  have ha : (((q₁ : ℝ).toNNReal : ℝ≥0) : ℝ) = q₁ := Real.coe_toNNReal _ hq0.le
  have hm : (((q₂ : ℝ).toNNReal : ℝ≥0) : ℝ) = q₂ := Real.coe_toNNReal _ hq20.le
  have hevn : ∀ᶠ n : ℕ in atTop, (∀ i, 1 / ((n : ℝ) + 1) < |w t₁ - vL i t₁| / 2) ∧
      ∀ i, 1 / ((n : ℝ) + 1) < |w t₁ - vR i t₁| / 2 := by
    have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    refine (Filter.eventually_all.2 fun i => h0.eventually (gt_mem_nhds ?_)).and
      (Filter.eventually_all.2 fun i => h0.eventually (gt_mem_nhds ?_))
    · exact half_pos (abs_pos.2 (sub_ne_zero.2 (hgL i)))
    · exact half_pos (abs_pos.2 (sub_ne_zero.2 (hgR i)))
  obtain ⟨j, hjL, hjR⟩ := hevn.exists
  have hmin1 : min t₂ ((t₁ : ℝ) + ε₀) ≤ t₂ := min_le_left _ _
  have hmin2 : min t₂ ((t₁ : ℝ) + ε₀) ≤ (t₁ : ℝ) + ε₀ := min_le_right _ _
  refine ⟨(q₁, q₂, j), ((t₁ : ℝ) - q₁) / 2, by linarith, ?_, ?_, ?_, ?_⟩
  · show (((q₁ : ℝ).toNNReal : ℝ≥0) : ℝ) + _ < t₁
    rw [ha]; linarith
  · show (t₁ : ℝ) < (((q₁ : ℝ).toNNReal : ℝ≥0) : ℝ) + (((q₂ : ℝ).toNNReal : ℝ≥0) : ℝ)
    rw [ha, hm]; linarith
  · refine lt_of_le_of_lt ?_ ht₂ζ
    rw [← ENNReal.ofReal_coe_nnreal]
    refine ENNReal.ofReal_le_ofReal ?_
    show (((q₁ : ℝ).toNNReal + (q₂ : ℝ).toNNReal : ℝ≥0) : ℝ) ≤ t₂
    rw [NNReal.coe_add, ha, hm]; linarith
  · intro s hs1 hs2
    have hs1' : (q₁ : ℝ) ≤ s := by rw [← ha]; exact_mod_cast hs1
    have hs2' : (s : ℝ) ≤ q₁ + q₂ := by
      have : (s : ℝ) ≤ (((q₁ : ℝ).toNNReal + (q₂ : ℝ).toNNReal : ℝ≥0) : ℝ) := by exact_mod_cast hs2
      rwa [NNReal.coe_add, ha, hm] at this
    have hsd : dist s t₁ < ε₀ := by
      rw [NNReal.dist_eq, abs_lt]
      constructor <;> linarith
    obtain ⟨hL, hR⟩ := hεgap s hsd
    constructor
    · intro i
      rcases hL i with h | h
      · exact (hjL i).le.trans h.le
      · exact absurd h (hgL i)
    · intro i
      rcases hR i with h | h
      · exact (hjR i).le.trans h.le
      · exact absurd h (hgR i)

/-- **The finite cover of the visits of a compact set** (deterministic part of (WF1)). -/
theorem exists_dyadicCount_trace_le (hη : IsGeneratingTrace w ζ η)
    (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) (hw0 : w 0 = 0)
    (hvL : ∀ i, ContinuousOn (vL i) {t | (t : ℝ≥0∞) < ζ}) (hvR : ∀ i, ContinuousOn (vR i) {t | (t : ℝ≥0∞) < ζ})
    (X : ℚ × ℚ × ℕ → CPath)
    (hXs : ∀ i, Continuous (drive 4 canonBM (X i)) ∧ drive 4 canonBM (X i) 0 = 0 ∧
      IsSimpleRadialChain (drive 4 canonBM (X i)))
    (hXd : ∀ i, HasInteriorDimBound (interiorDimBound 4) (drive 4 canonBM (X i)))
    (hXl : ∀ i : ℚ × ℚ × ℕ, ∀ t : ℝ≥0, t ≤ (i.2.1 : ℝ).toNNReal →
      (((i.1 : ℝ).toNNReal + t : ℝ≥0) : ℝ≥0∞) < ζ →
      (∀ s : ℝ≥0, (i.1 : ℝ).toNNReal ≤ s → s ≤ (i.1 : ℝ).toNNReal + t →
        GapsGE (1 / ((i.2.2 : ℝ) + 1)) (w s) (fun k => vL k s) (fun k => vR k s)) →
      w ((i.1 : ℝ).toNNReal + t) - w (i.1 : ℝ).toNNReal = Real.sqrt 4 * (X i).1 t)
    (hgap : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → η t ∈ H → (∀ k, w t ≠ vL k t) ∧ ∀ k, w t ≠ vR k t)
    {T : ℝ≥0} (hT : (T : ℝ≥0∞) < ζ) {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ H) :
    ∃ C : ℝ, ∀ᶠ n in atTop, (dyadicCount n (η '' Icc 0 T ∩ K) : ℝ) ≤ C * ((2 : ℝ) ^ n) ^ (15 / 8 : ℝ) := by
  classical
  set V : Set ℝ≥0 := Icc 0 T ∩ η ⁻¹' K with hVdef
  have hηc : ContinuousOn η (Icc 0 T) :=
    hη.2.1.mono fun r hr => (ENNReal.coe_le_coe.2 hr.2).trans hT.le
  have hVc : IsCompact V :=
    isCompact_Icc.of_isClosed_subset (hηc.preimage_isClosed_of_isClosed isClosed_Icc hK.isClosed)
      inter_subset_left
  -- a window at each visit
  have hwin : ∀ t₁ ∈ V, ∃ i : ℚ × ℚ × ℕ, ∃ ε : ℝ, 0 < ε ∧ ((i.1 : ℝ).toNNReal : ℝ) + ε < t₁ ∧
      (t₁ : ℝ) < (i.1 : ℝ).toNNReal + (i.2.1 : ℝ).toNNReal ∧
      ((((i.1 : ℝ).toNNReal + (i.2.1 : ℝ).toNNReal : ℝ≥0)) : ℝ≥0∞) < ζ ∧
      ∀ s : ℝ≥0, (i.1 : ℝ).toNNReal ≤ s → s ≤ (i.1 : ℝ).toNNReal + (i.2.1 : ℝ).toNNReal →
        GapsGE (1 / ((i.2.2 : ℝ) + 1)) (w s) (fun k => vL k s) (fun k => vR k s) := by
    intro t₁ ht₁
    have ht₁ζ : (t₁ : ℝ≥0∞) < ζ := lt_of_le_of_lt (ENNReal.coe_le_coe.2 ht₁.1.2) hT
    have hH : η t₁ ∈ H := hKH ht₁.2
    have hpos : 0 < t₁ := by
      refine pos_iff_ne_zero.2 fun h0 => ?_
      rw [h0, hη.1] at hH
      exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from hH)
    obtain ⟨hgL, hgR⟩ := hgap t₁ ht₁ζ hH
    exact exists_window hw hvL hvR hpos ht₁ζ hgL hgR
  choose! iW εW hεW hlo hhi hζW hgW using hwin
  set O : ℝ≥0 → Set ℝ≥0 := fun t₁ => {t : ℝ≥0 | ((iW t₁).1 : ℝ).toNNReal + εW t₁ < t ∧
    (t : ℝ) < ((iW t₁).1 : ℝ).toNNReal + ((iW t₁).2.1 : ℝ).toNNReal} with hOdef
  have hOo : ∀ t₁ ∈ V, IsOpen (O t₁) := fun t₁ _ =>
    (isOpen_lt continuous_const NNReal.continuous_coe).inter (isOpen_lt NNReal.continuous_coe continuous_const)
  have hcov : V ⊆ ⋃ t₁ ∈ V, O t₁ := fun t ht => mem_iUnion₂.2 ⟨t, ht, hlo t ht, hhi t ht⟩
  obtain ⟨F, hFV, hFfin, hFcov⟩ := hVc.elim_finite_subcover_image hOo hcov
  -- the pieces
  set Pc : ℝ≥0 → Set ℂ := fun t₁ => tracePiece w ((iW t₁).1 : ℝ).toNNReal (X (iW t₁)) (εW t₁)
    ((iW t₁).2.1 : ℝ).toNNReal with hPcdef
  have hsub : η '' Icc 0 T ∩ K ⊆ ⋃ t₁ ∈ hFfin.toFinset, Pc t₁ := by
    rintro _ ⟨⟨t, ht, rfl⟩, htK⟩
    obtain ⟨t₁, ht₁F, htO⟩ := mem_iUnion₂.1 (hFcov ⟨ht, htK⟩)
    refine mem_iUnion₂.2 ⟨t₁, hFfin.mem_toFinset.2 ht₁F, ?_⟩
    have hV1 := hFV ht₁F
    obtain ⟨hc, h0, hs⟩ := hXs (iW t₁)
    refine mem_tracePiece hη hw hw0 hc h0 hs (hζW t₁ hV1) (fun s hs1 => ?_) (hεW t₁ hV1) htO.1.le htO.2.le
    refine hXl (iW t₁) s hs1 (lt_of_le_of_lt (ENNReal.coe_le_coe.2 (add_le_add_right hs1 _)) (hζW t₁ hV1))
      fun r hr1 hr2 => hgW t₁ hV1 r hr1 (hr2.trans (add_le_add_right hs1 _))
  have hcnt : ∀ t₁ ∈ hFfin.toFinset, ∀ᶠ n in atTop,
      (dyadicCount n (Pc t₁) : ℝ) ≤ ((2 : ℝ) ^ n) ^ (15 / 8 : ℝ) := fun t₁ ht₁ => by
    have hV1 := hFV (hFfin.mem_toFinset.1 ht₁)
    exact eventually_dyadicCount_tracePiece_le hw hw0 (hXs (iW t₁)).2.2 (hXd (iW t₁))
      (lt_of_le_of_lt (ENNReal.coe_le_coe.2 le_self_add) (hζW t₁ hV1)) (hεW t₁ hV1)
  have hbdd : ∀ t₁ ∈ hFfin.toFinset, Bornology.IsBounded (Pc t₁) := fun t₁ ht₁ => by
    have hV1 := hFV (hFfin.mem_toFinset.1 ht₁)
    exact (isCompact_tracePiece hw hw0 (hXs (iW t₁)).2.2
      (lt_of_le_of_lt (ENNReal.coe_le_coe.2 le_self_add) (hζW t₁ hV1)) (hεW t₁ hV1)).isBounded
  refine ⟨hFfin.toFinset.card, ?_⟩
  filter_upwards [(Filter.eventually_all_finset _).2 hcnt] with n hn
  have hsubh : dyadicHits n (η '' Icc 0 T ∩ K) ⊆ ⋃ t₁ ∈ hFfin.toFinset, dyadicHits n (Pc t₁) := by
    rintro k ⟨z, hzk, hz⟩
    obtain ⟨t₁, ht₁, hzP⟩ := mem_iUnion₂.1 (hsub hz)
    exact mem_iUnion₂.2 ⟨t₁, ht₁, z, hzk, hzP⟩
  have hfin : (⋃ t₁ ∈ hFfin.toFinset, dyadicHits n (Pc t₁)).Finite :=
    Set.Finite.biUnion (Finset.finite_toSet _) fun t₁ ht₁ => dyadicHits_finite (hbdd t₁ ht₁)
  have h1 : (dyadicCount n (η '' Icc 0 T ∩ K) : ℝ) ≤ ∑ t₁ ∈ hFfin.toFinset, (dyadicCount n (Pc t₁) : ℝ) := by
    have := (Set.ncard_le_ncard hsubh hfin).trans (Finset.set_ncard_biUnion_le _ _)
    exact_mod_cast this
  refine h1.trans ?_
  calc ∑ t₁ ∈ hFfin.toFinset, (dyadicCount n (Pc t₁) : ℝ)
      ≤ ∑ _t₁ ∈ hFfin.toFinset, ((2 : ℝ) ^ n) ^ (15 / 8 : ℝ) := Finset.sum_le_sum fun t₁ ht₁ => hn t₁ ht₁
    _ = (hFfin.toFinset.card : ℝ) * ((2 : ℝ) ^ n) ^ (15 / 8 : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]

end Cover

/-! ### Almost surely, for every force word -/

section AE

variable {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {Ω : Type*}
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **(WF1) at `κ = 4` for every force word.** Almost surely, for every continuous generating trace `η` through the
lifetime, every `T < ζ` and every compact `K ⊆ ℍ`: `N_n(η[0,T] ∩ K) (n + 1) 4^{-n} → 0`. -/
theorem ae_tendsto_dyadicCount_trace_four [IsProbabilityMeasure P]
    (hE : IsIntegratedSLEEvolution 4 xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η → ∀ T : ℝ≥0, (T : ℝ≥0∞) < ζ ω →
      ∀ K : Set ℂ, IsCompact K → K ⊆ H →
        Tendsto (fun n : ℕ => (dyadicCount n (η '' Icc 0 T ∩ K) : ℝ) * (n + 1) / 4 ^ n) atTop (𝓝 0) := by
  have hloc := fun i : ℚ × ℚ × ℕ => Dimension.exists_brownian_localization four_pos hE
    ((i.1 : ℝ).toNNReal) ((i.2.1 : ℝ).toNNReal) (show (0 : ℝ) < 1 / ((i.2.2 : ℝ) + 1) by positivity)
  choose X hXm μ hμprob hμBM hac hXeq using hloc
  have hgood : ∀ i, ∀ᵐ ω ∂P, Continuous (drive 4 canonBM (X i ω)) ∧ drive 4 canonBM (X i ω) 0 = 0 ∧
      IsSimpleRadialChain (drive 4 canonBM (X i ω)) := fun i => by
    have := hμprob i
    exact ae_of_ae_map (hXm i).aemeasurable ((hac i).ae_le (WangWu.ae_isSimpleRadialChain_drive_four (hμBM i)))
  have hdim : ∀ i, ∀ᵐ ω ∂P, HasInteriorDimBound (interiorDimBound 4) (drive 4 canonBM (X i ω)) := fun i => by
    have := hμprob i
    filter_upwards [ae_trace_good_of_absolutelyContinuous four_pos (by norm_num) (hXm i).aemeasurable
      (hμBM i) (hac i)] with ω h using h.2.2
  filter_upwards [ae_all_iff.2 hgood, ae_all_iff.2 hdim, ae_all_iff.2 hXeq, hE.ae_forall_ne_of_mem_H,
    hE.2.2.2.2] with ω hg hd hx hgap hp η hη T hT K hK hKH
  obtain ⟨C, hC⟩ := exists_dyadicCount_trace_le hη hp.2.2.2.1 hp.1 hp.2.2.2.2.1 hp.2.2.2.2.2.1
    (fun i => X i ω) hg hd (fun i t ht htζ hgp => hx i t ht htζ hgp) (hgap η hη) hT hK hKH
  refine squeeze_zero' (Eventually.of_forall fun n => by positivity) ?_
    (WangWu.tendsto_mul_rpow_mul_succ_div_four_pow (by norm_num : (15 / 8 : ℝ) < 2) C)
  filter_upwards [hC] with n hn
  have h4 : (0 : ℝ) < 4 ^ n := by positivity
  have hn1 : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  rw [div_le_div_iff_of_pos_right h4]
  exact mul_le_mul_of_nonneg_right hn hn1

end AE

end WholeField

end InteractingSLE
