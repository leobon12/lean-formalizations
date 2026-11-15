/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BrClause
import InteractingSLE.Spec.Supplement.GW2BkCol

/-!
# A continuation threshold of a near word forces the cell exit strictly earlier

Packet PROVE-GW2-BUF (round 16). The near family's word at every index `m` is a DS1 word
(`NearCrossingFamily.hw`). It is ordered, and every NEAR prefix sum of its weights is `> −2`: left labels `i < mL`
and right labels `j < mR`. The labels colliding with the driver on one side are a prefix of that side's labels:
`w ≤ rightImg w x` for every `x`, and `rightImg w x` is monotone in `x`. So the side triggering a continuation
threshold (`ForceWord.ThresholdCondition`: colliding weights summing to `≤ −2`) has a colliding CONTROLLED label
(`i ≥ mL` or `j ≥ mR`). A controlled collision is preceded by an exit from the cell buffer, whose controlled labels
are exactly these (`cellBuf_famShapeB_eq`, by the family's orientation clause).

* `rightImg_eq_of_le_of_eq`, **`exists_ctrl_of_sum_le`** (the colliding set is a prefix);
* **`ctrl_collision_of_threshold`**, **`imgState_ctrl_of_threshold`** (a threshold has a controlled collision);
* **`cellBuf_famShapeB_eq`** (the cell buffer of the family's shape is `InBuffer f.mL f.mR`);
* `cellStop_le_of_notMem`, `cellStop_le_cap`;
* **`cellStop_lt_of_threshold`**: the cell exit fires strictly before every time at which the comparison image state
  satisfies the threshold of the family's word at any index `m`;
* **`cellStop_lt_of_gap_le`**: the cell exit fires strictly before `L'` once some controlled comparison gap is at most
  the cell level at a time before `L'` (the form the contact clause gives).
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology Finset
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Bh

open MartChar.RealFlow Exist.StagedLaw Supp8.GB6 Supp8.GB6.HullId GW2TipSystem GW2TipSystem.RootN4 GW2JDetR11
  Supp12.DSReach

/-! ### Colliding labels form a prefix -/

/-- A label left of a colliding label collides. -/
theorem rightImg_eq_of_le_of_eq {W : ℝ → ℝ} (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t) {x x' : ℝ} (hxx : x ≤ x')
    (h : rightImg W x' t = W t) : rightImg W x t = W t :=
  le_antisymm ((rightImg_mono_index hW ht hxx).trans h.le) (le_rightImg hW x ht)

/-- **A colliding set with weight `≤ −2` reaches a controlled label**, when the labels are sorted and every prefix
below `m` has weight `> −2`. -/
theorem exists_ctrl_of_sum_le {n : ℕ} {x : Fin n → ℝ} (hx : Monotone x) {ρ : Fin n → ℝ} {m : ℕ}
    (hp : ∀ j : Fin n, (j : ℕ) < m → -2 < ∑ l ∈ univ.filter (fun l => l ≤ j), ρ l)
    {W : ℝ → ℝ} (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t)
    (hsum : (∑ j ∈ univ.filter (fun j => rightImg W (x j) t = W t), ρ j) ≤ -2) :
    ∃ j : Fin n, m ≤ (j : ℕ) ∧ rightImg W (x j) t = W t := by
  set S := univ.filter (fun j => rightImg W (x j) t = W t) with hS
  have hne : S.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h, Finset.sum_empty] at hsum
    linarith
  have hJ : S.max' hne ∈ S := S.max'_mem hne
  have hJcol : rightImg W (x (S.max' hne)) t = W t := (Finset.mem_filter.1 hJ).2
  have hSeq : S = univ.filter (fun l => l ≤ S.max' hne) := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hl
      exact S.le_max' l hl
    · intro hl
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, rightImg_eq_of_le_of_eq hW ht (hx hl) hJcol⟩
  refine ⟨S.max' hne, ?_, hJcol⟩
  by_contra hlt
  have h1 := hp (S.max' hne) (not_le.1 hlt)
  rw [← hSeq] at h1
  linarith

/-- **A continuation threshold has a colliding controlled label.** -/
theorem ctrl_collision_of_threshold {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    (hord : IsOrderedForceWord xL xR) {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {mL mR : ℕ}
    (hpL : ∀ i : Fin nL, (i : ℕ) < mL → -2 < ∑ l ∈ univ.filter (fun l => l ≤ i), ρL l)
    (hpR : ∀ j : Fin nR, (j : ℕ) < mR → -2 < ∑ l ∈ univ.filter (fun l => l ≤ j), ρR l)
    {W : ℝ → ℝ} (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t)
    (hthr : ForceWord.ThresholdCondition ρL ρR (W t) (fun i => -rightImg (fun s => -W s) (-xL i) t)
      (fun j => rightImg W (xR j) t)) :
    (∃ j : Fin nR, mR ≤ (j : ℕ) ∧ rightImg W (xR j) t = W t) ∨
      ∃ i : Fin nL, mL ≤ (i : ℕ) ∧ -rightImg (fun s => -W s) (-xL i) t = W t := by
  unfold ForceWord.ThresholdCondition at hthr
  rcases hthr with h | h
  · right
    have hW' : Continuous fun s => -W s := hW.neg
    have hmono : Monotone fun i => -xL i := fun i i' hii => neg_le_neg (hord.1 hii)
    have hfilt : univ.filter (fun i => -rightImg (fun s => -W s) (-xL i) t = W t) =
        univ.filter (fun i => rightImg (fun s => -W s) ((fun i => -xL i) i) t = (fun s => -W s) t) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor <;> intro hi <;> linarith
    rw [hfilt] at h
    obtain ⟨i, hi, hcol⟩ := exists_ctrl_of_sum_le (x := fun i => -xL i) hmono hpL hW' ht h
    refine ⟨i, hi, ?_⟩
    have hcol' : rightImg (fun s => -W s) (-xL i) t = -W t := hcol
    linarith
  · left
    exact exists_ctrl_of_sum_le hord.2.2.1 hpR hW ht h

/-- **In image-state form**: a threshold of the image state of a continuous path has a colliding controlled
label. -/
theorem imgState_ctrl_of_threshold {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    (hord : IsOrderedForceWord xL xR) {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {mL mR : ℕ}
    (hpL : ∀ i : Fin nL, (i : ℕ) < mL → -2 < ∑ l ∈ univ.filter (fun l => l ≤ i), ρL l)
    (hpR : ∀ j : Fin nR, (j : ℕ) < mR → -2 < ∑ l ∈ univ.filter (fun l => l ≤ j), ρR l)
    {w : ℝ≥0 → ℝ} (hw : Continuous w) (t : ℝ≥0)
    (hthr : ForceWord.ThresholdCondition ρL ρR (GW2Sdg.imgState xL xR w t).1 (GW2Sdg.imgState xL xR w t).2.1
      (GW2Sdg.imgState xL xR w t).2.2) :
    (∃ j : Fin nR, mR ≤ (j : ℕ) ∧ (GW2Sdg.imgState xL xR w t).2.2 j = (GW2Sdg.imgState xL xR w t).1) ∨
      ∃ i : Fin nL, mL ≤ (i : ℕ) ∧ (GW2Sdg.imgState xL xR w t).2.1 i = (GW2Sdg.imgState xL xR w t).1 := by
  have hW : Continuous (frozenDrive w (t : ℝ)) := continuous_frozenDrive hw.continuousOn
  have hWt : frozenDrive w (t : ℝ) (t : ℝ) = w t := by
    simp only [frozenDrive, min_self, Real.toNNReal_coe]
  have h1 : (GW2Sdg.imgState xL xR w t).1 = frozenDrive w (t : ℝ) (t : ℝ) := by
    rw [hWt]
    rfl
  have hthr' : ForceWord.ThresholdCondition ρL ρR (frozenDrive w (t : ℝ) (t : ℝ))
      (fun i => -rightImg (fun s => -frozenDrive w (t : ℝ) s) (-xL i) t)
      (fun j => rightImg (frozenDrive w (t : ℝ)) (xR j) t) := by
    rw [← h1]
    exact hthr
  rcases ctrl_collision_of_threshold hord hpL hpR hW t.coe_nonneg hthr' with ⟨j, hj, hcol⟩ | ⟨i, hi, hcol⟩
  · exact Or.inl ⟨j, hj, by rw [h1]; exact hcol⟩
  · exact Or.inr ⟨i, hi, by rw [h1]; exact hcol⟩

/-! ### The cell buffer of the family's shape -/

/-- **The cell buffer of the family's shape keeps the gaps of the labels `i ≥ mL` and `j ≥ mR`** (by the
orientation clause: `mR = nR − 1` going left, `mL = nL − 1` going right). -/
theorem cellBuf_famShapeB_eq {κ : ℝ} (f : NearCrossingFamily.{u} κ) (R k : ℕ) :
    cellBuf (famShapeB f, R, k) = {p | InBuffer f.mL f.mR (R : ℝ) ((1 / 2 : ℝ) ^ k) p} := by
  unfold cellBuf
  rcases f.horientation with ⟨hg, hmR, -⟩ | ⟨hg, hmL, -⟩
  · simp only [famShapeB, hg, ↓reduceIte]
    rw [← hmR]
  · simp only [famShapeB, hg, Bool.false_eq_true, ↓reduceIte]
    rw [← hmL]

section Cell

variable {κ : ℝ} (f : NearCrossingFamily.{u} κ) (cell : RecData → NearCell) (posL posR : RecData → ℕ → ℝ)
  {y : RecData}

/-- The image state with the record's labels is in the record's cell iff the family's is in the family's. -/
theorem imgState_mem_cell_iff (hsh : famShapeB f = (cell y).1) (hL : ∀ i : Fin f.nL, f.xL i = posL y i)
    (hR : ∀ j : Fin f.nR, f.xR j = posR y j) (w : ℝ≥0 → ℝ) (t : ℝ≥0) :
    GW2Sdg.imgState (fun i : Fin (cell y).1.1 => posL y i) (fun j : Fin (cell y).1.2.1 => posR y j) w t ∈
        cellBuf (cell y) ↔
      GW2Sdg.imgState f.xL f.xR w t ∈ cellBuf (famShapeB f, (cell y).2.1, (cell y).2.2) := by
  refine imgState_mem_cellBuf_transport hsh.symm (cell y).2.1 (cell y).2.2 _ _ f.xL f.xR (fun i => ?_)
    (fun j => ?_) w t
  · have hn : f.nL = (cell y).1.1 := congrArg (fun K : NearShape => K.1) hsh
    exact (hL ⟨(i : ℕ), by rw [hn]; exact i.2⟩).symm
  · have hn : f.nR = (cell y).1.2.1 := congrArg (fun K : NearShape => K.2.1) hsh
    exact (hR ⟨(j : ℕ), by rw [hn]; exact j.2⟩).symm

/-- The cell exit fires no later than a time below the cap at which the family's image state is outside the cell. -/
theorem cellStop_le_of_notMem (hsh : famShapeB f = (cell y).1) (hL : ∀ i : Fin f.nL, f.xL i = posL y i)
    (hR : ∀ j : Fin f.nR, f.xR j = posR y j) (a : ℝ≥0) (b : ℝ) {c : ℝ≥0} (hc : 0 < c) {w : ℝ≥0 → ℝ}
    (hw : Continuous w)
    (h0 : GW2Sdg.imgState f.xL f.xR (scaledPath a b w) 0 ∈ cellBuf (famShapeB f, (cell y).2.1, (cell y).2.2))
    {t₁ : ℝ≥0} (ht₁ : t₁ ≤ c)
    (hout : GW2Sdg.imgState f.xL f.xR (scaledPath a b w) (a * t₁) ∉
      cellBuf (famShapeB f, (cell y).2.1, (cell y).2.2)) :
    cellStop cell posL posR a b c (y, w) ≤ t₁ := by
  rw [cellStop_eq]
  exact exitRule_le_of_notMem _ _ (isOpen_cellBuf _) (compl_cellBuf_nonempty _) a b hc y hw
    ((imgState_mem_cell_iff f cell posL posR hsh hL hR _ 0).2 h0) ht₁
    (fun h => hout ((imgState_mem_cell_iff f cell posL posR hsh hL hR _ _).1 h))

/-- The cell exit is at most the cap. -/
theorem cellStop_le_cap (hsh : famShapeB f = (cell y).1) (hL : ∀ i : Fin f.nL, f.xL i = posL y i)
    (hR : ∀ j : Fin f.nR, f.xR j = posR y j) (a : ℝ≥0) (b : ℝ) {c : ℝ≥0} (hc : 0 < c) {w : ℝ≥0 → ℝ}
    (hw : Continuous w)
    (h0 : GW2Sdg.imgState f.xL f.xR (scaledPath a b w) 0 ∈ cellBuf (famShapeB f, (cell y).2.1, (cell y).2.2)) :
    cellStop cell posL posR a b c (y, w) ≤ c := by
  obtain ⟨τ, hτ, -, hτc, -⟩ := exitRule_spec (fun i : Fin (cell y).1.1 => posL y i)
    (fun j : Fin (cell y).1.2.1 => posR y j) (isOpen_cellBuf (cell y)) (compl_cellBuf_nonempty (cell y)) a b hc y
    hw ((imgState_mem_cell_iff f cell posL posR hsh hL hR _ 0).2 h0)
  rw [cellStop_eq, hτ]
  exact ENNReal.coe_le_coe.2 hτc

/-- **The cell exit fires strictly before a continuation threshold** of the family's word at any index `m`, read
on the comparison image state. -/
theorem cellStop_lt_of_threshold (hsh : famShapeB f = (cell y).1) (hL : ∀ i : Fin f.nL, f.xL i = posL y i)
    (hR : ∀ j : Fin f.nR, f.xR j = posR y j) {a : ℝ≥0} (ha : 0 < a) (b : ℝ) {c : ℝ≥0} (hc : 0 < c)
    {w : ℝ≥0 → ℝ} (hw : Continuous w)
    (h0 : GW2Sdg.imgState f.xL f.xR (scaledPath a b w) 0 ∈ cellBuf (famShapeB f, (cell y).2.1, (cell y).2.2))
    (m : ℕ) {σ : ℝ≥0}
    (hthr : ForceWord.ThresholdCondition (f.ρLs m) (f.ρRs m)
      (GW2Sdg.imgState f.xL f.xR (scaledPath a b w) (a * σ)).1
      (GW2Sdg.imgState f.xL f.xR (scaledPath a b w) (a * σ)).2.1
      (GW2Sdg.imgState f.xL f.xR (scaledPath a b w) (a * σ)).2.2) :
    cellStop cell posL posR a b c (y, w) < σ := by
  obtain ⟨hord, -, -, hpL', hpR'⟩ := f.hw m
  have hpL : ∀ i : Fin f.nL, (i : ℕ) < f.mL → -2 < ∑ l ∈ univ.filter (fun l => l ≤ i), f.ρLs m l :=
    fun i hi => by have := hpL' i hi; linarith [f.hε]
  have hpR : ∀ j : Fin f.nR, (j : ℕ) < f.mR → -2 < ∑ l ∈ univ.filter (fun l => l ≤ j), f.ρRs m l :=
    fun j hj => by have := hpR' j hj; linarith [f.hε]
  have hsw := continuous_scaledPath a b hw
  set p : ℝ≥0 → ℝ × (Fin f.nL → ℝ) × (Fin f.nR → ℝ) := fun t => GW2Sdg.imgState f.xL f.xR (scaledPath a b w) t
    with hpdef
  have hp : Continuous p := continuous_imgState f.xL f.xR hsw
  have h0' : InBuffer f.mL f.mR ((cell y).2.1 : ℝ) ((1 / 2 : ℝ) ^ (cell y).2.2) (p 0) := by
    have := h0
    rw [cellBuf_famShapeB_eq] at this
    exact this
  have hg : (0 : ℝ) < (1 / 2 : ℝ) ^ (cell y).2.2 := by positivity
  have hex : ∃ t < a * σ, ¬ InBuffer f.mL f.mR ((cell y).2.1 : ℝ) ((1 / 2 : ℝ) ^ (cell y).2.2) (p t) := by
    rcases imgState_ctrl_of_threshold hord hpL hpR hsw (a * σ) hthr with ⟨j, hj, hcol⟩ | ⟨i, hi, hcol⟩
    · exact exists_notMem_before_rightCollision hg hp h0' hj hcol
    · exact exists_notMem_before_leftCollision hg hp h0' hi hcol
  obtain ⟨t, ht, hout⟩ := hex
  by_cases hσc : σ ≤ c
  · have ht₁ : t / a < σ := (div_lt_iff₀ ha).2 (by rwa [mul_comm])
    have heq : a * (t / a) = t := mul_div_cancel₀ t ha.ne'
    have hle := cellStop_le_of_notMem f cell posL posR hsh hL hR a b hc hw h0 (ht₁.le.trans hσc)
      (by
        rw [heq, cellBuf_famShapeB_eq]
        exact hout)
    exact lt_of_le_of_lt hle (by exact_mod_cast ht₁)
  · exact lt_of_le_of_lt (cellStop_le_cap f cell posL posR hsh hL hR a b hc hw h0)
      (by exact_mod_cast not_le.1 hσc)

/-- **The cell exit fires strictly before `L'`** once some controlled comparison gap is at most the cell level at a
time before `L'`. -/
theorem cellStop_lt_of_gap_le (hsh : famShapeB f = (cell y).1) (hL : ∀ i : Fin f.nL, f.xL i = posL y i)
    (hR : ∀ j : Fin f.nR, f.xR j = posR y j) (a : ℝ≥0) (b : ℝ) {c : ℝ≥0} (hc : 0 < c)
    {w : ℝ≥0 → ℝ} (hw : Continuous w)
    (h0 : GW2Sdg.imgState f.xL f.xR (scaledPath a b w) 0 ∈ cellBuf (famShapeB f, (cell y).2.1, (cell y).2.2))
    {L' : ℝ≥0∞} {u : ℝ≥0} (hu : (u : ℝ≥0∞) < L')
    (hgap : (∃ j : Fin f.nR, f.mR ≤ (j : ℕ) ∧
        (GW2Sdg.imgState f.xL f.xR (scaledPath a b w) (a * u)).2.2 j -
          (GW2Sdg.imgState f.xL f.xR (scaledPath a b w) (a * u)).1 ≤ (1 / 2 : ℝ) ^ (cell y).2.2) ∨
      ∃ i : Fin f.nL, f.mL ≤ (i : ℕ) ∧
        (GW2Sdg.imgState f.xL f.xR (scaledPath a b w) (a * u)).1 -
          (GW2Sdg.imgState f.xL f.xR (scaledPath a b w) (a * u)).2.1 i ≤ (1 / 2 : ℝ) ^ (cell y).2.2) :
    cellStop cell posL posR a b c (y, w) < L' := by
  have hout : GW2Sdg.imgState f.xL f.xR (scaledPath a b w) (a * u) ∉
      cellBuf (famShapeB f, (cell y).2.1, (cell y).2.2) := by
    rw [cellBuf_famShapeB_eq]
    intro hin
    rcases hgap with ⟨j, hj, hle⟩ | ⟨i, hi, hle⟩
    · exact absurd (hin.2.1 j hj) (not_lt.2 hle)
    · exact absurd (hin.2.2 i hi) (not_lt.2 hle)
  by_cases huc : u ≤ c
  · exact lt_of_le_of_lt (cellStop_le_of_notMem f cell posL posR hsh hL hR a b hc hw h0 huc hout) hu
  · exact lt_of_le_of_lt (cellStop_le_cap f cell posL posR hsh hL hR a b hc hw h0)
      (lt_trans (by exact_mod_cast not_le.1 huc) hu)

end Cell

end InteractingSLE.Theorem14.GW2Bh
