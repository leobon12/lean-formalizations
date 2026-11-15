/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SdyWord
import InteractingSLE.Spec.Restart.FCDetTransfer

/-!
# Measurability of the near structure and the near shape data in the word (decision D16)

Packet PROVE-GW2-BUF (round 11). D16 (FABLE-4, R121): BUF proves that the near buffer's SHAPE `(nL, nR, mL, mR,
goLeft)` and the label POSITIONS are measurable in the record, once SDE pins them as explicit functions of the
dilated base word (`nearShape`, SDE round 14). This file proves the word-level measurability of every ingredient,
from committed definitions only.

* **`forall_offJumps_iff_rat`**: for a word `c` and an open set `O`, a condition on `c.fn y` for all `y ∈ O` off
  the jumps holds iff it holds at the rational such `y`, because `c.fn` is locally constant off the jumps.
* `measurableSet_mem_jumps`, `measurable_fn_at`, **`measurableSet_offJumps`**: such conditions cut measurable sets
  of words.
* **`measurable_lastXL`**, **`measurable_lastXR`**: the outermost flow-line labels from `0`.
* **`measurableSet_nearStructTopW`** / **`measurableSet_nearStructBotW`**, `nearStructTop_iff` /
  `nearStructBot_iff`, **`measurable_nearDilWord`**: so `{(s, c) | NearStructTop κ s flip c}` and the `Bot` version
  are measurable (**`measurableSet_nearStructTop`**, **`measurableSet_nearStructBot`**).
* **`measurable_cutCountL`**, **`measurable_cutCountR`**: the far-block counts (SDE's `cutL`, `cutR`) and
  **`measurable_padXL`**, **`measurable_padXR`**: the label positions on each shape cell (padded by `0`).
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology Finset
open scoped NNReal ENNReal
open QuantumZipper (chiC)

namespace InteractingSLE.Theorem14.GW2Bh

open Restart GW2Sdy GW2TipSystem GW2TipSystem.RootH10

/-! ### Off-jump conditions are countable -/

/-- **Off the jumps, a pointwise condition on an open set is decided at rational points.** -/
theorem forall_offJumps_iff_rat (c : BoundaryWord) {O : Set ℝ} (hO : IsOpen O) (P : ℝ → Prop) :
    (∀ y ∈ O, y ∉ c.jumps → P (c.fn y)) ↔ ∀ q : ℚ, (q : ℝ) ∈ O → (q : ℝ) ∉ c.jumps → P (c.fn q) := by
  refine ⟨fun h q hq hqJ => h q hq hqJ, fun h y hyO hyJ => ?_⟩
  have hJc : IsOpen ((c.jumps : Set ℝ)ᶜ) := c.jumps.finite_toSet.isClosed.isOpen_compl
  have h1 : ∀ᶠ z in 𝓝 y, z ∈ O := hO.mem_nhds hyO
  have h2 : ∀ᶠ z in 𝓝 y, z ∈ ((c.jumps : Set ℝ)ᶜ) := hJc.mem_nhds hyJ
  have hev : ∀ᶠ z in 𝓝 y, z ∈ O ∧ z ∉ c.jumps ∧ c.index z = c.index y :=
    h1.and (h2.and (BoundaryWord.eventually_index_eq hyJ))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show y < y + ε by linarith)
  have hqd : dist (q : ℝ) y < ε := by
    rw [Real.dist_eq, abs_of_pos (by linarith)]
    linarith
  obtain ⟨hqO, hqJ, hqi⟩ := hball hqd
  have := h q hqO hqJ
  have e : c.fn q = c.fn y := by
    unfold BoundaryWord.fn
    rw [hqi]
  rwa [e] at this

theorem measurableSet_mem_jumps (y : ℝ) : MeasurableSet {c : BoundaryWord | y ∈ c.jumps} := by
  have e : {c : BoundaryWord | y ∈ c.jumps} = ⋃ i : ℕ, ({c : BoundaryWord | i < c.1} ∩
      (fun c : BoundaryWord => c.2.1 i) ⁻¹' {y}) := by
    ext c
    simp only [Set.mem_ofPred_eq, mem_iUnion, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
      BoundaryWord.mem_jumps]
  rw [e]
  refine MeasurableSet.iUnion fun i => ?_
  exact (measurable_fst (MeasurableSet.of_discrete (s := {n : ℕ | i < n}))).inter
    (BoundaryWord.measurable_position i (measurableSet_singleton y))

theorem measurable_fn_at (y : ℝ) : Measurable fun c : BoundaryWord => c.fn y :=
  measurable_height measurable_id (BoundaryWord.measurable_index.comp (measurable_id.prodMk measurable_const))

/-- **An off-jump condition on a measurable open window cuts a measurable set of words.** -/
theorem measurableSet_offJumps {O : BoundaryWord → Set ℝ} (hO : ∀ c, IsOpen (O c))
    (hOq : ∀ q : ℚ, MeasurableSet {c | (q : ℝ) ∈ O c}) {S : Set ℝ} (hS : MeasurableSet S) :
    MeasurableSet {c : BoundaryWord | ∀ y ∈ O c, y ∉ c.jumps → c.fn y ∈ S} := by
  have e : {c : BoundaryWord | ∀ y ∈ O c, y ∉ c.jumps → c.fn y ∈ S} =
      ⋂ q : ℚ, ({c | (q : ℝ) ∈ O c}ᶜ ∪ ({c : BoundaryWord | (q : ℝ) ∈ c.jumps} ∪
        (fun c : BoundaryWord => c.fn q) ⁻¹' S)) := by
    ext c
    rw [Set.mem_ofPred_eq, forall_offJumps_iff_rat c (hO c) (· ∈ S)]
    simp only [mem_iInter, Set.mem_union, Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_preimage]
    refine forall_congr' fun q => ?_
    tauto
  rw [e]
  exact MeasurableSet.iInter fun q =>
    (hOq q).compl.union ((measurableSet_mem_jumps q).union (measurable_fn_at q hS))

/-! ### The outermost labels -/

/-- Reading a measurable `ℕ`-indexed family at a measurable index. -/
theorem measurable_eval_nat {α : Type*} [MeasurableSpace α] {f : α → ℕ → ℝ} (hf : Measurable f)
    {k : α → ℕ} (hk : Measurable k) : Measurable fun a => f a (k a) := by
  have h : Measurable fun r : α × ℕ => f r.1 r.2 :=
    measurable_from_prod_countable_left fun m => (measurable_pi_apply m).comp hf
  exact h.comp (measurable_id.prodMk hk)

/-- The padded left label positions of the flow-line word from `0`. -/
def padXL (β : BoundaryWord) : ℕ → ℝ := (flowPad 0 0 (β, 0)).1.1

/-- The padded right label positions of the flow-line word from `0`. -/
def padXR (β : BoundaryWord) : ℕ → ℝ := (flowPad 0 0 (β, 0)).1.2

theorem measurable_padXL : Measurable padXL :=
  (measurable_fst.comp (measurable_fst.comp (measurable_flowPad 0 0))).comp (measurable_id.prodMk measurable_const)

theorem measurable_padXR : Measurable padXR :=
  (measurable_snd.comp (measurable_fst.comp (measurable_flowPad 0 0))).comp (measurable_id.prodMk measurable_const)

theorem padXL_eq (β : BoundaryWord) (i : Fin (flowLineNL β.fn β.jumps 0)) :
    padXL β i = flowLineXL β.fn β.jumps 0 i := by
  simp only [padXL, flowPad, i.2, ↓reduceDIte, Fin.eta]

theorem padXR_eq (β : BoundaryWord) (j : Fin (flowLineNR β.fn β.jumps 0)) :
    padXR β j = flowLineXR β.fn β.jumps 0 j := by
  simp only [padXR, flowPad, j.2, ↓reduceDIte, Fin.eta]

/-- The outermost left label. -/
def lastXL (β : BoundaryWord) : ℝ := flowLineXL β.fn β.jumps 0 (GW2TipStage.lastL β.fn β.jumps)

/-- The outermost right label. -/
def lastXR (β : BoundaryWord) : ℝ := flowLineXR β.fn β.jumps 0 (GW2TipStage.lastR β.fn β.jumps)

theorem measurable_lastXL : Measurable lastXL := by
  have e : lastXL = fun β => padXL β (flowLineNL β.fn β.jumps 0 - 1) := by
    funext β
    rw [lastXL, ← padXL_eq]
    rfl
  rw [e]
  exact measurable_eval_nat measurable_padXL ((measurable_from_nat (f := fun n : ℕ => n - 1)).comp
    FCDet.measurable_flowLineNL_zero)

theorem measurable_lastXR : Measurable lastXR := by
  have e : lastXR = fun β => padXR β (flowLineNR β.fn β.jumps 0 - 1) := by
    funext β
    rw [lastXR, ← padXR_eq]
    rfl
  rw [e]
  exact measurable_eval_nat measurable_padXR ((measurable_from_nat (f := fun n : ℕ => n - 1)).comp
    FCDet.measurable_flowLineNR_zero)

/-! ### The near structures -/

theorem measurableSet_oldLeftHeights (κ : ℝ) : MeasurableSet (oldLeftHeights κ) :=
  (isCompact_Icc.image (by fun_prop)).isClosed.measurableSet

theorem measurableSet_oldRightHeights (κ : ℝ) : MeasurableSet (oldRightHeights κ) :=
  (isCompact_Icc.image (by fun_prop)).isClosed.measurableSet

/-- The heights of the raised right (resp. left) sides: `Λ(1 + S) − πχ` with `S > −2`. -/
theorem measurableSet_raised (Λ b : ℝ) : MeasurableSet {v : ℝ | ∃ S : ℝ, -2 < S ∧ v = Λ * (1 + S) + b} := by
  by_cases hΛ : Λ = 0
  · have e : {v : ℝ | ∃ S : ℝ, -2 < S ∧ v = Λ * (1 + S) + b} = {b} := by
      ext v
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, hΛ, zero_mul, zero_add]
      exact ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨0, by norm_num, h⟩⟩
    rw [e]
    exact measurableSet_singleton b
  · have e : {v : ℝ | ∃ S : ℝ, -2 < S ∧ v = Λ * (1 + S) + b} = {v : ℝ | -2 < (v - b) / Λ - 1} := by
      ext v
      simp only [Set.mem_ofPred_eq]
      constructor
      · rintro ⟨S, hS, rfl⟩
        have : (Λ * (1 + S) + b - b) / Λ - 1 = S := by field_simp; ring
        rw [this]; exact hS
      · intro h
        refine ⟨(v - b) / Λ - 1, h, ?_⟩
        field_simp
        ring
    rw [e]
    exact measurableSet_lt measurable_const (by fun_prop)

/-- **The upper structure as a property of the dilated word.** -/
def NearStructTopW (κ : ℝ) (β : BoundaryWord) : Prop :=
  (∀ y ∈ Ioo (-3 : ℝ) 0, y ∉ β.jumps → β.fn y ∈ oldLeftHeights κ) ∧
    (∀ y ∈ Ioi (0 : ℝ), y ∉ β.jumps → β.fn y ∈ oldRightHeights κ ∪
      {v | ∃ S : ℝ, -2 < S ∧ v = sleLambda (16 / κ) * (1 + S) + -(Real.pi * chiC κ)}) ∧
    lastXL β ≤ -3 ∧ 0 < lastXR β ∧
    (∀ y ∈ Iio (lastXL β), y ∉ β.jumps → β.fn y ∈ ({-sleLambda (16 / κ) + Real.pi * chiC κ} : Set ℝ)) ∧
    ∀ y ∈ Ioi (lastXR β), y ∉ β.jumps → β.fn y ∈ ({sleLambda (16 / κ) - Real.pi * chiC κ} : Set ℝ)

/-- **The lower structure as a property of the dilated word.** -/
def NearStructBotW (κ : ℝ) (β : BoundaryWord) : Prop :=
  (∀ y ∈ Iio (0 : ℝ), y ∉ β.jumps → β.fn y ∈ oldLeftHeights κ ∪
      {v | ∃ S : ℝ, -2 < S ∧ v = -sleLambda (16 / κ) * (1 + S) + Real.pi * chiC κ}) ∧
    (∀ y ∈ Ioo (0 : ℝ) 3, y ∉ β.jumps → β.fn y ∈ oldRightHeights κ) ∧
    lastXL β < 0 ∧ 3 ≤ lastXR β ∧
    (∀ y ∈ Iio (lastXL β), y ∉ β.jumps → β.fn y ∈ ({-sleLambda (16 / κ) + Real.pi * chiC κ} : Set ℝ)) ∧
    ∀ y ∈ Ioi (lastXR β), y ∉ β.jumps → β.fn y ∈ ({sleLambda (16 / κ) - Real.pi * chiC κ} : Set ℝ)

theorem nearStructTop_iff (κ : ℝ) (s : ℝ≥0) (flip : Bool) (c : BoundaryWord) :
    NearStructTop κ s flip c ↔ NearStructTopW κ (nearDilWord s flip c) := by
  constructor
  · intro h
    refine ⟨h.oldL, fun y hy hyJ => ?_, h.xm, h.xp, fun y hy hyJ => h.farL y hy hyJ,
      fun y hy hyJ => h.farR y hy hyJ⟩
    rcases h.right y hy hyJ with h1 | ⟨S, hS, hv⟩
    · exact Or.inl h1
    · exact Or.inr ⟨S, hS, by rw [hv]; ring⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    refine ⟨h1, fun y hy hyJ => ?_, h3, h4, fun y hy hyJ => h5 y hy hyJ, fun y hy hyJ => h6 y hy hyJ⟩
    rcases h2 y hy hyJ with h | ⟨S, hS, hv⟩
    · exact Or.inl h
    · exact Or.inr ⟨S, hS, by rw [hv]; ring⟩

theorem nearStructBot_iff (κ : ℝ) (s : ℝ≥0) (flip : Bool) (c : BoundaryWord) :
    NearStructBot κ s flip c ↔ NearStructBotW κ (nearDilWord s flip c) := by
  constructor
  · intro h
    exact ⟨fun y hy hyJ => h.left y hy hyJ, h.oldR, h.xm, h.xp, fun y hy hyJ => h.farL y hy hyJ,
      fun y hy hyJ => h.farR y hy hyJ⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    exact ⟨fun y hy hyJ => h1 y hy hyJ, h2, h3, h4, fun y hy hyJ => h5 y hy hyJ, fun y hy hyJ => h6 y hy hyJ⟩

theorem measurableSet_nearStructTopW (κ : ℝ) : MeasurableSet {β : BoundaryWord | NearStructTopW κ β} := by
  have hL : ∀ q : ℚ, MeasurableSet {β : BoundaryWord | (q : ℝ) ∈ Iio (lastXL β)} := fun q =>
    measurableSet_lt measurable_const measurable_lastXL
  have hR : ∀ q : ℚ, MeasurableSet {β : BoundaryWord | (q : ℝ) ∈ Ioi (lastXR β)} := fun q =>
    measurableSet_lt measurable_lastXR measurable_const
  simp only [NearStructTopW, Set.ofPred_and]
  exact (measurableSet_offJumps (O := fun _ => Ioo (-3 : ℝ) 0) (fun _ => isOpen_Ioo)
    (fun _ => MeasurableSet.const _) (measurableSet_oldLeftHeights κ)).inter
    ((measurableSet_offJumps (O := fun _ => Ioi (0 : ℝ)) (fun _ => isOpen_Ioi) (fun _ => MeasurableSet.const _)
      ((measurableSet_oldRightHeights κ).union (measurableSet_raised _ _))).inter
    ((measurableSet_le measurable_lastXL measurable_const).inter
    ((measurableSet_lt measurable_const measurable_lastXR).inter
    ((measurableSet_offJumps (fun _ => isOpen_Iio) hL (measurableSet_singleton _)).inter
    (measurableSet_offJumps (fun _ => isOpen_Ioi) hR (measurableSet_singleton _))))))

theorem measurableSet_nearStructBotW (κ : ℝ) : MeasurableSet {β : BoundaryWord | NearStructBotW κ β} := by
  have hL : ∀ q : ℚ, MeasurableSet {β : BoundaryWord | (q : ℝ) ∈ Iio (lastXL β)} := fun q =>
    measurableSet_lt measurable_const measurable_lastXL
  have hR : ∀ q : ℚ, MeasurableSet {β : BoundaryWord | (q : ℝ) ∈ Ioi (lastXR β)} := fun q =>
    measurableSet_lt measurable_lastXR measurable_const
  simp only [NearStructBotW, Set.ofPred_and]
  exact (measurableSet_offJumps (O := fun _ => Iio (0 : ℝ)) (fun _ => isOpen_Iio)
    (fun _ => MeasurableSet.const _) ((measurableSet_oldLeftHeights κ).union (measurableSet_raised _ _))).inter
    ((measurableSet_offJumps (O := fun _ => Ioo (0 : ℝ) 3) (fun _ => isOpen_Ioo) (fun _ => MeasurableSet.const _)
      (measurableSet_oldRightHeights κ)).inter
    ((measurableSet_lt measurable_lastXL measurable_const).inter
    ((measurableSet_le measurable_const measurable_lastXR).inter
    ((measurableSet_offJumps (fun _ => isOpen_Iio) hL (measurableSet_singleton _)).inter
    (measurableSet_offJumps (fun _ => isOpen_Ioi) hR (measurableSet_singleton _))))))

/-! ### The dilated word and the structures in `(s, c)` -/

theorem measurable_dilW : Measurable fun p : ℝ × BoundaryWord => dilW p.1 p.2 := by
  refine (measurable_fst.comp measurable_snd).prodMk (Measurable.prodMk ?_ (measurable_snd.comp
    (measurable_snd.comp measurable_snd)))
  refine measurable_pi_iff.2 fun i => ?_
  exact measurable_fst.mul ((measurable_pi_apply i).comp (measurable_fst.comp (measurable_snd.comp measurable_snd)))

theorem measurable_nearDilWord (flip : Bool) : Measurable fun p : ℝ≥0 × BoundaryWord => nearDilWord p.1 flip p.2 := by
  have hs : Measurable fun p : ℝ≥0 × BoundaryWord => (Real.sqrt (p.1 : ℝ))⁻¹ :=
    (Real.continuous_sqrt.measurable.comp (measurable_coe_nnreal_real.comp measurable_fst)).inv
  cases flip
  · exact measurable_dilW.comp (hs.prodMk measurable_snd)
  · exact measurable_dilW.comp (hs.prodMk (FCPlumb.FCKerD.measurable_sreflWord.comp measurable_snd))

theorem measurableSet_nearStructTop (κ : ℝ) (flip : Bool) :
    MeasurableSet {p : ℝ≥0 × BoundaryWord | NearStructTop κ p.1 flip p.2} := by
  have e : {p : ℝ≥0 × BoundaryWord | NearStructTop κ p.1 flip p.2} =
      (fun p : ℝ≥0 × BoundaryWord => nearDilWord p.1 flip p.2) ⁻¹' {β | NearStructTopW κ β} := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, nearStructTop_iff]
  rw [e]
  exact measurable_nearDilWord flip (measurableSet_nearStructTopW κ)

theorem measurableSet_nearStructBot (κ : ℝ) (flip : Bool) :
    MeasurableSet {p : ℝ≥0 × BoundaryWord | NearStructBot κ p.1 flip p.2} := by
  have e : {p : ℝ≥0 × BoundaryWord | NearStructBot κ p.1 flip p.2} =
      (fun p : ℝ≥0 × BoundaryWord => nearDilWord p.1 flip p.2) ⁻¹' {β | NearStructBotW κ β} := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, nearStructBot_iff]
  rw [e]
  exact measurable_nearDilWord flip (measurableSet_nearStructBotW κ)

/-! ### The far-block counts -/

theorem card_filter_fin_eq_range {n : ℕ} (f : ℕ → ℝ) (P : ℝ → Prop) [DecidablePred P] :
    (univ.filter fun i : Fin n => P (f i)).card = ((Finset.range n).filter fun i => P (f i)).card := by
  rw [Finset.card_filter, Finset.card_filter]
  exact Fin.sum_univ_eq_sum_range (fun i => if P (f i) then 1 else 0) n

/-- The far-block count of the upper family (SDE's `cutL`): the left labels strictly right of `−3`. -/
def cutCountL (β : BoundaryWord) : ℕ :=
  (univ.filter fun i : Fin (flowLineNL β.fn β.jumps 0) => -3 < flowLineXL β.fn β.jumps 0 i).card

/-- The far-block count of the lower family (SDE's `cutR`): the right labels strictly left of `3`. -/
def cutCountR (β : BoundaryWord) : ℕ :=
  (univ.filter fun j : Fin (flowLineNR β.fn β.jumps 0) => flowLineXR β.fn β.jumps 0 j < 3).card

theorem cutCountL_eq (β : BoundaryWord) :
    cutCountL β = ((Finset.range (flowLineNL β.fn β.jumps 0)).filter fun i => -3 < padXL β i).card := by
  rw [cutCountL, ← card_filter_fin_eq_range (padXL β) (fun v => -3 < v)]
  congr 1
  exact Finset.filter_congr fun i _ => by rw [padXL_eq]

theorem cutCountR_eq (β : BoundaryWord) :
    cutCountR β = ((Finset.range (flowLineNR β.fn β.jumps 0)).filter fun j => padXR β j < 3).card := by
  rw [cutCountR, ← card_filter_fin_eq_range (padXR β) (fun v => v < 3)]
  congr 1
  exact Finset.filter_congr fun j _ => by rw [padXR_eq]

theorem measurable_cutCountL : Measurable cutCountL := by
  have e : cutCountL = fun β => ((Finset.range (flowLineNL β.fn β.jumps 0)).filter fun i => -3 < padXL β i).card :=
    funext cutCountL_eq
  rw [e]
  exact measurable_card_range_filter FCDet.measurable_flowLineNL_zero fun i =>
    measurableSet_lt measurable_const ((measurable_pi_apply i).comp measurable_padXL)

theorem measurable_cutCountR : Measurable cutCountR := by
  have e : cutCountR = fun β => ((Finset.range (flowLineNR β.fn β.jumps 0)).filter fun j => padXR β j < 3).card :=
    funext cutCountR_eq
  rw [e]
  exact measurable_card_range_filter FCDet.measurable_flowLineNR_zero fun j =>
    measurableSet_lt ((measurable_pi_apply j).comp measurable_padXR) measurable_const

end InteractingSLE.Theorem14.GW2Bh
