/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualMarg0
import InteractingSLE.Spec.ZhanGT4.DualJointInst
import Mathlib.MeasureTheory.Function.Floor

/-!
# Joint measurability of the patched dual density on the product of the two path spaces

Packet PROVE-ZHAN-GT4-A16. Source: Astra, *Follow-up proofs*, §A.1.4 (`source/external/AstraIG1/
ig1_followup_proofs.txt` L384–L387, R38): "Measurability for a random `I` follows by rounding `I` down to a finite grid
and using continuous dependence of the maps."

* Generic: the staircase functionals (`stairH`, `prevIn`, `maxIn` of random column ends) are measurable; a sum over the
  random set of column ends is a weighted sum over the index set (`sum_stairCols_eq`); and
  **`measurable_comp_of_sepCont`**: a function `f a x y`, measurable in `a` at every fixed grid point below the random
  point `(X a, Y a)` and separately continuous on the random rectangle `[0, X a] × [0, Y a]`, is measurable at the random
  point (rounding down to dyadic grids, first in `x`, then in `y`).
-/

set_option autoImplicit false

noncomputable section

open Finset Set Filter Topology MeasureTheory
open scoped NNReal

namespace InteractingSLE.ZhanGT4

open QuantumZipper (H IsForwardSol fwdMap fwdHull drive)

/-! ### Finite maxima as `ℝ≥0` suprema -/

section Max

/-- `max (S ∪ {0}) = sup_{x ∈ S} x⁺`. -/
theorem max'_insert_zero_eq_coe_sup (S : Finset ℝ) :
    (insert 0 S).max' (insert_nonempty 0 S) = ((S.sup Real.toNNReal : ℝ≥0) : ℝ) := by
  apply le_antisymm
  · refine max'_le _ _ _ fun x hx => ?_
    rcases mem_insert.1 hx with rfl | hx
    · exact NNReal.coe_nonneg _
    · exact (Real.le_coe_toNNReal x).trans (NNReal.coe_le_coe.2 (le_sup (f := Real.toNNReal) hx))
  · have h0 : 0 ≤ (insert 0 S).max' (insert_nonempty 0 S) := le_max' _ _ (mem_insert_self _ _)
    rw [← NNReal.coe_mk _ h0, NNReal.coe_le_coe]
    refine Finset.sup_le fun x hx => ?_
    rw [Real.toNNReal_le_iff_le_coe, NNReal.coe_mk]
    exact le_max' _ _ (mem_insert_of_mem hx)

variable {ι : Type*} [Fintype ι] {α : Type*} [MeasurableSpace α]

/-- The supremum over a filtered index set, as a supremum over all indices (in `ℝ≥0`). -/
theorem sup_filter_eq_sup_ite (P : ι → Prop) [DecidablePred P] (f : ι → ℝ≥0) :
    (univ.filter P).sup f = univ.sup fun j => if P j then f j else 0 := by
  apply le_antisymm
  · refine Finset.sup_le fun j hj => ?_
    have hPj := (mem_filter.1 hj).2
    have h := le_sup (f := fun j => if P j then f j else 0) (mem_univ j)
    simpa only [hPj, ↓reduceIte] using h
  · refine Finset.sup_le fun j _ => ?_
    split_ifs with hPj
    · exact le_sup (f := f) (mem_filter.2 ⟨mem_univ j, hPj⟩)
    · exact zero_le

omit [Fintype ι] in
/-- A finite supremum of measurable `ℝ≥0`-valued functions is measurable. -/
theorem measurable_finset_sup_nnreal {s : Finset ι} {f : ι → α → ℝ≥0} (hf : ∀ j, Measurable (f j)) :
    Measurable fun a => s.sup fun j => f j a := by
  have h : Measurable (s.sup f) :=
    Finset.sup_induction (p := Measurable) measurable_const (fun _ h1 _ h2 => h1.sup h2) fun j _ => hf j
  convert h using 1
  funext a
  rw [Finset.sup_apply]

/-- **The staircase height over a random column is measurable.** -/
theorem measurable_stairH {a b : ι → α → ℝ} (ha : ∀ i, Measurable (a i)) (hb : ∀ i, Measurable (b i)) {c : α → ℝ}
    (hc : Measurable c) : Measurable fun x => stairH (fun i => a i x) (fun i => b i x) (c x) := by
  classical
  have e : (fun x => stairH (fun i => a i x) (fun i => b i x) (c x)) = fun x =>
      ((univ.sup fun j => if c x ≤ a j x then (b j x).toNNReal else 0 : ℝ≥0) : ℝ) := by
    funext x
    unfold stairH
    rw [max'_insert_zero_eq_coe_sup, Finset.sup_image, ← sup_filter_eq_sup_ite]
    rfl
  rw [e]
  refine measurable_coe_nnreal_real.comp (measurable_finset_sup_nnreal fun j => ?_)
  exact Measurable.ite (measurableSet_le hc (ha j)) (hb j).real_toNNReal measurable_const

/-- **The previous column end below a random point is measurable.** -/
theorem measurable_prevIn_stairCols {a : ι → α → ℝ} (ha : ∀ i, Measurable (a i)) {c : α → ℝ} (hc : Measurable c) :
    Measurable fun x => prevIn (stairCols fun i => a i x) (c x) := by
  classical
  have e : (fun x => prevIn (stairCols fun i => a i x) (c x)) = fun x =>
      ((univ.sup fun j => if a j x < c x then (a j x).toNNReal else 0 : ℝ≥0) : ℝ) := by
    funext x
    unfold prevIn stairCols
    rw [max'_insert_zero_eq_coe_sup, Finset.filter_image, Finset.sup_image, ← sup_filter_eq_sup_ite]
    rfl
  rw [e]
  refine measurable_coe_nnreal_real.comp (measurable_finset_sup_nnreal fun j => ?_)
  exact Measurable.ite (measurableSet_lt (ha j) hc) (ha j).real_toNNReal measurable_const

/-- **The largest column end is measurable.** -/
theorem measurable_maxIn_stairCols {a : ι → α → ℝ} (ha : ∀ i, Measurable (a i)) :
    Measurable fun x => maxIn (stairCols fun i => a i x) := by
  have e : (fun x => maxIn (stairCols fun i => a i x)) = fun x =>
      ((univ.sup fun j => (a j x).toNNReal : ℝ≥0) : ℝ) := by
    funext x
    unfold maxIn stairCols
    rw [max'_insert_zero_eq_coe_sup, Finset.sup_image]
    rfl
  rw [e]
  exact measurable_coe_nnreal_real.comp (measurable_finset_sup_nnreal fun j => (ha j).real_toNNReal)

/-- **A sum over the column ends is a weighted sum over the indices.** -/
theorem sum_stairCols_eq (a : ι → ℝ) (g : ℝ → ℝ) :
    ∑ c ∈ stairCols a, g c = ∑ i, g (a i) / ((univ.filter fun j => a j = a i).card : ℝ) := by
  classical
  unfold stairCols
  refine Finset.sum_image' _ fun i _ => ?_
  have hmem : i ∈ univ.filter fun j => a j = a i := mem_filter.2 ⟨mem_univ _, rfl⟩
  have hcard : (0 : ℝ) < ((univ.filter fun j => a j = a i).card : ℝ) := by
    exact_mod_cast Finset.card_pos.2 ⟨i, hmem⟩
  have hc : ∀ j ∈ univ.filter fun j => a j = a i, g (a j) / ((univ.filter fun k => a k = a j).card : ℝ) =
      g (a i) / ((univ.filter fun k => a k = a i).card : ℝ) := fun j hj => by
    rw [(mem_filter.1 hj).2]
  rw [Finset.sum_congr rfl hc, Finset.sum_const, nsmul_eq_mul]
  field_simp

/-- The weights of `sum_stairCols_eq` are measurable. -/
theorem measurable_card_filter_eq {a : ι → α → ℝ} (ha : ∀ i, Measurable (a i)) (i : ι) :
    Measurable fun x => ((univ.filter fun j => a j x = a i x).card : ℝ) := by
  classical
  have e : (fun x => ((univ.filter fun j => a j x = a i x).card : ℝ)) = fun x =>
      ∑ j, if a j x = a i x then (1 : ℝ) else 0 := by
    funext x
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [e]
  exact Finset.measurable_sum _ fun j _ =>
    Measurable.ite (measurableSet_eq_fun (ha j) (ha i)) measurable_const measurable_const

end Max

/-! ### Separately continuous functions at random points -/

section Random

variable {α : Type*} [MeasurableSpace α]

/-- The dyadic rounding down `⌊2^k t⌋₊ / 2^k`. -/
def dyadDown (k : ℕ) (t : ℝ) : ℝ := (⌊(2 : ℝ) ^ k * t⌋₊ : ℝ) / 2 ^ k

theorem dyadDown_nonneg (k : ℕ) (t : ℝ) : 0 ≤ dyadDown k t := by unfold dyadDown; positivity

theorem dyadDown_le {t : ℝ} (ht : 0 ≤ t) (k : ℕ) : dyadDown k t ≤ t := by
  unfold dyadDown
  rw [div_le_iff₀ (by positivity)]
  have := Nat.floor_le (by positivity : 0 ≤ (2 : ℝ) ^ k * t)
  linarith

theorem tendsto_dyadDown {t : ℝ} (ht : 0 ≤ t) : Tendsto (fun k => dyadDown k t) atTop (𝓝 t) := by
  have hlow : ∀ k : ℕ, t - (1 / 2 : ℝ) ^ k ≤ dyadDown k t := fun k => by
    unfold dyadDown
    have h := Nat.lt_floor_add_one ((2 : ℝ) ^ k * t)
    have hp : (0 : ℝ) < 2 ^ k := by positivity
    rw [le_div_iff₀ hp]
    have e : (1 / 2 : ℝ) ^ k * 2 ^ k = 1 := by rw [← mul_pow]; norm_num
    rw [sub_mul, e]
    linarith
  have h0 : Tendsto (fun k : ℕ => t - (1 / 2 : ℝ) ^ k) atTop (𝓝 t) := by
    have := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
    simpa using tendsto_const_nhds.sub this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le h0 tendsto_const_nhds hlow fun k => dyadDown_le ht k

theorem tendsto_dyadDown_within {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun k => dyadDown k t) atTop (𝓝[Icc 0 t] t) :=
  tendsto_nhdsWithin_iff.2 ⟨tendsto_dyadDown ht, Eventually.of_forall fun k => ⟨dyadDown_nonneg k t, dyadDown_le ht k⟩⟩

/-- **A separately continuous function at a random point is measurable** (§A.1.4: "rounding `I` down to a finite
grid and using continuous dependence"). If `f a x y` is measurable in `a` at every fixed point `(x, y)` on the event that
`(x, y)` lies below the random point `(X a, Y a)`, continuous in `x ∈ [0, X a]` for every `y ∈ [0, Y a]` and
continuous in `y ∈ [0, Y a]` at `x = X a`, then `a ↦ f a (X a) (Y a)` is measurable. -/
theorem measurable_comp_of_sepCont {f : α → ℝ → ℝ → ℝ} {X Y : α → ℝ} (hX : Measurable X) (hY : Measurable Y)
    (hX0 : ∀ a, 0 ≤ X a) (hY0 : ∀ a, 0 ≤ Y a)
    (hf : ∀ x y, 0 ≤ x → 0 ≤ y → Measurable ({a | x ≤ X a ∧ y ≤ Y a}.indicator fun a => f a x y))
    (hcx : ∀ a, ∀ y ∈ Icc 0 (Y a), ContinuousOn (fun x => f a x y) (Icc 0 (X a)))
    (hcy : ∀ a, ContinuousOn (fun y => f a (X a) y) (Icc 0 (Y a))) :
    Measurable fun a => f a (X a) (Y a) := by
  have hgrid : ∀ k l : ℕ, Measurable fun a => f a (dyadDown k (X a)) (dyadDown l (Y a)) := by
    intro k l
    set F : α × (ℕ × ℕ) → ℝ := fun q => {a | (q.2.1 : ℝ) / 2 ^ k ≤ X a ∧ (q.2.2 : ℝ) / 2 ^ l ≤ Y a}.indicator
      (fun a => f a ((q.2.1 : ℝ) / 2 ^ k) ((q.2.2 : ℝ) / 2 ^ l)) q.1 with hFdef
    have hF : Measurable F := measurable_from_prod_countable_left fun nm =>
      hf ((nm.1 : ℝ) / 2 ^ k) ((nm.2 : ℝ) / 2 ^ l) (by positivity) (by positivity)
    have hN : Measurable fun a => (a, (⌊(2 : ℝ) ^ k * X a⌋₊, ⌊(2 : ℝ) ^ l * Y a⌋₊)) :=
      measurable_id.prodMk ((measurable_const.mul hX).nat_floor.prodMk (measurable_const.mul hY).nat_floor)
    convert hF.comp hN using 1
    funext a
    simp only [Function.comp_apply, hFdef]
    rw [Set.indicator_of_mem]
    · rfl
    · exact ⟨dyadDown_le (hX0 a) k, dyadDown_le (hY0 a) l⟩
  have hrow : ∀ l : ℕ, Measurable fun a => f a (X a) (dyadDown l (Y a)) := fun l =>
    measurable_of_tendsto_metrizable (fun k => hgrid k l) (tendsto_pi_nhds.2 fun a => by
      have hy : dyadDown l (Y a) ∈ Icc 0 (Y a) := ⟨dyadDown_nonneg _ _, dyadDown_le (hY0 a) l⟩
      exact ((hcx a _ hy) (X a) ⟨hX0 a, le_rfl⟩).tendsto.comp (tendsto_dyadDown_within (hX0 a)))
  exact measurable_of_tendsto_metrizable hrow (tendsto_pi_nhds.2 fun a =>
    ((hcy a) (Y a) ⟨hY0 a, le_rfl⟩).tendsto.comp (tendsto_dyadDown_within (hY0 a)))

end Random

/-! ### Continuity in the own time of curve `1` on a rectangle -/

namespace TwoEncl

variable {ι : Type*} [Fintype ι] {n : ℕ} {W₁ W₂ : ℝ → ℝ} {S₁ S₂ : ι → ℝ} {H₁ H₂ : ι → Set ℂ} {δ q d : ι → ℝ}
  {p : Fin n → ℝ} {Tm : ℝ} (h : TwoEncl W₁ W₂ S₁ S₂ H₁ H₂ δ q d p Tm)
include h

/-- **The `s`-view data at a height of rectangle `i`, on the full staircase width**: the frozen tip and the marks are
alive for the image chain up to the end of the width (the rectangle attaining the width supplies the marks). -/
theorem sView_encl_full (i : ι) {y : ℝ} (hy : y ∈ Icc (0 : ℝ) (S₂ i)) :
    S₁ i ≤ stairH S₂ S₁ y ∧
      OwnData W₁ (fwdHull W₂ y) (frzChart W₂ y) (stairH S₂ S₁ y) (sSelA W₁ W₂ S₁ S₂ y) (sSelW W₁ W₂ S₁ S₂ y) ∧
      (∃ x, IsForwardSol (sSelW W₁ W₂ S₁ S₂ y) ((W₂ y : ℝ) : ℂ) (sSelA W₁ W₂ S₁ S₂ y (stairH S₂ S₁ y)) x) ∧
      ∀ m, ∃ x, IsForwardSol (sSelW W₁ W₂ S₁ S₂ y) ((frzMarks W₂ p y m : ℝ) : ℂ)
        (sSelA W₁ W₂ S₁ S₂ y (stairH S₂ S₁ y)) x := by
  obtain ⟨j, hyj, hwj⟩ := exists_eq_stairH (S₁ := S₂) (S₂ := S₁) (fun j => (h.S₁pos j).le) hy.2
  obtain ⟨hw, hown, htip, -⟩ := h.sView_encl i hy
  obtain ⟨-, -, -, hmk⟩ := h.sView_encl j ⟨hy.1, hyj⟩
  exact ⟨hw, hown, htip, fun m => hmk (stairH S₂ S₁ y) ⟨stairH_nonneg _, hwj.le⟩ m⟩

/-- **The `s`-view `ℓ` is continuous in the own time of curve `1`** on every rectangle, at every height of it. -/
theorem continuousOn_sEll_own {κ : ℝ} (r : Fin n → ℝ) (i : ι) {y : ℝ} (hy : y ∈ Icc (0 : ℝ) (S₂ i)) :
    ContinuousOn (fun x => sEll κ r W₁ W₂ (sSelA W₁ W₂ S₁ S₂) (sSelW W₁ W₂ S₁ S₂) p x y) (Icc 0 (S₁ i)) := by
  obtain ⟨hw, hown, ⟨v₀, hv₀⟩, hmk⟩ := h.sView_encl_full i hy
  choose v hv using hmk
  have hal : ∀ m, ∃ w, IsForwardSol W₂ ((p m : ℝ) : ℂ) (S₂ i) w := (h.twoViewMarks i).alive₂
  have hne : ∀ m, frzMarks W₂ p y m ≠ W₂ y := fun m => by
    obtain ⟨w, hw'⟩ := hal m
    exact frzMarks_ne_of_isForwardSol h.cont₂ hw' hy
  have hinj : Function.Injective (frzMarks W₂ p y) := frzMarks_injective_of_isForwardSol h.cont₂ h.pinj hal hy
  have hc := (sView κ r W₁ W₂ (sSelA W₁ W₂ S₁ S₂) (sSelW W₁ W₂ S₁ S₂) p y).continuousOn_ell_driver hown hv₀ hv
    hne hinj
  exact hc.mono (Icc_subset_Icc_right hw)

/-- **The `s`-view normalised density is continuous in the own time of curve `1`** on every rectangle. -/
theorem continuousOn_normLog_sEll_own {κ : ℝ} (r : Fin n → ℝ) (i : ι) {y : ℝ} (hy : y ∈ Icc (0 : ℝ) (S₂ i)) :
    ContinuousOn (fun x => normLog (sEll κ r W₁ W₂ (sSelA W₁ W₂ S₁ S₂) (sSelW W₁ W₂ S₁ S₂) p) x y)
      (Icc 0 (S₁ i)) := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) (S₂ i) := ⟨le_rfl, (h.S₂pos i).le⟩
  unfold normLog
  exact (((h.continuousOn_sEll_own r i hy).sub (h.continuousOn_sEll_own r i h0)).sub continuousOn_const).add
    continuousOn_const

end TwoEncl

/-! ### The `s`-view facts at one height -/

section ViewAt

variable {ι : Type*} [Fintype ι] {n : ℕ} {W₁ W₂ : ℝ → ℝ} {S₁ S₂ : ι → ℝ} {p : Fin n → ℝ} {y : ℝ}

/-- **The `s`-view facts at one height `y`**: the frozen curve is continuous with injective marks alive at `y`, and the
canonical image data on the full staircase width exist with the frozen tip and the marks alive for the image chain. -/
structure SViewAt (W₁ W₂ : ℝ → ℝ) (S₁ S₂ : ι → ℝ) (p : Fin n → ℝ) (y : ℝ) : Prop where
  nonneg : 0 ≤ y
  cont₂ : Continuous W₂
  pinj : Function.Injective p
  alive₂ : ∀ m, ∃ w, IsForwardSol W₂ ((p m : ℝ) : ℂ) y w
  own : OwnData W₁ (fwdHull W₂ y) (frzChart W₂ y) (stairH S₂ S₁ y) (sSelA W₁ W₂ S₁ S₂ y) (sSelW W₁ W₂ S₁ S₂ y)
  tip : ∃ x, IsForwardSol (sSelW W₁ W₂ S₁ S₂ y) ((W₂ y : ℝ) : ℂ) (sSelA W₁ W₂ S₁ S₂ y (stairH S₂ S₁ y)) x
  marks : ∀ m, ∃ x, IsForwardSol (sSelW W₁ W₂ S₁ S₂ y) ((frzMarks W₂ p y m : ℝ) : ℂ)
    (sSelA W₁ W₂ S₁ S₂ y (stairH S₂ S₁ y)) x

/-- **The `s`-view `ℓ` at a height is continuous in the own time** on the whole staircase width. -/
theorem SViewAt.continuousOn_sEll (h : SViewAt W₁ W₂ S₁ S₂ p y) {κ : ℝ} (r : Fin n → ℝ) :
    ContinuousOn (fun x => sEll κ r W₁ W₂ (sSelA W₁ W₂ S₁ S₂) (sSelW W₁ W₂ S₁ S₂) p x y)
      (Icc 0 (stairH S₂ S₁ y)) := by
  obtain ⟨v₀, hv₀⟩ := h.tip
  choose v hv using h.marks
  have hne : ∀ m, frzMarks W₂ p y m ≠ W₂ y := fun m => by
    obtain ⟨w, hw⟩ := h.alive₂ m
    exact frzMarks_ne_of_isForwardSol h.cont₂ hw ⟨h.nonneg, le_rfl⟩
  have hinj := frzMarks_injective_of_isForwardSol h.cont₂ h.pinj h.alive₂ ⟨h.nonneg, le_rfl⟩
  exact (sView κ r W₁ W₂ (sSelA W₁ W₂ S₁ S₂) (sSelW W₁ W₂ S₁ S₂) p y).continuousOn_ell_driver h.own hv₀ hv hne hinj

variable {H₁ H₂ : ι → Set ℂ} {δ q d : ι → ℝ} {Tm : ℝ}

/-- Protected enclosures give the `s`-view facts at every height of a rectangle. -/
theorem TwoEncl.sViewAt (h : TwoEncl W₁ W₂ S₁ S₂ H₁ H₂ δ q d p Tm) (i : ι) (hy : y ∈ Icc (0 : ℝ) (S₂ i)) :
    SViewAt W₁ W₂ S₁ S₂ p y := by
  obtain ⟨-, hown, htip, hmk⟩ := h.sView_encl_full i hy
  exact ⟨hy.1, h.cont₂, h.pinj, fun m => by
    obtain ⟨w, hw⟩ := (h.twoViewMarks i).alive₂ m
    exact ⟨w, Ito.isForwardSol_of_le hw hy.1 hy.2⟩, hown, htip, hmk⟩

/-- **The `t`-view at curve-`1` height `0` as an `s`-view of the swapped, translated pair** (curve `2` − `c` grows,
curve `1` − `c` is frozen at height `0`, marks `p − c`; `c = W₂ 0`): protected enclosures give its facts (A15's
`tView_encl`, the rectangle attaining the width supplying the marks). -/
theorem TwoEncl.tViewAt_zero (h : TwoEncl W₁ W₂ S₁ S₂ H₁ H₂ δ q d p Tm) (i : ι) :
    SViewAt (fun s => W₂ s - W₂ 0) (fun s => W₁ s - W₂ 0) S₂ S₁ (fun m => p m - W₂ 0) 0 := by
  have hi : (0 : ℝ) ∈ Icc (0 : ℝ) (S₁ i) := ⟨le_rfl, (h.S₁pos i).le⟩
  obtain ⟨j, hj, hwj⟩ := exists_eq_stairH (S₁ := S₁) (S₂ := S₂) (fun j => (h.S₂pos j).le) hi.2
  obtain ⟨-, hown, htip, -⟩ := h.tView_encl i hi
  obtain ⟨-, -, -, hmk⟩ := h.tView_encl j ⟨le_rfl, hj⟩
  refine ⟨le_rfl, h.cont₁.sub continuous_const, fun m k hmk' => h.pinj (by simpa using hmk'), fun m => ?_, hown,
    htip, fun m => ?_⟩
  · obtain ⟨w, hw⟩ := (h.twoViewMarks i).alive₁ m
    exact ⟨w, isForwardSol_sub_const_iff.2 (Ito.isForwardSol_of_le hw le_rfl hi.2)⟩
  · have := hmk (stairH S₁ S₂ 0) ⟨stairH_nonneg _, hwj.le⟩ m
    exact this

/-- The `t`-view facts at height `0` for a curve `2` given as a translate `V + c` (`V 0 = 0`). -/
theorem TwoEncl.tViewAt_zero' (h : TwoEncl W₁ W₂ S₁ S₂ H₁ H₂ δ q d p Tm) (i : ι) {V : ℝ → ℝ} {c : ℝ}
    (hc : W₂ 0 = c) (hV : ∀ s, W₂ s - c = V s) :
    SViewAt V (fun s => W₁ s - c) S₂ S₁ (fun m => p m - c) 0 := by
  obtain rfl : c = W₂ 0 := hc.symm
  obtain rfl : V = fun s => W₂ s - W₂ 0 := (funext hV).symm
  exact h.tViewAt_zero i

end ViewAt

/-! ### The `s`-view `ℓ` on the product of the two path spaces -/

section PairGen

variable {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] {ι : Type*} [Fintype ι] {n : ℕ}

/-- **The canonical `s`-view `ℓ` along a pair of paths**: curve `1` = `√κ B(ω₁)`, curve `2` = `V(ω₂)`, column ends
`S₁ i ω₁`, heights `S₂ i ω₂`. -/
def pairEll (κ : ℝ) (rr p : Fin n → ℝ) (B : ℝ≥0 → Ω₁ → ℝ) (V : Ω₂ → ℝ → ℝ) (S₁ : ι → Ω₁ → ℝ)
    (S₂ : ι → Ω₂ → ℝ) (ω : Ω₁ × Ω₂) (x y : ℝ) : ℝ :=
  sEll κ rr (drive κ B ω.1) (V ω.2) (sSelA (drive κ B ω.1) (V ω.2) (fun i => S₁ i ω.1) (fun i => S₂ i ω.2))
    (sSelW (drive κ B ω.1) (V ω.2) (fun i => S₁ i ω.1) (fun i => S₂ i ω.2)) p x y

/-- **`ℓ(x, y)` at a fixed point is measurable on the product** on a measurable event on which the `s`-view facts hold
at height `y` and `x` is within the staircase width (A13's `measurable_ell_pair` for the canonical image data). -/
theorem measurable_pairEll_indicator_of {κ : ℝ} {B : ℝ≥0 → Ω₁ → ℝ} (hBc : ∀ ω, Continuous fun r => B r ω)
    (hBm : ∀ r : ℝ≥0, Measurable (B r)) {V : Ω₂ → ℝ → ℝ} (hVc : ∀ ω, Continuous (V ω)) {y : ℝ} (hy : 0 ≤ y)
    (hVhit : ∀ L : Set ℂ, IsCompact L → L ⊆ H → MeasurableSet {ω | (L ∩ fwdHull (V ω) y).Nonempty})
    (hVfwd : ∀ z ∈ H, Measurable fun ω => fwdMap (V ω) y z) (hVt : Measurable fun ω => V ω y)
    {S₁ : ι → Ω₁ → ℝ} {S₂ : ι → Ω₂ → ℝ} (rr p : Fin n → ℝ) {G : Set (Ω₁ × Ω₂)} (hG : MeasurableSet G) {x : ℝ}
    (hx : 0 ≤ x) (hS : ∀ ω ∈ G, SViewAt (drive κ B ω.1) (V ω.2) (fun i => S₁ i ω.1) (fun i => S₂ i ω.2) p y)
    (hmem : ∀ ω ∈ G, x ≤ stairH (fun i => S₂ i ω.2) (fun i => S₁ i ω.1) y) :
    Measurable (G.indicator fun ω => pairEll κ rr p B V S₁ S₂ ω x y) :=
  measurable_ell_pair (κ := κ) (B := B) hBc hx (fun r _ => hBm r) hVhit hVfwd hVt hVc hy rr p
    (W' := fun ω => sSelW (drive κ B ω.1) (V ω.2) (fun i => S₁ i ω.1) (fun i => S₂ i ω.2) y)
    (a := fun ω => sSelA (drive κ B ω.1) (V ω.2) (fun i => S₁ i ω.1) (fun i => S₂ i ω.2) y)
    (T := fun ω => stairH (fun i => S₂ i ω.2) (fun i => S₁ i ω.1) y) hG
    (fun ω hω => (hS ω hω).own) (fun ω hω => ⟨hx, hmem ω hω⟩) (fun ω hω m => (hS ω hω).alive₂ m)
    (fun ω hω => (hS ω hω).tip) (fun m ω hω => (hS ω hω).marks m)

/-- **The marginal exponent `ℓ(X, 0) − ℓ(0, 0)` at a random point within the width at height `0` is measurable on the
product**, given the `s`-view facts at height `0` everywhere. -/
theorem measurable_pairEll_marg_of {κ : ℝ} {B : ℝ≥0 → Ω₁ → ℝ} (hBc : ∀ ω, Continuous fun r => B r ω)
    (hBm : ∀ r : ℝ≥0, Measurable (B r)) {V : Ω₂ → ℝ → ℝ} (hVc : ∀ ω, Continuous (V ω))
    (hVhit : ∀ L : Set ℂ, IsCompact L → L ⊆ H → MeasurableSet {ω | (L ∩ fwdHull (V ω) 0).Nonempty})
    (hVfwd : ∀ z ∈ H, Measurable fun ω => fwdMap (V ω) 0 z) (hVt : Measurable fun ω => V ω 0)
    {S₁ : ι → Ω₁ → ℝ} {S₂ : ι → Ω₂ → ℝ} (hS₁ : ∀ i, Measurable (S₁ i)) (hS₂ : ∀ i, Measurable (S₂ i))
    (rr p : Fin n → ℝ) {X : Ω₁ × Ω₂ → ℝ} (hX : Measurable X) (hX0 : ∀ ω, 0 ≤ X ω)
    (hS0 : ∀ ω : Ω₁ × Ω₂, SViewAt (drive κ B ω.1) (V ω.2) (fun i => S₁ i ω.1) (fun i => S₂ i ω.2) p 0)
    (hXS : ∀ ω, X ω ≤ stairH (fun i => S₂ i ω.2) (fun i => S₁ i ω.1) 0) :
    Measurable fun ω => pairEll κ rr p B V S₁ S₂ ω (X ω) 0 - pairEll κ rr p B V S₁ S₂ ω 0 0 := by
  have hW : Measurable fun ω : Ω₁ × Ω₂ => stairH (fun i => S₂ i ω.2) (fun i => S₁ i ω.1) 0 :=
    measurable_stairH (fun i => (hS₂ i).comp measurable_snd) (fun i => (hS₁ i).comp measurable_fst) measurable_const
  have hL : ∀ x, 0 ≤ x → Measurable ({ω : Ω₁ × Ω₂ | x ≤ stairH (fun i => S₂ i ω.2) (fun i => S₁ i ω.1) 0}.indicator
      fun ω => pairEll κ rr p B V S₁ S₂ ω x 0) := fun x hx =>
    measurable_pairEll_indicator_of hBc hBm hVc le_rfl hVhit hVfwd hVt rr p (measurableSet_le measurable_const hW) hx
      (fun ω _ => hS0 ω) fun ω hω => hω
  have hY : Measurable fun _ : Ω₁ × Ω₂ => (0 : ℝ) := measurable_const
  have h := measurable_comp_of_sepCont (f := fun ω x _ => pairEll κ rr p B V S₁ S₂ ω x 0 -
      pairEll κ rr p B V S₁ S₂ ω 0 0) hX hY hX0 (fun _ => le_rfl) (fun x y hx hy => ?_) (fun ω y _ => ?_)
    (fun ω => continuousOn_const)
  · exact h
  · have hEm : MeasurableSet {ω : Ω₁ × Ω₂ | x ≤ X ω ∧ y ≤ (fun _ : Ω₁ × Ω₂ => (0 : ℝ)) ω} :=
      (measurableSet_le measurable_const hX).inter (measurableSet_le measurable_const hY)
    have e : {ω : Ω₁ × Ω₂ | x ≤ X ω ∧ y ≤ (fun _ : Ω₁ × Ω₂ => (0 : ℝ)) ω}.indicator
        (fun ω => pairEll κ rr p B V S₁ S₂ ω x 0 - pairEll κ rr p B V S₁ S₂ ω 0 0) = fun ω =>
        {ω : Ω₁ × Ω₂ | x ≤ X ω ∧ y ≤ (fun _ : Ω₁ × Ω₂ => (0 : ℝ)) ω}.indicator
          ({ω : Ω₁ × Ω₂ | x ≤ stairH (fun i => S₂ i ω.2) (fun i => S₁ i ω.1) 0}.indicator
            fun ω => pairEll κ rr p B V S₁ S₂ ω x 0) ω -
        {ω : Ω₁ × Ω₂ | x ≤ X ω ∧ y ≤ (fun _ : Ω₁ × Ω₂ => (0 : ℝ)) ω}.indicator
          ({ω : Ω₁ × Ω₂ | 0 ≤ stairH (fun i => S₂ i ω.2) (fun i => S₁ i ω.1) 0}.indicator
            fun ω => pairEll κ rr p B V S₁ S₂ ω 0 0) ω := by
      funext ω
      by_cases hω : ω ∈ {ω : Ω₁ × Ω₂ | x ≤ X ω ∧ y ≤ (fun _ : Ω₁ × Ω₂ => (0 : ℝ)) ω}
      · have h1 : ω ∈ {ω : Ω₁ × Ω₂ | x ≤ stairH (fun i => S₂ i ω.2) (fun i => S₁ i ω.1) 0} :=
          hω.1.trans (hXS ω)
        have h2 : ω ∈ {ω : Ω₁ × Ω₂ | 0 ≤ stairH (fun i => S₂ i ω.2) (fun i => S₁ i ω.1) 0} := stairH_nonneg _
        rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω, Set.indicator_of_mem hω, Set.indicator_of_mem h1,
          Set.indicator_of_mem h2]
      · simp only [Set.indicator_of_notMem hω]; ring
    rw [e]
    exact ((hL x hx).indicator hEm).sub ((hL 0 le_rfl).indicator hEm)
  · exact (((hS0 ω).continuousOn_sEll rr).sub continuousOn_const).mono (Icc_subset_Icc_right (hXS ω))

end PairGen

section Pair

variable {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] {ι : Type*} [Fintype ι] {n : ℕ}

variable {κ : ℝ} {B : ℝ≥0 → Ω₁ → ℝ} (hBc : ∀ ω, Continuous fun r => B r ω) (hBm : ∀ r : ℝ≥0, Measurable (B r))
  {V : Ω₂ → ℝ → ℝ} (hVc : ∀ ω, Continuous (V ω))
  (hVhit : ∀ t, 0 ≤ t → ∀ L : Set ℂ, IsCompact L → L ⊆ H → MeasurableSet {ω | (L ∩ fwdHull (V ω) t).Nonempty})
  (hVfwd : ∀ t, 0 ≤ t → ∀ z ∈ H, Measurable fun ω => fwdMap (V ω) t z) (hVt : ∀ t, Measurable fun ω => V ω t)
  {S₁ : ι → Ω₁ → ℝ} {S₂ : ι → Ω₂ → ℝ} (hS₁ : ∀ i, Measurable (S₁ i)) (hS₂ : ∀ i, Measurable (S₂ i))
  {H₁ H₂ : ι → Set ℂ} {δ q d : ι → ℝ} {p : Fin n → ℝ} {Tm : ℝ}
  (hE : ∀ ω : Ω₁ × Ω₂, TwoEncl (drive κ B ω.1) (V ω.2) (fun i => S₁ i ω.1) (fun i => S₂ i ω.2) H₁ H₂ δ q d p Tm)

include hS₁ hS₂ in
theorem measurableSet_inStair_pair (x y : ℝ) :
    MeasurableSet {ω : Ω₁ × Ω₂ | ∃ i, x ≤ S₁ i ω.1 ∧ y ≤ S₂ i ω.2} := by
  simp only [Set.ofPred_exists, Set.ofPred_and]
  exact MeasurableSet.iUnion fun i => (measurableSet_le measurable_const ((hS₁ i).comp measurable_fst)).inter
    (measurableSet_le measurable_const ((hS₂ i).comp measurable_snd))

include hBc hBm hVc hVhit hVfwd hVt hS₁ hS₂ hE in
/-- **`ℓ(x, y)` at a fixed point is measurable on the product**, on the event that `(x, y)` lies under the staircase
(A13's `measurable_ell_pair` for the canonical image data). -/
theorem measurable_pairEll_indicator (rr : Fin n → ℝ) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Measurable ({ω : Ω₁ × Ω₂ | ∃ i, x ≤ S₁ i ω.1 ∧ y ≤ S₂ i ω.2}.indicator
      fun ω => pairEll κ rr p B V S₁ S₂ ω x y) := by
  have hG := measurableSet_inStair_pair hS₁ hS₂ x y
  have hfull : ∀ ω ∈ {ω : Ω₁ × Ω₂ | ∃ i, x ≤ S₁ i ω.1 ∧ y ≤ S₂ i ω.2}, ∃ i, x ≤ S₁ i ω.1 ∧ y ≤ S₂ i ω.2 ∧
      _ := fun ω hω => by
    obtain ⟨i, hxi, hyi⟩ := hω
    exact ⟨i, hxi, hyi, (hE ω).sView_encl_full i ⟨hy, hyi⟩⟩
  exact measurable_ell_pair (κ := κ) (B := B) hBc hx (fun r _ => hBm r) (hVhit y hy) (hVfwd y hy) (hVt y) hVc hy rr
    p (W' := fun ω => sSelW (drive κ B ω.1) (V ω.2) (fun i => S₁ i ω.1) (fun i => S₂ i ω.2) y)
    (a := fun ω => sSelA (drive κ B ω.1) (V ω.2) (fun i => S₁ i ω.1) (fun i => S₂ i ω.2) y)
    (T := fun ω => stairH (fun i => S₂ i ω.2) (fun i => S₁ i ω.1) y) hG
    (fun ω hω => by obtain ⟨i, -, -, hf⟩ := hfull ω hω; exact hf.2.1)
    (fun ω hω => by obtain ⟨i, hxi, -, hf⟩ := hfull ω hω; exact ⟨hx, hxi.trans hf.1⟩)
    (fun ω hω m => by
      obtain ⟨i, -, hyi, -⟩ := hfull ω hω
      obtain ⟨w, hw⟩ := ((hE ω).twoViewMarks i).alive₂ m
      exact ⟨w, Ito.isForwardSol_of_le hw hy hyi⟩)
    (fun ω hω => by obtain ⟨i, -, -, hf⟩ := hfull ω hω; exact hf.2.2.1)
    (fun m ω hω => by obtain ⟨i, -, -, hf⟩ := hfull ω hω; exact hf.2.2.2 m)

include hBc hBm hVc hVhit hVfwd hVt hS₁ hS₂ hE in
/-- **The normalised density at a random point under the staircase is measurable on the product** (dyadic rounding,
`measurable_comp_of_sepCont`, with the separate continuity of the canonical `s`-view normalised density). -/
theorem measurable_pairNormLog (hκ : κ ≠ 0) (rr : Fin n → ℝ) {X Y : Ω₁ × Ω₂ → ℝ} (hX : Measurable X)
    (hY : Measurable Y) (hX0 : ∀ ω, 0 ≤ X ω) (hY0 : ∀ ω, 0 ≤ Y ω)
    (hXY : ∀ ω, ∃ i, X ω ≤ S₁ i ω.1 ∧ Y ω ≤ S₂ i ω.2) :
    Measurable fun ω => normLog (pairEll κ rr p B V S₁ S₂ ω) (X ω) (Y ω) := by
  have hL := fun x y (hx : 0 ≤ x) (hy : 0 ≤ y) =>
    measurable_pairEll_indicator hBc hBm hVc hVhit hVfwd hVt hS₁ hS₂ hE (p := p) rr hx hy
  refine measurable_comp_of_sepCont hX hY hX0 hY0 (fun x y hx hy => ?_) (fun ω y hy => ?_) (fun ω => ?_)
  · have hEm : MeasurableSet {ω : Ω₁ × Ω₂ | x ≤ X ω ∧ y ≤ Y ω} :=
      (measurableSet_le measurable_const hX).inter (measurableSet_le measurable_const hY)
    have hEG : ∀ ω ∈ {ω : Ω₁ × Ω₂ | x ≤ X ω ∧ y ≤ Y ω}, ∀ x' y' : ℝ, x' ≤ x → y' ≤ y →
        ω ∈ {ω : Ω₁ × Ω₂ | ∃ i, x' ≤ S₁ i ω.1 ∧ y' ≤ S₂ i ω.2} := fun ω hω x' y' hx' hy' => by
      obtain ⟨i, hXi, hYi⟩ := hXY ω
      exact ⟨i, hx'.trans (hω.1.trans hXi), hy'.trans (hω.2.trans hYi)⟩
    have e : {ω : Ω₁ × Ω₂ | x ≤ X ω ∧ y ≤ Y ω}.indicator (fun ω => normLog (pairEll κ rr p B V S₁ S₂ ω) x y) =
        fun ω => {ω : Ω₁ × Ω₂ | x ≤ X ω ∧ y ≤ Y ω}.indicator ({ω : Ω₁ × Ω₂ | ∃ i, x ≤ S₁ i ω.1 ∧ y ≤ S₂ i ω.2}.indicator
          fun ω => pairEll κ rr p B V S₁ S₂ ω x y) ω -
        {ω : Ω₁ × Ω₂ | x ≤ X ω ∧ y ≤ Y ω}.indicator ({ω : Ω₁ × Ω₂ | ∃ i, x ≤ S₁ i ω.1 ∧ 0 ≤ S₂ i ω.2}.indicator
          fun ω => pairEll κ rr p B V S₁ S₂ ω x 0) ω -
        {ω : Ω₁ × Ω₂ | x ≤ X ω ∧ y ≤ Y ω}.indicator ({ω : Ω₁ × Ω₂ | ∃ i, 0 ≤ S₁ i ω.1 ∧ y ≤ S₂ i ω.2}.indicator
          fun ω => pairEll κ rr p B V S₁ S₂ ω 0 y) ω +
        {ω : Ω₁ × Ω₂ | x ≤ X ω ∧ y ≤ Y ω}.indicator ({ω : Ω₁ × Ω₂ | ∃ i, 0 ≤ S₁ i ω.1 ∧ 0 ≤ S₂ i ω.2}.indicator
          fun ω => pairEll κ rr p B V S₁ S₂ ω 0 0) ω := by
      funext ω
      by_cases hω : ω ∈ {ω : Ω₁ × Ω₂ | x ≤ X ω ∧ y ≤ Y ω}
      · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω, Set.indicator_of_mem hω, Set.indicator_of_mem hω,
          Set.indicator_of_mem hω, Set.indicator_of_mem (hEG ω hω x y le_rfl le_rfl),
          Set.indicator_of_mem (hEG ω hω x 0 le_rfl hy), Set.indicator_of_mem (hEG ω hω 0 y hx le_rfl),
          Set.indicator_of_mem (hEG ω hω 0 0 hx hy)]
        rfl
      · simp only [Set.indicator_of_notMem hω]; ring
    rw [e]
    exact ((((hL x y hx hy).indicator hEm).sub ((hL x 0 hx le_rfl).indicator hEm)).sub
      ((hL 0 y le_rfl hy).indicator hEm)).add ((hL 0 0 le_rfl le_rfl).indicator hEm)
  · obtain ⟨i, hXi, hYi⟩ := hXY ω
    exact ((hE ω).continuousOn_normLog_sEll_own rr i ⟨hy.1, hy.2.trans hYi⟩).mono (Icc_subset_Icc_right hXi)
  · obtain ⟨i, hXi, hYi⟩ := hXY ω
    exact ((hE ω).continuousOn_normLog_sEll_height hκ rr i ⟨hX0 ω, hXi⟩).mono (Icc_subset_Icc_right hYi)

include hBc hBm hVc hVhit hVfwd hVt hS₁ hS₂ hE in
/-- **The curve-`1` marginal exponent `ℓ(X, 0) − ℓ(0, 0)` at a random column point is measurable on the product.** -/
theorem measurable_pairEll_marg (rr : Fin n → ℝ) {X : Ω₁ × Ω₂ → ℝ} (hX : Measurable X) (hX0 : ∀ ω, 0 ≤ X ω)
    (hXS : ∀ ω, ∃ i, X ω ≤ S₁ i ω.1) :
    Measurable fun ω => pairEll κ rr p B V S₁ S₂ ω (X ω) 0 - pairEll κ rr p B V S₁ S₂ ω 0 0 := by
  have hL := fun x y (hx : 0 ≤ x) (hy : 0 ≤ y) =>
    measurable_pairEll_indicator hBc hBm hVc hVhit hVfwd hVt hS₁ hS₂ hE (p := p) rr hx hy
  have hY : Measurable fun _ : Ω₁ × Ω₂ => (0 : ℝ) := measurable_const
  have h := measurable_comp_of_sepCont (f := fun ω x _ => pairEll κ rr p B V S₁ S₂ ω x 0 -
      pairEll κ rr p B V S₁ S₂ ω 0 0) hX hY hX0 (fun _ => le_rfl) (fun x y hx hy => ?_) (fun ω y _ => ?_)
    (fun ω => continuousOn_const)
  · exact h
  · have hEm : MeasurableSet {ω : Ω₁ × Ω₂ | x ≤ X ω ∧ y ≤ (fun _ : Ω₁ × Ω₂ => (0 : ℝ)) ω} :=
      (measurableSet_le measurable_const hX).inter (measurableSet_le measurable_const hY)
    have hEG : ∀ ω ∈ {ω : Ω₁ × Ω₂ | x ≤ X ω ∧ y ≤ (fun _ : Ω₁ × Ω₂ => (0 : ℝ)) ω}, ∀ x' : ℝ, x' ≤ x →
        ω ∈ {ω : Ω₁ × Ω₂ | ∃ i, x' ≤ S₁ i ω.1 ∧ 0 ≤ S₂ i ω.2} := fun ω hω x' hx' => by
      obtain ⟨i, hXi⟩ := hXS ω
      exact ⟨i, hx'.trans (hω.1.trans hXi), ((hE ω).S₂pos i).le⟩
    have e : {ω : Ω₁ × Ω₂ | x ≤ X ω ∧ y ≤ (fun _ : Ω₁ × Ω₂ => (0 : ℝ)) ω}.indicator
        (fun ω => pairEll κ rr p B V S₁ S₂ ω x 0 - pairEll κ rr p B V S₁ S₂ ω 0 0) = fun ω =>
        {ω : Ω₁ × Ω₂ | x ≤ X ω ∧ y ≤ (fun _ : Ω₁ × Ω₂ => (0 : ℝ)) ω}.indicator
          ({ω : Ω₁ × Ω₂ | ∃ i, x ≤ S₁ i ω.1 ∧ 0 ≤ S₂ i ω.2}.indicator fun ω => pairEll κ rr p B V S₁ S₂ ω x 0) ω -
        {ω : Ω₁ × Ω₂ | x ≤ X ω ∧ y ≤ (fun _ : Ω₁ × Ω₂ => (0 : ℝ)) ω}.indicator
          ({ω : Ω₁ × Ω₂ | ∃ i, 0 ≤ S₁ i ω.1 ∧ 0 ≤ S₂ i ω.2}.indicator fun ω => pairEll κ rr p B V S₁ S₂ ω 0 0) ω := by
      funext ω
      by_cases hω : ω ∈ {ω : Ω₁ × Ω₂ | x ≤ X ω ∧ y ≤ (fun _ : Ω₁ × Ω₂ => (0 : ℝ)) ω}
      · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω, Set.indicator_of_mem hω,
          Set.indicator_of_mem (hEG ω hω x le_rfl), Set.indicator_of_mem (hEG ω hω 0 hx)]
      · simp only [Set.indicator_of_notMem hω]; ring
    rw [e]
    exact ((hL x 0 hx le_rfl).indicator hEm).sub ((hL 0 0 le_rfl le_rfl).indicator hEm)
  · obtain ⟨i, hXi⟩ := hXS ω
    have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) (S₂ i ω.2) := ⟨le_rfl, ((hE ω).S₂pos i).le⟩
    exact (((hE ω).continuousOn_sEll_own rr i h0).sub continuousOn_const).mono (Icc_subset_Icc_right hXi)

end Pair

/-! ### The curve-`2` marginal exponent on the product -/

section PairT

variable {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] {ι : Type*} [Fintype ι] {n : ℕ}

/-- At height `0` the centred forward map is the translation by the start (everywhere). -/
theorem fwdMap_zero_eq_sub (V : ℝ → ℝ) (z : ℂ) : fwdMap V 0 z = z - V 0 := by
  have h := congrFun (frzChart_zero_eq_id V) z
  simp only [frzChart, id] at h
  exact eq_sub_of_add_eq h

/-- **The curve-`2` marginal exponent `ℓ_t(0, Y) − ℓ_t(0, 0)` (the `t`-view at curve-`1` height `0`) is measurable on
the product**, for curve `2` = `√(16/κ) B₂ + x₂` and a random time `Y` within the width at height `0`. It is the
`s`-view of the swapped, translated pair (`tEll_eq_sEll`) on `Ω₂ × Ω₁`, whose facts at height `0` are A15's `t`-view
data (`TwoEncl.tViewAt_zero'`). -/
theorem measurable_tEll_marg {κ : ℝ} {B₁ : ℝ≥0 → Ω₁ → ℝ} (hB₁m : ∀ r : ℝ≥0, Measurable (B₁ r))
    (hB₁c : ∀ ω, Continuous fun r => B₁ r ω) {B₂ : ℝ≥0 → Ω₂ → ℝ} (hB₂c : ∀ ω, Continuous fun r => B₂ r ω)
    (hB₂m : ∀ r : ℝ≥0, Measurable (B₂ r)) (hB₂0 : ∀ ω, B₂ 0 ω = 0) {x₂ : ℝ}
    {S₁ : ι → Ω₁ → ℝ} {S₂ : ι → Ω₂ → ℝ} (hS₁ : ∀ i, Measurable (S₁ i)) (hS₂ : ∀ i, Measurable (S₂ i))
    {H₁ H₂ : ι → Set ℂ} {δ q d : ι → ℝ} {p : Fin n → ℝ} {Tm : ℝ}
    (hE : ∀ ω : Ω₁ × Ω₂, TwoEncl (drive κ B₁ ω.1) (fun u => drive (16 / κ) B₂ ω.2 u + x₂) (fun i => S₁ i ω.1)
      (fun i => S₂ i ω.2) H₁ H₂ δ q d p Tm) [Nonempty ι]
    (rr : Fin n → ℝ) {Y : Ω₁ × Ω₂ → ℝ} (hY : Measurable Y) (hY0 : ∀ ω, 0 ≤ Y ω)
    (hYS : ∀ ω, Y ω ≤ stairH (fun i => S₁ i ω.1) (fun i => S₂ i ω.2) 0) :
    Measurable fun ω : Ω₁ × Ω₂ =>
      tEll κ rr (drive κ B₁ ω.1) (fun u => drive (16 / κ) B₂ ω.2 u + x₂)
          (tSelA (drive κ B₁ ω.1) (fun u => drive (16 / κ) B₂ ω.2 u + x₂) (fun i => S₁ i ω.1) (fun i => S₂ i ω.2))
          (tSelW (drive κ B₁ ω.1) (fun u => drive (16 / κ) B₂ ω.2 u + x₂) (fun i => S₁ i ω.1) (fun i => S₂ i ω.2))
          p 0 (Y ω) -
        tEll κ rr (drive κ B₁ ω.1) (fun u => drive (16 / κ) B₂ ω.2 u + x₂)
          (tSelA (drive κ B₁ ω.1) (fun u => drive (16 / κ) B₂ ω.2 u + x₂) (fun i => S₁ i ω.1) (fun i => S₂ i ω.2))
          (tSelW (drive κ B₁ ω.1) (fun u => drive (16 / κ) B₂ ω.2 u + x₂) (fun i => S₁ i ω.1) (fun i => S₂ i ω.2))
          p 0 0 := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  set V₁ : Ω₁ → ℝ → ℝ := fun ω u => drive κ B₁ ω u - x₂ with hV₁
  have hV₁c : ∀ ω, Continuous (V₁ ω) := fun ω => (QuantumZipper.drive_continuous (hB₁c ω)).sub continuous_const
  have hV0 : Measurable fun ω => V₁ ω 0 :=
    (measurable_drive_at (κ := κ) (B := B₁) (s := 0) le_rfl fun r _ => hB₁m r).sub measurable_const
  have hhit : ∀ L : Set ℂ, IsCompact L → L ⊆ H → MeasurableSet {ω | (L ∩ fwdHull (V₁ ω) 0).Nonempty} :=
    fun L _ _ => by
      have e : {ω | (L ∩ fwdHull (V₁ ω) 0).Nonempty} = ∅ := by
        ext ω
        simp [QuantumZipper.RS.fwdHull_zero_eq_empty (hV₁c ω)]
      rw [e]; exact MeasurableSet.empty
  have hfwd : ∀ z ∈ H, Measurable fun ω => fwdMap (V₁ ω) 0 z := fun z _ => by
    simp only [fwdMap_zero_eq_sub]
    exact measurable_const.sub (Complex.measurable_ofReal.comp hV0)
  have hS0 : ∀ ω' : Ω₂ × Ω₁, SViewAt (drive (16 / κ) B₂ ω'.1) (V₁ ω'.2) (fun i => S₂ i ω'.1)
      (fun i => S₁ i ω'.2) (fun m => p m - x₂) 0 := fun ω' =>
    (hE (ω'.2, ω'.1)).tViewAt_zero' i₀ (V := drive (16 / κ) B₂ ω'.1) (c := x₂)
      (by simp [QuantumZipper.drive_zero (hB₂0 ω'.1)]) fun s => by ring
  have hm := measurable_pairEll_marg_of (κ := 16 / κ) (B := B₂) hB₂c hB₂m (V := V₁) hV₁c hhit hfwd hV0
    (S₁ := S₂) (S₂ := S₁) hS₂ hS₁ (fun m => -(κ / 4) * rr m) (fun m => p m - x₂)
    (X := fun ω' => Y (ω'.2, ω'.1)) (hY.comp measurable_swap) (fun ω' => hY0 _) hS0 fun ω' => hYS (ω'.2, ω'.1)
  convert hm.comp measurable_swap using 1
  funext ω
  simp only [Function.comp_apply, Prod.fst_swap, Prod.snd_swap, pairEll]
  rw [tEll_eq_sEll κ rr p _ _ (QuantumZipper.drive_zero (hB₂0 ω.2)),
    tEll_eq_sEll κ rr p _ _ (QuantumZipper.drive_zero (hB₂0 ω.2))]

end PairT

/-! ### The patched dual density on the product of the two path spaces -/

section Dens

variable {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] {ι : Type*} [Fintype ι] {n : ℕ}

/-- The forward map of `√κ B` at a fixed point of `ℍ` and a fixed time is measurable. -/
theorem measurable_fwdMap_drive_at {Ω : Type*} [MeasurableSpace Ω] {κ : ℝ} {B : ℝ≥0 → Ω → ℝ}
    (hBc : ∀ ω, Continuous fun r => B r ω) (hBm : ∀ r : ℝ≥0, Measurable (B r)) {t : ℝ} (ht : 0 ≤ t) {z : ℂ}
    (hz : z ∈ H) : Measurable fun ω => fwdMap (drive κ B ω) t z := by
  have h := (measurable_fwd_drive (κ := κ) hBc ht (fun r _ => hBm r)).comp
    (measurable_const.prodMk measurable_id : Measurable fun ω : Ω => (z, ω))
  convert h using 1
  funext ω
  simp only [Function.comp_apply]
  by_cases hal : ∃ u, IsForwardSol (drive κ B ω) z t u
  · rw [Set.indicator_of_mem (show (z, ω) ∈ {p : ℂ × Ω | p.1 ∈ H ∧ ∃ u, IsForwardSol (drive κ B p.2) p.1 t u} from
      ⟨hz, hal⟩)]
  · rw [Set.indicator_of_notMem (fun h => hal h.2)]
    simp only [QuantumZipper.fwdMap, hal, ↓reduceDIte]

/-- The compact hits of the hull of a translated `√κ B + x` are measurable. -/
theorem measurableSet_hit_drive_add {Ω : Type*} [MeasurableSpace Ω] {κ : ℝ} {B : ℝ≥0 → Ω → ℝ}
    (hBc : ∀ ω, Continuous fun r => B r ω) (hBm : ∀ r : ℝ≥0, Measurable (B r)) {t : ℝ} (ht : 0 ≤ t) (x : ℝ)
    {L : Set ℂ} (hL : IsCompact L) (hLH : L ⊆ H) :
    MeasurableSet {ω | (L ∩ fwdHull (fun u => drive κ B ω u + x) t).Nonempty} := by
  have hL' : IsCompact ((fun z => z - (x : ℂ)) '' L) := hL.image (continuous_id.sub continuous_const)
  have hL'H : (fun z => z - (x : ℂ)) '' L ⊆ H := by
    rintro _ ⟨z, hz, rfl⟩
    have := hLH hz
    simp only [QuantumZipper.H, Set.mem_ofPred_eq] at this ⊢
    simpa using this
  have e : {ω | (L ∩ fwdHull (fun u => drive κ B ω u + x) t).Nonempty} =
      {ω | ((fun z => z - (x : ℂ)) '' L ∩ fwdHull (drive κ B ω) t).Nonempty} := by
    ext ω
    simp only [Set.mem_ofPred_eq, ConformalImageFull.fwdHull_add_const]
    constructor
    · rintro ⟨w, hwL, z, hz, rfl⟩
      exact ⟨z, ⟨z + x, hwL, by ring⟩, hz⟩
    · rintro ⟨z, ⟨w, hwL, rfl⟩, hz⟩
      exact ⟨w, hwL, w - x, hz, by ring⟩
  rw [e]
  exact measurableSet_hit_drive hBc ht (fun r _ => hBm r) hL' hL'H

/-- **The patched dual coupling density on `Ω₁ × Ω₂`** (§A.1.3–A.1.4): with curve `1` = `√κ B₁(ω₁)`, curve `2` =
`√(16/κ) B₂(ω₂) + x₂`, column ends `S₁ i ω₁`, heights `S₂ i ω₂`,
`D = M*_s(T, T) · Ñ_s(max S₁ ∧ T, 0)/Ñ_s(0, 0) · Ñ_t(0, max S₂ ∧ T)/Ñ_t(0, 0)` — the (D11) patch of the canonical
`s`-view normalised density times the two height-`0` marginal factors. -/
def dualDens (κ : ℝ) (rr p : Fin n → ℝ) (B₁ : ℝ≥0 → Ω₁ → ℝ) (B₂ : ℝ≥0 → Ω₂ → ℝ) (x₂ : ℝ) (S₁ : ι → Ω₁ → ℝ)
    (S₂ : ι → Ω₂ → ℝ) (Tm : ℝ) (ω : Ω₁ × Ω₂) : ℝ :=
  patch (fun i => S₁ i ω.1) (fun i => S₂ i ω.2)
      (fun x y => Real.exp (normLog (pairEll κ rr p B₁ (fun ω₂ u => drive (16 / κ) B₂ ω₂ u + x₂) S₁ S₂ ω) x y))
      Tm Tm *
    Real.exp (pairEll κ rr p B₁ (fun ω₂ u => drive (16 / κ) B₂ ω₂ u + x₂) S₁ S₂ ω
        (min (maxIn (stairCols fun i => S₁ i ω.1)) Tm) 0 -
      pairEll κ rr p B₁ (fun ω₂ u => drive (16 / κ) B₂ ω₂ u + x₂) S₁ S₂ ω 0 0) *
    Real.exp (tEll κ rr (drive κ B₁ ω.1) (fun u => drive (16 / κ) B₂ ω.2 u + x₂)
          (tSelA (drive κ B₁ ω.1) (fun u => drive (16 / κ) B₂ ω.2 u + x₂) (fun i => S₁ i ω.1) (fun i => S₂ i ω.2))
          (tSelW (drive κ B₁ ω.1) (fun u => drive (16 / κ) B₂ ω.2 u + x₂) (fun i => S₁ i ω.1) (fun i => S₂ i ω.2))
          p 0 (min (maxIn (stairCols fun i => S₂ i ω.2)) Tm) -
        tEll κ rr (drive κ B₁ ω.1) (fun u => drive (16 / κ) B₂ ω.2 u + x₂)
          (tSelA (drive κ B₁ ω.1) (fun u => drive (16 / κ) B₂ ω.2 u + x₂) (fun i => S₁ i ω.1) (fun i => S₂ i ω.2))
          (tSelW (drive κ B₁ ω.1) (fun u => drive (16 / κ) B₂ ω.2 u + x₂) (fun i => S₁ i ω.1) (fun i => S₂ i ω.2))
          p 0 0)

/-- **The patched dual density is jointly measurable on `Ω₁ × Ω₂`** (A15's "What remains" 2): every factor is the
canonical normalised density or a marginal exponent at random staircase points, measurable by dyadic rounding. -/
theorem measurable_dualDens {κ : ℝ} (hκ : 0 < κ) {B₁ : ℝ≥0 → Ω₁ → ℝ} (hB₁c : ∀ ω, Continuous fun r => B₁ r ω)
    (hB₁m : ∀ r : ℝ≥0, Measurable (B₁ r)) {B₂ : ℝ≥0 → Ω₂ → ℝ} (hB₂c : ∀ ω, Continuous fun r => B₂ r ω)
    (hB₂m : ∀ r : ℝ≥0, Measurable (B₂ r)) (hB₂0 : ∀ ω, B₂ 0 ω = 0) {x₂ : ℝ}
    {S₁ : ι → Ω₁ → ℝ} {S₂ : ι → Ω₂ → ℝ} (hS₁ : ∀ i, Measurable (S₁ i)) (hS₂ : ∀ i, Measurable (S₂ i))
    {H₁ H₂ : ι → Set ℂ} {δ q d : ι → ℝ} {p : Fin n → ℝ} {Tm : ℝ} (hTm : 0 ≤ Tm)
    (hE : ∀ ω : Ω₁ × Ω₂, TwoEncl (drive κ B₁ ω.1) (fun u => drive (16 / κ) B₂ ω.2 u + x₂) (fun i => S₁ i ω.1)
      (fun i => S₂ i ω.2) H₁ H₂ δ q d p Tm) [Nonempty ι] (rr : Fin n → ℝ) :
    Measurable (dualDens κ rr p B₁ B₂ x₂ S₁ S₂ Tm) := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  set V₂ : Ω₂ → ℝ → ℝ := fun ω u => drive (16 / κ) B₂ ω u + x₂ with hV₂
  have hV₂c : ∀ ω, Continuous (V₂ ω) := fun ω =>
    (QuantumZipper.drive_continuous (hB₂c ω)).add continuous_const
  have hVhit : ∀ t, 0 ≤ t → ∀ L : Set ℂ, IsCompact L → L ⊆ H →
      MeasurableSet {ω | (L ∩ fwdHull (V₂ ω) t).Nonempty} := fun t ht L hL hLH =>
    measurableSet_hit_drive_add hB₂c hB₂m ht x₂ hL hLH
  have hVfwd : ∀ t, 0 ≤ t → ∀ z ∈ H, Measurable fun ω => fwdMap (V₂ ω) t z := fun t ht z hz => by
    simp only [hV₂, ConformalImageFull.fwdMap_add_const]
    refine measurable_fwdMap_drive_at hB₂c hB₂m ht ?_
    have := hz
    simp only [QuantumZipper.H, Set.mem_ofPred_eq] at this ⊢
    simpa using this
  have hVt : ∀ t, Measurable fun ω => V₂ ω t := fun t => by
    show Measurable fun ω => Real.sqrt (16 / κ) * B₂ t.toNNReal ω + x₂
    exact (measurable_const.mul (hB₂m _)).add_const _
  have hS₁' : ∀ i, Measurable fun ω : Ω₁ × Ω₂ => S₁ i ω.1 := fun i => (hS₁ i).comp measurable_fst
  have hS₂' : ∀ i, Measurable fun ω : Ω₁ × Ω₂ => S₂ i ω.2 := fun i => (hS₂ i).comp measurable_snd
  have hNL := fun {X Y : Ω₁ × Ω₂ → ℝ} (hX : Measurable X) (hY : Measurable Y) (hX0 : ∀ ω, 0 ≤ X ω)
      (hY0 : ∀ ω, 0 ≤ Y ω) (hXY : ∀ ω, ∃ i, X ω ≤ S₁ i ω.1 ∧ Y ω ≤ S₂ i ω.2) =>
    measurable_pairNormLog hB₁c hB₁m hV₂c hVhit hVfwd hVt hS₁ hS₂ hE hκ.ne' rr hX hY hX0 hY0 hXY
  -- the patch exponent, as a weighted sum over the indices
  have hYm : ∀ i, Measurable fun ω : Ω₁ × Ω₂ =>
      min (stairH (fun i => S₁ i ω.1) (fun i => S₂ i ω.2) (S₁ i ω.1)) Tm := fun i =>
    (measurable_stairH hS₁' hS₂' (hS₁' i)).min measurable_const
  have hXY : ∀ i (ω : Ω₁ × Ω₂), ∃ j, S₁ i ω.1 ≤ S₁ j ω.1 ∧
      stairH (fun i => S₁ i ω.1) (fun i => S₂ i ω.2) (S₁ i ω.1) = S₂ j ω.2 :=
    fun i ω => exists_eq_stairH (fun j => ((hE ω).S₂pos j).le) le_rfl
  have hpatch : Measurable fun ω : Ω₁ × Ω₂ => patchLog (fun i => S₁ i ω.1) (fun i => S₂ i ω.2)
      (normLog (pairEll κ rr p B₁ V₂ S₁ S₂ ω)) Tm Tm := by
    have e : (fun ω : Ω₁ × Ω₂ => patchLog (fun i => S₁ i ω.1) (fun i => S₂ i ω.2)
        (normLog (pairEll κ rr p B₁ V₂ S₁ S₂ ω)) Tm Tm) = fun ω => ∑ i,
        (normLog (pairEll κ rr p B₁ V₂ S₁ S₂ ω) (min (S₁ i ω.1) Tm)
            (min (stairH (fun i => S₁ i ω.1) (fun i => S₂ i ω.2) (S₁ i ω.1)) Tm) -
          normLog (pairEll κ rr p B₁ V₂ S₁ S₂ ω) (min (prevIn (stairCols fun i => S₁ i ω.1) (S₁ i ω.1)) Tm)
            (min (stairH (fun i => S₁ i ω.1) (fun i => S₂ i ω.2) (S₁ i ω.1)) Tm)) /
        ((univ.filter fun j => S₁ j ω.1 = S₁ i ω.1).card : ℝ) := by
      funext ω
      unfold patchLog
      exact sum_stairCols_eq (fun i => S₁ i ω.1) fun c =>
        normLog (pairEll κ rr p B₁ V₂ S₁ S₂ ω) (min c Tm)
            (min (stairH (fun i => S₁ i ω.1) (fun i => S₂ i ω.2) c) Tm) -
          normLog (pairEll κ rr p B₁ V₂ S₁ S₂ ω) (min (prevIn (stairCols fun i => S₁ i ω.1) c) Tm)
            (min (stairH (fun i => S₁ i ω.1) (fun i => S₂ i ω.2) c) Tm)
    rw [e]
    refine Finset.measurable_sum _ fun i _ => ((hNL ((hS₁' i).min measurable_const) (hYm i) ?_ ?_ ?_).sub
      (hNL ((measurable_prevIn_stairCols hS₁' (hS₁' i)).min measurable_const) (hYm i) ?_ ?_ ?_)).div
      (measurable_card_filter_eq hS₁' i)
    · exact fun ω => le_min ((hE ω).S₁pos i).le hTm
    · exact fun ω => le_min (stairH_nonneg _) hTm
    · intro ω
      obtain ⟨j, hj, hjeq⟩ := hXY i ω
      exact ⟨j, (min_le_left _ _).trans hj, (min_le_left _ _).trans hjeq.le⟩
    · exact fun ω => le_min (prevIn_nonneg _ _) hTm
    · exact fun ω => le_min (stairH_nonneg _) hTm
    · intro ω
      obtain ⟨j, hj, hjeq⟩ := hXY i ω
      exact ⟨j, ((min_le_left _ _).trans (prevIn_le ((hE ω).S₁pos i).le)).trans hj, (min_le_left _ _).trans hjeq.le⟩
  -- the two marginal exponents
  have hm₁ := measurable_pairEll_marg_of hB₁c hB₁m hV₂c (hVhit 0 le_rfl) (hVfwd 0 le_rfl) (hVt 0) hS₁ hS₂ rr p
    (X := fun ω => min (maxIn (stairCols fun i => S₁ i ω.1)) Tm)
    ((measurable_maxIn_stairCols hS₁').min measurable_const) (fun ω => le_min (maxIn_nonneg _) hTm)
    (fun ω => (hE ω).sViewAt i₀ ⟨le_rfl, ((hE ω).S₂pos i₀).le⟩)
    (fun ω => by rw [stairH_zero_eq_maxIn fun i => ((hE ω).S₂pos i).le]; exact min_le_left _ _)
  have hm₂ := measurable_tEll_marg hB₁m hB₁c hB₂c hB₂m hB₂0 hS₁ hS₂ hE rr
    (Y := fun ω => min (maxIn (stairCols fun i => S₂ i ω.2)) Tm)
    ((measurable_maxIn_stairCols hS₂').min measurable_const) (fun ω => le_min (maxIn_nonneg _) hTm)
    (fun ω => by rw [stairH_zero_eq_maxIn fun i => ((hE ω).S₁pos i).le]; exact min_le_left _ _)
  have e : dualDens κ rr p B₁ B₂ x₂ S₁ S₂ Tm = fun ω =>
      Real.exp (patchLog (fun i => S₁ i ω.1) (fun i => S₂ i ω.2) (normLog (pairEll κ rr p B₁ V₂ S₁ S₂ ω)) Tm Tm) *
        Real.exp (pairEll κ rr p B₁ V₂ S₁ S₂ ω (min (maxIn (stairCols fun i => S₁ i ω.1)) Tm) 0 -
          pairEll κ rr p B₁ V₂ S₁ S₂ ω 0 0) *
        Real.exp (tEll κ rr (drive κ B₁ ω.1) (fun u => drive (16 / κ) B₂ ω.2 u + x₂)
            (tSelA (drive κ B₁ ω.1) (fun u => drive (16 / κ) B₂ ω.2 u + x₂) (fun i => S₁ i ω.1)
              (fun i => S₂ i ω.2))
            (tSelW (drive κ B₁ ω.1) (fun u => drive (16 / κ) B₂ ω.2 u + x₂) (fun i => S₁ i ω.1)
              (fun i => S₂ i ω.2)) p 0 (min (maxIn (stairCols fun i => S₂ i ω.2)) Tm) -
          tEll κ rr (drive κ B₁ ω.1) (fun u => drive (16 / κ) B₂ ω.2 u + x₂)
            (tSelA (drive κ B₁ ω.1) (fun u => drive (16 / κ) B₂ ω.2 u + x₂) (fun i => S₁ i ω.1)
              (fun i => S₂ i ω.2))
            (tSelW (drive κ B₁ ω.1) (fun u => drive (16 / κ) B₂ ω.2 u + x₂) (fun i => S₁ i ω.1)
              (fun i => S₂ i ω.2)) p 0 0) := by
    funext ω
    simp only [dualDens, patch, Real.log_exp]
    rfl
  rw [e]
  exact ((Real.measurable_exp.comp hpatch).mul (Real.measurable_exp.comp hm₁)).mul (Real.measurable_exp.comp hm₂)

end Dens

end InteractingSLE.ZhanGT4
