/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB9aTonelli

/-!
# Lemma GB9a: the ordered time-vector Tonelli argument with coordinatewise null sections

Packet PROVE-T14-TIP3. Lemma GB9a (`source/spec/p481-528.md` L1107–L1120, p. 527), proof ¶2:

> Fix a finite angle list. On the open simplex `0 < t₁ < ⋯ < t_n < ∞`, fix `t₁, …, t_{n−1}` and continue the last piece
> without another switch. Lemma 2.5 applied to the whole original-capacity concatenation gives, pathwise,
> `∫_{t_{n−1}}^∞ 1{η^{t₁,…,t_{n−1}}(t) ∈ ∂D} dt = 0`. […] Tonelli, first over the field and then over the earlier times,
> proves that the set of bad ordered vectors has Lebesgue measure zero. Apply the same argument to every initial
> sublist, and take the finite union, to include all switching tips of that vector.

The landed `Supp8.gb9a_of_pathwise_null` (PROVE-T14-TIP) takes as input that the whole `ω`-section of each bad set is
null. This file supplies that input from the form Lemma 2.5 actually gives: for a bad set `Bad k` attached to the
`k`-th switching or terminal tip, every section in the `k`-th coordinate (all other times fixed) is null, almost surely.

* `volume_eq_zero_of_update`: a measurable set of vectors whose sections in one coordinate are all null is null
  (Tonelli over the other coordinates);
* `volume_comp_equiv`: reordering the coordinates by a bijection `Fin N ≃ S` preserves Lebesgue measure (this covers
  the sorting of a tuple of distinct indices into an ordered time vector);
* `ae_measure_section_eq_zero_of_ae`: Tonelli with an almost-sure pathwise hypothesis;
* **`gb9a_of_ae_coord_null`**: the selection of one deterministic dense `Q = range q ⊂ (0, ∞)` such that, for every
  index `j`, every reordering `e` of the tuple `S j` and every tip `k`, the field gives probability zero to the bad
  event `Bad j k` at the time vector `i ↦ q (e i)`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory

namespace InteractingSLE

namespace Theorem14

namespace GW2Schedule

/-- `Fin.insertNth` as an update of a vector. -/
theorem insertNth_eq_update {n : ℕ} (i : Fin (n + 1)) (x : ℝ) (w : Fin n → ℝ) :
    Fin.insertNth (α := fun _ => ℝ) i x w = Function.update (Fin.insertNth (α := fun _ => ℝ) i 0 w) i x := by
  funext j
  refine Fin.succAboveCases i ?_ (fun k => ?_) j
  · simp only [Fin.insertNth_apply_same, Function.update_self]
  · rw [Fin.insertNth_apply_succAbove, Function.update_of_ne (Fin.succAbove_ne i k),
      Fin.insertNth_apply_succAbove]

/-- **One coordinate suffices**: a measurable set of vectors whose sections in the coordinate `i` are all
Lebesgue-null is Lebesgue-null. -/
theorem volume_eq_zero_of_update {N : ℕ} {A : Set (Fin N → ℝ)} (hA : MeasurableSet A) (i : Fin N)
    (hsec : ∀ v : Fin N → ℝ, volume {x : ℝ | Function.update v i x ∈ A} = 0) : volume A = 0 := by
  cases N with
  | zero => exact i.elim0
  | succ n =>
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i with hedef
    have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => (volume : Measure ℝ)) i
    have hpre : e ⁻¹' (e.symm ⁻¹' A) = A := by
      ext v; simp only [mem_preimage, MeasurableEquiv.symm_apply_apply]
    have h1 : volume A = ((volume : Measure ℝ).prod (Measure.pi fun _ : Fin n => (volume : Measure ℝ)))
        (e.symm ⁻¹' A) := by
      rw [← hmp.measure_preimage (e.symm.measurable hA).nullMeasurableSet, hpre, volume_pi]
    rw [h1, Measure.prod_apply_symm (e.symm.measurable hA)]
    refine lintegral_eq_zero_of_ae_eq_zero (Eventually.of_forall fun w => ?_)
    show volume ((fun x => (x, w)) ⁻¹' (e.symm ⁻¹' A)) = 0
    have hset : (fun x => (x, w)) ⁻¹' (e.symm ⁻¹' A) =
        {x : ℝ | Function.update (Fin.insertNth (α := fun _ => ℝ) i 0 w) i x ∈ A} := by
      ext x
      simp only [mem_preimage, mem_ofPred_eq]
      rw [← insertNth_eq_update]
      rfl
    rw [hset]
    exact hsec _

/-- **Reordering the coordinates preserves Lebesgue measure**: for a bijection `e : Fin N ≃ S`, the vectors `y` on
`S` with `y ∘ e ∈ A` have the measure of `A`. -/
theorem volume_comp_equiv {N : ℕ} {S : Finset ℕ} (e : Fin N ≃ S) {A : Set (Fin N → ℝ)} (hA : MeasurableSet A) :
    (Measure.pi fun _ : S => (volume : Measure ℝ)) {y | (fun i => y (e i)) ∈ A} = volume A := by
  have hmp := measurePreserving_piCongrLeft (fun _ : S => (volume : Measure ℝ)) e
  have hmeas : MeasurableSet {y : S → ℝ | (fun i => y (e i)) ∈ A} :=
    (measurable_pi_iff.2 fun i => measurable_pi_apply (e i)) hA
  rw [← hmp.measure_preimage hmeas.nullMeasurableSet, volume_pi]
  congr 1
  ext v
  simp only [mem_preimage, mem_ofPred_eq]
  have : (fun i => (MeasurableEquiv.piCongrLeft (fun _ : S => ℝ) e v) (e i)) = v := by
    funext i
    exact Equiv.piCongrLeft_apply_apply (P := fun _ : S => ℝ) e v i
  rw [this]

/-- **Tonelli with an almost-sure pathwise hypothesis**: if almost every `ω`-section of a measurable set `B ⊆ Ω × Y`
is `ν`-null, then for `ν`-almost every `y` the `y`-section is `P`-null. -/
theorem ae_measure_section_eq_zero_of_ae {Ω Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y] (P : Measure Ω)
    (ν : Measure Y) [SFinite P] [SFinite ν] {B : Set (Ω × Y)} (hB : MeasurableSet B)
    (hpath : ∀ᵐ ω ∂P, ν {y | (ω, y) ∈ B} = 0) : ∀ᵐ y ∂ν, P {ω | (ω, y) ∈ B} = 0 := by
  have h1 : (P.prod ν) B = 0 := (Measure.measure_prod_null hB).2 hpath
  rw [Measure.prod_apply_symm hB] at h1
  filter_upwards [(lintegral_eq_zero_iff (measurable_measure_prodMk_right hB)).1 h1] with y hy
  exact hy

/-- **Lemma GB9a, ordered time vectors** (selection with coordinatewise null sections). Let `ι` be countable; for
each `j` let `S j` be a finite set of auxiliary indices and, for each tip `k` of the time vectors indexed by
`Fin (S j).card`, let `Bad j k ⊆ Ω × (Fin (S j).card → ℝ)` be measurable with, almost surely, every section in the
`k`-th coordinate Lebesgue-null (Lemma 2.5 for the `k`-th piece, all other times fixed). Then there is one
deterministic sequence `q` of positive reals, dense in `(0, ∞)`, such that for every `j`, every reordering
`e : Fin (S j).card ≃ S j` and every `k`, the field gives probability zero to `Bad j k` at the times `i ↦ q (e i)`. -/
theorem gb9a_of_ae_coord_null {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P] {ι : Type*}
    [Countable ι] (S : ι → Finset ℕ) (Bad : (j : ι) → Fin (S j).card → Set (Ω × (Fin (S j).card → ℝ)))
    (hm : ∀ j k, MeasurableSet (Bad j k))
    (hsec : ∀ j k, ∀ᵐ ω ∂P, ∀ v : Fin (S j).card → ℝ,
      volume {x : ℝ | (ω, Function.update v k x) ∈ Bad j k} = 0) :
    ∃ q : ℕ → ℝ, (∀ m, 0 < q m) ∧ Ioi 0 ⊆ closure (range q) ∧
      ∀ j (e : Fin (S j).card ≃ S j) k, P {ω | (ω, fun i => q (e i)) ∈ Bad j k} = 0 := by
  classical
  set B : (j : ι) → Set (Ω × (S j → ℝ)) := fun j =>
    ⋃ (e : Fin (S j).card ≃ S j) (k : Fin (S j).card), {p | (p.1, fun i => p.2 (e i)) ∈ Bad j k} with hBdef
  have hBm : ∀ j, MeasurableSet (B j) := fun j =>
    MeasurableSet.iUnion fun e => MeasurableSet.iUnion fun k =>
      (measurable_fst.prodMk (measurable_pi_iff.2 fun i => (measurable_pi_apply (e i)).comp measurable_snd))
        (hm j k)
  have hnull : ∀ j, ∀ᵐ y ∂(Measure.pi fun _ : S j => (volume : Measure ℝ)), P {ω | (ω, y) ∈ B j} = 0 := by
    intro j
    refine ae_measure_section_eq_zero_of_ae P _ (hBm j) ?_
    have hk : ∀ᵐ ω ∂P, ∀ k, ∀ v : Fin (S j).card → ℝ,
        volume {x : ℝ | (ω, Function.update v k x) ∈ Bad j k} = 0 := ae_all_iff.2 fun k => hsec j k
    filter_upwards [hk] with ω hω
    have e1 : {y : S j → ℝ | (ω, y) ∈ B j} = ⋃ (e : Fin (S j).card ≃ S j) (k : Fin (S j).card),
        {y : S j → ℝ | (fun i => y (e i)) ∈ {v | (ω, v) ∈ Bad j k}} := by
      ext y; simp only [hBdef, mem_iUnion, mem_ofPred_eq]
    rw [e1]
    refine measure_iUnion_null fun e => measure_iUnion_null fun k => ?_
    have hsm : MeasurableSet {v : Fin (S j).card → ℝ | (ω, v) ∈ Bad j k} := measurable_prodMk_left (hm j k)
    rw [volume_comp_equiv e hsm]
    exact volume_eq_zero_of_update hsm k fun v => hω k v
  obtain ⟨q, hq0, hqd, hq⟩ := Supp8.gb9a_exists_dense P S B hnull
  refine ⟨q, hq0, hqd, fun j e k => measure_mono_null (fun ω hω => ?_) (hq j)⟩
  simp only [mem_ofPred_eq, hBdef, mem_iUnion]
  exact ⟨e, k, hω⟩

end GW2Schedule

end Theorem14

end InteractingSLE
