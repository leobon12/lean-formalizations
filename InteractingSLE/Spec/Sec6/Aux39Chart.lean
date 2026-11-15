/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec6.Aux38

/-!
# Facts in a fixed earlier chart (Lemma 1.2 of the ZTip-elimination note)

Ruling R41 adopts `source/external/AstraIG1/ig1_ztip_elimination.txt` for **Aux.** lemmas 37–43.
Its Lemma 1.2 (L65–L101, "Facts used without changing the chart") holds for every realized
continuous Loewner trace in its strict half-plane-capacity parameter:

1. the own-mapped future `δ_r` cannot have a nontrivial time interval contained in `ℝ`;
2. for `s ≤ r ≤ t`, `δ_s(t) = f_{s,r}(δ_r(t))` (`f_{s,r}` the continuously extended inverse
   mapping-out map of the increment from `s` to `r`);
3. if an injective incoming path `α : [0, 1] → Ω` has first-visit parameter
   `u(t) = min {v : α(v) ∈ R_t}` and `u` is constant on `[a, b]`, then it is constant on `[r, b]`
   whenever the physical point `p(a) = α(u(a))` has already been visited by `r ≤ a`.

Here `δ_r(t) = trMap W r t 0` (centred at the driver: `W_r` corresponds to `0`), `f_{s,r} =
trMap W s r` (PROVE-YUAN-M1B), and `R_t = η([0, t])`.

## Main results

* `fillH_union_of_im_eq_zero`: adding real points does not change a filling;
* `ownFuture_not_forall_real` (item 1);
* `ownFuture_trans` (item 2);
* `firstVisit`, `firstVisit_le`, `antitoneOn_firstVisit`, `firstVisit_mem`, `firstVisit_eq_of_mem`
  and `firstVisit_const_of_visited` (item 3).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology

open QuantumZipper (H Hbar fwdHull fwdMapInv)
open QuantumZipper.RS (shiftDrive)
open InteractingSLE.YuanSimpleApprox (trMap)

namespace InteractingSLE.Sec6

/-! ### Item 1: no real interval -/

/-- Adding real points does not change a filling: `fill(A ∪ B) = fill(A)` when `B ⊆ ℝ`. -/
theorem fillH_union_of_im_eq_zero {A B : Set ℂ} (hB : ∀ z ∈ B, z.im = 0) :
    fillH (A ∪ B) = fillH A := by
  have hBc : closure B ⊆ {z : ℂ | z.im = 0} :=
    closure_minimal hB (isClosed_eq Complex.continuous_im continuous_const)
  have hHc : H \ closure (A ∪ B) = H \ closure A := by
    rw [closure_union]
    ext z
    simp only [Set.mem_sdiff, mem_union, not_or]
    constructor
    · exact fun h => ⟨h.1, h.2.1⟩
    · refine fun h => ⟨h.1, h.2, fun hz => ?_⟩
      have h1 : z.im = 0 := hBc hz
      have h2 : 0 < z.im := h.1
      linarith
  ext z
  simp only [fillH, Set.mem_ofPred_eq, hHc]
  constructor
  · rintro ⟨hz, h | h⟩
    · rw [closure_union] at h
      rcases h with h | h
      · exact ⟨hz, Or.inl h⟩
      · have h1 : z.im = 0 := hBc h
        have h2 : 0 < z.im := hz
        linarith
    · exact ⟨hz, Or.inr h⟩
  · rintro ⟨hz, h | h⟩
    · exact ⟨hz, Or.inl (closure_mono subset_union_left h)⟩
    · exact ⟨hz, Or.inr h⟩

variable {W : ℝ → ℝ} {η : ℝ → ℂ}

/-- **Lemma 1.2 (1).** The own-mapped future `δ_r(t) = trMap W r t 0` of a continuous Loewner trace
has no nontrivial time interval in `ℝ`: on every `[c, d]` with `r ≤ c < d` some value lies in `ℍ`.
A real segment of the future adds no hull, whereas the hulls grow strictly. -/
theorem ownFuture_not_forall_real (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    {r c d : ℝ} (hr : 0 ≤ r) (hrc : r ≤ c) (hcd : c < d) :
    ∃ t ∈ Icc c d, trMap W r t 0 ∈ H := by
  by_contra hcon
  push Not at hcon
  set V := shiftDrive W r with hV
  have hVc : Continuous V := QuantumZipper.RS.continuous_shiftDrive hW r
  have hV0 : V 0 = 0 := InteractingSLE.shiftDrive_zero W r
  have hγ := YuanSimpleApprox.isLoewnerTrace_shift' hη hW hW0 hr
  set γ := loewnerTip V with hγdef
  have hreal : ∀ u ∈ Icc (c - r) (d - r), (γ u).im = 0 := by
    intro u hu
    have hmem := hcon (u + r) ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have hH : γ u ∈ Hbar := by
      have := YuanSimpleApprox.trMap_zero_mem_Hbar hη hW hW0 hr (b := u + r) (by linarith [hu.1])
      rwa [YuanSimpleApprox.trMap_zero, add_sub_cancel_right] at this
    rw [YuanSimpleApprox.trMap_zero, add_sub_cancel_right] at hmem
    exact le_antisymm (not_lt.1 hmem) hH
  have hc0 : 0 ≤ c - r := sub_nonneg.2 hrc
  have hcd' : c - r < d - r := by linarith
  have himg : γ '' Icc 0 (d - r) = γ '' Icc 0 (c - r) ∪ γ '' Icc (c - r) (d - r) := by
    rw [← image_union, Icc_union_Icc_eq_Icc hc0 hcd'.le]
  have heq : fwdHull V (d - r) = fwdHull V (c - r) := by
    rw [hγ.2.2 _ (hc0.trans hcd'.le), hγ.2.2 _ hc0, himg]
    exact fillH_union_of_im_eq_zero (by rintro _ ⟨u, hu, rfl⟩; exact hreal u hu)
  have hss := QuantumZipper.RS.fwdHull_ssubset hVc hV0 hc0 hcd'
  rw [heq] at hss
  exact hss.ne rfl

/-! ### Item 2: composition of increments -/

/-- **Lemma 1.2 (2).** For `s ≤ r ≤ t`, `δ_s(t) = f_{s,r}(δ_r(t))`. -/
theorem ownFuture_trans (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    {s r t : ℝ} (hs : 0 ≤ s) (hsr : s ≤ r) (hrt : r ≤ t) :
    trMap W s t 0 = trMap W s r (trMap W r t 0) :=
  (YuanSimpleApprox.trMap_trMap hη hW hW0 hs hsr hrt zero_mem_Hbar).symm

/-! ### Item 3: first-visit parameters -/

/-- The **first-visit parameter** of an incoming path `α : [0, 1] → ℂ` at time `t`:
`u(t) = min {v ∈ [0, 1] : α(v) ∈ R_t}`, for a family `R` of visited sets. -/
def firstVisit (R : ℝ → Set ℂ) (α : ℝ → ℂ) (t : ℝ) : ℝ := sInf {v ∈ Icc (0 : ℝ) 1 | α v ∈ R t}

section FirstVisit

variable {R : ℝ → Set ℂ} {α : ℝ → ℂ}

theorem firstVisit_set_bddBelow (t : ℝ) : BddBelow {v ∈ Icc (0 : ℝ) 1 | α v ∈ R t} :=
  ⟨0, fun _ hv => hv.1.1⟩

theorem firstVisit_le {t v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) (hvR : α v ∈ R t) :
    firstVisit R α t ≤ v :=
  csInf_le (firstVisit_set_bddBelow t) ⟨hv, hvR⟩

/-- If the visited parameters form a closed set (continuous `α`, closed `R t`) and are nonempty,
the minimum is attained. -/
theorem firstVisit_mem (hα : ContinuousOn α (Icc 0 1)) {t : ℝ} (hR : IsClosed (R t))
    (hne : ∃ v ∈ Icc (0 : ℝ) 1, α v ∈ R t) :
    firstVisit R α t ∈ Icc (0 : ℝ) 1 ∧ α (firstVisit R α t) ∈ R t := by
  have hcl : IsClosed {v ∈ Icc (0 : ℝ) 1 | α v ∈ R t} :=
    hα.preimage_isClosed_of_isClosed isClosed_Icc hR
  obtain ⟨v, hv⟩ := hne
  exact hcl.csInf_mem ⟨v, hv⟩ (firstVisit_set_bddBelow t)

/-- Visited sets increase, so first-visit parameters decrease. -/
theorem firstVisit_anti (hRm : Monotone R) {s t : ℝ} (hst : s ≤ t)
    (hne : ∃ v ∈ Icc (0 : ℝ) 1, α v ∈ R s) : firstVisit R α t ≤ firstVisit R α s := by
  obtain ⟨v, hv⟩ := hne
  exact csInf_le_csInf (firstVisit_set_bddBelow t) ⟨v, hv⟩ fun w hw => ⟨hw.1, hRm hst hw.2⟩

/-- **Lemma 1.2 (3).** Let `u` be the first-visit parameter. If the physical point `α(u(a))` has
already been visited by a time `r ≤ a`, then `u(r) = u(a)`; consequently, if `u` is constant on
`[a, b]`, it is constant on `[r, b]`. -/
theorem firstVisit_eq_of_visited (hα : ContinuousOn α (Icc 0 1)) (hRm : Monotone R)
    {r a : ℝ} (hra : r ≤ a) (hRa : IsClosed (R a)) (hne : ∃ v ∈ Icc (0 : ℝ) 1, α v ∈ R a)
    (hvis : α (firstVisit R α a) ∈ R r) : firstVisit R α r = firstVisit R α a := by
  have hmem := firstVisit_mem hα hRa hne
  refine le_antisymm (firstVisit_le hmem.1 hvis) ?_
  exact firstVisit_anti hRm hra ⟨_, hmem.1, hvis⟩

theorem firstVisit_const_of_visited (hα : ContinuousOn α (Icc 0 1)) (hRm : Monotone R)
    {r a b : ℝ} (hra : r ≤ a) (hRa : IsClosed (R a)) (hne : ∃ v ∈ Icc (0 : ℝ) 1, α v ∈ R r)
    (hconst : ∀ t ∈ Icc a b, firstVisit R α t = firstVisit R α a)
    (hvis : α (firstVisit R α a) ∈ R r) :
    ∀ t ∈ Icc r b, firstVisit R α t = firstVisit R α a := by
  have hne' : ∃ v ∈ Icc (0 : ℝ) 1, α v ∈ R a := by
    obtain ⟨v, hv, hvR⟩ := hne; exact ⟨v, hv, hRm hra hvR⟩
  have hra' := firstVisit_eq_of_visited hα hRm hra hRa hne' hvis
  intro t ht
  rcases le_total t a with hta | hat
  · have h1 : firstVisit R α t ≤ firstVisit R α r := firstVisit_anti hRm ht.1 hne
    have h2 : firstVisit R α a ≤ firstVisit R α t := by
      obtain ⟨v, hv, hvR⟩ := hne
      exact firstVisit_anti hRm hta ⟨v, hv, hRm ht.1 hvR⟩
    rw [hra'] at h1
    exact le_antisymm h1 h2
  · exact hconst t ⟨hat, ht.2⟩

end FirstVisit

end InteractingSLE.Sec6
