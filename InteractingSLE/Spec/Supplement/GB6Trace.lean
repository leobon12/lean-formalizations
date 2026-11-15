/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6Law
import InteractingSLE.Spec.Supplement.GB5
import InteractingSLE.Spec.Supplement.G12RemPassiveWord
import InteractingSLE.Spec.Supplement.LPProbReflect
import InteractingSLE.Spec.Sec4.Prob41Trace

/-!
# Proposition GB6: the protected tails of the conditional counterflow (GB5 with passive marks)

Packet PROVE-GB6D, the probabilistic half of GB6's step (e). GB6's proof (p. 519): "Its two final flow-boundary tails
are protected by GB5, even when its earlier original boundary partial sums are below `c`"; "Those junctions have the
outward flow-side partial sum at least `c`, so GB5 protects the junction itself"; (e): "GB5 excludes the required
finite reference contact".

For an integrated `SLE_k(ρ)` evolution with infinite lifetime and a point `p > 0` beyond which every right cumulative
weight is at least `c = k/2 − 2` (and before which every one is `> −2`), almost surely the trace never visits the closed
tail `[p, ∞)`:

* if `p` is a mark, Lemma GB5 (`Supp8.GB5.gb5`) at the first label at `p` keeps the driver strictly left of that mark,
  and the deterministic avoidance `Sec4.IsIntegratedSLEPath.trace_ne_of_right` gives the tail
  (`ae_trace_ne_of_ge_mark`);
* otherwise a passive zero-weight mark is inserted at `p` (`Supp7.G12.isIntegratedSLEEvolution_insertPassive`; the
  seed mark below `p` is the required lower mark), which changes neither the driver nor the cumulative weights
  (`ae_trace_ne_of_ge`).

The left tail is the reflection (`IsIntegratedSLEEvolution.reflect`, `LP.isGeneratingTrace_reflect`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Finset
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Supp8

namespace GB6

section Protect

variable {k : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
  {η : Ω → ℝ≥0 → ℂ}

/-- At a group end, the labels up to it are the labels at or left of its position. -/
theorem filter_le_eq_filter_xR_le (hmono : Monotone xR) {i : Fin nR} (hend : ∀ i', i < i' → xR i < xR i') :
    univ.filter (fun l => l ≤ i) = univ.filter (fun l => xR l ≤ xR i) := by
  ext l
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨fun h => hmono h, fun h => ?_⟩
  by_contra hl
  exact absurd h (not_le.2 (hend l (not_le.1 hl)))

/-- **The closed tail beyond a protected mark is never visited** (Lemma GB5 at the first label of the mark). -/
theorem ae_trace_ne_of_ge_mark (hk : 0 < k) (hF : IsOrderedForceWord xL xR)
    (hE : IsIntegratedSLEEvolution k xL xR ρL ρR P 𝓕 W VL VR B ζ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤)
    (hη : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) ⊤ (η ω)) (j : Fin nR) (hj0 : 0 < xR j)
    (hjmin : ∀ i, xR i = xR j → j ≤ i) (hfirst : xR ⟨0, Fin.pos j⟩ < xR j)
    (hin : ∀ x, x < xR j → -2 < ∑ i ∈ univ.filter (fun i => xR i ≤ x), ρR i)
    (hout : ∀ x, xR j ≤ x → k / 2 - 2 ≤ ∑ i ∈ univ.filter (fun i => xR i ≤ x), ρR i) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, ∀ y : ℝ, xR j ≤ y → η ω t ≠ y := by
  have hmono := hF.2.2.1
  have hsep := GB5.gb5 hk hF j (fun i hij hend => by
      rw [filter_le_eq_filter_xR_le hmono hend]
      refine hin _ (lt_of_le_of_ne (hmono hij.le) fun heq => ?_)
      exact absurd (hjmin i heq) (not_le.2 hij))
    (fun i hji hend => by
      rw [filter_le_eq_filter_xR_le hmono hend]
      exact hout _ (hmono hji)) hfirst hE
  filter_upwards [hsep, hζ, hE.2.2.2.2, hη] with ω hs hζω hp hηω t y hy
  rw [hζω] at hs hp
  exact Sec4.IsIntegratedSLEPath.trace_ne_of_right hp hηω j (fun t _ => hs t ENNReal.coe_lt_top) t
    (hj0.trans_le hy) hy

/-- **The closed tail `[p, ∞)` is never visited** when every right cumulative weight is `> −2` before `p` and at
least `k/2 − 2` from `p` on, and some right mark lies left of `p` (a passive mark is inserted at `p` if needed). -/
theorem ae_trace_ne_of_ge [IsProbabilityMeasure P] (hk : 0 < k) (hF : IsOrderedForceWord xL xR)
    (hE : IsIntegratedSLEEvolution k xL xR ρL ρR P 𝓕 W VL VR B ζ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤)
    (hη : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) ⊤ (η ω)) {p : ℝ} (hp : 0 < p)
    (hseed : ∃ i, xR i < p)
    (hin : ∀ x, x < p → -2 < ∑ i ∈ univ.filter (fun i => xR i ≤ x), ρR i)
    (hout : ∀ x, p ≤ x → k / 2 - 2 ≤ ∑ i ∈ univ.filter (fun i => xR i ≤ x), ρR i) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, ∀ y : ℝ, p ≤ y → η ω t ≠ y := by
  obtain ⟨i₀, hi₀⟩ := hseed
  have hmono := hF.2.2.1
  by_cases hpm : ∃ j, xR j = p
  · -- `p` is a mark: the first label there
    have hne : (univ.filter (fun j => xR j = p)).Nonempty := by
      obtain ⟨j, hj⟩ := hpm; exact ⟨j, Finset.mem_filter.2 ⟨mem_univ _, hj⟩⟩
    set j := (univ.filter (fun j => xR j = p)).min' hne with hjdef
    have hjp : xR j = p := (Finset.mem_filter.1 (Finset.min'_mem _ hne)).2
    have hjmin : ∀ i, xR i = xR j → j ≤ i := fun i hi =>
      Finset.min'_le _ i (Finset.mem_filter.2 ⟨mem_univ _, hi.trans hjp⟩)
    have hfirst : xR ⟨0, Fin.pos j⟩ < xR j := by
      rw [hjp]
      exact lt_of_le_of_lt (hmono (show (⟨0, Fin.pos j⟩ : Fin nR) ≤ i₀ from Fin.le_def.2 (Nat.zero_le _))) hi₀
    have h := ae_trace_ne_of_ge_mark hk hF hE hζ hη j (hjp ▸ hp) hjmin hfirst (fun x hx => hin x (hjp ▸ hx))
      (fun x hx => hout x (hjp ▸ hx))
    rw [hjp] at h
    exact h
  · -- insert a passive mark at `p`
    push Not at hpm
    have hne : (univ.filter (fun j => xR j < p)).Nonempty := ⟨i₀, Finset.mem_filter.2 ⟨mem_univ _, hi₀⟩⟩
    set k₀ := (univ.filter (fun j => xR j < p)).max' hne with hk₀def
    have hk₀ : xR k₀ < p := (Finset.mem_filter.1 (Finset.max'_mem _ hne)).2
    have hk₀y : ∀ j, xR j < p → j ≤ k₀ := fun j hj =>
      Finset.le_max' _ j (Finset.mem_filter.2 ⟨mem_univ _, hj⟩)
    set q : Fin (nR + 1) := k₀.succ with hqdef
    have hE' := Supp7.G12.isIntegratedSLEEvolution_insertPassive hE hF hp hk₀ hk₀y
    have hb : ∀ j : Fin nR, j.castSucc < q → xR j ≤ p := fun j hj => by
      rw [hqdef, Fin.castSucc_lt_succ_iff] at hj
      exact (hmono hj).trans hk₀.le
    have ha : ∀ j : Fin nR, q ≤ j.castSucc → p ≤ xR j := fun j hj => by
      have hkj : k₀ < j := by
        rw [hqdef] at hj
        by_contra hjk; rw [not_lt] at hjk
        exact absurd hj (not_le.2 (Fin.castSucc_lt_succ_iff.2 hjk))
      by_contra hlt; rw [not_le] at hlt
      exact absurd (hk₀y j hlt) (not_le.2 hkj)
    have hmono' := Supp7.G12.monotone_insertNth hmono q hb ha
    have hF' : IsOrderedForceWord xL (Fin.insertNth (α := fun _ => ℝ) q p xR) := by
      refine ⟨hF.1, hF.2.1, hmono', fun i => ?_⟩
      rcases Fin.eq_self_or_eq_succAbove q i with rfl | ⟨j, rfl⟩
      · simp only [Fin.insertNth_apply_same]; exact hp.le
      · simp only [Fin.insertNth_apply_succAbove]; exact hF.2.2.2 j
    have hqp : Fin.insertNth (α := fun _ => ℝ) q p xR q = p := Fin.insertNth_apply_same _ _ _
    have hsum : ∀ x : ℝ, ∑ i ∈ univ.filter (fun i => Fin.insertNth (α := fun _ => ℝ) q p xR i ≤ x),
        Fin.insertNth (α := fun _ => ℝ) q 0 ρR i = ∑ j ∈ univ.filter (fun j => xR j ≤ x), ρR j := by
      intro x
      rw [Finset.sum_filter, Finset.sum_filter, Supp7.G12.sum_insertNth_of_eq_zero q _ (by simp)]
      simp only [Fin.insertNth_apply_succAbove]
    have hjmin : ∀ i, Fin.insertNth (α := fun _ => ℝ) q p xR i = Fin.insertNth (α := fun _ => ℝ) q p xR q →
        q ≤ i := by
      intro i hi
      rw [hqp] at hi
      rcases Fin.eq_self_or_eq_succAbove q i with rfl | ⟨j, rfl⟩
      · exact le_rfl
      · simp only [Fin.insertNth_apply_succAbove] at hi
        exact absurd hi (hpm j)
    have hfirst : Fin.insertNth (α := fun _ => ℝ) q p xR ⟨0, Fin.pos q⟩ <
        Fin.insertNth (α := fun _ => ℝ) q p xR q := by
      rw [hqp]
      refine lt_of_le_of_lt (hmono' (show (⟨0, Fin.pos q⟩ : Fin (nR + 1)) ≤ q.succAbove k₀ from
        Fin.le_def.2 (Nat.zero_le _))) ?_
      rw [Fin.insertNth_apply_succAbove]; exact hk₀
    have h := ae_trace_ne_of_ge_mark hk hF' hE' hζ hη q (by rw [hqp]; exact hp) hjmin hfirst
      (fun x hx => by rw [hsum]; exact hin x (hqp ▸ hx)) (fun x hx => by rw [hsum]; exact hout x (hqp ▸ hx))
    rw [hqp] at h
    exact h

/-- **The closed left tail `(−∞, p]` is never visited** (the reflection of `ae_trace_ne_of_ge`): `p < 0`, every left
cumulative weight `> −2` right of `p` and at least `k/2 − 2` at and beyond `p`, some left mark right of `p`. -/
theorem ae_trace_ne_of_le [IsProbabilityMeasure P] (hk : 0 < k) (hF : IsOrderedForceWord xL xR)
    (hE : IsIntegratedSLEEvolution k xL xR ρL ρR P 𝓕 W VL VR B ζ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤)
    (hη : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) ⊤ (η ω)) {p : ℝ} (hp : p < 0)
    (hseed : ∃ i, p < xL i)
    (hin : ∀ x, p < x → -2 < ∑ i ∈ univ.filter (fun i => x ≤ xL i), ρL i)
    (hout : ∀ x, x ≤ p → k / 2 - 2 ≤ ∑ i ∈ univ.filter (fun i => x ≤ xL i), ρL i) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, ∀ y : ℝ, y ≤ p → η ω t ≠ y := by
  have hη' : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => (-W) t ω) ⊤ (fun t => LP.reflectC (η ω t)) := by
    filter_upwards [hη] with ω h
    exact LP.isGeneratingTrace_reflect h
  have hfilt : ∀ x : ℝ, univ.filter (fun i => (-xL) i ≤ x) = univ.filter (fun i => -x ≤ xL i) := fun x =>
    Finset.filter_congr fun i _ => by simp only [Pi.neg_apply]; constructor <;> intro h <;> linarith
  obtain ⟨i₀, hi₀⟩ := hseed
  have h := ae_trace_ne_of_ge (p := -p) hk (Supp7.G12.isOrderedForceWord_reflect hF) hE.reflect hζ hη'
    (by linarith) ⟨i₀, by simp only [Pi.neg_apply]; linarith⟩
    (fun x hx => by rw [hfilt]; exact hin _ (by linarith)) (fun x hx => by rw [hfilt]; exact hout _ (by linarith))
  filter_upwards [h] with ω hω t y hy heq
  refine hω t (-y) (by linarith) ?_
  rw [heq]
  simp [LP.reflectC]

end Protect

end GB6

end Supp8

end InteractingSLE
