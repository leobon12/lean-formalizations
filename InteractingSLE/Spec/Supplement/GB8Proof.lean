/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB8
import InteractingSLE.Spec.Supplement.Aux108Inf
import InteractingSLE.Spec.Ito.Dynkin

/-!
# Lemma GB8: the proof, from its three cited inputs

Packet PROVE-T14-TIP2. Specification supplement §8.8, **Lemma GB8** and its proof (`source/spec/p481-528.md`
L1019–L1043, pp. 523–524); the statement is `Supp8.GB8.GB8Statement` (driver form, `GB8.lean`).

The proof in the source has four ingredients:

1. "Lemma GB7a protects the open right tail, and G12 protects its junction `x₊`": no contact with `[x₊, ∞)`
   (`RightNoContactStatement`, a named input: Lemma GB7a and Lemma G12 in driver form);
2. "On the event of no far-left contact there is therefore no finite continuation threshold": proved here
   (`exists_isFirstFarContact`: at a finite lifetime the state has a limit satisfying the threshold condition
   (Aux. lemma 3), and every group at the driver other than the whole left side has weight `> −2`);
3. "The complete finite-force theorem makes the trace transient … a sufficiently late rational own time `q` is an
   interior time after the last real contact": in driver form, on the no-contact event with infinite lifetime the gaps
   stay bounded away from `0` after some rational time (`EventualSepStatement`, a named input);
4. the reference comparison: "Choose reference marks … give them weights `κ − 4` and `c_κ` … This two-mark reference
   has an almost surely finite first real endpoint … Aux. 108 gives equivalence on the entire stopped history,
   including the event of an infinite stopping time … It therefore gives the same zero probability for the actual
   interior transient future. Countably many rational `q`, reference choices, and buffers exclude the event of no
   far-left contact": proved here from Aux. 108 through an infinite stopping time (`Aux108Inf`, restarted at every
   rational time `q > 0`, buffers `δ = 1/(n+1)`), with the reference's finite swallow of its outer left mark
   (`ReferenceSwallowStatement`, a named input: the full-span case of Aux. 22 for the two-mark word, in driver form).

Driver-form choices. The reference marks are the outermost actual marks themselves (all left weight `κ − 4` on
`x_{L,last}`, all right weight `c_κ` on `x_{R,last}`, the other marks passive), so the reference has the same side
totals ("their far heights agree exactly") and its outer left swallow is a real endpoint left of every actual inner
mark. The hull buffer is "every gap at least `δ`".

## Main results

* `exists_isFirstFarContact`, `eq_zeta_of_isFirstFarContact` (deterministic, along one integrated path);
* `ae_exists_isFirstFarContact`: the first conclusion of GB8 from inputs 3 and 4;
* **`gb8Statement_of_inputs`**: `GB8Statement` from the three named inputs.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Supp8

namespace GB8

open Aux108Inf Zhan Coupling Sec7.RandRestart Sec2.Assembly

/-! ### Groups at the driver are initial segments -/

section Prefix

/-- On an ordered side (`v` antitone, every mark at most `w`), the labels at `w` form an initial segment, so their
total weight is a partial sum: it exceeds `−2` when every partial sum before the last label does, and the last label
is at `w` only if the total exceeds `−2`. -/
theorem neg_two_lt_sum_filter {n : ℕ} {v ρ : Fin n → ℝ} {w : ℝ} (hv : Antitone v) (hle : ∀ i, v i ≤ w)
    (hps : ∀ i : Fin n, (i : ℕ) < n - 1 → -2 < ∑ l ∈ univ.filter (fun l => l ≤ i), ρ l)
    (hlast : ∀ i : Fin n, (i : ℕ) = n - 1 → v i = w → -2 < ∑ l, ρ l) :
    -2 < ∑ i ∈ univ.filter (fun i => v i = w), ρ i := by
  set Z := univ.filter (fun i => v i = w) with hZ
  rcases Z.eq_empty_or_nonempty with he | hne
  · rw [he, sum_empty]; norm_num
  set k := Z.max' hne with hk
  have hkZ : v k = w := (mem_filter.1 (Z.max'_mem hne)).2
  have hZk : Z = univ.filter (fun l => l ≤ k) := by
    ext i
    simp only [hZ, mem_filter, mem_univ, true_and]
    constructor
    · intro hi
      exact Z.le_max' i (mem_filter.2 ⟨mem_univ _, hi⟩)
    · intro hik
      exact le_antisymm (hle i) (hkZ ▸ hv hik)
  rw [hZk]
  rcases lt_or_ge (k : ℕ) (n - 1) with h | h
  · exact hps k h
  · have hkn : (k : ℕ) = n - 1 := le_antisymm (by have := k.isLt; omega) h
    have huniv : univ.filter (fun l : Fin n => l ≤ k) = univ := by
      ext l
      simp only [mem_filter, mem_univ, true_and, iff_true]
      exact Fin.le_def.2 (by have := l.isLt; omega)
    rw [huniv]
    exact hlast k hkn hkZ

/-- The right-side version (`v` monotone, every mark at least `w`). -/
theorem neg_two_lt_sum_filter_right {n : ℕ} {v ρ : Fin n → ℝ} {w : ℝ} (hv : Monotone v) (hle : ∀ i, w ≤ v i)
    (hps : ∀ i : Fin n, (i : ℕ) < n - 1 → -2 < ∑ l ∈ univ.filter (fun l => l ≤ i), ρ l)
    (hlast : ∀ i : Fin n, (i : ℕ) = n - 1 → v i = w → -2 < ∑ l, ρ l) :
    -2 < ∑ i ∈ univ.filter (fun i => v i = w), ρ i := by
  have e : univ.filter (fun i => v i = w) = univ.filter (fun i => -v i = -w) := by
    ext i; simp only [mem_filter, mem_univ, true_and, neg_inj]
  rw [e]
  exact neg_two_lt_sum_filter (fun i j hij => neg_le_neg (hv hij)) (fun i => neg_le_neg (hle i)) hps
    fun i hi h => hlast i hi (neg_inj.1 h)

end Prefix

/-! ### The first far-left contact along one path -/

section Path

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- **No threshold at a limit state off the outer left mark.** If the outermost left mark is strictly left of the
driver, every group at the driver has weight `> −2` (GB8: every earlier side partial sum is `> −2` and the right total
`κ/2 − 2` is `> −2`), so the threshold condition fails. -/
theorem not_threshold_of_lt (hκ : 0 < κ) (hnL : 0 < nL) {w₀ : ℝ} {vL₀ : Fin nL → ℝ} {vR₀ : Fin nR → ℝ}
    (hvL : Antitone vL₀) (hvLw : ∀ i, vL₀ i ≤ w₀) (hvR : Monotone vR₀) (hvRw : ∀ j, w₀ ≤ vR₀ j)
    (hlast : vL₀ ⟨nL - 1, Nat.sub_lt hnL one_pos⟩ < w₀) (hsR : ∑ j, ρR j = κ / 2 - 2)
    (hpsL : ∀ i : Fin nL, (i : ℕ) < nL - 1 → -2 < ∑ l ∈ univ.filter (fun l => l ≤ i), ρL l)
    (hpsR : ∀ j : Fin nR, (j : ℕ) < nR - 1 → -2 < ∑ l ∈ univ.filter (fun l => l ≤ j), ρR l) :
    ¬ ForceWord.ThresholdCondition ρL ρR w₀ vL₀ vR₀ := by
  rintro (h | h)
  · have := neg_two_lt_sum_filter (ρ := ρL) hvL hvLw hpsL fun i hi he => by
      have : i = ⟨nL - 1, Nat.sub_lt hnL one_pos⟩ := Fin.ext hi
      rw [this] at he
      exact absurd he hlast.ne
    linarith
  · have := neg_two_lt_sum_filter_right (ρ := ρR) hvR hvRw hpsR fun _ _ _ => by rw [hsR]; linarith
    linarith

/-- **The first far-left contact exists** along an integrated path of the GB8 word whose state has a threshold limit
at every finite positive lifetime (Aux. lemma 3), unless the lifetime is infinite and the outermost left mark never
meets the driver (`hinf` excludes that case). -/
theorem exists_isFirstFarContact (hκ : 0 < κ) (hnL : 0 < nL) (hF : IsOrderedForceWord xL xR)
    (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ)
    (hlim : ∀ T : ℝ≥0, 0 < T → (T : ℝ≥0∞) = ζ → ∃ (w₀ : ℝ) (vL₀ : Fin nL → ℝ) (vR₀ : Fin nR → ℝ),
      Tendsto (fun t => (w t, fun i => vL i t, fun j => vR j t)) (𝓝[<] T) (𝓝 (w₀, vL₀, vR₀)) ∧
      ForceWord.ThresholdCondition ρL ρR w₀ vL₀ vR₀)
    (hxm : xL ⟨nL - 1, Nat.sub_lt hnL one_pos⟩ < 0) (hsR : ∑ j, ρR j = κ / 2 - 2)
    (hpsL : ∀ i : Fin nL, (i : ℕ) < nL - 1 → -2 < ∑ l ∈ univ.filter (fun l => l ≤ i), ρL l)
    (hpsR : ∀ j : Fin nR, (j : ℕ) < nR - 1 → -2 < ∑ l ∈ univ.filter (fun l => l ≤ j), ρR l)
    (hinf : ζ = ⊤ → (∀ t : ℝ≥0, vL ⟨nL - 1, Nat.sub_lt hnL one_pos⟩ t < w t) → False) :
    ∃ τ : ℝ≥0, IsFirstFarContact w (vL ⟨nL - 1, Nat.sub_lt hnL one_pos⟩) ζ τ := by
  set ℓ : Fin nL := ⟨nL - 1, Nat.sub_lt hnL one_pos⟩ with hℓ
  have hpF := hp.isForcePath
  have hopen : IsOpen {t : ℝ≥0 | (t : ℝ≥0∞) < ζ} := isOpen_lt ENNReal.continuous_coe continuous_const
  by_cases hz : ∃ t : ℝ≥0, (t : ℝ≥0∞) < ζ ∧ vL ℓ t = w t
  · -- a contact before the lifetime: the first one
    set Z := {t : ℝ≥0 | (t : ℝ≥0∞) < ζ ∧ vL ℓ t = w t} with hZ
    obtain ⟨t₀, ht₀ζ, ht₀⟩ := hz
    have hZne : Z.Nonempty := ⟨t₀, ht₀ζ, ht₀⟩
    set τ := sInf Z with hτ
    have hτt₀ : τ ≤ t₀ := csInf_le (OrderBot.bddBelow Z) ⟨ht₀ζ, ht₀⟩
    have hτζ : (τ : ℝ≥0∞) < ζ := lt_of_le_of_lt (by exact_mod_cast hτt₀) ht₀ζ
    have hcl : τ ∈ closure Z := csInf_mem_closure hZne (OrderBot.bddBelow Z)
    have hcont : ContinuousAt (fun t => vL ℓ t - w t) τ :=
      ((hpF.continuousOn_vL ℓ).sub hpF.continuousOn_w).continuousAt (hopen.mem_nhds hτζ)
    have hτeq : vL ℓ τ = w τ := by
      by_contra hne
      have hne' : vL ℓ τ - w τ ≠ 0 := sub_ne_zero.2 hne
      obtain ⟨u, hu, huZ⟩ := mem_closure_iff_nhds.1 hcl _ (hcont.eventually_ne hne')
      exact hu (sub_eq_zero.2 huZ.2)
    have hτ0 : 0 < τ := by
      rw [pos_iff_ne_zero]
      intro h0
      rw [h0, hpF.vL_zero ℓ, hpF.w_zero] at hτeq
      linarith
    refine ⟨τ, hτ0, fun u hu => ?_, Or.inl ⟨hτζ, hτeq⟩⟩
    have huζ : (u : ℝ≥0∞) < ζ := lt_trans (by exact_mod_cast hu) hτζ
    have hnot : u ∉ Z := notMem_of_lt_csInf hu (OrderBot.bddBelow Z)
    exact lt_of_le_of_ne (hpF.vL_le_w huζ ℓ) fun he => hnot ⟨huζ, he⟩
  · push Not at hz
    have hlt : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → vL ℓ t < w t := fun t ht =>
      lt_of_le_of_ne (hpF.vL_le_w ht ℓ) (hz t ht)
    by_cases hζ : ζ = ⊤
    · exact absurd (hinf hζ fun t => hlt t (by rw [hζ]; exact ENNReal.coe_lt_top)) not_false
    -- a finite lifetime: no threshold at the start, so `ζ > 0`, and the limit state is at the outer mark
    have hnothr0 : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR :=
      not_threshold_of_lt hκ hnL hF.1 hF.2.1 hF.2.2.1 hF.2.2.2 hxm hsR hpsL hpsR
    have hζ0 : ζ ≠ 0 := fun h0 => hnothr0 (hpF.threshold_of_eq_zero h0)
    set T := ζ.toNNReal with hT
    have hTe : (T : ℝ≥0∞) = ζ := ENNReal.coe_toNNReal hζ
    have hT0 : 0 < T := by
      rw [pos_iff_ne_zero]; intro h; rw [h] at hTe; exact hζ0 (by rw [← hTe]; rfl)
    obtain ⟨w₀, vL₀, vR₀, hl, hthr⟩ := hlim T hT0 hTe
    have hne : (𝓝[<] T).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hT0⟩
    have hbefore : ∀ᶠ t : ℝ≥0 in 𝓝[<] T, ((t : ℝ≥0) : ℝ≥0∞) < ζ := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      rw [← hTe]; exact_mod_cast ht
    have hw : Tendsto w (𝓝[<] T) (𝓝 w₀) := (continuous_fst.tendsto _).comp hl
    have hvl : ∀ i, Tendsto (fun t => vL i t) (𝓝[<] T) (𝓝 (vL₀ i)) := fun i =>
      ((continuous_apply i).comp (continuous_fst.comp continuous_snd)).continuousAt.tendsto.comp hl
    have hvr : ∀ j, Tendsto (fun t => vR j t) (𝓝[<] T) (𝓝 (vR₀ j)) := fun j =>
      ((continuous_apply j).comp (continuous_snd.comp continuous_snd)).continuousAt.tendsto.comp hl
    by_cases h0 : vL₀ ℓ = w₀
    · refine ⟨T, hT0, fun u hu => hlt u (by rw [← hTe]; exact_mod_cast hu), Or.inr ⟨hTe, ?_⟩⟩
      have := hw.sub (hvl ℓ)
      rwa [h0, sub_self] at this
    · exfalso
      refine not_threshold_of_lt hκ hnL (vL₀ := vL₀) (vR₀ := vR₀) ?_ ?_ ?_ ?_ ?_ hsR hpsL hpsR hthr
      · intro i j hij
        exact le_of_tendsto_of_tendsto (hvl j) (hvl i) (hbefore.mono fun t ht => hpF.antitone_vL ht hij)
      · intro i
        exact le_of_tendsto_of_tendsto (hvl i) hw (hbefore.mono fun t ht => hpF.vL_le_w ht i)
      · intro i j hij
        exact le_of_tendsto_of_tendsto (hvr i) (hvr j) (hbefore.mono fun t ht => hpF.monotone_vR ht hij)
      · intro j
        exact le_of_tendsto_of_tendsto hw (hvr j) (hbefore.mono fun t ht => hpF.w_le_vR ht j)
      · exact lt_of_le_of_ne (le_of_tendsto_of_tendsto (hvl ℓ) hw
          (hbefore.mono fun t ht => hpF.vL_le_w ht ℓ)) h0

/-- **"If the left total is at most `−2`, that far-left swallowing is its continuation threshold."** A contact of the
outermost left mark before the lifetime puts every left label at the driver, a group of weight `κ − 4 ≤ −2`, which is
a threshold; so the first contact is the lifetime. -/
theorem eq_zeta_of_isFirstFarContact (hnL : 0 < nL) (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ)
    (hsL : ∑ i, ρL i = κ - 4) (hκ2 : κ - 4 ≤ -2) {τ : ℝ≥0}
    (hτ : IsFirstFarContact w (vL ⟨nL - 1, Nat.sub_lt hnL one_pos⟩) ζ τ) : (τ : ℝ≥0∞) = ζ := by
  obtain ⟨-, -, ⟨hτζ, heq⟩ | ⟨hτζ, -⟩⟩ := hτ
  · exfalso
    have hpF := hp.isForcePath
    refine hpF.not_threshold hτζ (Or.inl ?_)
    have hall : univ.filter (fun i => vL i τ = w τ) = univ := by
      ext i
      simp only [mem_filter, mem_univ, true_and, iff_true]
      refine le_antisymm (hpF.vL_le_w hτζ i) ?_
      rw [← heq]
      exact hpF.antitone_vL hτζ (Fin.le_def.2 (by have := i.isLt; simp only; omega))
    rw [hall, hsL]
    exact hκ2
  · exact hτζ

end Path

/-! ### The named inputs -/

/-- The reference weights of a side: the total `s` on the outermost label, `0` on the others (passive marks). -/
def refW (n : ℕ) (s : ℝ) : Fin n → ℝ := fun i => if (i : ℕ) + 1 = n then s else 0

theorem sum_refW {n : ℕ} (hn : 0 < n) (s : ℝ) : ∑ i, refW n s i = s := by
  rw [Finset.sum_eq_single ⟨n - 1, Nat.sub_lt hn one_pos⟩]
  · simp only [refW]
    split_ifs with h
    · rfl
    · exfalso; apply h; show n - 1 + 1 = n; omega
  · intro i _ hi
    simp only [refW]
    split_ifs with h
    · exact absurd (Fin.ext (by simp only; omega)) hi
    · rfl
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **Named input: Aux. 22's full-span endpoint for the GB8 reference, driver form** (GB8 proof, p. 523: "This
two-mark reference has an almost surely finite first real endpoint strictly to the left of `a₋`: the strip calculation
in the proof of Proposition 5.9 applies directly … The full-span case of Aux. 22 gives a finite upper-strip endpoint,
hence the claimed finite first swallow of `a₋`"; "Retain all actual and reference marks, with zero weights where
needed"). For `0 < κ < 4` and an ordered word with marks off the seed carrying all left weight `κ − 4` on its
outermost left mark and all right weight `κ/2 − 2` on its outermost right mark (the other marks passive), almost
surely the outermost left mark is swallowed at a finite time: it meets the driver before the lifetime, or the lifetime
is finite (a continuation threshold). -/
def ReferenceSwallowStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (nL nR : ℕ) (hnL : 0 < nL), 0 < nR → ∀ (xL : Fin nL → ℝ) (xR : Fin nR → ℝ),
    IsOrderedForceWord xL xR → (∀ i, xL i < 0) → (∀ j, 0 < xR j) →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ)
      (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution κ xL xR (refW nL (κ - 4)) (refW nR (κ / 2 - 2)) P 𝓕 W VL VR B ζ →
      ∀ᵐ ω ∂P, ζ ω ≠ ⊤ ∨ ∃ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω ∧ VL ⟨nL - 1, Nat.sub_lt hnL one_pos⟩ t ω = W t ω

/-- **Named input: eventual separation on the no-contact event** (GB8 proof, p. 523: "On the event of no far-left
contact there is therefore no finite continuation threshold. The complete finite-force theorem makes the trace
transient to infinity on that event. Every real contact then lies in the fixed compact interval `[x₋, x₊]`, so a
sufficiently late rational own time `q` is an interior time after the last real contact"), driver form: for the GB8
word with a continuous trace through its lifetime, almost surely, if the lifetime is infinite and the outermost left
mark never meets the driver, then after some rational time every gap stays at least some `δ > 0` (the trace is
interior, and stays a positive distance from the compact boundary support, after `q`). -/
def EventualSepStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (nL nR : ℕ) (hnL : 0 < nL) (hnR : 0 < nR) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ)
    (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ),
    IsOrderedForceWord xL xR →
    xL ⟨nL - 1, Nat.sub_lt hnL one_pos⟩ < 0 → 0 < xR ⟨nR - 1, Nat.sub_lt hnR one_pos⟩ →
    ∑ i, ρL i = κ - 4 → ∑ j, ρR j = κ / 2 - 2 →
    (∀ i : Fin nL, (i : ℕ) < nL - 1 → -2 < ∑ l ∈ univ.filter (fun l => l ≤ i), ρL l) →
    (∀ j : Fin nR, (j : ℕ) < nR - 1 → -2 < ∑ l ∈ univ.filter (fun l => l ≤ j), ρR l) →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ)
      (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ →
      (∀ᵐ ω ∂P, ∃ γ : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) γ) →
      ∀ᵐ ω ∂P, ζ ω = ⊤ → (∀ t : ℝ≥0, VL ⟨nL - 1, Nat.sub_lt hnL one_pos⟩ t ω < W t ω) →
        ∃ q : ℚ≥0, 0 < q ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ≥0, (q : ℝ≥0) ≤ t → δ ≤ minGap (stateAt W VL VR t ω)

/-- **Named input: no contact with `[x₊, ∞)`** (GB8 proof, p. 523: "Lemma GB7a protects the open right tail, and G12
protects its junction `x₊` because `c_κ > d_κ`"), driver form: for the GB8 word with a continuous trace through its
lifetime, almost surely the outermost right mark never meets the driver before the lifetime. -/
def RightNoContactStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (nL nR : ℕ) (hnL : 0 < nL) (hnR : 0 < nR) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ)
    (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ),
    IsOrderedForceWord xL xR →
    xL ⟨nL - 1, Nat.sub_lt hnL one_pos⟩ < 0 → 0 < xR ⟨nR - 1, Nat.sub_lt hnR one_pos⟩ →
    ∑ i, ρL i = κ - 4 → ∑ j, ρR j = κ / 2 - 2 →
    (∀ i : Fin nL, (i : ℕ) < nL - 1 → -2 < ∑ l ∈ univ.filter (fun l => l ≤ i), ρL l) →
    (∀ j : Fin nR, (j : ℕ) < nR - 1 → -2 < ∑ l ∈ univ.filter (fun l => l ≤ j), ρR l) →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ)
      (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ →
      (∀ᵐ ω ∂P, ∃ γ : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) γ) →
      ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → W t ω < VR ⟨nR - 1, Nat.sub_lt hnR one_pos⟩ t ω

/-! ### The reference comparison -/

/-- The smallest gap is invariant under a common translation. -/
theorem minGap_sub {nL nR : ℕ} (a c : ℝ) (b : Fin nL → ℝ) (d : Fin nR → ℝ) :
    minGap ((a - c, fun i => b i - c, fun j => d j - c) : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)) =
      minGap ((a, b, d) : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)) := by
  unfold minGap
  congr 1
  funext k
  rcases k with _ | i | j
  · rfl
  · show |a - c - (b i - c)| = |a - b i|
    ring_nf
  · show |a - c - (d j - c)| = |a - d j|
    ring_nf

/-- **The GB8 reference leaves every buffer** (from `ReferenceSwallowStatement`): its canonical law gives `sepSet δ`
probability `0` from every ordered word with marks off the seed. -/
theorem codeLaw_sepSet_refW_eq_zero (hRef : ReferenceSwallowStatement.{0}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {nL nR : ℕ} (hnL : 0 < nL) (hnR : 0 < nR) {y : (Fin nL → ℝ) × (Fin nR → ℝ)} (hord : IsOrderedForceWord y.1 y.2)
    (hL0 : ∀ i, y.1 i < 0) (hR0 : ∀ j, 0 < y.2 j) {δ : ℝ} (hδ : 0 < δ) :
    codeLaw κ (refW nL (κ - 4)) (refW nR (κ / 2 - 2)) (sepSet δ) y = 0 := by
  obtain ⟨Ω', mΩ', P', hP', 𝓕', W', VL', VR', B', ζ', hE'⟩ :=
    exists_isIntegratedSLEEvolution_assembled hκ hord (ρL := refW nL (κ - 4)) (ρR := refW nR (κ / 2 - 2))
  have hsep : ∀ i j, y.1 i < y.2 j := fun i j => (hL0 i).trans (hR0 j)
  rw [← ZhanGT4.measure_eventOf_eq_codeLaw_state hκ hsep hE' (S := sepSet δ) (Ψ := SepForever δ)
    (measurableSet_sepSet δ) (fun x _ _ => mem_sepSet_iff x) sepForever_congr]
  refine measure_mono_null (fun ω hω => ?_)
    (ae_iff.1 ((hRef κ hκ hκ4 nL nR hnL hnR y.1 y.2 hord hL0 hR0 P' 𝓕' W' VL' VR' B' ζ' hE').and hE'.2.2.2.2))
  rintro ⟨hr, hp⟩
  obtain ⟨hζ, hq⟩ := hω
  rcases hr with hne | ⟨t, -, heq⟩
  · exact hne hζ
  have hpF := hp.isForcePath
  have hcon : ContinuousOn (fun s => stateAt W' VL' VR' s ω) {s : ℝ≥0 | (s : ℝ≥0∞) < ζ' ω} :=
    hpF.continuousOn_w.prodMk ((continuousOn_pi.2 hpF.continuousOn_vL).prodMk (continuousOn_pi.2 hpF.continuousOn_vR))
  have hc : Continuous fun s => minGap (stateAt W' VL' VR' s ω) := by
    rw [hζ] at hcon
    exact continuous_minGap.comp (continuousOn_univ.1 (hcon.mono fun _ _ => ENNReal.coe_lt_top))
  have h1 := le_of_forall_nnrat hc (fun q => hq q) t
  have h2 : minGap (stateAt W' VL' VR' t ω) ≤ 0 := by
    refine (Finset.inf'_le _ (Finset.mem_univ (some (Sum.inl ⟨nL - 1, Nat.sub_lt hnL one_pos⟩)))).trans
      (le_of_eq ?_)
    show |W' t ω - VL' ⟨nL - 1, Nat.sub_lt hnL one_pos⟩ t ω| = 0
    rw [heq, sub_self, abs_zero]
  linarith

/-- **GB8, first conclusion, from the two inputs of the far-left argument**: almost surely the outermost left mark
has a first contact with the driver at a finite time `τ > 0` (before or at the lifetime), and `τ = ζ` when
`κ − 4 ≤ −2`. -/
theorem ae_exists_isFirstFarContact (hRef : ReferenceSwallowStatement.{0}) (hSep : EventualSepStatement.{u})
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {nL nR : ℕ} (hnL : 0 < nL) (hnR : 0 < nR) {xL : Fin nL → ℝ}
    {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (hF : IsOrderedForceWord xL xR)
    (hxm : xL ⟨nL - 1, Nat.sub_lt hnL one_pos⟩ < 0) (hxp : 0 < xR ⟨nR - 1, Nat.sub_lt hnR one_pos⟩)
    (hsL : ∑ i, ρL i = κ - 4) (hsR : ∑ j, ρR j = κ / 2 - 2)
    (hpsL : ∀ i : Fin nL, (i : ℕ) < nL - 1 → -2 < ∑ l ∈ univ.filter (fun l => l ≤ i), ρL l)
    (hpsR : ∀ j : Fin nR, (j : ℕ) < nR - 1 → -2 < ∑ l ∈ univ.filter (fun l => l ≤ j), ρR l)
    {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (htr : ∀ᵐ ω ∂P, ∃ γ : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) γ) :
    ∀ᵐ ω ∂P, ∃ τ : ℝ≥0, IsFirstFarContact (fun t => W t ω) (fun t => VL ⟨nL - 1, Nat.sub_lt hnL one_pos⟩ t ω)
      (ζ ω) τ ∧ (κ - 4 ≤ -2 → (τ : ℝ≥0∞) = ζ ω) := by
  have : IsProbabilityMeasure P := hE.1.isProbabilityMeasure'
  have hLtot : ∑ i, refW nL (κ - 4) i = ∑ i, ρL i := by rw [sum_refW hnL, hsL]
  have hRtot : ∑ j, refW nR (κ / 2 - 2) j = ∑ j, ρR j := by rw [sum_refW hnR, hsR]
  -- after every rational time `q > 0`, the gaps do not stay at least `1/(n+1)` forever
  have hns : ∀ q : ℚ≥0, ∀ n : ℕ, ∀ᵐ ω ∂P, 0 < q → ¬ (ζ ω = ⊤ ∧
      ∀ t : ℝ≥0, (q : ℝ≥0) ≤ t → 1 / ((n : ℝ) + 1) ≤ minGap (stateAt W VL VR t ω)) := by
    intro q n
    by_cases hq : 0 < q
    swap
    · exact Eventually.of_forall fun _ h => absurd h hq
    have hδ : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hT : IsStoppingTime 𝓕 fun _ : Ω => (((q : ℝ≥0)) : WithTop ℝ≥0) := isStoppingTime_const 𝓕 _
    set A := {ω | ((q : ℝ≥0) : ℝ≥0∞) < ζ ω ∧ (fun p => -minGap p) (stateAt W VL VR (q : ℝ≥0) ω) < 0} with hAdef
    have hA : MeasurableSet[hT.measurableSpace] A := by
      rw [IsStoppingTime.measurableSpace_const]
      exact measurableSet_lt_zeta_and_lt hE.2.1 hE.2.2.1 hE.2.2.2.1 continuous_minGap.neg 0 (q : ℝ≥0)
    have hq0 : (0 : ℝ≥0) < (q : ℝ≥0) := by exact_mod_cast hq
    have hAoff : ∀ᵐ ω ∂P, ω ∈ A → (∀ i, VL i (q : ℝ≥0) ω < W (q : ℝ≥0) ω) ∧
        ∀ j, W (q : ℝ≥0) ω < VR j (q : ℝ≥0) ω := by
      filter_upwards [hE.2.2.2.2] with ω hp hωA
      obtain ⟨hqζ, hpos⟩ := hωA
      have hpos' : 0 < minGap (stateAt W VL VR (q : ℝ≥0) ω) := by
        have h : -minGap (stateAt W VL VR (q : ℝ≥0) ω) < 0 := hpos
        linarith
      have hpF := hp.isForcePath
      refine ⟨fun i => lt_of_le_of_ne (hpF.vL_le_w hqζ i) fun he => ?_,
        fun j => lt_of_le_of_ne (hpF.w_le_vR hqζ j) fun he => ?_⟩
      · have h : minGap (stateAt W VL VR (q : ℝ≥0) ω) ≤ gapOf (stateAt W VL VR (q : ℝ≥0) ω) (some (Sum.inl i)) :=
          Finset.inf'_le _ (Finset.mem_univ _)
        have : gapOf (stateAt W VL VR (q : ℝ≥0) ω) (some (Sum.inl i)) = 0 := by
          show |W (q : ℝ≥0) ω - VL i (q : ℝ≥0) ω| = 0
          rw [he, sub_self, abs_zero]
        linarith
      · have h : minGap (stateAt W VL VR (q : ℝ≥0) ω) ≤ gapOf (stateAt W VL VR (q : ℝ≥0) ω) (some (Sum.inr j)) :=
          Finset.inf'_le _ (Finset.mem_univ _)
        have : gapOf (stateAt W VL VR (q : ℝ≥0) ω) (some (Sum.inr j)) = 0 := by
          show |W (q : ℝ≥0) ω - VR j (q : ℝ≥0) ω| = 0
          rw [he, sub_self, abs_zero]
        linarith
    have hzero := measure_restart_sepForever_eq_zero (ρL' := refW nL (κ - 4)) (ρR' := refW nR (κ / 2 - 2)) hκ hE
      hT hA (fun ω hω => ⟨hω.1, Or.inl hq0⟩) hAoff hLtot hRtot hδ
      (fun y hord hL0 hR0 => codeLaw_sepSet_refW_eq_zero hRef hκ hκ4 hnL hnR hord hL0 hR0 hδ)
    rw [ae_iff]
    refine measure_mono_null (fun ω hω => ?_) hzero
    simp only [not_imp, not_not, Set.mem_ofPred_eq] at hω
    obtain ⟨-, hζ, hgap⟩ := hω
    refine ⟨⟨by rw [hζ]; exact ENNReal.coe_lt_top, ?_⟩, ?_⟩
    · have := hgap (q : ℝ≥0) le_rfl
      show -minGap (stateAt W VL VR (q : ℝ≥0) ω) < 0
      linarith
    · refine ⟨by rw [hζ]; exact ENNReal.top_sub_coe, fun q' => ?_⟩
      rw [minGap_sub]
      exact hgap _ le_self_add
  have hall : ∀ᵐ ω ∂P, ∀ q : ℚ≥0, ∀ n : ℕ, 0 < q → ¬ (ζ ω = ⊤ ∧
      ∀ t : ℝ≥0, (q : ℝ≥0) ≤ t → 1 / ((n : ℝ) + 1) ≤ minGap (stateAt W VL VR t ω)) := by
    rw [ae_all_iff]; intro q; rw [ae_all_iff]; exact hns q
  filter_upwards [hE.2.2.2.2, hE.ae_tendsto_threshold hκ,
    hSep κ hκ hκ4 nL nR hnL hnR xL xR ρL ρR hF hxm hxp hsL hsR hpsL hpsR P 𝓕 W VL VR B ζ hE htr, hall]
    with ω hp hlim hes hns'
  obtain ⟨τ, hτ⟩ := exists_isFirstFarContact hκ hnL hF hp hlim hxm hsR hpsL hpsR fun hζ hlt => by
    obtain ⟨q, hq0, δ, hδ, hgap⟩ := hes hζ hlt
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
    exact hns' q n hq0 ⟨hζ, fun t ht => hn.le.trans (hgap t ht)⟩
  exact ⟨τ, hτ, fun hk => eq_zeta_of_isFirstFarContact hnL hp hsL hk hτ⟩

/-- **Lemma GB8 from its three named inputs** (pp. 523–524): `ReferenceSwallowStatement` (the full-span case of
Aux. 22 for the two-mark reference), `EventualSepStatement` (transience of the complete finite-force flow on the
no-contact event, in driver form) and `RightNoContactStatement` (Lemmas GB7a and G12 at the right far mark). The
Aux. 108 comparison through the infinite stopping time, the exclusion of a finite threshold off the far-left mark, the
threshold sentence and the final crossing are proved. -/
theorem gb8Statement_of_inputs (hRef : ReferenceSwallowStatement.{0}) (hSep : EventualSepStatement.{u})
    (hRight : RightNoContactStatement.{u}) : GB8Statement.{u} := by
  intro κ hκ hκ4 nL nR hnL hnR xL xR ρL ρR hF hxm hxp hsL hsR hpsL hpsR Ω mΩ P 𝓕 W VL VR B ζ hE htr
  filter_upwards [ae_exists_isFirstFarContact hRef hSep hκ hκ4 hnL hnR hF hxm hxp hsL hsR hpsL hpsR hE htr,
    hRight κ hκ hκ4 nL nR hnL hnR xL xR ρL ρR hF hxm hxp hsL hsR hpsL hpsR P 𝓕 W VL VR B ζ hE htr,
    hE.2.2.2.2] with ω hc hr hp
  obtain ⟨τ, hτ, hthr⟩ := hc
  exact ⟨⟨τ, hτ, hthr⟩, hr, fun hx => exists_crossing_of_contact_path hp _ hx hτ⟩

end GB8

end Supp8

end InteractingSLE
