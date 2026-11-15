/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Frozen.Spec.IsIntegratedSLEEvolution
import InteractingSLE.Frozen.Spec.IsGeneratingTrace
import InteractingSLE.Frozen.Spec.IsOrderedForceWord
import InteractingSLE.Spec.Sec2.TerminalPath

/-!
# Lemma GB8 (a critical far-side word must reach its attracting tail)

Packet PROVE-T14-TIP. Specification supplement §8.8, **Lemma GB8** (`source/spec/p481-528.md` L1019–L1050,
pp. 523–524):

> Let `0 < κ < 4` and `c_κ = κ/2 − 2`. Consider a finite-force flow in `ℍ` with continuous trace, continued through its
> original lifetime. Fix separated original marks `x₋ < 0 < x₊` beyond which the boundary heights are constant. Suppose
> the total left and right weights are respectively `s_L = κ − 4`, `s_R = c_κ`, and every earlier side partial sum is
> strictly greater than `−2`. The initial seed groups, when present, are also admissible. Then the trace has an almost
> surely finite first contact with `(−∞, x₋)`, and it has no contact with `[x₊, ∞)`. If the left total is at most `−2`,
> that far-left swallowing is its continuation threshold. In particular, if `x₋ ≤ −3`, its continuous driver crosses
> `−(2 + 1/8)` strictly before that first contact.

## Driver form

The flow is an integrated `SLE_κ(ρ)` evolution (frozen `IsIntegratedSLEEvolution`) of an ordered word with
`n_L, n_R ≥ 1` labels whose outermost labels sit at `x₋ = x_{L,n_L−1} < 0` and `x₊ = x_{R,n_R−1} > 0` (the marks
beyond which the heights are constant), with a continuous generating trace through its lifetime. Contact of the trace
with `(−∞, x₋)` is the swallowing of `x₋`, i.e. the collision of its force coordinate `V^{L,n_L−1}` with the driver;
contact with `[x₊, ∞)` is the collision of `V^{R,n_R−1}` with the driver.

* `GB8Statement`: the lemma in this form (named statement; its proof needs the complete finite-force theorem
  (transience), the domain-Markov restart at a late rational interior time, Aux. 22's strip endpoint for the two-mark
  reference, and Aux. 108's whole-history finite-energy comparison — see the handoff);
* **`exists_crossing_of_contact`** (proved): the last sentence of the lemma from its first: "the protected left
  junction coordinate is nonincreasing until its first swallow. At the first far-left contact it equals the driver and
  is at most `x₋`. Driver continuity therefore gives the asserted strictly earlier crossing." Both a contact before
  the lifetime and a contact at the lifetime (a threshold) are covered.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology Finset
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Supp8

namespace GB8

/-- **First far-left contact**: the outermost left force coordinate meets the driver at the positive time `τ`, before
or at the lifetime, and not earlier. At `τ < ζ` this is the equality `V^{L,last}_τ = W_τ`; at `τ = ζ` it is the limit
of the gap from the left. -/
def IsFirstFarContact (w vl : ℝ≥0 → ℝ) (ζ : ℝ≥0∞) (τ : ℝ≥0) : Prop :=
  0 < τ ∧ (∀ u : ℝ≥0, u < τ → vl u < w u) ∧
    (((τ : ℝ≥0∞) < ζ ∧ vl τ = w τ) ∨
      ((τ : ℝ≥0∞) = ζ ∧ Tendsto (fun u => w u - vl u) (𝓝[<] τ) (𝓝 0)))

/-- **Named statement: Lemma GB8**, driver form (pp. 523–524). -/
def GB8Statement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (nL nR : ℕ) (hnL : 0 < nL) (hnR : 0 < nR) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ)
    (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ),
    IsOrderedForceWord xL xR →
    -- the separated outermost marks `x₋ < 0 < x₊`
    xL ⟨nL - 1, Nat.sub_lt hnL one_pos⟩ < 0 → 0 < xR ⟨nR - 1, Nat.sub_lt hnR one_pos⟩ →
    -- the totals `s_L = κ − 4`, `s_R = κ/2 − 2`
    ∑ i, ρL i = κ - 4 → ∑ j, ρR j = κ / 2 - 2 →
    -- every earlier side partial sum is greater than `−2`
    (∀ i : Fin nL, (i : ℕ) < nL - 1 → -2 < ∑ l ∈ univ.filter (fun l => l ≤ i), ρL l) →
    (∀ j : Fin nR, (j : ℕ) < nR - 1 → -2 < ∑ l ∈ univ.filter (fun l => l ≤ j), ρR l) →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ)
      (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ →
      -- the continuous trace, continued through the lifetime
      (∀ᵐ ω ∂P, ∃ γ : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) γ) →
      ∀ᵐ ω ∂P,
        -- an almost surely finite first contact with `(−∞, x₋)`
        (∃ τ : ℝ≥0, IsFirstFarContact (fun t => W t ω) (fun t => VL ⟨nL - 1, Nat.sub_lt hnL one_pos⟩ t ω)
            (ζ ω) τ ∧
          -- if the left total is at most `−2`, that swallowing is the continuation threshold
          (κ - 4 ≤ -2 → (τ : ℝ≥0∞) = ζ ω)) ∧
        -- no contact with `[x₊, ∞)`
        (∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → W t ω < VR ⟨nR - 1, Nat.sub_lt hnR one_pos⟩ t ω) ∧
        -- if `x₋ ≤ −3`, the driver crosses `−(2 + 1/8)` strictly before that first contact
        (xL ⟨nL - 1, Nat.sub_lt hnL one_pos⟩ ≤ -3 →
          ∃ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω ∧ W t ω < -(2 + 1 / 8) ∧
            ∀ u ≤ t, VL ⟨nL - 1, Nat.sub_lt hnL one_pos⟩ u ω < W u ω)

/-- **GB8, last sentence, from the first contact** (deterministic): if the driver is continuous before the
lifetime, the far-left coordinate is nonincreasing before the lifetime and starts at `x₋ ≤ −3`, then at a first
far-left contact `τ` the driver has crossed `−(2 + 1/8)` at some time `t < τ` (strictly before the contact, and before
the lifetime). -/
theorem exists_crossing_of_contact {w vl : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}
    (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) (hvl : ∀ s t : ℝ≥0, s ≤ t → (t : ℝ≥0∞) < ζ → vl t ≤ vl s)
    {xm : ℝ} (hvl0 : vl 0 = xm) (hxm : xm ≤ -3) {τ : ℝ≥0} (hτ : IsFirstFarContact w vl ζ τ) :
    ∃ t : ℝ≥0, (t : ℝ≥0∞) < ζ ∧ w t < -(2 + 1 / 8) ∧ ∀ u ≤ t, vl u < w u := by
  obtain ⟨hτ0, hbefore, hcon⟩ := hτ
  have hlt : ∀ u : ℝ≥0, u < τ → (u : ℝ≥0∞) < ζ := fun u hu => by
    rcases hcon with ⟨hτζ, -⟩ | ⟨hτζ, -⟩
    · exact lt_trans (by exact_mod_cast hu) hτζ
    · rw [← hτζ]; exact_mod_cast hu
  have hne : (𝓝[<] τ).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hτ0⟩
  -- the driver is eventually below `−(2 + 1/8)` before `τ`
  have hev : ∀ᶠ u in 𝓝[<] τ, w u < -(2 + 1 / 8) := by
    rcases hcon with ⟨hτζ, heq⟩ | ⟨-, h⟩
    · have hc : ContinuousAt w τ :=
        hw.continuousAt ((isOpen_lt ENNReal.continuous_coe continuous_const).mem_nhds hτζ)
      have hwτ : w τ < -(2 + 1 / 8) := by
        have := hvl 0 τ bot_le hτζ
        rw [hvl0] at this
        linarith
      exact (hc.eventually (gt_mem_nhds hwτ)).filter_mono nhdsWithin_le_nhds
    · filter_upwards [h.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num)), self_mem_nhdsWithin]
        with u hu hut
      have := hvl 0 u bot_le (hlt u hut)
      rw [hvl0] at this
      linarith
  obtain ⟨t, ht, htτ⟩ := (hev.and self_mem_nhdsWithin).exists
  exact ⟨t, hlt t htτ, ht, fun u hu => hbefore u (lt_of_le_of_lt hu htτ)⟩

/-- **GB8, last sentence, along an integrated path**: the far-left coordinate of an integrated path is nonincreasing and
its driver is continuous, so a first contact of a label starting at `x ≤ −3` is preceded by a crossing of
`−(2 + 1/8)`. -/
theorem exists_crossing_of_contact_path {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ}
    {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} (hP : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ) (i : Fin nL)
    (hx : xL i ≤ -3) {τ : ℝ≥0} (hτ : IsFirstFarContact w (vL i) ζ τ) :
    ∃ t : ℝ≥0, (t : ℝ≥0∞) < ζ ∧ w t < -(2 + 1 / 8) ∧ ∀ u ≤ t, vL i u < w u :=
  exists_crossing_of_contact hP.isForcePath.continuousOn_w
    (fun _ _ hst ht => hP.isForcePath.vL_le_of_le hst ht i) (hP.isForcePath.vL_zero i) hx hτ

end GB8

end Supp8

end InteractingSLE
