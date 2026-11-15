/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB8InputsRef
import InteractingSLE.Spec.Supplement.GB8EnergyCode

/-!
# Proposition 5.9's one-stage construction, step 1: the far-left swallow of a stage word from a separated start

Packet PROVE-PROP59T. Specification §5.2, proof of Proposition 5.9 (`source/spec/p097-144.md` L1002–L1016,
pp. 143–144):

> If we use the extreme angle `−e_jπ/2`, the full-span case of **Aux.** lemma 22 and the boundary calculation below
> show that the driver reaches `e_j(2 + 1/8)` before the trajectory hits the revealed counterflow or its continuation
> threshold. […] At angle `+π/2` […] their total left and right weights are `κ − 4` and `c = κ/2 − 2`. […] The
> remaining boundary is the lower strip boundary. Its finite force partial sums are at least `c`, including the far
> right total, so it has precisely the lower non-hitting data required by **Aux.** lemma 22. That lemma's full-span
> case gives an actual endpoint at a finite upper-strip point. Pulling back gives a first real endpoint strictly in
> `(−∞, x₋)`, not at `x₋` or infinity.

**Stage words.** An integrated `SLE_κ(ρ)` evolution whose last (outermost) left mark is `x₋` carries a *stage word*
(`IsStageWord`) when the total left and right weights are `κ − 4` and `κ/2 − 2` and Zhan's lower prefix sums hold:
every prefix sum of the left weights before the last one, and every prefix sum of the right weights, is at least
`κ/2 − 2` (`Strip.HasStripPrefixSums κ (Fin.init ρL) ρR`; the source's "finite force partial sums are at least `c`,
including the far right total"). Only the left total and the prefix sums enter this file. The charge
condition of Zhan's strip theorem is then automatic: `q₋ = κ − 4`, `q₊ = −2`, `|q₊ − q₋| = |2 − κ| < 2`
(`abs_charge_lt_of_sum`). Unlike Lemma GB8 (supplement §8.8, partial sums only `> −2`, whose proof goes through the
complete finite-force theorem), this regime needs neither transience nor Theorem 1.3: Aux. 22 applies to the word
itself.

## Main results

* `abs_charge_lt_of_sum`: the charge condition from the left total `κ − 4`;
* **`ae_swallow_of_strict`**: from a separated start with distinct positions (every left mark negative, every right
  mark positive), almost surely the lifetime is finite or the outermost left mark meets the driver before it
  (Aux. 22's strip endpoint for the reflected word, `Sec5.Aux22Strip.ae_exists_stripEnd_of_integrated`);
* `NoSwallow`, `noSwallowSet`, `measurableSet_noSwallowSet`, `mem_noSwallowSet_iff`: the complementary path event
  (infinite lifetime, the outermost left mark strictly left of the driver forever) and its Borel code set;
* **`codeLaw_noSwallowSet_eq_zero`**: its canonical law vanishes at every separated start with distinct positions.

Nothing here uses Theorem 1.2, Theorem 1.3 or any result taking them as hypotheses (ruling R48).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Finset
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Sec5

namespace Prop59Tips

open Sec2.Assembly Sec7.RandRestart

/-! ### The stage word -/

/-- **A stage word** (proof of Proposition 5.9, p. 144, at angle `+π/2`): the total left and right weights are
`κ − 4` and `c = κ/2 − 2`, and Zhan's lower prefix sums hold (every prefix sum of the left weights before the last
one, and of the right weights, is at least `κ/2 − 2`). -/
def IsStageWord (κ : ℝ) {j n : ℕ} (ρL : Fin (j + 1) → ℝ) (ρR : Fin n → ℝ) : Prop :=
  ∑ i, ρL i = κ - 4 ∧ Strip.HasStripPrefixSums κ (Fin.init ρL) ρR ∧ ∑ k, ρR k = κ / 2 - 2

/-- **The charge condition of a stage word**: `q₋ = κ − 4`, `q₊ = κ − 6 − q₋ = −2`, so `|q₊ − q₋| = |2 − κ| < 2`. -/
theorem abs_charge_lt_of_sum {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {j n : ℕ} {ρL : Fin (j + 1) → ℝ}
    (ρR : Fin n → ℝ) (hsL : ∑ i, ρL i = κ - 4) :
    |Strip.chargePlus κ (Fin.init ρL) ρR (ρL (Fin.last j)) -
      Strip.chargeMinus (Fin.init ρL) (ρL (Fin.last j))| < 2 := by
  have hm : Strip.chargeMinus (Fin.init ρL) (ρL (Fin.last j)) = κ - 4 := by
    rw [Strip.chargeMinus, ← hsL, Fin.sum_univ_castSucc]
    rfl
  have hsum := Strip.chargePlus_add_chargeMinus κ (Fin.init ρL) ρR (ρL (Fin.last j))
  rw [abs_lt]
  constructor <;> linarith

/-! ### The swallow from a separated start -/

/-- **The far-left swallow of a stage word from a separated start** (Aux. 22, full span, p. 144). For an integrated
`SLE_κ(ρ)` evolution, `0 < κ < 4`, of a stage word whose left positions are distinct and negative and whose right
positions are distinct and positive, almost surely the lifetime is finite or the outermost left mark meets the
driver before it ("Pulling back gives a first real endpoint strictly in `(−∞, x₋)`"). -/
theorem ae_swallow_of_strict {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {j n : ℕ} {xL : Fin (j + 1) → ℝ}
    {xR : Fin n → ℝ} {ρL : Fin (j + 1) → ℝ} {ρR : Fin n → ℝ} {Ω : Type u} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin (j + 1) → ℝ≥0 → Ω → ℝ} {VR : Fin n → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hxL : StrictAnti xL) (hxL0 : ∀ i, xL i < 0) (hxR : StrictMono xR) (hxR0 : ∀ k, 0 < xR k)
    (hw : IsStageWord κ ρL ρR) :
    ∀ᵐ ω ∂P, ζ ω ≠ ⊤ ∨ ∃ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω ∧ VL (Fin.last j) t ω = W t ω := by
  have hR := hE.reflect
  have h := Sec5.Aux22Strip.ae_exists_stripEnd_of_integrated (XL := -xR) (XR := -xL) hκ hκ4.le hR
    (by simpa using hxL0 (Fin.last j)) (fun a b hab => by simpa using hxL hab)
    (fun k => by simpa using hxL0 k.castSucc) (fun a b hab => by simpa using hxR hab)
    (fun k => by simpa using hxR0 k) hw.2.1 (abs_charge_lt_of_sum hκ hκ4 ρR hw.1)
  filter_upwards [h, hE.ae_isIntegratedSLEPath] with ω hω hp
  obtain ⟨S, -, -, -, -, hlife, -⟩ := hω
  by_cases hζ : ζ ω = ⊤
  · right
    have hnot : ¬ ∀ r ≤ S, VL (Fin.last j) r ω < W r ω := fun hall =>
      lt_irrefl S ((hlife S).1 ⟨by rw [hζ]; exact ENNReal.coe_lt_top, fun r hr => by simpa using hall r hr⟩)
    push Not at hnot
    obtain ⟨r, -, hr⟩ := hnot
    have hrζ : (r : ℝ≥0∞) < ζ ω := by rw [hζ]; exact ENNReal.coe_lt_top
    exact ⟨r, hrζ, le_antisymm (hp.isForcePath.vL_le_w hrζ (Fin.last j)) hr⟩
  · exact Or.inl hζ

/-! ### The no-swallow event, in countable form, and its code set -/

section Code

variable {nL nR : ℕ}

/-- **No swallow of the mark `ℓ`**, in countable form: infinite lifetime, and on each horizon `[0, N)` the gap
`w − v^{L,ℓ}` stays at least `1/(n + 1)` at the rational times. For continuous paths this is "infinite lifetime and
`v^{L,ℓ} < w` forever" (`noSwallowQ_of_forall_lt`, `forall_lt_of_noSwallowQ`). -/
def NoSwallowQ (ℓ : Fin nL) (w : ℝ≥0 → ℝ) (vL : Fin nL → ℝ≥0 → ℝ) (_vR : Fin nR → ℝ≥0 → ℝ) (τ : ℝ≥0∞) : Prop :=
  τ = ⊤ ∧ ∀ N : ℕ, ∃ n : ℕ, ∀ p : ℚ≥0, (p : ℝ≥0) < N → 1 / ((n : ℝ) + 1) ≤ w p - vL ℓ p

/-- The Borel code set of `NoSwallowQ`. -/
def noSwallowSet (ℓ : Fin nL) : Set (XCode nL nR) := {x | NoSwallowQ ℓ (cw x) (cvL x) (cvR x) (cζ x)}

theorem measurableSet_noSwallowSet (ℓ : Fin nL) : MeasurableSet (noSwallowSet (nR := nR) ℓ) := by
  have e : noSwallowSet (nR := nR) ℓ = {x | cζ x = ⊤} ∩ ⋂ N : ℕ, ⋃ n : ℕ,
      {x : XCode nL nR | ∀ p : ℚ≥0, (p : ℝ≥0) < N → 1 / ((n : ℝ) + 1) ≤ cw x p - cvL x ℓ p} := by
    ext x; simp [noSwallowSet, NoSwallowQ]
  rw [e]
  refine (measurableSet_eq_fun measurable_cζ measurable_const).inter
    (MeasurableSet.iInter fun N => MeasurableSet.iUnion fun n => ?_)
  exact measurableSet_setOfPred.2 (Measurable.forall fun _ => measurable_const_imp _ (measurableSet_setOfPred.1
    (measurableSet_le measurable_const ((measurable_cw_at _).sub (measurable_cvL_at ℓ _)))))

/-- `NoSwallowQ` depends only on the paths before the lifetime (here: everywhere, the lifetime being infinite). -/
theorem noSwallowQ_congr (ℓ : Fin nL) (w w' : ℝ≥0 → ℝ) (vL vL' : Fin nL → ℝ≥0 → ℝ) (vR vR' : Fin nR → ℝ≥0 → ℝ)
    (τ : ℝ≥0∞) (h : ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ → w t = w' t ∧ (∀ i, vL i t = vL' i t) ∧ ∀ j, vR j t = vR' j t)
    (hs : NoSwallowQ ℓ w vL vR τ) : NoSwallowQ ℓ w' vL' vR' τ := by
  obtain ⟨hτ, hq⟩ := hs
  refine ⟨hτ, fun N => ?_⟩
  obtain ⟨n, hn⟩ := hq N
  refine ⟨n, fun p hp => ?_⟩
  obtain ⟨h1, h2, -⟩ := h p (by rw [hτ]; exact ENNReal.coe_lt_top)
  rw [← h1, ← h2 ℓ]
  exact hn p hp

/-- For continuous paths, "`v^{L,ℓ} < w` forever" gives the countable form. -/
theorem noSwallowQ_of_forall_lt {ℓ : Fin nL} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} (vR : Fin nR → ℝ≥0 → ℝ)
    (hw : Continuous w) (hv : Continuous (vL ℓ)) (hlt : ∀ t, vL ℓ t < w t) :
    NoSwallowQ ℓ w vL vR ⊤ := by
  refine ⟨rfl, fun N => ?_⟩
  have hc : ContinuousOn (fun t => w t - vL ℓ t) (Icc 0 (N : ℝ≥0)) := (hw.sub hv).continuousOn
  obtain ⟨t₀, ht₀, hmin⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := (N : ℝ≥0))).exists_isMinOn
    ⟨0, le_rfl, zero_le⟩ hc
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 (hlt t₀))
  exact ⟨n, fun p hp => hn.le.trans (hmin ⟨zero_le, hp.le⟩)⟩

/-- For continuous paths the countable form gives "`v^{L,ℓ} < w` forever". -/
theorem forall_lt_of_noSwallowQ {ℓ : Fin nL} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ}
    {τ : ℝ≥0∞} (hw : Continuous w) (hv : Continuous (vL ℓ)) (hs : NoSwallowQ ℓ w vL vR τ) (t : ℝ≥0) :
    vL ℓ t < w t := by
  obtain ⟨n, hn⟩ := hs.2 (⌈(t : ℝ)⌉₊ + 1)
  have htN : t < ((⌈(t : ℝ)⌉₊ + 1 : ℕ) : ℝ≥0) := by
    have : (t : ℝ) < ((⌈(t : ℝ)⌉₊ + 1 : ℕ) : ℝ) := by
      push_cast; linarith [Nat.le_ceil (t : ℝ)]
    exact_mod_cast this
  have h1 := Supp8.GB8.le_of_forall_nnrat_lt (hw.sub hv) (fun q hq' => hn q hq') htN
  have h3 : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  have h1' : 1 / ((n : ℝ) + 1) ≤ w t - vL ℓ t := h1
  linarith

/-- **The canonical law of a stage word gives the no-swallow code set probability `0`** from every separated start
with distinct positions (`ae_swallow_of_strict` on the canonical evolution). -/
theorem codeLaw_noSwallowSet_eq_zero {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {j n : ℕ} {ρL : Fin (j + 1) → ℝ}
    {ρR : Fin n → ℝ} (hw : IsStageWord κ ρL ρR) {y : (Fin (j + 1) → ℝ) × (Fin n → ℝ)}
    (hyL : StrictAnti y.1) (hyL0 : ∀ i, y.1 i < 0) (hyR : StrictMono y.2) (hyR0 : ∀ k, 0 < y.2 k) :
    codeLaw κ ρL ρR (noSwallowSet (Fin.last j)) y = 0 := by
  have hord : IsOrderedForceWord y.1 y.2 :=
    ⟨hyL.antitone, fun i => (hyL0 i).le, hyR.monotone, fun k => (hyR0 k).le⟩
  obtain ⟨Ω', mΩ', P', hP', 𝓕', W', VL', VR', B', ζ', hE'⟩ :=
    exists_isIntegratedSLEEvolution_assembled hκ hord (ρL := ρL) (ρR := ρR)
  have hsep : ∀ i k, y.1 i < y.2 k := fun i k => (hyL0 i).trans (hyR0 k)
  rw [← ZhanGT4.measure_eventOf_eq_codeLaw_state hκ hsep hE' (S := noSwallowSet (Fin.last j))
    (Ψ := NoSwallowQ (Fin.last j)) (measurableSet_noSwallowSet (Fin.last j)) (fun x _ _ => Iff.rfl)
    (noSwallowQ_congr (Fin.last j))]
  refine measure_mono_null (fun ω hω => ?_)
    (ae_iff.1 ((ae_swallow_of_strict hκ hκ4 hE' hyL hyL0 hyR hyR0 hw).and hE'.2.2.2.2))
  rintro ⟨hr, hp⟩
  have hω' := hω
  obtain ⟨hζ, -⟩ := hω
  rcases hr with hne | ⟨t, -, heq⟩
  · exact hne hζ
  have hpF := hp.isForcePath
  have hwc : Continuous fun s => W' s ω := by
    have h := hpF.continuousOn_w
    rw [hζ] at h
    exact continuousOn_univ.1 (h.mono fun _ _ => ENNReal.coe_lt_top)
  have hvc : Continuous fun s => VL' (Fin.last j) s ω := by
    have h := hpF.continuousOn_vL (Fin.last j)
    rw [hζ] at h
    exact continuousOn_univ.1 (h.mono fun _ _ => ENNReal.coe_lt_top)
  have := forall_lt_of_noSwallowQ (ℓ := Fin.last j) (w := fun s => W' s ω) (vL := fun i s => VL' i s ω)
    (vR := fun k s => VR' k s ω) hwc hvc hω' t
  rw [heq] at this
  exact lt_irrefl _ this

end Code

end Prop59Tips

end Sec5

end InteractingSLE
