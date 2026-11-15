/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop59StageUnit
import InteractingSLE.Spec.Sec5.Grid
import InteractingSLE.Spec.Supplement.GB9CapStages
import InteractingSLE.Spec.Supplement.GW2TipCanonSkel

/-!
# Proposition 5.9's stage experiment: switching, the stage system, one-stage estimates

Packet PROVE-PROP59T2. Specification §5.2, proof of Proposition 5.9, pp. 143–147. At depth `j` (stage `j + 1`) the
target level is `−2` for even `j` (angle `+π/2`) and `+2` for odd `j` (angle `−π/2`), with target band
`I = (level − 1/4, level + 1/4)` (`I₋`, `I₊`).

**The switch** (pp. 145–146, "We must switch at a time in `Q`, measured in the original clock"): with the grid
`G n` of mesh `δ n` in `Q` (original clock), the stage succeeds at grid index `n` if at some piece time `s` whose
original-clock time `clk s` is a grid point, the piece is alive, its absolute driver is in the target band and it has
not touched its far mark; the switching time is such an `s` for the least grid point (`swT`). Every successful finite
prefix therefore switches at times of `Q`. The source rounds the hitting time of the exact level up to the grid; we
switch at the first grid time inside the band, which has the same properties (a grid time of `Q`, chosen before the
next piece is explored, success probability tending to one as the mesh shrinks) and needs no rounding lemma.

**The stage system** (`IsStageSystem`): the structural facts of the realized construction for every rule `r` (the
grid index used at each stage): coherence in the rule, monotone pasts, the reached events `R (j + 1) = R j ∩ succ`,
the next start (the state at the switch with the two new marks at the driver), measurability of the switch events,
the original clock, the initial dilation (`z₋ ≤ −3`, `z₊ ≥ 3`), and the link of the realized prefix with the light
cone's nodes (its `ψ`-trace on `[0, Σ switches]` is a Loewner trace inside the closure of the nodes' images).

**One-stage estimates** from the stage law:
* `ae_eventually_succ`: almost surely on `R j`, the stage succeeds for every large grid index (crossing by
  `compPremise_crossL/R` + the band-and-grid argument);
* `le_measure_unit`: at the even stages `j = 2k + 3`, every past event `A` has `p₀ P(A) ≤ P(A ∩ (abort ∪ unit))`
  (`exists_compPremise_unit`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec5

namespace Prop59Stage

/-! ### Bands and grids -/

/-- The target level at depth `j`: `−2` for even `j`, `2` for odd `j`. -/
def level (j : ℕ) : ℝ := if Even j then -2 else 2

/-- The target band at depth `j`. -/
def band (j : ℕ) : Set ℝ := Ioo (level j - 1 / 4) (level j + 1 / 4)

theorem band_even {j : ℕ} (hj : Even j) : band j = Ioo (-(9 / 4)) (-(7 / 4)) := by
  simp only [band, level, hj, ↓reduceIte]; congr 1 <;> norm_num

theorem band_odd {j : ℕ} (hj : ¬ Even j) : band j = Ioo (7 / 4) (9 / 4) := by
  simp only [band, level, hj, ↓reduceIte]; congr 1 <;> norm_num

/-- A grid of mesh `δ < y − x` (with `0 ≤ x`) has a point strictly between `x` and `y`. -/
theorem exists_grid_btwn {Q : Set ℝ≥0} {δ : ℝ≥0} {g : ℕ → ℝ≥0} (hg : IsSwitchGrid Q δ g) {x y : ℝ≥0}
    (hxy : x + δ < y) : ∃ k, x < g k ∧ g k < y := by
  classical
  have hex : ∃ k, x < g k := (hg.tendsto.eventually (eventually_gt_atTop x)).exists
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
  · rw [h0]
    exact lt_of_le_of_lt (hg.zero_le.trans le_add_self) hxy
  · obtain ⟨k, hk⟩ : ∃ k, Nat.find hex = k + 1 := ⟨Nat.find hex - 1, by omega⟩
    have hle : g k ≤ x := not_lt.1 (Nat.find_min hex (by omega))
    rw [hk]
    exact lt_of_le_of_lt ((hg.succ_le k).trans (by simpa only [add_comm] using add_le_add_right hle δ)) hxy

/-- **A crossing spends a time interval in the band**: a function continuous on `[0, t]` with values on opposite
sides of `L` at `0` and `t` stays within `1/4` of `L` on a nondegenerate interval `[t₁, t₂] ⊆ [0, t]`. -/
theorem exists_band_interval {f : ℝ≥0 → ℝ} {t : ℝ≥0} (hf : ContinuousOn f (Icc 0 t)) {L : ℝ}
    (hcross : (f 0 - L) * (f t - L) < 0) :
    ∃ t₁ t₂ : ℝ≥0, t₁ < t₂ ∧ t₂ ≤ t ∧ ∀ u ∈ Icc t₁ t₂, |f u - L| < 1 / 4 := by
  have hL : L ∈ uIcc (f 0) (f t) := by
    rcases lt_or_gt_of_ne (show f 0 - L ≠ 0 from fun h => by rw [h, zero_mul] at hcross; exact lt_irrefl _ hcross)
      with h | h
    · have : 0 < f t - L := by nlinarith
      exact mem_uIcc.2 (Or.inl ⟨by linarith, by linarith⟩)
    · have : f t - L < 0 := by nlinarith
      exact mem_uIcc.2 (Or.inr ⟨by linarith, by linarith⟩)
  obtain ⟨t₀, ht₀, hft₀⟩ := intermediate_value_uIcc (a := (0 : ℝ≥0)) (b := t)
    (hf.mono (by rw [uIcc_of_le zero_le])) hL
  rw [uIcc_of_le zero_le] at ht₀
  have ht₀t : t₀ < t := by
    refine lt_of_le_of_ne ht₀.2 fun h => ?_
    rw [h] at hft₀; rw [hft₀, sub_self, mul_zero] at hcross; exact lt_irrefl _ hcross
  have hc : ContinuousWithinAt f (Icc 0 t) t₀ := hf t₀ ht₀
  have hev : ∀ᶠ u in 𝓝[Icc 0 t] t₀, |f u - L| < 1 / 4 := by
    have : Tendsto (fun u => f u - L) (𝓝[Icc 0 t] t₀) (𝓝 0) := by
      have := hc.tendsto.sub_const L; rwa [hft₀, sub_self] at this
    exact (this.abs.eventually (gt_mem_nhds (by norm_num : |(0 : ℝ)| < 1 / 4))).mono fun u hu => by
      simpa using hu
  obtain ⟨V, hV, hVsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hev
  obtain ⟨c, hc, hcsub⟩ := exists_Ico_subset_of_mem_nhds hV ⟨t, ht₀t⟩
  obtain ⟨t₂, ht₂1, ht₂2⟩ := exists_between (lt_min hc ht₀t)
  refine ⟨t₀, t₂, ht₂1, ht₂2.le.trans (min_le_right _ _), fun u hu => ?_⟩
  have huc : u < c := lt_of_le_of_lt hu.2 (ht₂2.trans_le (min_le_left _ _))
  have hut : u ≤ t := hu.2.trans (ht₂2.le.trans (min_le_right _ _))
  exact hVsub ⟨hcsub ⟨hu.1, huc⟩, zero_le, hut⟩

/-! ### The switch -/

section Switch

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {nL₀ nR₀ : ℕ}

/-- The far gap at depth `j`: `W − V^L_far` for a leftward stage, `V^R_far − W` for a rightward one. -/
def farGap (hnL : 0 < nL₀) (hnR : 0 < nR₀) (j : ℕ) (d : StageData Ω (nL₀ + j) (nR₀ + j)) (ω : Ω) (u : ℝ≥0) : ℝ :=
  if Even j then d.W u ω - d.VL (farL (by omega : 0 < nL₀ + j)) u ω
  else d.VR (farR (by omega : 0 < nR₀ + j)) u ω - d.W u ω

/-- **The switching condition at a piece time `s`**: alive, absolute driver in the target band, no far contact up to
`s`. -/
def SwCond (hnL : 0 < nL₀) (hnR : 0 < nR₀) (j : ℕ) (d : StageData Ω (nL₀ + j) (nR₀ + j)) (ω : Ω) (s : ℝ≥0) :
    Prop :=
  (s : ℝ≥0∞) < d.ζ ω ∧ (d.y ω).1 + d.W s ω ∈ band j ∧ ∀ u ≤ s, 0 < farGap hnL hnR j d ω u

/-- **The stage succeeds at grid index `n`**: some piece time with a grid point of `G n` as original-clock time
satisfies the switching condition. -/
def succSet (G : ℕ → ℕ → ℝ≥0) (hnL : 0 < nL₀) (hnR : 0 < nR₀) (j : ℕ) (d : StageData Ω (nL₀ + j) (nR₀ + j))
    (n : ℕ) : Set Ω :=
  {ω | ∃ k : ℕ, ∃ s : ℝ≥0, d.clk ω s = G n k ∧ SwCond hnL hnR j d ω s}

open Classical in
/-- **The switching time**: a piece time realizing the least successful grid point (`0` if the stage fails). -/
def swT (G : ℕ → ℕ → ℝ≥0) (hnL : 0 < nL₀) (hnR : 0 < nR₀) (j : ℕ) (d : StageData Ω (nL₀ + j) (nR₀ + j)) (n : ℕ)
    (ω : Ω) : ℝ≥0 :=
  if h : ω ∈ succSet G hnL hnR j d n then Classical.choose (Nat.find_spec h) else 0

omit mΩ in
theorem swT_spec {G : ℕ → ℕ → ℝ≥0} {hnL : 0 < nL₀} {hnR : 0 < nR₀} {j : ℕ} {d : StageData Ω (nL₀ + j) (nR₀ + j)}
    {n : ℕ} {ω : Ω} (h : ω ∈ succSet G hnL hnR j d n) :
    SwCond hnL hnR j d ω (swT G hnL hnR j d n ω) ∧ ∃ k, d.clk ω (swT G hnL hnR j d n ω) = G n k := by
  classical
  have hs := Classical.choose_spec (Nat.find_spec h)
  have e : swT G hnL hnR j d n ω = Classical.choose (Nat.find_spec h) := by
    simp only [swT, h, ↓reduceDIte]
  rw [e]
  exact ⟨hs.2, _, hs.1⟩

/-- **The next start**: the absolute driver at the switch, and the relative positions at the switch with one new
mark on each side at the driver (index `0`). -/
def nextStart (G : ℕ → ℕ → ℝ≥0) (hnL : 0 < nL₀) (hnR : 0 < nR₀) (j : ℕ) (d : StageData Ω (nL₀ + j) (nR₀ + j))
    (n : ℕ) (ω : Ω) : Start (nL₀ + (j + 1)) (nR₀ + (j + 1)) :=
  ((d.y ω).1 + d.W (swT G hnL hnR j d n ω) ω,
    Fin.cons 0 fun i => d.VL i (swT G hnL hnR j d n ω) ω - d.W (swT G hnL hnR j d n ω) ω,
    Fin.cons 0 fun k => d.VR k (swT G hnL hnR j d n ω) ω - d.W (swT G hnL hnR j d n ω) ω)

omit mΩ in
theorem nextStart_fst (G : ℕ → ℕ → ℝ≥0) (hnL : 0 < nL₀) (hnR : 0 < nR₀) (j : ℕ)
    (d : StageData Ω (nL₀ + j) (nR₀ + j)) (n : ℕ) (ω : Ω) :
    (nextStart G hnL hnR j d n ω).1 = (d.y ω).1 + d.W (swT G hnL hnR j d n ω) ω := rfl

omit mΩ in
theorem nextStart_farL (G : ℕ → ℕ → ℝ≥0) (hnL : 0 < nL₀) (hnR : 0 < nR₀) (j : ℕ)
    (d : StageData Ω (nL₀ + j) (nR₀ + j)) (n : ℕ) (ω : Ω) (p : 0 < nL₀ + (j + 1)) :
    (nextStart G hnL hnR j d n ω).2.1 (farL p) =
      d.VL (farL (Nat.lt_of_lt_of_le hnL (Nat.le_add_right nL₀ j))) (swT G hnL hnR j d n ω) ω -
        d.W (swT G hnL hnR j d n ω) ω := by
  have h1 : (farL p : Fin (nL₀ + (j + 1))) = (farL (Nat.lt_of_lt_of_le hnL (Nat.le_add_right nL₀ j))).succ :=
    Fin.ext (by simp only [farL, Fin.val_succ]; omega)
  rw [h1]
  rfl

omit mΩ in
theorem nextStart_farR (G : ℕ → ℕ → ℝ≥0) (hnL : 0 < nL₀) (hnR : 0 < nR₀) (j : ℕ)
    (d : StageData Ω (nL₀ + j) (nR₀ + j)) (n : ℕ) (ω : Ω) (p : 0 < nR₀ + (j + 1)) :
    (nextStart G hnL hnR j d n ω).2.2 (farR p) =
      d.VR (farR (Nat.lt_of_lt_of_le hnR (Nat.le_add_right nR₀ j))) (swT G hnL hnR j d n ω) ω -
        d.W (swT G hnL hnR j d n ω) ω := by
  have h1 : (farR p : Fin (nR₀ + (j + 1))) = (farR (Nat.lt_of_lt_of_le hnR (Nat.le_add_right nR₀ j))).succ :=
    Fin.ext (by simp only [farR, Fin.val_succ]; omega)
  rw [h1]
  rfl

omit mΩ in
theorem nextStart_R_zero (G : ℕ → ℕ → ℝ≥0) (hnL : 0 < nL₀) (hnR : 0 < nR₀) (j : ℕ)
    (d : StageData Ω (nL₀ + j) (nR₀ + j)) (n : ℕ) (ω : Ω) : (nextStart G hnL hnR j d n ω).2.2 0 = 0 := rfl

omit mΩ in
theorem nextStart_R_succ (G : ℕ → ℕ → ℝ≥0) (hnL : 0 < nL₀) (hnR : 0 < nR₀) (j : ℕ)
    (d : StageData Ω (nL₀ + j) (nR₀ + j)) (n : ℕ) (ω : Ω) (m : Fin (nR₀ + j)) :
    (nextStart G hnL hnR j d n ω).2.2 m.succ =
      d.VR m (swT G hnL hnR j d n ω) ω - d.W (swT G hnL hnR j d n ω) ω := rfl

/-- The realized total `ψ`-capacity time after the first `m` stages under the rule `r`. -/
def capT (G : ℕ → ℕ → ℝ≥0) (hnL : 0 < nL₀) (hnR : 0 < nR₀) (sys : StageSys Ω nL₀ nR₀) (r : ℕ → ℕ) (m : ℕ)
    (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range m, (swT G hnL hnR i (sys r i) (r i) ω : ℝ)

end Switch

/-! ### The stage system -/

/-- **The structural facts of the realized alternating construction** (fixed counterflow time `r` and root), for
switching grids `G n` of mesh `δ n → 0` in the prescribed set `Q` (original clock) and node images `C ω` (the `ψ`-images
of the light cone's nodes in the remaining domain). -/
structure IsStageSystem {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) {nL₀ nR₀ : ℕ} (hnL : 0 < nL₀)
    (hnR : 0 < nR₀) (Q : Set ℝ≥0) (δ : ℕ → ℝ≥0) (G : ℕ → ℕ → ℝ≥0) (sys : StageSys Ω nL₀ nR₀)
    (C : Ω → Set ℂ) : Prop where
  /-- The grids. -/
  grid : ∀ n, IsSwitchGrid Q (δ n) (G n)
  /-- The meshes shrink. -/
  mesh : Tendsto δ atTop (𝓝 0)
  /-- Stage `j` depends only on the grid indices of the earlier stages. -/
  coh : ∀ r r' : ℕ → ℕ, ∀ j, (∀ i < j, r i = r' i) → sys r j = sys r' j
  /-- The pasts are sub-σ-algebras. -/
  past_le : ∀ r j, (sys r j).past ≤ mΩ
  /-- The pasts increase. -/
  past_mono : ∀ r j, (sys r j).past ≤ (sys r (j + 1)).past
  /-- The stage is reached on an event of its past. -/
  R_meas : ∀ r j, MeasurableSet[(sys r j).past] (sys r j).R
  /-- The next stage is reached iff this one is reached and succeeds. -/
  R_succ : ∀ r j, (sys r (j + 1)).R = (sys r j).R ∩ succSet G hnL hnR j (sys r j) (r j)
  /-- The next start is the state at the switch with the new marks at the driver. -/
  y_next : ∀ r j, ∀ᵐ ω ∂P, ω ∈ (sys r (j + 1)).R → (sys r (j + 1)).y ω = nextStart G hnL hnR j (sys r j) (r j) ω
  /-- The success of a stage, and a success after a unit of `ψ`-time, are known at the next stage. -/
  succ_meas : ∀ r j, MeasurableSet[(sys r (j + 1)).past] (succSet G hnL hnR j (sys r j) (r j)) ∧
    MeasurableSet[(sys r (j + 1)).past]
      {ω | ω ∈ succSet G hnL hnR j (sys r j) (r j) ∧ 1 ≤ swT G hnL hnR j (sys r j) (r j) ω}
  /-- The start and the samples of the piece are measurable. -/
  meas : ∀ r j, Measurable (sys r j).y ∧
    Measurable fun ω => samp ((sys r j).W · ω) (fun i t => (sys r j).VL i t ω) (fun k t => (sys r j).VR k t ω)
      ((sys r j).ζ ω)
  /-- The original clock is continuous and strictly increasing. -/
  clk : ∀ r j, ∀ᵐ ω ∂P, ω ∈ (sys r j).R → Continuous ((sys r j).clk ω) ∧ StrictMono ((sys r j).clk ω)
  /-- The initial dilation: the driver starts at `0`, the far marks beyond `∓3`. -/
  init : ∀ r, ∀ᵐ ω ∂P, ω ∈ (sys r 0).R → ((sys r 0).y ω).1 = 0 ∧
    ((sys r 0).y ω).1 + ((sys r 0).y ω).2.1 (farL (by omega : 0 < nL₀ + 0)) ≤ -3 ∧
    3 ≤ ((sys r 0).y ω).1 + ((sys r 0).y ω).2.2 (farR (by omega : 0 < nR₀ + 0))
  /-- The realized successful prefix is a Loewner trace in `ψ`-coordinates (capacity time `Σ switches`) inside the
  closure of the node images. -/
  chain : ∀ r j, ∀ᵐ ω ∂P, ω ∈ (sys r (j + 1)).R → ∃ (W' : ℝ → ℝ) (η : ℝ → ℂ) (T : ℝ), Continuous W' ∧ W' 0 = 0 ∧
    IsLoewnerTraceLT W' T η ∧ capT G hnL hnR sys r (j + 1) ω < T ∧
    η '' Icc 0 (capT G hnL hnR sys r (j + 1) ω) ⊆ closure (C ω)

/-! ### Invariants of the realized construction -/

section Invariants

variable {κ : ℝ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {nL₀ nR₀ : ℕ} {hnL : 0 < nL₀}
  {hnR : 0 < nR₀} {Q : Set ℝ≥0} {δ : ℕ → ℝ≥0} {G : ℕ → ℕ → ℝ≥0} {sys : StageSys Ω nL₀ nR₀} {C : Ω → Set ℂ}
  {ρL₀ : Fin nL₀ → ℝ} {ρR₀ : Fin nR₀ → ℝ}

theorem farL_succ (_h : 0 < nL₀) (j : ℕ) :
    (farL (by omega : 0 < nL₀ + (j + 1)) : Fin (nL₀ + (j + 1))) = (farL (by omega : 0 < nL₀ + j)).succ := by
  ext; simp only [farL, Fin.val_succ]; omega

theorem farR_succ (_h : 0 < nR₀) (j : ℕ) :
    (farR (by omega : 0 < nR₀ + (j + 1)) : Fin (nR₀ + (j + 1))) = (farR (by omega : 0 < nR₀ + j)).succ := by
  ext; simp only [farR, Fin.val_succ]; omega

/-- The pathwise clause of the stage law at every stage. -/
theorem ae_path (hL : Prop59StageLawStatement κ P ρL₀ ρR₀ sys) (r : ℕ → ℕ) (j : ℕ) :
    ∀ᵐ ω ∂P, ω ∈ (sys r j).R → IsOrderedForceWord ((sys r j).y ω).2.1 ((sys r j).y ω).2.2 ∧
      StrictAnti ((sys r j).y ω).2.1 ∧ StrictMono ((sys r j).y ω).2.2 ∧
      IsIntegratedSLEPath κ ((sys r j).y ω).2.1 ((sys r j).y ω).2.2 (stageρL κ ρL₀ j) (stageρR κ ρR₀ j)
        ((sys r j).W · ω) (fun i t => (sys r j).VL i t ω) (fun k t => (sys r j).VR k t ω) ((sys r j).B · ω)
        ((sys r j).ζ ω) :=
  (hL r j).1

/-- **The invariant**: the start lies within `9/4` of `0` (in the band of the previous switch), on the far side of the
coming target, and the far marks stay beyond `∓3`. -/
def StageInv (hL0 : 0 < nL₀) (hR0 : 0 < nR₀) (j : ℕ) (y : Start (nL₀ + j) (nR₀ + j)) : Prop :=
  -(9 / 4) < y.1 ∧ y.1 < 9 / 4 ∧ (Even j → -(7 / 4) < y.1) ∧ (¬ Even j → y.1 < 7 / 4) ∧
    y.1 + y.2.1 (farL (Nat.lt_of_lt_of_le hL0 (Nat.le_add_right nL₀ j))) ≤ -3 ∧
    3 ≤ y.1 + y.2.2 (farR (Nat.lt_of_lt_of_le hR0 (Nat.le_add_right nR₀ j)))

theorem ae_stageInv (hL : Prop59StageLawStatement κ P ρL₀ ρR₀ sys) (hS : IsStageSystem P hnL hnR Q δ G sys C)
    (r : ℕ → ℕ) (j : ℕ) : ∀ᵐ ω ∂P, ω ∈ (sys r j).R → StageInv hnL hnR j ((sys r j).y ω) := by
  induction j with
  | zero =>
    filter_upwards [hS.init r] with ω h hω
    obtain ⟨h0, hl, hr⟩ := h hω
    refine ⟨by rw [h0]; norm_num, by rw [h0]; norm_num, fun _ => by rw [h0]; norm_num, fun h => absurd ⟨0, rfl⟩ h,
      hl, hr⟩
  | succ j ih =>
    filter_upwards [ih, ae_path hL r j, hS.y_next r j] with ω hinv hp hy hω
    have hωR : ω ∈ (sys r j).R ∩ succSet G hnL hnR j (sys r j) (r j) := by rw [← hS.R_succ]; exact hω
    obtain ⟨⟨hsζ, hband, -⟩, -⟩ := swT_spec hωR.2
    obtain ⟨ha1, ha2, -, -, hfl, hfr⟩ := hinv hωR.1
    have hfp := (hp hωR.1).2.2.2.isForcePath
    rw [hy hω]
    set s := swT G hnL hnR j (sys r j) (r j) ω with hs
    have hvl : (sys r j).VL (farL (by omega : 0 < nL₀ + j)) s ω ≤ ((sys r j).y ω).2.1 (farL (by omega)) := by
      have := hfp.vL_le_of_le zero_le hsζ (farL (by omega : 0 < nL₀ + j)); rwa [hfp.vL_zero] at this
    have hvr : ((sys r j).y ω).2.2 (farR (by omega)) ≤ (sys r j).VR (farR (by omega : 0 < nR₀ + j)) s ω := by
      have := hfp.le_vR_of_le zero_le hsζ (farR (by omega : 0 < nR₀ + j)); rwa [hfp.vR_zero] at this
    have hb : -(9 / 4) < ((sys r j).y ω).1 + (sys r j).W s ω ∧ ((sys r j).y ω).1 + (sys r j).W s ω < 9 / 4 ∧
        (Even j → ((sys r j).y ω).1 + (sys r j).W s ω < -(7 / 4)) ∧
        (¬ Even j → 7 / 4 < ((sys r j).y ω).1 + (sys r j).W s ω) := by
      by_cases hj : Even j
      · rw [band_even hj] at hband
        exact ⟨hband.1, by linarith [hband.2], fun _ => hband.2, fun h => absurd hj h⟩
      · rw [band_odd hj] at hband
        exact ⟨by linarith [hband.1], hband.2, fun h => absurd h hj, fun _ => hband.1⟩
    refine ⟨?_, ?_, fun he => ?_, fun he => ?_, ?_, ?_⟩ <;>
      simp only [nextStart_fst, nextStart_farL, nextStart_farR, ← hs]
    · exact hb.1
    · exact hb.2.1
    · have hj : ¬ Even j := fun h => (Nat.not_even_iff_odd.2 h.add_one) he
      linarith [hb.2.2.2 hj]
    · have hj : Even j := by
        by_contra h; exact he (Nat.not_even_iff_odd.1 h).add_one
      linarith [hb.2.2.1 hj]
    · linarith
    · linarith

/-- **A crossing of the target level before the far contact makes the stage succeed for all large grid indices**
(deterministic; p. 145: "On `{S_j < L_j}`, continuity of the individual driving trajectory and of its time change
gives, for all sufficiently large `m`, […] `W(q_m(S_j)) ∈ I_{e_j}`"). -/
theorem eventually_mem_succSet (hS : IsStageSystem P hnL hnR Q δ G sys C) (r : ℕ → ℕ) (j : ℕ) {ω : Ω}
    (hw : ContinuousOn (fun u => (sys r j).W u ω) {u | (u : ℝ≥0∞) < (sys r j).ζ ω})
    (hclk : Continuous ((sys r j).clk ω)) (hmono : StrictMono ((sys r j).clk ω)) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < (sys r j).ζ ω)
    (hcross : (((sys r j).y ω).1 + (sys r j).W 0 ω - level j) * (((sys r j).y ω).1 + (sys r j).W t ω - level j) < 0)
    (hgap : ∀ u ≤ t, 0 < farGap hnL hnR j (sys r j) ω u) :
    ∀ᶠ n in atTop, ω ∈ succSet G hnL hnR j (sys r j) n := by
  have hsub : Icc (0 : ℝ≥0) t ⊆ {u | (u : ℝ≥0∞) < (sys r j).ζ ω} := fun u hu =>
    lt_of_le_of_lt (by exact_mod_cast hu.2) ht
  obtain ⟨t₁, t₂, h12, h2t, hband⟩ := exists_band_interval (f := fun u => ((sys r j).y ω).1 + (sys r j).W u ω)
    ((continuousOn_const.add hw).mono hsub) hcross
  have hc12 : (sys r j).clk ω t₁ < (sys r j).clk ω t₂ := hmono h12
  filter_upwards [hS.mesh.eventually (gt_mem_nhds (tsub_pos_of_lt hc12))] with n hn
  obtain ⟨k, hk1, hk2⟩ := exists_grid_btwn (hS.grid n) (lt_tsub_iff_left.1 hn)
  obtain ⟨s, hs, hsk⟩ := intermediate_value_Icc h12.le hclk.continuousOn ⟨hk1.le, hk2.le⟩
  have hst : s ≤ t := hs.2.trans h2t
  refine ⟨k, s, hsk, lt_of_le_of_lt (by exact_mod_cast hst) ht, ?_, fun u hu => hgap u (hu.trans hst)⟩
  have := hband s hs
  rw [abs_lt] at this
  exact ⟨by linarith [this.1], by linarith [this.2]⟩

/-- **Every stage eventually succeeds** (almost surely on `R j`, for every large grid index): the stage law with the
crossing premise (`compPremise_crossL/R`, Aux. lemma 22) and the band-and-grid argument. -/
theorem ae_eventually_succ [IsFiniteMeasure P] (hκ : 0 < κ) (hκ4 : κ < 4)
    (hL : Prop59StageLawStatement κ P ρL₀ ρR₀ sys) (hS : IsStageSystem P hnL hnR Q δ G sys C)
    (hwL : ∀ j, Even j → IsStageWordN κ (stageρL κ ρL₀ j) (stageρR κ ρR₀ j))
    (hwR : ∀ j, ¬ Even j → IsStageWordN κ (stageρR κ ρR₀ j) (stageρL κ ρL₀ j)) (r : ℕ → ℕ) (j : ℕ) :
    ∀ᵐ ω ∂P, ω ∈ (sys r j).R → ∀ᶠ n in atTop, ω ∈ succSet G hnL hnR j (sys r j) n := by
  have hL' : 0 < nL₀ + j := by omega
  have hR' : 0 < nR₀ + j := by omega
  have hRm : MeasurableSet (sys r j).R := hS.past_le r j _ (hS.R_meas r j)
  have hpair : Measurable fun ω => ((sys r j).y ω, samp ((sys r j).W · ω) (fun i t => (sys r j).VL i t ω)
      (fun k t => (sys r j).VR k t ω) ((sys r j).ζ ω)) := (hS.meas r j).1.prodMk (hS.meas r j).2
  -- the comparison form with `p = 1` gives the event almost surely on `R`
  have hae : ∀ {D : Set (Start (nL₀ + j) (nR₀ + j))} {S : Set (Start (nL₀ + j) (nR₀ + j) × Samp (nL₀ + j) (nR₀ + j))},
      MeasurableSet D → MeasurableSet S → CompPremise κ (stageρL κ ρL₀ j) (stageρR κ ρR₀ j) D S 1 →
      ∀ᵐ ω ∂P, ω ∈ (sys r j).R → (sys r j).y ω ∈ D → ((sys r j).y ω, samp ((sys r j).W · ω)
        (fun i t => (sys r j).VL i t ω) (fun k t => (sys r j).VR k t ω) ((sys r j).ζ ω)) ∈ S := by
    intro D S hD hS' hp
    have h := (hL r j).le_measure hD hS' le_rfl hp (hS.R_meas r j) subset_rfl
    rw [one_mul] at h
    set E : Set Ω := {ω | (sys r j).y ω ∈ D → ((sys r j).y ω, samp ((sys r j).W · ω)
      (fun i t => (sys r j).VL i t ω) (fun k t => (sys r j).VR k t ω) ((sys r j).ζ ω)) ∈ S} with hE
    have hEm : MeasurableSet E := by
      have : MeasurableSet {p : Start (nL₀ + j) (nR₀ + j) × Samp (nL₀ + j) (nR₀ + j) | p.1 ∈ D → p ∈ S} := by
        have e : {p : Start (nL₀ + j) (nR₀ + j) × Samp (nL₀ + j) (nR₀ + j) | p.1 ∈ D → p ∈ S} =
            (Prod.fst ⁻¹' D)ᶜ ∪ S := by ext p; simp only [mem_ofPred_eq, mem_union, mem_compl_iff, mem_preimage]; tauto
        rw [e]; exact (measurable_fst hD).compl.union hS'
      exact hpair this
    have hnull : P ((sys r j).R \ E) = 0 := by
      have h3 : P ((sys r j).R ∩ E) ≤ P (sys r j).R := measure_mono inter_subset_left
      have h4 : P ((sys r j).R ∩ E) = P (sys r j).R := le_antisymm h3 h
      rw [← sdiff_self_inter, measure_sdiff inter_subset_left (hRm.inter hEm).nullMeasurableSet
        (measure_ne_top _ _), h4, tsub_self]
    rw [ae_iff]
    refine measure_mono_null (fun ω hω => ?_) hnull
    have hω' : ¬ (ω ∈ (sys r j).R → ω ∈ E) := hω
    refine ⟨?_, fun hE' => hω' fun _ => hE'⟩
    by_contra h
    exact hω' fun h' => absurd h' h
  by_cases hj : Even j
  · filter_upwards [hae (measurableSet_startsL hL' hR') (measurableSet_crossL _ _)
      (compPremise_crossL hκ hκ4 hL' hR' (hwL j hj)), ae_path hL r j, ae_stageInv hL hS r j, hS.clk r j]
      with ω hcr hp hinv hclk hω
    obtain ⟨hF, hxL, hxR, hpath⟩ := hp hω
    obtain ⟨ha1, ha2, hev, -, hfl, hfr⟩ := hinv hω
    have hfp := hpath.isForcePath
    have hmem : (sys r j).y ω ∈ startsL hL' hR' :=
      ⟨hF, hxL, hxR, hfl, by linarith, by linarith⟩
    obtain ⟨t, htζ, hwt, hgap⟩ := path_of_crossL (x := ((sys r j).y ω).2) hfp.continuousOn_w
      (hfp.continuousOn_vL _) (hcr hω hmem)
    refine eventually_mem_succSet hS r j hfp.continuousOn_w (hclk hω).1 (hclk hω).2 htζ ?_ fun u hu => ?_
    · simp only [hfp.w_zero, level, hj, ↓reduceIte]
      have := hev hj
      nlinarith
    · simp only [farGap, hj, ↓reduceIte]; linarith [hgap u hu]
  · filter_upwards [hae (measurableSet_startsR hL' hR') (measurableSet_crossR _ _)
      (compPremise_crossR hκ hκ4 hL' hR' (hwR j hj)), ae_path hL r j, ae_stageInv hL hS r j, hS.clk r j]
      with ω hcr hp hinv hclk hω
    obtain ⟨hF, hxL, hxR, hpath⟩ := hp hω
    obtain ⟨ha1, ha2, -, hodd, hfl, hfr⟩ := hinv hω
    have hfp := hpath.isForcePath
    have hmem : (sys r j).y ω ∈ startsR hL' hR' :=
      ⟨hF, hxL, hxR, hfr, by linarith, by linarith⟩
    obtain ⟨t, htζ, hwt, hgap⟩ := path_of_crossR (x := ((sys r j).y ω).2) hfp.continuousOn_w
      (hfp.continuousOn_vR _) (hcr hω hmem)
    refine eventually_mem_succSet hS r j hfp.continuousOn_w (hclk hω).1 (hclk hω).2 htζ ?_ fun u hu => ?_
    · simp only [hfp.w_zero, level, hj, ↓reduceIte]
      have := hodd hj
      nlinarith
    · simp only [farGap, hj, ↓reduceIte]; linarith [hgap u hu]

/-- **The admissible start of an even stage** (p. 146: "At its start the driver is in `I₋`. […] Except for the new
first right force point at the current driver, all right force points are at least `7/4`: they were present at the
preceding completed rightward sweep and are nondecreasing, or were created at that rightward switch."). -/
theorem ae_mem_startsU (hL : Prop59StageLawStatement κ P ρL₀ ρR₀ sys) (hS : IsStageSystem P hnL hnR Q δ G sys C)
    (r : ℕ → ℕ) {j : ℕ} (hj : ¬ Even j) :
    ∀ᵐ ω ∂P, ω ∈ (sys r (j + 2)).R → (sys r (j + 2)).y ω ∈ startsU := by
  filter_upwards [ae_path hL r j, ae_path hL r (j + 1), ae_path hL r (j + 2), hS.y_next r j, hS.y_next r (j + 1)]
    with ω hp0 hp1 hp2 hy0 hy1 hω
  have hω1 : ω ∈ (sys r (j + 1)).R ∩ succSet G hnL hnR (j + 1) (sys r (j + 1)) (r (j + 1)) := by
    rw [← hS.R_succ]; exact hω
  have hω0 : ω ∈ (sys r j).R ∩ succSet G hnL hnR j (sys r j) (r j) := by rw [← hS.R_succ]; exact hω1.1
  obtain ⟨⟨hs1ζ, hb1, -⟩, -⟩ := swT_spec hω1.2
  obtain ⟨⟨hs0ζ, hb0, -⟩, -⟩ := swT_spec hω0.2
  have hj1 : Even (j + 1) := (Nat.not_even_iff_odd.1 hj).add_one
  rw [band_even hj1] at hb1
  rw [band_odd hj] at hb0
  have hfp1 := (hp1 hω1.1).2.2.2.isForcePath
  have hfp0 := (hp0 hω0.1).2.2.2.isForcePath
  refine ⟨?_, ?_, (hp2 hω).1, fun k hk => ?_⟩
  · rw [hy1 hω, nextStart_fst]; exact hb1.1
  · rw [hy1 hω, nextStart_fst]; exact hb1.2
  · obtain ⟨m, rfl⟩ : ∃ m : Fin (nR₀ + (j + 1)), k = m.succ := by
      rcases Fin.eq_zero_or_eq_succ k with h0 | h
      · exact absurd (by rw [h0]; rfl) (Nat.pos_iff_ne_zero.1 hk)
      · exact h
    rw [hy1 hω, nextStart_fst, nextStart_R_succ]
    set s1 := swT G hnL hnR (j + 1) (sys r (j + 1)) (r (j + 1)) ω
    have hm1 : (sys r (j + 1)).VR m 0 ω ≤ (sys r (j + 1)).VR m s1 ω := hfp1.le_vR_of_le zero_le hs1ζ m
    rw [hfp1.vR_zero m] at hm1
    have key : 7 / 4 ≤ ((sys r (j + 1)).y ω).1 + ((sys r (j + 1)).y ω).2.2 m := by
      rw [hy0 hω1.1, nextStart_fst]
      rcases Fin.eq_zero_or_eq_succ m with h0 | ⟨m', rfl⟩
      · rw [h0, nextStart_R_zero, add_zero]; exact hb0.1.le
      · rw [nextStart_R_succ]
        have := hfp0.w_le_vR hs0ζ m'
        linarith [hb0.1]
    linarith

/-- **The unit estimate of the even stages** (Lemma 5.10 at the first passage through `0`; p. 147): at depth
`j + 2` (`j` odd), every past event `A` satisfies `p₀ P(A) ≤ P(A ∩ (abort ∪ unit))`, where *unit* means success with
switching time at least `1`. -/
theorem le_measureReal_unit [IsProbabilityMeasure P] (hL : Prop59StageLawStatement κ P ρL₀ ρR₀ sys)
    (hS : IsStageSystem P hnL hnR Q δ G sys C) {p₀ : ℝ≥0∞} (hp₀1 : p₀ ≤ 1)
    (hprem : ∀ j, CompPremise κ (stageρL κ ρL₀ (j + 1)) (stageρR κ ρR₀ (j + 1)) startsU unitSet p₀)
    (r : ℕ → ℕ) {j : ℕ} (hj : ¬ Even j) {A : Set Ω} (hA : MeasurableSet[(sys r (j + 2)).past] A) :
    p₀.toReal * P.real A ≤ P.real (A ∩ (((sys r (j + 2)).R)ᶜ ∪
      ((sys r (j + 2)).R \ succSet G hnL hnR (j + 2) (sys r (j + 2)) (r (j + 2))) ∪
      {ω | ω ∈ succSet G hnL hnR (j + 2) (sys r (j + 2)) (r (j + 2)) ∧
        1 ≤ swT G hnL hnR (j + 2) (sys r (j + 2)) (r (j + 2)) ω})) := by
  set d := sys r (j + 2) with hd
  have hRm : MeasurableSet d.R := hS.past_le r _ _ (hS.R_meas r _)
  have hAm : MeasurableSet A := hS.past_le r _ _ hA
  have hpair : Measurable fun ω => (d.y ω, samp (d.W · ω) (fun i t => d.VL i t ω) (fun k t => d.VR k t ω)
      (d.ζ ω)) := (hS.meas r _).1.prodMk (hS.meas r _).2
  set E : Set Ω := {ω | d.y ω ∈ startsU → (d.y ω, samp (d.W · ω) (fun i t => d.VL i t ω)
      (fun k t => d.VR k t ω) (d.ζ ω)) ∈ unitSet} with hE
  have hEm : MeasurableSet E := by
    have e : {p : Start (nL₀ + (j + 2)) (nR₀ + (j + 2)) × Samp (nL₀ + (j + 2)) (nR₀ + (j + 2)) |
        p.1 ∈ startsU → p ∈ unitSet} = (Prod.fst ⁻¹' startsU)ᶜ ∪ unitSet := by
      ext p; simp only [mem_ofPred_eq, mem_union, mem_compl_iff, mem_preimage]; tauto
    have : MeasurableSet {p : Start (nL₀ + (j + 2)) (nR₀ + (j + 2)) × Samp (nL₀ + (j + 2)) (nR₀ + (j + 2)) |
        p.1 ∈ startsU → p ∈ unitSet} := by
      rw [e]; exact (measurable_fst measurableSet_startsU).compl.union measurableSet_unitSet
    exact hpair this
  have h := (hL r (j + 2)).le_measure measurableSet_startsU measurableSet_unitSet hp₀1 (hprem (j + 1))
    (hA.inter (hS.R_meas r _)) inter_subset_right
  -- on good samples of `A ∩ R ∩ E`, the stage aborts or spends a unit
  have hgood : ∀ᵐ ω ∂P, ω ∈ A ∩ d.R ∩ E → ω ∈ A ∩ ((d.R)ᶜ ∪ (d.R \ succSet G hnL hnR (j + 2) d (r (j + 2))) ∪
      {ω | ω ∈ succSet G hnL hnR (j + 2) d (r (j + 2)) ∧ 1 ≤ swT G hnL hnR (j + 2) d (r (j + 2)) ω}) := by
    filter_upwards [ae_mem_startsU hL hS r hj, ae_path hL r (j + 2)] with ω hU hp ⟨⟨hωA, hωR⟩, hωE⟩
    refine ⟨hωA, ?_⟩
    by_cases hsc : ω ∈ succSet G hnL hnR (j + 2) d (r (j + 2))
    · refine Or.inr ⟨hsc, ?_⟩
      obtain ⟨⟨hsζ, hband, -⟩, -⟩ := swT_spec hsc
      have hodd : ¬ Even (j + 2) := fun h => hj (by simpa [Nat.even_add] using h)
      rw [band_odd hodd] at hband
      have hunit := hωE (hU hωR)
      have hfp := (hp hωR).2.2.2.isForcePath
      set s := swT G hnL hnR (j + 2) d (r (j + 2)) ω
      by_contra hs1
      push Not at hs1
      have hc : ContinuousAt (fun u => (d.y ω).1 + d.W u ω) s :=
        (continuousOn_const.add hfp.continuousOn_w).continuousAt ((Coupling.isOpen_setOf_coe_lt _).mem_nhds hsζ)
      obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 (hc.eventually (lt_mem_nhds hband.1))
      obtain ⟨b, hsb, hbζ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hsζ
      have hεn : s < s + ε.toNNReal := lt_add_of_pos_right _ (Real.toNNReal_pos.2 hε)
      obtain ⟨q, hq1, hq2⟩ := exists_nnrat_btwn₀ (lt_min (ENNReal.coe_lt_coe.1 hsb) (lt_min hs1 hεn))
      have hqζ : ((q : ℝ≥0) : ℝ≥0∞) < d.ζ ω := lt_trans (by exact_mod_cast hq2.trans_le (min_le_left _ _)) hbζ
      have hq1' : ((q : ℝ≥0) : ℝ) < 1 := by
        have := hq2.trans_le ((min_le_right _ _).trans (min_le_left _ _)); exact_mod_cast this
      have hqd : dist (q : ℝ≥0) s < ε := by
        have h3 := hq2.trans_le ((min_le_right _ _).trans (min_le_right _ _))
        rw [NNReal.dist_eq, abs_lt]
        have h4 : ((q : ℝ≥0) : ℝ) < s + ε := by
          have := (NNReal.coe_lt_coe.2 h3); rwa [NNReal.coe_add, Real.coe_toNNReal _ hε.le] at this
        constructor <;> linarith [NNReal.coe_lt_coe.2 hq1]
      have h1 := hball hqd
      have h2 := hunit q hq1' hqζ
      change (d.y ω).1 + ((samp (d.W · ω) (fun i t => d.VL i t ω) (fun k t => d.VR k t ω) (d.ζ ω)).2 q).1 < 7 / 4
        at h2
      rw [samp_snd_of_lt _ _ _ hqζ] at h2
      simp only at h1 h2
      linarith
    · exact Or.inl (Or.inr ⟨hωR, hsc⟩)
  -- the measure estimate
  set B : Set Ω := A ∩ ((d.R)ᶜ ∪ (d.R \ succSet G hnL hnR (j + 2) d (r (j + 2))) ∪
      {ω | ω ∈ succSet G hnL hnR (j + 2) d (r (j + 2)) ∧ 1 ≤ swT G hnL hnR (j + 2) d (r (j + 2)) ω}) with hB
  have h1 : P (A ∩ d.R ∩ E) ≤ P (B ∩ d.R) := by
    refine measure_mono_ae ?_
    filter_upwards [hgood] with ω hω h'
    exact ⟨hω h', h'.1.2⟩
  have h2 : A \ d.R ⊆ B \ d.R := fun ω hω => ⟨⟨hω.1, Or.inl (Or.inl hω.2)⟩, hω.2⟩
  have hsplitA : P.real A = P.real (A ∩ d.R) + P.real (A \ d.R) :=
    (measureReal_inter_add_sdiff (μ := P) (s := A) hRm).symm
  have hsplitB : P.real B = P.real (B ∩ d.R) + P.real (B \ d.R) :=
    (measureReal_inter_add_sdiff (μ := P) (s := B) hRm).symm
  have hp0 : p₀.toReal ≤ 1 := by
    have := ENNReal.toReal_mono ENNReal.one_ne_top hp₀1; simpa using this
  have h3 : p₀.toReal * P.real (A ∩ d.R) ≤ P.real (B ∩ d.R) := by
    have := ENNReal.toReal_mono (measure_ne_top _ _) (h.trans h1)
    rwa [ENNReal.toReal_mul] at this
  have h4 : P.real (A \ d.R) ≤ P.real (B \ d.R) := measureReal_mono h2
  rw [hsplitA, hsplitB, mul_add]
  have h5 : p₀.toReal * P.real (A \ d.R) ≤ P.real (A \ d.R) :=
    mul_le_of_le_one_left measureReal_nonneg hp0
  linarith

end Invariants

end Prop59Stage

end Sec5

end InteractingSLE
