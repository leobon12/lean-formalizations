/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.DS3ProofReach
import InteractingSLE.Spec.Supplement.GB8Energy

/-!
# The exact-extreme crossing as a reach event of probability close to one (follow-up note A.3)

Packet PROVE-T14-TIP7, ruling R53 (`source/external/AstraIG1/ig1_followup_a_e_audited.txt`, A.3, lines 155–163):

> The exact-extreme crossing argument on pp. 594 and 622 supplies a finite crossing before old-counterflow contact and
> any bad collision. […] GB8's whole-history comparison excludes a transient future avoiding the crossing. […] This
> finite compact prefix has bounded coordinates and positive designated far gaps. It follows that
> `P_{θ*}(U_{T,R,g}) → 1` as `T, R ↑ ∞, g ↓ 0`.

In driver form (the stage's joint-chart word at the exact extreme angle is a GB8 word, with the old-counterflow tail
junctions as its outermost labels): for an integrated evolution of a GB8 word whose outermost left label is at
`x₋ ≤ −3` and whose designated far left labels (indices `≥ m_L`: the attracting-side original groups and the junction)
all start at most `−3`, with the far right label the junction alone (`m_R = n_R − 1`), the leftward reach event

  `U_n = {∃ t < n, W_t < −17/8, and on [0, t]: every coordinate in (−n, n), every far gap > 1/(n+1)}`

has `P(U_n) → 1`.

Proof. GB8 (`Supp8.GB8.GB8Statement`, proved from Theorem 1.3 by `gb8Statement_of_thm13`) gives, almost surely, a
time `t` before the lifetime with `W_t < −17/8` before the first far-left contact, and no contact with the far right
label at all. Let `c = max(W_t, −11/4) < −17/8` and let `t'` be the first time with `W ≤ c` (a least element of a
compact set; `t' > 0` since `W_0 = 0`). By continuity from the left `W_{t'} = c ≥ −11/4`, and `W > c` before `t'`. Far
left labels are nonincreasing (`vL_le_of_le`), so they stay `≤ −3` and their gaps are `≥ 1/4` on `[0, t']`. The far
right gap is a positive continuous function on the compact `[0, t']`, so it has a positive minimum; the coordinates
are bounded there. A large `n` gives `ω ∈ U_n`. The events increase with `n`, so continuity from below gives the limit.

## Main results

* `exists_reach_left_of_path` (deterministic);
* `ae_exists_reachEvent_left`, `tendsto_measure_reachEvent_left`, **`exists_lt_measure_reachEvent_left`**;
* the same from Theorem 1.3 (`exists_lt_measure_reachEvent_left_of_thm13`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Finset Set
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Theorem14

namespace CS3Cross

open Supp12 Supp12.DS2 Supp12.DSReach Supp8.GB8

variable {nL nR : ℕ}

/-- The leftward target `{W < −17/8}`. -/
def leftTarget : Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)) := {p | p.1 < -(2 + 1 / 8)}

theorem isOpen_leftTarget : IsOpen (leftTarget : Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ))) :=
  isOpen_lt continuous_fst continuous_const

/-- The `n`-th inner buffer of the leftward stage: coordinates in `(−n, n)`, far gaps `> 1/(n+1)` for the left
labels of index `≥ m_L` and the last right label. -/
def leftBuf (mL : ℕ) (nR : ℕ) (n : ℕ) : Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)) :=
  {p | InBuffer mL (nR - 1) n (1 / ((n : ℝ) + 1)) p}

theorem leftBuf_mono (mL nR : ℕ) : Monotone (leftBuf (nL := nL) mL nR) := by
  intro n n' hnn' p hp
  refine inBuffer_mono (by exact_mod_cast hnn') ?_ hp
  have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  exact one_div_le_one_div_of_le h1 (by exact_mod_cast Nat.add_le_add_right hnn' 1)

/-- The leftward reach events increase with `n`. -/
theorem reachEvent_left_mono {Ω : Type*} (mL : ℕ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
    (VR : Fin nR → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) :
    Monotone fun n : ℕ => reachEvent (n : ℝ≥0) leftTarget (leftBuf mL nR n) W VL VR ζ := fun n n' h =>
  reachEvent_mono (by exact_mod_cast h) subset_rfl (leftBuf_mono mL nR h) W VL VR ζ

/-! ### The deterministic step -/

section Path

variable {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- **The first passage below a level, with bounded coordinates and positive far gaps** (deterministic). Let the
driver and the force coordinates be continuous before the lifetime, the far left labels (`i ≥ m_L`) nonincreasing and
starting at most `−3`, the driver starting at `0`. If at some time `t` before the lifetime the driver is below
`−17/8` and the last right label is strictly right of the driver on `[0, t]`, then for some `n` the path reaches
`{W < −17/8}` before `n` inside the `n`-th leftward buffer. -/
theorem exists_reach_left_of_path (hnR : 0 < nR) (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ})
    (hvL : ∀ i, ContinuousOn (vL i) {t | (t : ℝ≥0∞) < ζ}) (hvR : ∀ j, ContinuousOn (vR j) {t | (t : ℝ≥0∞) < ζ})
    (hw0 : w 0 = 0) {mL : ℕ} (hfar : ∀ i : Fin nL, mL ≤ (i : ℕ) → ∀ u : ℝ≥0, (u : ℝ≥0∞) < ζ → vL i u ≤ -3)
    {t : ℝ≥0} (htζ : (t : ℝ≥0∞) < ζ) (hwt : w t < -(2 + 1 / 8))
    (hR : ∀ u ≤ t, w u < vR ⟨nR - 1, Nat.sub_lt hnR one_pos⟩ u) :
    ∃ n : ℕ, ∃ t' : ℝ≥0, t' < (n : ℝ≥0) ∧ (t' : ℝ≥0∞) < ζ ∧ w t' < -(2 + 1 / 8) ∧
      ∀ u ≤ t', InBuffer mL (nR - 1) n (1 / ((n : ℝ) + 1)) (w u, fun i => vL i u, fun j => vR j u) := by
  set c : ℝ := max (w t) (-(11 / 4)) with hc
  have hc_lt : c < -(2 + 1 / 8) := max_lt hwt (by norm_num)
  have hc_ge : -(11 / 4) ≤ c := le_max_right _ _
  have hsub : Icc (0 : ℝ≥0) t ⊆ {u | (u : ℝ≥0∞) < ζ} := fun u hu =>
    lt_of_le_of_lt (by exact_mod_cast hu.2) htζ
  have hwI : ContinuousOn w (Icc 0 t) := hw.mono hsub
  -- the first passage `t'` of `W ≤ c`
  set S : Set ℝ≥0 := Icc 0 t ∩ w ⁻¹' Iic c with hS
  have hSc : IsCompact S := by
    refine isCompact_Icc.of_isClosed_subset ?_ inter_subset_left
    exact hwI.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hSne : S.Nonempty := ⟨t, ⟨⟨zero_le, le_rfl⟩, show w t ≤ c from le_max_left _ _⟩⟩
  obtain ⟨t', ⟨⟨-, ht't⟩, hwt'⟩, hleast⟩ := hSc.exists_isLeast hSne
  have hbefore : ∀ u < t', c < w u := fun u hu => by
    by_contra hcon
    exact absurd (hleast ⟨⟨zero_le, (hu.le.trans ht't)⟩, not_lt.1 hcon⟩) (not_le.2 hu)
  have ht'0 : 0 < t' := by
    rcases (zero_le : (0 : ℝ≥0) ≤ t').lt_or_eq with h | h
    · exact h
    · exfalso
      have : w t' ≤ c := hwt'
      rw [← h, hw0] at this
      linarith
  -- continuity from the left: `w t' ≥ c`
  have hwt'c : c ≤ w t' := by
    have : NeBot (𝓝[Iio t'] t') := nhdsWithin_Iio_neBot' ⟨0, ht'0⟩ le_rfl
    have hcw : ContinuousWithinAt w (Iio t') t' :=
      (hwI t' ⟨zero_le, ht't⟩).mono fun u hu => ⟨zero_le, (le_of_lt hu).trans ht't⟩
    exact ge_of_tendsto hcw (eventually_nhdsWithin_of_forall fun u hu => (hbefore u hu).le)
  have ht'ζ : (t' : ℝ≥0∞) < ζ := lt_of_le_of_lt (by exact_mod_cast ht't) htζ
  have hsub' : Icc (0 : ℝ≥0) t' ⊆ {u | (u : ℝ≥0∞) < ζ} := fun u hu =>
    lt_of_le_of_lt (by exact_mod_cast hu.2) ht'ζ
  have hw_ge : ∀ u ≤ t', -(11 / 4) ≤ w u := fun u hu => by
    rcases hu.lt_or_eq with h | h
    · exact hc_ge.trans (hbefore u h).le
    · rw [h]; exact hc_ge.trans hwt'c
  -- a bound on the coordinates over `[0, t']`
  set F : ℝ≥0 → ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) := fun u => (w u, fun i => vL i u, fun j => vR j u) with hF
  have hFc : ContinuousOn F (Icc 0 t') := by
    refine (hw.mono hsub').prodMk ((continuousOn_pi.2 fun i => (hvL i).mono hsub').prodMk
      (continuousOn_pi.2 fun j => (hvR j).mono hsub'))
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hFc
  -- a positive minimum of the far right gap over `[0, t']`
  set jR : Fin nR := ⟨nR - 1, Nat.sub_lt hnR one_pos⟩ with hjR
  have hgc : ContinuousOn (fun u => vR jR u - w u) (Icc 0 t') := ((hvR jR).mono hsub').sub (hw.mono hsub')
  obtain ⟨u₀, hu₀, hmin⟩ := isCompact_Icc.exists_isMinOn ⟨0, ⟨le_rfl, zero_le⟩⟩ hgc
  set m₀ : ℝ := vR jR u₀ - w u₀ with hm₀
  have hm₀pos : 0 < m₀ := sub_pos.2 (hR u₀ (hu₀.2.trans ht't))
  -- choose `n`
  set g₀ : ℝ := min m₀ (1 / 4) with hg₀
  have hg₀pos : 0 < g₀ := lt_min hm₀pos (by norm_num)
  obtain ⟨n, hn⟩ := exists_nat_gt (max (max (t' : ℝ) C) (1 / g₀))
  have hn1 : (t' : ℝ) < n := lt_of_le_of_lt (le_max_left _ _ |>.trans (le_max_left _ _)) hn
  have hnC : C < n := lt_of_le_of_lt (le_max_right _ _ |>.trans (le_max_left _ _)) hn
  have hng : 1 / g₀ < n := lt_of_le_of_lt (le_max_right _ _) hn
  have hgap : 1 / ((n : ℝ) + 1) < g₀ := by
    have h1 : 0 < (n : ℝ) + 1 := by positivity
    rw [div_lt_iff₀ h1]
    have := (div_lt_iff₀ hg₀pos).1 hng
    nlinarith
  refine ⟨n, t', by exact_mod_cast hn1, ht'ζ, lt_of_le_of_lt (le_of_eq_of_le rfl hwt') hc_lt, fun u hu => ?_⟩
  have huI : u ∈ Icc (0 : ℝ≥0) t' := ⟨zero_le, hu⟩
  have hFu : ‖F u‖ ≤ C := hC u huI
  have hwu : ‖w u‖ ≤ C := (norm_fst_le (F u)).trans hFu
  have hvLu : ∀ i, ‖vL i u‖ ≤ C := fun i =>
    ((norm_le_pi_norm (fun i => vL i u) i).trans (norm_fst_le (F u).2)).trans ((norm_snd_le (F u)).trans hFu)
  have hvRu : ∀ j, ‖vR j u‖ ≤ C := fun j =>
    ((norm_le_pi_norm (fun j => vR j u) j).trans (norm_snd_le (F u).2)).trans ((norm_snd_le (F u)).trans hFu)
  refine ⟨⟨?_, fun i => ?_, fun j => ?_⟩, fun j hj => ?_, fun i hi => ?_⟩
  · exact lt_of_le_of_lt (by simpa [Real.norm_eq_abs] using hwu) hnC
  · exact lt_of_le_of_lt (by simpa [Real.norm_eq_abs] using hvLu i) hnC
  · exact lt_of_le_of_lt (by simpa [Real.norm_eq_abs] using hvRu j) hnC
  · have hjeq : j = jR := Fin.ext (le_antisymm (Nat.le_sub_one_of_lt j.2) hj)
    subst hjeq
    have : m₀ ≤ vR jR u - w u := hmin huI
    exact lt_of_lt_of_le hgap ((min_le_left _ _).trans this)
  · have h1 := hfar i hi u (lt_of_le_of_lt (by exact_mod_cast hu) ht'ζ)
    have h2 := hw_ge u hu
    have : (1 : ℝ) / 4 ≤ w u - vL i u := by linarith
    exact lt_of_lt_of_le hgap ((min_le_right _ _).trans this)

end Path

/-! ### The probabilistic statements -/

variable {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {Ω : Type u}
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **The exact-extreme crossing, pathwise almost surely** (A.3 with GB8): for a GB8 word whose outermost left label
starts at `x₋ ≤ −3` and whose designated far left labels (`i ≥ m_L`) all start at most `−3`, almost surely the
leftward reach event `U_n` occurs for some `n`. -/
theorem ae_exists_reachEvent_left (hGB8 : GB8Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4) (hnL : 0 < nL)
    (hnR : 0 < nR) (hF : IsOrderedForceWord xL xR) (hxp : 0 < xR ⟨nR - 1, Nat.sub_lt hnR one_pos⟩)
    (hxm : xL ⟨nL - 1, Nat.sub_lt hnL one_pos⟩ ≤ -3) (hsL : ∑ i, ρL i = κ - 4) (hsR : ∑ j, ρR j = κ / 2 - 2)
    (hpL : ∀ i : Fin nL, (i : ℕ) < nL - 1 → -2 < ∑ l ∈ univ.filter (fun l => l ≤ i), ρL l)
    (hpR : ∀ j : Fin nR, (j : ℕ) < nR - 1 → -2 < ∑ l ∈ univ.filter (fun l => l ≤ j), ρR l)
    {mL : ℕ} (hfar : ∀ i : Fin nL, mL ≤ (i : ℕ) → xL i ≤ -3)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (htr : ∀ᵐ ω ∂P, ∃ γ : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) γ) :
    ∀ᵐ ω ∂P, ∃ n : ℕ, ω ∈ reachEvent (n : ℝ≥0) leftTarget (leftBuf mL nR n) W VL VR ζ := by
  have hlt0 : xL ⟨nL - 1, Nat.sub_lt hnL one_pos⟩ < 0 := by linarith
  have h8 := hGB8 κ hκ hκ4 nL nR hnL hnR xL xR ρL ρR hF hlt0 hxp hsL hsR hpL hpR P 𝓕 W VL VR B ζ hE htr
  filter_upwards [h8, hE.2.2.2.2] with ω hω hp
  obtain ⟨-, hnoR, hcross⟩ := hω
  obtain ⟨t, htζ, hwt, -⟩ := hcross hxm
  have hfp := hp.isForcePath
  have hfar' : ∀ i : Fin nL, mL ≤ (i : ℕ) → ∀ u : ℝ≥0, (u : ℝ≥0∞) < ζ ω → VL i u ω ≤ -3 := fun i hi u hu =>
    (hfp.vL_le_of_le zero_le hu i).trans (by rw [hfp.vL_zero i]; exact hfar i hi)
  obtain ⟨n, t', ht'n, ht'ζ, hwt', hbuf⟩ := exists_reach_left_of_path (w := fun t => W t ω)
    (vL := fun i t => VL i t ω) (vR := fun j t => VR j t ω) hnR hfp.continuousOn_w hfp.continuousOn_vL
    hfp.continuousOn_vR hfp.w_zero hfar' htζ hwt
    (fun u hu => hnoR u (lt_of_le_of_lt (by exact_mod_cast hu) htζ))
  exact ⟨n, t', ht'n, ht'ζ, hwt', fun u hu => hbuf u hu⟩

/-- **The exact-extreme crossing has probability tending to one**: `P(U_n) → P(⋃ U_n) = 1`. -/
theorem tendsto_measure_reachEvent_left [IsProbabilityMeasure P] (hGB8 : GB8Statement.{u}) (hκ : 0 < κ)
    (hκ4 : κ < 4) (hnL : 0 < nL) (hnR : 0 < nR) (hF : IsOrderedForceWord xL xR)
    (hxp : 0 < xR ⟨nR - 1, Nat.sub_lt hnR one_pos⟩) (hxm : xL ⟨nL - 1, Nat.sub_lt hnL one_pos⟩ ≤ -3)
    (hsL : ∑ i, ρL i = κ - 4) (hsR : ∑ j, ρR j = κ / 2 - 2)
    (hpL : ∀ i : Fin nL, (i : ℕ) < nL - 1 → -2 < ∑ l ∈ univ.filter (fun l => l ≤ i), ρL l)
    (hpR : ∀ j : Fin nR, (j : ℕ) < nR - 1 → -2 < ∑ l ∈ univ.filter (fun l => l ≤ j), ρR l)
    {mL : ℕ} (hfar : ∀ i : Fin nL, mL ≤ (i : ℕ) → xL i ≤ -3)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (htr : ∀ᵐ ω ∂P, ∃ γ : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) γ) :
    Tendsto (fun n : ℕ => P (reachEvent (n : ℝ≥0) leftTarget (leftBuf mL nR n) W VL VR ζ)) atTop (𝓝 1) := by
  have hlim := tendsto_measure_iUnion_atTop (μ := P) (reachEvent_left_mono (nL := nL) (nR := nR) mL W VL VR ζ)
  have hae := ae_exists_reachEvent_left hGB8 hκ hκ4 hnL hnR hF hxp hxm hsL hsR hpL hpR hfar hE htr
  have hone : P (⋃ n : ℕ, reachEvent (n : ℝ≥0) leftTarget (leftBuf mL nR n) W VL VR ζ) = 1 := by
    refine le_antisymm prob_le_one ?_
    have hnull : P (⋃ n : ℕ, reachEvent (n : ℝ≥0) leftTarget (leftBuf mL nR n) W VL VR ζ)ᶜ = 0 := by
      rw [ae_iff] at hae
      refine measure_mono_null (fun ω hω => ?_) hae
      simp only [mem_compl_iff, mem_iUnion, not_exists] at hω
      simp only [mem_ofPred_eq, not_exists]
      exact hω
    calc (1 : ℝ≥0∞) = P univ := measure_univ.symm
      _ ≤ P (⋃ n : ℕ, reachEvent (n : ℝ≥0) leftTarget (leftBuf mL nR n) W VL VR ζ) +
          P (⋃ n : ℕ, reachEvent (n : ℝ≥0) leftTarget (leftBuf mL nR n) W VL VR ζ)ᶜ := by
            rw [← union_compl_self (⋃ n : ℕ, reachEvent (n : ℝ≥0) leftTarget (leftBuf mL nR n) W VL VR ζ)]
            exact measure_union_le _ _
      _ = _ := by rw [hnull, add_zero]
  rw [hone] at hlim
  exact hlim

/-- **A buffer with crossing probability `> 1 − δ`** ("Choose a rational buffer for which this probability exceeds
`1 − ε/4`", A.3). -/
theorem exists_lt_measure_reachEvent_left [IsProbabilityMeasure P] (hGB8 : GB8Statement.{u}) (hκ : 0 < κ)
    (hκ4 : κ < 4) (hnL : 0 < nL) (hnR : 0 < nR) (hF : IsOrderedForceWord xL xR)
    (hxp : 0 < xR ⟨nR - 1, Nat.sub_lt hnR one_pos⟩) (hxm : xL ⟨nL - 1, Nat.sub_lt hnL one_pos⟩ ≤ -3)
    (hsL : ∑ i, ρL i = κ - 4) (hsR : ∑ j, ρR j = κ / 2 - 2)
    (hpL : ∀ i : Fin nL, (i : ℕ) < nL - 1 → -2 < ∑ l ∈ univ.filter (fun l => l ≤ i), ρL l)
    (hpR : ∀ j : Fin nR, (j : ℕ) < nR - 1 → -2 < ∑ l ∈ univ.filter (fun l => l ≤ j), ρR l)
    {mL : ℕ} (hfar : ∀ i : Fin nL, mL ≤ (i : ℕ) → xL i ≤ -3)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (htr : ∀ᵐ ω ∂P, ∃ γ : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) γ) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ n : ℕ, 1 - δ < P (reachEvent (n : ℝ≥0) leftTarget (leftBuf mL nR n) W VL VR ζ) := by
  have hlim := tendsto_measure_reachEvent_left hGB8 hκ hκ4 hnL hnR hF hxp hxm hsL hsR hpL hpR hfar hE htr
  have h1 : (1 : ℝ≥0∞) - δ < 1 := ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hδ.ne'
  exact (hlim.eventually (lt_mem_nhds h1)).exists

/-- The same from Theorem 1.3 (GB8 is proved from it, `gb8Statement_of_thm13`). -/
theorem exists_lt_measure_reachEvent_left_of_thm13 [IsProbabilityMeasure P] (h13 : Exist.Theorem13Statement.{u})
    (hκ : 0 < κ) (hκ4 : κ < 4) (hnL : 0 < nL) (hnR : 0 < nR) (hF : IsOrderedForceWord xL xR)
    (hxp : 0 < xR ⟨nR - 1, Nat.sub_lt hnR one_pos⟩) (hxm : xL ⟨nL - 1, Nat.sub_lt hnL one_pos⟩ ≤ -3)
    (hsL : ∑ i, ρL i = κ - 4) (hsR : ∑ j, ρR j = κ / 2 - 2)
    (hpL : ∀ i : Fin nL, (i : ℕ) < nL - 1 → -2 < ∑ l ∈ univ.filter (fun l => l ≤ i), ρL l)
    (hpR : ∀ j : Fin nR, (j : ℕ) < nR - 1 → -2 < ∑ l ∈ univ.filter (fun l => l ≤ j), ρR l)
    {mL : ℕ} (hfar : ∀ i : Fin nL, mL ≤ (i : ℕ) → xL i ≤ -3)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (htr : ∀ᵐ ω ∂P, ∃ γ : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) γ) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ n : ℕ, 1 - δ < P (reachEvent (n : ℝ≥0) leftTarget (leftBuf mL nR n) W VL VR ζ) :=
  exists_lt_measure_reachEvent_left (gb8Statement_of_thm13 h13) hκ hκ4 hnL hnR hF hxp hxm hsL hsR hpL hpR hfar
    hE htr hδ

end CS3Cross

end Theorem14

end InteractingSLE
