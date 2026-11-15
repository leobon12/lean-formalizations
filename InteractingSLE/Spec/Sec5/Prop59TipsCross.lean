/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop59TipsSeed
import InteractingSLE.Spec.Supplement.GB8InputsRight
import InteractingSLE.Spec.Supplement.CS3ProofCrossRight

/-!
# Proposition 5.9's one-stage construction, step 3: the driver crosses `∓(2 + 1/8)` before the far contact

Packet PROVE-PROP59T. Specification §5.2, proof of Proposition 5.9 (`source/spec/p097-144.md` L1002–L1016,
`p145-192.md` L1–L3, pp. 143–145):

> If we use the extreme angle `−e_jπ/2`, the full-span case of **Aux.** lemma 22 and the boundary calculation below
> show that the driver reaches `e_j(2 + 1/8)` before the trajectory hits the revealed counterflow or its continuation
> threshold. Its first new real hit lies beyond the corresponding marked point of magnitude at least `3`. […] The
> corresponding left force coordinate is nonincreasing; at this first swallow it equals the driver and is at most
> `x₋ ≤ −3`. Driver continuity therefore gives the strictly earlier crossing of `−(2 + 1/8)`. […] Reflection gives the
> angle-`−π/2` assertion.
>
> For any prescribed error `ε_j > 0`, choose a finite capacity horizon, a driver bound, and positive lower bounds on
> the additional force-point gaps so that, for this extreme-angle law, the driver crosses the level `e_j(2+1/8)` before
> this localization ends with probability larger than `1 − ε_j/4`.

This is the R48-safe form of Lemma GB8's conclusion for the stage words of Proposition 5.9 (all lower prefix sums at
least `κ/2 − 2`): the swallow comes from Aux. 22 directly (`ae_swallow`), not from the complete finite-force theorem,
so neither Theorem 1.3 nor `Supp8.GB8.GB8Statement` is used. The remaining wiring reuses PROVE-T14-TIP2/TIP4/TIP7's
deterministic steps and the unconditional no-right-contact lemma (`Supp8.GB8.rightNoContactStatement`).

## Main results

* `neg_two_lt_partialL`, `neg_two_lt_partialR`: the stage word's partial sums exceed `−2` (GB8's form);
* **`ae_stage_cross_left`**: a.s. a first far-left contact `τ` (and `τ = ζ` when `κ ≤ 2`), no contact of the last
  right mark before the lifetime, and, if `x₋ ≤ −3`, a time before the lifetime at which the driver is below
  `−(2 + 1/8)` with the far-left mark still strictly left of it;
* **`ae_exists_reachEvent_left_stage`**, **`tendsto_measure_reachEvent_left_stage`**,
  **`exists_lt_measure_reachEvent_left_stage`**: the leftward reach events `U_n` (PROVE-T14-TIP7's buffers) have
  probability tending to `1` ("the driver crosses the level … before this localization ends with probability larger
  than `1 − ε_j/4`");
* **`ae_exists_reachEvent_right_stage`**, **`exists_lt_measure_reachEvent_right_stage`**: the rightward stage
  (angle `−π/2`), by reflection.

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

open Supp8.GB8 Supp12.DSReach Theorem14.CS3Cross

/-! ### Index and partial-sum bookkeeping -/

theorem last_eq_mk (j : ℕ) (h : 0 < j + 1) : (⟨j + 1 - 1, Nat.sub_lt h one_pos⟩ : Fin (j + 1)) = Fin.last j :=
  Fin.ext (Nat.add_sub_cancel j 1)

theorem filter_le_eq_Iic {m : ℕ} (i : Fin m) : (univ.filter fun l : Fin m => l ≤ i) = Finset.Iic i := by
  ext l; simp

/-- The left partial sums of a stage word before the last mark exceed `−2` (they are at least `κ/2 − 2`). -/
theorem neg_two_lt_partialL {κ : ℝ} (hκ : 0 < κ) {j n : ℕ} {ρL : Fin (j + 1) → ℝ} {ρR : Fin n → ℝ}
    (hw : IsStageWord κ ρL ρR) (i : Fin (j + 1)) (hi : (i : ℕ) < j + 1 - 1) :
    -2 < ∑ l ∈ univ.filter (fun l => l ≤ i), ρL l := by
  have hij : (i : ℕ) < j := by omega
  set k : Fin j := ⟨i, hij⟩ with hk
  have hik : i = k.castSucc := Fin.ext rfl
  rw [filter_le_eq_Iic, hik]
  have e : ∑ l ∈ Finset.Iic k.castSucc, ρL l = ∑ l ∈ Finset.Iic k, Fin.init ρL l := by
    have hI : Finset.Iic k.castSucc = (Finset.Iic k).map Fin.castSuccEmb := by
      ext i
      simp only [Finset.mem_Iic, Finset.mem_map, Fin.castSuccEmb_apply]
      constructor
      · intro hi
        refine ⟨i.castPred (Fin.ne_last_of_lt (lt_of_le_of_lt hi (Fin.castSucc_lt_last k))), ?_, by simp⟩
        rw [← Fin.castSucc_le_castSucc_iff, Fin.castSucc_castPred]
        exact hi
      · rintro ⟨a, ha, rfl⟩
        exact Fin.castSucc_le_castSucc_iff.2 ha
    rw [hI, Finset.sum_map]
    rfl
  rw [e]
  linarith [hw.2.1.1 k]

/-- The right partial sums of a stage word exceed `−2` (they are at least `κ/2 − 2`). -/
theorem neg_two_lt_partialR {κ : ℝ} (hκ : 0 < κ) {j n : ℕ} {ρL : Fin (j + 1) → ℝ} {ρR : Fin n → ℝ}
    (hw : IsStageWord κ ρL ρR) (k : Fin n) : -2 < ∑ l ∈ univ.filter (fun l => l ≤ k), ρR l := by
  rw [filter_le_eq_Iic]
  linarith [hw.2.1.2 k]

/-! ### The stage crossing -/

section Cross

variable {κ : ℝ} {j n : ℕ} {xL : Fin (j + 1) → ℝ} {xR : Fin n → ℝ} {ρL : Fin (j + 1) → ℝ} {ρR : Fin n → ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin (j + 1) → ℝ≥0 → Ω → ℝ} {VR : Fin n → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **One stage of the alternating construction at angle `+π/2`** (pp. 143–144; Lemma GB8's conclusion for a stage
word, R48-safe). Let `(W, V, B)` be an integrated `SLE_κ(ρ)` evolution, `0 < κ < 4`, of an ordered stage word with
distinct positions on each side (seed marks allowed), outermost left mark `x₋ < 0`, outermost right mark `x₊ > 0`,
with a continuous generating trace through its lifetime. Then almost surely:
* the outermost left mark has a first contact `τ > 0` with the driver, before or at the lifetime, and `τ = ζ` if
  `κ ≤ 2` ("If the left total is at most `−2`, that far-left swallowing is its continuation threshold");
* the outermost right mark never meets the driver before the lifetime;
* if `x₋ ≤ −3`, the driver is below `−(2 + 1/8)` at some time before the lifetime, the far-left mark still strictly
  left of it up to then. -/
theorem ae_stage_cross_left (hκ : 0 < κ) (hκ4 : κ < 4) (hn : 0 < n)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hF : IsOrderedForceWord xL xR)
    (hxL : StrictAnti xL) (hxR : StrictMono xR) (hxm : xL (Fin.last j) < 0)
    (hxp : 0 < xR ⟨n - 1, Nat.sub_lt hn one_pos⟩) (hw : IsStageWord κ ρL ρR)
    (htr : ∀ᵐ ω ∂P, ∃ γ : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) γ) :
    ∀ᵐ ω ∂P, (∃ τ : ℝ≥0, IsFirstFarContact (fun t => W t ω) (fun t => VL (Fin.last j) t ω) (ζ ω) τ ∧
        (κ - 4 ≤ -2 → (τ : ℝ≥0∞) = ζ ω)) ∧
      (∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → W t ω < VR ⟨n - 1, Nat.sub_lt hn one_pos⟩ t ω) ∧
      (xL (Fin.last j) ≤ -3 → ∃ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω ∧ W t ω < -(2 + 1 / 8) ∧
        ∀ u ≤ t, VL (Fin.last j) u ω < W u ω) := by
  have : IsProbabilityMeasure P := hE.1.isProbabilityMeasure'
  have hj : 0 < j + 1 := Nat.succ_pos j
  have hlast := last_eq_mk j hj
  have hxm' : xL ⟨j + 1 - 1, Nat.sub_lt hj one_pos⟩ < 0 := by rw [hlast]; exact hxm
  have hpsL := neg_two_lt_partialL hκ hw
  have hpsR : ∀ k : Fin n, (k : ℕ) < n - 1 → -2 < ∑ l ∈ univ.filter (fun l => l ≤ k), ρR l :=
    fun k _ => neg_two_lt_partialR hκ hw k
  have hright := rightNoContactStatement κ hκ hκ4 (j + 1) n hj hn xL xR ρL ρR hF hxm' hxp hw.1 hw.2.2 hpsL hpsR
    P 𝓕 W VL VR B ζ hE htr
  filter_upwards [hE.2.2.2.2, hE.ae_tendsto_threshold hκ, ae_swallow hκ hκ4 hE hxL hxR hw, hright]
    with ω hp hlim hsw hr
  have hinf : ζ ω = ⊤ → (∀ t : ℝ≥0, VL ⟨j + 1 - 1, Nat.sub_lt hj one_pos⟩ t ω < W t ω) → False := by
    intro hζ hlt
    rw [hlast] at hlt
    rcases hsw with hne | ⟨t, -, heq⟩
    · exact hne hζ
    · exact lt_irrefl _ (heq ▸ hlt t)
  obtain ⟨τ, hτ⟩ := exists_isFirstFarContact hκ hj hF hp hlim hxm' hw.2.2 hpsL hpsR hinf
  rw [hlast] at hτ
  have hthr : κ - 4 ≤ -2 → (τ : ℝ≥0∞) = ζ ω := fun hk => by
    have := eq_zeta_of_isFirstFarContact hj hp hw.1 hk (by rw [hlast]; exact hτ)
    exact this
  exact ⟨⟨τ, hτ, hthr⟩, hr, fun hx => exists_crossing_of_contact_path hp (Fin.last j) hx hτ⟩

/-- **The leftward stage reaches its target inside a buffer** (pathwise almost surely; A.3's reach event): if the
designated far left labels (`i ≥ m_L`) all start at most `−3`, almost surely some `U_n` occurs. -/
theorem ae_exists_reachEvent_left_stage (hκ : 0 < κ) (hκ4 : κ < 4) (hn : 0 < n)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hF : IsOrderedForceWord xL xR)
    (hxL : StrictAnti xL) (hxR : StrictMono xR) (hxm : xL (Fin.last j) ≤ -3)
    (hxp : 0 < xR ⟨n - 1, Nat.sub_lt hn one_pos⟩) (hw : IsStageWord κ ρL ρR) {mL : ℕ}
    (hfar : ∀ i : Fin (j + 1), mL ≤ (i : ℕ) → xL i ≤ -3)
    (htr : ∀ᵐ ω ∂P, ∃ γ : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) γ) :
    ∀ᵐ ω ∂P, ∃ m : ℕ, ω ∈ reachEvent (m : ℝ≥0) leftTarget (leftBuf mL n m) W VL VR ζ := by
  have h8 := ae_stage_cross_left hκ hκ4 hn hE hF hxL hxR (by linarith) hxp hw htr
  filter_upwards [h8, hE.2.2.2.2] with ω hω hp
  obtain ⟨-, hnoR, hcross⟩ := hω
  obtain ⟨t, htζ, hwt, -⟩ := hcross hxm
  have hfp := hp.isForcePath
  have hfar' : ∀ i : Fin (j + 1), mL ≤ (i : ℕ) → ∀ u : ℝ≥0, (u : ℝ≥0∞) < ζ ω → VL i u ω ≤ -3 :=
    fun i hi u hu => (hfp.vL_le_of_le zero_le hu i).trans (by rw [hfp.vL_zero i]; exact hfar i hi)
  obtain ⟨m, t', ht'm, ht'ζ, hwt', hbuf⟩ := exists_reach_left_of_path (w := fun t => W t ω)
    (vL := fun i t => VL i t ω) (vR := fun k t => VR k t ω) hn hfp.continuousOn_w hfp.continuousOn_vL
    hfp.continuousOn_vR hfp.w_zero hfar' htζ hwt
    (fun u hu => hnoR u (lt_of_le_of_lt (by exact_mod_cast hu) htζ))
  exact ⟨m, t', ht'm, ht'ζ, hwt', fun u hu => hbuf u hu⟩

/-- **The leftward stage's reach probability tends to one**: `P(U_n) → 1`. -/
theorem tendsto_measure_reachEvent_left_stage [IsProbabilityMeasure P] (hκ : 0 < κ) (hκ4 : κ < 4) (hn : 0 < n)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hF : IsOrderedForceWord xL xR)
    (hxL : StrictAnti xL) (hxR : StrictMono xR) (hxm : xL (Fin.last j) ≤ -3)
    (hxp : 0 < xR ⟨n - 1, Nat.sub_lt hn one_pos⟩) (hw : IsStageWord κ ρL ρR) {mL : ℕ}
    (hfar : ∀ i : Fin (j + 1), mL ≤ (i : ℕ) → xL i ≤ -3)
    (htr : ∀ᵐ ω ∂P, ∃ γ : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) γ) :
    Tendsto (fun m : ℕ => P (reachEvent (m : ℝ≥0) leftTarget (leftBuf mL n m) W VL VR ζ)) atTop (𝓝 1) := by
  have hlim := tendsto_measure_iUnion_atTop (μ := P) (reachEvent_left_mono (nL := j + 1) (nR := n) mL W VL VR ζ)
  have hae := ae_exists_reachEvent_left_stage hκ hκ4 hn hE hF hxL hxR hxm hxp hw hfar htr
  have hone : P (⋃ m : ℕ, reachEvent (m : ℝ≥0) leftTarget (leftBuf mL n m) W VL VR ζ) = 1 := by
    refine le_antisymm prob_le_one ?_
    have hnull : P (⋃ m : ℕ, reachEvent (m : ℝ≥0) leftTarget (leftBuf mL n m) W VL VR ζ)ᶜ = 0 := by
      rw [ae_iff] at hae
      refine measure_mono_null (fun ω hω => ?_) hae
      simp only [mem_compl_iff, mem_iUnion, not_exists] at hω
      simp only [mem_ofPred_eq, not_exists]
      exact hω
    calc (1 : ℝ≥0∞) = P univ := measure_univ.symm
      _ ≤ P (⋃ m : ℕ, reachEvent (m : ℝ≥0) leftTarget (leftBuf mL n m) W VL VR ζ) +
          P (⋃ m : ℕ, reachEvent (m : ℝ≥0) leftTarget (leftBuf mL n m) W VL VR ζ)ᶜ := by
            rw [← union_compl_self (⋃ m : ℕ, reachEvent (m : ℝ≥0) leftTarget (leftBuf mL n m) W VL VR ζ)]
            exact measure_union_le _ _
      _ = _ := by rw [hnull, add_zero]
  rw [hone] at hlim
  exact hlim

/-- **A leftward buffer with reach probability `> 1 − δ`** ("choose a finite capacity horizon, a driver bound, and
positive lower bounds on the additional force-point gaps so that … the driver crosses the level `e_j(2+1/8)` before
this localization ends with probability larger than `1 − ε_j/4`"). -/
theorem exists_lt_measure_reachEvent_left_stage [IsProbabilityMeasure P] (hκ : 0 < κ) (hκ4 : κ < 4) (hn : 0 < n)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hF : IsOrderedForceWord xL xR)
    (hxL : StrictAnti xL) (hxR : StrictMono xR) (hxm : xL (Fin.last j) ≤ -3)
    (hxp : 0 < xR ⟨n - 1, Nat.sub_lt hn one_pos⟩) (hw : IsStageWord κ ρL ρR) {mL : ℕ}
    (hfar : ∀ i : Fin (j + 1), mL ≤ (i : ℕ) → xL i ≤ -3)
    (htr : ∀ᵐ ω ∂P, ∃ γ : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) γ) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ m : ℕ, 1 - δ < P (reachEvent (m : ℝ≥0) leftTarget (leftBuf mL n m) W VL VR ζ) := by
  have hlim := tendsto_measure_reachEvent_left_stage hκ hκ4 hn hE hF hxL hxR hxm hxp hw hfar htr
  have h1 : (1 : ℝ≥0∞) - δ < 1 := ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hδ.ne'
  exact (hlim.eventually (lt_mem_nhds h1)).exists

end Cross

/-! ### The rightward stage (angle `−π/2`), by reflection -/

section Right

variable {κ : ℝ} {nL j : ℕ} {xL : Fin nL → ℝ} {xR : Fin (j + 1) → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin (j + 1) → ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin (j + 1) → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **The rightward stage reaches its target inside a buffer** ("Reflection gives the angle-`−π/2` assertion"): for an
integrated evolution whose reflected word is a stage word (`IsStageWord κ ρR ρL`: right total `κ − 4`, left total
`κ/2 − 2`, Zhan's prefix sums), with distinct positions on each side, outermost right mark `x₊ ≥ 3` and designated far
right labels starting at least `3`, almost surely some rightward reach event `U_n` occurs. -/
theorem ae_exists_reachEvent_right_stage (hκ : 0 < κ) (hκ4 : κ < 4) (hnL : 0 < nL)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hF : IsOrderedForceWord xL xR)
    (hxL : StrictAnti xL) (hxR : StrictMono xR) (hxp : 3 ≤ xR (Fin.last j))
    (hxm : xL ⟨nL - 1, Nat.sub_lt hnL one_pos⟩ < 0) (hw : IsStageWord κ ρR ρL) {mR : ℕ}
    (hfar : ∀ k : Fin (j + 1), mR ≤ (k : ℕ) → 3 ≤ xR k)
    (htr : ∀ᵐ ω ∂P, ∃ γ : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) γ) :
    ∀ᵐ ω ∂P, ∃ m : ℕ, ω ∈ reachEvent (m : ℝ≥0) rightTarget (rightBuf nL mR m) W VL VR ζ := by
  have hEr := IsIntegratedSLEEvolution.reflect hE
  have htr' : ∀ᵐ ω ∂P, ∃ γ : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => (-W) t ω) (ζ ω) γ := by
    filter_upwards [htr] with ω ⟨γ, hγ⟩
    exact ⟨fun t => LP.reflectC (γ t), LP.isGeneratingTrace_reflect hγ⟩
  have hxm' : (-xR) (Fin.last j) ≤ -3 := by simp only [Pi.neg_apply]; linarith
  have hxp' : 0 < (-xL) ⟨nL - 1, Nat.sub_lt hnL one_pos⟩ := by simp only [Pi.neg_apply]; linarith
  have hfar' : ∀ k : Fin (j + 1), mR ≤ (k : ℕ) → (-xR) k ≤ -3 := fun k hk => by
    simp only [Pi.neg_apply]; linarith [hfar k hk]
  have h := ae_exists_reachEvent_left_stage (P := P) hκ hκ4 hnL hEr (isOrderedForceWord_reflect hF)
    (fun a b hab => neg_lt_neg (hxR hab)) (fun a b hab => neg_lt_neg (hxL hab)) hxm' hxp' hw hfar' htr'
  filter_upwards [h] with ω ⟨m, t, htm, htζ, hO, hB⟩
  refine ⟨m, t, htm, htζ, ?_, fun u hu => ?_⟩
  · have : -W t ω < -(2 + 1 / 8) := hO
    show 2 + 1 / 8 < W t ω
    linarith
  · exact mem_leftBuf_reflect_iff.1 (hB u hu)

/-- **A rightward buffer with reach probability `> 1 − δ`.** -/
theorem exists_lt_measure_reachEvent_right_stage [IsProbabilityMeasure P] (hκ : 0 < κ) (hκ4 : κ < 4)
    (hnL : 0 < nL) (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hF : IsOrderedForceWord xL xR)
    (hxL : StrictAnti xL) (hxR : StrictMono xR) (hxp : 3 ≤ xR (Fin.last j))
    (hxm : xL ⟨nL - 1, Nat.sub_lt hnL one_pos⟩ < 0) (hw : IsStageWord κ ρR ρL) {mR : ℕ}
    (hfar : ∀ k : Fin (j + 1), mR ≤ (k : ℕ) → 3 ≤ xR k)
    (htr : ∀ᵐ ω ∂P, ∃ γ : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) γ) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ m : ℕ, 1 - δ < P (reachEvent (m : ℝ≥0) rightTarget (rightBuf nL mR m) W VL VR ζ) := by
  have hlim := tendsto_measure_iUnion_atTop (μ := P)
    (reachEvent_right_mono (nL := nL) (nR := j + 1) mR W VL VR ζ)
  have hae := ae_exists_reachEvent_right_stage hκ hκ4 hnL hE hF hxL hxR hxp hxm hw hfar htr
  have hone : P (⋃ m : ℕ, reachEvent (m : ℝ≥0) rightTarget (rightBuf nL mR m) W VL VR ζ) = 1 := by
    refine le_antisymm prob_le_one ?_
    have hnull : P (⋃ m : ℕ, reachEvent (m : ℝ≥0) rightTarget (rightBuf nL mR m) W VL VR ζ)ᶜ = 0 := by
      rw [ae_iff] at hae
      refine measure_mono_null (fun ω hω => ?_) hae
      simp only [mem_compl_iff, mem_iUnion, not_exists] at hω
      simp only [mem_ofPred_eq, not_exists]
      exact hω
    calc (1 : ℝ≥0∞) = P univ := measure_univ.symm
      _ ≤ P (⋃ m : ℕ, reachEvent (m : ℝ≥0) rightTarget (rightBuf nL mR m) W VL VR ζ) +
          P (⋃ m : ℕ, reachEvent (m : ℝ≥0) rightTarget (rightBuf nL mR m) W VL VR ζ)ᶜ := by
            rw [← union_compl_self (⋃ m : ℕ, reachEvent (m : ℝ≥0) rightTarget (rightBuf nL mR m) W VL VR ζ)]
            exact measure_union_le _ _
      _ = _ := by rw [hnull, add_zero]
  rw [hone] at hlim
  have h1 : (1 : ℝ≥0∞) - δ < 1 := ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hδ.ne'
  exact (hlim.eventually (lt_mem_nhds h1)).exists

end Right

end Prop59Tips

end Sec5

end InteractingSLE
