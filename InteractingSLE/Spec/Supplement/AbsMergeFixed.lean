/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.AbsMergePath
import InteractingSLE.Spec.Sec2.TerminalEvolution
import InteractingSLE.Spec.Sec4.RepulsionNoncollision

/-!
# No force collision at a fixed time

Packet PROVE-ABSMERGE. For an integrated `SLE_κ(ρ)` evolution (any `κ > 0`, ordered force word) and a deterministic
time `t > 0`, almost surely on `{t < ζ}` no force point is on the driver at `t`
(**`ae_forall_ne_of_isIntegratedSLEEvolution`**). In particular a fixed time is almost surely not an absorbed merge
(`AbsMergeFlow`).

**Proof (right side).** Suppose the right marks `0, …, k` meet the driver at `t` (an initial segment; its weight
`S = ∑_{l ≤ k} ρ_l > −2` because `t < ζ`), the others stay away. Along the grid `a_n ↑ t` let
`x_n = Γ(a_n) / (√κ √(t − a_n))` with `Γ` of `AbsMergePath`, and `Z_n = (B_t − B_{a_n}) / √(t − a_n)`. The
pathwise bounds of `AbsMergePath` give, on the event `colEvent` (collision of exactly that group, outer marks moving by
at most `√(t − a_n)` after `a_N`):

* `x_n − 1/√κ ≤ Z_n` for `n ≥ N` (`gamR_sub_le`), and
* `x_n → −∞ ⇒ Z_n ≤ x_n + C/√κ` eventually (`sqrt_mul_le_gamR_add`), so `Z_n → −∞`.

`colEvent` belongs to `⨆ₙ 𝓕_{a_n}` (the processes are adapted before `ζ`; we use their values killed at `ζ`, which
agree with them at the grid points on the event) and `x_n` is `𝓕_{a_n}`-measurable, so Lévy's 0–1 law against the fresh
Gaussian increment (`measure_eq_zero_of_lowerBound`) gives `P(colEvent) = 0`. Every right collision at `t` lies in
one of the countably many events `colEvent t … k N` (`exists_abs_farR_le`). The left side is the right side of the
reflected evolution (`IsIntegratedSLEEvolution.reflect`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Finset
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Theorem14

namespace AbsMerge

open Sec2 GW2aForce

/-! ### Killed processes -/

section Kill

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ} {ζ : Ω → ℝ≥0∞}

/-- The process killed at `ζ` (value `0` from `ζ` on). -/
def kill (ζ : Ω → ℝ≥0∞) (X : ℝ≥0 → Ω → ℝ) (s : ℝ≥0) (ω : Ω) : ℝ :=
  if (s : ℝ≥0∞) < ζ ω then X s ω else 0

theorem kill_of_lt {X : ℝ≥0 → Ω → ℝ} {s : ℝ≥0} {ω : Ω} (h : (s : ℝ≥0∞) < ζ ω) : kill ζ X s ω = X s ω := by
  simp only [kill, h, ↓reduceIte]

/-- A process adapted before `ζ`, killed at `ζ`, is adapted. -/
theorem measurable_kill {X : ℝ≥0 → Ω → ℝ} (hX : AdaptedBefore 𝓕 ζ X) (s : ℝ≥0) :
    Measurable[𝓕 s] (kill ζ X s) := by
  intro A hA
  have h1 := hX s A hA
  have h2 : MeasurableSet[𝓕 s] {ω | (s : ℝ≥0∞) < ζ ω} := by
    have := hX s univ MeasurableSet.univ
    simpa only [mem_univ, and_true] using this
  have heq : kill ζ X s ⁻¹' A = {ω | (s : ℝ≥0∞) < ζ ω ∧ X s ω ∈ A} ∪
      ({ω | (s : ℝ≥0∞) < ζ ω}ᶜ ∩ {_ω | (0 : ℝ) ∈ A}) := by
    ext ω
    simp only [kill, Set.mem_preimage, Set.mem_union, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_compl_iff]
    split_ifs with h <;> simp [h]
  rw [heq]
  exact h1.union (h2.compl.inter (MeasurableSet.const _))

end Kill

/-! ### The event of one colliding group -/

section Event

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- The event that the right marks `0, …, k` collide with the driver at `t` along the grid and the other marks move by
at most `√(t − a_n)` after `a_N` (stated for the killed processes). -/
def colEvent (t : ℝ≥0) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
    (VR : Fin nR → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (k : Fin nR) (N : ℕ) : Set Ω :=
  {ω | (∀ n, (grid t n : ℝ≥0∞) < ζ ω) ∧
    (∀ l, l ≤ k → Tendsto (fun n => kill ζ (VR l) (grid t n) ω - kill ζ W (grid t n) ω) atTop (𝓝 0)) ∧
    ∀ n, N ≤ n → ∀ j, n ≤ j →
      |farR ρL ρR (fun i s => kill ζ (VL i) s ω) (fun i s => kill ζ (VR i) s ω) k (grid t n) (grid t j)| ≤
        Real.sqrt ((t : ℝ) - grid t n)}

/-- The variable `x_n = Γ(a_n) / (√κ √(t − a_n))` (of the killed processes). -/
def xSeq (κ : ℝ) (t : ℝ≥0) (ρR : Fin nR → ℝ) (W : ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
    (k : Fin nR) (n : ℕ) (ω : Ω) : ℝ :=
  gamR ρR (fun s => kill ζ W s ω) (fun i s => kill ζ (VR i) s ω) k (grid t n) /
    (Real.sqrt κ * Real.sqrt ((t : ℝ) - grid t n))

theorem measurable_xSeq (hW : AdaptedBefore 𝓕 ζ W) (hVR : ∀ i, AdaptedBefore 𝓕 ζ (VR i)) (t : ℝ≥0)
    (k : Fin nR) (n : ℕ) : Measurable[𝓕 (grid t n)] (xSeq κ t ρR W VR ζ k n) := by
  have hw := measurable_kill hW (grid t n)
  have hv := fun i => measurable_kill (hVR i) (grid t n)
  unfold xSeq gamR
  refine Measurable.div_const (((hv k).sub hw).add (Finset.measurable_sum _ fun l _ => ?_)) _
  exact ((hv k).sub (hv l)).const_mul _

theorem measurableSet_colEvent (hW : AdaptedBefore 𝓕 ζ W) (hVL : ∀ i, AdaptedBefore 𝓕 ζ (VL i))
    (hVR : ∀ i, AdaptedBefore 𝓕 ζ (VR i)) (t : ℝ≥0) (k : Fin nR) (N : ℕ) :
    MeasurableSet[⨆ n, 𝓕 (grid t n)] (colEvent t ρL ρR W VL VR ζ k N) := by
  set m := ⨆ n, 𝓕 (grid t n) with hm
  have hle : ∀ n, 𝓕 (grid t n) ≤ m := fun n => le_iSup (fun n => 𝓕 (grid t n)) n
  have hkm : ∀ (X : ℝ≥0 → Ω → ℝ), AdaptedBefore 𝓕 ζ X → ∀ n, Measurable[m] (kill ζ X (grid t n)) :=
    fun X hX n => (measurable_kill hX (grid t n)).mono (hle n) le_rfl
  have h1 : MeasurableSet[m] {ω | ∀ n, (grid t n : ℝ≥0∞) < ζ ω} := by
    rw [Set.ofPred_forall]
    refine MeasurableSet.iInter fun n => hle n _ ?_
    have := hW (grid t n) univ MeasurableSet.univ
    simpa only [mem_univ, and_true] using this
  have h2 : MeasurableSet[m] {ω | ∀ l, l ≤ k →
      Tendsto (fun n => kill ζ (VR l) (grid t n) ω - kill ζ W (grid t n) ω) atTop (𝓝 0)} := by
    rw [Set.ofPred_forall]
    refine MeasurableSet.iInter fun l => ?_
    rw [Set.ofPred_forall]
    refine MeasurableSet.iInter fun _ => ?_
    exact measurableSet_tendsto (𝓝 0) fun n => (hkm _ (hVR l) n).sub (hkm _ hW n)
  have h3 : MeasurableSet[m] {ω | ∀ n, N ≤ n → ∀ j, n ≤ j →
      |farR ρL ρR (fun i s => kill ζ (VL i) s ω) (fun i s => kill ζ (VR i) s ω) k (grid t n) (grid t j)| ≤
        Real.sqrt ((t : ℝ) - grid t n)} := by
    rw [Set.ofPred_forall]
    refine MeasurableSet.iInter fun n => ?_
    rw [Set.ofPred_forall]
    refine MeasurableSet.iInter fun _ => ?_
    rw [Set.ofPred_forall]
    refine MeasurableSet.iInter fun j => ?_
    rw [Set.ofPred_forall]
    refine MeasurableSet.iInter fun _ => ?_
    refine measurableSet_le (continuous_abs.measurable.comp ?_) measurable_const
    unfold farR
    refine Measurable.add (Finset.measurable_sum _ fun l _ => ?_) (Finset.measurable_sum _ fun i _ => ?_)
    · exact ((hkm _ (hVR l) j).sub (hkm _ (hVR l) n)).const_mul _
    · exact ((hkm _ (hVL i) j).sub (hkm _ (hVL i) n)).const_mul _
  exact h1.inter (h2.inter h3)

end Event

/-! ### The colliding-group event is null; no collision at a fixed time -/

section Right

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞}

/-- **The event of one colliding group is null** (Lévy's 0–1 law against the fresh Gaussian increment). -/
theorem measure_colEvent_eq_zero (hκ : 0 < κ) (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    {t : ℝ≥0} (ht : 0 < t) {k : Fin nR} (hS : -2 < partialR ρR k) (N : ℕ) :
    P (colEvent t ρL ρR W VL VR ζ k N) = 0 := by
  have hsκ : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  -- on the event, the killed processes are the processes at the grid points
  have hconv : ∀ ω ∈ colEvent t ρL ρR W VL VR ζ k N,
      (∀ n, (grid t n : ℝ≥0∞) < ζ ω) ∧
      (∀ l, l ≤ k → Tendsto (fun n => VR l (grid t n) ω - W (grid t n) ω) atTop (𝓝 0)) ∧
      (∀ n, N ≤ n → ∀ j, n ≤ j → |farR ρL ρR (fun i s => VL i s ω) (fun i s => VR i s ω) k (grid t n)
        (grid t j)| ≤ Real.sqrt ((t : ℝ) - grid t n)) ∧
      ∀ n, xSeq κ t ρR W VR ζ k n ω = gamR ρR (fun s => W s ω) (fun i s => VR i s ω) k (grid t n) /
        (Real.sqrt κ * Real.sqrt ((t : ℝ) - grid t n)) := by
    intro ω hω
    obtain ⟨hζ, hcol, hfar⟩ := hω
    refine ⟨hζ, fun l hl => (hcol l hl).congr fun n => ?_, fun n hn j hj => ?_, fun n => ?_⟩
    · rw [kill_of_lt (hζ n), kill_of_lt (hζ n)]
    · have := hfar n hn j hj
      simp only [farR, kill_of_lt (hζ n), kill_of_lt (hζ j)] at this
      simpa only [farR] using this
    · simp only [xSeq, gamR, kill_of_lt (hζ n)]
  have hbt : ∀ᵐ ω ∂P, Tendsto (fun n => B (grid t n) ω) atTop (𝓝 (B t ω)) := by
    filter_upwards [hE.ae_continuous_B] with ω hB
    exact (hB.tendsto t).comp (tendsto_grid t)
  refine measure_eq_zero_of_lowerBound hE.isFilteredBrownianReal ht
    (measurableSet_colEvent hE.adaptedBefore_W hE.adaptedBefore_VL hE.adaptedBefore_VR t k N)
    (x := xSeq κ t ρR W VR ζ k) (measurable_xSeq hE.adaptedBefore_W hE.adaptedBefore_VR t k)
    (c := 1 / Real.sqrt κ) (N := N) ?_ ?_
  · filter_upwards [hE.ae_isIntegratedSLEPath, hbt] with ω hp hb hω n hn
    obtain ⟨hζ, hcol, hfar, hx⟩ := hconv ω hω
    have hl := gamR_sub_le hp hζ hb hS hcol hfar hn
    have hd : 0 < Real.sqrt ((t : ℝ) - grid t n) := Real.sqrt_pos.2 (sub_grid_pos ht n)
    rw [hx n, normIncr, sub_le_iff_le_add, div_le_iff₀ (mul_pos hsκ hd)]
    have e1 : ((B t ω - B (grid t n) ω) / Real.sqrt ((t : ℝ) - grid t n) + 1 / Real.sqrt κ) *
        (Real.sqrt κ * Real.sqrt ((t : ℝ) - grid t n)) =
        Real.sqrt κ * (B t ω - B (grid t n) ω) + Real.sqrt ((t : ℝ) - grid t n) := by
      field_simp
    rw [e1]
    linarith
  · filter_upwards [hE.ae_isIntegratedSLEPath, hbt] with ω hp hb hω hxbot
    obtain ⟨hζ, hcol, hfar, hx⟩ := hconv ω hω
    obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 (tendsto_atBot.1 hxbot (-1))
    have hneg : ∀ j, n₀ ≤ j → gamR ρR (fun s => W s ω) (fun i s => VR i s ω) k (grid t j) ≤
        -(Real.sqrt κ * Real.sqrt ((t : ℝ) - grid t j)) := by
      intro j hj
      have h1 := hn₀ j hj
      have hd : 0 < Real.sqrt ((t : ℝ) - grid t j) := Real.sqrt_pos.2 (sub_grid_pos ht j)
      rw [hx j, div_le_iff₀ (mul_pos hsκ hd)] at h1
      linarith
    refine tendsto_atBot_mono' _ ?_ (tendsto_atBot_add_const_right _ (upC κ ρR k / Real.sqrt κ) hxbot)
    filter_upwards [eventually_ge_atTop (max n₀ N)] with n hn
    have hup := sqrt_mul_le_gamR_add hp hκ ht hζ hb hS hcol hfar hneg (le_of_max_le_left hn)
      (le_of_max_le_right hn)
    have hd : 0 < Real.sqrt ((t : ℝ) - grid t n) := Real.sqrt_pos.2 (sub_grid_pos ht n)
    rw [hx n, normIncr, div_le_iff₀ hd]
    have e1 : (gamR ρR (fun s => W s ω) (fun i s => VR i s ω) k (grid t n) /
        (Real.sqrt κ * Real.sqrt ((t : ℝ) - grid t n)) + upC κ ρR k / Real.sqrt κ) *
        Real.sqrt ((t : ℝ) - grid t n) =
        (gamR ρR (fun s => W s ω) (fun i s => VR i s ω) k (grid t n) +
          upC κ ρR k * Real.sqrt ((t : ℝ) - grid t n)) / Real.sqrt κ := by
      field_simp
    rw [e1, le_div_iff₀ hsκ]
    linarith

/-- **No right force collision at a fixed time.** -/
theorem ae_forall_ne_vR (hκ : 0 < κ) (hF : IsOrderedForceWord xL xR)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) {t : ℝ≥0} (ht : 0 < t) :
    ∀ᵐ ω ∂P, (t : ℝ≥0∞) < ζ ω → ∀ j, W t ω ≠ VR j t ω := by
  classical
  have hae : ∀ᵐ ω ∂P, ∀ k : Fin nR, ∀ N : ℕ, -2 < partialR ρR k → ω ∉ colEvent t ρL ρR W VL VR ζ k N := by
    rw [ae_all_iff]
    intro k
    rw [ae_all_iff]
    intro N
    by_cases hk : -2 < partialR ρR k
    · filter_upwards [measure_eq_zero_iff_ae_notMem.1 (measure_colEvent_eq_zero hκ hE ht hk N)] with ω hω _
      exact hω
    · exact ae_of_all _ fun ω h => absurd h hk
  filter_upwards [hE.ae_isIntegratedSLEPath, hae] with ω hp hnot htζ j hj
  have hfp := hp.isForcePath
  obtain ⟨m, hmn, hm⟩ := exists_eq_iff_lt (fun i => VR i t ω) (W t ω) (hfp.monotone_vR htζ) (hfp.w_le_vR htζ)
  have hjm : j.val < m := (hm j).1 hj.symm
  set k : Fin nR := ⟨m - 1, by omega⟩ with hk_def
  have hlk : ∀ l : Fin nR, l ≤ k ↔ VR l t ω = W t ω := fun l => by
    rw [hm l, Fin.le_def]
    show l.val ≤ m - 1 ↔ l.val < m
    omega
  have hS : -2 < partialR ρR k := by
    have hnt := hfp.not_threshold htζ
    unfold ForceWord.ThresholdCondition at hnt
    push Not at hnt
    have hfilt : univ.filter (fun i : Fin nR => VR i t ω = W t ω) = univ.filter (fun l : Fin nR => l ≤ k) :=
      Finset.filter_congr fun l _ => (hlk l).symm
    rw [partialR, ← hfilt]
    exact hnt.2
  have hR : ∀ l, ¬ l ≤ k → W t ω < VR l t ω := fun l hl =>
    lt_of_le_of_ne (hfp.w_le_vR htζ l) fun h => hl ((hlk l).2 h.symm)
  have hL : ∀ i, VL i t ω < W t ω := fun i => by
    have := hp.vL_lt_vR_of_pos hF ht htζ i j
    rwa [← hj] at this
  obtain ⟨N, hN⟩ := exists_abs_farR_le hfp ht htζ hR hL
  have hζn : ∀ n, (grid t n : ℝ≥0∞) < ζ ω := fun n => lt_trans (by exact_mod_cast grid_lt ht n) htζ
  have hopen : IsOpen {s : ℝ≥0 | (s : ℝ≥0∞) < ζ ω} := isOpen_lt ENNReal.continuous_coe continuous_const
  have hnhds : {s : ℝ≥0 | (s : ℝ≥0∞) < ζ ω} ∈ 𝓝 t := hopen.mem_nhds htζ
  refine hnot k N hS ⟨hζn, fun l hl => ?_, fun n hn j' hj' => ?_⟩
  · have hc : ContinuousAt (fun s => VR l s ω - W s ω) t :=
      ((hfp.continuousOn_vR l).continuousAt hnhds).sub (hfp.continuousOn_w.continuousAt hnhds)
    have := hc.tendsto.comp (tendsto_grid t)
    rw [(hlk l).1 hl, sub_self] at this
    refine this.congr fun n => ?_
    simp only [Function.comp_apply, kill_of_lt (hζn n)]
  · simp only [farR, kill_of_lt (hζn n), kill_of_lt (hζn j')]
    have := hN n hn j' hj'
    simpa only [farR] using this

/-- **No force collision at a fixed time**: for an integrated `SLE_κ(ρ)` evolution (`κ > 0`, ordered word) and a
deterministic `t > 0`, almost surely on `{t < ζ}` every force point is off the driver at `t`. -/
theorem ae_forall_ne_of_isIntegratedSLEEvolution (hκ : 0 < κ) (hF : IsOrderedForceWord xL xR)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) {t : ℝ≥0} (ht : 0 < t) :
    ∀ᵐ ω ∂P, (t : ℝ≥0∞) < ζ ω → (∀ i, W t ω ≠ VL i t ω) ∧ ∀ j, W t ω ≠ VR j t ω := by
  have hF' : IsOrderedForceWord (-xR) (-xL) :=
    ⟨fun _ _ h => neg_le_neg (hF.2.2.1 h), fun i => neg_nonpos.2 (hF.2.2.2 i),
      fun _ _ h => neg_le_neg (hF.1 h), fun i => neg_nonneg.2 (hF.2.1 i)⟩
  filter_upwards [ae_forall_ne_vR hκ hF hE ht, ae_forall_ne_vR hκ hF' hE.reflect ht] with ω hR hL htζ
  refine ⟨fun i h => hL htζ i ?_, hR htζ⟩
  simp only [Pi.neg_apply, h]

end Right

end AbsMerge

end Theorem14

end InteractingSLE
