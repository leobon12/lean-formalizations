/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1RestartFinalRun
import InteractingSLE.Spec.Supplement.WalkPieceProof
import InteractingSLE.Spec.Supplement.WalkMarkedLocal
import InteractingSLE.Spec.Restart.MarkovChart

/-!
# Theorem 1.4's walk pieces read in their launch chart (deterministic)

Packet PROVE-T14-WALK (the launch-locality leaf `WalkLaw.WalkStageLaunchLocalStatement`). Along a run whose launched
pieces are regular, the chart `c` of the state after `k` instructions is conformal, its inverse stays within bounded
distance of the identity (`GW1P.HasProperBdryExt`, `WalkPiece.pieces_run_regular`), and its finite boundary values lie
on the recorded past or off `ℍ` (`GW1RestartFinal.chart_boundaryRange_run`). Hence:

* **`mem_of_frontier_dom`**, **`mem_stageSet_of_frontier`**: a point of `ℍ` on the frontier of the chart domain lies on
  the explored set `stageSet k` (a sequence in the domain converging to it has bounded chart preimages, whose limit
  point is real: there the inverse has its boundary value);
* **`disjoint_pieceSet_iff`**: for an open `U ⊆ ℍ` avoided by the explored set, the piece launched by instruction `k`
  avoids `U` exactly when its chart trace avoids the chart pre-image `chartPre c U` (the boundary values of the chart
  at the real points of the trace lie on the explored set or off `ℍ`, hence off `U`; WALKLAW3 §5 (a) 3 (i));
* `firstEntrance_eq_top_iff`: a continuous path never enters an open set exactly when its first entrance time is `⊤`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Bornology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.WalkLeaf

open Exist.Staged Exist.StagedLaw

/-! ### The frontier of a chart domain -/

theorem isClosed_Hbar : IsClosed Hbar := isClosed_le continuous_const Complex.continuous_im

theorem H_subset_Hbar : H ⊆ Hbar := fun _ hz => le_of_lt (show (0 : ℝ) < _ from hz)

/-- **A point of `ℍ` on the frontier of the domain of a good conformal chart is a boundary value of the chart**, hence
lies on any set `A` carrying its finite boundary values in `ℍ`. -/
theorem mem_of_frontier_dom {c : Chart} (hcc : c.IsConformal) (hc : GW1P.HasProperBdryExt c) {A : Set ℂ}
    (hA : GW1RestartFinal.HasBoundaryRange c A) {z : ℂ} (hzH : z ∈ H) (hzcl : z ∈ closure (c.dom : Set ℂ))
    (hzD : z ∉ c.dom) : z ∈ A := by
  obtain ⟨f, C, hf, hC⟩ := hc
  obtain ⟨g, hg, hr⟩ := hA
  rw [hcc.coe_dom] at hzcl
  have hzD' : z ∉ c.2.1 '' H := fun h => hzD (by rw [← SetLike.mem_coe, hcc.coe_dom]; exact h)
  obtain ⟨w, hw, hwz⟩ := mem_closure_iff_seq_limit.1 hzcl
  choose y hyH hyw using hw
  -- the chart preimages are bounded
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 (Metric.isBounded_range_of_tendsto w hwz)
  have hyb : IsBounded (range y) := by
    refine isBounded_iff_forall_norm_le.2 ⟨R + C, ?_⟩
    rintro _ ⟨n, rfl⟩
    have h1 : ‖f (y n) - y n‖ ≤ C := hC _ (H_subset_Hbar (hyH n))
    have h2 : f (y n) = w n := by rw [WalkPiece.bdry_eq_inv_of_mem_H hcc hf (hyH n), hyw n]
    have h3 : ‖w n‖ ≤ R := hR _ ⟨n, rfl⟩
    calc ‖y n‖ = ‖w n - (f (y n) - y n)‖ := by rw [h2]; ring_nf
      _ ≤ ‖w n‖ + ‖f (y n) - y n‖ := norm_sub_le _ _
      _ ≤ R + C := add_le_add h3 h1
  obtain ⟨y₀, hy₀, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded hyb fun n => mem_range_self n
  have hy₀H : y₀ ∈ Hbar :=
    closure_minimal (range_subset_iff.2 fun n => H_subset_Hbar (hyH n)) isClosed_Hbar hy₀
  have hwφ : Tendsto (fun n => c.2.1 (y (φ n))) atTop (𝓝 z) := by
    have := hwz.comp hφ.tendsto_atTop
    refine this.congr fun n => ?_
    simp only [Function.comp_apply, hyw]
  by_cases hy₀' : y₀ ∈ H
  · exfalso
    have hcont : ContinuousAt c.2.1 y₀ :=
      (hcc.1.differentiableAt (QuantumZipper.isOpen_H.mem_nhds hy₀')).continuousAt
    have h2 : Tendsto (fun n => c.2.1 (y (φ n))) atTop (𝓝 (c.2.1 y₀)) := hcont.tendsto.comp hlim
    exact hzD' ⟨y₀, hy₀', tendsto_nhds_unique h2 hwφ⟩
  · have hlimH : Tendsto (fun n => y (φ n)) atTop (𝓝[H] y₀) :=
      tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall fun n => hyH _⟩
    have hz : g y₀ = z := tendsto_nhds_unique ((hg y₀ hy₀H).comp hlimH) hwφ
    rcases hr y₀ hy₀H hy₀' with h | h
    · rwa [← hz]
    · exact absurd (hz ▸ hzH) h

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- The points of `ℍ` of the recorded physical set are on the explored set. -/
theorem mem_stageSet_of_mem_prefixPhysSet {Ω : Type*} (spec : ExplSpec) (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ)
    (ω : Ω) {z : ℂ} (hz : z ∈ SB.prefixPhysSet κ b jumps spec (fun j => E j ω) k) (hzH : z ∈ H) :
    z ∈ WalkLaw.stageSet κ b jumps spec E k ω := by
  refine ⟨?_, hzH⟩
  rcases hz with (hz | hz) | hz
  · rw [mem_singleton_iff] at hz
    exact absurd (hz ▸ hzH) (WalkPiece.ofReal_notMem_H _)
  · exact hz
  · obtain ⟨a, -, x, -, rfl⟩ := mem_iUnion₂.1 hz
    exact absurd hzH (WalkPiece.ofReal_notMem_H _)

/-- **The frontier of a run chart's domain in `ℍ` lies on the explored set** (launched pieces regular). -/
theorem mem_stageSet_of_frontier {Ω : Type*} (spec : ExplSpec) (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (ω : Ω)
    (hreg : ∀ (k : ℕ) (c : Chart) (θ : ℝ), (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k =
      some (c, θ) → GW1P.PieceRegular (E k ω).1 (min (instrTime spec k) (E k ω).2)) (k : ℕ) :
    ∀ z ∈ H, z ∈ closure ((stChart (ExplState.run κ b jumps spec (fun j => E j ω) k)).dom : Set ℂ) →
      z ∉ (stChart (ExplState.run κ b jumps spec (fun j => E j ω) k)).dom →
        z ∈ WalkLaw.stageSet κ b jumps spec E k ω := by
  intro z hzH hzcl hzD
  obtain ⟨hcc, hA⟩ := GW1RestartFinal.chart_boundaryRange_run spec (fun j => E j ω) hreg k
  have hc := ((WalkPiece.pieces_run_regular (κ := κ) (b := b) (jumps := jumps) spec (fun j => E j ω) hreg k).1).2
  exact mem_stageSet_of_mem_prefixPhysSet spec E k ω (mem_of_frontier_dom hcc hc hA hzH hzcl hzD) hzH

/-! ### Avoidance by a launched piece, read in its chart -/

/-- **A launched piece avoids an open `U ⊆ ℍ` off the explored set exactly when its chart trace avoids the chart
pre-image of `U`.** -/
theorem disjoint_pieceSet_iff {Ω : Type*} (spec : ExplSpec) (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (ω : Ω)
    (hreg : ∀ (k : ℕ) (c : Chart) (θ : ℝ), (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k =
      some (c, θ) → GW1P.PieceRegular (E k ω).1 (min (instrTime spec k) (E k ω).2)) {k : ℕ} {c : Chart} {θ : ℝ}
    (hl : (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k = some (c, θ))
    {U : Set ℂ} (hUH : U ⊆ H) (hdU : Disjoint (WalkLaw.stageSet κ b jumps spec E k ω) U) {α : ℝ≥0 → ℂ}
    (hα : IsGeneratingTrace (E k ω).1 (min (instrTime spec k) (E k ω).2) α) :
    Disjoint (WalkLaw.pieceSet κ b jumps spec E k ω) U ↔
      ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ min (instrTime spec k) (E k ω).2 → α t ∉ Restart.MarkovChart.chartPre c U := by
  set S := min (instrTime spec k) (E k ω).2 with hSdef
  have hr := hreg k c θ hl
  obtain ⟨-, -, hcS⟩ := eq_launch_of_launches (κ := κ) (b := b) (jumps := jumps) spec (fun j => E j ω) hl
  obtain ⟨hcc, hA⟩ := GW1RestartFinal.chart_boundaryRange_run spec (fun j => E j ω) hreg k
  change (ExplState.run κ b jumps spec (fun j => E j ω) k).2.2.2.2.1.IsConformal at hcc
  rw [← hcS] at hcc
  obtain ⟨g, hg, hgr⟩ := hA
  change ∀ p ∈ Hbar, Tendsto (ExplState.run κ b jumps spec (fun j => E j ω) k).2.2.2.2.1.2.1 (𝓝[H] p) (𝓝 (g p))
    at hg
  rw [← hcS] at hg
  have hW0 : (E k ω).1 0 = 0 := hr.1
  have hWc : ContinuousOn (E k ω).1 {t | (t : ℝ≥0∞) ≤ S} := hr.2.1
  have hWlt : ContinuousOn (E k ω).1 {t | (t : ℝ≥0∞) < S} :=
    hWc.mono fun t (ht : (t : ℝ≥0∞) < S) => (le_of_lt ht : (t : ℝ≥0∞) ≤ S)
  have hαH : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ S → α t ∈ Hbar := fun t ht =>
    Sec7.IsGeneratingTrace.mem_Hbar hα hWlt hW0 ht
  have hne : (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none := by
    rw [hl]; exact Option.some_ne_none _
  have hP : WalkLaw.pieceSet κ b jumps spec E k ω = g '' (α '' {t | (t : ℝ≥0∞) ≤ S}) ∩ H := by
    simp only [WalkLaw.pieceSet, hne, ↓reduceIte]
    rw [← hcS, ← hSdef, CounterflowRange.tipSet_stopped_eq_of_tendsto hα hWc hW0 fun t ht => hg _ (hαH t ht)]
  -- the boundary reading
  have hread : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ S → (g (α t) ∈ U ↔ α t ∈ Restart.MarkovChart.chartPre c U) := by
    intro t ht
    by_cases hαt : α t ∈ H
    · rw [WalkPiece.bdry_eq_inv_of_mem_H hcc hg hαt]
      exact ⟨fun h => ⟨hαt, h⟩, And.right⟩
    · refine ⟨fun h => ?_, fun h => absurd h.1 hαt⟩
      exfalso
      rcases hgr _ (hαH t ht) hαt with h' | h'
      · have hzH : g (α t) ∈ H := hUH h
        exact Set.disjoint_left.1 hdU (mem_stageSet_of_mem_prefixPhysSet spec E k ω h' hzH) h
      · exact h' (hUH h)
  rw [hP]
  constructor
  · intro hd t ht hpre
    exact Set.disjoint_left.1 hd ⟨⟨α t, ⟨t, ht, rfl⟩, rfl⟩, hUH ((hread t ht).2 hpre)⟩ ((hread t ht).2 hpre)
  · intro h
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨⟨_, ⟨t, ht, rfl⟩, rfl⟩, -⟩ hU
    exact h t ht ((hread t ht).1 hU)

/-! ### First entrance -/

/-- A continuous path never enters an open set exactly when its first entrance time is `⊤`. -/
theorem firstEntrance_eq_top_iff {V : Set ℂ} (hV : IsOpen V) {γ : ℝ≥0 → ℂ} (hγ : Continuous γ) :
    Sec6.firstEntrance V (Sec6.pathCoord γ) = ⊤ ↔ ∀ t, γ t ∉ V := by
  constructor
  · intro htop t ht
    obtain ⟨q, -, hq⟩ := Sec6.exists_rat_le_mem hV hγ ht
    have hle := Sec6.firstEntrance_le (U := V) (c := Sec6.pathCoord γ) (q := q) hq
    rw [htop] at hle
    exact ENNReal.coe_ne_top (top_le_iff.1 hle)
  · intro h
    exact iInf₂_eq_top.2 fun q hq => absurd hq (h q)

/-- A trace frozen at `S` avoids a set exactly when the trace avoids it on `[0, S]`. -/
theorem forall_frozen_notMem_iff {α : ℝ≥0 → ℂ} {S : ℝ≥0∞} {V : Set ℂ} :
    (∀ t : ℝ≥0, α (min (t : ℝ≥0∞) S).toNNReal ∉ V) ↔ ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ S → α t ∉ V := by
  constructor
  · intro h t ht
    have := h t
    rwa [min_eq_left ht, ENNReal.toNNReal_coe] at this
  · intro h t
    refine h _ ?_
    exact ENNReal.coe_toNNReal_le_self.trans (min_le_right _ _)

end InteractingSLE.Theorem14.WalkLeaf
