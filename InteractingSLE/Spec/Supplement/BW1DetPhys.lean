/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.BW1TermKernel
import InteractingSLE.Spec.Supplement.BW1TermZero
import InteractingSLE.Spec.Supplement.GW1DetBoundaryWalk

/-!
# BW1 at a walk launch: the relation in physical coordinates (`TerminalPhysStatement`)

Packet PROVE-BW1-DET. `BW1Term.TerminalPhysStatement` translates BW1's relation, written in the coordinate of the
launch chart `c = stChart (run 2n)`, into physical coordinates. Ingredients, all landed:

* the post-piece chart is `d = c.trans (termChart D)` (`BW1Term.stChart_run_succ_eq_trans`);
* the launch chart has a proper boundary extension `f` that is injective off the old union `A`
  (`GW1Z.chartFiber_run`, the fibre invariant of a regular run); the chart of the piece has one too
  (`GW1P.HasProperBdryExt.loewner_stopped`);
* boundary extensions compose, so physical tips through `d` are `f` of the tips through `termChart D`
  (`tipAt_trans_trans_iff`);
* the new union is the old union and `f` of the piece trace (`prefixPhysSet_succ_of_launch`,
  `CounterflowRange.tipSet_stopped_eq_of_tendsto`); a physical tip of the launch counterflow off the old union lies
  in the new union iff its launch-coordinate tip lies on the piece, by injectivity of `f` off `A`
  (`firstTipTime_launch_eq`).

## Main results

* `tipAt_trans_trans_iff`, `prefixPhysSet_succ_of_launch`, `firstTipTime_launch_eq`;
* **`terminalPhysStatement`**: `BW1Term.TerminalPhysStatement` holds.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.BW1Det

open Exist Exist.Staged Exist.StagedLaw GW1W GW1WalkFinish BW1Term PiecewiseConstantBoundaryData

/-! ### Composition of boundary extensions -/

/-- **Physical tips through a composed chart.** If `d` and `e` have proper boundary extensions `f` and `g` and `e⁻¹`
maps `ℍ` into `ℍ`, then for a driver with a complete generating trace the tips through `(d.trans e).trans ∞` are
the images under `f` of the tips through `e.trans ∞`. -/
theorem tipAt_trans_trans_iff {d e : Chart} {f g : ℂ → ℂ} {C C' : ℝ}
    (hf : ∀ p ∈ Hbar, Tendsto d.2.1 (𝓝[H] p) (𝓝 (f p))) (hC : ∀ p ∈ Hbar, ‖f p - p‖ ≤ C)
    (hg : ∀ p ∈ Hbar, Tendsto e.2.1 (𝓝[H] p) (𝓝 (g p))) (hC' : ∀ p ∈ Hbar, ‖g p - p‖ ≤ C')
    (heH : ∀ w ∈ H, e.2.1 w ∈ H) {W : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} (hγ : IsGeneratingTrace W ⊤ γ)
    (hW : Continuous W) (hW0 : W 0 = 0) {r : ℝ≥0} {z : ℂ} :
    ((d.trans e).trans infinitySourceChart).tipAt W r z ↔
      ∃ q : ℂ, (e.trans infinitySourceChart).tipAt W r q ∧ z = f q := by
  have hgH : ∀ p ∈ Hbar, g p ∈ Hbar := fun p hp => GW1P.mem_Hbar_of_tendsto hp heH (hg p hp)
  have hfg : ∀ p ∈ Hbar, Tendsto (d.trans e).2.1 (𝓝[H] p) (𝓝 (f (g p))) := by
    intro p hp
    have h1 : Tendsto e.2.1 (𝓝[H] p) (𝓝[H] (g p)) :=
      tendsto_nhdsWithin_iff.2 ⟨hg p hp, eventually_mem_nhdsWithin.mono heH⟩
    exact (hf (g p) (hgH p hp)).comp h1
  have hCfg : ∀ p ∈ Hbar, ‖f (g p) - p‖ ≤ C + C' := by
    intro p hp
    calc ‖f (g p) - p‖ = ‖(f (g p) - g p) + (g p - p)‖ := by ring_nf
      _ ≤ ‖f (g p) - g p‖ + ‖g p - p‖ := norm_add_le _ _
      _ ≤ C + C' := add_le_add (hC _ (hgH p hp)) (hC' p hp)
  rw [GW1Det.tipAt_trans_iff_exists hfg hCfg hγ hW hW0]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨g p, (GW1Det.tipAt_trans_iff_exists hg hC' hγ hW hW0).2 ⟨p, hp, rfl⟩, rfl⟩
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨p, hp, rfl⟩ := (GW1Det.tipAt_trans_iff_exists hg hC' hγ hW hW0).1 hq
    exact ⟨p, hp, rfl⟩

/-- The inverse of the chart of a regular piece maps `ℍ` into `ℍ`. -/
theorem termChart_inv_mem_H {D : (ℝ≥0 → ℝ) × ℝ≥0∞} (hD : GW1P.PieceRegular D.1 (min ⊤ D.2)) {w : ℂ}
    (hw : w ∈ H) : (termChart D).2.1 w ∈ H := by
  obtain ⟨hc, h0⟩ := hD.continuous_stoppedReal
  have h := QuantumZipper.RS.fwdMapInv_mem_H hc h0 (NNReal.coe_nonneg ((min ⊤ D.2).toNNReal)) hw
  change QuantumZipper.fwdMapInv _ _ w + ((0 : ℝ) : ℂ) ∈ H
  rw [Complex.ofReal_zero, add_zero]
  exact h

/-- The chart of a regular piece with finite lifetime has a proper boundary extension. -/
theorem hasProperBdryExt_termChart {D : (ℝ≥0 → ℝ) × ℝ≥0∞} (hD : GW1P.PieceRegular D.1 (min ⊤ D.2))
    (hfin : D.2 ≠ ⊤) : GW1P.HasProperBdryExt (termChart D) :=
  (GW1P.hasProperBdryExt_recenter_id 0).loewner_stopped hD (GW1W.min_top_ne_top hfin)

/-! ### The new union after a launch -/

section Run

variable {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {right : Bool} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- **A walk launch appends the piece to the physical union**, read through the launch chart. -/
theorem prefixPhysSet_succ_of_launch {k : ℕ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (k + 1)).2.2.2.1 k ≠ none) :
    SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ right) D (k + 1) =
      SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ right) D k ∪
        (stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D k)).tipSet
          (retOf ⊤ (D k)).1 (retOf ⊤ (D k)).2.1 := by
  have e1 := pieces_launch (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D k) k (D k) θ ⊤
  have e2 := arcs_launch (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D k) k (D k) θ ⊤
  simp only [SB.prefixPhysSet, GW1W.launch_walk hl, e1, e2]
  ext z
  simp only [mem_union, mem_iUnion, exists_prop, List.mem_append, List.mem_singleton]
  constructor
  · rintro ((h | ⟨p, hp | rfl, hz⟩) | h)
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inl (Or.inl (Or.inr ⟨p, hp, hz⟩))
    · exact Or.inr hz
    · exact Or.inl (Or.inr h)
  · rintro (((h | ⟨p, hp, hz⟩) | h) | h)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr ⟨p, Or.inl hp, hz⟩)
    · exact Or.inr h
    · exact Or.inl (Or.inr ⟨_, Or.inr rfl, h⟩)

end Run

/-! ### The first visit of the new union -/

/-- **The first physical visit of the new union is the first launch-coordinate visit of the root and the piece.**
Let the launch chart `c` have a proper boundary extension `f` injective off the old union `A`, let `D` be a regular
piece, and let the regular driver `V` never have a physical tip (through `c` and the inversion) in `A`. Then the first
time the physical tip of `V` lies in `A ∪ c(piece)` is the first time its launch-coordinate tip lies in `termSet D`. -/
theorem firstTipTime_launch_eq {c : Chart} {f : ℂ → ℂ} {C : ℝ} {A : Set ℂ}
    (hf : ∀ p ∈ Hbar, Tendsto c.2.1 (𝓝[H] p) (𝓝 (f p))) (hC : ∀ p ∈ Hbar, ‖f p - p‖ ≤ C)
    (hinj : ∀ x ∈ Hbar, ∀ y ∈ Hbar, f x = f y → f x ∉ A → x = y)
    {D : (ℝ≥0 → ℝ) × ℝ≥0∞} (hD : GW1P.PieceRegular D.1 (min ⊤ D.2))
    {V : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} (hγ : IsGeneratingTrace V ⊤ γ) (hV : Continuous V) (hV0 : V 0 = 0)
    (havoid : ∀ r z, (c.trans infinitySourceChart).tipAt V r z → z ∉ A) :
    firstTipTime infinitySourceChart V (termSet D) =
      firstTipTime (c.trans infinitySourceChart) V (A ∪ c.tipSet (retOf ⊤ D).1 (retOf ⊤ D).2.1) := by
  obtain ⟨hW0, hWc, α, hα, -⟩ := hD
  have hαH : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ min ⊤ D.2 → α t ∈ Hbar := fun t ht =>
    Sec7.IsGeneratingTrace.mem_Hbar hα (hWc.mono fun x (hs : (x : ℝ≥0∞) < min ⊤ D.2) =>
      (le_of_lt hs : (x : ℝ≥0∞) ≤ min ⊤ D.2)) hW0 ht
  have hpiece : c.tipSet (retOf ⊤ D).1 (retOf ⊤ D).2.1 = f '' (α '' {t | (t : ℝ≥0∞) ≤ min ⊤ D.2}) :=
    CounterflowRange.tipSet_stopped_eq_of_tendsto hα hWc hW0 fun t ht => hf _ (hαH t ht)
  have hterm : (Chart.id.recenter 0).tipSet (retOf ⊤ D).1 (retOf ⊤ D).2.1 =
      (fun z : ℂ => z + ((0 : ℝ) : ℂ)) '' (α '' {t | (t : ℝ≥0∞) ≤ min ⊤ D.2}) := by
    refine CounterflowRange.tipSet_stopped_eq_of_tendsto hα hWc hW0 fun t _ => ?_
    rw [CounterflowRange.recenter_id_inv]
    exact ((continuous_id.add continuous_const).tendsto _).mono_left nhdsWithin_le_nhds
  unfold firstTipTime
  refine iInf_congr fun t => iInf_congr_Prop ?_ fun _ => rfl
  constructor
  · rintro ⟨z, hz, htip⟩
    rcases hz with hz0 | hz
    · rw [mem_singleton_iff] at hz0
      obtain ⟨hne, he⟩ := (GW4Leaf.tipAt_infinitySourceChart_iff hγ hV hV0 t z).1 htip
      rw [hz0] at he
      exact absurd (inv_eq_zero.1 (neg_eq_zero.1 he.symm)) hne
    · rw [hterm] at hz
      obtain ⟨_, ⟨s, hs, rfl⟩, rfl⟩ := hz
      refine ⟨f (α s + ((0 : ℝ) : ℂ)), Or.inr ?_, (GW1Det.tipAt_trans_iff_exists hf hC hγ hV hV0).2
        ⟨_, htip, rfl⟩⟩
      rw [hpiece]
      exact ⟨α s, ⟨s, hs, rfl⟩, by rw [Complex.ofReal_zero, add_zero]⟩
  · rintro ⟨z, hzB, htip⟩
    have hA := havoid t z htip
    obtain ⟨p, hp, rfl⟩ := (GW1Det.tipAt_trans_iff_exists hf hC hγ hV hV0).1 htip
    rcases hzB with hzA | hzP
    · exact absurd hzA hA
    rw [hpiece] at hzP
    obtain ⟨_, ⟨s, hs, rfl⟩, he⟩ := hzP
    obtain ⟨hne, rfl⟩ := (GW4Leaf.tipAt_infinitySourceChart_iff hγ hV hV0 t p).1 hp
    have hpH : -(γ t)⁻¹ ∈ Hbar :=
      GW4Traverse.negInv_mem_Hbar (Sec7.IsGeneratingTrace.mem_Hbar hγ hV.continuousOn hV0 le_top)
    have hsp := hinj (α s) (hαH s hs) _ hpH he (he ▸ hA)
    refine ⟨-(γ t)⁻¹, Or.inr ?_, hp⟩
    rw [hterm]
    exact ⟨α s, ⟨s, hs, rfl⟩, by simp only [Complex.ofReal_zero, add_zero, hsp]⟩

/-! ### The statement -/

/-- **`TerminalPhysStatement` holds** (supplement p. 615; Astra follow-up 5 §4.3): BW1's relation in the launch
coordinate is the retained clock in physical coordinates. -/
theorem terminalPhysStatement : TerminalPhysStatement := by
  intro κ hκ _ b jumps hb right D hreg hS hP n hk V Q hV hQ havoid ℓ hℓc hℓm hrange hrel
  have hlen := (GW1W.even_of_launches_walk hk).2
  rw [boundaryWalk_length] at hlen
  have hn : n < (jumpSet b jumps).card := by omega
  have hl := GW1LaunchClock.previous_launch_of_next hκ hb D hreg hS hP hn hk
  have hfin := ne_top_of_next hl hk
  have hc1 := stChart_run_succ_eq_trans hl hfin
  have hDp : GW1P.PieceRegular (D (2 * n)).1 (min ⊤ (D (2 * n)).2) := by
    obtain ⟨⟨c, θ'⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hl
    have := hP _ _ _ hcθ
    rwa [GW1W.instrTime_walk hl] at this
  obtain ⟨f₀, C₀, hf₀, hC₀, hinj⟩ :=
    GW1Z.chartFiber_run (κ := κ) (b := b) (jumps := jumps) (GW1Z.walkSpec b jumps right) D hP (2 * n)
  obtain ⟨g, C', hg, hC'⟩ := hasProperBdryExt_termChart hDp hfin
  obtain ⟨hVc, hV0, γ, hγ, -⟩ := hV
  obtain ⟨hQc, hQ0, γQ, hγQ, -⟩ := hQ
  refine ⟨hℓc, hℓm, ?_, fun r z => ?_⟩
  · rw [hrange, firstTipTime_launch_eq hf₀ hC₀ hinj hDp hγ hVc hV0 havoid, prefixPhysSet_succ_of_launch hl]
  · rw [hc1, tipAt_trans_trans_iff hf₀ hC₀ hg hC' (fun w hw => termChart_inv_mem_H hDp hw) hγQ hQc hQ0,
      GW1Det.tipAt_trans_iff_exists hf₀ hC₀ hγ hVc hV0]
    simp only [hrel r]

end InteractingSLE.Theorem14.BW1Det
