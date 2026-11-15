/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkSideAssembly

/-!
# Theorem 1.4's walk leaves: the chart domain avoids the explored pieces

Packet PROVE-T14-WALKSIDE. Proves the deterministic `PrefixChartDomStatement` (used by `ae_prefix_limit`): along a run
with regular launched pieces, the domain of the current chart is disjoint from every recorded piece, unless the run is
*done* (a piece run through an infinite lifetime does not change the chart). A recentring keeps the domain; a Loewner
step shrinks it (`dom_loewner_subset`); and the new piece avoids the new domain (`disjoint_dom_loewner_tipSet`): its
points are the boundary values `f(α_t)` of the launch chart along its trace `α`; an interior trace point lies in the
hull at the stop (filling, and continuity at the stop), which the new inverse map avoids; a real trace point has a
boundary value off the old domain (the forward map is continuous there).

* `dom_recenter`, `dom_loewner_subset`, `status_launch_of_top`;
* `mem_fwdHull_of_pieceRegular`, **`disjoint_dom_loewner_tipSet`**;
* **`disjoint_dom_or_done`** (induction along the run), **`prefixChartDomStatement`**;
* **`walkPrefixSideStatement_of_prefix`**: `WalkPrefixSideStatement` from the two prefix inputs.

Deterministic. R48: serves Theorem 1.4 only.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull fwdMapInv)

universe u

namespace InteractingSLE.Theorem14.WalkSide

open Exist.StagedLaw Exist.Staged

section Dom

/-- A recentring keeps the chart domain. -/
theorem dom_recenter (c : Chart) (a : ℝ) : (c.recenter a).dom = c.dom := by
  have himg : (fun z : ℂ => z + a) '' H = H := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      change 0 < (w + a).im
      rw [Complex.add_im, Complex.ofReal_im, add_zero]
      exact hw
    · intro hz
      refine ⟨z - a, ?_, by ring⟩
      change 0 < (z - a).im
      rw [Complex.sub_im, Complex.ofReal_im, sub_zero]
      exact hz
  have e : (c.recenter a).2.1 '' H = c.2.1 '' H := by
    change (fun z => c.2.1 (z + a)) '' H = c.2.1 '' H
    calc (fun z => c.2.1 (z + a)) '' H = c.2.1 '' ((fun z : ℂ => z + a) '' H) := (Set.image_image _ _ _).symm
      _ = c.2.1 '' H := by rw [himg]
  ext z
  change z ∈ interior ((c.recenter a).2.1 '' H) ↔ z ∈ interior (c.2.1 '' H)
  rw [e]

/-- A Loewner step shrinks the chart domain. -/
theorem dom_loewner_subset {c : Chart} (hc : c.IsConformal) {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    {T : ℝ} (hT : 0 ≤ T) : ((c.loewner W T).dom : Set ℂ) ⊆ c.dom := by
  rw [(hc.loewner hW hW0 hT).coe_dom, hc.coe_dom]
  rintro _ ⟨w, hw, rfl⟩
  exact ⟨fwdMapInv W T w, QuantumZipper.RS.fwdMapInv_mem_H hW hW0 hT hw, rfl⟩

/-- A launch with an infinite stop ends the run (status *done*). -/
theorem status_launch_of_top (s : ExplState) (k : ℕ) (D : (ℝ≥0 → ℝ) × ℝ≥0∞) (θ : ℝ) (t : ℝ≥0∞)
    (h : min t D.2 = ⊤) : stStatus (ExplState.launch s k D θ t) = stDone := by
  obtain ⟨pieces, arcs, retained, launches, chart, status, pt, angle, recR, recL⟩ := s
  unfold ExplState.launch
  dsimp only
  simp only [h, ↓reduceIte]

end Dom

/-! ### The new piece avoids the new domain -/

section Piece

variable {V : ℝ≥0 → ℝ} {S : ℝ≥0∞}

/-- **An interior point of a regular piece's trace lies in the hull at the stop** (of the stopped driver). -/
theorem mem_fwdHull_of_pieceRegular (hS : S ≠ ⊤) (hr : GW1P.PieceRegular V S) {α : ℝ≥0 → ℂ}
    (hα : IsGeneratingTrace V S α) {t : ℝ≥0} (ht : (t : ℝ≥0∞) ≤ S) (hH : α t ∈ H) :
    α t ∈ fwdHull (fun x : ℝ => V (min ((x.toNNReal : ℝ≥0) : ℝ≥0∞) S).toNNReal) (S.toNNReal : ℝ) := by
  obtain ⟨hU, hU0⟩ := hr.continuous_stoppedReal
  obtain ⟨hV0, hVc, -, -, -⟩ := hr
  set W : ℝ → ℝ := fun x => V (min ((x.toNNReal : ℝ≥0) : ℝ≥0∞) S).toNNReal with hWdef
  have hSS : ((S.toNNReal : ℝ≥0) : ℝ≥0∞) = S := ENNReal.coe_toNNReal hS
  -- before the stop: filling, then the two drivers agree
  have hbefore : ∀ s : ℝ≥0, (s : ℝ≥0∞) < S → α s ∈ H → α s ∈ fwdHull W (S.toNNReal : ℝ) := by
    intro s hs hsH
    have hs' : s < S.toNNReal := by rw [← ENNReal.coe_lt_coe, hSS]; exact hs
    have hfill : α s ∈ fwdHull (fun x : ℝ => V x.toNNReal) (s : ℝ) := by
      by_contra hK
      obtain ⟨⟨z, -, hcc⟩, -⟩ := hα.2.2 s hs
      have hmem : α s ∈ H \ fwdHull (fun x : ℝ => V x.toNNReal) (s : ℝ) := ⟨hsH, hK⟩
      rw [← hcc] at hmem
      exact (connectedComponentIn_subset _ _ hmem).2 ⟨s, ⟨zero_le, le_rfl⟩, rfl⟩
    set t' : ℝ := ((s : ℝ) + (S.toNNReal : ℝ)) / 2 with ht'
    have hst' : (s : ℝ) < t' := by
      have : (s : ℝ) < (S.toNNReal : ℝ) := by exact_mod_cast hs'
      linarith
    have ht'S : t' ≤ (S.toNNReal : ℝ) := by
      have : (s : ℝ) < (S.toNNReal : ℝ) := by exact_mod_cast hs'
      linarith
    have hc1 : ContinuousOn (fun x : ℝ => V x.toNNReal) (Icc 0 t') := by
      refine hVc.comp continuous_real_toNNReal.continuousOn fun x hx => ?_
      change ((x.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ S
      rw [← hSS, ENNReal.coe_le_coe]
      exact (Real.toNNReal_le_toNNReal hx.2).trans (by rw [Real.toNNReal_le_iff_le_coe]; exact ht'S)
    have hEq : EqOn (fun x : ℝ => V x.toNNReal) W (Icc 0 (s : ℝ)) := by
      intro x hx
      have hxs : ((x.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ S := by
        refine le_trans (ENNReal.coe_le_coe.2 ?_) hs.le
        rw [Real.toNNReal_le_iff_le_coe]; exact hx.2
      simp only [hWdef, min_eq_left hxs, ENNReal.toNNReal_coe]
    rw [LocalExt.fwdHull_congr_of_continuousOn hc1 hU.continuousOn s.coe_nonneg hst' hEq] at hfill
    exact (QuantumZipper.fwdHull_mono (W := W)).1 (by exact_mod_cast hs'.le) hfill
  rcases ht.lt_or_eq with hlt | heq
  · exact hbefore t hlt hH
  -- at the stop: by continuity of the trace and openness of the complement of the hull
  by_contra hK
  have hU' : IsOpen (H \ fwdHull W (S.toNNReal : ℝ)) :=
    QuantumZipper.FwdHolo.isOpen_compl_fwdHull hU (NNReal.coe_nonneg _)
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [hα.1] at hH
    exact (lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from hH))
  have hcont : ContinuousWithinAt α {s : ℝ≥0 | (s : ℝ≥0∞) ≤ S} t := hα.2.1 t ht
  have hev : ∀ᶠ s in 𝓝[{s : ℝ≥0 | (s : ℝ≥0∞) ≤ S}] t, α s ∈ H \ fwdHull W (S.toNNReal : ℝ) :=
    hcont (hU'.mem_nhds ⟨hH, hK⟩)
  have hle : 𝓝[<] t ≤ 𝓝[{s : ℝ≥0 | (s : ℝ≥0∞) ≤ S}] t :=
    nhdsWithin_mono _ fun s hs => by
      rw [← heq]; exact ENNReal.coe_le_coe.2 (le_of_lt hs)
  have : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, pos_iff_ne_zero.2 ht0⟩
  obtain ⟨s, hs1, hs2⟩ := ((hev.filter_mono hle).and self_mem_nhdsWithin).exists
  have hsS : (s : ℝ≥0∞) < S := by rw [← heq]; exact ENNReal.coe_lt_coe.2 hs2
  exact hs1.2 (hbefore s hsS hs1.1)

/-- **The new piece avoids the domain of the chart after it** (finite stop, regular piece, conformal launch chart
with boundary values on `ℍ̄`). -/
theorem disjoint_dom_loewner_tipSet {c : Chart} (hc : c.IsConformal) {f : ℂ → ℂ}
    (hf : ∀ p ∈ Hbar, Tendsto c.2.1 (𝓝[H] p) (𝓝 (f p))) (hS : S ≠ ⊤) (hr : GW1P.PieceRegular V S) :
    Disjoint ((c.loewner (fun x : ℝ => V (min ((x.toNNReal : ℝ≥0) : ℝ≥0∞) S).toNNReal)
        (S.toNNReal : ℝ)).dom : Set ℂ)
      (c.tipSet (fun r : ℝ≥0 => V (min (r : ℝ≥0∞) S).toNNReal) S) := by
  obtain ⟨hU, hU0⟩ := hr.continuous_stoppedReal
  have hr' := hr
  obtain ⟨hV0, hVc, α, hα, -⟩ := hr'
  set W : ℝ → ℝ := fun x => V (min ((x.toNNReal : ℝ≥0) : ℝ≥0∞) S).toNNReal with hWdef
  have hT : (0 : ℝ) ≤ (S.toNNReal : ℝ) := NNReal.coe_nonneg _
  have hαH : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ S → α t ∈ Hbar := fun t ht =>
    Sec7.IsGeneratingTrace.mem_Hbar hα (hVc.mono fun _ (hs : _ < S) => (le_of_lt hs : _ ≤ S)) hV0 ht
  rw [CounterflowRange.tipSet_stopped_eq_of_tendsto hα hVc hV0 fun t ht => hf _ (hαH t ht)]
  rw [Set.disjoint_left]
  rintro z hzD ⟨_, ⟨t, ht, rfl⟩, rfl⟩
  have hcl := hc.loewner hU hU0 hT
  rw [hcl.coe_dom] at hzD
  obtain ⟨w, hw, hwz⟩ := hzD
  change c.2.1 (fwdMapInv W (S.toNNReal : ℝ) w) = f (α t) at hwz
  have hξ := QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hU hU0 hT hw
  set ξ := fwdMapInv W (S.toNNReal : ℝ) w with hξdef
  have := GW1P.neBot_nhdsWithin_H (hαH t ht)
  by_cases hαt : α t ∈ H
  · have hcont : ContinuousAt c.2.1 (α t) := (hc.1.differentiableAt (QuantumZipper.isOpen_H.mem_nhds hαt)).continuousAt
    have h1 : f (α t) = c.2.1 (α t) :=
      tendsto_nhds_unique (hf _ (hαH t ht)) (hcont.tendsto.mono_left nhdsWithin_le_nhds)
    have h2 : α t = ξ := hc.injOn hαt hξ.1 (by rw [← h1, ← hwz])
    exact hξ.2 (h2 ▸ mem_fwdHull_of_pieceRegular hS hr hα ht hαt)
  · -- a real trace point: its boundary value would be in the old domain
    have hdomc : c.2.1 ξ ∈ (c.dom : Set ℂ) := by rw [hc.coe_dom]; exact mem_image_of_mem _ hξ.1
    have hfc : ContinuousAt c.1 (c.2.1 ξ) := (hc.differentiableOn_fwd.differentiableAt
      (c.dom.isOpen.mem_nhds hdomc)).continuousAt
    have h1 : Tendsto (fun u => c.1 (c.2.1 u)) (𝓝[H] (α t)) (𝓝 ξ) := by
      have hf' : Tendsto c.2.1 (𝓝[H] (α t)) (𝓝 (c.2.1 ξ)) := by rw [hwz]; exact hf _ (hαH t ht)
      have := hfc.tendsto.comp hf'
      rw [hc.2.2 ξ hξ.1] at this
      exact this
    have h2 : Tendsto (fun u => c.1 (c.2.1 u)) (𝓝[H] (α t)) (𝓝 (α t)) := by
      refine (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with u hu
      exact (hc.2.2 u hu).symm
    exact hαt (tendsto_nhds_unique h2 h1 ▸ hξ.1)

end Piece

/-! ### Along the run -/

section Run

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- **Along a regular run, the chart domain is disjoint from the recorded pieces, unless the run is done.** -/
theorem disjoint_dom_or_done (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hreg : ∀ (k : ℕ) (c : Chart) (θ : ℝ), (ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 k = some (c, θ) →
      GW1P.PieceRegular (D k).1 (min (instrTime spec k) (D k).2)) :
    ∀ n : ℕ, stStatus (ExplState.run κ b jumps spec D n) = stDone ∨
      Disjoint ((stChart (ExplState.run κ b jumps spec D n)).dom : Set ℂ)
        (⋃ p ∈ (ExplState.run κ b jumps spec D n).1, p.1.tipSet p.2.1 p.2.2)
  | 0 => Or.inr (by
      have h0 : (ExplState.run κ b jumps spec D 0).1 = [] := rfl
      rw [h0]
      simp)
  | n + 1 => by
    by_cases hd : stStatus (ExplState.run κ b jumps spec D n) = stDone
    · left
      rw [GW1WalkFinish.done_run_succ spec D hd]
      exact hd
    have ih := (disjoint_dom_or_done spec D hreg n).resolve_left hd
    rcases hl : (ExplState.run κ b jumps spec D (n + 1)).2.2.2.1 n with _ | ⟨c, θ⟩
    · right
      obtain ⟨a, ha⟩ := chart_run_succ_of_noLaunch (κ := κ) (b := b) (jumps := jumps) spec D hl
      change Disjoint (((ExplState.run κ b jumps spec D (n + 1)).2.2.2.2.1).dom : Set ℂ) _
      rw [ha, dom_recenter, GW1P.pieces_run_succ_of_noLaunch spec D hl]
      exact ih
    · obtain ⟨-, he, -⟩ := eq_launch_of_launches (κ := κ) (b := b) (jumps := jumps) spec D hl
      set S := min (instrTime spec n) (D n).2 with hSdef
      rcases eq_or_ne S ⊤ with htop | htop
      · left
        rw [he]
        exact status_launch_of_top _ _ _ _ _ htop
      · right
        have hr := hreg n c θ hl
        obtain ⟨hU, hU0⟩ := hr.continuous_stoppedReal
        obtain ⟨hconf, f, hf, -⟩ := GW1RestartFinal.chart_boundaryRange_run spec D hreg n
        change Disjoint (((ExplState.run κ b jumps spec D (n + 1)).2.2.2.2.1).dom : Set ℂ) _
        rw [he, chart_launch _ _ _ _ _ htop, CounterflowRange.pieces_launch]
        have hsplit : (⋃ p ∈ (ExplState.run κ b jumps spec D n).1 ++
              [((ExplState.run κ b jumps spec D n).2.2.2.2.1,
                fun r : ℝ≥0 => (D n).1 (min (r : ℝ≥0∞) S).toNNReal, S)], p.1.tipSet p.2.1 p.2.2) =
            (⋃ p ∈ (ExplState.run κ b jumps spec D n).1, p.1.tipSet p.2.1 p.2.2) ∪
              (ExplState.run κ b jumps spec D n).2.2.2.2.1.tipSet
                (fun r : ℝ≥0 => (D n).1 (min (r : ℝ≥0∞) S).toNNReal) S := by
          ext z
          simp only [mem_union, mem_iUnion, exists_prop, List.mem_append, List.mem_singleton]
          constructor
          · rintro ⟨p, hp | rfl, hz⟩
            · exact Or.inl ⟨p, hp, hz⟩
            · exact Or.inr hz
          · rintro (⟨p, hp, hz⟩ | hz)
            · exact ⟨p, Or.inl hp, hz⟩
            · exact ⟨_, Or.inr rfl, hz⟩
        rw [hsplit]
        refine Disjoint.union_right ?_ (disjoint_dom_loewner_tipSet hconf hf htop hr)
        exact ih.mono_left (dom_loewner_subset hconf hU hU0 (NNReal.coe_nonneg _))

/-- **`PrefixChartDomStatement` holds.** -/
theorem prefixChartDomStatement : PrefixChartDomStatement := by
  intro κ b jumps w D ℓ θ τ hℓ hwℓ hl hτ hreg
  have hreg' := pieceRegular_capSpec D hℓ.le hwℓ hreg τ
  have hl' : (ExplState.run κ b jumps (capSpec w ℓ θ τ) D (ℓ + 1)).2.2.2.1 ℓ ≠ none := by
    rw [launches_run_capSpec_succ hℓ.le hwℓ]
    exact hl
  obtain ⟨⟨c, θ'⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hl'
  obtain ⟨-, he, -⟩ := eq_launch_of_launches (capSpec w ℓ θ τ) D hcθ
  have hst : stStatus (ExplState.run κ b jumps (capSpec w ℓ θ τ) D (ℓ + 1)) ≠ stDone := by
    rw [he, instrTime_capSpec hℓ.le,
      (GW2Schedule.status_launch _ ℓ (D ℓ) θ' (ENNReal.coe_ne_top : ((τ : ℝ≥0) : ℝ≥0∞) ≠ ⊤)).1 hτ]
    decide
  exact (disjoint_dom_or_done (capSpec w ℓ θ τ) D hreg' (ℓ + 1)).resolve_left hst

end Run

/-! ### The reduction -/

/-- **`WalkBdry.WalkPrefixSideStatement θ right` from the two prefix inputs** (the capped prefix's marked locality and
a measurable version of the prefix chart), for an angle in `[−π/2, π/2]`; the chart-domain statement is proved
(`prefixChartDomStatement`). Theorems 1.2–1.3 enter through the walk's marked locality; R48: Theorem 1.4 only. -/
theorem walkPrefixSideStatement_of_prefix (h12p : Exist.Staged.Theorem12ParamStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) {θ : ℝ} (hθ : θ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) {right : Bool}
    (hA : PrefixMarkedLocalStatement.{u} θ right) (hB : PrefixChartVersionStatement.{u} θ right) :
    WalkBdry.WalkPrefixSideStatement.{u} θ right :=
  walkPrefixSideStatement_of_inputs h12p h13 hθ hA hB prefixChartDomStatement

end InteractingSLE.Theorem14.WalkSide
