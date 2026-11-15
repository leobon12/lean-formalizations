/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBLxEntry
import InteractingSLE.Spec.Supplement.SBLwShift
import InteractingSLE.Spec.Supplement.GW1PieceRun
import InteractingSLE.Spec.Supplement.SB2FinCollar

/-!
# SB2(1)'s entry value exists: the launch chart's left boundary values converge at `L⁻`

Packet PROVE-T14-SB2FIN3, after ruling R91. SB2(1)'s target is the entry form `Lx.SB2UpperLaunchEntryStatement`: the
relative upper flow starts at the entry `m = e_L = g_A(L⁻)` of the launch chart (`Lx.IsLeftEntryValue c L m`). This
file proves that the entry value **exists** for every regular, unfinished run chart and pins it down:

* `bdryValue c x` (the real boundary value of `c` at `x`) and `leftEntry c L` (its limit at `L⁻`);
  `IsLeftEntryValue.eq_leftEntry`: an entry value is `leftEntry c L`, so it is a function of the chart;
* **`exists_isLeftEntryValue_of_hullModel`**: a conformal chart with a hull model (`WalkIntCanon.HullModel`) and a
  boundary map of its inverse has an entry value at every `L` left of which the real line is free of the hull: the
  boundary values on `(−∞, L)` are continuous (local Schwarz reflection, `IsMapOut.exists_reflection`), injective (the
  boundary map inverts them), within bounded distance of the identity (`IsMapOut.exists_norm_sub_le`), hence strictly
  increasing (`ContinuousOn.strictMonoOn_of_injOn_Icc`) and bounded above, so they converge
  (`MonotoneOn.tendsto_nhdsLT`);
* **`isLeftEntryValue_runChart`**: the run chart (regular, unfinished) at any `L` at most every real point of a compact
  `A` with the prefix's fill — `L` may be a point of the walk (no ball premise);
* `stStatus_ne_done_of_launches`: a launching state is unfinished;
* `isCompact_tipSet`, `finite_stops_compact_arcs_run`, `isCompact_tipSet_pieces_run`, **`isCompact_prefixPhysSet_run`**,
  **`isCompact_lowerPrefix`**: before the walk is finished, every recorded piece has a finite stop (a launch with an
  infinite stop, or a move to the end of `ℝ`, finishes the walk) and a compact tip set, every arc is a compact
  interval, so the prefix is compact — in particular `lowerPrefix` at every launch;
* **`isLeftEntryValue_launchChart`**: at a launching sample whose pieces are regular,
  `IsLeftEntryValue (launchChart …) (realMin (lowerPrefix …)) (leftEntry …)`.

So SB2(1)'s entry point is `m := leftEntry (launchChart …) (realMin …)` (`Lv.launchEntry`), and the entry clause of the
target holds for it at every regular launch; only `m ≤ 0` (the walk's tip is the chart's boundary point `0`, GW1's
`ExteriorRecord` datum) is left to `Lv.SB2RelDriverStatement`. Deterministic; no named input.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Lv

/-- The event that instruction `k` of the lower walk (`boundaryWalkSpec b jumps (−π/2) true`) launches. -/
def launchSet (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type*}
    (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) : Set Ω :=
  {ω₀ | (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
    (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω₀) (k + 1)).2.2.2.1 k ≠ none}

/-- The chart in which instruction `k` of the lower walk launches (the identity chart when it does not launch). -/
def launchChart (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type*}
    (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) (ω₀ : Ω) : Chart :=
  ((ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
    (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω₀) (k + 1)).2.2.2.1 k).elim Chart.id Prod.fst

theorem launchChart_eq {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type*}
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {ω₀ : Ω} {c₀ : Chart} {θ : ℝ}
    (h : (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω₀) (k + 1)).2.2.2.1 k = some (c₀, θ)) :
    launchChart κ b jumps E k ω₀ = c₀ := by
  simp only [launchChart, h, Option.elim]

theorem mem_launchSet {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type*}
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {ω₀ : Ω} {c₀ : Chart} {θ : ℝ}
    (h : (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω₀) (k + 1)).2.2.2.1 k = some (c₀, θ)) :
    ω₀ ∈ launchSet κ b jumps E k := by
  simp only [launchSet, mem_ofPred_eq, h, ne_eq, reduceCtorEq, not_false_eq_true]

end InteractingSLE.Theorem14.SB.Lv

namespace InteractingSLE.Theorem14.SB.Lx

/-- The real boundary value of a chart at a real point: the real part of the limit of the forward map from `ℍ`. -/
def bdryValue (c : Chart) (x : ℝ) : ℝ := (limUnder (𝓝[H] (x : ℂ)) c.1).re

/-- The entry value of a chart at `L`: the limit from the left of its real boundary values. -/
def leftEntry (c : Chart) (L : ℝ) : ℝ := limUnder (𝓝[<] L) (bdryValue c)

theorem tendsto_bdryValue {c : Chart} {x : ℝ} {w : ℂ} (h : Tendsto c.1 (𝓝[H] (x : ℂ)) (𝓝 w))
    (hw : w.im = 0) : bdryValue c x = w.re ∧ Tendsto c.1 (𝓝[H] (x : ℂ)) (𝓝 (bdryValue c x : ℂ)) := by
  have := GW1P.neBot_nhdsWithin_H (Lw.ofReal_mem_Hbar x)
  have hv : bdryValue c x = w.re := by rw [bdryValue, h.limUnder_eq]
  refine ⟨hv, ?_⟩
  have hw' : ((w.re : ℝ) : ℂ) = w := Complex.ext (by simp) (by simp [hw])
  rw [hv, hw']
  exact h

/-- An entry value is the chart's `leftEntry`. -/
theorem IsLeftEntryValue.eq_leftEntry {c : Chart} {L m : ℝ} (h : IsLeftEntryValue c L m) :
    m = leftEntry c L := by
  obtain ⟨e, he, hlim⟩ := h
  have hc : Tendsto (bdryValue c) (𝓝[<] L) (𝓝 m) := by
    refine hlim.congr' (eventually_nhdsWithin_of_forall fun x hx => ?_)
    have h1 := tendsto_bdryValue (he x hx) (by simp)
    rw [h1.1, Complex.ofReal_re]
  exact hc.limUnder_eq.symm

/-- **A chart with a hull model and a boundary map has an entry value at every `L` left of which the real line is
free**: its real boundary values on `(−∞, L)` are continuous (local reflection), injective (the boundary map inverts
them), within bounded distance of the identity (the mapping-out normalization), hence strictly increasing, and bounded
above; so they converge at `L⁻`. -/
theorem exists_isLeftEntryValue_of_hullModel {c : Chart} (hcc : c.IsConformal) (M : WalkIntCanon.HullModel c)
    {g : ℂ → ℂ} (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g c.2.1 H) {L : ℝ}
    (hfree : ∀ x : ℝ, x < L → ∃ ρ > 0, Disjoint (ball (x : ℂ) ρ) M.hull) :
    ∃ m, IsLeftEntryValue c L m := by
  -- the local reflection at a free real point
  have hloc : ∀ x : ℝ, x < L → ∃ ρ > 0, ∃ G : ℂ → ℂ, ContinuousOn G (ball (x : ℂ) ρ) ∧
      ∀ y : ℝ, (y : ℂ) ∈ ball (x : ℂ) ρ →
        Tendsto c.1 (𝓝[H] (y : ℂ)) (𝓝 (G y - M.shift)) ∧ (G y - M.shift).im = 0 := by
    intro x hx
    obtain ⟨ρ, hρ, hd⟩ := hfree x hx
    obtain ⟨G, hGd, -, -, hGr, -, hGt⟩ := M.mapOut.exists_reflection M.isHull hd
    refine ⟨ρ / 2, half_pos hρ, G, hGd.continuousOn, fun y hy => ⟨?_, ?_⟩⟩
    · have h1 := hGt (y : ℂ) hy (by simp)
      have hn : 𝓝[ball (x : ℂ) (ρ / 2) ∩ H] (y : ℂ) = 𝓝[H] (y : ℂ) :=
        nhdsWithin_inter_of_mem (mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds hy))
      rw [hn] at h1
      simpa using h1.sub_const (M.shift : ℂ)
    · rw [Complex.sub_im, hGr _ hy (by simp)]
      simp
  -- the boundary values
  have he : ∀ x : ℝ, x < L → Tendsto c.1 (𝓝[H] (x : ℂ)) (𝓝 (bdryValue c x : ℂ)) := fun x hx => by
    obtain ⟨ρ, hρ, G, -, hG⟩ := hloc x hx
    exact (tendsto_bdryValue (hG x (mem_ball_self hρ)).1 (hG x (mem_ball_self hρ)).2).2
  -- points near a free real point are in the chart domain
  have hdom : ∀ x : ℝ, x < L → ∀ᶠ z in 𝓝[H] (x : ℂ), z ∈ (c.dom : Set ℂ) := fun x hx => by
    obtain ⟨ρ, hρ, hd⟩ := hfree x hx
    filter_upwards [inter_mem_nhdsWithin H (ball_mem_nhds (x : ℂ) hρ)] with z hz
    rw [M.dom_eq]
    exact ⟨hz.1, fun h => hd.ne_of_mem hz.2 h rfl⟩
  -- continuity
  have hcont : ContinuousOn (bdryValue c) (Iio L) := by
    intro x hx
    obtain ⟨ρ, hρ, G, hGc, hG⟩ := hloc x hx
    have hball : (fun y : ℝ => (y : ℂ)) ⁻¹' ball (x : ℂ) ρ ∈ 𝓝 x :=
      Complex.continuous_ofReal.continuousAt.preimage_mem_nhds (ball_mem_nhds _ hρ)
    have heq : (fun y : ℝ => (G y).re - M.shift) =ᶠ[𝓝 x] bdryValue c := by
      filter_upwards [hball] with y hy
      rw [(tendsto_bdryValue (hG y hy).1 (hG y hy).2).1]
      simp
    have hGx : ContinuousAt G (x : ℂ) := hGc.continuousAt (ball_mem_nhds _ hρ)
    have h1 : ContinuousAt (fun y : ℝ => (G y).re - M.shift) x :=
      ((Complex.continuous_re.continuousAt.comp (hGx.comp Complex.continuous_ofReal.continuousAt)).sub
        continuousAt_const)
    exact (h1.congr heq).continuousWithinAt
  -- the boundary map inverts the boundary values
  have hinv : ∀ x : ℝ, x < L → g (bdryValue c x) = x := fun x hx => by
    have := GW1P.neBot_nhdsWithin_H (Lw.ofReal_mem_Hbar x)
    have h1 : Tendsto c.1 (𝓝[H] (x : ℂ)) (𝓝[H] (bdryValue c x : ℂ)) :=
      tendsto_nhdsWithin_iff.2 ⟨he x hx, (hdom x hx).mono fun z hz => hcc.fwd_mem hz⟩
    have h2 : Tendsto g (𝓝[H] (bdryValue c x : ℂ)) (𝓝 (g (bdryValue c x))) :=
      (hgc _ (Lw.ofReal_mem_Hbar _)).tendsto.mono_left
        (nhdsWithin_mono _ fun z hz => le_of_lt (show (0 : ℝ) < z.im from hz))
    have h3 : Tendsto (fun z => g (c.1 z)) (𝓝[H] (x : ℂ)) (𝓝 (x : ℂ)) := by
      refine (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).congr' ?_
      filter_upwards [hdom x hx] with z hz
      rw [hgi (hcc.fwd_mem hz), hcc.inv_fwd hz]
      rfl
    exact tendsto_nhds_unique (h2.comp h1) h3
  have hinj : InjOn (bdryValue c) (Iio L) := fun x hx y hy hxy => by
    have h1 := hinv x hx
    rw [hxy, hinv y hy] at h1
    exact_mod_cast h1.symm
  -- bounded displacement
  obtain ⟨C, hC⟩ := M.mapOut.exists_norm_sub_le M.isHull
  have hdisp : ∀ x : ℝ, x < L → |bdryValue c x + M.shift - x| ≤ C := fun x hx => by
    have := GW1P.neBot_nhdsWithin_H (Lw.ofReal_mem_Hbar x)
    have h1 : Tendsto (fun z => ‖c.1 z + M.shift - z‖) (𝓝[H] (x : ℂ))
        (𝓝 ‖(bdryValue c x : ℂ) + M.shift - x‖) :=
      (((he x hx).add_const _).sub (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id)).norm
    have h2 : ‖(bdryValue c x : ℂ) + M.shift - x‖ ≤ C := by
      refine le_of_tendsto h1 ?_
      filter_upwards [hdom x hx] with z hz
      rw [M.dom_eq] at hz
      exact hC z hz
    have e : (bdryValue c x : ℂ) + M.shift - x = ((bdryValue c x + M.shift - x : ℝ) : ℂ) := by push_cast; ring
    rw [e, Complex.norm_real, Real.norm_eq_abs] at h2
    exact h2
  have hlo : ∀ x : ℝ, x < L → x - M.shift - C ≤ bdryValue c x := fun x hx => by
    have := (abs_le.1 (hdisp x hx)).1; linarith
  have hhi : ∀ x : ℝ, x < L → bdryValue c x ≤ x - M.shift + C := fun x hx => by
    have := (abs_le.1 (hdisp x hx)).2; linarith
  -- monotone
  have hmono : MonotoneOn (bdryValue c) (Iio L) := by
    intro x hx y hy hxy
    rcases eq_or_lt_of_le hxy with rfl | hlt
    · exact le_rfl
    set a := min x (y - 2 * C - 1) with ha
    have hax : a ≤ x := min_le_left _ _
    have hay : a ≤ y - 2 * C - 1 := min_le_right _ _
    have hsub : Icc a y ⊆ Iio L := fun z hz => lt_of_le_of_lt hz.2 hy
    have haL : a < L := lt_of_le_of_lt hax hx
    have hfa : bdryValue c a ≤ bdryValue c y := by
      have := hhi a haL; have := hlo y hy; linarith
    have hs := ContinuousOn.strictMonoOn_of_injOn_Icc (hax.trans hlt.le) hfa (hcont.mono hsub)
      (hinj.mono hsub)
    exact (hs ⟨hax, hlt.le⟩ ⟨hax.trans hlt.le, le_rfl⟩ hlt).le
  have hbdd : BddAbove (bdryValue c '' Iio L) := by
    refine ⟨L - M.shift + C, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    have := hhi x hx
    have : x < L := hx
    linarith
  exact ⟨_, bdryValue c, he, hmono.tendsto_nhdsLT hbdd⟩

open Exist.StagedLaw in
/-- **The walk's run chart has an entry value at every `L` at most every real point of `A`** (any compact `A` with the
fill of the run's prefix, e.g. `lowerPrefix`): `IsLeftEntryValue (run chart) L (leftEntry (run chart) L)`. This is
the existence half of SB2(1)'s entry clause (ruling R91); `L` may be a point of the walk. -/
theorem isLeftEntryValue_runChart {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} (spec : ExplSpec)
    (D : ℕ → (NNReal → ℝ) × ENNReal)
    (hreg : ∀ k c θ', (ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 k = some (c, θ') →
      GW1P.PieceRegular (D k).1 (min (instrTime spec k) (D k).2)) (n : ℕ)
    (hnot : stStatus (ExplState.run κ b jumps spec D n) ≠ GW1Conn.stDone) {A : Set ℂ}
    (hAc : IsCompact A) (hAf : fillH A = fillH (SB.prefixPhysSet κ b jumps spec D n)) {L : ℝ}
    (hLA : ∀ y : ℝ, (y : ℂ) ∈ A → L ≤ y) :
    IsLeftEntryValue (stChart (ExplState.run κ b jumps spec D n)) L
      (leftEntry (stChart (ExplState.run κ b jumps spec D n)) L) := by
  obtain ⟨M, hK⟩ := Lw.exists_hullModel_fill spec D hreg n hnot
  have hcc := (GW2aCont.isConformal_runChart (κ := κ) (b := b) (jumps := jumps) spec D n
    fun j _ c θ h => hreg j c θ h).1
  obtain ⟨g, hgc, hgi, -, -⟩ := Lw.exists_bdryMap_of_hasProperBdryExt hcc
    (GW1P.isClosed_pieces_run (κ := κ) (b := b) (jumps := jumps) spec D hreg n).1
  obtain ⟨m, hm⟩ := exists_isLeftEntryValue_of_hullModel hcc M hgc hgi (L := L) fun x hx => by
    obtain ⟨ρ, hρ, hd⟩ := Lw.exists_ball_disjoint_fillH hAc fun y hy => lt_of_lt_of_le hx (hLA y hy)
    rw [hAf, ← hK] at hd
    exact ⟨ρ, hρ, hd⟩
  exact hm.eq_leftEntry ▸ hm

open Exist.Staged Exist.StagedLaw in
/-- A state at which an instruction launches is not finished. -/
theorem stStatus_ne_done_of_launches {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} (spec : ExplSpec)
    (D : ℕ → (NNReal → ℝ) × ENNReal) {k : ℕ} {c : Chart} {θ : ℝ}
    (h : (ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 k = some (c, θ)) :
    stStatus (ExplState.run κ b jumps spec D k) ≠ GW1Conn.stDone := by
  intro hst
  have h0 := launches_run_of_le (κ := κ) (b := b) (jumps := jumps) spec D (le_refl k)
  obtain ⟨hk, -, -⟩ := eq_launch_of_launches spec D h
  rw [run_succ, hk] at h
  simp only at h
  change (ExplState.flowStep κ b spec.2.1 (ExplState.run κ b jumps spec D k) k (D k) θ
    (instrTime spec k)).2.2.2.1 k = some (c, θ) at h
  have hfs : ExplState.flowStep κ b spec.2.1 (ExplState.run κ b jumps spec D k) k (D k) θ (instrTime spec k) =
      ExplState.run κ b jumps spec D k := by
    generalize ExplState.run κ b jumps spec D k = s at hst ⊢
    obtain ⟨pieces, arcs, ret, lau, chart, st, pt, ang, rR, rL⟩ := s
    change st = _ at hst
    subst hst
    rfl
  rw [hfs, h0] at h
  exact absurd h (by simp)

open Exist.Staged Exist.StagedLaw

/-- **The tip set of a regular piece stopped at a finite time, read in a good chart, is compact** (it is `f(α([0, S]))`,
as in `GW1P.isClosed_tipSet`). -/
theorem isCompact_tipSet {c : Chart} (hc : GW1P.HasProperBdryExt c) {W : ℝ≥0 → ℝ} {S : ℝ≥0∞}
    (h : GW1P.PieceRegular W S) (hS : S ≠ ⊤) :
    IsCompact (c.tipSet (fun r : ℝ≥0 => W (min (r : ℝ≥0∞) S).toNNReal) S) := by
  obtain ⟨f, C, hf, -⟩ := hc
  obtain ⟨hW0, hWc, α, hα, -⟩ := h
  have hαH : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ S → α t ∈ Hbar := fun t ht =>
    Sec7.IsGeneratingTrace.mem_Hbar hα (hWc.mono fun _ (hs : _ < S) => (le_of_lt hs : _ ≤ S)) hW0 ht
  rw [CounterflowRange.tipSet_stopped_eq_of_tendsto hα hWc hW0 fun t ht => hf _ (hαH t ht)]
  have hfc : ContinuousOn f Hbar := GW1P.continuousOn_of_tendsto hf
  have hset : {t : ℝ≥0 | (t : ℝ≥0∞) ≤ S} = Icc 0 S.toNNReal := by
    ext t
    simp only [mem_ofPred_eq, mem_Icc, zero_le, true_and]
    rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal hS]
  rw [hset]
  have hαc : ContinuousOn α (Icc 0 S.toNNReal) := hα.2.1.mono fun s hs =>
    (ENNReal.coe_le_coe.2 hs.2).trans (ENNReal.coe_toNNReal_le_self)
  refine (isCompact_Icc.image_of_continuousOn hαc).image_of_continuousOn (hfc.mono ?_)
  rintro _ ⟨s, hs, rfl⟩
  exact hαH s ((ENNReal.coe_le_coe.2 hs.2).trans ENNReal.coe_toNNReal_le_self)

/-! ### The walk's prefix is compact before the walk is finished -/

theorem arcs_launch' (s : ExplState) (k : ℕ) (D : (ℝ≥0 → ℝ) × ℝ≥0∞) (θ : ℝ) (t : ℝ≥0∞) :
    (ExplState.launch s k D θ t).2.1 = s.2.1 := by
  obtain ⟨pieces, arcs, retained, launches, chart, status, pt, angle, recR, recL⟩ := s
  unfold ExplState.launch
  dsimp only
  repeat' first
    | rfl
    | split

theorem stStatus_launch_of_top (s : ExplState) (k : ℕ) (D : (ℝ≥0 → ℝ) × ℝ≥0∞) (θ : ℝ) (t : ℝ≥0∞)
    (h : min t D.2 = ⊤) : stStatus (ExplState.launch s k D θ t) = GW1Conn.stDone := by
  obtain ⟨pieces, arcs, retained, launches, chart, status, pt, angle, recR, recL⟩ := s
  unfold ExplState.launch
  dsimp only
  simp only [h, ↓reduceIte]

theorem stStatus_moveToEnd (s : ExplState) (r : Bool) :
    stStatus (ExplState.moveToEnd s r) = GW1Conn.stDone := by
  obtain ⟨pieces, arcs, retained, launches, chart, status, pt, angle, recR, recL⟩ := s
  rfl

theorem pieces_moveAlong' (s : ExplState) (r : Bool) (x : ℝ) (m : Bool) :
    (ExplState.moveAlong s r x m).1 = s.1 := by
  obtain ⟨pieces, arcs, retained, launches, chart, status, pt, angle, recR, recL⟩ := s
  rfl

theorem arcs_moveAlong' (s : ExplState) (r : Bool) (x : ℝ) (m : Bool) :
    ∃ a b : ℝ, (ExplState.moveAlong s r x m).2.1 = s.2.1 ++ [Icc a b] := by
  obtain ⟨pieces, arcs, retained, launches, chart, status, pt, angle, recR, recL⟩ := s
  cases r
  · exact ⟨x, pt, rfl⟩
  · exact ⟨pt, x, rfl⟩

/-- One boundary continuation keeps the finite stops and the compact arcs, unless it finishes the walk. -/
theorem finite_compact_contStep {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} (s : ExplState) (v : Option ℝ)
    (pref : Bool) (hst : stStatus (ExplState.contStep κ b jumps s v pref) ≠ GW1Conn.stDone)
    (hp : ∀ p ∈ s.1, p.2.2 ≠ ⊤) (ha : ∀ a ∈ s.2.1, IsCompact a) :
    (∀ p ∈ (ExplState.contStep κ b jumps s v pref).1, p.2.2 ≠ ⊤) ∧
      ∀ a ∈ (ExplState.contStep κ b jumps s v pref).2.1, IsCompact a := by
  rcases contStep_cases (κ := κ) (b := b) (jumps := jumps) s v pref with e | e | ⟨r, x, m, e⟩ | ⟨r, e⟩ <;>
    rw [e] at hst ⊢
  · exact ⟨hp, ha⟩
  · exact ⟨hp, ha⟩
  · obtain ⟨a₀, b₀, hab⟩ := arcs_moveAlong' s r x m
    rw [pieces_moveAlong', hab]
    refine ⟨hp, fun a h => ?_⟩
    rcases List.mem_append.1 h with h | h
    · exact ha a h
    · rw [List.mem_singleton] at h
      rw [h]
      exact isCompact_Icc
  · exact absurd (stStatus_moveToEnd s r) hst

/-- One flow instruction keeps the finite stops and the compact arcs, unless it finishes the walk. -/
theorem finite_compact_flowStep {κ : ℝ} {b : ℝ → ℝ} (gw2 : Bool) (s : ExplState) (k : ℕ)
    (D : (ℝ≥0 → ℝ) × ℝ≥0∞) (θ : ℝ) (t : ℝ≥0∞)
    (hst : stStatus (ExplState.flowStep κ b gw2 s k D θ t) ≠ GW1Conn.stDone)
    (hp : ∀ p ∈ s.1, p.2.2 ≠ ⊤) (ha : ∀ a ∈ s.2.1, IsCompact a) :
    (∀ p ∈ (ExplState.flowStep κ b gw2 s k D θ t).1, p.2.2 ≠ ⊤) ∧
      ∀ a ∈ (ExplState.flowStep κ b gw2 s k D θ t).2.1, IsCompact a := by
  rcases flowStep_trichotomy (κ := κ) (b := b) gw2 s k D θ t with e | e | e <;> rw [e] at hst ⊢
  · exact ⟨hp, ha⟩
  · exact ⟨hp, ha⟩
  · rw [CounterflowRange.pieces_launch, arcs_launch']
    by_cases htop : min t D.2 = ⊤
    · exact absurd (stStatus_launch_of_top s k D θ t htop) hst
    refine ⟨fun p h => ?_, ha⟩
    rcases List.mem_append.1 h with h | h
    · exact hp p h
    · rw [List.mem_singleton] at h
      rw [h]
      exact htop

/-- **Before the walk is finished, every recorded piece has a finite stop and every recorded arc is compact.** -/
theorem finite_stops_compact_arcs_run {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} (spec : ExplSpec)
    (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) :
    ∀ n, stStatus (ExplState.run κ b jumps spec D n) ≠ GW1Conn.stDone →
      (∀ p ∈ (ExplState.run κ b jumps spec D n).1, p.2.2 ≠ ⊤) ∧
        ∀ a ∈ (ExplState.run κ b jumps spec D n).2.1, IsCompact a
  | 0, _ => by simp [ExplState.run, ExplState.init]
  | n + 1, hst => by
    have hst' : stStatus (ExplState.run κ b jumps spec D n) ≠ GW1Conn.stDone := fun h =>
      hst (by rw [GW1WalkFinish.done_run_succ spec D h]; exact h)
    obtain ⟨ihp, iha⟩ := finite_stops_compact_arcs_run spec D n hst'
    rw [run_succ] at hst ⊢
    cases hk : spec.2.2[n]? with
    | none => exact ⟨ihp, iha⟩
    | some ins =>
      rw [hk] at hst
      simp only at hst ⊢
      rcases ins with ⟨θ, t⟩ | r | ⟨x, r⟩
      · exact finite_compact_flowStep _ _ _ _ _ _ hst ihp iha
      · exact finite_compact_contStep _ _ _ hst ihp iha
      · exact finite_compact_contStep _ _ _ hst ihp iha

/-- **Along a run with regular launched pieces, every recorded piece with a finite stop has a compact tip set** (the
induction of `GW1P.isClosed_pieces_run`, with `isCompact_tipSet`). -/
theorem isCompact_tipSet_pieces_run {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} (spec : ExplSpec)
    (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hreg : ∀ (k : ℕ) (c : Chart) (θ : ℝ), (ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 k = some (c, θ) →
      GW1P.PieceRegular (D k).1 (min (instrTime spec k) (D k).2)) (n : ℕ) :
    GW1P.HasProperBdryExt (ExplState.run κ b jumps spec D n).2.2.2.2.1 ∧
      ∀ p ∈ (ExplState.run κ b jumps spec D n).1, p.2.2 ≠ ⊤ → IsCompact (p.1.tipSet p.2.1 p.2.2) := by
  induction n with
  | zero =>
    refine ⟨GW1P.hasProperBdryExt_recenter_id spec.1, fun p hp => ?_⟩
    simp [ExplState.run, ExplState.init] at hp
  | succ n ih =>
    obtain ⟨hc, hp⟩ := ih
    rcases hl : (ExplState.run κ b jumps spec D (n + 1)).2.2.2.1 n with _ | ⟨c, θ⟩
    · obtain ⟨a, ha⟩ := chart_run_succ_of_noLaunch (κ := κ) (b := b) (jumps := jumps) spec D hl
      rw [ha, GW1P.pieces_run_succ_of_noLaunch spec D hl]
      exact ⟨hc.recenter a, hp⟩
    · have hr := hreg n c θ hl
      obtain ⟨-, he, -⟩ := eq_launch_of_launches (κ := κ) (b := b) (jumps := jumps) spec D hl
      rw [he, CounterflowRange.pieces_launch]
      refine ⟨?_, fun p hp' hpt => ?_⟩
      · rcases eq_or_ne (min (instrTime spec n) (D n).2) ⊤ with htop | htop
        · rw [GW1P.chart_launch_of_top _ _ _ _ _ htop]
          exact hc
        · rw [chart_launch _ _ _ _ _ htop]
          exact hc.loewner_stopped hr htop
      · rcases List.mem_append.1 hp' with hq | hq
        · exact hp p hq hpt
        · rw [List.mem_singleton] at hq
          subst hq
          exact isCompact_tipSet hc hr hpt

/-- **The walk's physical prefix is compact before the walk is finished** (regular launched pieces). -/
theorem isCompact_prefixPhysSet_run {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} (spec : ExplSpec)
    (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hreg : ∀ (k : ℕ) (c : Chart) (θ : ℝ), (ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 k = some (c, θ) →
      GW1P.PieceRegular (D k).1 (min (instrTime spec k) (D k).2)) (n : ℕ)
    (hnot : stStatus (ExplState.run κ b jumps spec D n) ≠ GW1Conn.stDone) :
    IsCompact (SB.prefixPhysSet κ b jumps spec D n) := by
  obtain ⟨hfin, harc⟩ := finite_stops_compact_arcs_run spec D n hnot
  have hcpt := (isCompact_tipSet_pieces_run spec D hreg n).2
  unfold SB.prefixPhysSet
  refine (isCompact_singleton.union ?_).union ?_
  · exact (List.finite_toSet _).isCompact_biUnion fun p hp => hcpt p hp (hfin p hp)
  · exact (List.finite_toSet _).isCompact_biUnion fun a ha =>
      (harc a ha).image Complex.continuous_ofReal

open Lv in
/-- **The retained lower prefix is compact at a launch** of the lower walk (regular launched pieces). -/
theorem isCompact_lowerPrefix {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type*}
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u : ℝ} {ω₀ : Ω}
    (hreg : ∀ j c θ', (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω₀) (j + 1)).2.2.2.1 j = some (c, θ') →
      GW1P.PieceRegular (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω₀).1
        (min (instrTime (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j)
          (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω₀).2))
    (hF : ω₀ ∈ launchSet κ b jumps E k) : IsCompact (lowerPrefix κ b jumps E k u ω₀) := by
  obtain ⟨⟨c, θ⟩, hl⟩ := Option.ne_none_iff_exists'.1 hF
  exact (isCompact_prefixPhysSet_run _ _ hreg k (stStatus_ne_done_of_launches _ _ hl)).union
    (isCompact_Icc.image Complex.continuous_ofReal)

/-- **The entry value at a launch of the lower walk** (SB2(1)'s entry clause, ruling R91): at a sample where
instruction `k` launches and the launched pieces are regular, the launch chart has the entry value `leftEntry` at
`L = realMin (lowerPrefix …)` (the retained prefix is compact: `isCompact_lowerPrefix`). -/
theorem isLeftEntryValue_launchChart {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type*}
    {E : ExplSpec → ℕ → Ω → (NNReal → ℝ) × ENNReal} {k : ℕ} {u : ℝ} {ω₀ : Ω}
    (hreg : ∀ j c θ', (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω₀) (j + 1)).2.2.2.1 j = some (c, θ') →
      GW1P.PieceRegular (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω₀).1
        (min (instrTime (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j)
          (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω₀).2))
    (hF : ω₀ ∈ Lv.launchSet κ b jumps E k) :
    IsLeftEntryValue (Lv.launchChart κ b jumps E k ω₀) (realMin (lowerPrefix κ b jumps E k u ω₀))
      (leftEntry (Lv.launchChart κ b jumps E k ω₀) (realMin (lowerPrefix κ b jumps E k u ω₀))) := by
  have hAc := isCompact_lowerPrefix (u := u) hreg hF
  obtain ⟨⟨c, θ⟩, hl⟩ := Option.ne_none_iff_exists'.1 hF
  rw [Lv.launchChart_eq hl, (eq_launch_of_launches _ _ hl).2.2]
  exact isLeftEntryValue_runChart _ _ hreg k (stStatus_ne_done_of_launches _ _ hl) hAc
    (Lw.fillH_union_real _ _) fun y hy => FinRel.realMin_le_of_mem hAc hy

end InteractingSLE.Theorem14.SB.Lx

namespace InteractingSLE.Theorem14.SB.Lv

/-- **SB2(1)'s entry point** in the launch chart: the entry value `e_L = g_A(L⁻)` of the launch chart at
`L = realMin (lowerPrefix …)` (`Lx.leftEntry`; by `Lx.IsLeftEntryValue.eq_leftEntry` the only possible `m` of the
entry form). -/
def launchEntry (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type*}
    (E : ExplSpec → ℕ → Ω → (NNReal → ℝ) × ENNReal) (k : ℕ) (u : ℝ) (ω : Ω) : ℝ :=
  Lx.leftEntry (launchChart κ b jumps E k ω) (realMin (lowerPrefix κ b jumps E k u ω))

end InteractingSLE.Theorem14.SB.Lv
