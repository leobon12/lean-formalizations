/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2HEntry
import InteractingSLE.Spec.Supplement.GW1WalkFinishTip

/-!
# GW1's exterior record puts SB2(1)'s entry point left of the launch point: `m ≤ 0`

Packet PROVE-GW1-EXTREC. SB2(1)'s entry form (ruling R91) starts the relative upper flow at the entry
`m = Lx.leftEntry c L` of the lower walk's launch chart `c` at `L = min(A ∩ ℝ)`, and asks `m ≤ 0`: the entry over `L`
is left of the chart point `0` where the new lower piece starts. This file proves it deterministically from the tip
correspondence at `0` (GW1's `ExteriorRecord` datum, through `GW1WalkFinish.boundary_limit_of_exteriorRecord`):

* `bdryValue_facts`: for a conformal chart with a hull model and a boundary map `g` of its inverse, the real boundary
  values left of a free `L` are continuous (local reflection, `IsMapOut.exists_reflection`) and `g` inverts them;
* **`entry_nonpos_of_tendsto`**: if moreover `c⁻¹ → p` at `0` from `ℍ` and `p` is not a free real point left of `L`,
  every entry value at `L` is `≤ 0` (otherwise the boundary values, unbounded below by the bounded displacement of the
  boundary map and tending to `m > 0`, take the value `0` at some `x₀ < L` by the IVT, and then `p = g 0 = x₀`);
* `leftEntry_runChart_nonpos`: the same for the chart of an unfinished regular run;
* **`launchEntry_nonpos_of_exteriorRecord`**: at a launch of the lower walk with the exterior record
  (`ExteriorRecord true`) and a nonnegative right record, `Lv.launchEntry … ≤ 0`.

Deterministic; no named input.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.GW1Ext

open Exist.Staged Exist.StagedLaw SB.Lx

/-- **The real boundary values left of a free `L`**: for a conformal chart with a hull model whose hull leaves the
real line free left of `L`, and a continuous boundary map `g` of its inverse, the chart has real boundary values
`bdryValue c x` at every `x < L`, they are continuous on `(−∞, L)`, and `g` inverts them. (The local-reflection and
inversion steps of `SB.Lx.exists_isLeftEntryValue_of_hullModel`, exported.) -/
theorem bdryValue_facts {c : Chart} (hcc : c.IsConformal) (M : WalkIntCanon.HullModel c) {g : ℂ → ℂ}
    (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g c.2.1 H) {L : ℝ}
    (hfree : ∀ x : ℝ, x < L → ∃ ρ > 0, Disjoint (ball (x : ℂ) ρ) M.hull) :
    (∀ x : ℝ, x < L → Tendsto c.1 (𝓝[H] (x : ℂ)) (𝓝 (bdryValue c x : ℂ))) ∧
      ContinuousOn (bdryValue c) (Iio L) ∧ ∀ x : ℝ, x < L → g (bdryValue c x) = x := by
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
  refine ⟨he, ?_, ?_⟩
  · -- continuity
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
  · -- the boundary map inverts the boundary values
    intro x hx
    have := GW1P.neBot_nhdsWithin_H (SB.Lw.ofReal_mem_Hbar x)
    have h1 : Tendsto c.1 (𝓝[H] (x : ℂ)) (𝓝[H] (bdryValue c x : ℂ)) :=
      tendsto_nhdsWithin_iff.2 ⟨he x hx, (hdom x hx).mono fun z hz => hcc.fwd_mem hz⟩
    have h2 : Tendsto g (𝓝[H] (bdryValue c x : ℂ)) (𝓝 (g (bdryValue c x))) :=
      (hgc _ (SB.Lw.ofReal_mem_Hbar _)).tendsto.mono_left
        (nhdsWithin_mono _ fun z hz => le_of_lt (show (0 : ℝ) < z.im from hz))
    have h3 : Tendsto (fun z => g (c.1 z)) (𝓝[H] (x : ℂ)) (𝓝 (x : ℂ)) := by
      refine (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).congr' ?_
      filter_upwards [hdom x hx] with z hz
      rw [hgi (hcc.fwd_mem hz), hcc.inv_fwd hz]
      rfl
    exact tendsto_nhds_unique (h2.comp h1) h3

/-- **The entry over `L` is left of the chart point `0`** when `0` corresponds to a point `p` that is not a free real
point left of `L`: for a conformal chart with a hull model, a proper boundary extension of its inverse, and the real
line free of the hull left of `L`, if `c⁻¹ → p` at `0` from `ℍ`, every entry value `m` at `L` is `≤ 0`.

Proof: suppose `m > 0`. The real boundary values `e = bdryValue c` are continuous on `(−∞, L)` and inverted by the
boundary map `g` of `c⁻¹`; `g` moves points by at most `C`, so `e x ≤ x + C < 0` far left; `e → m > 0` at `L⁻`. By the
IVT `e x₀ = 0` for some `x₀ < L`, and then `p = g 0 = g (e x₀) = x₀`, a free real point left of `L`. -/
theorem entry_nonpos_of_tendsto {c : Chart} (hcc : c.IsConformal) (M : WalkIntCanon.HullModel c)
    (hc : GW1P.HasProperBdryExt c) {L m : ℝ}
    (hfree : ∀ x : ℝ, x < L → ∃ ρ > 0, Disjoint (ball (x : ℂ) ρ) M.hull)
    (hm : IsLeftEntryValue c L m) {p : ℂ} (hp : Tendsto c.2.1 (𝓝[H] 0) (𝓝 p))
    (hpL : ∀ x : ℝ, x < L → p ≠ (x : ℂ)) : m ≤ 0 := by
  obtain ⟨g, hgc, hgi, -, hgt⟩ := SB.Lw.exists_bdryMap_of_hasProperBdryExt hcc hc
  obtain ⟨f, C, hf, hC⟩ := hc
  obtain ⟨he, hcont, hinv⟩ := bdryValue_facts hcc M hgc hgi hfree
  -- the boundary map is the proper extension, so it moves points by at most `C`
  have hgf : ∀ q ∈ Hbar, g q = f q := fun q hq => by
    have := GW1P.neBot_nhdsWithin_H hq
    exact tendsto_nhds_unique (hgt q hq) (hf q hq)
  -- the entry value is the limit of the boundary values
  have hlim : Tendsto (bdryValue c) (𝓝[<] L) (𝓝 m) := by
    obtain ⟨e, he', hlim⟩ := hm
    refine hlim.congr' (eventually_nhdsWithin_of_forall fun x hx => ?_)
    have h1 := tendsto_bdryValue (he' x hx) (by simp)
    rw [h1.1, Complex.ofReal_re]
  by_contra hm0
  push Not at hm0
  -- far left the boundary values are negative
  set x₁ : ℝ := min (L - 1) (-C - 1) with hx₁
  have hx₁L : x₁ < L := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hneg : bdryValue c x₁ < 0 := by
    have h1 := hC _ (SB.Lw.ofReal_mem_Hbar (bdryValue c x₁))
    rw [← hgf _ (SB.Lw.ofReal_mem_Hbar _), hinv x₁ hx₁L, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs] at h1
    have h2 := (abs_le.1 h1).1
    have h3 : x₁ ≤ -C - 1 := min_le_right _ _
    linarith
  -- near `L` they are positive
  obtain ⟨x₂, hpos, hx₂⟩ := ((hlim.eventually (lt_mem_nhds hm0)).and (Ioo_mem_nhdsLT hx₁L)).exists
  -- the IVT gives a zero
  have hsub : Icc x₁ x₂ ⊆ Iio L := fun z hz => lt_of_le_of_lt hz.2 hx₂.2
  obtain ⟨x₀, hx₀, h0⟩ := intermediate_value_Icc hx₂.1.le (hcont.mono hsub) ⟨hneg.le, hpos.le⟩
  have hx₀L : x₀ < L := hsub hx₀
  -- then `p = g 0 = x₀`
  have hg0 : g 0 = x₀ := by
    have := hinv x₀ hx₀L
    rwa [h0, Complex.ofReal_zero] at this
  have hp0 : p = g 0 := by
    have := GW1P.neBot_nhdsWithin_H (SB.Lw.ofReal_mem_Hbar 0)
    rw [Complex.ofReal_zero] at this
    exact tendsto_nhds_unique hp (hgt 0 (by simpa using SB.Lw.ofReal_mem_Hbar 0))
  exact hpL x₀ hx₀L (hp0.trans hg0)

/-- **The run chart**: for an unfinished regular run and any compact `A` with the fill of its prefix and `L` at most
every real point of `A`, if the run chart's inverse tends at `0` to a point `p` that is not a free real point left
of `L`, the entry of the run chart at `L` is `≤ 0`. -/
theorem leftEntry_runChart_nonpos {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} (spec : ExplSpec)
    (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hreg : ∀ k c θ', (ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 k = some (c, θ') →
      GW1P.PieceRegular (D k).1 (min (instrTime spec k) (D k).2)) (n : ℕ)
    (hnot : stStatus (ExplState.run κ b jumps spec D n) ≠ GW1Conn.stDone) {A : Set ℂ}
    (hAc : IsCompact A) (hAf : fillH A = fillH (SB.prefixPhysSet κ b jumps spec D n)) {L : ℝ}
    (hLA : ∀ y : ℝ, (y : ℂ) ∈ A → L ≤ y) {p : ℂ}
    (hp : Tendsto (stChart (ExplState.run κ b jumps spec D n)).2.1 (𝓝[H] 0) (𝓝 p))
    (hpL : ∀ x : ℝ, x < L → p ≠ (x : ℂ)) :
    leftEntry (stChart (ExplState.run κ b jumps spec D n)) L ≤ 0 := by
  obtain ⟨M, hK⟩ := SB.Lw.exists_hullModel_fill spec D hreg n hnot
  have hcc := (GW2aCont.isConformal_runChart (κ := κ) (b := b) (jumps := jumps) spec D n
    fun j _ c θ h => hreg j c θ h).1
  refine entry_nonpos_of_tendsto hcc M
    (GW1P.isClosed_pieces_run (κ := κ) (b := b) (jumps := jumps) spec D hreg n).1 (fun x hx => ?_)
    (isLeftEntryValue_runChart spec D hreg n hnot hAc hAf hLA) hp hpL
  obtain ⟨ρ, hρ, hd⟩ := SB.Lw.exists_ball_disjoint_fillH hAc fun y hy => lt_of_lt_of_le hx (hLA y hy)
  rw [hAf, ← hK] at hd
  exact ⟨ρ, hρ, hd⟩

open SB.Lv in
/-- **SB2(1)'s entry point is `≤ 0` at a launch with GW1's exterior record** (the clause `m ≤ 0` of
`Lv.SB2RelDriverStatement`, at one sample): if instruction `k` of the lower walk launches at `ω₀`, the launched pieces
are regular, the state before the launch has the exterior record `ExteriorRecord true` (so the launch chart's inverse
tends at `0` to the current point, `GW1WalkFinish.boundary_limit_of_exteriorRecord`, and the current point is the
right record) and the right record is `≥ 0`, then `launchEntry … ≤ 0` for every upper seed `u ≤ 0`: the current point
is a real point `≥ 0 ≥ u ≥ L`, not a free point left of `L`. -/
theorem launchEntry_nonpos_of_exteriorRecord {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type*}
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u : ℝ} {ω₀ : Ω}
    (hreg : ∀ j c θ', (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω₀) (j + 1)).2.2.2.1 j = some (c, θ') →
      GW1P.PieceRegular (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω₀).1
        (min (instrTime (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j)
          (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω₀).2))
    (hF : ω₀ ∈ launchSet κ b jumps E k) (hu : u ≤ 0)
    (hE : GW1WalkFinish.ExteriorRecord true (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω₀) k))
    (h0 : 0 ≤ stRecR (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω₀) k)) :
    launchEntry κ b jumps E k u ω₀ ≤ 0 := by
  have hAc := isCompact_lowerPrefix (u := u) hreg hF
  obtain ⟨⟨c, θ⟩, hl⟩ := Option.ne_none_iff_exists'.1 hF
  have hLu : SB.realMin (SB.lowerPrefix κ b jumps E k u ω₀) ≤ u :=
    SB.FinRel.realMin_le_of_mem hAc (Or.inr ⟨u, ⟨le_rfl, hu⟩, rfl⟩)
  have hlim := GW1WalkFinish.boundary_limit_of_exteriorRecord
    (GW1WalkFinish.hasBdryLimits_chart_run _ _ hreg k) hE
  obtain ⟨-, hpt, -⟩ := hE
  unfold SB.Lv.launchEntry
  rw [launchChart_eq hl, (eq_launch_of_launches _ _ hl).2.2]
  refine leftEntry_runChart_nonpos _ _ hreg k (stStatus_ne_done_of_launches _ _ hl) hAc
    (SB.Lw.fillH_union_real _ _) (fun y hy => SB.FinRel.realMin_le_of_mem hAc hy) hlim fun x hx hpx => ?_
  have hx' : stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω₀) k) = x := by exact_mod_cast hpx
  linarith

end InteractingSLE.Theorem14.GW1Ext
