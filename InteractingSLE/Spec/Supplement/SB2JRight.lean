/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2HEntry

/-!
# SB2(2)'s entry value exists: the launch chart's right boundary values converge at `R⁺`

Packet PROVE-T14-SB2FIN4 (ruling R93). SB2(2)'s target (`SB2LowerLaunchEntryStatement`, `SB2JLower`) reads the lower
walk's remainder in the launch chart `c` of the upper own-angle history, from "the prime end over `R` selected by its
free right collar" (`R = max(A ∩ ℝ)`): the entry value `e_R = g_A(R⁺)` of `c` at `R`. This file is the mirror image
of PROVE-T14-SB2FIN3's `SB2HEntry` (the left entry value of SB2(1)):

* `IsRightEntryValue c R e` (the real boundary values of `c` on `(R, ∞)` tend to `e` at `R⁺`), `rightEntry c R` and
  `IsRightEntryValue.eq_rightEntry` (an entry value is `rightEntry c R`);
* `exists_ball_disjoint_fillH_right`: a real point right of every real point of a compact `A` has a ball missing
  `fillH A` (mirror of `Lw.exists_ball_disjoint_fillH`);
* **`exists_isRightEntryValue_of_hullModel`**: a conformal chart with a hull model and a boundary map has an entry
  value at every `R` right of which the real line is free of the hull (continuous, injective, bounded displacement,
  hence strictly increasing and bounded below, so the limit at `R⁺` exists: `MonotoneOn.tendsto_nhdsGT`);
* **`isRightEntryValue_runChart`**: the run chart of any program (regular, unfinished) at any `R` at least every real
  point of a compact `A` with the prefix's fill;
* `upperSpec`, `upperLaunchSet`, `upperLaunchChart`, `upperEntry` (`= rightEntry (upperLaunchChart …) (realMax
  (upperPrefix …))`), `isCompact_upperPrefix`, `le_realMax_of_mem`, **`isRightEntryValue_upperLaunchChart`**: at a
  launching sample of the upper schedule program with regular pieces, the launch chart has the entry value
  `upperEntry` at `R = realMax (upperPrefix …)`.

Deterministic; no named input.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Lx

/-- **The right entry value** of a chart at `R` (SB2(2): "from the prime end over `R` selected by its free right
collar"): the chart extends to the real points right of `R` with real boundary values, which tend to `e` at `R⁺`. -/
def IsRightEntryValue (c : Chart) (R e : ℝ) : Prop :=
  ∃ f : ℝ → ℝ, (∀ x > R, Tendsto c.1 (𝓝[H] (x : ℂ)) (𝓝 (f x : ℂ))) ∧ Tendsto f (𝓝[>] R) (𝓝 e)

/-- The right entry value of a chart at `R`: the limit from the right of its real boundary values. -/
def rightEntry (c : Chart) (R : ℝ) : ℝ := limUnder (𝓝[>] R) (bdryValue c)

/-- A right entry value is the chart's `rightEntry`. -/
theorem IsRightEntryValue.eq_rightEntry {c : Chart} {R e : ℝ} (h : IsRightEntryValue c R e) :
    e = rightEntry c R := by
  obtain ⟨f, hf, hlim⟩ := h
  have hc : Tendsto (bdryValue c) (𝓝[>] R) (𝓝 e) := by
    refine hlim.congr' (eventually_nhdsWithin_of_forall fun x hx => ?_)
    have h1 := tendsto_bdryValue (hf x hx) (by simp)
    rw [h1.1, Complex.ofReal_re]
  exact hc.limUnder_eq.symm

/-- **A free real point right of a compact set has a ball missing its fill** (mirror of
`Lw.exists_ball_disjoint_fillH`): if every real point of the compact `A` is `< x`, a small ball around `x` misses
`fillH A`. -/
theorem exists_ball_disjoint_fillH_right {A : Set ℂ} (hA : IsCompact A) {x : ℝ}
    (hx : ∀ y : ℝ, (y : ℂ) ∈ A → y < x) : ∃ ρ > 0, Disjoint (ball (x : ℂ) ρ) (fillH A) := by
  -- a margin to the left of `x` free of real points of `A`
  obtain ⟨x', hxx', hx'⟩ : ∃ x' : ℝ, x' < x ∧ ∀ y : ℝ, (y : ℂ) ∈ A → y < x' := by
    by_cases hR : ∃ y : ℝ, (y : ℂ) ∈ A
    · have hRc : IsCompact {y : ℝ | (y : ℂ) ∈ A} :=
        (Complex.isometry_ofReal.isClosedEmbedding.isCompact_preimage hA)
      obtain ⟨y₀, hy₀, hmax⟩ := hRc.exists_isGreatest hR
      refine ⟨(x + y₀) / 2, by linarith [hx y₀ hy₀], fun y hy => ?_⟩
      linarith [hmax hy, hx y₀ hy₀]
    · push Not at hR
      exact ⟨x - 1, by linarith, fun y hy => absurd hy (hR y)⟩
  -- a height below which `A` has no point right of `x'`
  obtain ⟨h₀, hh₀, hh₀A⟩ : ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ z ∈ A, x' ≤ z.re → h₀ ≤ |z.im| := by
    set K := A ∩ {z : ℂ | x' ≤ z.re}
    have hK : IsCompact K := hA.inter_right (isClosed_le continuous_const Complex.continuous_re)
    by_cases hKe : K.Nonempty
    · obtain ⟨z₀, hz₀, hmin⟩ := hK.exists_isMinOn hKe (Complex.continuous_im.abs.continuousOn)
      refine ⟨|z₀.im|, abs_pos.2 fun h0 => ?_, fun z hz hzr => hmin ⟨hz, hzr⟩⟩
      have hz₀r : ((z₀.re : ℝ) : ℂ) = z₀ := Complex.ext (by simp) (by simp [h0])
      have h1 := hx' z₀.re (hz₀r ▸ hz₀.1)
      have h2 : x' ≤ z₀.re := hz₀.2
      linarith
    · exact ⟨1, one_pos, fun z hz hzr => absurd ⟨z, hz, hzr⟩ hKe⟩
  set S : Set ℂ := {z | x' < z.re ∧ 0 < z.im ∧ z.im < h₀} with hS
  have hSA : Disjoint S (closure A) := by
    rw [hA.isClosed.closure_eq]
    refine Set.disjoint_left.2 fun z hzS hzA => ?_
    have := hh₀A z hzA hzS.1.le
    rw [abs_of_pos hzS.2.1] at this
    linarith [hzS.2.2]
  have hSc : IsPreconnected S := by
    have hSeq : S = {c : ℂ | x' < c.re} ∩ {c | 0 < c.im} ∩ {c | c.im < h₀} := by
      ext z; simp only [hS, mem_ofPred_eq, mem_inter_iff, and_assoc]
    rw [hSeq]
    exact (((convex_halfSpace_re_gt x').inter (convex_halfSpace_im_gt 0)).inter
      (convex_halfSpace_im_lt h₀)).isPreconnected
  have hSub : ¬ Bornology.IsBounded S := by
    intro hb
    obtain ⟨M, hM⟩ := hb.exists_norm_le
    set r : ℝ := max (x' + 1) (|M| + 1)
    have hr1 : x' < r := lt_of_lt_of_le (by linarith) (le_max_left _ _)
    have hr2 : |M| + 1 ≤ r := le_max_right _ _
    have hmem : (r : ℂ) + ((h₀ / 2 : ℝ) : ℂ) * Complex.I ∈ S := by
      refine ⟨?_, ?_, ?_⟩ <;> simp <;> linarith
    have h1 := hM _ hmem
    have h2 := Complex.abs_re_le_norm ((r : ℂ) + ((h₀ / 2 : ℝ) : ℂ) * Complex.I)
    have h3 : ((r : ℂ) + ((h₀ / 2 : ℝ) : ℂ) * Complex.I).re = r := by simp
    rw [h3, abs_of_pos (by linarith [abs_nonneg M])] at h2
    linarith [le_abs_self M]
  refine ⟨min (x - x') h₀, lt_min (by linarith) hh₀, Set.disjoint_left.2 fun z hzb hzF => ?_⟩
  have hzd : dist z x < min (x - x') h₀ := hzb
  have hre : |z.re - x| < x - x' := by
    have := Complex.abs_re_le_norm (z - x)
    simp only [Complex.sub_re, Complex.ofReal_re] at this
    rw [← dist_eq_norm] at this
    linarith [min_le_left (x - x') h₀]
  have him : |z.im| < h₀ := by
    have := Complex.abs_im_le_norm (z - x)
    simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at this
    rw [← dist_eq_norm] at this
    linarith [min_le_right (x - x') h₀]
  have hzS : z ∈ S :=
    ⟨by linarith [(abs_lt.1 hre).1], hzF.1, by linarith [le_abs_self z.im]⟩
  rcases hzF.2 with hcl | hbd
  · exact Set.disjoint_left.1 hSA hzS hcl
  · have hsub : S ⊆ connectedComponentIn (H \ closure A) z :=
      hSc.subset_connectedComponentIn hzS fun w hw => ⟨hw.2.1, Set.disjoint_left.1 hSA hw⟩
    exact hSub (hbd.subset hsub)

/-- **A chart with a hull model and a boundary map has a right entry value at every `R` right of which the real line
is free** (mirror of `exists_isLeftEntryValue_of_hullModel`): its real boundary values on `(R, ∞)` are continuous
(local reflection), injective (the boundary map inverts them), within bounded distance of the identity, hence strictly
increasing, and bounded below; so they converge at `R⁺`. -/
theorem exists_isRightEntryValue_of_hullModel {c : Chart} (hcc : c.IsConformal) (M : WalkIntCanon.HullModel c)
    {g : ℂ → ℂ} (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g c.2.1 H) {R : ℝ}
    (hfree : ∀ x : ℝ, R < x → ∃ ρ > 0, Disjoint (ball (x : ℂ) ρ) M.hull) :
    ∃ e, IsRightEntryValue c R e := by
  -- the local reflection at a free real point
  have hloc : ∀ x : ℝ, R < x → ∃ ρ > 0, ∃ G : ℂ → ℂ, ContinuousOn G (ball (x : ℂ) ρ) ∧
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
  have he : ∀ x : ℝ, R < x → Tendsto c.1 (𝓝[H] (x : ℂ)) (𝓝 (bdryValue c x : ℂ)) := fun x hx => by
    obtain ⟨ρ, hρ, G, -, hG⟩ := hloc x hx
    exact (tendsto_bdryValue (hG x (mem_ball_self hρ)).1 (hG x (mem_ball_self hρ)).2).2
  -- points near a free real point are in the chart domain
  have hdom : ∀ x : ℝ, R < x → ∀ᶠ z in 𝓝[H] (x : ℂ), z ∈ (c.dom : Set ℂ) := fun x hx => by
    obtain ⟨ρ, hρ, hd⟩ := hfree x hx
    filter_upwards [inter_mem_nhdsWithin H (ball_mem_nhds (x : ℂ) hρ)] with z hz
    rw [M.dom_eq]
    exact ⟨hz.1, fun h => hd.ne_of_mem hz.2 h rfl⟩
  -- continuity
  have hcont : ContinuousOn (bdryValue c) (Ioi R) := by
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
  have hinv : ∀ x : ℝ, R < x → g (bdryValue c x) = x := fun x hx => by
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
  have hinj : InjOn (bdryValue c) (Ioi R) := fun x hx y hy hxy => by
    have h1 := hinv x hx
    rw [hxy, hinv y hy] at h1
    exact_mod_cast h1.symm
  -- bounded displacement
  obtain ⟨C, hC⟩ := M.mapOut.exists_norm_sub_le M.isHull
  have hdisp : ∀ x : ℝ, R < x → |bdryValue c x + M.shift - x| ≤ C := fun x hx => by
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
  have hlo : ∀ x : ℝ, R < x → x - M.shift - C ≤ bdryValue c x := fun x hx => by
    have := (abs_le.1 (hdisp x hx)).1; linarith
  have hhi : ∀ x : ℝ, R < x → bdryValue c x ≤ x - M.shift + C := fun x hx => by
    have := (abs_le.1 (hdisp x hx)).2; linarith
  -- monotone
  have hmono : MonotoneOn (bdryValue c) (Ioi R) := by
    intro x hx y hy hxy
    rcases eq_or_lt_of_le hxy with rfl | hlt
    · exact le_rfl
    set a := max y (x + 2 * C + 1) with ha
    have hya : y ≤ a := le_max_left _ _
    have hxa : x + 2 * C + 1 ≤ a := le_max_right _ _
    have hsub : Icc x a ⊆ Ioi R := fun z hz => lt_of_lt_of_le (show R < x from hx) hz.1
    have hRa : R < a := lt_of_lt_of_le (show R < y from hy) hya
    have hfa : bdryValue c x ≤ bdryValue c a := by
      have := hhi x hx; have := hlo a hRa; linarith
    have hs := ContinuousOn.strictMonoOn_of_injOn_Icc (hlt.le.trans hya) hfa (hcont.mono hsub)
      (hinj.mono hsub)
    exact (hs ⟨le_rfl, hlt.le.trans hya⟩ ⟨hlt.le, hya⟩ hlt).le
  have hbdd : BddBelow (bdryValue c '' Ioi R) := by
    refine ⟨R - M.shift - C, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    have := hlo x hx
    have : R < x := hx
    linarith
  exact ⟨_, bdryValue c, he, hmono.tendsto_nhdsGT hbdd⟩

open Exist.StagedLaw in
/-- **A run chart has a right entry value at every `R` at least every real point of `A`** (mirror of
`isLeftEntryValue_runChart`; any program, regular and unfinished, any compact `A` with the prefix's fill):
`IsRightEntryValue (run chart) R (rightEntry (run chart) R)`. `R` may be a point of `A`. -/
theorem isRightEntryValue_runChart {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} (spec : ExplSpec)
    (D : ℕ → (NNReal → ℝ) × ENNReal)
    (hreg : ∀ k c θ', (ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 k = some (c, θ') →
      GW1P.PieceRegular (D k).1 (min (instrTime spec k) (D k).2)) (n : ℕ)
    (hnot : stStatus (ExplState.run κ b jumps spec D n) ≠ GW1Conn.stDone) {A : Set ℂ}
    (hAc : IsCompact A) (hAf : fillH A = fillH (SB.prefixPhysSet κ b jumps spec D n)) {R : ℝ}
    (hRA : ∀ y : ℝ, (y : ℂ) ∈ A → y ≤ R) :
    IsRightEntryValue (stChart (ExplState.run κ b jumps spec D n)) R
      (rightEntry (stChart (ExplState.run κ b jumps spec D n)) R) := by
  obtain ⟨M, hK⟩ := Lw.exists_hullModel_fill spec D hreg n hnot
  have hcc := (GW2aCont.isConformal_runChart (κ := κ) (b := b) (jumps := jumps) spec D n
    fun j _ c θ h => hreg j c θ h).1
  obtain ⟨g, hgc, hgi, -, -⟩ := Lw.exists_bdryMap_of_hasProperBdryExt hcc
    (GW1P.isClosed_pieces_run (κ := κ) (b := b) (jumps := jumps) spec D hreg n).1
  obtain ⟨e, he⟩ := exists_isRightEntryValue_of_hullModel hcc M hgc hgi (R := R) fun x hx => by
    obtain ⟨ρ, hρ, hd⟩ := exists_ball_disjoint_fillH_right hAc fun y hy => lt_of_le_of_lt (hRA y hy) hx
    rw [hAf, ← hK] at hd
    exact ⟨ρ, hρ, hd⟩
  exact he.eq_rightEntry ▸ he

/-- The largest real point of a compact set bounds its real points. -/
theorem le_realMax_of_mem {A : Set ℂ} (hA : IsCompact A) {y : ℝ} (hy : (y : ℂ) ∈ A) : y ≤ realMax A := by
  refine le_csSup ?_ hy
  obtain ⟨M, hM⟩ := hA.isBounded.exists_norm_le
  refine ⟨M, fun z hz => ?_⟩
  have := hM _ hz
  rw [Complex.norm_real, Real.norm_eq_abs] at this
  exact (le_abs_self z).trans this

end InteractingSLE.Theorem14.SB.Lx

namespace InteractingSLE.Theorem14.SB.Lu

open Lx Exist.Staged Exist.StagedLaw

/-- The upper own-angle history of SB2(2): the schedule `l` from the upper seed `u` (`upperPrefix`'s program). -/
def upperSpec (u : ℝ) (l : List (ℝ × ℝ≥0)) : ExplSpec := ⟨u, true, scheduleProgram 0 l⟩

/-- The event that instruction `k` of the upper schedule program launches. -/
def upperLaunchSet (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type*}
    (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (u : ℝ) (l : List (ℝ × ℝ≥0)) (k : ℕ) : Set Ω :=
  {ω₀ | (ExplState.run κ b jumps (upperSpec u l) (fun j => E (upperSpec u l) j ω₀) (k + 1)).2.2.2.1 k ≠ none}

/-- The chart in which instruction `k` of the upper schedule program launches (the identity chart otherwise). -/
def upperLaunchChart (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type*}
    (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (u : ℝ) (l : List (ℝ × ℝ≥0)) (k : ℕ) (ω₀ : Ω) : Chart :=
  ((ExplState.run κ b jumps (upperSpec u l) (fun j => E (upperSpec u l) j ω₀) (k + 1)).2.2.2.1 k).elim
    Chart.id Prod.fst

/-- **SB2(2)'s entry point** in the upper launch chart: the right entry value `e_R = g_A(R⁺)` at
`R = realMax (upperPrefix …)` (`Lx.rightEntry`; by `Lx.IsRightEntryValue.eq_rightEntry` the only possible one). -/
def upperEntry (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type*}
    (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (u : ℝ) (l : List (ℝ × ℝ≥0)) (k : ℕ) (ω : Ω) : ℝ :=
  rightEntry (upperLaunchChart κ b jumps E u l k ω) (realMax (upperPrefix κ b jumps E u l k ω))

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type*} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
  {u : ℝ} {l : List (ℝ × ℝ≥0)} {k : ℕ} {ω₀ : Ω}

theorem upperLaunchChart_eq {c₀ : Chart} {θ : ℝ}
    (h : (ExplState.run κ b jumps (upperSpec u l) (fun j => E (upperSpec u l) j ω₀) (k + 1)).2.2.2.1 k =
      some (c₀, θ)) : upperLaunchChart κ b jumps E u l k ω₀ = c₀ := by
  simp only [upperLaunchChart, h, Option.elim]

theorem mem_upperLaunchSet {c₀ : Chart} {θ : ℝ}
    (h : (ExplState.run κ b jumps (upperSpec u l) (fun j => E (upperSpec u l) j ω₀) (k + 1)).2.2.2.1 k =
      some (c₀, θ)) : ω₀ ∈ upperLaunchSet κ b jumps E u l k := by
  simp only [upperLaunchSet, mem_ofPred_eq, h, ne_eq, reduceCtorEq, not_false_eq_true]

/-- **The retained upper prefix is compact at a launch** of the upper schedule program (regular launched pieces). -/
theorem isCompact_upperPrefix
    (hreg : ∀ j c θ', (ExplState.run κ b jumps (upperSpec u l) (fun i => E (upperSpec u l) i ω₀) (j + 1)).2.2.2.1 j =
        some (c, θ') →
      GW1P.PieceRegular (E (upperSpec u l) j ω₀).1 (min (instrTime (upperSpec u l) j) (E (upperSpec u l) j ω₀).2))
    (hF : ω₀ ∈ upperLaunchSet κ b jumps E u l k) : IsCompact (upperPrefix κ b jumps E u l k ω₀) := by
  obtain ⟨⟨c, θ⟩, hlk⟩ := Option.ne_none_iff_exists'.1 hF
  exact (isCompact_prefixPhysSet_run _ _ hreg k (stStatus_ne_done_of_launches _ _ hlk)).union
    (isCompact_Icc.image Complex.continuous_ofReal)

/-- **The entry value at a launch of the upper schedule program** (SB2(2)'s entry clause, ruling R93): at a sample
where instruction `k` launches and the launched pieces are regular, the launch chart has the right entry value
`upperEntry` at `R = realMax (upperPrefix …)`. -/
theorem isRightEntryValue_upperLaunchChart
    (hreg : ∀ j c θ', (ExplState.run κ b jumps (upperSpec u l) (fun i => E (upperSpec u l) i ω₀) (j + 1)).2.2.2.1 j =
        some (c, θ') →
      GW1P.PieceRegular (E (upperSpec u l) j ω₀).1 (min (instrTime (upperSpec u l) j) (E (upperSpec u l) j ω₀).2))
    (hF : ω₀ ∈ upperLaunchSet κ b jumps E u l k) :
    IsRightEntryValue (upperLaunchChart κ b jumps E u l k ω₀) (realMax (upperPrefix κ b jumps E u l k ω₀))
      (upperEntry κ b jumps E u l k ω₀) := by
  have hAc := isCompact_upperPrefix hreg hF
  obtain ⟨⟨c, θ⟩, hlk⟩ := Option.ne_none_iff_exists'.1 hF
  unfold upperEntry
  rw [upperLaunchChart_eq hlk, (eq_launch_of_launches _ _ hlk).2.2]
  exact isRightEntryValue_runChart _ _ hreg k (stStatus_ne_done_of_launches _ _ hlk) hAc
    (Lw.fillH_union_real _ _) fun y hy => le_realMax_of_mem hAc hy

/-- The right entry value of the upper launch chart is nonnegative once the prime end over `R` lies right of the
chart's boundary point `0`: if the boundary values right of `R` are at least `0`, so is `e_R`. -/
theorem upperEntry_nonneg_of_bdryValue
    (he : IsRightEntryValue (upperLaunchChart κ b jumps E u l k ω₀) (realMax (upperPrefix κ b jumps E u l k ω₀))
      (upperEntry κ b jumps E u l k ω₀))
    (h0 : ∀ x > realMax (upperPrefix κ b jumps E u l k ω₀),
      0 ≤ bdryValue (upperLaunchChart κ b jumps E u l k ω₀) x) :
    0 ≤ upperEntry κ b jumps E u l k ω₀ := by
  obtain ⟨f, hf, hlim⟩ := he
  refine ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun x hx => ?_)
  have h1 := tendsto_bdryValue (hf x hx) (by simp)
  have := h0 x hx
  rw [h1.1, Complex.ofReal_re] at this
  exact this

end InteractingSLE.Theorem14.SB.Lu
