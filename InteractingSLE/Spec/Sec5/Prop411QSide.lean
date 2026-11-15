/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.ReverseContactS5
import InteractingSLE.Spec.Sec5.Cond44RefSide

/-!
# Proposition 4.9's per-time side in Lemma 4.5's chart `Q`: the deterministic no-wrap step

Packet PROVE-SEC5-O. Specification §4.2, proof of Proposition 4.9 (`source/spec/p097-144.md#prop-4.9`, p. 120):

> "fix any stopping time `τ′` for `η′` … Then `η` almost surely exits `𝒮 ∖ η′([0, τ′])` on the left side of
> `η′([0, τ′])` or to the left of `z₀` on `∂_U𝒮`. … We will now argue that `η′(τ′)` is to the right of `η`. Let `τ` be
> the first time `η` exits `𝒮 ∖ η′([0, τ′])`. … the only way that `η′(τ′)` could be strictly to the left of `η` is if
> after `τ`, `η` wraps around `η′([0, τ′])` and hits its right side. … This is a contradiction since `η′` absorbs the
> points of `η` in reverse chronological order by Lemma 4.7."

**The chart.** In Lemma 4.5's chart `Q` the flow line `η` is a proper arc of `ℍ` from `0` to `∞` and the counterflow
line is `η′ = R ∘ β`, `R(z) = −1/z`, for a Loewner trace `β` (driver `w`) from `0` to `∞`. The counterflow prefix
`η′((0, s])` fills `G = R(K_s)`, and `Ψ = R ∘ f_s ∘ R` (`WangWu.revChart`) maps `ℍ ∖ G` onto `ℍ`, fixing `0` and
sending the tip `η′(s)` to `∞`. In `Ψ`'s coordinates the left side of `G` is the far negative half-line; "`η` exits
`ℍ ∖ G` on the left side of `G`" says that `Ψ ∘ η` has a negative real limit `x₀` at the exit time `t₀`.

**The no-wrap step, made precise** (`negInv_notMem_leftSideOf_of_exit`). If, in addition, `η` stays in `G` after `t₀`
(this is where the reverse chronological order of Lemma 4.7 enters: `Prop411QOrder`), then the tip `η′(s)` is not on
the left side of `η`. Proof: the Möbius map `M(z) = x₀ z / (x₀ − z)` (fixing `0`, sending `x₀` to `∞`) turns
`Ψ ∘ η|[0, t₀)` into a proper arc `γ`. The right side of `γ` is preconnected (Wang–Wu's crosscut theory), so its image
`S = Ψ⁻¹ M⁻¹(rightSide γ)` is a preconnected subset of `ℍ ∖ η`. It contains points near the tip (near `∞` in `Ψ`'s
coordinates, i.e. near `M(∞) = −x₀ > 0`) and points near a positive real point of the physical boundary (through the
boundary extension of the Loewner map at a far negative point, `WangWu.SideValues`). So `S` lies in one component of
`ℍ ∖ η`, which touches `ℝ₊`; were the tip on the left side, that component would also be on the left side.

## Main results

* `mobAt`, `mobAt_mem_H`, `mobAt_neg_mobAt`, `tendsto_norm_mobAt`, `tendsto_mobAt_cobounded`: the Möbius chart;
* `eventually_mem_rightSideOf`, `eventually_mem_leftSideOf`: points of `ℍ` near a nonzero real point lie on the
  corresponding side of a proper arc;
* `exists_neg_extendFrom_fwdMapInv`: far on the negative axis the boundary extension of `F_s` is a negative real;
* **`negInv_notMem_leftSideOf_of_exit`**: the no-wrap step.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Prop411Q

open WangWu hiding ratPt exists_ratPt_dist_lt

/-! ### The Möbius chart `M(z) = x₀ z / (x₀ − z)` -/

section Mobius

/-- The Möbius map of `ℍ` fixing `0` and sending the real point `x₀ ≠ 0` to `∞` (and `∞` to `−x₀`). -/
def mobAt (x₀ : ℝ) (z : ℂ) : ℂ := (x₀ : ℂ) * z / ((x₀ : ℂ) - z)

theorem mobAt_zero (x₀ : ℝ) : mobAt x₀ 0 = 0 := by simp [mobAt]

theorem im_mobAt (x₀ : ℝ) (z : ℂ) : (mobAt x₀ z).im = x₀ ^ 2 * z.im / normSq ((x₀ : ℂ) - z) := by
  simp only [mobAt, div_im, mul_re, mul_im, ofReal_re, ofReal_im, sub_re, sub_im]
  ring

theorem sub_ne_zero_of_mem_H (x₀ : ℝ) {z : ℂ} (hz : z ∈ H) : (x₀ : ℂ) - z ≠ 0 := fun h => by
  have : ((x₀ : ℂ) - z).im = 0 := by rw [h]; simp
  simp only [sub_im, ofReal_im, zero_sub, neg_eq_zero] at this
  have h2 : (0 : ℝ) < z.im := hz
  linarith

theorem mobAt_mem_H {x₀ : ℝ} (hx₀ : x₀ ≠ 0) {z : ℂ} (hz : z ∈ H) : mobAt x₀ z ∈ H := by
  show 0 < (mobAt x₀ z).im
  rw [im_mobAt]
  have h1 : 0 < normSq ((x₀ : ℂ) - z) := normSq_pos.2 (sub_ne_zero_of_mem_H x₀ hz)
  have h2 : (0 : ℝ) < z.im := hz
  positivity

/-- `M_{−x₀}` inverts `M_{x₀}` off the pole. -/
theorem mobAt_neg_mobAt {x₀ : ℝ} (hx₀ : x₀ ≠ 0) {z : ℂ} (hz : (x₀ : ℂ) - z ≠ 0) :
    mobAt (-x₀) (mobAt x₀ z) = z := by
  have hx : (x₀ : ℂ) ≠ 0 := ofReal_ne_zero.2 hx₀
  simp only [mobAt, ofReal_neg]
  have h2 : -(x₀ : ℂ) - (x₀ : ℂ) * z / ((x₀ : ℂ) - z) = -(x₀ : ℂ) ^ 2 / ((x₀ : ℂ) - z) := by
    field_simp
    ring
  rw [h2]
  field_simp

theorem mobAt_mobAt_neg {x₀ : ℝ} (hx₀ : x₀ ≠ 0) {z : ℂ} (hz : (x₀ : ℂ) + z ≠ 0) :
    mobAt x₀ (mobAt (-x₀) z) = z := by
  have h := mobAt_neg_mobAt (x₀ := -x₀) (neg_ne_zero.2 hx₀) (z := z) (by simpa [sub_eq_add_neg, add_comm]
    using (show -(x₀ : ℂ) - z ≠ 0 from fun h => hz (by linear_combination -h)))
  simpa only [neg_neg] using h

theorem continuousAt_mobAt (x₀ : ℝ) {z : ℂ} (hz : (x₀ : ℂ) - z ≠ 0) : ContinuousAt (mobAt x₀) z := by
  unfold mobAt
  exact (continuousAt_const.mul continuousAt_id).div (continuousAt_const.sub continuousAt_id) hz

/-- `‖M(z)‖ → ∞` as `z → x₀`. -/
theorem tendsto_norm_mobAt {x₀ : ℝ} (hx₀ : x₀ ≠ 0) :
    Tendsto (fun z => ‖mobAt x₀ z‖) (𝓝[≠] (x₀ : ℂ)) atTop := by
  have hnum : Tendsto (fun z : ℂ => ‖(x₀ : ℂ) * z‖) (𝓝[≠] (x₀ : ℂ)) (𝓝 (‖(x₀ : ℂ) * x₀‖)) :=
    ((continuous_const.mul continuous_id).norm.tendsto _).mono_left nhdsWithin_le_nhds
  have hpos : 0 < ‖(x₀ : ℂ) * x₀‖ := by
    rw [norm_mul]; have := norm_pos_iff.2 (ofReal_ne_zero.2 hx₀); positivity
  have hden : Tendsto (fun z : ℂ => ‖(x₀ : ℂ) - z‖) (𝓝[≠] (x₀ : ℂ)) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun z : ℂ => ‖(x₀ : ℂ) - z‖) (𝓝 (x₀ : ℂ)) (𝓝 ‖(x₀ : ℂ) - x₀‖) :=
        (continuous_const.sub continuous_id).norm.tendsto _
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz
      exact norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hz))
  have h := hnum.pos_mul_atTop hpos (tendsto_inv_nhdsGT_zero.comp hden)
  refine h.congr fun z => ?_
  simp only [Function.comp_apply, mobAt, div_eq_mul_inv, norm_mul, norm_inv]

/-- `M(z) → −x₀` as `‖z‖ → ∞`. -/
theorem tendsto_mobAt_cobounded {x₀ : ℝ} {ι : Type*} {l : Filter ι} {f : ι → ℂ}
    (hf : Tendsto (fun i => ‖f i‖) l atTop) : Tendsto (fun i => mobAt x₀ (f i)) l (𝓝 ((-x₀ : ℝ) : ℂ)) := by
  have hinv : Tendsto (fun i => (f i)⁻¹) l (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact hf.inv_tendsto_atTop.congr fun i => by simp
  have hev : ∀ᶠ i in l, f i ≠ 0 := (hf.eventually_gt_atTop 0).mono fun i hi => norm_pos_iff.1 hi
  have hlim : Tendsto (fun i => (x₀ : ℂ) / ((x₀ : ℂ) * (f i)⁻¹ - 1)) l
      (𝓝 ((x₀ : ℂ) / ((x₀ : ℂ) * 0 - 1))) :=
    tendsto_const_nhds.div ((tendsto_const_nhds.mul hinv).sub tendsto_const_nhds) (by simp)
  rw [mul_zero, zero_sub, div_neg, div_one] at hlim
  refine (hlim.congr' (hev.mono fun i hi => ?_)).trans (by simp)
  simp only [mobAt]
  field_simp

end Mobius

/-! ### Points of `ℍ` near a nonzero real point lie on its side of a proper arc -/

section Sides

variable {γ : ℝ → ℂ}

theorem ofReal_mem_closure_ball_inter_H (x : ℝ) {r : ℝ} (hr : 0 < r) :
    (x : ℂ) ∈ closure (ball (x : ℂ) r ∩ H) := by
  have ht : Tendsto (fun ε : ℝ => (x : ℂ) + ε * I) (𝓝[>] 0) (𝓝 (x : ℂ)) := by
    have : Tendsto (fun ε : ℝ => (x : ℂ) + ε * I) (𝓝 0) (𝓝 ((x : ℂ) + (0 : ℝ) * I)) :=
      (continuous_const.add (continuous_ofReal.mul continuous_const)).tendsto _
    simpa using this.mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto ht ?_
  have hb : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), (x : ℂ) + ε * I ∈ ball (x : ℂ) r := ht.eventually (ball_mem_nhds _ hr)
  filter_upwards [hb, self_mem_nhdsWithin] with ε hε hε0
  exact ⟨hε, show (0 : ℝ) < ((x : ℂ) + ε * I).im by simpa using hε0⟩

/-- A small half-disc at a real point off the arc lies in one component of `ℍ ∖ arc`, adherent to that point. -/
theorem exists_halfDisc_component (hγ : IsProperArc γ) {x : ℝ} (hx : x ≠ 0) :
    ∃ r > 0, ∀ z ∈ ball (x : ℂ) r ∩ H, z ∈ H \ arcRange γ ∧
      (x : ℂ) ∈ closure (connectedComponentIn (H \ arcRange γ) z) := by
  have hxA := hγ.ofReal_notMem_arcRange hx
  obtain ⟨r, hr, hrA⟩ := Metric.isOpen_iff.1 hγ.isClosed_arcRange.isOpen_compl _ hxA
  refine ⟨r, hr, fun z hz => ?_⟩
  have hV : ball (x : ℂ) r ∩ H ⊆ H \ arcRange γ := fun w hw => ⟨hw.2, hrA hw.1⟩
  have hconv : Convex ℝ (ball (x : ℂ) r ∩ H) := (convex_ball _ _).inter (convex_halfSpace_im_gt 0)
  have hsub : ball (x : ℂ) r ∩ H ⊆ connectedComponentIn (H \ arcRange γ) z :=
    hconv.isPreconnected.subset_connectedComponentIn hz hV
  exact ⟨hV hz, closure_mono hsub (ofReal_mem_closure_ball_inter_H x hr)⟩

theorem eventually_mem_rightSideOf (hγ : IsProperArc γ) {x : ℝ} (hx : 0 < x) :
    ∀ᶠ z in 𝓝[H] (x : ℂ), z ∈ rightSideOf (arcRange γ) := by
  obtain ⟨r, hr, hcomp⟩ := exists_halfDisc_component hγ hx.ne'
  filter_upwards [inter_mem_nhdsWithin H (ball_mem_nhds (x : ℂ) hr)] with z hz
  obtain ⟨hzA, hcl⟩ := hcomp z ⟨hz.2, hz.1⟩
  exact ⟨hzA, x, hx, hγ.ofReal_notMem_arcRange hx.ne', hcl⟩

theorem eventually_mem_leftSideOf (hγ : IsProperArc γ) {x : ℝ} (hx : x < 0) :
    ∀ᶠ z in 𝓝[H] (x : ℂ), z ∈ leftSideOf (arcRange γ) := by
  obtain ⟨r, hr, hcomp⟩ := exists_halfDisc_component hγ hx.ne
  filter_upwards [inter_mem_nhdsWithin H (ball_mem_nhds (x : ℂ) hr)] with z hz
  obtain ⟨hzA, hcl⟩ := hcomp z ⟨hz.2, hz.1⟩
  exact ⟨hzA, x, hx, hγ.ofReal_notMem_arcRange hx.ne, hcl⟩

end Sides

/-! ### Far on the negative axis the Loewner map is real -/

section Boundary

variable {w : ℝ → ℝ} {β : ℝ → ℂ} {s : ℝ}

/-- **The boundary extension of `F_s` at a far negative real point is a negative real**: there are `ω₀ < 0` and
`y₀ < 0` with `F_s(ξ) → y₀` as `ξ → ω₀` in `ℍ` (left of the hull image `F̄_s` maps into `ℝ`, Wang–Wu's
`neg_rightImg_sub_lt_of_extendFrom_mem_H`, and `F̄_s` moves points by a bounded amount). -/
theorem exists_neg_tendsto_fwdMapInv (hβ : IsLoewnerTrace w β) (hw : Continuous w) (hw0 : w 0 = 0)
    (hs : 0 ≤ s) : ∃ ω₀ y₀ : ℝ, ω₀ < 0 ∧ y₀ < 0 ∧
      Tendsto (fwdMapInv w s) (𝓝[H] (ω₀ : ℂ)) (𝓝 (y₀ : ℂ)) := by
  obtain ⟨C, -, hC⟩ := exists_norm_extendFrom_sub_le hβ hw hw0 hs
  set ω₀ : ℝ := min (-|C| - 1) (-MartChar.RealFlow.rightImg (fun r => -w r) 0 s - w s - 1) with hω₀
  have hω₀neg : ω₀ < 0 := (min_le_left _ _).trans_lt (by linarith [abs_nonneg C])
  have hHbar : ((ω₀ : ℝ) : ℂ) ∈ Hbar := mem_Hbar_of_im_eq_zero (by simp)
  set F := extendFrom H (fwdMapInv w s) (ω₀ : ℂ) with hF
  have hFH : F ∉ H := fun h => by
    have := neg_rightImg_sub_lt_of_extendFrom_mem_H hβ hw hw0 hs (x := ω₀) h
    have h2 : ω₀ ≤ -MartChar.RealFlow.rightImg (fun r => -w r) 0 s - w s - 1 := min_le_right _ _
    linarith
  have hFim : F.im = 0 := by
    have h1 : 0 ≤ F.im := extendFrom_mem_Hbar hβ hw hw0 hs hHbar
    have h2 : ¬ 0 < F.im := hFH
    linarith [not_lt.1 h2]
  have hFre : F.re < 0 := by
    have h1 := hC _ hHbar
    have h2 : |(F - (ω₀ : ℂ)).re| ≤ ‖F - (ω₀ : ℂ)‖ := abs_re_le_norm _
    simp only [sub_re, ofReal_re] at h2
    have h3 : ω₀ ≤ -|C| - 1 := min_le_left _ _
    have h4 := (abs_le.1 (h2.trans h1)).2
    linarith [le_abs_self C]
  refine ⟨ω₀, F.re, hω₀neg, hFre, ?_⟩
  have hFeq : F = ((F.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hFim])
  rw [← hFeq]
  exact (hβ.hasBdryLimits hw hw0 hs).tendsto hHbar

end Boundary

/-! ### The no-wrap step -/

section NoWrap

/-- The time change `u ↦ t₀ u / (1 + u)` from `[0, ∞)` onto `[0, t₀)`. -/
def arcClock (t₀ u : ℝ) : ℝ := t₀ * (u / (1 + u))

theorem arcClock_pos {t₀ u : ℝ} (ht₀ : 0 < t₀) (hu : 0 < u) : 0 < arcClock t₀ u := by
  unfold arcClock; positivity

theorem arcClock_lt {t₀ u : ℝ} (ht₀ : 0 < t₀) (hu : 0 ≤ u) : arcClock t₀ u < t₀ := by
  unfold arcClock
  have h1 : u / (1 + u) < 1 := (div_lt_one (by linarith)).2 (by linarith)
  nlinarith

theorem arcClock_inv {t₀ t : ℝ} (ht0 : 0 ≤ t) (ht : t < t₀) : arcClock t₀ (t / (t₀ - t)) = t := by
  unfold arcClock
  have h : t₀ - t ≠ 0 := sub_ne_zero.2 ht.ne'
  have ht₀ : t₀ ≠ 0 := by linarith
  have h2 : (1 + t / (t₀ - t)) = t₀ / (t₀ - t) := by field_simp; ring
  rw [h2]
  field_simp

theorem arcClock_injOn {t₀ : ℝ} (ht₀ : 0 < t₀) : InjOn (arcClock t₀) (Ici 0) := by
  intro u hu v hv e
  unfold arcClock at e
  have hu1 : (1 + u) ≠ 0 := by have : (0 : ℝ) ≤ u := hu; linarith
  have hv1 : (1 + v) ≠ 0 := by have : (0 : ℝ) ≤ v := hv; linarith
  have e2 : u / (1 + u) = v / (1 + v) := mul_left_cancel₀ ht₀.ne' e
  field_simp at e2
  linarith

theorem continuous_arcClock_at {t₀ u : ℝ} (hu : 0 ≤ u) : ContinuousAt (arcClock t₀) u := by
  unfold arcClock
  exact continuousAt_const.mul (continuousAt_id.div (continuousAt_const.add continuousAt_id) (by linarith))

theorem tendsto_arcClock_atTop {t₀ : ℝ} (ht₀ : 0 < t₀) : Tendsto (arcClock t₀) atTop (𝓝[<] t₀) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, (eventually_ge_atTop 0).mono fun u hu => arcClock_lt ht₀ hu⟩
  have h1 : Tendsto (fun u : ℝ => u / (1 + u)) atTop (𝓝 1) := by
    have h2 : Tendsto (fun u : ℝ => 1 - (1 + u)⁻¹) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub (tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left _ 1 tendsto_id))
    rw [sub_zero] at h2
    refine h2.congr' ((eventually_ge_atTop 0).mono fun u hu => ?_)
    have : (1 + u) ≠ 0 := by linarith
    field_simp
    ring
  have h3 := (tendsto_const_nhds (x := t₀)).mul h1
  rw [mul_one] at h3
  exact h3

variable {η β : ℝ → ℂ} {w : ℝ → ℝ} {s t₀ x₀ : ℝ}

/-- The exit arc: `M ∘ Ψ ∘ η ∘ (time change)` on `(0, ∞)`, and `0` at times `≤ 0`. -/
def exitArc (w : ℝ → ℝ) (s t₀ x₀ : ℝ) (η : ℝ → ℂ) (u : ℝ) : ℂ :=
  if u ≤ 0 then 0 else mobAt x₀ (revChart w s (η (arcClock t₀ u)))

theorem exitArc_of_pos {u : ℝ} (hu : 0 < u) :
    exitArc w s t₀ x₀ η u = mobAt x₀ (revChart w s (η (arcClock t₀ u))) := by
  simp [exitArc, not_le.2 hu]

/-- **`M ∘ Ψ ∘ η` up to the exit time is a proper arc.** -/
theorem isProperArc_exitArc (hη : IsProperArc η) (hw : Continuous w) (hw0 : w 0 = 0) (hs : 0 ≤ s)
    (ht₀ : 0 < t₀) (hx₀ : x₀ ≠ 0) (hpre : ∀ t ∈ Ioo 0 t₀, η t ∉ negInv '' fwdHull w s)
    (hlim : Tendsto (fun t => revChart w s (η t)) (𝓝[<] t₀) (𝓝 (x₀ : ℂ))) :
    IsProperArc (exitArc w s t₀ x₀ η) := by
  set G := negInv '' fwdHull w s with hG
  have hmem : ∀ u, 0 < u → η (arcClock t₀ u) ∈ H \ G := fun u hu =>
    ⟨hη.mem_H _ (arcClock_pos ht₀ hu), hpre _ ⟨arcClock_pos ht₀ hu, arcClock_lt ht₀ hu.le⟩⟩
  have hΨH : ∀ u, 0 < u → revChart w s (η (arcClock t₀ u)) ∈ H := fun u hu => revChart_mem_H hw hs (hmem u hu)
  have hopen : IsOpen (H \ G) := isOpen_H_diff_negInv_fwdHull hw hs
  have hηc : ∀ {t : ℝ}, 0 < t → ContinuousAt η t := fun ht =>
    hη.cont.continuousAt (Ici_mem_nhds ht)
  -- continuity at positive times
  have hcpos : ∀ u, 0 < u → ContinuousAt (fun u => mobAt x₀ (revChart w s (η (arcClock t₀ u)))) u := by
    intro u hu
    have h1 : ContinuousAt (fun u => η (arcClock t₀ u)) u :=
      ContinuousAt.comp (g := η) (f := arcClock t₀) (hηc (arcClock_pos ht₀ hu)) (continuous_arcClock_at hu.le)
    have h2 : ContinuousAt (revChart w s) (η (arcClock t₀ u)) :=
      (continuousOn_revChart hw hs).continuousAt (hopen.mem_nhds (hmem u hu))
    have h3 : ContinuousAt (fun u => revChart w s (η (arcClock t₀ u))) u :=
      ContinuousAt.comp (g := revChart w s) (f := fun u => η (arcClock t₀ u)) h2 h1
    exact ContinuousAt.comp (g := mobAt x₀) (f := fun u => revChart w s (η (arcClock t₀ u)))
      (continuousAt_mobAt x₀ (sub_ne_zero_of_mem_H x₀ (hΨH u hu))) h3
  refine ⟨?_, ?_, by simp [exitArc], fun u hu => ?_, ?_⟩
  · intro u hu
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ u from hu) with h0 | h0
    · -- continuity at `0`
      subst h0
      refine continuousWithinAt_Ioi_iff_Ici.1 ?_
      have hη0 : Tendsto (fun u => η (arcClock t₀ u)) (𝓝[>] 0) (𝓝[H \ G] 0) := by
        refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
        · have hc : ContinuousWithinAt η (Ici 0) 0 := hη.cont 0 (Set.mem_Ici.2 le_rfl)
          have h0 : arcClock t₀ 0 = 0 := by simp [arcClock]
          have ha : Tendsto (arcClock t₀) (𝓝[>] 0) (𝓝[Ici 0] 0) := by
            refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
            · have := (continuous_arcClock_at (t₀ := t₀) (le_refl (0 : ℝ))).tendsto
              rw [h0] at this
              exact this.mono_left nhdsWithin_le_nhds
            · filter_upwards [self_mem_nhdsWithin] with u hu using (arcClock_pos ht₀ hu).le
          have := hc.tendsto.comp ha
          rwa [hη.zero] at this
        · filter_upwards [self_mem_nhdsWithin] with u hu using hmem u hu
      have h2 := (tendsto_revChart_zero hw hw0 hs).comp hη0
      have h3 := (continuousAt_mobAt x₀ (sub_ne_zero.2 (by simpa using hx₀))).tendsto.comp h2
      rw [mobAt_zero] at h3
      refine (h3.congr' ?_).trans (by simp [exitArc])
      filter_upwards [self_mem_nhdsWithin] with u hu
      simp only [Function.comp_apply]
      rw [exitArc_of_pos hu]
    · refine ((hcpos u h0).congr ?_).continuousWithinAt
      filter_upwards [Ioi_mem_nhds h0] with v hv
      rw [exitArc_of_pos hv]
  · intro u hu v hv e
    have hu' : (0 : ℝ) ≤ u := hu
    have hv' : (0 : ℝ) ≤ v := hv
    rcases eq_or_lt_of_le hu' with hu0 | hu0 <;> rcases eq_or_lt_of_le hv' with hv0 | hv0
    · rw [← hu0, ← hv0]
    · exfalso
      rw [← hu0, exitArc_of_pos hv0] at e
      simp only [exitArc, le_refl, ↓reduceIte] at e
      exact ne_zero_of_mem_H (mobAt_mem_H hx₀ (hΨH v hv0)) e.symm
    · exfalso
      rw [← hv0, exitArc_of_pos hu0] at e
      simp only [exitArc, le_refl, ↓reduceIte] at e
      exact ne_zero_of_mem_H (mobAt_mem_H hx₀ (hΨH u hu0)) e
    · rw [exitArc_of_pos hu0, exitArc_of_pos hv0] at e
      have e1 := congrArg (mobAt (-x₀)) e
      rw [mobAt_neg_mobAt hx₀ (sub_ne_zero_of_mem_H x₀ (hΨH u hu0)),
        mobAt_neg_mobAt hx₀ (sub_ne_zero_of_mem_H x₀ (hΨH v hv0))] at e1
      have e2 := injOn_revChart hw hw0 hs (hmem u hu0) (hmem v hv0) e1
      have e3 := hη.inj (show arcClock t₀ u ∈ Ici 0 from (arcClock_pos ht₀ hu0).le)
        (show arcClock t₀ v ∈ Ici 0 from (arcClock_pos ht₀ hv0).le) e2
      exact arcClock_injOn ht₀ hu hv e3
  · rw [exitArc_of_pos hu]
    exact mobAt_mem_H hx₀ (hΨH u hu)
  · have hg : Tendsto (fun u => revChart w s (η (arcClock t₀ u))) atTop (𝓝[≠] (x₀ : ℂ)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨hlim.comp (tendsto_arcClock_atTop ht₀), ?_⟩
      filter_upwards [eventually_gt_atTop 0] with u hu
      exact fun h => sub_ne_zero_of_mem_H x₀ (hΨH u hu) (by rw [show (x₀ : ℂ) = _ from h.symm]; ring)
    refine ((tendsto_norm_mobAt hx₀).comp hg).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with u hu
    simp only [Function.comp_apply]
    rw [exitArc_of_pos hu]

/-- **The region to the right of the exit crosscut**: the image under `Ψ⁻¹ ∘ M⁻¹` of the right side of the exit
arc `M ∘ Ψ ∘ η|[0, t₀)`. It lies in `ℍ ∖ R(K_s)`, contains the points of `ℍ ∖ R(K_s)` near the tip `η′(s)`
(`Ψ`-coordinates near `∞`), and the points near some small positive real point of the physical boundary. -/
def exitRightSet (w : ℝ → ℝ) (s t₀ x₀ : ℝ) (η : ℝ → ℂ) : Set ℂ :=
  revChartInv w s '' (mobAt (-x₀) '' rightSideOf (arcRange (exitArc w s t₀ x₀ η)))

/-- **Proposition 4.9's no-wrap step in the chart `Q`, general form** (deterministic). Let `η` be a proper arc (the
flow line), `β` a Loewner trace of the continuous driver `w` (the counterflow line `η′ = R ∘ β` in the chart `R`), and
`s ≥ 0`. Suppose `η` exits `ℍ ∖ R(K_s)` at time `t₀ > 0` on the left side of the counterflow prefix: before `t₀` it
avoids `R(K_s)`, and in the chart `Ψ = R ∘ f_s ∘ R` of `ℍ ∖ R(K_s)` it tends to a negative real point `x₀` as
`t ↑ t₀`. If after `t₀` the flow line never enters the region to the right of its exit crosscut (`exitRightSet`; it
does not wrap around the tip), then the counterflow tip `η′(s) = R(β(s))` is not on the left side of `η`. -/
theorem negInv_notMem_leftSideOf_of_exit' (hη : IsProperArc η) (hβ : IsLoewnerTrace w β) (hw : Continuous w)
    (hw0 : w 0 = 0) (hs : 0 ≤ s) (ht₀ : 0 < t₀) (hx₀ : x₀ < 0)
    (hpre : ∀ t ∈ Ioo 0 t₀, η t ∉ negInv '' fwdHull w s)
    (hlim : Tendsto (fun t => revChart w s (η t)) (𝓝[<] t₀) (𝓝 (x₀ : ℂ)))
    (hpost : ∀ t, t₀ ≤ t → η t ∉ exitRightSet w s t₀ x₀ η) :
    negInv (β s) ∉ leftSideOf (arcRange η) := by
  intro hL
  have hβs : β s ≠ 0 := fun h => by
    rw [h] at hL
    exact ne_zero_of_mem_H hL.1.1 (by simp [negInv])
  set G := negInv '' fwdHull w s with hG
  set A := arcRange η with hA
  set γ := exitArc w s t₀ x₀ η with hγdef
  have hγ : IsProperArc γ := isProperArc_exitArc hη hw hw0 hs ht₀ hx₀.ne hpre hlim
  set S := mobAt (-x₀) '' rightSideOf (arcRange γ) with hSdef
  have hx₀' : x₀ ≠ 0 := hx₀.ne
  -- `S ⊆ ℍ`, and `S` is preconnected
  have hSH : S ⊆ H := by
    rintro _ ⟨m, hm, rfl⟩
    exact mobAt_mem_H (neg_ne_zero.2 hx₀') hm.1.1
  have hSc : IsPreconnected S := by
    refine hγ.isPreconnected_rightSideOf.image _ fun m hm => ?_
    exact (continuousAt_mobAt (-x₀) (sub_ne_zero_of_mem_H (-x₀) hm.1.1)).continuousWithinAt
  -- the inverse chart maps `S` into `ℍ ∖ η`
  have hSA : revChartInv w s '' S ⊆ H \ A := by
    rintro _ ⟨ξ, hξ, rfl⟩
    obtain ⟨m, hm, rfl⟩ := hξ
    have hξH : mobAt (-x₀) m ∈ H := mobAt_mem_H (neg_ne_zero.2 hx₀') hm.1.1
    have hmem := revChartInv_mem hw hw0 hs hξH
    refine ⟨hmem.1, ?_⟩
    rintro ⟨t, ht, he⟩
    have ht' : (0 : ℝ) ≤ t := ht
    rcases eq_or_lt_of_le ht' with h0 | h0
    · rw [← h0, hη.zero] at he
      exact ne_zero_of_mem_H hmem.1 he.symm
    by_cases htt : t₀ ≤ t
    · exact hpost t htt (he ▸ ⟨_, ⟨m, hm, rfl⟩, rfl⟩)
    · push Not at htt
      have hΨ : revChart w s (η t) = mobAt (-x₀) m := by
        rw [he, revChart_revChartInv hw hw0 hs hξH]
      have hmeq : m = mobAt x₀ (revChart w s (η t)) := by
        rw [hΨ, mobAt_mobAt_neg hx₀' (fun h => ?_)]
        have := hm.1.1
        have h' : m = -(x₀ : ℂ) := by linear_combination h
        rw [h'] at this
        exact absurd this (by simp [QuantumZipper.H])
      refine hm.1.2 ⟨t / (t₀ - t), div_nonneg ht' (by linarith), ?_⟩
      rw [hmeq, hγdef, exitArc_of_pos (div_pos h0 (by linarith)), arcClock_inv ht' htt]
  have hSc' : IsPreconnected (revChartInv w s '' S) :=
    hSc.image _ ((continuousOn_revChartInv hw hw0 hs).mono hSH)
  -- the tip side: points of `S` near `∞` are mapped near the tip
  have hLopen : IsOpen (leftSideOf A) := Cond44Ref.isOpen_leftSideOf_arcRange hη
  obtain ⟨z₁, hz₁S, hz₁L⟩ : ∃ z ∈ revChartInv w s '' S, z ∈ leftSideOf A := by
    set f : ℕ → ℂ := fun n => ((n : ℝ) + 1 : ℝ) * I with hf
    have hfH : ∀ n, f n ∈ H := fun n => show (0 : ℝ) < (f n).im by simp [hf]; positivity
    have hfn : Tendsto (fun n => ‖f n‖) atTop atTop := by
      have : ∀ n, ‖f n‖ = (n : ℝ) + 1 := fun n => by
        simp only [hf, norm_mul, norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
        exact abs_of_pos (by positivity)
      simp only [this]
      exact tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    have h1 := tendsto_revChartInv_tip hβ hw hw0 hs hβs (Eventually.of_forall hfH) hfn
    have h2 : Tendsto (fun n => mobAt x₀ (f n)) atTop (𝓝[H] (((-x₀ : ℝ)) : ℂ)) :=
      tendsto_nhdsWithin_iff.2 ⟨tendsto_mobAt_cobounded hfn,
        Eventually.of_forall fun n => mobAt_mem_H hx₀' (hfH n)⟩
    have h3 := h2.eventually (eventually_mem_rightSideOf hγ (show (0 : ℝ) < -x₀ by linarith))
    have h4 := h1.eventually (hLopen.mem_nhds hL)
    obtain ⟨n, hn3, hn4⟩ := (h3.and h4).exists
    refine ⟨_, ⟨f n, ⟨mobAt x₀ (f n), hn3, mobAt_neg_mobAt hx₀' (sub_ne_zero_of_mem_H x₀ (hfH n))⟩, rfl⟩, hn4⟩
  -- hence the whole image lies on the left side of `η`
  have hSL : revChartInv w s '' S ⊆ leftSideOf A := fun z hz =>
    mem_leftSideOf_of_mem_connectedComponentIn hz₁L (hSc'.subset_connectedComponentIn hz₁S hSA hz)
  -- the boundary side: points of `S` near a far negative real are mapped near a positive real point
  obtain ⟨ω₀, y₀, hω₀, hy₀, hlimF⟩ := exists_neg_tendsto_fwdMapInv hβ hw hw0 hs
  set r₀ : ℝ := -ω₀⁻¹ with hr₀
  have hr₀pos : 0 < r₀ := by rw [hr₀]; exact neg_pos.2 (inv_lt_zero.2 hω₀)
  have hr₀c : negInv (r₀ : ℂ) = (ω₀ : ℂ) := by simp [negInv, hr₀]
  have hNe : (𝓝[H] (r₀ : ℂ)).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.1 (closure_H ▸ mem_Hbar_of_im_eq_zero (by simp))
  have hneg : Tendsto negInv (𝓝[H] (r₀ : ℂ)) (𝓝[H] (ω₀ : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have := (continuousAt_negInv (ofReal_ne_zero.2 hr₀pos.ne')).tendsto
      rw [hr₀c] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ξ hξ using negInv_mem_H hξ
  have hinv : Tendsto (revChartInv w s) (𝓝[H] (r₀ : ℂ)) (𝓝[H] (negInv (y₀ : ℂ))) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · exact (continuousAt_negInv (ofReal_ne_zero.2 hy₀.ne)).tendsto.comp (hlimF.comp hneg)
    · filter_upwards [self_mem_nhdsWithin] with ξ hξ using (revChartInv_mem hw hw0 hs hξ).1
  have hy₀c : negInv (y₀ : ℂ) = ((-y₀⁻¹ : ℝ) : ℂ) := by simp [negInv]
  rw [hy₀c] at hinv
  have hR := hinv.eventually (eventually_mem_rightSideOf hη (show (0 : ℝ) < -y₀⁻¹ from
    neg_pos.2 (inv_lt_zero.2 hy₀)))
  set m₀ : ℝ := x₀ * r₀ / (x₀ - r₀) with hm₀
  have hm₀pos : 0 < m₀ := div_pos_of_neg_of_neg (mul_neg_of_neg_of_pos hx₀ hr₀pos) (by linarith)
  have hmob : Tendsto (mobAt x₀) (𝓝[H] (r₀ : ℂ)) (𝓝[H] (m₀ : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have h1 := (continuousAt_mobAt x₀ (z := (r₀ : ℂ)) (by
        rw [← ofReal_sub]; exact ofReal_ne_zero.2 (by linarith))).tendsto
      have h2 : mobAt x₀ (r₀ : ℂ) = (m₀ : ℂ) := by simp [mobAt, hm₀]
      rw [h2] at h1
      exact h1.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ξ hξ using mobAt_mem_H hx₀' hξ
  have hS := hmob.eventually (eventually_mem_rightSideOf hγ hm₀pos)
  obtain ⟨ξ, hξR, hξS, hξH⟩ := (hR.and (hS.and self_mem_nhdsWithin)).exists
  have hξS' : ξ ∈ S := ⟨mobAt x₀ ξ, hξS, mobAt_neg_mobAt hx₀' (sub_ne_zero_of_mem_H x₀ hξH)⟩
  exact Set.disjoint_left.1 hη.disjoint_leftSideOf_rightSideOf (hSL ⟨ξ, hξS', rfl⟩) hξR

/-- **Proposition 4.9's no-wrap step in the chart `Q`** (deterministic). As `negInv_notMem_leftSideOf_of_exit'`, with
the no-wrap hypothesis supplied by Lemma 4.7's reverse chronological order: `η` stays in `R(K_s)` from `t₀` on
(`Prop411QOrder.mem_negInv_fwdHull_of_isFirstHitQ`). Then the counterflow tip `η′(s) = R(β(s))` is not on the left
side of `η`. -/
theorem negInv_notMem_leftSideOf_of_exit (hη : IsProperArc η) (hβ : IsLoewnerTrace w β) (hw : Continuous w)
    (hw0 : w 0 = 0) (hs : 0 ≤ s) (ht₀ : 0 < t₀) (hx₀ : x₀ < 0)
    (hpre : ∀ t ∈ Ioo 0 t₀, η t ∉ negInv '' fwdHull w s)
    (hlim : Tendsto (fun t => revChart w s (η t)) (𝓝[<] t₀) (𝓝 (x₀ : ℂ)))
    (hpost : ∀ t, t₀ ≤ t → η t ∈ negInv '' fwdHull w s) :
    negInv (β s) ∉ leftSideOf (arcRange η) := by
  refine negInv_notMem_leftSideOf_of_exit' hη hβ hw hw0 hs ht₀ hx₀ hpre hlim fun t ht hmem => ?_
  obtain ⟨ξ, hξ, e⟩ := hmem
  obtain ⟨m, hm, rfl⟩ := hξ
  have hξH : mobAt (-x₀) m ∈ H := mobAt_mem_H (neg_ne_zero.2 hx₀.ne) hm.1.1
  exact (revChartInv_mem hw hw0 hs hξH).2 (e ▸ hpost t ht)

end NoWrap

end InteractingSLE.Sec5.Prop411Q
