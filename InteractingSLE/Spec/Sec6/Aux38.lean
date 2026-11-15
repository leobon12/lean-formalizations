/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Foundations.Loewner.YuanSimpleApproxTrans

/-!
# Aux. lemma 38: no change of side through a strict old arc

Specification §6.2, **Aux.** lemma 38 (`source/spec/p193-240.md` L138–L142, p. 200):

> Let `γ` be a continuous Loewner trace with its own continuous mapping-out continuation. Suppose a
> compact simple arc `J` is contained in its range by time `r`, and `p` is an interior point of `J`.
> Choose a Jordan neighborhood `U` in which `J` is a diameter and has two local sides. At a later
> visit to `p`, the trace cannot approach from one of those sides and depart through the other.
> More precisely, on some time neighborhood of that visit the trace stays in the closure of one of
> these sides within `U`.

The local sides of `J` in `U` are the connected components of `U \ J`. The proof of the source
(the own-mapped future `δ = g_r ∘ γ` is continuous by [Yua22, Corollary 1.3]; a small upper
half-disc about `δ(t)` maps into `U` and avoids the old range, so its connected image lies in one
side) uses neither that `J` is an arc, nor that `p` is interior to `J`, nor that `U \ J` has exactly
two components: only that `J` lies in the range by time `r`, that `U` is open, and that the visit
is at a time `t > r`. The theorem below is stated in this generality; with `J` the arc and `U` the
Jordan neighborhood of the source it is exactly Aux. lemma 38.

## Main results

* `traceMapOut_trMap_zero`: the own-mapped future: `f̄_r(δ_r(t)) = γ(t)` for `0 ≤ r ≤ t`, where
  `f̄_r = trMap W 0 r` is the continuously extended inverse map at time `r` and
  `δ_r(t) = trMap W r t 0` the continuous own-mapped future (centred at `W_r`);
* `trMap_zero_image_H_disjoint`: `f̄_r(ℍ)` avoids the range by time `r`;
* `aux38_exists_side`: **Aux. lemma 38**.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology

open QuantumZipper (H Hbar fwdHull fwdMapInv)
open QuantumZipper.RS (shiftDrive)
open InteractingSLE.YuanSimpleApprox (trMap)

namespace InteractingSLE.Sec6

variable {W : ℝ → ℝ} {η : ℝ → ℂ}

/-- **The own-mapped future lies over the trace.** For a continuous Loewner trace and
`0 ≤ r ≤ t`, the continuously extended inverse map at time `r` sends the own-mapped future
`δ_r(t) = trMap W r t 0` to `η(t)`. -/
theorem traceMapOut_trMap_zero (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    {r t : ℝ} (hr : 0 ≤ r) (hrt : r ≤ t) : trMap W 0 r (trMap W r t 0) = η t := by
  rw [YuanSimpleApprox.trMap_trMap hη hW hW0 le_rfl hr hrt zero_mem_Hbar,
    YuanSimpleApprox.trMap_zero, YuanSimpleApprox.shiftDrive_zero_eq hW0, sub_zero,
    hη.loewnerTip_eq hW hW0 (hr.trans hrt)]

/-- **The open active domain avoids the old range.** `f̄_r(ℍ) ⊆ ℍ \ K_r` does not meet
`η([0, r])`. -/
theorem trMap_zero_image_H_disjoint (hη : IsLoewnerTrace W η) (hW : Continuous W)
    (hW0 : W 0 = 0) {r : ℝ} (hr : 0 ≤ r) : Disjoint (trMap W 0 r '' H) (η '' Icc 0 r) := by
  rw [Set.disjoint_left]
  intro x hx hxr
  have hx' := YuanSimpleApprox.trMap_image_subset hW hr hx
  rw [YuanSimpleApprox.shiftDrive_zero_eq hW0, sub_zero, hη.2.2 r hr] at hx'
  exact hx'.2 ⟨hx'.1, Or.inl (subset_closure hxr)⟩

/-- Points of `ℍ̄` close to `v` are limits of points of `ball v ρ ∩ ℍ`. -/
theorem mem_closure_ball_inter_H {v w : ℂ} {ρ : ℝ} (hw : w ∈ Hbar) (hwv : w ∈ ball v ρ) :
    w ∈ closure (ball v ρ ∩ H) := by
  have hc : Tendsto (fun s : ℝ => w + (s : ℂ) * I) (𝓝[>] 0) (𝓝 w) := by
    have : Continuous fun s : ℝ => w + (s : ℂ) * I := by fun_prop
    have h := this.tendsto 0
    simp only [ofReal_zero, zero_mul, add_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto hc ?_
  have hball : ∀ᶠ s : ℝ in 𝓝[>] 0, w + (s : ℂ) * I ∈ ball v ρ :=
    hc.eventually (isOpen_ball.mem_nhds hwv)
  filter_upwards [hball, self_mem_nhdsWithin] with s hs hs0
  refine ⟨hs, ?_⟩
  show 0 < (w + (s : ℂ) * I).im
  have hw' : 0 ≤ w.im := hw
  have hs0' : (0 : ℝ) < s := hs0
  simp only [add_im, mul_im, ofReal_re, I_im, ofReal_im, I_re, mul_zero, add_zero, mul_one]
  linarith

/-- **Aux. lemma 38** (no change of side through a strict old arc). Let `η` be a continuous
Loewner trace of a continuous driver `W` with `W 0 = 0` (its own continuous mapping-out
continuation is [Yua22, Corollary 1.3]). Let `J ⊆ η([0, r])` and let `U` be an open set containing
the point `η(t)` visited at a later time `t > r`. Then there are `ε > 0` and a local side of `J` in
`U` — a connected component of `U \ J` — such that on the time neighborhood `(t - ε, t + ε)` the
trace stays in `U` and in the closure of that side. -/
theorem aux38_exists_side (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    {J U : Set ℂ} {r t : ℝ} (hr : 0 ≤ r) (hrt : r < t) (hJ : J ⊆ η '' Icc 0 r) (hU : IsOpen U)
    (htU : η t ∈ U) :
    ∃ ε > 0, ∃ z ∈ U \ J, ∀ t' ∈ Ioo (t - ε) (t + ε),
      η t' ∈ U ∧ η t' ∈ closure (connectedComponentIn (U \ J) z) := by
  set f := trMap W 0 r with hf
  set δ : ℝ → ℂ := fun t' => trMap W r t' 0 with hδ
  have hfc : ContinuousOn f Hbar := YuanSimpleApprox.trMap_continuousOn hη hW hW0 le_rfl hr
  have hδc : ContinuousOn δ (Ici r) := YuanSimpleApprox.continuousOn_trMap_zero hη hW hW0 hr
  have hδH : ∀ t' ∈ Ici r, δ t' ∈ Hbar := fun t' ht' =>
    YuanSimpleApprox.trMap_zero_mem_Hbar hη hW hW0 hr ht'
  have hfδ : ∀ t' ∈ Ici r, f (δ t') = η t' := fun t' ht' =>
    traceMapOut_trMap_zero hη hW hW0 hr ht'
  set v := δ t with hv
  have hvH : v ∈ Hbar := hδH t hrt.le
  -- a ball about `v` whose closed part in `ℍ̄` maps into `U`
  have hfv : f v ∈ U := by rw [hfδ t hrt.le]; exact htU
  obtain ⟨ρ, hρ, hρU⟩ : ∃ ρ > 0, ∀ w ∈ Hbar, dist w v < ρ → f w ∈ U :=
    Metric.continuousWithinAt_iff.1 (hfc v hvH) |> fun h => by
      obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU (f v) hfv
      obtain ⟨ρ, hρ, hρε⟩ := h ε hε
      exact ⟨ρ, hρ, fun w hw hwv => hεU (hρε hw hwv)⟩
  set B := ball v ρ ∩ H with hB
  have hBH : B ⊆ H := inter_subset_right
  have hBne : (v + ((ρ / 2 : ℝ) : ℂ) * I) ∈ B := by
    refine ⟨?_, ?_⟩
    · rw [mem_ball, dist_eq, add_sub_cancel_left, norm_mul, norm_I, mul_one, norm_real,
        Real.norm_eq_abs, abs_of_pos (half_pos hρ)]
      exact half_lt_self hρ
    · show 0 < (v + ((ρ / 2 : ℝ) : ℂ) * I).im
      have hv' : 0 ≤ v.im := hvH
      simp only [add_im, mul_im, ofReal_re, I_im, ofReal_im, I_re, mul_zero, add_zero, mul_one]
      linarith
  have hBc : IsPreconnected B := ((convex_ball v ρ).inter convex_H).isPreconnected
  have hHHbar : H ⊆ Hbar := H_subset_Hbar
  -- the image of `B` is a preconnected subset of `U \ J`
  have hfB : f '' B ⊆ U \ J := by
    rintro _ ⟨w, hw, rfl⟩
    refine ⟨hρU w (hHHbar (hBH hw)) (mem_ball.1 hw.1), fun hwJ => ?_⟩
    exact Set.disjoint_left.1 (trMap_zero_image_H_disjoint hη hW hW0 hr) ⟨w, hBH hw, rfl⟩
      (hJ hwJ)
  have hfBc : IsPreconnected (f '' B) :=
    hBc.image f ((hfc.mono hHHbar).mono hBH)
  set z := f (v + ((ρ / 2 : ℝ) : ℂ) * I) with hz
  have hzB : z ∈ f '' B := ⟨_, hBne, rfl⟩
  have hfBsub : f '' B ⊆ connectedComponentIn (U \ J) z :=
    hfBc.subset_connectedComponentIn hzB hfB
  -- continuity of the own-mapped future at `t`
  have hδt : ContinuousAt δ t := hδc.continuousAt (Ici_mem_nhds hrt)
  obtain ⟨ε₀, hε₀, hε₀δ⟩ := Metric.continuousAt_iff.1 hδt ρ hρ
  refine ⟨min ε₀ (t - r), lt_min hε₀ (sub_pos.2 hrt), z, hfB hzB, fun t' ht' => ?_⟩
  have ht'r : t' ∈ Ici r := by
    have := ht'.1
    have h2 : min ε₀ (t - r) ≤ t - r := min_le_right _ _
    show r ≤ t'
    linarith
  have hdist : dist t' t < ε₀ := by
    rw [Real.dist_eq, abs_lt]
    have h1 : min ε₀ (t - r) ≤ ε₀ := min_le_left _ _
    constructor <;> linarith [ht'.1, ht'.2]
  have hδball : δ t' ∈ ball v ρ := hε₀δ hdist
  have hδt'H := hδH t' ht'r
  refine ⟨?_, ?_⟩
  · rw [← hfδ t' ht'r]; exact hρU _ hδt'H hδball
  · rw [← hfδ t' ht'r]
    have hcl : δ t' ∈ closure B := mem_closure_ball_inter_H hδt'H hδball
    have hclH : closure B ⊆ Hbar := by
      rw [← closure_H]; exact closure_mono hBH
    have h1 : f (δ t') ∈ closure (f '' B) :=
      (hfc.mono hclH).image_closure ⟨_, hcl, rfl⟩
    exact closure_mono hfBsub h1

end InteractingSLE.Sec6
