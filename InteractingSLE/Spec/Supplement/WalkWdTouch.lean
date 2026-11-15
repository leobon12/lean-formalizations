/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2GFibre

/-!
# A real limit of a transition at a landing on any boundary point, from the fibre lemma

Packet PROVE-WALK-WORDS2, toward `WalkTouchMatchStatement` (prefix matches at the real touch points of the pieces).
PROVE-WALK-WORDS' `exists_transition_extension` gets the limit of the transition `T = c'.fwd ∘ c.inv` at a real point
`x₀` from a landing on a trace point **in ℍ** (where the launch chart is analytic). At a real touch point the landings
near `x₀` may themselves be real touch points, so that route is unavailable. Here the limit comes from cluster sets
alone:

* **`exists_tendsto_real_of_fibre`** (generic): let `T` be continuous and bounded on a half-disc `ℍ ∩ B(x₀, δ₀)` with
  values in `ℍ`, and `F` continuous on `ℍ̄` with `F(T w) → q`, where `q ∉ F(ℍ)`, `F(0) ≠ q`, and two real preimages of
  `q` on one side of `0` coincide. Then `T(w)` tends to a nonzero real `y` with `F(y) = q`.

Proof: every cluster point `ξ` of `T` lies in `ℍ̄` (values in `ℍ`), has `F(ξ) = q` (continuity), hence is real
(`q ∉ F(ℍ)`) and nonzero. If there were cluster points on both sides of `0`, every half-disc would contain points
where `Re T` is negative and positive, hence (connected half-disc, intermediate values) a point where `Re T = 0`; these
points have a cluster point with real part `0`, which is real and nonzero — impossible. So all cluster points have one
sign and coincide by the fibre hypothesis; a bounded map with a unique cluster point converges.

For a Loewner trace, `F = F̄_τ` (the extended inverse map) satisfies the fibre hypothesis at **every** trace point,
real or not (`SB.FinRel.eq_of_extendFrom_eq_of_same_side_gen`); `exists_tendsto_real_of_fibre_loewner` packages it.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Set Topology Complex Metric
open QuantumZipper (H Hbar fwdMapInv)

namespace InteractingSLE.Theorem14.WalkWd

/-- **A real limit from the fibre** (see the module docstring). -/
theorem exists_tendsto_real_of_fibre {T F : ℂ → ℂ} {x₀ q : ℂ} {δ₀ M : ℝ} (hδ₀ : 0 < δ₀) (hx₀ : x₀ ∈ Hbar)
    (hTc : ContinuousOn T (H ∩ ball x₀ δ₀)) (hTH : MapsTo T (H ∩ ball x₀ δ₀) H)
    (hTb : ∀ w ∈ H ∩ ball x₀ δ₀, ‖T w‖ ≤ M) (hFc : ContinuousOn F Hbar)
    (hFT : Tendsto (fun w => F (T w)) (𝓝[H] x₀) (𝓝 q)) (hq : ∀ z ∈ H, F z ≠ q) (hq0 : F 0 ≠ q)
    (hfib : ∀ y₁ y₂ : ℝ, 0 < y₁ * y₂ → F y₁ = q → F y₂ = q → y₁ = y₂) :
    ∃ y : ℝ, y ≠ 0 ∧ F y = q ∧ Tendsto T (𝓝[H] x₀) (𝓝 (y : ℂ)) := by
  have : (𝓝[H] x₀).NeBot := GW1P.neBot_nhdsWithin_H hx₀
  have hev : ∀ᶠ w in 𝓝[H] x₀, w ∈ H ∩ ball x₀ δ₀ := inter_mem_nhdsWithin H (ball_mem_nhds x₀ hδ₀)
  have hK : IsCompact (closedBall (0 : ℂ) M) := isCompact_closedBall 0 M
  have hTK : ∀ᶠ w in 𝓝[H] x₀, T w ∈ closedBall (0 : ℂ) M :=
    hev.mono fun w hw => mem_closedBall_zero_iff.2 (hTb w hw)
  have hTH' : ∀ᶠ w in 𝓝[H] x₀, T w ∈ H := hev.mono fun w hw => hTH hw
  -- every cluster point is a nonzero real preimage of `q`
  have hclu : ∀ ξ : ℂ, MapClusterPt ξ (𝓝[H] x₀) T → ξ.im = 0 ∧ ξ ≠ 0 ∧ F ξ = q := by
    intro ξ hξ
    have hξH : ξ ∈ Hbar := by
      by_contra hn
      obtain ⟨w, hw1, hw2⟩ := (hξ.frequently (QuantumZipper.isClosed_Hbar.isOpen_compl.mem_nhds hn)).and_eventually
        hTH' |>.exists
      exact hw1 (le_of_lt (show (0 : ℝ) < (T w).im from hw2))
    have hFξ : F ξ = q := by
      by_contra hne
      set r : ℝ := dist (F ξ) q / 2 with hr
      have hr0 : 0 < r := by rw [hr]; exact half_pos (dist_pos.2 hne)
      obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.1 ((hFc ξ hξH).preimage_mem_nhdsWithin (ball_mem_nhds _ hr0))
      have hfr := hξ.frequently (ball_mem_nhds ξ hε)
      obtain ⟨w, hw1, hw2, hw3⟩ := (hfr.and_eventually (hTH'.and (hFT.eventually (ball_mem_nhds q hr0)))).exists
      have h1 : F (T w) ∈ ball (F ξ) r := hball ⟨hw1, le_of_lt (show (0 : ℝ) < (T w).im from hw2)⟩
      have h2 := dist_triangle (F ξ) (F (T w)) q
      have hw3' : dist (F (T w)) q < r := hw3
      rw [mem_ball, dist_comm] at h1
      linarith
    have hξim : ξ.im = 0 := le_antisymm (not_lt.1 fun h => hq ξ h hFξ) hξH
    exact ⟨hξim, fun h0 => hq0 (h0 ▸ hFξ), hFξ⟩
  -- no two cluster points on opposite sides
  have hside : ∀ ξ₁ ξ₂ : ℂ, MapClusterPt ξ₁ (𝓝[H] x₀) T → MapClusterPt ξ₂ (𝓝[H] x₀) T →
      ξ₁.re < 0 → 0 < ξ₂.re → False := by
    intro ξ₁ ξ₂ h₁ h₂ hr₁ hr₂
    have hfreq : ∃ᶠ w in 𝓝[H] x₀, T w ∈ {ζ : ℂ | ζ.re = 0} ∩ closedBall (0 : ℂ) M := by
      rw [Filter.frequently_iff]
      intro U hU
      obtain ⟨δ, hδ, hδU⟩ := Metric.mem_nhdsWithin_iff.1 hU
      set S : Set ℂ := H ∩ ball x₀ (min δ δ₀) with hS
      have hSn : S ∈ 𝓝[H] x₀ := inter_mem_nhdsWithin H (ball_mem_nhds x₀ (lt_min hδ hδ₀))
      have hSsub : S ⊆ H ∩ ball x₀ δ₀ := fun w hw => ⟨hw.1, ball_subset_ball (min_le_right _ _) hw.2⟩
      have hSp : IsPreconnected S :=
        ((convex_halfSpace_gt Complex.imLm.isLinear 0).inter (convex_ball x₀ _)).isPreconnected
      have hf₁ : ∃ᶠ w in 𝓝[H] x₀, (T w).re < 0 :=
        h₁.frequently ((isOpen_lt Complex.continuous_re continuous_const).mem_nhds hr₁)
      have hf₂ : ∃ᶠ w in 𝓝[H] x₀, 0 < (T w).re :=
        h₂.frequently ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hr₂)
      obtain ⟨w₁, hw₁, hw₁S⟩ := (hf₁.and_eventually hSn).exists
      obtain ⟨w₂, hw₂, hw₂S⟩ := (hf₂.and_eventually hSn).exists
      have hcont : ContinuousOn (fun w => (T w).re) S := Complex.continuous_re.comp_continuousOn (hTc.mono hSsub)
      obtain ⟨w, hwS, hw0⟩ := hSp.intermediate_value hw₁S hw₂S hcont ⟨le_of_lt hw₁, le_of_lt hw₂⟩
      refine ⟨w, hδU ⟨ball_subset_ball (min_le_left _ _) hwS.2, hwS.1⟩, hw0, ?_⟩
      exact mem_closedBall_zero_iff.2 (hTb w (hSsub hwS))
    have hK₀ : IsCompact ({ζ : ℂ | ζ.re = 0} ∩ closedBall (0 : ℂ) M) :=
      hK.of_isClosed_subset ((isClosed_eq Complex.continuous_re continuous_const).inter isClosed_closedBall)
        inter_subset_right
    obtain ⟨ζ, hζ, hζc⟩ := hK₀.exists_mapClusterPt_of_frequently hfreq
    obtain ⟨hζim, hζ0, -⟩ := hclu ζ hζc
    exact hζ0 (Complex.ext hζ.1 hζim)
  -- the unique cluster point
  obtain ⟨ξ₀, -, hξ₀⟩ := hK.exists_mapClusterPt_of_frequently hTK.frequently
  obtain ⟨h0im, h00, hF0⟩ := hclu ξ₀ hξ₀
  have hreal : ∀ ξ : ℂ, ξ.im = 0 → ((ξ.re : ℝ) : ℂ) = ξ := fun ξ h => Complex.ext (by simp) (by simp [h])
  have huniq : ∀ ξ : ℂ, MapClusterPt ξ (𝓝[H] x₀) T → ξ = ξ₀ := by
    intro ξ hξ
    obtain ⟨him, h0, hF⟩ := hclu ξ hξ
    have hre0 : ξ.re ≠ 0 := fun h => h0 (Complex.ext h him)
    have hre0' : ξ₀.re ≠ 0 := fun h => h00 (Complex.ext h h0im)
    have hsame : 0 < ξ.re * ξ₀.re := by
      rcases lt_or_gt_of_ne hre0 with h1 | h1 <;> rcases lt_or_gt_of_ne hre0' with h2 | h2
      · exact mul_pos_of_neg_of_neg h1 h2
      · exact (hside ξ ξ₀ hξ hξ₀ h1 h2).elim
      · exact (hside ξ₀ ξ hξ₀ hξ h2 h1).elim
      · exact mul_pos h1 h2
    have := hfib ξ.re ξ₀.re hsame (by rw [hreal ξ him]; exact hF) (by rw [hreal ξ₀ h0im]; exact hF0)
    rw [← hreal ξ him, ← hreal ξ₀ h0im, this]
  refine ⟨ξ₀.re, fun h => h00 (Complex.ext h h0im), by rw [hreal ξ₀ h0im]; exact hF0, ?_⟩
  rw [hreal ξ₀ h0im]
  exact hK.tendsto_nhds_of_unique_mapClusterPt hTK fun ξ _ hξ => huniq ξ hξ

/-- **The Loewner form**: a map `T` from a half-disc at `x₀ ∈ ℍ̄` into `ℍ`, continuous and bounded, with
`F̄_τ(T w) → η(s)` (`s < τ`, `η` injective on `[0, τ]`), tends to a nonzero real preimage of the trace point `η(s)` —
real or not. -/
theorem exists_tendsto_real_of_fibre_loewner {W : ℝ → ℝ} {η : ℝ → ℂ} (hη : IsLoewnerTrace W η)
    (hW : Continuous W) (hW0 : W 0 = 0) {s τ : ℝ} (hs : 0 ≤ s) (hsτ : s < τ) (hinj : InjOn η (Icc 0 τ))
    {T : ℂ → ℂ} {x₀ : ℂ} {δ₀ M : ℝ} (hδ₀ : 0 < δ₀) (hx₀ : x₀ ∈ Hbar)
    (hTc : ContinuousOn T (H ∩ ball x₀ δ₀)) (hTH : MapsTo T (H ∩ ball x₀ δ₀) H)
    (hTb : ∀ w ∈ H ∩ ball x₀ δ₀, ‖T w‖ ≤ M)
    (hFT : Tendsto (fun w => extendFrom H (fwdMapInv W τ) (T w)) (𝓝[H] x₀) (𝓝 (η s))) :
    ∃ y : ℝ, y ≠ 0 ∧ extendFrom H (fwdMapInv W τ) y = η s ∧ Tendsto T (𝓝[H] x₀) (𝓝 (y : ℂ)) := by
  have hτ0 : 0 ≤ τ := hs.trans hsτ.le
  refine exists_tendsto_real_of_fibre hδ₀ hx₀ hTc hTH hTb (hη.hasBdryLimits hW hW0 hτ0).continuousOn hFT
    (fun z hz he => WalkWords.trace_notMem_image_H hη hW hW0 hτ0 ⟨hs, hsτ.le⟩ ⟨z, hz, he⟩) ?_
    (fun y₁ y₂ h h₁ h₂ => SB.FinRel.eq_of_extendFrom_eq_of_same_side_gen hη hW hW0 hs hsτ hinj h h₁ h₂)
  rw [ZhanGT4.extendFrom_zero_eq hη hW hW0 hτ0]
  exact fun he => (ne_of_lt hsτ).symm (hinj ⟨hτ0, le_rfl⟩ ⟨hs, hsτ.le⟩ he)

end InteractingSLE.Theorem14.WalkWd
