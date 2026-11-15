/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Aux37FrameChart

/-!
# Aux. lemma 37's witness frame: the pocket collar is not swallowed and its component is unchanged

Packet PROVE-STRIPSYS40, frame field (F4). Specification §6.2, Aux. lemma 37's proof (`source/spec/p193-240.md`
L104–L120, pp. 198–199): "The compact arc `J` ... never loses its incident `C`-side collar to new range, because the new
range avoids `C`. This collar lies in the unchanged central component".

* **`collar_of_band`** (abstract, flow chart): a band of a conformal chart of a pocket `P` along an arc whose points
  avoid the hull `A_r`, touching a point off the hull `A_s`, gives an approach from the pocket inside one component of
  `ℍ ∖ (A_s ∪ walls)` equal to its component of `ℍ ∖ (A_r ∪ walls)`, provided every preconnected subset of `P ∖ A_r`
  meeting `ℍ ∖ A_s` misses `A_s` and components of `ℍ ∖ (A_r ∪ walls)` stay in `P`.
* `exists_bracket`: a continuous injective real function on `[σ₁, σ₂]` has its values at interior points strictly
  inside the image interval.

No Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement`, `*_of_param` (R43, R48).
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter Topology Function Complex
open QuantumZipper (H Hbar)
open InteractingSLE.WangWu (negInv)
open scoped NNReal Real

namespace InteractingSLE.Sec7.Aux37Frame

/-! ### The image interval of a continuous injective function -/

section Bracket

/-- A continuous injective `f` on `[σ₁, σ₂]` maps an interior point strictly inside an interval `[a, b]` of values
that `f` attains on `[σ₁, σ₂]`, with `f σ₁ ∈ [a, b]`. -/
theorem exists_bracket {f : ℝ → ℝ} {σ₁ σ₀ σ₂ : ℝ} (h10 : σ₁ < σ₀) (h02 : σ₀ < σ₂)
    (hfc : ContinuousOn f (Icc σ₁ σ₂)) (hfi : InjOn f (Icc σ₁ σ₂)) :
    ∃ a b : ℝ, a < f σ₀ ∧ f σ₀ < b ∧ f σ₁ ∈ Icc a b ∧ Icc a b ⊆ f '' Icc σ₁ σ₂ := by
  have h12 : σ₁ ≤ σ₂ := (h10.trans h02).le
  have m1 : σ₁ ∈ Icc σ₁ σ₂ := ⟨le_rfl, h12⟩
  have m0 : σ₀ ∈ Icc σ₁ σ₂ := ⟨h10.le, h02.le⟩
  have m2 : σ₂ ∈ Icc σ₁ σ₂ := ⟨h12, le_rfl⟩
  rcases hfc.strictMonoOn_of_injOn_Icc' h12 hfi with hm | hm
  · refine ⟨f σ₁, f σ₂, hm m1 m0 h10, hm m0 m2 h02, ⟨le_rfl, (hm m1 m2 (h10.trans h02)).le⟩, ?_⟩
    rw [hfc.image_Icc_of_monotoneOn h12 hm.monotoneOn]
  · refine ⟨f σ₂, f σ₁, hm m0 m2 h02, hm m1 m0 h10, ⟨(hm m1 m2 (h10.trans h02)).le, le_rfl⟩, ?_⟩
    rw [hfc.image_Icc_of_antitoneOn h12 hm.antitoneOn]

end Bracket

/-! ### The collar from a band -/

section Collar

/-- **The pocket collar along an arc is not swallowed and its component is unchanged** (abstract form, flow chart).
`c` is a conformal chart of the pocket `P` (its inverse maps `ℍ` into `P`), `f σ` the chart value of the arc point
`p σ` (`σ ∈ [σ₁, σ₂]`, `f` continuous and injective, the inverse landing at `p σ`); the arc avoids `A_r` and its first
point avoids `A_s ⊇ A_r`. If every preconnected subset of `P ∖ A_r` that meets `ℍ ∖ A_s` misses `A_s` (no new hull in
the avoided pocket), and components of `ℍ ∖ (A_r ∪ W)` from `P` stay in `P`, then the chart approach at `f σ₀`
(`σ₁ < σ₀ < σ₂`) comes from `ℍ ∖ (A_s ∪ W)`, inside one component of it that is also a component of
`ℍ ∖ (A_r ∪ W)`. -/
theorem collar_of_band {c : Chart} (hc : c.IsConformal) {P Wu Ar As : Set ℂ} (hcP : MapsTo c.2.1 H P)
    (hPW : Disjoint P Wu) (hArs : Ar ⊆ As) (hOr : IsOpen (H \ Ar)) (hOs : IsOpen (H \ As))
    (hcomp : ∀ z ∈ P, connectedComponentIn (H \ (Ar ∪ Wu)) z ⊆ P)
    (htrans : ∀ S : Set ℂ, IsPreconnected S → S ⊆ P \ Ar → (S \ As).Nonempty → Disjoint S As)
    {f : ℝ → ℝ} {p : ℝ → ℂ} {σ₁ σ₀ σ₂ : ℝ} (h10 : σ₁ < σ₀) (h02 : σ₀ < σ₂)
    (hfc : ContinuousOn f (Icc σ₁ σ₂)) (hfi : InjOn f (Icc σ₁ σ₂))
    (hlim : ∀ σ ∈ Icc σ₁ σ₂, Tendsto c.2.1 (𝓝[H] (f σ : ℂ)) (𝓝 (p σ)))
    (hpr : ∀ σ ∈ Icc σ₁ σ₂, p σ ∈ H \ Ar) (hps : p σ₁ ∈ H \ As) :
    (∀ᶠ w in map c.2.1 (𝓝[H] (f σ₀ : ℂ)), w ∈ H \ (As ∪ Wu)) ∧
      ∃ z ∈ H \ (As ∪ Wu), connectedComponentIn (H \ (As ∪ Wu)) z = connectedComponentIn (H \ (Ar ∪ Wu)) z ∧
        ∀ᶠ w in map c.2.1 (𝓝[H] (f σ₀ : ℂ)), w ∈ connectedComponentIn (H \ (As ∪ Wu)) z := by
  obtain ⟨a, b, ha, hb, h1ab, hab⟩ := exists_bracket h10 h02 hfc hfi
  -- the band
  obtain ⟨δ, hδ, hband⟩ := exists_band (c := c) isCompact_Icc hOr fun q hq => by
    obtain ⟨σ, hσ, rfl⟩ := hab hq
    exact ⟨p σ, hpr σ hσ, hlim σ hσ⟩
  set S : Set ℂ := {w : ℂ | w ∈ H ∧ w.re ∈ Icc a b ∧ w.im < δ} with hS
  set B : Set ℂ := c.2.1 '' S with hB
  have hSH : S ⊆ H := fun w hw => hw.1
  have hcont : ContinuousOn c.2.1 H := hc.1.continuousOn
  have hBpc : IsPreconnected B := ((convex_band a b δ).isPreconnected).image _ (hcont.mono hSH)
  have hBr : B ⊆ P \ Ar := by
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨hcP hw.1, (hband w hw.1 hw.2.1 hw.2.2).2⟩
  have hBH : B ⊆ H := by rintro _ ⟨w, hw, rfl⟩; exact hc.2.1 hw.1
  -- the band meets `ℍ ∖ A_s` near the first arc point
  have hBs : (B \ As).Nonempty := by
    have hm : c.2.1 ⁻¹' (H \ As) ∈ 𝓝[H] (f σ₁ : ℂ) :=
      hlim σ₁ ⟨le_rfl, (h10.trans h02).le⟩ (hOs.mem_nhds hps)
    obtain ⟨ρ, hρ, hρs⟩ := Metric.mem_nhdsWithin_iff.1 hm
    set t : ℝ := min ρ δ / 2 with ht
    have ht0 : 0 < t := by positivity
    have htρ : t < ρ := by have := min_le_left ρ δ; linarith
    have htδ : t < δ := by have := min_le_right ρ δ; linarith
    set w : ℂ := (f σ₁ : ℂ) + (t : ℂ) * I with hw
    have hwre : w.re = f σ₁ := by simp [hw]
    have hwim : w.im = t := by simp [hw]
    have hwH : w ∈ H := show (0 : ℝ) < w.im by rw [hwim]; exact ht0
    have hwball : w ∈ ball (f σ₁ : ℂ) ρ := by
      rw [mem_ball, dist_eq, show w - (f σ₁ : ℂ) = (t : ℂ) * I by rw [hw]; ring, norm_mul,
        Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
      exact htρ
    exact ⟨c.2.1 w, ⟨w, ⟨hwH, by rw [hwre]; exact h1ab, by rw [hwim]; exact htδ⟩, rfl⟩,
      (hρs ⟨hwball, hwH⟩).2⟩
  have hBdis : Disjoint B As := htrans B hBpc hBr hBs
  have hBE : B ⊆ H \ (As ∪ Wu) := fun z hz =>
    ⟨hBH hz, fun h => h.elim (fun h' => Set.disjoint_left.1 hBdis hz h')
      (fun h' => Set.disjoint_left.1 hPW (hBr hz).1 h')⟩
  -- the chart approach at `f σ₀` is eventually in the band
  have hev : ∀ᶠ w in 𝓝[H] (f σ₀ : ℂ), w ∈ S := by
    have hpos : 0 < min (min (f σ₀ - a) (b - f σ₀)) δ := lt_min (lt_min (by linarith) (by linarith)) hδ
    filter_upwards [inter_mem_nhdsWithin H (ball_mem_nhds _ hpos), self_mem_nhdsWithin] with w hw hwH
    have hd : dist w (f σ₀ : ℂ) < min (min (f σ₀ - a) (b - f σ₀)) δ := hw.2
    have hre : |w.re - f σ₀| < min (min (f σ₀ - a) (b - f σ₀)) δ := by
      have := Complex.abs_re_le_norm (w - (f σ₀ : ℂ))
      rw [sub_re, ofReal_re] at this
      rw [dist_eq] at hd
      exact this.trans_lt hd
    have him : |w.im| < min (min (f σ₀ - a) (b - f σ₀)) δ := by
      have := Complex.abs_im_le_norm (w - (f σ₀ : ℂ))
      rw [sub_im, ofReal_im, sub_zero] at this
      rw [dist_eq] at hd
      exact this.trans_lt hd
    rw [abs_lt] at hre him
    have e1 := min_le_left (min (f σ₀ - a) (b - f σ₀)) δ
    have e2 := min_le_right (min (f σ₀ - a) (b - f σ₀)) δ
    have e3 := min_le_left (f σ₀ - a) (b - f σ₀)
    have e4 := min_le_right (f σ₀ - a) (b - f σ₀)
    exact ⟨hwH, ⟨by linarith, by linarith⟩, by linarith⟩
  have hevB : ∀ᶠ w in map c.2.1 (𝓝[H] (f σ₀ : ℂ)), w ∈ B :=
    Filter.mem_map.2 (Filter.mem_of_superset hev fun w hw => ⟨w, hw, rfl⟩)
  refine ⟨hevB.mono fun w hw => hBE hw, ?_⟩
  -- a base point in the band
  set w₀ : ℂ := (f σ₀ : ℂ) + ((δ / 2 : ℝ) : ℂ) * I with hw₀
  have hw₀S : w₀ ∈ S := by
    refine ⟨show (0 : ℝ) < w₀.im by simp [hw₀]; linarith, ⟨by simp [hw₀]; linarith, by simp [hw₀]; linarith⟩, ?_⟩
    simp [hw₀]; linarith
  set z := c.2.1 w₀ with hz
  have hzB : z ∈ B := ⟨w₀, hw₀S, rfl⟩
  have hzE := hBE hzB
  have hBcomp : B ⊆ connectedComponentIn (H \ (As ∪ Wu)) z := hBpc.subset_connectedComponentIn hzB hBE
  refine ⟨z, hzE, le_antisymm ?_ ?_, hevB.mono fun w hw => hBcomp hw⟩
  · exact connectedComponentIn_mono z (sdiff_subset_sdiff_right (union_subset_union_left Wu hArs))
  · set Q := connectedComponentIn (H \ (Ar ∪ Wu)) z with hQ
    have hzr : z ∈ H \ (Ar ∪ Wu) := ⟨hzE.1, fun h => h.elim (fun h' => (hBr hzB).2 h') (fun h' => hzE.2 (Or.inr h'))⟩
    have hQpc : IsPreconnected Q := isPreconnected_connectedComponentIn
    have hQsub : Q ⊆ H \ (Ar ∪ Wu) := connectedComponentIn_subset _ _
    have hQP : Q ⊆ P \ Ar := fun y hy => ⟨hcomp z (hBr hzB).1 hy, fun h => (hQsub hy).2 (Or.inl h)⟩
    have hQs : (Q \ As).Nonempty := ⟨z, mem_connectedComponentIn hzr, fun h => hzE.2 (Or.inl h)⟩
    have hQdis := htrans Q hQpc hQP hQs
    refine hQpc.subset_connectedComponentIn (mem_connectedComponentIn hzr) fun y hy => ⟨(hQsub hy).1, ?_⟩
    rintro (h | h)
    · exact Set.disjoint_left.1 hQdis hy h
    · exact (hQsub hy).2 (Or.inr h)

end Collar

end InteractingSLE.Sec7.Aux37Frame
