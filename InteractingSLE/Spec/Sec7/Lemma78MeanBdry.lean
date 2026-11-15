/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Aux57
import InteractingSLE.Spec.Restart.R1MeanChart

/-!
# Lemma 7.8's candidate mean at untouched real points and across chart transitions

Packet PROVE-PRIMEEND (specification Lemma 7.8, `source/spec/p289-336.md#lem-7.8-proof`, pp. 292–294: "On a
trace-free original boundary interval, ordinary local-set boundary decay gives the original datum. **Aux.** lemma 57
fixes the argument lift on every untouched original-real interval and on the transition from each ordinary
single-prefix chart to the joint chart").

Lemma 7.8's candidate mean in the first-contact chart of `Restart.PairData` is `𝔤_β ∘ φ − χ arg φ′`, with `φ =
d.fwd ω` (the mapping-out function of `fill(K)` shifted so that the contact point goes to `0`), `arg φ′ = d.lift ω`
(the imaginary part of the canonical logarithm of `g′`, normalized at `∞`) and `𝔤_β = β.mean` (the bounded harmonic
extension of a finite boundary word). This file proves the deterministic boundary behaviour of the candidate that the
mean identification (`Restart.IsBoxPointwiseMean`) compares with the conditional mean:

* `PairData.IsMeasGood.tendsto_lift_of_disjoint` : at a real point `x` with a ball avoiding `fill(K)`, the chart lift
  tends to `0` (Aux. 57);
* `PairData.IsMeasGood.shift_im` : the contact point goes to a real point;
* `PairData.IsMeasGood.exists_tendsto_fwd_of_disjoint` : at such `x`, `φ(z)` tends (in `ℍ`) to a real point `w`;
* `BoundaryWord.tendsto_mean_comp` : the word mean tends to the word's height at a non-jump real point;
* `PairData.IsMeasGood.exists_tendsto_candidate_of_disjoint` : at such `x`, the candidate `β.mean ∘ φ − χ arg φ′`
  tends to the height `β.fn w` (the original datum, when `β` carries it there);
* `PairData.IsMeasGood.tendsto_lift_sub_of_transition` : for a sub-hull `A ⊆ fill(K)` (an individual prefix) with
  its own canonical lift, at a boundary point `q` where `g_A` tends to a real point untouched by `g_A(fill(K) \ A)`,
  the joint lift minus the individual lift tends to `0` (Aux. 57 for the transition);
* `exists_ball_disjoint_image_of_notMem` : the clearance condition of the transition (a ball around the prime end
  `u` of `p` misses the chart image of a closed set `S ∌ p`), from continuity of the inverse map on `ℍ̄`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped NNReal

open QuantumZipper (H)

namespace InteractingSLE

namespace Restart

variable {Ω : Type*} [MeasurableSpace Ω] {d : PairData Ω}

/-- **Aux. 57 in the first-contact chart**: at a real point `x` with a ball `B(x, ρ)` avoiding `fill(K)`, the chart
lift `arg φ′` tends to `0` along `ℍ`. -/
theorem PairData.IsMeasGood.tendsto_lift_of_disjoint (hd : d.IsMeasGood) (ω : Ω) {x ρ : ℝ} (hρ : 0 < ρ)
    (hdisj : Disjoint (ball (x : ℂ) ρ) (fillH (d.K ω))) : Tendsto (d.lift ω) (𝓝[H] (x : ℂ)) (𝓝 0) := by
  have hA := hd.isHPHull ω
  exact IsCanonicalDerivLog.tendsto_im_nhdsWithin_zero hA (isCanonicalDerivLog_canonDerivLog hA)
    (ConformalImage.isMapOut_mapOut hA) hρ hdisj

/-- On the contact event the contact point is sent to a real point: `Im shift = 0`. -/
theorem PairData.IsMeasGood.shift_im (hd : d.IsMeasGood) {ω : Ω} (hω : ω ∈ d.E) : (d.shift ω).im = 0 := by
  have hA := hd.isHPHull ω
  have hpD : d.p ω ∉ H \ fillH (d.K ω) := by
    rintro ⟨hpH, hpF⟩
    refine hpF ⟨hpH, Or.inl (subset_closure ?_)⟩
    rw [p_of_mem hω, K_of_mem hω]
    exact Or.inl ⟨d.s₀ ω, ⟨zero_le, le_rfl⟩, rfl⟩
  have him : Tendsto (fun z => (d.g ω z).im) (𝓝[d.D ω] (d.p ω)) (𝓝 0) :=
    (ConformalImage.isMapOut_mapOut hA).tendsto_im_nhdsWithin hA hpD
  have : (𝓝[d.D ω] (d.p ω)).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (hd.p_mem_closure ω)
  exact tendsto_nhds_unique ((continuous_im.tendsto _).comp (hd.tendsto_shift ω)) him

/-- **The chart at an untouched real point**: if `B(x, ρ)` avoids `fill(K)`, then on the contact event `φ(z)` tends,
inside `ℍ`, to a real point `w` as `z → x` along `ℍ`. -/
theorem PairData.IsMeasGood.exists_tendsto_fwd_of_disjoint (hd : d.IsMeasGood) {ω : Ω} (hω : ω ∈ d.E) {x ρ : ℝ}
    (hρ : 0 < ρ) (hdisj : Disjoint (ball (x : ℂ) ρ) (fillH (d.K ω))) :
    ∃ w : ℝ, Tendsto (d.fwd ω) (𝓝[H] (x : ℂ)) (𝓝[H] (w : ℂ)) := by
  have hA := hd.isHPHull ω
  have hg := ConformalImage.isMapOut_mapOut hA
  obtain ⟨G, -, -, -, hGr, -, hGt⟩ := hg.exists_reflection hA hdisj
  have hxB : (x : ℂ) ∈ ball (x : ℂ) (ρ / 2) := mem_ball_self (half_pos hρ)
  have hGx : (G x).im = 0 := hGr _ hxB (by simp)
  have hsh := hd.shift_im hω
  have hfil : 𝓝[H] (x : ℂ) = 𝓝[ball (x : ℂ) (ρ / 2) ∩ H] (x : ℂ) := by
    rw [nhdsWithin_inter_of_mem (mem_nhdsWithin_of_mem_nhds (ball_mem_nhds _ (half_pos hρ)))]
  refine ⟨(G x).re - (d.shift ω).re, tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩⟩
  · have h1 := (hGt x hxB (by simp)).sub_const (d.shift ω)
    rw [← hfil] at h1
    have e : G x - d.shift ω = (((G x).re - (d.shift ω).re : ℝ) : ℂ) :=
      Complex.ext (by simp) (by simp [hGx, hsh])
    rw [← e]
    exact h1
  · have hsub : ball (x : ℂ) (ρ / 2) ∩ H ⊆ H \ fillH (d.K ω) := ball_half_inter_H_subset hdisj
    rw [hfil]
    filter_upwards [self_mem_nhdsWithin] with z hz
    show 0 < (d.g ω z - d.shift ω).im
    rw [sub_im, hsh, sub_zero]
    exact hg.1.2.mapsTo (hsub hz)

/-- **The word mean at a non-jump real point**: if `f → w` inside `ℍ` (`w ∉` the jumps of a sorted word `c`), then
`c.mean ∘ f → c.fn w`. -/
theorem BoundaryWord.tendsto_mean_comp {α : Type*} {c : BoundaryWord} (hc : c.IsSorted) {f : α → ℂ} {l : Filter α}
    {w : ℝ} (hf : Tendsto f l (𝓝[H] (w : ℂ))) (hw : w ∉ c.jumps) :
    Tendsto (fun a => c.mean (f a)) l (𝓝 (c.fn w)) :=
  ((c.isBoundedHarmonicExtension_mean hc).2.2 w (by simpa using hw)).comp hf

/-- **Lemma 7.8's candidate at an untouched real point**: if `B(x, ρ)` avoids `fill(K)`, then on the contact event
there is a real `w` (the image of `x`) such that `φ(z) → w` inside `ℍ`, and, when `w` is not a jump of the sorted
word `c`, the candidate `c.mean ∘ φ − χ arg φ′` tends to the height `c.fn w` as `z → x` along `ℍ`. -/
theorem PairData.IsMeasGood.exists_tendsto_candidate_of_disjoint (hd : d.IsMeasGood) {ω : Ω} (hω : ω ∈ d.E)
    {x ρ : ℝ} (hρ : 0 < ρ) (hdisj : Disjoint (ball (x : ℂ) ρ) (fillH (d.K ω))) (k : ℝ) {c : BoundaryWord}
    (hc : c.IsSorted) :
    ∃ w : ℝ, Tendsto (d.fwd ω) (𝓝[H] (x : ℂ)) (𝓝[H] (w : ℂ)) ∧
      (w ∉ c.jumps → Tendsto (fun z => c.mean (d.fwd ω z) - k * d.lift ω z) (𝓝[H] (x : ℂ)) (𝓝 (c.fn w))) := by
  obtain ⟨w, hw⟩ := hd.exists_tendsto_fwd_of_disjoint hω hρ hdisj
  refine ⟨w, hw, fun hwj => ?_⟩
  have h := (BoundaryWord.tendsto_mean_comp hc hw hwj).sub
    ((hd.tendsto_lift_of_disjoint ω hρ hdisj).const_mul k)
  simpa using h

/-- **Aux. 57 for the transition from an individual chart to the joint chart.** Let `A ⊆ fill(K)` be a hull (an
individual selected prefix, filled) with mapping-out function `g_A` and canonical logarithm `L_A` of `g_A′`. At a
point `q` where `g_A(z)` tends inside `ℍ` to a real point `u` whose ball `B(u, ρ)` avoids the transition hull
`g_A(fill(K) \ A)`, the joint chart lift minus the individual lift `Im L_A` tends to `0` along the active domain. -/
theorem PairData.IsMeasGood.tendsto_lift_sub_of_transition (hd : d.IsMeasGood) (ω : Ω) {A : Set ℂ} {gA LA : ℂ → ℂ}
    (hA : IsHPHull A) (hAK : A ⊆ fillH (d.K ω)) (hgA : IsMapOut A gA) (hLA : IsCanonicalDerivLog A gA LA)
    {q : ℂ} {u ρ : ℝ} (hρ : 0 < ρ) (hdisj : Disjoint (ball (u : ℂ) ρ) (gA '' (fillH (d.K ω) \ A)))
    (hq : Tendsto gA (𝓝[d.D ω] q) (𝓝[H] (u : ℂ))) :
    Tendsto (fun z => d.lift ω z - (LA z).im) (𝓝[d.D ω] q) (𝓝 0) := by
  have hB := hd.isHPHull ω
  exact _root_.InteractingSLE.Sec7.tendsto_im_sub_canonDerivLog hA hB hAK hgA (ConformalImage.isMapOut_mapOut hB) hLA
    (isCanonicalDerivLog_canonDerivLog hB) hρ hdisj hq

/-- **Prime-end clearance from physical separation** (the condition (OM2) of p. 296 in the chart of a hull `A`). Let
`F` be continuous on `ℍ̄` and invert `g` on `ℍ \ A` (`F (g z) = z`), with `g(ℍ \ A) ⊆ ℍ`. If `F(u) = p` for a real
`u` and the closed set `S` misses `p`, then a ball around `u` misses `g(S ∩ (ℍ \ A))`: the part of `S` in the
domain stays away, in the chart, from the prime end `u` of `p`. -/
theorem exists_ball_disjoint_image_of_notMem {A S : Set ℂ} {g F : ℂ → ℂ} (hFc : ContinuousOn F QuantumZipper.Hbar)
    (hFg : ∀ z ∈ H \ A, F (g z) = z) (hgH : MapsTo g (H \ A) H) {u : ℝ} {p : ℂ} (hFu : F u = p) (hS : IsClosed S)
    (hpS : p ∉ S) : ∃ ρ > 0, Disjoint (ball (u : ℂ) ρ) (g '' (S ∩ (H \ A))) := by
  obtain ⟨ε, hε, hεS⟩ := Metric.isOpen_iff.1 hS.isOpen_compl p hpS
  have huH : (u : ℂ) ∈ QuantumZipper.Hbar := show (0 : ℝ) ≤ (u : ℂ).im by simp
  obtain ⟨ρ, hρ, hρF⟩ := Metric.continuousWithinAt_iff.1 (hFc _ huH) ε hε
  refine ⟨ρ, hρ, Set.disjoint_left.2 fun w hw ⟨z, ⟨hzS, hzD⟩, hzw⟩ => ?_⟩
  have hwH : w ∈ QuantumZipper.Hbar := by
    rw [← hzw]; exact le_of_lt (show 0 < (g z).im from hgH hzD)
  have h1 := hρF hwH (mem_ball.1 hw)
  rw [← hzw, hFg z hzD, hFu] at h1
  exact hεS (mem_ball.2 h1) hzS

end Restart

end InteractingSLE
