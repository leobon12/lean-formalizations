/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FCAux79Mean

/-!
# Aux. 79 at the later first-contact lines: the heights on the new piece

Packet PROVE-FCAUX79 (spec p. 290: "At any exposed side away from that vertex and the finitely many tips, the two
ranges have positive local distance. Nested boundary comparison consequently gives the corresponding single-path
height there. … For a compact subarc of the later first prefix choose a rational stop after that subarc and before its
endpoint"). This file reduces the new-piece heights `FCAux79.IsFCSideLimit` (the one remaining hypothesis of
`FCAux79.ae_chartTransport_lineMean`) to a **deterministic orientation statement** `IsFCSideSign`:

* `tendsto_lift_sub_line`: Aux. 57 for the transition from a single-prefix chart of the first path to the canonical
  chart of the later hull (the later-line copy of `SideHeightBox.tendsto_lift_sub`);
* `IsFCSideSign` (definition): at a point `p = η₁(s)` of the open new piece reached from the later domain along an
  approach with composed-chart value `y ≠ 0`, the single-path chart value `y'` of `η₁` at a later stop `q` has the
  sign of `y`, and `p` is not a real point on the forbidden side of the seed `x₁`;
* `tendsto_new_side`: the pathwise assembly (Proposition 3.8 with the single prefix at a rational stop, the single-path
  heights `SideHeightBoxSingle.singlePathSideHeight_gen`, the lift transition and the sign);
* `isFCSideLimit_of_sign`: `IsFCSideLimit` from the named inputs of the glued (R1) and `IsFCSideSign`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull logDerivFwd)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE

namespace Restart.FCAux79

open Sec7 Sec7.SideHeightBox Supp7 LocalSets Sec6

universe u

section Path

variable {Ω : Type*} [MeasurableSpace Ω] {d : PairData Ω} {ω : Ω} {x₁ x₂ : ℝ} {t : ℝ≥0}
  {W : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {ζc : ℝ≥0∞} {Q : ℝ≥0}

/-- **Aux. lemma 57 for the transition from a single-prefix chart to the canonical chart of the later hull, along an
approach** (the later-line copy of `SideHeightBox.tendsto_lift_sub`, with the first-contact union replaced by the
later union `lineK`). -/
theorem tendsto_lift_sub_line (hd : d.IsMeasGood) (hl : IsFCLine d ω x₁ x₂ t W γ ζc Q) {γ₁ : ℝ≥0 → ℂ} {ζ : ℝ≥0∞}
    {x : ℝ} {W₁ : ℝ≥0 → ℝ} {q : ℝ≥0} (hg : IsGeneratingTrace W₁ ζ (fun t => γ₁ t - x))
    (hWc : ContinuousOn W₁ {s | (s : ℝ≥0∞) < ζ}) (hW0 : W₁ 0 = 0) (hi : InjOn γ₁ {t | (t : ℝ≥0∞) ≤ ζ})
    (hq : (q : ℝ≥0∞) < ζ) (hq0 : 0 < q) (hsub : γ₁ '' Icc 0 q ⊆ lineK d t ω) {p : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hloc : lineK d t ω ∩ ball p ρ ⊆ γ₁ '' Icc 0 q) (U : Ultrafilter ℂ)
    (hU : (U : Filter ℂ) ≤ 𝓝[H \ fillH (lineK d t ω)] p) {y : ℝ}
    (hfy : Tendsto (fun z => fwdMap (fun r : ℝ => W₁ r.toNNReal) q (z - x)) U (𝓝 (y : ℂ))) :
    Tendsto (fun z => (canonDerivLog (fillH (lineK d t ω)) z).im -
      (logDerivFwd (fun r : ℝ => W₁ r.toNNReal) q (z - x)).im) U (𝓝 0) := by
  have hKc := hl.isCompact_lineK hd
  have hB := hl.isHPHull_lineK hd
  obtain ⟨κ, hK, hgm, hL⟩ := ReverseArc.exists_physChart hg hWc hW0 hq
  obtain ⟨Φ, hΦc, hΦH, -, hinv, hmaps⟩ := ReverseArc.exists_physInv hg hWc hW0 hi hq hq0
  obtain ⟨ε, hε, hno⟩ := ReverseArc.exists_ball_notMem_of_approach hKc.isClosed hsub hmaps hΦc hΦH hinv hρ hloc U hU
    hfy
  have hdisj : Disjoint (ball (((y + κ : ℝ)) : ℂ) ε)
      ((fun z => fwdMap (fun r : ℝ => W₁ r.toNNReal) q (z - x) + κ) '' (fillH (lineK d t ω) \
        fillH (γ₁ '' Icc 0 q))) := by
    rw [Set.disjoint_left]
    rintro w hwb ⟨z, ⟨hzK, hzA⟩, rfl⟩
    refine hno z ⟨hzK.1, hzA⟩ hzK ?_
    rw [mem_ball, dist_eq_norm] at hwb ⊢
    convert hwb using 2
    push_cast; ring
  have hF : (U : Filter ℂ) ≤ 𝓟 (H \ fillH (lineK d t ω)) := hU.trans inf_le_right
  have hq' : Tendsto (fun z => fwdMap (fun r : ℝ => W₁ r.toNNReal) q (z - x) + κ) U
      (𝓝[H] (((y + κ : ℝ)) : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have := hfy.add_const (κ : ℂ)
      convert this using 2
      push_cast; ring
    · filter_upwards [hF (mem_principal_self _)] with z hz
      exact hgm.1.2.mapsTo ⟨hz.1, fun h => hz.2 (fillH_mono hsub h)⟩
  exact ReverseArc.tendsto_im_sub_of_le hK hB (fillH_mono hsub) hgm (ConformalImage.isMapOut_mapOut hB) hL
    (isCanonicalDerivLog_canonDerivLog hB) hF hε hdisj hq'

/-- **The side of an approach to the new piece** (the deterministic orientation input of the heights on the new
piece; spec p. 290, "Nested boundary comparison consequently gives the corresponding single-path height there"). For
every driver `W₁` generating the first path from its seed `x₁`, at every real `y` that the extended inverse `Φ` of `f_Q`
sends to a point `γ(σ)`, `0 < σ < Q`, of the open chart path, with `0 < y < R̃` or `L̃ < y < 0` (`R̃`, `L̃` the images
of `0±`; at the corners a real touch point is also reached along the real line), with physical point
`ψ(γ(σ)) = η₁(s)`, and every later
stop `q ∈ (s, s₀ + t)` with `η₁(q) ∈ ℍ`: along every approach `U → y` in `ℍ` on which the single-path chart
`f^{(1)}_q(ψ_t(·) − x₁)` has a real limit `y'`, `y'` has the sign of `y`, and `η₁(s)` is not a real point on the side
of the seed `x₁` that the single-path heights exclude (right of `x₁` for `y > 0`, left of `x₁` for `y < 0`). -/
def IsFCSideSign (d : PairData Ω) (ω : Ω) (x₁ : ℝ) (t : ℝ≥0) (W : ℝ≥0 → ℝ) (γ : ℝ≥0 → ℂ) (Q : ℝ≥0) : Prop :=
  ∀ W₁ : ℝ≥0 → ℝ, IsGeneratingTrace W₁ (d.ζ₁ ω) (fun s => d.η₁ ω s - x₁) →
    ContinuousOn W₁ {s | (s : ℝ≥0∞) < d.ζ₁ ω} → W₁ 0 = 0 →
    ∀ (y : ℝ) (σ : ℝ≥0), σ ∈ Ioo 0 Q → extendFrom H (fwdMapInv (fun s : ℝ => W s.toNNReal) Q) y = γ σ →
    ∀ s q : ℝ≥0, d.inv ω (γ σ) = d.η₁ ω s → s < q → q < d.s₀ ω + t → d.η₁ ω q ∈ H →
    ∀ U : Ultrafilter ℂ, (U : Filter ℂ) ≤ 𝓝[H] (y : ℂ) → ∀ y' : ℝ,
      Tendsto (fun w => fwdMap (fun r : ℝ => W₁ r.toNNReal) q
        (d.inv ω (fwdMapInv (fun s : ℝ => W s.toNNReal) Q w) - x₁)) U (𝓝 (y' : ℂ)) →
      (0 < y → y < MartChar.RealFlow.rightImg (fun s : ℝ => W s.toNNReal) 0 Q - W Q →
        0 < y' ∧ ¬ ((d.η₁ ω s - x₁).im = 0 ∧ 0 ≤ (d.η₁ ω s - x₁).re)) ∧
      (y < 0 → -MartChar.RealFlow.rightImg (fun s : ℝ => -W s.toNNReal) 0 Q - W Q < y →
        y' < 0 ∧ ¬ ((d.η₁ ω s - x₁).im = 0 ∧ (d.η₁ ω s - x₁).re ≤ 0))

/-- **The heights on the new piece at one chart point** (pathwise; the inputs are the almost sure statements at the
rational stops of the first path, as in `SideHeightBox.tendsto_side_right`: the comparison `hcmp` of the later union
`lineK ∩ ℍ` with the prefix `η₁([0, r]) ∩ ℍ`, the single-path heights `hsh` and the harmonic representatives `hrep`;
and the orientation `hsign`). At every real `y ≠ 0` that `Φ` sends onto the open chart path, the composed field mean
tends to `hR` (`0 < y < R̃`) or `hL` (`L̃ < y < 0`). -/
theorem tendsto_new_side (hd : d.IsMeasGood) (hl : IsFCLine d ω x₁ x₂ t W γ ζc Q) {κ hL hR : ℝ} {m : ℝ≥0}
    (hst : d.s₀ ω + t < m) {W₁ : ℝ≥0 → ℝ} (hg₁ : IsGeneratingTrace W₁ (d.ζ₁ ω) (fun s => d.η₁ ω s - x₁))
    (hWc₁ : ContinuousOn W₁ {s | (s : ℝ≥0∞) < d.ζ₁ ω}) (hW0₁ : W₁ 0 = 0) {A : ℝ≥0 → Set ℂ}
    (hA : ∀ q : ℝ≥0, q ≤ m → (q : ℝ≥0∞) < d.ζ₁ ω → A q = d.η₁ ω '' Icc 0 q ∩ H) {u₀ v : ℂ → ℝ}
    (hv : InnerProductSpace.HarmonicOnNhd v (H \ (lineK d t ω ∩ H))) {g : DistOn upperHalfPlaneOpens}
    (hvr : ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (lineK d t ω ∩ H) → g φ = ∫ z, v z * φ z)
    {G : ℚ → DistOn upperHalfPlaneOpens} (hrep : ∀ r : ℚ, IsHarmonicDistOn (G r) (H \ A (r : ℝ).toNNReal))
    (hcmp : ∀ r : ℚ, ∀ vB vA : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd vB (H \ (lineK d t ω ∩ H)) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (lineK d t ω ∩ H) → g φ = ∫ z, vB z * φ z) →
      InnerProductSpace.HarmonicOnNhd vA (H \ A (r : ℝ).toNNReal) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A (r : ℝ).toNNReal → G r φ = ∫ z, vA z * φ z) →
      ∀ p : ℂ, p ∈ (lineK d t ω ∩ H) ∪ {z : ℂ | z.im = 0} → p ∈ A (r : ℝ).toNNReal ∪ {z : ℂ | z.im = 0} →
      (∃ ρ > 0, A (r : ℝ).toNNReal ∩ ball p ρ ⊆ lineK d t ω ∩ H) →
      (∃ ρ > 0, (lineK d t ω ∩ H) ∩ ball p ρ ⊆ A (r : ℝ).toNNReal) →
      Tendsto (fun z => vB z - vA z) (𝓝[H \ ((lineK d t ω ∩ H) ∪ A (r : ℝ).toNNReal)] p) (𝓝 0))
    (hsh : ∀ r : ℚ, (r : ℝ).toNNReal ≤ m → (((r : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) < d.ζ₁ ω → ∀ vA : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd vA (H \ A (r : ℝ).toNNReal) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A (r : ℝ).toNNReal → G r φ = ∫ z, vA z * φ z) →
      ∀ (p : ℂ) (F : Filter ℂ), F.NeBot → F ≤ 𝓝[H \ fillH (d.η₁ ω '' Icc 0 (r : ℝ).toNNReal)] p → ∀ y : ℝ,
        Tendsto (fun z => fwdMap (fun s : ℝ => W₁ s.toNNReal) (r : ℝ).toNNReal (z - x₁)) F (𝓝 (y : ℂ)) →
        (0 < y → ¬ ((p - x₁).im = 0 ∧ 0 ≤ (p - x₁).re) → Tendsto (fun z => vA z + u₀ z +
          QuantumZipper.chiC κ * (logDerivFwd (fun s : ℝ => W₁ s.toNNReal) (r : ℝ).toNNReal (z - x₁)).im) F
          (𝓝 hR)) ∧
        (y < 0 → ¬ ((p - x₁).im = 0 ∧ (p - x₁).re ≤ 0) → Tendsto (fun z => vA z + u₀ z +
          QuantumZipper.chiC κ * (logDerivFwd (fun s : ℝ => W₁ s.toNNReal) (r : ℝ).toNNReal (z - x₁)).im) F
          (𝓝 hL)))
    (hsign : IsFCSideSign d ω x₁ t W γ Q) {y : ℝ}
    (hy : extendFrom H (fwdMapInv (fun s : ℝ => W s.toNNReal) Q) y ∈ γ '' Ioo 0 Q) :
    (0 < y → y < MartChar.RealFlow.rightImg (fun s : ℝ => W s.toNNReal) 0 Q - W Q →
      Tendsto (compMean d t W Q v u₀ κ ω) (𝓝[H] (y : ℂ)) (𝓝 hR)) ∧
    (y < 0 → -MartChar.RealFlow.rightImg (fun s : ℝ => -W s.toNNReal) 0 Q - W Q < y →
      Tendsto (compMean d t W Q v u₀ κ ω) (𝓝[H] (y : ℂ)) (𝓝 hL)) := by
  set χ := QuantumZipper.chiC κ with hχ
  set w' : ℝ → ℝ := fun s => W s.toNNReal with hw'
  set ψt : ℂ → ℂ := fun w => d.inv ω (fwdMapInv w' Q w) with hψt
  have hE := hl.mem_E
  have hfc := hl.isFirstContact hd
  have hC := hl.chart hd
  obtain ⟨σ, hσ, hσe⟩ := hy
  have hpI : d.inv ω (γ σ) ∈ d.η₁ ω '' Icc (d.s₀ ω) (d.s₀ ω + t) := hl.image ▸ ⟨σ, Ioo_subset_Icc_self hσ, rfl⟩
  obtain ⟨s, hsI, hse⟩ := hpI
  have hγσ : γ σ ∈ Hbar := hl.γ_mem_Hbar hσ.2.le
  have hγinj : ∀ σ' : ℝ≥0, σ' ≤ Q → γ σ = γ σ' → σ = σ' := fun σ' hσ' h =>
    hl.inj ((ENNReal.coe_le_coe.2 hσ.2.le).trans hl.lt.le) ((ENNReal.coe_le_coe.2 hσ').trans hl.lt.le) h
  have hs₀ : d.s₀ ω < s := by
    refine lt_of_le_of_ne hsI.1 fun h => ?_
    have h1 : d.inv ω (γ σ) = d.inv ω (γ 0) := by
      rw [← hse, ← h, hl.gen.1]
      exact (inv_zero_eq_contact hd hE).symm
    have := hγinj 0 zero_le (inv_injOn_Hbar hd hl hγσ (hl.γ_mem_Hbar zero_le) h1)
    exact (ne_of_gt hσ.1) this
  have hst' : s < d.s₀ ω + t := by
    refine lt_of_le_of_ne hsI.2 fun h => ?_
    have h1 : d.inv ω (γ σ) = d.inv ω (γ Q) := by rw [← hse, h, hl.tip]
    have := hγinj Q le_rfl (inv_injOn_Hbar hd hl hγσ (hl.γ_mem_Hbar le_rfl) h1)
    exact (ne_of_lt hσ.2) this
  -- a rational stop after `s`
  obtain ⟨r, hr1, hr2, hr3⟩ := IsPathGood.exists_rat_mem_H hl.path₁ hst' hl.le_life
  set q := (r : ℝ).toNNReal with hqdef
  have hqm : q ≤ m := (hr2.trans hst).le
  have hqζ : (q : ℝ≥0∞) < d.ζ₁ ω := lt_of_lt_of_le (ENNReal.coe_lt_coe.2 hr2) hl.le_life
  have hq0 : 0 < q := lt_of_le_of_lt zero_le hr1
  set p := d.η₁ ω s with hpdef
  have hsζ : (s : ℝ≥0∞) ≤ d.ζ₁ ω := (ENNReal.coe_le_coe.2 hst'.le).trans hl.le_life
  -- `p` is off the second prefix and off the later part of the first
  have hp₂ : p ∉ d.η₂ ω '' Icc 0 (d.t₀ ω) := by
    rintro ⟨t', ht', he⟩
    obtain ⟨-, ht₀⟩ := hfc.2.2.2 s t' hsζ ((ENNReal.coe_le_coe.2 ht'.2).trans hfc.2.1) he.symm
    have htt : t' = d.t₀ ω := le_antisymm ht'.2 ht₀
    have h1 : d.η₁ ω s = d.η₁ ω (d.s₀ ω) := by rw [hfc.2.2.1, ← htt]; exact he.symm
    have := hl.injOn₁ ⟨zero_le, hst'.le⟩ ⟨zero_le, le_self_add⟩ h1
    exact (ne_of_gt hs₀) this
  have hp₁ : p ∉ d.η₁ ω '' Icc q (d.s₀ ω + t) := by
    rintro ⟨s', hs', he⟩
    have := hl.injOn₁ ⟨zero_le, hs'.2⟩ ⟨zero_le, hst'.le⟩ he
    exact absurd (this ▸ hs'.1) (not_le.2 hr1)
  have hNc : IsCompact (d.η₂ ω '' Icc 0 (d.t₀ ω) ∪ d.η₁ ω '' Icc q (d.s₀ ω + t)) :=
    (isCompact_Icc.image_of_continuousOn (hl.continuousOn₂ hd)).union
      (isCompact_Icc.image_of_continuousOn (hl.continuousOn₁.mono (Icc_subset_Icc_left zero_le)))
  obtain ⟨ρ, hρ, hρN⟩ := Metric.isOpen_iff.1 hNc.isClosed.isOpen_compl p (by
    rintro (h | h)
    · exact hp₂ h
    · exact hp₁ h)
  have hloc : lineK d t ω ∩ ball p ρ ⊆ d.η₁ ω '' Icc 0 q := by
    rintro z ⟨(⟨s', hs', rfl⟩ | hz), hzb⟩
    · by_cases hs'q : s' ≤ q
      · exact ⟨s', ⟨zero_le, hs'q⟩, rfl⟩
      · exact absurd (Or.inr ⟨s', ⟨(not_le.1 hs'q).le, hs'.2⟩, rfl⟩) (hρN hzb)
    · exact absurd (Or.inl hz) (hρN hzb)
  have hsubP : d.η₁ ω '' Icc 0 q ⊆ lineK d t ω := fun z ⟨s', hs', he⟩ =>
    Or.inl ⟨s', ⟨zero_le, hs'.2.trans hr2.le⟩, he⟩
  have hDA : H \ fillH (lineK d t ω) ⊆ H \ fillH (d.η₁ ω '' Icc 0 q) := sdiff_subset_sdiff_right (fillH_mono hsubP)
  have hAq := hA q hqm hqζ
  have hBA : (lineK d t ω ∩ H) ∩ ball p ρ ⊆ A q := by
    rw [hAq]; rintro z ⟨⟨hzK, hzH⟩, hzb⟩; exact ⟨hloc ⟨hzK, hzb⟩, hzH⟩
  have hAB : A q ⊆ lineK d t ω ∩ H := by rw [hAq]; exact inter_subset_inter_left _ hsubP
  have hDB : H \ fillH (lineK d t ω) ⊆ H \ ((lineK d t ω ∩ H) ∪ A q) := by
    rw [union_eq_left.2 hAB]
    intro z hz
    exact ⟨hz.1, fun h => hz.2 ⟨h.2, Or.inl (subset_closure h.1)⟩⟩
  have hpbar : p ∈ Hbar := IsPathGood.im_nonneg hl.path₁ hsζ
  have hpK : p ∈ lineK d t ω := Or.inl ⟨s, ⟨zero_le, hsI.2⟩, rfl⟩
  have hpB : p ∈ (lineK d t ω ∩ H) ∪ {z : ℂ | z.im = 0} := by
    rcases mem_H_or_im_eq_zero hpbar with h | h
    · exact Or.inl ⟨hpK, h⟩
    · exact Or.inr h
  have hpA : p ∈ A q ∪ {z : ℂ | z.im = 0} := by
    rw [hAq]
    rcases mem_H_or_im_eq_zero hpbar with h | h
    · exact Or.inl ⟨⟨s, ⟨zero_le, hr1.le⟩, rfl⟩, h⟩
    · exact Or.inr h
  obtain ⟨vA, hvA, hvAr⟩ := hrep r
  have hcmp' := hcmp r v vA hv hvr hvA hvAr p hpB hpA ⟨1, one_pos, fun z hz => hAB hz.1⟩ ⟨ρ, hρ, hBA⟩
  -- the composed chart tends to `p` within the later domain
  have hψc : ContinuousOn (d.inv ω) Hbar := hC.2.2.2.2.2.2.2.1
  have hT : Tendsto ψt (𝓝[H] (y : ℂ)) (𝓝[H \ fillH (lineK d t ω)] p) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun w hw => (hl.inv_mem hd hw).1⟩
    have h1 := (hl.tendsto_fwdMapInv (ofReal_mem_Hbar y)).mono_right
      (nhdsWithin_mono _ fun z hz => QuantumZipper.H_subset_Hbar hz.1)
    rw [← hσe] at h1
    have h2 := (hψc (γ σ) hγσ).tendsto.comp h1
    have hpe : p = d.inv ω (γ σ) := hse
    rw [hpe]
    exact h2
  have hcore : ∀ U : Ultrafilter ℂ, (U : Filter ℂ) ≤ 𝓝[H] (y : ℂ) →
      ∃ y' : ℝ, Tendsto (fun z => fwdMap (fun s : ℝ => W₁ s.toNNReal) q (z - x₁)) (U.map ψt) (𝓝 (y' : ℂ)) ∧
        ((U.map ψt : Filter ℂ) ≤ 𝓝[H \ fillH (lineK d t ω)] p) ∧
        (0 < y → y < MartChar.RealFlow.rightImg (fun s : ℝ => W s.toNNReal) 0 Q - W Q →
          0 < y' ∧ ¬ ((p - x₁).im = 0 ∧ 0 ≤ (p - x₁).re)) ∧
        (y < 0 → -MartChar.RealFlow.rightImg (fun s : ℝ => -W s.toNNReal) 0 Q - W Q < y →
          y' < 0 ∧ ¬ ((p - x₁).im = 0 ∧ (p - x₁).re ≤ 0)) := by
    intro U hU
    have hV : (U.map ψt : Filter ℂ) ≤ 𝓝[H \ fillH (lineK d t ω)] p := by
      rw [Ultrafilter.coe_map]; exact (map_mono hU).trans hT
    have hch := isPhysChart hg₁ hWc₁ hW0₁ hl.path₁.1 hqζ hq0
    obtain ⟨y', hfy, -⟩ := hch.exists_real_tendsto ⟨s, ⟨zero_le, hr1.le⟩, rfl⟩ (U.map ψt)
      (hV.trans (nhdsWithin_mono _ hDA))
    have hfy' : Tendsto (fun w => fwdMap (fun r : ℝ => W₁ r.toNNReal) q
        (d.inv ω (fwdMapInv (fun s : ℝ => W s.toNNReal) Q w) - x₁)) U (𝓝 (y' : ℂ)) := by
      rw [Ultrafilter.coe_map] at hfy; exact tendsto_map'_iff.1 hfy
    have hsg := hsign W₁ hg₁ hWc₁ hW0₁ y σ hσ hσe.symm s q hse.symm hr1 hr2 hr3 U hU y' hfy'
    exact ⟨y', hfy, hV, hsg.1, hsg.2⟩
  refine ⟨fun hpos hlt => ?_, fun hneg hlt => ?_⟩
  · rw [tendsto_iff_ultrafilter]
    intro U hU
    obtain ⟨y', hfy, hV, hs1, -⟩ := hcore U hU
    obtain ⟨hy'pos, hpR⟩ := hs1 hpos hlt
    have h1 := (hsh r hqm hqζ vA hvA hvAr p (U.map ψt) inferInstance (hV.trans (nhdsWithin_mono _ hDA)) y'
      hfy).1 hy'pos hpR
    have h2 := tendsto_lift_sub_line hd hl hg₁ hWc₁ hW0₁ hl.path₁.1 hqζ hq0 hsubP hρ hloc (U.map ψt) hV hfy
    have h3 := hcmp'.mono_left (hV.trans (nhdsWithin_mono _ hDB))
    have hsum := h3.add (h1.add (h2.const_mul χ))
    rw [zero_add, mul_zero, add_zero] at hsum
    have hfin : Tendsto (fun z => v z + u₀ z + χ * (canonDerivLog (fillH (lineK d t ω)) z).im)
        (U.map ψt : Filter ℂ) (𝓝 hR) := hsum.congr fun z => by ring
    rw [Ultrafilter.coe_map] at hfin
    exact tendsto_map'_iff.1 hfin
  · rw [tendsto_iff_ultrafilter]
    intro U hU
    obtain ⟨y', hfy, hV, -, hs2⟩ := hcore U hU
    obtain ⟨hy'neg, hpL⟩ := hs2 hneg hlt
    have h1 := (hsh r hqm hqζ vA hvA hvAr p (U.map ψt) inferInstance (hV.trans (nhdsWithin_mono _ hDA)) y'
      hfy).2 hy'neg hpL
    have h2 := tendsto_lift_sub_line hd hl hg₁ hWc₁ hW0₁ hl.path₁.1 hqζ hq0 hsubP hρ hloc (U.map ψt) hV hfy
    have h3 := hcmp'.mono_left (hV.trans (nhdsWithin_mono _ hDB))
    have hsum := h3.add (h1.add (h2.const_mul χ))
    rw [zero_add, mul_zero, add_zero] at hsum
    have hfin : Tendsto (fun z => v z + u₀ z + χ * (canonDerivLog (fillH (lineK d t ω)) z).im)
        (U.map ψt : Filter ℂ) (𝓝 hL) := hsum.congr fun z => by ring
    rw [Ultrafilter.coe_map] at hfin
    exact tendsto_map'_iff.1 hfin

end Path

section Main

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x₁ x₂ θ₁ θ₂ : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {η₁ η₂ : Ω → ℝ≥0 → ℂ}
  {ζ₁ ζ₂ : Ω → ℝ≥0∞}

/-- **The heights on the new piece** (`IsFCSideLimit`, spec p. 290) in the setting of
`FirstContactWordKernelStatement`, from the named inputs of the glued (R1) (Lemma 7.5, Lemma 7.7, Aux. 56 at first
entrances) and the deterministic orientation `IsFCSideSign` at every reading of the continuation. Proof: Proposition
3.8 for the later union and the prefix `η₁([0, r])` at every rational `r`, the single-path heights at `r`
(`singlePathSideHeight_gen`), and `tendsto_new_side`. -/
theorem isFCSideLimit_of_sign (hL75 : Theorem15.Lemma75Statement.{u}) (hL77 : Supp10.Lemma77Statement.{u})
    (hA56 : RetainedRangeEntranceStatement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hx : x₂ < x₁) (hθ : θ₁ < θ₂ + Real.pi)
    (hh : IsGFFWithBoundaryData P h b jumps) (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁)
    (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂) {d : PairData Ω} (hd : d.IsMeasGood) (hζ₁ : d.ζ₁ = ζ₁)
    (hζ₂ : d.ζ₂ = ζ₂)
    (hae : ∀ᵐ ω ∂P, ω ∈ d.G ∧ (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → d.η₁ ω s = η₁ ω s) ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ₂ ω → d.η₂ ω t = η₂ ω t)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    (hsign : ∀ (ω : Ω) (t : ℝ≥0) (W : ℝ≥0 → ℝ) (γ : ℝ≥0 → ℂ) (ζc : ℝ≥0∞) (Q : ℝ≥0),
      IsFCLine d ω x₁ x₂ t W γ ζc Q → IsFCSideSign d ω x₁ t W γ Q) :
    IsFCSideLimit κ θ₁ x₁ x₂ P h η₁ η₂ ζ₁ ζ₂ u₀ d := by
  intro m t ηc₁ ηc₂ g hc₁ hc₂ hm₁ hm₂ hag₁ hag₂ hg
  subst hζ₁ hζ₂
  classical
  have hh0 := isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀
  obtain ⟨hBm, hBloc, hBdet, hBunb⟩ :=
    shUnion_facts hL75 hL77 hA56 hκ hκ4 hb hx hθ hh hη₁ hη₂ hu₀ (m : ℝ≥0) t hc₁ hc₂ hm₁ hm₂ hag₁ hag₂
  have hF₁ := fun q : ℝ≥0 => range_facts hL75 hA56 hκ hκ4 hb hh hη₁ hu₀ (m : ℝ≥0) q hc₁ hm₁ hag₁
  have hmean₁ : ∀ r : ℚ, ∃ G, IsLocalSetMean (fun ω => ηc₁ ω '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ (r : ℝ).toNNReal} ∩ H)
      (WholeField.centredField h u₀) P G := fun r =>
    IsLocalSet.exists_isLocalSetMean hh0 (hF₁ _).1 (hF₁ _).2.1
  choose G₁ hG₁ using hmean₁
  obtain ⟨_, _, W₁, _, _, _, -, hcoup₁, htr₁⟩ := id hη₁
  have hC₁ := fun r : ℚ => ae_tendsto_sub_of_locals hh0 hBm (hF₁ _).1 hBloc (hF₁ _).2.1 hBdet (hF₁ _).2.2.1 hBunb
    (hF₁ _).2.2.2 hg (hG₁ r)
  have hS₁ := fun r : ℚ => singlePathSideHeight_gen (m := (m : ℝ≥0)) (q := (r : ℝ).toNNReal) hL75 hA56 hκ hκ4 hb hh
    hη₁ htr₁ hu₀
  have hS₁' : ∀ r : ℚ, ∀ᵐ ω ∂P, (r : ℝ).toNNReal ≤ (m : ℝ≥0) → _ := fun r => by
    by_cases hrm : (r : ℝ).toNNReal ≤ (m : ℝ≥0)
    · filter_upwards [hS₁ r hrm hc₁ hm₁ hag₁ (hG₁ r)] with ω hω _
      exact hω
    · exact Eventually.of_forall fun ω h => absurd h hrm
  have hcmp := ae_retHist_eq_fcHist hd hc₁ hc₂ m hae hag₁ hag₂
  filter_upwards [hae, hag₁, hag₂, hcmp, htr₁, hcoup₁.1.2.2.2.2, ae_all_iff.2 hC₁, ae_all_iff.2 hS₁',
    ae_all_iff.2 fun r => (hG₁ r).2.1]
    with ω ⟨_, ha₁, ha₂⟩ hag₁ω hag₂ω ⟨_, heq⟩ htr₁ω hpath₁ hC₁ω hS₁ω hR₁ω hbox hst v hv hvrep W γ ζc Q hl y hy
  have hU : shUnion ηc₁ ηc₂ t 0 ω = lineK d t ω ∩ H :=
    shUnion_eq_lineK m t hbox hst hl.le_life ha₁ ha₂ hag₁ω hag₂ω (heq hbox)
  have hg₁ : IsGeneratingTrace (fun t => W₁ t ω) (d.ζ₁ ω) (fun t => d.η₁ ω t - x₁) :=
    isGeneratingTrace_congr htr₁ω fun t ht => by simp only [ha₁ t ht]
  have himg₁ : ∀ q : ℝ≥0, (q : ℝ≥0∞) < d.ζ₁ ω → η₁ ω '' Icc 0 q = d.η₁ ω '' Icc 0 q := fun q hq =>
    image_congr fun t ht => (ha₁ t ((ENNReal.coe_le_coe.2 ht.2).trans hq.le)).symm
  have hA₁ : ∀ q : ℝ≥0, q ≤ (m : ℝ≥0) → (q : ℝ≥0∞) < d.ζ₁ ω →
      ηc₁ ω '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ q} ∩ H = d.η₁ ω '' Icc 0 q ∩ H := fun q hqm hq => by
    rw [image_capped_eq hag₁ω (le_min hq.le (ENNReal.coe_le_coe.2 hqm)), himg₁ q hq]
  rw [hU] at hv hvrep hC₁ω
  exact tendsto_new_side hd hl hst hg₁ hpath₁.2.2.2.1 hpath₁.1
    (A := fun q => ηc₁ ω '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ q} ∩ H) hA₁ hv hvrep (G := fun r => G₁ r ω) hR₁ω hC₁ω
    (fun r hrm hrζ vA hvA hvAr p F hF hFle y hy => by
      rw [← himg₁ _ hrζ] at hFle
      exact hS₁ω r hrm hrζ vA hvA hvAr p F hF hFle y hy)
    (hsign ω t W γ ζc Q hl) hy

/-- **Aux. lemma 79 at the later first-contact lines, K2's `hmean`, for Lemma 7.8's word** (the entry point for the
first-contact plumbing, PROVE-FCDET §4.1): `ae_chartTransport_lineMean` with the first-contact chart boundary values of
the explicit word `d.word c₀ (−λ − θ₂χ) (λ − θ₁χ)` (landed: `isBoxChartBoundaryLimit_word`,
`isBoxSideLimit_of_flowLines`) and the new-piece heights from the orientation (`isFCSideLimit_of_sign`). The only
hypothesis beyond the setting and the named inputs of the glued (R1) is the deterministic `IsFCSideSign`. -/
theorem ae_chartTransport_lineMean_word (hL75 : Theorem15.Lemma75Statement.{u})
    (hL77 : Supp10.Lemma77Statement.{u}) (hA56 : RetainedRangeEntranceStatement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hx : x₂ < x₁) (hθ : θ₁ < θ₂ + Real.pi)
    (hh : IsGFFWithBoundaryData P h b jumps) (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁)
    (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂) {d : PairData Ω} (hd : d.IsMeasGood) (hζ₁ : d.ζ₁ = ζ₁)
    (hζ₂ : d.ζ₂ = ζ₂)
    (hae : ∀ᵐ ω ∂P, ω ∈ d.G ∧ (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → d.η₁ ω s = η₁ ω s) ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ₂ ω → d.η₂ ω t = η₂ ω t)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) {c₀ : BoundaryWord}
    (hc₀ : StrictMonoOn c₀.2.1 (Iio c₀.1)) (hc₀J : c₀.jumps = jumps) (hc₀b : ∀ y ∉ jumps, c₀.fn y = b y)
    (hsign : ∀ (ω : Ω) (t : ℝ≥0) (W : ℝ≥0 → ℝ) (γ : ℝ≥0 → ℂ) (ζc : ℝ≥0∞) (Q : ℝ≥0),
      IsFCLine d ω x₁ x₂ t W γ ζc Q → IsFCSideSign d ω x₁ t W γ Q)
    (m : ℕ) (t : ℝ≥0) {ηc₁ ηc₂ : Ω → ℝ≥0 → ℂ} (hc₁ : ∀ ω, Continuous (ηc₁ ω)) (hc₂ : ∀ ω, Continuous (ηc₂ ω))
    (hm₁ : ∀ s, Measurable fun ω => ηc₁ ω s) (hm₂ : ∀ s, Measurable fun ω => ηc₂ ω s)
    (hag₁ : ∀ᵐ ω ∂P, ∀ s, ηc₁ ω s = η₁ ω (capTime m (ζ₁ ω) s))
    (hag₂ : ∀ᵐ ω ∂P, ∀ s, ηc₂ ω s = η₂ ω (capTime m (ζ₂ ω) s)) {g : Ω → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean (shUnion ηc₁ ηc₂ t 0) (WholeField.centredField h u₀) P g) :
    ∀ᵐ ω ∂P, ω ∈ meetBox d m → d.s₀ ω + t < m →
      ∀ (W : ℝ≥0 → ℝ) (γ : ℝ≥0 → ℂ) (ζc : ℝ≥0∞) (Q : ℝ≥0), IsFCLine d ω x₁ x₂ t W γ ζc Q →
      ∀ {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ),
      (∀ i, xL i ≤ 0) → (∀ j, 0 ≤ xR j) →
      (∃ S : Set ℝ, S.Finite ∧ ∀ x ∉ S, forceBoundaryData κ ρL ρR xL xR x =
        (d.word c₀ (-sleLambda κ - θ₂ * QuantumZipper.chiC κ) (sleLambda κ - θ₁ * QuantumZipper.chiC κ) ω).fn x +
          θ₁ * QuantumZipper.chiC κ) →
      ∀ ψ : TestOn upperHalfPlaneOpens, tsupport ψ ⊆ H \ fwdHull (fun s : ℝ => W s.toNNReal) Q →
        Chart.chartTransport (hd.isConformal_chart ω) 1 (θ₁ * QuantumZipper.chiC κ) (QuantumZipper.chiC κ)
            (g ω + SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀) ψ =
          ∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal) Q
            (LocalExt.bheAt κ ρL ρR (flowL W Q xL) (flowR W Q xR)) z * ψ z :=
  ae_chartTransport_lineMean hL75 hL77 hA56 hκ hκ4 hb hx hθ hh hη₁ hη₂ hd hζ₁ hζ₂ hae hu₀
    (isBoxChartBoundaryLimit_word hL75 hL77 hA56 hκ hκ4 hb hx hθ hh hη₁ hη₂ hd hζ₁ hζ₂ hae hu₀ hc₀ hc₀J hc₀b
      (isBoxSideLimit_of_flowLines hL75 hL77 hA56 hκ hκ4 hb hx hθ hh hη₁ hη₂ hd hζ₁ hζ₂ hae hu₀))
    (isFCSideLimit_of_sign hL75 hL77 hA56 hκ hκ4 hb hx hθ hh hη₁ hη₂ hd hζ₁ hζ₂ hae hu₀ hsign)
    m t hc₁ hc₂ hm₁ hm₂ hag₁ hag₂ hg

end Main

end Restart.FCAux79

end InteractingSLE
