/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideHeightBoxJoint
import InteractingSLE.Spec.Sec7.SideHeightBoxProb
import InteractingSLE.Spec.Sec7.Lemma78MeanWordMeas

/-!
# Lemma 7.8's exposed-side heights in the first-contact chart: `IsBoxSideLimit`

Packet PROVE-SIDEHEIGHT2 (specification Lemma 7.8 and its proof, pp. 290–294). In the first-contact chart `ψ` of two
flow lines `η₁` (angle `θ₁`, seed `x₁`) and `η₂` (angle `θ₂`, seed `x₂ < x₁`), the conditional mean of the field given
the first-contact union `K` tends, at every chart point `w ∈ (0, R)`, to `λ − θ₁χ` and, at every `w ∈ (L, 0)`, to
`−λ − θ₂χ` (`isBoxSideLimit_of_flowLines`; the finite exceptional set is empty). Consequently Lemma 7.8's mean
formula holds on every box for a retained-measurable sorted boundary word (`exists_isBoxMeanIdentification`, the mean
part of `FirstContactWordKernelStatement`).

## Proof at a chart point `w ∈ (0, R)`

* **Geometry** (`SideHeightBoxJoint`): `ψ(w) = η₁(s)` with `s < s₀`; a real `ψ(w)` lies left of `x₁`; near `ψ(w)` the
  first-contact compact is the prefix `η₁([0, q])` for a rational stop `s < q < s₀` with interior tip, and the real
  points adherent to the domain lie on `η₁`.
* **Side** (`SideHeightBoxSign`): along every approach (an ultrafilter `V` at `ψ(w)` from the domain `D`) the chart
  `f_q(· − x₁)` tends to some `y > 0`.
* **Single path** (`SideHeightBoxSingle`): the range mean of `η₁([0, q])` has height `λ − θ₁χ` along `V`.
* **Comparison** (`SideHeightBoxProb`, Proposition 3.8 twice): the union mean minus the range mean tends to `0`.
* **Lift** (Aux. lemma 57): the first-contact lift minus the single-path lift tends to `0`.

The left side is the mirror image (`f_q(· − x₂)` tends to a negative limit, height `−λ − θ₂χ`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric Bornology Complex
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Sec7

namespace SideHeightBox

open QuantumZipper (H Hbar fwdMap fwdHull)
open LQGMetric (DistOn TestOn)
open LocalSets Sec6 Restart HalfPlaneSep

/-! ### Congruences -/

theorem isGeneratingTrace_congr {w : ℝ≥0 → ℝ} {T : ℝ≥0∞} {γ γ' : ℝ≥0 → ℂ} (hg : IsGeneratingTrace w T γ)
    (he : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ T → γ' t = γ t) : IsGeneratingTrace w T γ' := by
  obtain ⟨h0, hc, hf⟩ := hg
  refine ⟨by rw [he 0 (by simp)]; exact h0, hc.congr fun t ht => he t ht, fun t ht => ?_⟩
  have : γ' '' Icc 0 t = γ '' Icc 0 t :=
    image_congr fun s hs => he s ((ENNReal.coe_le_coe.2 hs.2).trans ht.le)
  rw [this]
  exact hf t ht

theorem isPathGood_congr {η η' : ℝ≥0 → ℂ} {ζ : ℝ≥0∞} {x : ℝ} (hp : IsPathGood η ζ x)
    (he : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ → η' t = η t) : IsPathGood η' ζ x := by
  obtain ⟨hi, w, hw, hw0, hg⟩ := hp
  exact ⟨hi.congr fun t ht => (he t ht).symm, w, hw, hw0, isGeneratingTrace_congr hg fun t ht => by
    simp only [he t ht]⟩


/-! ### The pathwise argument at a chart point of an exposed side -/

section Pathwise

variable {Ω : Type*} [MeasurableSpace Ω] {d : PairData Ω}

theorem mem_union_real_of_mem_K (hd : d.IsMeasGood) {ω : Ω} (hE : ω ∈ d.E) {S : Set ℂ} {p : ℂ}
    (hpK : p ∈ d.K ω) (hS : p ∈ H → p ∈ S) : p ∈ S ∪ {z : ℂ | z.im = 0} := by
  by_cases hpH : p ∈ H
  · exact Or.inl (hS hpH)
  · right
    have hHbar : 0 ≤ p.im := by
      rw [PairData.K_of_mem hE] at hpK
      obtain ⟨-, -, hH₁, hH₂, -⟩ := hd.pathFacts hE
      rcases hpK with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
      exacts [hH₁ ht, hH₂ ht]
    exact le_antisymm (not_lt.1 hpH) hHbar

/-- **The height on the right side at one chart point** (pathwise; the inputs are the almost sure statements at the
rational stops: the comparison `hcmp`, the single-path heights `hsh` and the harmonic representatives `hrep`). -/
theorem tendsto_side_right (hd : d.IsMeasGood) {ω : Ω} (hE : ω ∈ d.E) {κ x₁ x₂ hR : ℝ} (hx : x₂ < x₁) {m : ℝ≥0}
    (hs₀m : d.s₀ ω < m) (hs₀ζ : (d.s₀ ω : ℝ≥0∞) < d.ζ₁ ω)
    (hp₁ : IsPathGood (d.η₁ ω) (d.ζ₁ ω) x₁) (hp₂ : IsPathGood (d.η₂ ω) (d.ζ₂ ω) x₂) {W : ℝ≥0 → ℝ}
    (hg : IsGeneratingTrace W (d.ζ₁ ω) (fun t => d.η₁ ω t - x₁)) (hWc : ContinuousOn W {s | (s : ℝ≥0∞) < d.ζ₁ ω})
    (hW0 : W 0 = 0) {B : Set ℂ} (hB : B = d.K ω ∩ H) {A : ℝ≥0 → Set ℂ}
    (hA : ∀ q : ℝ≥0, q ≤ m → (q : ℝ≥0∞) < d.ζ₁ ω → A q = d.η₁ ω '' Icc 0 q ∩ H) {u₀ v : ℂ → ℝ}
    (hv : InnerProductSpace.HarmonicOnNhd v (H \ B)) {g : DistOn upperHalfPlaneOpens}
    (hvr : ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ B → g φ = ∫ z, v z * φ z)
    {G : ℚ → DistOn upperHalfPlaneOpens} (hrep : ∀ r : ℚ, IsHarmonicDistOn (G r) (H \ A (r : ℝ).toNNReal))
    (hcmp : ∀ r : ℚ, ∀ vB vA : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd vB (H \ B) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ B → g φ = ∫ z, vB z * φ z) →
      InnerProductSpace.HarmonicOnNhd vA (H \ A (r : ℝ).toNNReal) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A (r : ℝ).toNNReal → G r φ = ∫ z, vA z * φ z) →
      ∀ p : ℂ, p ∈ B ∪ {z : ℂ | z.im = 0} → p ∈ A (r : ℝ).toNNReal ∪ {z : ℂ | z.im = 0} →
      (∃ ρ > 0, A (r : ℝ).toNNReal ∩ ball p ρ ⊆ B) → (∃ ρ > 0, B ∩ ball p ρ ⊆ A (r : ℝ).toNNReal) →
      Tendsto (fun z => vB z - vA z) (𝓝[H \ (B ∪ A (r : ℝ).toNNReal)] p) (𝓝 0))
    (hsh : ∀ r : ℚ, (r : ℝ).toNNReal ≤ m → (((r : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) < d.ζ₁ ω → ∀ vA : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd vA (H \ A (r : ℝ).toNNReal) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A (r : ℝ).toNNReal → G r φ = ∫ z, vA z * φ z) →
      ∀ (p : ℂ) (F : Filter ℂ), F.NeBot → F ≤ 𝓝[H \ fillH (d.η₁ ω '' Icc 0 (r : ℝ).toNNReal)] p → ∀ y : ℝ,
        Tendsto (fun z => fwdMap (fun s : ℝ => W s.toNNReal) (r : ℝ).toNNReal (z - x₁)) F (𝓝 (y : ℂ)) →
        0 < y → ¬ ((p - x₁).im = 0 ∧ 0 ≤ (p - x₁).re) →
        Tendsto (fun z => vA z + u₀ z + QuantumZipper.chiC κ *
          (QuantumZipper.logDerivFwd (fun s : ℝ => W s.toNNReal) (r : ℝ).toNNReal (z - x₁)).im) F (𝓝 hR))
    {w : ℝ} (hw0 : 0 < w) (hwR : w < d.wordR ω) :
    Tendsto (fun z => v (d.inv ω z) + u₀ (d.inv ω z) + QuantumZipper.chiC κ * d.lift ω (d.inv ω z))
      (𝓝[H] (w : ℂ)) (𝓝 hR) := by
  have hfc := hd.isFirstContact hE
  obtain ⟨s, hs, hse, hreal_lt⟩ := exists_inv_eq_right' hd hE hp₁ hp₂ hx hw0 hwR
  obtain ⟨r, hr1, hr2, hr3⟩ := IsPathGood.exists_rat_mem_H hp₁ hs hfc.1
  set q := (r : ℝ).toNNReal with hqdef
  have hqm : q ≤ m := (hr2.trans hs₀m).le
  have hqζ : (q : ℝ≥0∞) < d.ζ₁ ω := (ENNReal.coe_lt_coe.2 hr2).trans hs₀ζ
  have hq0 : 0 < q := lt_of_le_of_lt zero_le hr1
  set p := d.inv ω w with hpdef
  have hKeq : d.K ω = d.η₁ ω '' Icc 0 (d.s₀ ω) ∪ d.η₂ ω '' Icc 0 (d.t₀ ω) := by
    rw [PairData.K_of_mem hE, prefixSet]
  have hdisj : ∀ t < d.t₀ ω, d.η₂ ω t ∉ d.η₁ ω '' Icc 0 (d.s₀ ω) := by
    rintro t ht ⟨u, hu, hue⟩
    exact (ne_of_lt ht) (meet_eq_contact hd hE u t hu.2 ht.le hue).2
  obtain ⟨ρ, hρ, hloc⟩ := exists_ball_inter_subset hp₁ hp₂ hfc.1 hfc.2.1 hfc.2.2.1.symm hdisj hr1 hr2.le
  rw [← hKeq, ← hse] at hloc
  obtain ⟨r₁, hr₁, hreal⟩ := exists_ball_real_right hd hE hp₁ hp₂ hx hw0 hwR
  have hD : d.D ω = H \ fillH (d.η₁ ω '' Icc 0 (d.s₀ ω) ∪ d.η₂ ω '' Icc 0 (d.t₀ ω)) := by
    rw [PairData.D, hKeq]
  have hsubK : d.η₁ ω '' Icc 0 q ⊆ d.K ω :=
    hKeq ▸ (image_mono (Icc_subset_Icc_right hr2.le)).trans subset_union_left
  have hDA : d.D ω ⊆ H \ fillH (d.η₁ ω '' Icc 0 q) := sdiff_subset_sdiff_right (fillH_mono hsubK)
  have hAq := hA q hqm hqζ
  have hAB : A q ⊆ B := by
    rw [hAq, hB]
    exact inter_subset_inter_left _ hsubK
  have hBA : B ∩ ball p ρ ⊆ A q := by
    rw [hAq, hB]
    rintro z ⟨⟨hzK, hzH⟩, hzb⟩
    exact ⟨hloc ⟨hzK, hzb⟩, hzH⟩
  have hDB : d.D ω ⊆ H \ (B ∪ A q) := by
    rw [union_eq_left.2 hAB, hB]
    intro z hz
    exact ⟨hz.1, fun h => hz.2 ⟨h.2, Or.inl (subset_closure h.1)⟩⟩
  have hpK : p ∈ d.K ω := hd.inv_mem_K_of_mem_Icc hE ((hd.wordL_nonpos hE).trans hw0.le) hwR.le
  have hpB : p ∈ B ∪ {z : ℂ | z.im = 0} :=
    mem_union_real_of_mem_K hd hE hpK fun hpH => by rw [hB]; exact ⟨hpK, hpH⟩
  have hpA : p ∈ A q ∪ {z : ℂ | z.im = 0} :=
    mem_union_real_of_mem_K hd hE hpK fun hpH => by rw [hAq, hse]; exact ⟨⟨s, ⟨zero_le, hr1.le⟩, rfl⟩, hse ▸ hpH⟩
  obtain ⟨vA, hvA, hvAr⟩ := hrep r
  have hcmp' := hcmp r v vA hv hvr hvA hvAr p hpB hpA ⟨1, one_pos, fun z hz => hAB hz.1⟩ ⟨ρ, hρ, hBA⟩
  -- along every approach
  rw [tendsto_iff_ultrafilter]
  intro U hU
  set V := U.map (d.inv ω) with hVdef
  have hV : (V : Filter ℂ) ≤ 𝓝[d.D ω] p := by
    rw [hVdef, Ultrafilter.coe_map]
    exact (map_mono hU).trans (hd.tendsto_inv_real hE w).1
  have hch := isPhysChart hg hWc hW0 hp₁.1 hqζ hq0
  obtain ⟨y, hfy, -⟩ := hch.exists_real_tendsto ⟨s, ⟨zero_le, hr1.le⟩, hse.symm⟩ V (hV.trans (nhdsWithin_mono _ hDA))
  have hy : 0 < y := by
    refine pos_of_approach_gen hp₁ hp₂ hx hg hWc hW0 hs₀ζ hfc.2.1 hfc.2.2.1.symm hdisj hr1 hr2 hr3 hr₁
      (fun z hz hzim hzcl => ?_) V ?_ hfy
    · rw [← hD] at hzcl
      rw [← hse] at hz
      exact hreal z hz hzim hzcl
    · rw [← hD, ← hse]
      exact hV
  have hpR : ¬ ((p - x₁).im = 0 ∧ 0 ≤ (p - x₁).re) := by
    rintro ⟨h1, h2⟩
    have him : p.im = 0 := by simpa using h1
    have := hreal_lt him
    simp only [sub_re, ofReal_re] at h2
    linarith
  have h1 := hsh r hqm hqζ vA hvA hvAr p V inferInstance (hV.trans (nhdsWithin_mono _ hDA)) y hfy hy hpR
  have h2 := tendsto_lift_sub hd ω hg hWc hW0 hp₁.1 hqζ hq0 hsubK hρ hloc V hV hfy
  have h3 := hcmp'.mono_left (hV.trans (nhdsWithin_mono _ hDB))
  have hsum := h3.add (h1.add (h2.const_mul (QuantumZipper.chiC κ)))
  rw [zero_add, mul_zero, add_zero] at hsum
  have hfin : Tendsto (fun z => v z + u₀ z + QuantumZipper.chiC κ * d.lift ω z) (V : Filter ℂ) (𝓝 hR) :=
    hsum.congr fun z => by ring
  rw [hVdef, Ultrafilter.coe_map] at hfin
  exact tendsto_map'_iff.1 hfin

/-- **The height on the left side at one chart point** (the mirror image of `tendsto_side_right`). -/
theorem tendsto_side_left (hd : d.IsMeasGood) {ω : Ω} (hE : ω ∈ d.E) {κ x₁ x₂ hL : ℝ} (hx : x₂ < x₁) {m : ℝ≥0}
    (ht₀m : d.t₀ ω < m) (ht₀ζ : (d.t₀ ω : ℝ≥0∞) < d.ζ₂ ω)
    (hp₁ : IsPathGood (d.η₁ ω) (d.ζ₁ ω) x₁) (hp₂ : IsPathGood (d.η₂ ω) (d.ζ₂ ω) x₂) {W : ℝ≥0 → ℝ}
    (hg : IsGeneratingTrace W (d.ζ₂ ω) (fun t => d.η₂ ω t - x₂)) (hWc : ContinuousOn W {s | (s : ℝ≥0∞) < d.ζ₂ ω})
    (hW0 : W 0 = 0) {B : Set ℂ} (hB : B = d.K ω ∩ H) {A : ℝ≥0 → Set ℂ}
    (hA : ∀ q : ℝ≥0, q ≤ m → (q : ℝ≥0∞) < d.ζ₂ ω → A q = d.η₂ ω '' Icc 0 q ∩ H) {u₀ v : ℂ → ℝ}
    (hv : InnerProductSpace.HarmonicOnNhd v (H \ B)) {g : DistOn upperHalfPlaneOpens}
    (hvr : ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ B → g φ = ∫ z, v z * φ z)
    {G : ℚ → DistOn upperHalfPlaneOpens} (hrep : ∀ r : ℚ, IsHarmonicDistOn (G r) (H \ A (r : ℝ).toNNReal))
    (hcmp : ∀ r : ℚ, ∀ vB vA : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd vB (H \ B) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ B → g φ = ∫ z, vB z * φ z) →
      InnerProductSpace.HarmonicOnNhd vA (H \ A (r : ℝ).toNNReal) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A (r : ℝ).toNNReal → G r φ = ∫ z, vA z * φ z) →
      ∀ p : ℂ, p ∈ B ∪ {z : ℂ | z.im = 0} → p ∈ A (r : ℝ).toNNReal ∪ {z : ℂ | z.im = 0} →
      (∃ ρ > 0, A (r : ℝ).toNNReal ∩ ball p ρ ⊆ B) → (∃ ρ > 0, B ∩ ball p ρ ⊆ A (r : ℝ).toNNReal) →
      Tendsto (fun z => vB z - vA z) (𝓝[H \ (B ∪ A (r : ℝ).toNNReal)] p) (𝓝 0))
    (hsh : ∀ r : ℚ, (r : ℝ).toNNReal ≤ m → (((r : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) < d.ζ₂ ω → ∀ vA : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd vA (H \ A (r : ℝ).toNNReal) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A (r : ℝ).toNNReal → G r φ = ∫ z, vA z * φ z) →
      ∀ (p : ℂ) (F : Filter ℂ), F.NeBot → F ≤ 𝓝[H \ fillH (d.η₂ ω '' Icc 0 (r : ℝ).toNNReal)] p → ∀ y : ℝ,
        Tendsto (fun z => fwdMap (fun s : ℝ => W s.toNNReal) (r : ℝ).toNNReal (z - x₂)) F (𝓝 (y : ℂ)) →
        y < 0 → ¬ ((p - x₂).im = 0 ∧ (p - x₂).re ≤ 0) →
        Tendsto (fun z => vA z + u₀ z + QuantumZipper.chiC κ *
          (QuantumZipper.logDerivFwd (fun s : ℝ => W s.toNNReal) (r : ℝ).toNNReal (z - x₂)).im) F (𝓝 hL))
    {w : ℝ} (hwL : d.wordL ω < w) (hw0 : w < 0) :
    Tendsto (fun z => v (d.inv ω z) + u₀ (d.inv ω z) + QuantumZipper.chiC κ * d.lift ω (d.inv ω z))
      (𝓝[H] (w : ℂ)) (𝓝 hL) := by
  have hfc := hd.isFirstContact hE
  obtain ⟨s, hs, hse, hreal_lt⟩ := exists_inv_eq_left' hd hE hp₁ hp₂ hx hwL hw0
  obtain ⟨r, hr1, hr2, hr3⟩ := IsPathGood.exists_rat_mem_H hp₂ hs hfc.2.1
  set q := (r : ℝ).toNNReal with hqdef
  have hqm : q ≤ m := (hr2.trans ht₀m).le
  have hqζ : (q : ℝ≥0∞) < d.ζ₂ ω := (ENNReal.coe_lt_coe.2 hr2).trans ht₀ζ
  have hq0 : 0 < q := lt_of_le_of_lt zero_le hr1
  set p := d.inv ω w with hpdef
  have hKeq : d.K ω = d.η₁ ω '' Icc 0 (d.s₀ ω) ∪ d.η₂ ω '' Icc 0 (d.t₀ ω) := by
    rw [PairData.K_of_mem hE, prefixSet]
  have hdisj : ∀ t < d.s₀ ω, d.η₁ ω t ∉ d.η₂ ω '' Icc 0 (d.t₀ ω) := by
    rintro t ht ⟨u, hu, hue⟩
    exact (ne_of_lt ht) (meet_eq_contact hd hE t u ht.le hu.2 hue.symm).1
  obtain ⟨ρ, hρ, hloc⟩ := exists_ball_inter_subset hp₂ hp₁ hfc.2.1 hfc.1 hfc.2.2.1 hdisj hr1 hr2.le
  rw [union_comm, ← hKeq, ← hse] at hloc
  obtain ⟨r₁, hr₁, hreal⟩ := exists_ball_real_left hd hE hp₁ hp₂ hx hwL hw0
  have hD : d.D ω = H \ fillH (d.η₁ ω '' Icc 0 (d.s₀ ω) ∪ d.η₂ ω '' Icc 0 (d.t₀ ω)) := by
    rw [PairData.D, hKeq]
  have hsubK : d.η₂ ω '' Icc 0 q ⊆ d.K ω :=
    hKeq ▸ (image_mono (Icc_subset_Icc_right hr2.le)).trans subset_union_right
  have hDA : d.D ω ⊆ H \ fillH (d.η₂ ω '' Icc 0 q) := sdiff_subset_sdiff_right (fillH_mono hsubK)
  have hAq := hA q hqm hqζ
  have hAB : A q ⊆ B := by
    rw [hAq, hB]
    exact inter_subset_inter_left _ hsubK
  have hBA : B ∩ ball p ρ ⊆ A q := by
    rw [hAq, hB]
    rintro z ⟨⟨hzK, hzH⟩, hzb⟩
    exact ⟨hloc ⟨hzK, hzb⟩, hzH⟩
  have hDB : d.D ω ⊆ H \ (B ∪ A q) := by
    rw [union_eq_left.2 hAB, hB]
    intro z hz
    exact ⟨hz.1, fun h => hz.2 ⟨h.2, Or.inl (subset_closure h.1)⟩⟩
  have hpK : p ∈ d.K ω := hd.inv_mem_K_of_mem_Icc hE hwL.le (hw0.le.trans (hd.wordR_nonneg hE))
  have hpB : p ∈ B ∪ {z : ℂ | z.im = 0} :=
    mem_union_real_of_mem_K hd hE hpK fun hpH => by rw [hB]; exact ⟨hpK, hpH⟩
  have hpA : p ∈ A q ∪ {z : ℂ | z.im = 0} :=
    mem_union_real_of_mem_K hd hE hpK fun hpH => by rw [hAq, hse]; exact ⟨⟨s, ⟨zero_le, hr1.le⟩, rfl⟩, hse ▸ hpH⟩
  obtain ⟨vA, hvA, hvAr⟩ := hrep r
  have hcmp' := hcmp r v vA hv hvr hvA hvAr p hpB hpA ⟨1, one_pos, fun z hz => hAB hz.1⟩ ⟨ρ, hρ, hBA⟩
  -- along every approach
  rw [tendsto_iff_ultrafilter]
  intro U hU
  set V := U.map (d.inv ω) with hVdef
  have hV : (V : Filter ℂ) ≤ 𝓝[d.D ω] p := by
    rw [hVdef, Ultrafilter.coe_map]
    exact (map_mono hU).trans (hd.tendsto_inv_real hE w).1
  have hch := isPhysChart hg hWc hW0 hp₂.1 hqζ hq0
  obtain ⟨y, hfy, -⟩ := hch.exists_real_tendsto ⟨s, ⟨zero_le, hr1.le⟩, hse.symm⟩ V (hV.trans (nhdsWithin_mono _ hDA))
  have hy : y < 0 := by
    refine neg_of_approach_gen hp₁ hp₂ hx hg hWc hW0 ht₀ζ hfc.1 hfc.2.2.1 hdisj hr1 hr2 hr3 hr₁
      (fun z hz hzim hzcl => ?_) V ?_ hfy
    · rw [← hD] at hzcl
      rw [← hse] at hz
      exact hreal z hz hzim hzcl
    · rw [← hD, ← hse]
      exact hV
  have hpR : ¬ ((p - x₂).im = 0 ∧ (p - x₂).re ≤ 0) := by
    rintro ⟨h1, h2⟩
    have him : p.im = 0 := by simpa using h1
    have := hreal_lt him
    simp only [sub_re, ofReal_re] at h2
    linarith
  have h1 := hsh r hqm hqζ vA hvA hvAr p V inferInstance (hV.trans (nhdsWithin_mono _ hDA)) y hfy hy hpR
  have h2 := tendsto_lift_sub hd ω hg hWc hW0 hp₂.1 hqζ hq0 hsubK hρ hloc V hV hfy
  have h3 := hcmp'.mono_left (hV.trans (nhdsWithin_mono _ hDB))
  have hsum := h3.add (h1.add (h2.const_mul (QuantumZipper.chiC κ)))
  rw [zero_add, mul_zero, add_zero] at hsum
  have hfin : Tendsto (fun z => v z + u₀ z + QuantumZipper.chiC κ * d.lift ω z) (V : Filter ℂ) (𝓝 hL) :=
    hsum.congr fun z => by ring
  rw [hVdef, Ultrafilter.coe_map] at hfin
  exact tendsto_map'_iff.1 hfin

end Pathwise


/-! ### `IsBoxSideLimit` -/

section Main

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x₁ x₂ θ₁ θ₂ : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {η₁ η₂ : Ω → ℝ≥0 → ℂ}
  {ζ₁ ζ₂ : Ω → ℝ≥0∞}

/-- **Lemma 7.8's exposed-side heights in the first-contact chart** (`IsBoxSideLimit` with `hL = −λ − θ₂χ`,
`hR = λ − θ₁χ`, specification p. 293), in the setting of `FirstContactWordKernelStatement`, from the named inputs of
the glued (R1) (Lemma 7.5, Lemma 7.7, Aux. lemma 56 at first entrances). The exceptional set is empty. -/
theorem isBoxSideLimit_of_flowLines (hL75 : Theorem15.Lemma75Statement.{u})
    (hL77 : Supp10.Lemma77Statement.{u}) (hA56 : RetainedRangeEntranceStatement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hx : x₂ < x₁) (hθ : θ₁ < θ₂ + Real.pi)
    (hh : IsGFFWithBoundaryData P h b jumps) (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁)
    (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂) {d : PairData Ω} (hd : d.IsMeasGood) (hζ₁ : d.ζ₁ = ζ₁)
    (hζ₂ : d.ζ₂ = ζ₂)
    (hae : ∀ᵐ ω ∂P, ω ∈ d.G ∧ (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → d.η₁ ω s = η₁ ω s) ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ₂ ω → d.η₂ ω t = η₂ ω t)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) :
    IsBoxSideLimit κ P h η₁ η₂ ζ₁ ζ₂ u₀ d (-sleLambda κ - θ₂ * QuantumZipper.chiC κ)
      (sleLambda κ - θ₁ * QuantumZipper.chiC κ) := by
  intro m ηc₁ ηc₂ g hc₁ hc₂ hm₁ hm₂ hag₁ hag₂ hg
  subst hζ₁ hζ₂
  classical
  have hh0 := isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀
  obtain ⟨hBm, hBloc, hBdet, hBunb⟩ :=
    fcUnion_facts hL75 hL77 hA56 hκ hκ4 hb hx hθ hh hη₁ hη₂ hu₀ (m : ℝ≥0) hc₁ hc₂ hm₁ hm₂ hag₁ hag₂
  have hF₁ := fun q : ℝ≥0 => range_facts hL75 hA56 hκ hκ4 hb hh hη₁ hu₀ (m : ℝ≥0) q hc₁ hm₁ hag₁
  have hF₂ := fun q : ℝ≥0 => range_facts hL75 hA56 hκ hκ4 hb hh hη₂ hu₀ (m : ℝ≥0) q hc₂ hm₂ hag₂
  have hmean₁ : ∀ r : ℚ, ∃ G, IsLocalSetMean (fun ω => ηc₁ ω '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ (r : ℝ).toNNReal} ∩ H)
      (WholeField.centredField h u₀) P G := fun r =>
    IsLocalSet.exists_isLocalSetMean hh0 (hF₁ _).1 (hF₁ _).2.1
  have hmean₂ : ∀ r : ℚ, ∃ G, IsLocalSetMean (fun ω => ηc₂ ω '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ (r : ℝ).toNNReal} ∩ H)
      (WholeField.centredField h u₀) P G := fun r =>
    IsLocalSet.exists_isLocalSetMean hh0 (hF₂ _).1 (hF₂ _).2.1
  choose G₁ hG₁ using hmean₁
  choose G₂ hG₂ using hmean₂
  obtain ⟨_, _, W₁, _, _, _, -, hcoup₁, htr₁⟩ := id hη₁
  obtain ⟨_, _, W₂, _, _, _, -, hcoup₂, htr₂⟩ := id hη₂
  have hC₁ := fun r : ℚ => ae_tendsto_sub_of_locals hh0 hBm (hF₁ _).1 hBloc (hF₁ _).2.1 hBdet (hF₁ _).2.2.1 hBunb
    (hF₁ _).2.2.2 hg (hG₁ r)
  have hC₂ := fun r : ℚ => ae_tendsto_sub_of_locals hh0 hBm (hF₂ _).1 hBloc (hF₂ _).2.1 hBdet (hF₂ _).2.2.1 hBunb
    (hF₂ _).2.2.2 hg (hG₂ r)
  have hS₁ := fun r : ℚ => singlePathSideHeight_gen (m := (m : ℝ≥0)) (q := (r : ℝ).toNNReal) hL75 hA56 hκ hκ4 hb hh
    hη₁ htr₁ hu₀
  have hS₂ := fun r : ℚ => singlePathSideHeight_gen (m := (m : ℝ≥0)) (q := (r : ℝ).toNNReal) hL75 hA56 hκ hκ4 hb hh
    hη₂ htr₂ hu₀
  have hS₁' : ∀ r : ℚ, ∀ᵐ ω ∂P, (r : ℝ).toNNReal ≤ (m : ℝ≥0) → _ := fun r => by
    by_cases hrm : (r : ℝ).toNNReal ≤ (m : ℝ≥0)
    · filter_upwards [hS₁ r hrm hc₁ hm₁ hag₁ (hG₁ r)] with ω hω _
      exact hω
    · exact Eventually.of_forall fun ω h => absurd h hrm
  have hS₂' : ∀ r : ℚ, ∀ᵐ ω ∂P, (r : ℝ).toNNReal ≤ (m : ℝ≥0) → _ := fun r => by
    by_cases hrm : (r : ℝ).toNNReal ≤ (m : ℝ≥0)
    · filter_upwards [hS₂ r hrm hc₂ hm₂ hag₂ (hG₂ r)] with ω hω _
      exact hω
    · exact Eventually.of_forall fun ω h => absurd h hrm
  have hpg₁ := ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₁
  have hpg₂ := ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₂
  have hcmp := ae_retHist_eq_fcHist hd hc₁ hc₂ m hae hag₁ hag₂
  filter_upwards [hae, hag₁, hag₂, hcmp, hpg₁, hpg₂, htr₁, htr₂, hcoup₁.1.2.2.2.2, hcoup₂.1.2.2.2.2,
    ae_all_iff.2 hC₁, ae_all_iff.2 hC₂, ae_all_iff.2 hS₁', ae_all_iff.2 hS₂', ae_all_iff.2 fun r => (hG₁ r).2.1,
    ae_all_iff.2 fun r => (hG₂ r).2.1]
    with ω ⟨_, ha₁, ha₂⟩ hag₁ω hag₂ω ⟨_, heq⟩ hp₁ω hp₂ω htr₁ω htr₂ω hpath₁ hpath₂ hC₁ω hC₂ω hS₁ω hS₂ω hR₁ω hR₂ω
    hbox v hv hvrep
  obtain ⟨hE, hs₀m, ht₀m, hs₀ζ, ht₀ζ⟩ := mem_meetBox_iff.1 hbox
  have hp₁ : IsPathGood (d.η₁ ω) (d.ζ₁ ω) x₁ := isPathGood_congr hp₁ω fun t ht => ha₁ t ht
  have hp₂ : IsPathGood (d.η₂ ω) (d.ζ₂ ω) x₂ := isPathGood_congr hp₂ω fun t ht => ha₂ t ht
  have hg₁ : IsGeneratingTrace (fun t => W₁ t ω) (d.ζ₁ ω) (fun t => d.η₁ ω t - x₁) :=
    isGeneratingTrace_congr htr₁ω fun t ht => by simp only [ha₁ t ht]
  have hg₂ : IsGeneratingTrace (fun t => W₂ t ω) (d.ζ₂ ω) (fun t => d.η₂ ω t - x₂) :=
    isGeneratingTrace_congr htr₂ω fun t ht => by simp only [ha₂ t ht]
  have hfcU : fcUnion ηc₁ ηc₂ ω = d.K ω ∩ H := fcUnion_eq_K_of_good m hbox ha₁ ha₂ hag₁ω hag₂ω (heq hbox)
  have himg₁ : ∀ q : ℝ≥0, (q : ℝ≥0∞) < d.ζ₁ ω → η₁ ω '' Icc 0 q = d.η₁ ω '' Icc 0 q := fun q hq =>
    image_congr fun t ht => (ha₁ t ((ENNReal.coe_le_coe.2 ht.2).trans hq.le)).symm
  have himg₂ : ∀ q : ℝ≥0, (q : ℝ≥0∞) < d.ζ₂ ω → η₂ ω '' Icc 0 q = d.η₂ ω '' Icc 0 q := fun q hq =>
    image_congr fun t ht => (ha₂ t ((ENNReal.coe_le_coe.2 ht.2).trans hq.le)).symm
  have hA₁ : ∀ q : ℝ≥0, q ≤ (m : ℝ≥0) → (q : ℝ≥0∞) < d.ζ₁ ω →
      ηc₁ ω '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ q} ∩ H = d.η₁ ω '' Icc 0 q ∩ H := fun q hqm hq => by
    rw [image_capped_eq hag₁ω (le_min hq.le (ENNReal.coe_le_coe.2 hqm)), himg₁ q hq]
  have hA₂ : ∀ q : ℝ≥0, q ≤ (m : ℝ≥0) → (q : ℝ≥0∞) < d.ζ₂ ω →
      ηc₂ ω '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ q} ∩ H = d.η₂ ω '' Icc 0 q ∩ H := fun q hqm hq => by
    rw [image_capped_eq hag₂ω (le_min hq.le (ENNReal.coe_le_coe.2 hqm)), himg₂ q hq]
  refine ⟨∅, finite_empty, fun w _ => ⟨fun hwL hw0 => ?_, fun hw0 hwR => ?_⟩⟩
  · refine tendsto_side_left hd hE hx ht₀m ht₀ζ hp₁ hp₂ hg₂ hpath₂.2.2.2.1 hpath₂.1 hfcU
      (A := fun q => ηc₂ ω '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ q} ∩ H) hA₂ hv hvrep (G := fun r => G₂ r ω) hR₂ω hC₂ω
      (fun r hrm hrζ vA hvA hvAr p F hF hFle y hy hy0 hpL => ?_) hwL hw0
    rw [← himg₂ _ hrζ] at hFle
    exact ((hS₂ω r hrm hrζ vA hvA hvAr p F hF hFle y hy).2 hy0 hpL)
  · refine tendsto_side_right hd hE hx hs₀m hs₀ζ hp₁ hp₂ hg₁ hpath₁.2.2.2.1 hpath₁.1 hfcU
      (A := fun q => ηc₁ ω '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ q} ∩ H) hA₁ hv hvrep (G := fun r => G₁ r ω) hR₁ω hC₁ω
      (fun r hrm hrζ vA hvA hvAr p F hF hFle y hy hy0 hpR => ?_) hw0 hwR
    rw [← himg₁ _ hrζ] at hFle
    exact ((hS₁ω r hrm hrζ vA hvA hvAr p F hF hFle y hy).1 hy0 hpR)

/-- **The mean part of `FirstContactWordKernelStatement`** (Lemma 7.8's mean formula on every box): in its setting
there is a `retSigma d P`-measurable boundary datum, sorted on the meeting branch, with `IsBoxMeanIdentification`
(PROVE-PRIMEEND2's `exists_isBoxMeanIdentification_of_sideLimit` with the exposed-side heights proved here). -/
theorem exists_isBoxMeanIdentification (hL75 : Theorem15.Lemma75Statement.{u})
    (hL77 : Supp10.Lemma77Statement.{u}) (hA56 : RetainedRangeEntranceStatement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hx : x₂ < x₁) (hθ : θ₁ < θ₂ + Real.pi)
    (hh : IsGFFWithBoundaryData P h b jumps) (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁)
    (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂) {d : PairData Ω} (hd : d.IsMeasGood) (hζ₁ : d.ζ₁ = ζ₁)
    (hζ₂ : d.ζ₂ = ζ₂)
    (hae : ∀ᵐ ω ∂P, ω ∈ d.G ∧ (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → d.η₁ ω s = η₁ ω s) ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ₂ ω → d.η₂ ω t = η₂ ω t)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) :
    ∃ β : Ω → BoundaryWord, Measurable[retSigma d P] β ∧ (∀ᵐ ω ∂P, ω ∈ meetSet d → (β ω).IsSorted) ∧
      IsBoxMeanIdentification κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd β :=
  exists_isBoxMeanIdentification_of_sideLimit hL75 hL77 hA56 hκ hκ4 hb hx hθ hh hη₁ hη₂ hd hζ₁ hζ₂ hae hu₀
    (isBoxSideLimit_of_flowLines hL75 hL77 hA56 hκ hκ4 hb hx hθ hh hη₁ hη₂ hd hζ₁ hζ₂ hae hu₀)

end Main

end SideHeightBox

end Sec7

end InteractingSLE
