/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61Conf2Word
import InteractingSLE.Spec.Sec5.Aux61SlitVChart
import InteractingSLE.Spec.Sec5.Aux61MeanIdSlit
import InteractingSLE.Spec.Supplement.CounterflowRange

/-!
# Aux. 61 at the glued stop, IV: the slit-side boundary data and (K-b)

Packet PROVE-AUX61-CONFIG. Assembly of PROVE-AUX61-SLIT's comparison with the deterministic two-sides calculation:

* **`IsGluedSlit.tendsto_slit_sub_meanF`** (per sample, deterministic): given SLIT's comparison conclusion `hconv`
  (the output of `Aux61SlitV.ae_tendsto_chart_sub_flowMean` at one sample, with height offset `a = 0` and lift
  coefficient `k = χ`), a cover of the continuation by comparison indices (rational comparison times `ρ i` strictly
  between each continuation time and the chart time, with `A ⊆ L i` near the continuation point), the physical flow
  line's means `M₂ i = couplingMean κ Wph (ρ i) (uph i)` on `D` with side heights `bL`/`bR`, the chart word with the
  same side heights at the chart slit, and a cutoff of the correction: a harmonic representative `v` satisfies
  `v ∘ F_t − meanF ∘ F_t → 0` at every real `x′ ≠ 0` whose `F_t`-boundary value lies in `ℍ` (every point of the two
  new sides of the chart slit);
* **`exists_chartTrace_of_code`**: the chart-side trace clauses of `IsGluedSlit` from FIBDATA's `PathGood` clauses;
* **`isChartMeanAt_canonMean_of_glued`** — **(K-b)** through `Aux61MeanId.isChartMeanAt_of_slit` for the canonical
  mean `canonMean`: from one decomposition `h₁` (`IsChartGaussAt`), the glued data a.s. on the live event
  (`IsGluedSlitSample`), SLIT's conclusion, and the two remaining boundary inputs as **named hypotheses** — the
  logarithmic growth of `v − canonMean` in the disc chart (MEAN's (b)) and the old real boundary limits off a finite
  set (MEAN's (c1)). Harmonicity of `canonMean` (MEAN's (a)) is GLUEINST's `harmonicOnNhd_canonMean` from the cutoff;
  the chart word's heights on the chart slit are `tendsto_canonExt_of_mem_left/right` (`Aux61Conf2Word`).

Conditional helpers with distinct names; no source statement is replaced. R48/R77: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement`, any `*_of_param`, or Astra's post-contact kernel.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Complex Set Metric Filter Topology
open scoped NNReal ENNReal ComplexConjugate Real
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv logDerivFwd chiC)
open QuantumZipper.CA (cayleyInv)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Sec5.Aux61Conf2

open Restart.FlowStopIdentCMI (CMCut)
open Aux61Win (IsCutoffOn meanF)
open Aux61Fib (FibCode FibData)
open Aux61ChLoc (IsChartGaussAt IsChartMeanAt)
open Aux61UnionK (chartHull canonMean)
open Aux61FibK (canonExt)

universe u v

namespace IsGluedSlit

variable {Wph : ℝ → ℝ} {η : ℝ → ℂ} {r τ : ℝ} {c : Chart} {D : Set ℂ} {w : ℝ → ℝ} {γ : ℝ → ℂ} {Tc t : ℝ}
  (hg : IsGluedSlit Wph η r τ c D w γ Tc t)
include hg

/-- **The two new sides at one sample.** With SLIT's comparison conclusion `hconv` for the comparison sets `L i`
(height offset `0`, lift coefficient `χ`), a cover of the continuation by comparison indices, the physical means
`M₂ i = couplingMean κ Wph (ρ i) (uph i)` on `D` with side heights `bL`/`bR`, the chart word `uc` with the same side
heights on the chart slit, and a cutoff `F` of `q` on a neighbourhood `N` of the closed chart hull: every harmonic
representative `v` has `v ∘ F_t − meanF κ uc q F w t ∘ F_t → 0` at each real `x′ ≠ 0` with `F̄_t(x′) ∈ ℍ`. -/
theorem tendsto_slit_sub_meanF (κ : ℝ) {v : ℂ → ℝ} {ι : Type*} {ρ : ι → ℝ} {L : ι → Set ℂ} {A : Set ℂ}
    {M₂ uph : ι → ℂ → ℝ} {uc q : ℂ → ℝ} {bL bR : ℝ} {F : CMCut} {N : Set ℂ} {O : Set ℝ}
    (hconv : ∀ i, ρ i < r + τ → ∀ z₀ ∈ L i ∪ {z : ℂ | z.im = 0}, (∃ ε > 0, A ∩ ball z₀ ε ⊆ L i) →
      ∀ l : Filter ℂ, l ≤ 𝓟 (H \ fwdHull w t) → Tendsto c.2.1 l (𝓝 z₀) →
        Tendsto (fun ζ => v ζ - (M₂ i (c.2.1 ζ) + 0 + chiC κ * c.2.2 (c.2.1 ζ))) l (𝓝 0))
    (hcover : ∀ s' ∈ Ioo 0 τ, ∃ i, r + s' < ρ i ∧ ρ i < r + τ ∧ η (r + s') ∈ L i ∧
      ∃ ε > 0, A ∩ ball (η (r + s')) ε ⊆ L i)
    (hM₂ : ∀ i, ∀ z ∈ D, M₂ i z = couplingMean κ Wph (ρ i) (uph i) z)
    (huL : ∀ i, ∀ p : ℝ, p < 0 → extendFrom H (fwdMapInv Wph (ρ i)) p ∈ H →
      Tendsto (uph i) (𝓝[H] (p : ℂ)) (𝓝 bL))
    (huR : ∀ i, ∀ p : ℝ, 0 < p → extendFrom H (fwdMapInv Wph (ρ i)) p ∈ H →
      Tendsto (uph i) (𝓝[H] (p : ℂ)) (𝓝 bR))
    (hucL : ∀ x' : ℝ, x' < 0 → extendFrom H (fwdMapInv w t) x' ∈ H → Tendsto uc (𝓝[H] (x' : ℂ)) (𝓝 bL))
    (hucR : ∀ x' : ℝ, 0 < x' → extendFrom H (fwdMapInv w t) x' ∈ H → Tendsto uc (𝓝[H] (x' : ℂ)) (𝓝 bR))
    (hF : IsCutoffOn F q N O) (hKN : closure (fwdHull w t) ⊆ N)
    {x' : ℝ} (hx'0 : x' ≠ 0) (hx'H : extendFrom H (fwdMapInv w t) x' ∈ H) :
    Tendsto (fun y => v (fwdMapInv w t y) - meanF κ uc q F w t (fwdMapInv w t y)) (𝓝[H] (x' : ℂ)) (𝓝 0) := by
  obtain ⟨s', hs', hx'⟩ := hg.exists_slitTime hx'0 hx'H
  obtain ⟨i, hi1, hi2, hiL, hball⟩ := hcover s' hs'
  have hρ : r + (ρ i - r) = ρ i := by ring
  have hdet := hg.tendsto_chartReading_sub_meanF κ (σ := ρ i - r) hs'.1 (by linarith) (by linarith) hx' hx'0
    (uph := uph i)
    (bL := bL) (bR := bR) (fun p hp hpH => huL i p hp (by rwa [hρ] at hpH))
    (fun p hp hpH => huR i p hp (by rwa [hρ] at hpH)) (fun h => hucL x' h hx'H) (fun h => hucR x' h hx'H) hF hKN
  rw [hρ] at hdet
  refine Aux61SlitV.tendsto_slit_of_chart (hconv i hi2 _ (Or.inl hiL) hball)
    (fun y hy => QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hg.hw hg.hw0 hg.tpos.le hy)
    (hg.tendsto_inv_fwdMapInv ⟨hs'.1, hs'.2.le⟩ hx') (hdet.congr' (eventually_nhdsWithin_of_forall fun y hy => ?_))
  dsimp only
  rw [hM₂ i _ (hg.inv_mem_D (QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hg.hw hg.hw0 hg.tpos.le hy).1), add_zero]

end IsGluedSlit

/-! ### The chart side from the fibre code -/

/-- **The chart side of `IsGluedSlit` from the fibre code's path facts** (FIBDATA's `PathGood` clauses): for a good code
(`GoodTrace`), injective through its lifetime and interior at positive times before it, and a chart time `q` before the
lifetime, the code's driver and path read on `ℝ` form a Loewner trace continuous before some `Tc > q`, simple on
`[0, q]` and in `ℍ` on `(0, q]`. -/
theorem exists_chartTrace_of_code {s : FibCode} (hgood : s ∈ Aux61Fib.GoodTrace)
    (hinj : InjOn s.trace {t | (t : ℝ≥0∞) ≤ s.life})
    (hint : ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < s.life → s.trace t ∈ H) {q : ℝ≥0} (hq : (q : ℝ≥0∞) < s.life) :
    ∃ Tc : ℝ, (q : ℝ) < Tc ∧
      IsLoewnerTraceLT (fun u : ℝ => FibCode.driver u.toNNReal s) Tc (fun u : ℝ => s.trace u.toNNReal) ∧
      InjOn (fun u : ℝ => s.trace u.toNNReal) (Icc 0 (q : ℝ)) ∧ ∀ u ∈ Ioc (0 : ℝ) q, s.trace u.toNNReal ∈ H := by
  obtain ⟨σ', hqσ', hσ'⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hq
  have hgen : IsGeneratingTrace (FibCode.driver · s) σ' s.trace :=
    ⟨hgood.1, hgood.2.1.mono fun t ht => le_trans ht hσ'.le, fun t ht => hgood.2.2 t (lt_trans ht hσ')⟩
  have hle : ∀ u ∈ Icc (0 : ℝ) q, ((u.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ s.life := fun u hu =>
    (ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hu.2)).trans hq.le
  refine ⟨σ', NNReal.coe_lt_coe.2 (ENNReal.coe_lt_coe.1 hqσ'),
    Theorem14.CounterflowRange.isLoewnerTraceLT_of_isGeneratingTrace hgen, fun u hu v hv he => ?_,
    fun u hu => hint _ (Real.toNNReal_pos.2 hu.1) ((ENNReal.coe_le_coe.2
      (Real.toNNReal_le_iff_le_coe.2 hu.2)).trans_lt hq)⟩
  have h := hinj (hle u hu) (hle v hv) he
  rwa [Real.toNNReal_eq_toNNReal_iff hu.1 hv.1] at h

/-! ### (K-b) for the canonical mean -/

section KB

variable {X : Type u} {𝒢 : MeasurableSpace X} [mX : MeasurableSpace X] {β : Type*} [mβ : MeasurableSpace β]
  {μ : Measure X} {Z : X → β} {B : Set β} {Y : X → FibCode} {q : ℝ≥0} {h₁ : X → DistOn upperHalfPlaneOpens}

/-- The chart driver of the code at a sample. -/
abbrev chartDrv (Y : X → FibCode) (x : X) : ℝ → ℝ := fun s : ℝ => FibCode.driver s.toNNReal (Y x)

/-- **The glued slit data of one sample** for the (K-b) assembly: the two-sides data `IsGluedSlit` with the code's
chart driver at the chart time `q`, the data's parameter `κ`, the cutoff `F₀` of the data's correction on a
neighbourhood `N` of the closed chart hull, the cover of the continuation by comparison indices, and the physical flow
line's means `M₂ i = couplingMean κ Wph (ρ i) (uph i)` on `D` with the flow line's heights `∓π/√κ` on the left/right
side of `η[0, ρ i]`. (The chart word's heights on the chart slit are proved: `tendsto_canonExt_of_mem_left/right`.) -/
structure IsGluedSlitSample (κ : ℝ) (d : FibData) (F₀ : CMCut) (N : Set ℂ) (s : FibCode) (q : ℝ≥0)
    (Wph : ℝ → ℝ) (η : ℝ → ℂ) (r τ : ℝ) (c : Chart) (D : Set ℂ) (γ : ℝ → ℂ) (Tc : ℝ) {ι : Type*}
    (ρ : ι → ℝ) (L : ι → Set ℂ) (A : Set ℂ) (M₂ uph : ι → ℂ → ℝ) : Prop where
  glued : IsGluedSlit Wph η r τ c D (fun s' : ℝ => FibCode.driver s'.toNNReal s) γ Tc q
  kappa : d.κ = κ
  cutoff : IsCutoffOn F₀ d.q N d.O₀
  hullN : closure (fwdHull (fun s' : ℝ => FibCode.driver s'.toNNReal s) q) ⊆ N
  cover : ∀ s' ∈ Ioo 0 τ, ∃ i, r + s' < ρ i ∧ ρ i < r + τ ∧ η (r + s') ∈ L i ∧
    ∃ ε > 0, A ∩ ball (η (r + s')) ε ⊆ L i
  mean : ∀ i, ∀ z ∈ D, M₂ i z = couplingMean κ Wph (ρ i) (uph i) z
  physL : ∀ i, ∀ p : ℝ, p < 0 → extendFrom H (fwdMapInv Wph (ρ i)) p ∈ H →
    Tendsto (uph i) (𝓝[H] (p : ℂ)) (𝓝 (-(Real.pi / Real.sqrt κ)))
  physR : ∀ i, ∀ p : ℝ, 0 < p → extendFrom H (fwdMapInv Wph (ρ i)) p ∈ H →
    Tendsto (uph i) (𝓝[H] (p : ℂ)) (𝓝 (Real.pi / Real.sqrt κ))

/-- **(K-b) for the canonical mean from the glued data** (Aux. 61's mean identification at the glued stop, through
`Aux61MeanId.isChartMeanAt_of_slit`). Inputs: one conditional Gaussian decomposition `h₁` of the chart field given `𝒢`;
almost surely on the live event the glued slit data of the sample (`IsGluedSlitSample`), the comparison events `S' i`
containing every comparison index before the chart time, and PROVE-AUX61-SLIT's comparison conclusion `hconv` (the
output of `Aux61SlitV.ae_tendsto_chart_sub_flowMean` with height offset `0` and lift coefficient `χ`); and, as named
remaining inputs, the logarithmic growth of `v − canonMean` in the disc chart (`hgrowth`, MEAN's (b)) and its vanishing
limits at the old real boundary off a finite set (`hold`, MEAN's (c1)). The two new sides of the chart slit (MEAN's
(c2)) and the harmonicity of `canonMean` (MEAN's (a)) are proved here. -/
theorem isChartMeanAt_canonMean_of_glued [IsFiniteMeasure μ] (hY : Measurable Y) (hB : MeasurableSet B)
    (hG₀ : IsChartGaussAt μ Z B Y q 𝒢 h₁) (κ : ℝ) {d : X → FibData} {F₀ : X → CMCut} {N : X → Set ℂ}
    {Wph : X → ℝ → ℝ} {η : X → ℝ → ℂ} {r τ Tc : X → ℝ} {c : X → Chart} {D : X → Set ℂ} {γ : X → ℝ → ℂ}
    {ι : Type*} {ρ : ι → X → ℝ} {L : ι → X → Set ℂ} {A : X → Set ℂ} {M₂ uph : ι → X → ℂ → ℝ}
    {S' : ι → Set X}
    (hglued : ∀ᵐ x ∂μ, Z x ∈ B → (q : ℝ≥0∞) < (Y x).life →
      IsGluedSlitSample κ (d x) (F₀ x) (N x) (Y x) q (Wph x) (η x) (r x) (τ x) (c x) (D x) (γ x) (Tc x)
        (fun i => ρ i x) (fun i => L i x) (A x) (fun i => M₂ i x) (fun i => uph i x))
    (hS' : ∀ᵐ x ∂μ, Z x ∈ B → (q : ℝ≥0∞) < (Y x).life → ∀ i, ρ i x < r x + τ x → x ∈ S' i)
    (hconv : ∀ᵐ x ∂μ, ∀ i, Z x ∈ B → (q : ℝ≥0∞) < (Y x).life → x ∈ S' i →
      ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ chartHull Y q x) →
      (∀ ψ : TestOn upperHalfPlaneOpens, tsupport ψ ⊆ H \ chartHull Y q x → h₁ x ψ = ∫ z, v z * ψ z) →
      ∀ z₀ ∈ L i x ∪ {z : ℂ | z.im = 0}, (∃ r > 0, A x ∩ ball z₀ r ⊆ L i x) →
      ∀ l : Filter ℂ, l ≤ 𝓟 (H \ chartHull Y q x) → Tendsto (c x).2.1 l (𝓝 z₀) →
        Tendsto (fun ζ => v ζ - (M₂ i x ((c x).2.1 ζ) + 0 + chiC κ * (c x).2.2 ((c x).2.1 ζ))) l (𝓝 0))
    (hgrowth : ∀ᵐ x ∂μ, Z x ∈ B → (q : ℝ≥0∞) < (Y x).life → ∀ v : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd v (H \ chartHull Y q x) →
      (∀ ψ : TestOn upperHalfPlaneOpens, tsupport ψ ⊆ H \ chartHull Y q x → h₁ x ψ = ∫ z, v z * ψ z) →
      ∃ C : ℝ, ∀ ζ ∈ ball (0 : ℂ) 1,
        |v (fwdMapInv (chartDrv Y x) q (cayleyInv ζ)) -
          canonMean.{v} (d x) (F₀ x) (ULift.up (Y x)) q (fwdMapInv (chartDrv Y x) q (cayleyInv ζ))| ≤
        C * (1 + Real.log (1 / (1 - ‖ζ‖))))
    (hold : ∀ᵐ x ∂μ, Z x ∈ B → (q : ℝ≥0∞) < (Y x).life → ∀ v : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd v (H \ chartHull Y q x) →
      (∀ ψ : TestOn upperHalfPlaneOpens, tsupport ψ ⊆ H \ chartHull Y q x → h₁ x ψ = ∫ z, v z * ψ z) →
      ∃ S : Set ℝ, S.Finite ∧ ∀ x' : ℝ, x' ∉ S → extendFrom H (fwdMapInv (chartDrv Y x) q) x' ∉ H →
        Tendsto (fun y => v (fwdMapInv (chartDrv Y x) q y) -
          canonMean.{v} (d x) (F₀ x) (ULift.up (Y x)) q (fwdMapInv (chartDrv Y x) q y)) (𝓝[H] (x' : ℂ)) (𝓝 0)) :
    @IsChartMeanAt X mX β mβ μ Z B Y q 𝒢 fun x => canonMean.{v} (d x) (F₀ x) (ULift.up (Y x)) q := by
  refine Aux61MeanId.isChartMeanAt_of_slit hY hB hG₀ ?_ ?_
  · filter_upwards [hglued] with x hx hxB hlt
    have hs := hx hxB hlt
    exact Aux61GInst.harmonicOnNhd_canonMean hs.cutoff (ULift.up (Y x)) q hs.hullN
  · filter_upwards [hglued, hS', hconv, hgrowth, hold] with x hx hxS hxc hxg hxo hxB hlt v hv hrep
    have hs := hx hxB hlt
    obtain ⟨C, hC⟩ := hxg hxB hlt v hv hrep
    obtain ⟨S, hS, hlim⟩ := hxo hxB hlt v hv hrep
    refine ⟨⟨C, hC⟩, insert 0 S, hS.insert 0, fun x' hx' => ?_⟩
    have hx'0 : x' ≠ 0 := fun h => hx' (h ▸ mem_insert _ _)
    have hx'S : x' ∉ S := fun h => hx' (mem_insert_of_mem _ h)
    by_cases hH : extendFrom H (fwdMapInv (chartDrv Y x) q) x' ∈ H
    · have h := hs.glued.tendsto_slit_sub_meanF κ (v := v) (ρ := fun i => ρ i x) (L := fun i => L i x)
        (A := A x) (M₂ := fun i => M₂ i x) (uph := fun i => uph i x)
        (fun i hi z₀ hz₀ hball l hl hinv => hxc i hxB hlt (hxS hxB hlt i hi) v hv hrep z₀ hz₀ hball l hl hinv)
        hs.cover hs.mean hs.physL hs.physR
        (fun x'' h0 hx'' => hs.kappa ▸ tendsto_canonExt_of_mem_left.{v} (d x) hs.glued h0 hx'')
        (fun x'' h0 hx'' => hs.kappa ▸ tendsto_canonExt_of_mem_right.{v} (d x) hs.glued h0 hx'')
        hs.cutoff hs.hullN hx'0 hH
      have hκ := hs.kappa
      simp only [canonMean, hκ]
      exact h
    · exact hlim x' hx'S hH

end KB

end InteractingSLE.Sec5.Aux61Conf2
