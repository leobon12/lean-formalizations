import HigherDimLFPPAS.Normalizer.Ratio
import HigherDimLFPPAS.Normalizer.Seed
import HigherDimLQGMetric.Sec4.Lemma44

/-!
# Lemma 2.5 for admissible seeds (packet N1; MA1 A7)

Lemma 2.5 of `source/higher-dimensional-lfpp-almost-sure.pdf` (l. 290–310), for every admissible (signed)
seed `κ`, every `Q` (the proof uses only (1.5) at exponent `Q`; no relation with `√(2d)` or with the DGZ
exponent is needed), every strong assignment `IsStrongExpMetric d ξ Q D`, and a normalized LGF `h` on
`(Ω, P)` satisfying (1.6). With `c_ε(r) = r 𝔞_{ε/r} / (r^{ξQ} 𝔞_ε)` ((1.8); this is
`HigherDimLQGMetric.l9bRatio κ ξ (fun s => s ^ (ξ * Q)) ε r` by definition):

* `lemma25_unif`, `lemma25_tendstoUniformlyOn`: `c_ε(r) → 1` uniformly for `r` in compact subsets of
  `(0, ∞)` ((2.9), uniformly);
* `lemma25_tendsto`: (2.9) for each fixed `r > 0`;
* `lemma25_window`, `lemma25_window_sup`: (2.10), `sup_{ε ∈ [(n+1)^{−a}, n^{−a}]} |𝔞_ε/𝔞_{n^{−a}} − 1| → 0` for
  every `a > 0` (eventually-uniform form and `ℝ≥0∞`-supremum form);
* `lemma25_exponent`, `lemma25_rpow_bounds`: `𝔞_ε = ε^{1−ξQ+o(1)}`, i.e. `log 𝔞_ε / log ε → 1 − ξQ`, and
  `ε^{1−ξQ+η} ≤ 𝔞_ε ≤ ε^{1−ξQ−η}` for small `ε`, every `η > 0`.

The paper's route through regular variation ([1] Theorems 1.2.1, 1.3.1) is replaced by the coupling argument
of `Normalizer/Ratio.lean` and the elementary consequences of `Normalizer/Exponent.lean`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace HigherDimLFPPAS.Normalizer

open HigherDimLQGMetric
open HigherDimLFPP (Rd e₁)

/-- **Lemma 2.5, (2.9) uniformly on `[a, b]`**: for an admissible seed, a strong assignment at exponent
`Q` and (1.6) for the normalized LGF `h`, `sup_{r ∈ [a, b]} |c_ε(r) − 1| → 0` as `ε ↓ 0`, for every
`0 < a`. -/
theorem lemma25_unif {d : ℕ} (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsAdmissibleSeed κ) {ξ Q : ℝ}
    {D : DistRd d → ContMetric d} (hD : IsStrongExpMetric d ξ Q D)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistRd d}
    (hh : IsNormalizedLGF h P)
    (hconv : TendstoInProbLU P (fun ε ω => (aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω)) (𝓝[>] 0)
      (fun ω => (D (h ω)).1))
    {a b : ℝ} (ha : 0 < a) :
    ∀ η : ℝ, 0 < η → ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ r ∈ Icc a b,
      |r * aEps κ ξ (ε / r) / (r ^ (ξ * Q) * aEps κ ξ ε) - 1| ≤ η :=
  n1_ratio_unif_of_cont hd hD hh hconv (fun _ hε => n1_ae_continuous_seed hd hκ hε)
    (fun r hr => n1_ae_lfppDist_scale_e₁_seed hd hκ ξ hh r hr) ha

/-- **Lemma 2.5, (2.9) uniformly on compact sets**: `c_ε(r) → 1` uniformly for `r` in every compact
`K ⊆ (0, ∞)`. -/
theorem lemma25_tendstoUniformlyOn {d : ℕ} (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsAdmissibleSeed κ)
    {ξ Q : ℝ} {D : DistRd d → ContMetric d} (hD : IsStrongExpMetric d ξ Q D)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistRd d}
    (hh : IsNormalizedLGF h P)
    (hconv : TendstoInProbLU P (fun ε ω => (aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω)) (𝓝[>] 0)
      (fun ω => (D (h ω)).1))
    {K : Set ℝ} (hK : IsCompact K) (hK0 : K ⊆ Ioi 0) :
    TendstoUniformlyOn (fun ε r => r * aEps κ ξ (ε / r) / (r ^ (ξ * Q) * aEps κ ξ ε))
      (fun _ => 1) (𝓝[>] 0) K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro η hη
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · exact Eventually.of_forall fun ε r hr => by rw [hKe] at hr; exact absurd hr (notMem_empty r)
  obtain ⟨a, haK, ha⟩ := hK.exists_isLeast hKne
  obtain ⟨b, hbK, hb⟩ := hK.exists_isGreatest hKne
  have ha0 : 0 < a := hK0 haK
  filter_upwards [lemma25_unif hd hκ hD hh hconv ha0 (η / 2) (by positivity)] with ε hε r hr
  rw [Real.dist_eq, abs_sub_comm]
  exact lt_of_le_of_lt (hε r ⟨ha hr, hb hr⟩) (by linarith)

/-- **Lemma 2.5, (2.9)**: `c_ε(r) → 1` as `ε ↓ 0`, for every fixed `r > 0`. -/
theorem lemma25_tendsto {d : ℕ} (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsAdmissibleSeed κ) {ξ Q : ℝ}
    {D : DistRd d → ContMetric d} (hD : IsStrongExpMetric d ξ Q D)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistRd d}
    (hh : IsNormalizedLGF h P)
    (hconv : TendstoInProbLU P (fun ε ω => (aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω)) (𝓝[>] 0)
      (fun ω => (D (h ω)).1))
    {r : ℝ} (hr : 0 < r) :
    Tendsto (fun ε => r * aEps κ ξ (ε / r) / (r ^ (ξ * Q) * aEps κ ξ ε)) (𝓝[>] 0) (𝓝 1) := by
  rw [Metric.tendsto_nhds]
  intro η hη
  filter_upwards [lemma25_unif hd hκ hD hh hconv (b := r) hr (η / 2) (by positivity)] with ε hε
  rw [Real.dist_eq]
  exact lt_of_le_of_lt (hε r ⟨le_rfl, le_rfl⟩) (by linarith)

/-- **Lemma 2.5, (2.10)**: for every `a > 0` and `η > 0`, eventually in `n`, for all
`ε ∈ [(n+1)^{−a}, n^{−a}]`, `|𝔞_ε / 𝔞_{n^{−a}} − 1| ≤ η`. -/
theorem lemma25_window {d : ℕ} (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsAdmissibleSeed κ) {ξ Q : ℝ}
    {D : DistRd d → ContMetric d} (hD : IsStrongExpMetric d ξ Q D)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistRd d}
    (hh : IsNormalizedLGF h P)
    (hconv : TendstoInProbLU P (fun ε ω => (aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω)) (𝓝[>] 0)
      (fun ω => (D (h ω)).1))
    {a : ℝ} (ha : 0 < a) :
    ∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop, ∀ ε ∈ Icc (((n : ℝ) + 1) ^ (-a)) ((n : ℝ) ^ (-a)),
      |aEps κ ξ ε / aEps κ ξ ((n : ℝ) ^ (-a)) - 1| ≤ η :=
  n1_window_of_unif (A := aEps κ ξ) (θ := ξ * Q)
    (fun η hη => lemma25_unif hd hκ hD hh hconv one_pos η hη) ha

/-- **Lemma 2.5, (2.10), supremum form**: for every `a > 0`,
`sup_{ε ∈ [(n+1)^{−a}, n^{−a}]} |𝔞_ε / 𝔞_{n^{−a}} − 1| → 0` (supremum in `ℝ≥0∞`, no junk values). -/
theorem lemma25_window_sup {d : ℕ} (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsAdmissibleSeed κ)
    {ξ Q : ℝ} {D : DistRd d → ContMetric d} (hD : IsStrongExpMetric d ξ Q D)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistRd d}
    (hh : IsNormalizedLGF h P)
    (hconv : TendstoInProbLU P (fun ε ω => (aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω)) (𝓝[>] 0)
      (fun ω => (D (h ω)).1))
    {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n : ℕ => ⨆ ε ∈ Icc (((n : ℝ) + 1) ^ (-a)) ((n : ℝ) ^ (-a)),
      ENNReal.ofReal |aEps κ ξ ε / aEps κ ξ ((n : ℝ) ^ (-a)) - 1|) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro e he
  rcases eq_top_or_lt_top e with rfl | hetop
  · exact Eventually.of_forall fun n => le_top
  have hepos : 0 < e.toReal := ENNReal.toReal_pos he.ne' hetop.ne
  filter_upwards [lemma25_window hd hκ hD hh hconv ha e.toReal hepos] with n hn
  refine iSup₂_le fun ε hε => ?_
  calc ENNReal.ofReal |aEps κ ξ ε / aEps κ ξ ((n : ℝ) ^ (-a)) - 1|
      ≤ ENNReal.ofReal e.toReal := ENNReal.ofReal_le_ofReal (hn ε hε)
    _ = e := ENNReal.ofReal_toReal hetop.ne

/-- **Lemma 2.5, the exponent**: `log 𝔞_ε / log ε → 1 − ξQ` as `ε ↓ 0`, i.e. `𝔞_ε = ε^{1−ξQ+o(1)}`. -/
theorem lemma25_exponent {d : ℕ} (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsAdmissibleSeed κ) {ξ Q : ℝ}
    {D : DistRd d → ContMetric d} (hD : IsStrongExpMetric d ξ Q D)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistRd d}
    (hh : IsNormalizedLGF h P)
    (hconv : TendstoInProbLU P (fun ε ω => (aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω)) (𝓝[>] 0)
      (fun ω => (D (h ω)).1)) :
    Tendsto (fun ε => Real.log (aEps κ ξ ε) / Real.log ε) (𝓝[>] 0) (𝓝 (1 - ξ * Q)) :=
  n1_exponent_of_unif (A := aEps κ ξ) (θ := ξ * Q)
    (eventually_nhdsWithin_of_forall fun _ hε => aEps_pos hd hκ ξ hε)
    (fun η hη => lemma25_unif hd hκ hD hh hconv one_pos η hη)

/-- **Lemma 2.5, the exponent, two-sided form**: for every `η > 0`,
`ε^{1−ξQ+η} ≤ 𝔞_ε ≤ ε^{1−ξQ−η}` for all small `ε > 0`. -/
theorem lemma25_rpow_bounds {d : ℕ} (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsAdmissibleSeed κ)
    {ξ Q : ℝ} {D : DistRd d → ContMetric d} (hD : IsStrongExpMetric d ξ Q D)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistRd d}
    (hh : IsNormalizedLGF h P)
    (hconv : TendstoInProbLU P (fun ε ω => (aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω)) (𝓝[>] 0)
      (fun ω => (D (h ω)).1)) :
    ∀ η : ℝ, 0 < η → ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ε ^ (1 - ξ * Q + η) ≤ aEps κ ξ ε ∧ aEps κ ξ ε ≤ ε ^ (1 - ξ * Q - η) :=
  n1_rpow_bounds_of_unif (A := aEps κ ξ) (θ := ξ * Q)
    (eventually_nhdsWithin_of_forall fun _ hε => aEps_pos hd hκ ξ hε)
    (fun η hη => lemma25_unif hd hκ hD hh hconv one_pos η hη)

/-- The ratio of the statements is the repository's `l9bRatio` at the sharp normalizer `r ↦ r^{ξQ}`
(definitional). -/
theorem n1_ratio_eq_l9bRatio {d : ℕ} (κ : Rd d → ℝ) (ξ Q ε r : ℝ) :
    r * aEps κ ξ (ε / r) / (r ^ (ξ * Q) * aEps κ ξ ε) = l9bRatio κ ξ (fun s => s ^ (ξ * Q)) ε r :=
  rfl

end HigherDimLFPPAS.Normalizer
