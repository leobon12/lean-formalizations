import HigherDimLFPPAS.Normalizer.Transfer
import HigherDimLFPPAS.Signed.LFPP
import HigherDimLQGMetric.LfppTight.MetricScale

/-!
# `𝔞_ε` and the transfer of (1.6) for admissible (signed) seeds (packet N1; MA1 A1, A3)

Final forms, for every admissible seed `κ` (`HigherDimLFPPAS.IsAdmissibleSeed`, no sign condition; ruling L7),
of the identification of the paper's normalizer (1.4) with the frozen `aEps` (MA1 Details A1) and of the
transfer of Assumption 1.1 (v) to every normalized LGF and to the recentred rescaled fields `h^{z,r}` (MA1
A3). The two inputs on the seed come from packet G1's sign-free copies:

* `n1_ae_continuous_seed`: the convolution field of the normalized LGF is a.s. continuous at every cutoff
  (`HigherDimLFPPAS.Signed.l10a_ae_continuous_convMollify_seed`);
* `n1_ae_lfppDist_scale_seed`: the exact LFPP scaling identity
  `D^ε_h(r u, r v) = r e^{ξ h_r(0)} D^{ε/r}_{g}(u, v)`, `g = recentAff r 0 h`, a.s. for all `ε, u, v`
  (`HigherDimLFPPAS.Signed.l9b_ae_convMollify_affine_seed` and the deterministic
  `HigherDimLQGMetric.l6a_lfppDist_scale_of_conv_eq`); sign-free form of `l6c_ae_lfppDist_scale`.

Main results: `half_le_prob_iff_aEps_le`, `aEps_pos`, `aEps_eq_lowerMedian`, `aEps_eq_paperMedian` (A1);
`lfppConv_transfer`, `lfppConv_recentAff`, `lfppConv_paperRecentred` (A3).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace HigherDimLFPPAS.Normalizer

open HigherDimLQGMetric
open HigherDimLFPP (Rd e₁)

/-! ## The two seed inputs -/

/-- For an admissible seed, the convolution field of the normalized law is a.s. continuous at every
positive cutoff. -/
theorem n1_ae_continuous_seed {d : ℕ} (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsAdmissibleSeed κ)
    {ε : ℝ} (hε : 0 < ε) : ∀ᵐ g ∂(normLGFLaw d), Continuous fun z => convMollify κ ε g z := by
  have : IsProbabilityMeasure (normLGFLaw d) := (normLGFLaw_spec_holds d hd).1
  exact Signed.l10a_ae_continuous_convMollify_seed hd κ hκ (normLGFLaw d) id
    (normLGFLaw_spec_holds d hd).2.1 hε

/-- **Exact LFPP scaling for admissible seeds** (sign-free form of
`HigherDimLQGMetric.l6c_ae_lfppDist_scale`, with the recentred field `recentAff r 0 h`): for a normalized
LGF `h` and `r > 0`, almost surely, for all `ε > 0` and `u, v`,
`D^ε_h(r u, r v) = r e^{ξ h_r(0)} D^{ε/r}_{recentAff r 0 h}(u, v)`. -/
theorem n1_ae_lfppDist_scale_seed {d : ℕ} (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsAdmissibleSeed κ)
    (ξ : ℝ) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistRd d} (hh : IsNormalizedLGF h P) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε → ∀ u v : Rd d,
      lfppDist κ ξ ε (h ω) (r • u, r • v) =
        r * Real.exp (ξ * sphereAvg (h ω) r 0) * lfppDist κ ξ (ε / r) (recentAff r 0 (h ω)) (u, v) := by
  filter_upwards [Signed.l9b_ae_convMollify_affine_seed hd hκ hh 0 hr] with ω hω
  intro ε hε u v
  have heq : ∀ z : Rd d, convMollify κ ε (h ω) (0 + r • z) =
      convMollify κ (ε / r) (recentAff r 0 (h ω)) z + sphereAvg (h ω) r 0 := fun z => by
    rw [hω.1 ε hε z, hω.2]
  have hsc := l6a_lfppDist_scale_of_conv_eq κ ξ ε r (sphereAvg (h ω) r 0) hr (h ω)
    (recentAff r 0 (h ω)) 0 u v heq
  simpa only [zero_add] using hsc

/-- The scaling identity at the pair `(0, r e₁)`, in the form consumed by `Normalizer/Ratio.lean`. -/
theorem n1_ae_lfppDist_scale_e₁_seed {d : ℕ} (hd : 2 ≤ d) {κ : Rd d → ℝ}
    (hκ : IsAdmissibleSeed κ) (ξ : ℝ) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistRd d} (hh : IsNormalizedLGF h P) (r : ℝ) (hr : 0 < r) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε →
      lfppDist κ ξ ε (h ω) (0, r • e₁ d) =
        r * Real.exp (ξ * sphereAvg (h ω) r 0) *
          lfppDist κ ξ (ε / r) (recentAff r 0 (h ω)) (0, e₁ d) := by
  filter_upwards [n1_ae_lfppDist_scale_seed hd hκ ξ hh hr] with ω hω
  intro ε hε
  have := hω ε hε 0 (e₁ d)
  rwa [smul_zero] at this

/-! ## MA1 A1: the paper's normalizer is `aEps` -/

/-- **The distribution function of `D^ε_h(0, e₁)` under `P`** reaches `1/2` exactly from `aEps κ ξ ε` on,
for every admissible seed, normalized LGF `h` on any probability space and `ε > 0`. -/
theorem half_le_prob_iff_aEps_le {d : ℕ} (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsAdmissibleSeed κ)
    (ξ : ℝ) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistRd d} (hh : IsNormalizedLGF h P) {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    (2 : ℝ≥0∞)⁻¹ ≤ P {ω | lfppDist κ ξ ε (h ω) (0, e₁ d) ≤ x} ↔ aEps κ ξ ε ≤ x :=
  n1_half_le_prob_iff hd ξ (n1_ae_continuous_seed hd hκ hε) hh x

/-- **Positivity of the normalizer** for every admissible seed and every `ε > 0`. -/
theorem aEps_pos {d : ℕ} (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsAdmissibleSeed κ) (ξ : ℝ) {ε : ℝ}
    (hε : 0 < ε) : 0 < aEps κ ξ ε :=
  n1_aEps_pos_of_cont hd ξ (n1_ae_continuous_seed hd hκ hε)

/-- **(1.4) = `aEps`** (lower median over `ℝ`): for every admissible seed, normalized LGF `h` on any
probability space `(Ω, P)` and `ε > 0`, `aEps κ ξ ε = inf {m : P[D^ε_h(0, e₁) ≤ m] ≥ 1/2}`. -/
theorem aEps_eq_lowerMedian {d : ℕ} (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsAdmissibleSeed κ) (ξ : ℝ)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistRd d}
    (hh : IsNormalizedLGF h P) {ε : ℝ} (hε : 0 < ε) :
    aEps κ ξ ε = sInf {m : ℝ | (2 : ℝ≥0∞)⁻¹ ≤ P {ω | lfppDist κ ξ ε (h ω) (0, e₁ d) ≤ m}} :=
  n1_aEps_eq_sInf_prob hd ξ (n1_ae_continuous_seed hd hκ hε) hh

/-- **(1.4) = `aEps`, the paper's form**: for every admissible seed, normalized LGF `h` on any
probability space `(Ω, P)` and `ε > 0`,
`aEps κ ξ ε = 𝔞_ε = inf {a > 0 : P[D^ε_h(0, e₁) ≤ a] ≥ 1/2}`. -/
theorem aEps_eq_paperMedian {d : ℕ} (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsAdmissibleSeed κ) (ξ : ℝ)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistRd d}
    (hh : IsNormalizedLGF h P) {ε : ℝ} (hε : 0 < ε) :
    aEps κ ξ ε =
      sInf {a : ℝ | 0 < a ∧ (2 : ℝ≥0∞)⁻¹ ≤ P {ω | lfppDist κ ξ ε (h ω) (0, e₁ d) ≤ a}} :=
  n1_aEps_eq_paperMedian_of_cont hd ξ (n1_ae_continuous_seed hd hκ hε) hh

/-! ## MA1 A3: transfer of (1.6) -/

/-- **Transfer of Assumption 1.1 (v)** (MA1 A3): for an admissible seed and a measurable assignment `D`,
(1.6) for one normalized LGF `h` on `(Ω, P)` implies (1.6) for every normalized LGF `g` on every
probability space `(Ω', P')`. -/
theorem lfppConv_transfer {d : ℕ} (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsAdmissibleSeed κ) {ξ : ℝ}
    {D : DistRd d → ContMetric d} (hDm : Measurable D)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistRd d}
    (hh : IsNormalizedLGF h P)
    (hconv : TendstoInProbLU P (fun ε ω => (aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω)) (𝓝[>] 0)
      (fun ω => (D (h ω)).1))
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {g : Ω' → DistRd d} (hg : IsNormalizedLGF g P') :
    TendstoInProbLU P' (fun ε ω => (aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (g ω)) (𝓝[>] 0)
      (fun ω => (D (g ω)).1) :=
  n1_tendstoInProbLU_transfer_of_cont hd (fun _ hε => n1_ae_continuous_seed hd hκ hε) hDm hh
    hconv hg

/-- (1.6) for the recentred rescaled fields `recentAff r z h = h(r · + z) − (h(r · + z))_1(0)`, for an
admissible seed. -/
theorem lfppConv_recentAff {d : ℕ} (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsAdmissibleSeed κ) {ξ : ℝ}
    {D : DistRd d → ContMetric d} (hDm : Measurable D)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistRd d}
    (hh : IsNormalizedLGF h P)
    (hconv : TendstoInProbLU P (fun ε ω => (aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω)) (𝓝[>] 0)
      (fun ω => (D (h ω)).1))
    {r : ℝ} (hr : 0 < r) (z : Rd d) :
    TendstoInProbLU P (fun ε ω => (aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (recentAff r z (h ω))) (𝓝[>] 0)
      (fun ω => (D (recentAff r z (h ω))).1) :=
  n1_tendstoInProbLU_recentAff_of_cont hd (fun _ hε => n1_ae_continuous_seed hd hκ hε) hDm hh
    hconv hr z

/-- (1.6) for the paper's recentred rescaled fields `h^{z,r} = h(z + r ·) − h_r(z)`, for an admissible
seed. -/
theorem lfppConv_paperRecentred {d : ℕ} (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsAdmissibleSeed κ)
    {ξ : ℝ} {D : DistRd d → ContMetric d} (hDm : Measurable D)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistRd d}
    (hh : IsNormalizedLGF h P)
    (hconv : TendstoInProbLU P (fun ε ω => (aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω)) (𝓝[>] 0)
      (fun ω => (D (h ω)).1))
    {r : ℝ} (hr : 0 < r) (z : Rd d) :
    TendstoInProbLU P (fun ε ω => (aEps κ ξ ε)⁻¹ •
        lfppDist κ ξ ε (addConst (affineComp r z (h ω)) (-sphereAvg (h ω) r z))) (𝓝[>] 0)
      (fun ω => (D (addConst (affineComp r z (h ω)) (-sphereAvg (h ω) r z))).1) :=
  n1_tendstoInProbLU_paperRecentred_of_cont hd (fun _ hε => n1_ae_continuous_seed hd hκ hε) hDm
    hh hconv hr z

end HigherDimLFPPAS.Normalizer
