import GaussianLQG.Frozen.IsCanonicalLQGMetric
import LQGMetric.Blueprint.M2Defs
import LQGMetric.Metric.WeylBasic
import LQGMetric.Field.CameronMartin
import LQGMetric.Papers.GM.S3.GoodAnnulus
import LQGMetric.Papers.LM.T1_6Cross
import SmallGammaGeodesics.Core.TestFun

/-!
# Interfaces of track CC (conformal covariance, Gwynne–Miller arXiv:1905.00384, Thm 1.3)

Exact statements fixed by the plan `planning/audits/CC0-conformal-covariance-plan.md`, §5.1 and Details (c),
under rulings G9, G10, G17 and G19–G22. Consumers take `ConfCovLE` (§5) or `ConfCov`/`MCInput` (§7) as
interface hypotheses; track CC discharges `MasterCC` (CC11) and `MCInput` (CC12), and the G-track discharges
`NICInput` (ruling G20). Proved here: `confCovLE_of_confCov`, `iter_closed`, `confCovLE_of_biLip_improve`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace SmallGammaGeodesics.CC

open LQGMetric LQGMetric.Blueprint

/-! ## 1. Maps, pullbacks, couplings -/

/-- `ϕ` is holomorphic and injective on an open `W ⊇ closure V`, with `V` bounded and open.
The image domain is `U = ϕ '' V`. -/
structure IsConfNbhd (ϕ : ℂ → ℂ) (W V : Set ℂ) : Prop where
  isOpen_W : IsOpen W
  isOpen_V : IsOpen V
  isBounded_V : Bornology.IsBounded V
  closure_subset : closure V ⊆ W
  differentiableOn : DifferentiableOn ℂ ϕ W
  injOn : InjOn ϕ W

/-- `τg` is the conformal pullback `|ϕ'|² · (g ∘ ϕ)` on `W`, and `0` off `W`. -/
def IsConfPull (ϕ : ℂ → ℂ) (W : Set ℂ) (g τg : TestC) : Prop :=
  ∀ x, τg x = W.indicator (fun y => ‖deriv ϕ y‖ ^ 2 * g (ϕ y)) x

/-- **The conformal coupling**: `(h ∘ ϕ⁻¹ + Q log |(ϕ⁻¹)'|)|_{ϕ(V)} = (h̄ + f)|_{ϕ(V)}`, tested
against every `g ∈ 𝓓(ℂ)` supported in `ϕ(V)` after the substitution `y = ϕ x`
(`∫ log|(ϕ⁻¹)'(y)| g(y) dy = -∫ log|ϕ'(x)| τg(x) dx`). -/
def IsConfCoupling (γ : ℝ) (ϕ : ℂ → ℂ) (W V : Set ℂ) (h hbar : DistC) (f : C(ℂ, ℝ)) : Prop :=
  ∀ g τg : TestC, tsupport (g : ℂ → ℝ) ⊆ ϕ '' V → IsConfPull ϕ W g τg →
    h τg - Q γ * ∫ x, Real.log ‖deriv ϕ x‖ * τg x = hbar g + ∫ y, f y * g y

/-- the transported metric `D^ϕ(z, w) := D_{h̄+f}(ϕ z, ϕ w; ϕ(V))` on `V` -/
def confMetric (D : DistC → ContMetric) (ϕ : ℂ → ℂ) (V : Set ℂ) (hbar : DistC) (f : C(ℂ, ℝ))
    (z w : ℂ) : ℝ≥0∞ :=
  (D (addFun hbar f)).internal (ϕ '' V) (ϕ z) (ϕ w)

/-- non-vacuity companion: pullbacks of test functions supported in `ϕ(V)` are test functions -/
def ExistsConfPull : Prop :=
  ∀ (ϕ : ℂ → ℂ) (W V : Set ℂ), IsConfNbhd ϕ W V → ∀ g : TestC,
    tsupport (g : ℂ → ℝ) ⊆ ϕ '' V → ∃ τg : TestC, IsConfPull ϕ W g τg

/-! ## 2. The master theorem (two-sided) and the one-sided form -/

/-- **[3] Theorem 1.3, intended form, coupled** (two-sided). -/
def ConfCov (γ : ℝ) (D : DistC → ContMetric) : Prop :=
  ∀ (ϕ : ℂ → ℂ) (W V : Set ℂ), IsConfNbhd ϕ W V →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h hbar : Ω → DistC) (f : Ω → C(ℂ, ℝ)),
    IsWholePlaneGFF h P → IsWholePlaneGFF hbar P → Measurable f →
    (∀ᵐ ω ∂P, IsConfCoupling γ ϕ W V (h ω) (hbar ω) (f ω)) →
    ∀ᵐ ω ∂P, ∀ z ∈ V, ∀ w ∈ V,
      (D (h ω)).internal V z w = confMetric D ϕ V (hbar ω) (f ω) z w

/-- **[3] Proposition 3.6, coupled** (one-sided; the form (5.3) needs, GA2 [CC≥]). -/
def ConfCovLE (γ : ℝ) (D : DistC → ContMetric) : Prop :=
  ∀ (ϕ : ℂ → ℂ) (W V : Set ℂ), IsConfNbhd ϕ W V →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h hbar : Ω → DistC) (f : Ω → C(ℂ, ℝ)),
    IsWholePlaneGFF h P → IsWholePlaneGFF hbar P → Measurable f →
    (∀ᵐ ω ∂P, IsConfCoupling γ ϕ W V (h ω) (hbar ω) (f ω)) →
    ∀ᵐ ω ∂P, ∀ z ∈ V, ∀ w ∈ V,
      confMetric D ϕ V (hbar ω) (f ω) z w ≤ (D (h ω)).internal V z w

/-- **Reversal** ([3], proof of Thm 1.3 from Prop 3.6): the one-sided form for every map of the
class gives the two-sided form (apply it to `ϕ⁻¹` with the reversed coupling `(h̄, h, -f ∘ ϕ)`). -/
def Reversal (γ : ℝ) (D : DistC → ContMetric) : Prop := ConfCovLE γ D → ConfCov γ D

theorem confCovLE_of_confCov {γ : ℝ} {D : DistC → ContMetric} (H : ConfCov γ D) :
    ConfCovLE γ D := by
  intro ϕ W V hϕ Ω _ P _ h hbar f hh hhb hf hc
  filter_upwards [H ϕ W V hϕ P h hbar f hh hhb hf hc] with ω hω z hz w hw
  exact (hω z hz w hw).ge

/-- the master keystones (canonical metric; strong metrics follow from GM Thm 1.2 uniqueness) -/
def MasterCC : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ D : DistC → ContMetric, GaussianLQG.IsCanonicalLQGMetric γ D →
    ConfCov γ D

def MasterCCLE : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ D : DistC → ContMetric, GaussianLQG.IsCanonicalLQGMetric γ D →
    ConfCovLE γ D

def MasterCCStrong : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ D : DistC → ContMetric, IsStrongLQGMetric γ D → ConfCov γ D

/-! ## 3. The modulo-constants export (MC) for Möbius maps (GA4 (F3)) -/

/-- the mean-zero pairing vector of a distribution on `U` (`σ₀(U)` coordinates) -/
def pair0On (U : Set ℂ) (x : DistC) : TestC0On U → ℝ := fun g => x g.1.1

/-- the chosen conformal pullback of a test function (junk `0` if no test function fits) -/
def confPull (ϕ : ℂ → ℂ) (W : Set ℂ) (g : TestC) : TestC := by
  classical
  exact if hg : ∃ τg : TestC, IsConfPull ϕ W g τg then hg.choose else 0

/-- the `σ₀(ϕ(V))` pairing vector of `h ∘ ϕ⁻¹ + Q log |(ϕ⁻¹)'|` -/
def confPair0 (γ : ℝ) (ϕ : ℂ → ℂ) (W V : Set ℂ) (h : DistC) : TestC0On (ϕ '' V) → ℝ :=
  fun g => h (confPull ϕ W g.1.1) - Q γ * ∫ x, Real.log ‖deriv ϕ x‖ * confPull ϕ W g.1.1 x

/-- `ϕ` is a Möbius map -/
def IsMobius (ϕ : ℂ → ℂ) : Prop :=
  ∃ a b c d : ℂ, a * d - b * c ≠ 0 ∧ ∀ z, ϕ z = (a * z + b) / (c * z + d)

/-- a `σ₀(U)` internal-metric functional (GA4 A10): measurable in the mean-zero pairing vector
and valid, up to a positive finite factor, for every whole-plane GFF plus a test function -/
def IsSigma0Metric (D : DistC → ContMetric) (U : Set ℂ)
    (d : (TestC0On U → ℝ) → ℂ → ℂ → ℝ≥0∞) : Prop :=
  Measurable d ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (g : TestC), IsWholePlaneGFF h P →
    ∀ᵐ ω ∂P, ∃ c : ℝ≥0∞, 0 < c ∧ c < ⊤ ∧ ∀ z ∈ U, ∀ w ∈ U,
      (D (addFun (h ω) (testCont g))).internal U z w =
        c * d (pair0On U (addFun (h ω) (testCont g))) z w

/-- **(MC)**: Möbius covariance of internal metrics modulo constants (GA4 (F3), σ₀ form) -/
def MCInput (D : DistC → ContMetric) (γ : ℝ) : Prop :=
  ∀ (ϕ : ℂ → ℂ) (W V : Set ℂ), IsMobius ϕ → IsConfNbhd ϕ W V →
  ∃ d : (TestC0On (ϕ '' V) → ℝ) → ℂ → ℂ → ℝ≥0∞, IsSigma0Metric D (ϕ '' V) d ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
      IsWholePlaneGFF h P → ∀ᵐ ω ∂P, ∃ c : ℝ≥0∞, 0 < c ∧ c < ⊤ ∧ ∀ z ∈ V, ∀ w ∈ V,
        (D (h ω)).internal V z w = c * d (confPair0 γ ϕ W V (h ω)) (ϕ z) (ϕ w)

/-! ## 4. Internal milestones -/

/-- **[3] Prop 2.1 (coupled)**: small-scale closeness, uniformly over a compact `K ⊆ V` -/
def ConfSmallScale (γ : ℝ) (D : DistC → ContMetric) : Prop :=
  ∀ (ϕ : ℂ → ℂ) (W V : Set ℂ), IsConfNbhd ϕ W V → ∀ K : Set ℂ, IsCompact K → K ⊆ V →
  ∀ δ : ℝ, 0 < δ → ∀ η : ℝ, 0 < η → ∃ r₀ : ℝ, 0 < r₀ ∧
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h hbar : Ω → DistC) (f : Ω → C(ℂ, ℝ)),
    IsWholePlaneGFF h P → IsWholePlaneGFF hbar P → Measurable f →
    (∀ᵐ ω ∂P, IsConfCoupling γ ϕ W V (h ω) (hbar ω) (f ω)) →
    ∀ z ∈ K, ∀ r ∈ Ioc (0 : ℝ) r₀,
      P {ω | ¬ ∀ u ∈ ball z r, ∀ v ∈ ball z r,
          confMetric D ϕ V (hbar ω) (f ω) u v ≤ ENNReal.ofReal ((D (h ω)).1 (u, v) +
            δ * r ^ (xiGamma γ * Q γ) * Real.exp (xiGamma γ * circleAvg (h ω) r z)) ∧
          ENNReal.ofReal ((D (h ω)).1 (u, v)) ≤ confMetric D ϕ V (hbar ω) (f ω) u v +
            ENNReal.ofReal (δ * r ^ (xiGamma γ * Q γ) *
              Real.exp (xiGamma γ * circleAvg (h ω) r z))} ≤ ENNReal.ofReal η

/-- **[3] Prop 3.1, one direction (coupled, on the domain)** -/
def ConfBiLipLE (γ : ℝ) (D : DistC → ContMetric) : Prop :=
  ∀ (ϕ : ℂ → ℂ) (W V : Set ℂ), IsConfNbhd ϕ W V →
  ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h hbar : Ω → DistC) (f : Ω → C(ℂ, ℝ)),
    IsWholePlaneGFF h P → IsWholePlaneGFF hbar P → Measurable f →
    (∀ᵐ ω ∂P, IsConfCoupling γ ϕ W V (h ω) (hbar ω) (f ω)) →
    ∀ᵐ ω ∂P, ∀ z ∈ V, ∀ w ∈ V,
      confMetric D ϕ V (hbar ω) (f ω) z w ≤ ENNReal.ofReal C * (D (h ω)).internal V z w

/-! ## 5. Shared and generic inputs -/

/-- a global `C^∞` near-identity diffeomorphism `Φ` (inverse `Ψ`), equal to the identity off a
compact set, whose inverse is holomorphic on `U` -/
structure IsNearIdDiffeo (Φ Ψ : ℂ → ℂ) (U : Set ℂ) (ε : ℝ) : Prop where
  contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ
  contDiff_inv : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ
  left_inv : ∀ z, Ψ (Φ z) = z
  right_inv : ∀ z, Φ (Ψ z) = z
  eq_id_off : ∃ R : ℝ, ∀ z, R ≤ ‖z‖ → Φ z = z
  deriv_close : ∀ z, ‖fderiv ℝ Φ z - ContinuousLinearMap.id ℝ ℂ‖ ≤ ε
  holo_inv : DifferentiableOn ℂ Ψ U

/-- **NIC** (near-identity conformal coupling; GA2 D5 in general form, shared with Lemma 4.2′;
the Gaussian-increment clause was added on BP1's finding, ruling G24):
`h ∘ Φ⁻¹ = h̄ + K` on `U` with `K` harmonic and `E(K z - K w)² ≲ ε² · Var(h_s(z) - h_s(w))`. -/
def NICInput : Prop :=
  ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 < C ∧ ∀ (Φ Ψ : ℂ → ℂ) (U : Set ℂ) (ε : ℝ), IsOpen U → 0 ≤ ε →
    ε ≤ ε₀ → IsNearIdDiffeo Φ Ψ U ε →
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (h hbar : Ω → DistC) (K : Ω → ℂ → ℝ),
      IsWholePlaneGFF h P ∧ IsWholePlaneGFF hbar P ∧
      Measurable (fun p : Ω × ℂ => K p.1 p.2) ∧
      (∀ ω, InnerProductSpace.HarmonicOnNhd (K ω) U) ∧
      -- the increments of `K` on `U` form a centred Gaussian process (BP1, needed by the
      -- chaining and Borell–TIS sup bounds of Lemma 4.2′; `K` is a white-noise functional)
      IsGaussianProcess (fun (p : U × U) (ω : Ω) => K ω p.1 - K ω p.2) P ∧
      (∀ p : U × U, ∫ ω, (K ω p.1 - K ω p.2) ∂P = 0) ∧
      (∀ᵐ ω ∂P, ∀ g τg : TestC, tsupport (g : ℂ → ℝ) ⊆ U →
          (∀ x, τg x = |LinearMap.det (fderiv ℝ Φ x : ℂ →ₗ[ℝ] ℂ)| * g (Φ x)) →
          h ω τg = hbar ω g + ∫ y, K ω y * g y) ∧
      ∀ z w : ℂ, ∀ s : ℝ, 0 < s → closedBall z s ⊆ U → closedBall w s ⊆ U →
        ∫ ω, (K ω z - K ω w) ^ 2 ∂P ≤
          C * ε ^ 2 * min (‖z - w‖ / s) (1 + Real.log (1 + ‖z - w‖ / s))

/-- **law-equality continuity** (Lusin substitute), for a sequence of couplings on possibly
different spaces: if `Y n` and `Y' n` both have law `μ` and are coordinatewise close in
probability, then `F (Y n)` and `F (Y' n)` are close in probability, for any Borel `F`. -/
def LawEqCont : Prop :=
  ∀ {T : Type} [PseudoMetricSpace T] [MeasurableSpace T] [BorelSpace T]
    [SecondCountableTopology T] (F : (ℕ → ℝ) → T), Measurable F →
    ∀ μ : Measure (ℕ → ℝ), IsProbabilityMeasure μ →
    ∀ (Ω : ℕ → Type) [∀ n, MeasurableSpace (Ω n)] (P : ∀ n, Measure (Ω n))
      [∀ n, IsProbabilityMeasure (P n)] (Y Y' : ∀ n, Ω n → ℕ → ℝ),
      (∀ n, Measurable (Y n)) → (∀ n, Measurable (Y' n)) →
      (∀ n, (P n).map (Y n) = μ) → (∀ n, (P n).map (Y' n) = μ) →
      (∀ k : ℕ, ∀ η : ℝ, 0 < η →
        Tendsto (fun n => P n {ω | η ≤ |Y n ω k - Y' n ω k|}) atTop (𝓝 0)) →
      ∀ δ : ℝ, 0 < δ →
        Tendsto (fun n => P n {ω | δ ≤ dist (F (Y n ω)) (F (Y' n ω))}) atTop (𝓝 0)

/-- **[3] Prop 3.6, improvement step**: [3] Steps 2–6 with the current a.s. bound `C` in place of
the optimal constant `C_*`; `θ = A/(A+1)` with `A` from [3] Lemma 3.9 (independent of `C`, `δ`). -/
def ConfImprove (γ : ℝ) (D : DistC → ContMetric) : Prop :=
  ∃ θ : ℝ, 0 ≤ θ ∧ θ < 1 ∧ ∀ δ : ℝ, 0 < δ → ∀ C : ℝ, 1 + δ ≤ C →
  ∀ (ϕ : ℂ → ℂ) (W V : Set ℂ), IsConfNbhd ϕ W V →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h hbar : Ω → DistC) (f : Ω → C(ℂ, ℝ)),
    IsWholePlaneGFF h P → IsWholePlaneGFF hbar P → Measurable f →
    (∀ᵐ ω ∂P, IsConfCoupling γ ϕ W V (h ω) (hbar ω) (f ω)) →
    (∀ᵐ ω ∂P, ∀ z ∈ V, ∀ w ∈ V,
      confMetric D ϕ V (hbar ω) (f ω) z w ≤ ENNReal.ofReal C * (D (h ω)).internal V z w) →
    ∀ᵐ ω ∂P, ∀ z ∈ V, ∀ w ∈ V,
      confMetric D ϕ V (hbar ω) (f ω) z w ≤
        ENNReal.ofReal (1 + δ + θ * (C - 1 - δ)) * (D (h ω)).internal V z w

/-- the iteration `C ↦ 1 + δ + θ (C - 1 - δ)` in closed form -/
lemma iter_closed (θ δ M : ℝ) (k : ℕ) :
    1 + δ + θ * ((1 + δ + θ ^ k * M) - 1 - δ) = 1 + δ + θ ^ (k + 1) * M := by
  ring

/-- **The iteration replaces `C_*`**: one-directional bi-Lipschitz plus the improvement step give
the one-sided conformal covariance. -/
theorem confCovLE_of_biLip_improve {γ : ℝ} {D : DistC → ContMetric} (hB : ConfBiLipLE γ D)
    (hI : ConfImprove γ D) : ConfCovLE γ D := by
  intro ϕ W V hϕ Ω _ P _ h hbar f hh hhb hf hc
  obtain ⟨C₀, hC₀, hB'⟩ := hB ϕ W V hϕ
  obtain ⟨θ, hθ0, hθ1, hI'⟩ := hI
  have hB0 := hB' P h hbar f hh hhb hf hc
  -- the bound with `C = 1 + δ + θ^k M δ`, `M δ = max C₀ (1+δ) - 1 - δ ≥ 0`
  have key : ∀ δ : ℝ, 0 < δ → ∀ k : ℕ, ∀ᵐ ω ∂P, ∀ z ∈ V, ∀ w ∈ V,
      confMetric D ϕ V (hbar ω) (f ω) z w ≤
        ENNReal.ofReal (1 + δ + θ ^ k * (max C₀ (1 + δ) - 1 - δ)) *
          (D (h ω)).internal V z w := by
    intro δ hδ k
    have hM : 0 ≤ max C₀ (1 + δ) - 1 - δ := by
      have := le_max_right C₀ (1 + δ); linarith
    induction k with
    | zero =>
      filter_upwards [hB0] with ω hω z hz w hw
      refine (hω z hz w hw).trans (mul_le_mul_left ?_ _)
      refine ENNReal.ofReal_le_ofReal ?_
      have := le_max_left C₀ (1 + δ); simp only [pow_zero, one_mul]; linarith
    | succ k ih =>
      have hC : 1 + δ ≤ 1 + δ + θ ^ k * (max C₀ (1 + δ) - 1 - δ) := by
        have : 0 ≤ θ ^ k * (max C₀ (1 + δ) - 1 - δ) := mul_nonneg (pow_nonneg hθ0 k) hM
        linarith
      have := hI' δ hδ _ hC ϕ W V hϕ P h hbar f hh hhb hf hc ih
      simpa only [iter_closed] using this
  -- countably many `δ = 1/(n+1)` and `k`
  have hall : ∀ᵐ ω ∂P, ∀ n k : ℕ, ∀ z ∈ V, ∀ w ∈ V,
      confMetric D ϕ V (hbar ω) (f ω) z w ≤
        ENNReal.ofReal (1 + (1 / ((n : ℝ) + 1)) +
          θ ^ k * (max C₀ (1 + (1 / ((n : ℝ) + 1))) - 1 - (1 / ((n : ℝ) + 1)))) *
          (D (h ω)).internal V z w := by
    rw [ae_all_iff]; intro n; rw [ae_all_iff]; intro k
    exact key _ (by positivity) k
  filter_upwards [hall] with ω hω z hz w hw
  set a := confMetric D ϕ V (hbar ω) (f ω) z w
  set b := (D (h ω)).internal V z w
  by_cases hb : b = ⊤
  · rw [hb]; exact le_top
  -- for each `n`, a bound with factor `1 + 2/(n+1)`
  have hn : ∀ n : ℕ, a ≤ ENNReal.ofReal (1 + 2 / ((n : ℝ) + 1)) * b := by
    intro n
    set δ : ℝ := 1 / ((n : ℝ) + 1) with hδdef
    have hδ : 0 < δ := by positivity
    set M : ℝ := max C₀ (1 + δ) - 1 - δ
    have hlim : Tendsto (fun k : ℕ => θ ^ k * M) atTop (𝓝 (0 * M)) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one hθ0 hθ1).mul_const M
    rw [zero_mul] at hlim
    obtain ⟨k, hk⟩ := (hlim.eventually (gt_mem_nhds hδ)).exists
    refine (hω n k z hz w hw).trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _)
    have h2 : 2 / ((n : ℝ) + 1) = δ + δ := by rw [hδdef]; ring
    rw [h2]; linarith
  have htend : Tendsto (fun n : ℕ => ENNReal.ofReal (1 + 2 / ((n : ℝ) + 1)) * b) atTop
      (𝓝 (ENNReal.ofReal 1 * b)) := by
    refine ENNReal.Tendsto.mul_const ?_ (Or.inr hb)
    refine ENNReal.tendsto_ofReal ?_
    have : Tendsto (fun n : ℕ => 2 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
      have := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (2 : ℝ)
      simpa [div_eq_mul_inv] using this
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).add this
  rw [ENNReal.ofReal_one, one_mul] at htend
  exact ge_of_tendsto' htend hn

/-- **universal locality**: one locality functional for countably many GFF-plus-continuous
fields, possibly on different probability spaces (coin mixture; GA5 (a9) generalized) -/
def UniversalLocality (D : DistC → ContMetric) : Prop :=
  ∀ (U : TopologicalSpace.Opens ℂ) (ι : Type) [Countable ι] (Ω : ι → Type)
    [∀ i, MeasurableSpace (Ω i)] (P : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (P i)]
    (g : ∀ i, Ω i → DistC), (∀ i, IsGFFPlusCont (g i) (P i)) →
    ∃ F : DistOn U → (ℂ → ℂ → ℝ≥0∞), Measurable F ∧
      ∀ i, ∀ᵐ ω ∂(P i), ∀ z ∈ U, ∀ w ∈ U,
        (D (g i ω)).internal U z w = F (restrictTo U (g i ω)) z w

/-- events determined, modulo the circle average at radius `c₀ r`, by the field on the annulus
`A_{s₁c₀r, s₂c₀r}(w)` -/
def IsAnnulusLocal {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (h : Ω → DistC)
    (E : ℂ → ℝ → Set Ω) (c₀ s₁ s₂ : ℝ) : Prop :=
  ∀ w : ℂ, ∀ r : ℝ, 0 < r →
    AEEventIn P (fieldSigma (fun ω => addConst (h ω) (-circleAvg (h ω) (c₀ * r) w))
      (annulus w (s₁ * (c₀ * r)) (s₂ * (c₀ * r)))) (E w r)

/-- **generic good-annulus covering** (LM Lemma 4.2 / GM Lemmas 3.8–3.9 / [3] Lemma 3.11, `N = 0`) -/
def CoverLemma : Prop :=
  ∀ (c₀ s₁ s₂ : ℝ) (N : ℕ), 0 < c₀ → 0 < s₁ → s₁ < s₂ → s₂ < 1 → 2 ≤ N →
    (N : ℝ)⁻¹ ≤ s₁ → ∀ q : ℝ, 0 < q → ∃ p : ℝ, 0 < p ∧ p < 1 ∧
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
    IsWholePlaneGFF h P → ∀ E : ℂ → ℝ → Set Ω, IsAnnulusLocal P h E c₀ s₁ s₂ →
    ∀ K : Set ℂ, IsCompact K → ∀ r₀ : ℝ, 0 < r₀ →
    (∀ w : ℂ, infDist w K ≤ 1 → ∀ r ∈ Ioc (0 : ℝ) r₀, ENNReal.ofReal p ≤ P (E w r)) →
    ∃ C ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε ∈ Ioo (0 : ℝ) ε₁,
      P {ω | ¬ ∀ z ∈ K, ∃ k : ℕ, ∃ m : ℤ × ℤ, ε ^ 2 ≤ (N : ℝ)⁻¹ ^ k * ε ∧
        ‖z - GM.gridPt (ε ^ 2 / 4) m‖ < (N : ℝ)⁻¹ ^ k * ε / 2 ∧
        ω ∈ E (GM.gridPt (ε ^ 2 / 4) m) ((N : ℝ)⁻¹ ^ k * ε)} ≤ ENNReal.ofReal (C * ε ^ q)

/-- **LM Theorem 1.6, deterministic chaining, extended-metric form** (generalizes
`LQGMetric.LM.lm_chain_det` from a `ContMetric` to any `[0,∞]`-valued function with the triangle
inequality, as needed for the domain metric `D^ϕ`) -/
def ChainDetExt : Prop :=
  ∀ (d : ℂ → ℂ → ℝ≥0∞), (∀ x y z, d x z ≤ d x y + d y z) → (∀ x, d x x = 0) →
  ∀ {C ε ρ : ℝ}, 0 ≤ C → 0 < ρ → ∀ (P : ℝ → ℂ), ContinuousOn P (Icc 0 1) →
  ∀ (ℓ : ℝ → ℝ), MonotoneOn ℓ (Icc 0 1) → ∀ good : ℂ → ℝ → Prop,
    (∀ s ∈ Icc (0 : ℝ) 1, ∃ w r, ρ ≤ r ∧ r ≤ ε ∧ ‖P s - w‖ < r / 2 ∧ good w r) →
    (∀ w r, good w r → ∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1, a ≤ b →
      ‖P a - w‖ < r / 2 → ‖P b - w‖ = r →
      ∀ u ∈ sphere w r, ∀ v ∈ sphere w r, d u v ≤ ENNReal.ofReal (C * (ℓ b - ℓ a))) →
    ∃ x y, ‖x - P 0‖ ≤ 2 * ε ∧ ‖y - P 1‖ ≤ 2 * ε ∧ d x y ≤ ENNReal.ofReal (C * (ℓ 1 - ℓ 0))

end SmallGammaGeodesics.CC
