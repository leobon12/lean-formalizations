import HigherDimLQGMetric.Weak.DetDefs
import HigherDimLQGMetric.Markov.Defs
import HigherDimLQGMetric.DGZ.Interfaces
import HigherDimLQGMetric.Frozen.AEps
import HigherDimLQGMetric.Frozen.LfppDist
import HigherDimLQGMetric.Frozen.NormalizedAtScale
import HigherDimLQGMetric.Frozen.IsLGFPlusBddCont
import HigherDimLQGMetric.Frozen.TendstoInProbLU
import HigherDimLQGMetric.Frozen.IsWeakExpMetric
import HigherDimLQGMetric.Frozen.ConvMollify
import HigherDimLQGMetric.Frozen.UnitSphereProb
import HigherDimLQGMetric.Frozen.IsNormalizedLGF
import HigherDimLQGMetric.Frozen.SphereAvg
import HigherDimLQGMetric.Frozen.ContMetricInternal
import HigherDimLQGMetric.Frozen.ContMetricIsLength
import HigherDimLQGMetric.Frozen.WeylScale
import HigherDimLFPP.Field.LogCov
import LQGMetric.Prob.CondIndepEv
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Interface statements of blocks B1/B3 (orchestrator-owned; ruling M30)

The statements of [1] §§2–3 that the B1/B3 packets prove (L1e, L2c, L6a, L6c, L7a–L7c, L8) and that later packets consume
before they land (the interface pattern: a consumer takes the named `Prop` as a hypothesis, the assembly discharges it).
Copied **verbatim** from MA5 Details (c) (`planning/audits/statements/MA5Surface.lean.txt`, §§10–14; namespace
`MA5Scratch` replaced by `HigherDimLQGMetric`), omitting the definitions already in the library (`Weak/DetDefs.lean`:
`fieldLfppE`, `fieldLfpp`, `toCMapRd`, `supPairs`, `infPairs`, `IsProperFn`, `IsContLengthFn`, `L6c_lengthLimit`,
`L6d_weylCont`, `L6e_weylLfpp`; `Markov/Defs.lean`: `fieldSigmaRd`, `extOpen`, `ofFunOn`, `DMarkovRd`; the frozen
definitions) and MA5's probe-only `DGZExport`, with one change (**ruling M30**): the B2 premise `DGZExport d ξ κ →` of
`L6a_tight`, `L6b_cross`, `L6f_tightScales`, `L7a_locality`, `L7f_determined`, `L8_thm13` is replaced by MA7's export,
`(∃ Q : ℝ, DGZ.DGZHyp d κ ξ Q ∧ DGZ.RealEpsAdapterShape d κ ξ Q) →` (MA5 §3.3 note 1, MA7 G21: the adapter of packet L5c
is the B2 → B3 interface; MA5's A6 is MA7's D-ADP); and (**ruling M31**) `L7b_copies` takes `2 ≤ d`. Workers import this module and never edit or redefine it.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
-- the σ-algebras below are used through `MeasurableSet[...]`, not as instances
set_option warn.classDefReducibility false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Distributions ENNReal FourierTransform

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd e₁)

/-! ## The lower median (MA5 §7) -/

/-- lower median `inf {m : μ(X ≤ m) ≥ 1/2}` -/
def lowerMedian {α : Type*} [MeasurableSpace α] (μ : Measure α) (X : α → ℝ) : ℝ :=
  sInf {m : ℝ | (2 : ℝ≥0∞)⁻¹ ≤ μ {x | X x ≤ m}}

/-! ## B1 statements (MA5 §10): L1e, L2c -/

section B1
variable {d : ℕ}

/-- `(h * K_ε)(x) - ⨍_{∂B_1(0)} h * K_ε` -/
def convMollifyNorm (κ : Rd d → ℝ) (ε : ℝ) (h : DistRd d) (x : Rd d) : ℝ :=
  convMollify κ ε h x - ∫ u, convMollify κ ε h u ∂(unitSphereProb d)

/-- **L1e** (= [1] Prop. 1.10 / Lemma 2.9, law identity, corrected form): for a normalized LGF
`h`, the convolution field normalized by its unit-sphere average has the law of the white-noise
field over `(ε, ∞)` paired with `δ_x - σ₁` (HigherDimLFPP's model), as a random continuous
function. -/
def L1e_law : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∀ κ : Rd d → ℝ, HigherDimLFPP.IsLFPPKernel κ → ∀ ε : ℝ, 0 < ε →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistRd d),
    IsNormalizedLGF h P →
  ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (W : HigherDimLFPP.WN d → Ω' → ℝ) (Φ : Rd d → Ω' → ℝ), HigherDimLFPP.IsWhiteNoise P' W →
    (∀ ω', Continuous fun x => Φ x ω') →
    (∀ x, Φ x =ᵐ[P'] W (HigherDimLFPP.bandVecM κ (Ioi ε) (Measure.dirac x) (unitSphereProb d))) →
    (∀ᵐ ω ∂P, Continuous (convMollifyNorm κ ε (h ω))) ∧
    ∀ A : Set (Rd d → ℝ), MeasurableSet A →
      P {ω | convMollifyNorm κ ε (h ω) ∈ A} = P' {ω' | (fun x => Φ x ω') ∈ A}

/-- radial smooth bump `ψ_{a,b}`: `1` on `B̄_a(0)`, support `B_b(0)` for `0 < a < b`, built from
mathlib's radial base `ContDiffBumpBase.ofInnerProductSpace` (mathlib's `ContDiffBump` uses a
`Classical.choice` profile that is not provably radial; 2D DEV-DFB2c) -/
def radBump (a b : ℝ) (x : Rd d) : ℝ :=
  (ContDiffBumpBase.ofInnerProductSpace (Rd d)).toFun (b / a) (a⁻¹ • x)

lemma radBump_radial (a b : ℝ) {x y : Rd d} (h : ‖x‖ = ‖y‖) :
    radBump a b x = radBump a b y := by
  simp only [radBump, ContDiffBumpBase.ofInnerProductSpace, norm_smul, h]

lemma contDiff_radBump {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (radBump (d := d) a b) := by
  have h1 : 1 < b / a := (one_lt_div ha).2 hab
  exact (ContDiffBumpBase.ofInnerProductSpace (Rd d)).smooth.comp_contDiff
    (contDiff_const.prodMk (contDiff_id.const_smul a⁻¹)) (fun _ => ⟨h1, mem_univ _⟩)

lemma hasCompactSupport_radBump {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    HasCompactSupport (radBump (d := d) a b) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Rd d) b) fun x hx => ?_
  rw [Metric.mem_closedBall, dist_zero_right, not_le] at hx
  have hba : 0 < b / a - 1 := sub_pos.2 ((one_lt_div ha).2 hab)
  have hx' : b / a < ‖a⁻¹ • x‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos ha, inv_mul_eq_div]
    exact div_lt_div_of_pos_right hx ha
  simp only [radBump, ContDiffBumpBase.ofInnerProductSpace]
  exact Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg
    (by linarith) hba.le)

lemma contDiff_truncKer {κ : Rd d → ℝ} (hK : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (convKernel κ))
    {ε : ℝ} (hε : 0 < ε) (z : Rd d) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w => convKernelEps κ ε (z - w) * radBump (Real.sqrt ε / 2) (Real.sqrt ε) (z - w)) := by
  have hs := Real.sqrt_pos.2 hε
  refine ContDiff.mul ?_ ((contDiff_radBump (by positivity) (by linarith)).comp
    (contDiff_const.sub contDiff_id))
  unfold convKernelEps
  exact contDiff_const.mul (hK.comp ((contDiff_const.sub contDiff_id).const_smul _))

lemma hasCompactSupport_truncKer (κ : Rd d → ℝ) {ε : ℝ} (hε : 0 < ε) (z : Rd d) :
    HasCompactSupport
      (fun w => convKernelEps κ ε (z - w) * radBump (Real.sqrt ε / 2) (Real.sqrt ε) (z - w)) := by
  have hs := Real.sqrt_pos.2 hε
  have h1 : HasCompactSupport
      (fun w : Rd d => radBump (Real.sqrt ε / 2) (Real.sqrt ε) (z - w)) :=
    (hasCompactSupport_radBump (d := d) (by positivity) (by linarith)).comp_homeomorph
      (Homeomorph.subLeft z)
  exact h1.mul_left

open Classical in
/-- `w ↦ Ψ_ε(z-w) K_ε(z-w)` as a test function, `Ψ_ε = ψ_{√ε/2, √ε}` radial ([1] (2.19); junk `0`
unless `K` is smooth and `ε > 0`) -/
def truncTest (κ : Rd d → ℝ) (ε : ℝ) (z : Rd d) : TestRd d :=
  if hK : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (convKernel κ) ∧ 0 < ε then
    { toFun := fun w => convKernelEps κ ε (z - w) * radBump (Real.sqrt ε / 2) (Real.sqrt ε) (z - w)
      contDiff' := contDiff_truncKer hK.1 hK.2 z
      hasCompactSupport' := hasCompactSupport_truncKer κ hK.2 z
      tsupport_subset' := subset_univ _ }
  else 0

/-- `h̄*_ε(z) = h * (Ψ_ε K_ε)(z)` ([1] (2.19)): a genuine pairing, local at scale `√ε` -/
def truncMollify (κ : Rd d → ℝ) (ε : ℝ) (h : DistRd d) (z : Rd d) : ℝ := h (truncTest κ ε z)

/-- **L2c** (= [1] Lemma 2.12): a.s. `h*_ε - h̄*_ε → 0` uniformly on compacts as `ε ↓ 0`. -/
def L2c_trunc : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∀ κ : Rd d → ℝ, HigherDimLFPP.IsLFPPKernel κ →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistRd d),
    IsNormalizedLGF h P → ∀ᵐ ω ∂P, ∀ R : ℝ, 0 < R →
      TendstoUniformlyOn (fun ε z => convMollify κ ε (h ω) z - truncMollify κ ε (h ω) z) 0
        (𝓝[>] 0) (Metric.closedBall (0 : Rd d) R)

end B1

/-! ## Tightness of a family of random metrics (MA5 §11) -/

section B2Interface
variable {d : ℕ}

/-- tightness of the laws of `X i`, `i ∈ S`, with every law in the closure carried by continuous
metrics (MA0's `TightOver`, for an arbitrary index type) -/
def TightFamily {ι Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ι → Ω → C(Rd d × Rd d, ℝ)) (S : Set ι) : Prop :=
  (∀ i ∈ S, AEMeasurable (X i) P) ∧
  IsTightMeasureSet {μ | ∃ i ∈ S, μ = P.map (X i)} ∧
  ∀ μ : ProbabilityMeasure C(Rd d × Rd d, ℝ),
    μ ∈ closure {ν : ProbabilityMeasure C(Rd d × Rd d, ℝ) |
      ∃ i ∈ S, (ν : Measure C(Rd d × Rd d, ℝ)) = P.map (X i)} →
    ∀ᵐ D ∂(μ : Measure C(Rd d × Rd d, ℝ)), IsContinuousMetric D ∧ IsProperFn D

end B2Interface

/-! ## B3 statements, packet L6 (MA5 §12) -/

section L6
variable {d : ℕ}

/-- the white-noise model's kernel exponent (kernel-specific `Q`, so that B3 does not depend on
D-KI): `log D_ε / log ε → 1 - ξ Q` for this `κ` -/
def IsKernelExponent (d : ℕ) (κ : Rd d → ℝ) (ξ Q : ℝ) : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : HigherDimLFPP.WN d → Ω → ℝ),
    HigherDimLFPP.IsWhiteNoise P W →
  ∀ H : ℝ → Rd d → Ω → ℝ, (∀ ε ∈ Ioo (0 : ℝ) 1, HigherDimLFPP.IsBandVersion P W κ ε 1 (H ε)) →
    HigherDimLFPP.IsLFPPExponent H P ξ (1 - ξ * Q)

/-- **L6a** (= corrected [1] Lemma 3.3, all `ε ∈ (0,1)`, fixed `𝔞_ε` of the normalized LGF):
for an LGF plus a bounded continuous function, `𝔞_ε⁻¹ D^ε_h` is tight and every limit law is
carried by proper continuous metrics. -/
def L6a_tight (d : ℕ) (ξ : ℝ) (κ : Rd d → ℝ) : Prop :=
  (∃ Q : ℝ, DGZ.DGZHyp d κ ξ Q ∧ DGZ.RealEpsAdapterShape d κ ξ Q) →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistRd d),
    IsLGFPlusBddCont h P →
    (∀ ε ∈ Ioo (0 : ℝ) 1, 0 < aEps κ ξ ε) ∧
    TightFamily P (fun ε ω => toCMapRd ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω))) (Ioo 0 1)

/-- **L6b** (= corrected [1] Lemma 3.4, uniform in scale and centre) -/
def L6b_cross (d : ℕ) (ξ : ℝ) (κ : Rd d → ℝ) : Prop :=
  (∃ Q : ℝ, DGZ.DGZHyp d κ ξ Q ∧ DGZ.RealEpsAdapterShape d κ ξ Q) →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistRd d),
    IsLGFPlusBddCont h P → ∀ p : ℝ, p < 1 → ∀ C : ℝ, 0 < C →
    ∃ R ε₀ : ℝ, 1 < R ∧ 0 < ε₀ ∧ ∀ r : ℝ, 0 < r → ∀ x : Rd d, ∀ ε ∈ Ioo (0 : ℝ) (ε₀ * r),
      ENNReal.ofReal p ≤ P {ω | supPairs (lfppDist κ ξ ε (h ω)) (Metric.ball x r) ≤
        ENNReal.ofReal C⁻¹ * infPairs (lfppDist κ ξ ε (h ω)) (Metric.sphere x r)
          (Metric.sphere x (R * r))}

/-- joint convergence in law of `(h, X n)` to `(h, Y)` with the field fixed (stable convergence;
equivalent to LQGMetric's `pairJ`-coordinate form, D90 there) -/
def StablyTendstoLU {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (h : Ω → DistRd d)
    (X : ℕ → Ω → C(Rd d × Rd d, ℝ)) (Y : Ω → C(Rd d × Rd d, ℝ)) : Prop :=
  ∀ g : DistRd d → ℝ, Measurable g → (∃ C, ∀ x, |g x| ≤ C) →
  ∀ φ : C(Rd d × Rd d, ℝ) → ℝ, Continuous φ → (∃ C, ∀ x, |φ x| ≤ C) →
    Tendsto (fun n => ∫ ω, g (h ω) * φ (X n ω) ∂P) atTop (𝓝 (∫ ω, g (h ω) * φ (Y ω) ∂P))

/-- the normalized LFPP sequence along `εs` -/
def lfppSeq (κ : Rd d → ℝ) (ξ : ℝ) (εs : ℕ → ℝ) (h : DistRd d) (n : ℕ) : C(Rd d × Rd d, ℝ) :=
  toCMapRd ((aEps κ ξ (εs n))⁻¹ • lfppDist κ ξ (εs n) h)

/-- **L6f** (= corrected [1] Lemma 3.7): with `𝔠_r` := lower median of
`e^{-ξ h_r(0)} D_h(0, r e₁)` (the paper's limit `lim 𝔞_{ε_n}/(r 𝔞_{ε_n/r})` need not exist),
the rescaled limits are tight over all `r > 0` with continuous-metric limits. -/
def L6f_tightScales (d : ℕ) (ξ : ℝ) (κ : Rd d → ℝ) : Prop :=
  (∃ Q : ℝ, DGZ.DGZHyp d κ ξ Q ∧ DGZ.RealEpsAdapterShape d κ ξ Q) → ∀ εs : ℕ → ℝ, (∀ n, 0 < εs n) → Tendsto εs atTop (𝓝 0) →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistRd d)
    (Dh : Ω → ContMetric d), IsNormalizedLGF h P → Measurable Dh →
    StablyTendstoLU P h (fun n ω => lfppSeq κ ξ εs (h ω) n) (fun ω => (Dh ω).1) →
    let c : ℝ → ℝ := fun r =>
      lowerMedian P (fun ω => Real.exp (-ξ * sphereAvg (h ω) r 0) * (Dh ω).1 (0, r • e₁ d))
    (∀ r : ℝ, 0 < r → 0 < c r) ∧
      TightFamily P (fun r ω => normalizedAtScale ξ (fun _ => (Dh ω)) c (h ω) r) (Ioi 0)

end L6

/-! ## B3 statements, packet L7 (MA5 §13) -/

section L7
variable {d : ℕ} {Ω : Type*}

/-- `σ(h)` -/
def fullSigmaRd (h : Ω → DistRd d) : MeasurableSpace Ω := MeasurableSpace.comap h inferInstance

/-- `σ(I(·,·;V))` for a random family of internal metrics -/
def famSigmaRd (I : Ω → Set (Rd d) → Rd d → Rd d → ℝ≥0∞) (V : Set (Rd d)) :
    MeasurableSpace Ω :=
  MeasurableSpace.comap (fun ω => I ω V) inferInstance

/-- the internal metrics `V ↦ D(·,·;V)` of a random metric -/
def internalFamRd (D : Ω → ContMetric d) : Ω → Set (Rd d) → Rd d → Rd d → ℝ≥0∞ :=
  fun ω V => (D ω).internal V

/-- the locality test sets: bounded open sets with Lebesgue-null boundary (boxes, shells,
balls, dyadic domains) -/
def IsNiceOpen (V : TopologicalSpace.Opens (Rd d)) : Prop :=
  Bornology.IsBounded (V : Set (Rd d)) ∧ volume (frontier (V : Set (Rd d))) = 0

/-- **Joint locality, MA5 form** (replaces [1] Def. 3.9/3.12): for nice `V`, the internal
metrics on `V` are conditionally independent of `(h, internal metrics on ℝ^d ∖ V̄)` given
`h|_V`. (Equivalent to: conditional independence given `h` of the inside and outside internal
metrics, plus `σ(h|_V)`-measurability of the conditional law of the inside ones.) -/
def IsJointlyLocalRd [MeasurableSpace Ω] (P : Measure Ω) (h : Ω → DistRd d)
    (I₁ I₂ : Ω → Set (Rd d) → Rd d → Rd d → ℝ≥0∞) : Prop :=
  ∀ V : TopologicalSpace.Opens (Rd d), IsNiceOpen V →
    LQGMetric.CondIndepEv (fieldSigmaRd h V) (famSigmaRd I₁ V ⊔ famSigmaRd I₂ V)
      (fullSigmaRd h ⊔ famSigmaRd I₁ (closure (V : Set (Rd d)))ᶜ ⊔
        famSigmaRd I₂ (closure (V : Set (Rd d)))ᶜ) P

/-- **Joint ξ-additivity, MA5 form** (replaces [1] Def. 3.10/3.12) -/
def IsXiAdditiveRd [MeasurableSpace Ω] (ξ : ℝ) (P : Measure Ω) (h : Ω → DistRd d)
    (D₁ D₂ : Ω → ContMetric d) : Prop :=
  Measurable D₁ ∧ Measurable D₂ ∧ (∀ᵐ ω ∂P, (D₁ ω).IsLength ∧ (D₂ ω).IsLength) ∧
  ∀ (z : Rd d) (r : ℝ), 0 < r →
    IsJointlyLocalRd P (fun ω => addConst (h ω) (-sphereAvg (h ω) r z))
      (fun ω V u v => ENNReal.ofReal (Real.exp (-ξ * sphereAvg (h ω) r z)) * (D₁ ω).internal V u v)
      (fun ω V u v => ENNReal.ofReal (Real.exp (-ξ * sphereAvg (h ω) r z)) * (D₂ ω).internal V u v)

/-- the open shell `A_{a,b}(z) = B_b(z) ∖ B̄_a(z)` -/
def shellOpen (z : Rd d) (a b : ℝ) : TopologicalSpace.Opens (Rd d) :=
  ⟨Metric.ball z b \ Metric.closedBall z a, Metric.isOpen_ball.sdiff Metric.isClosed_closedBall⟩

/-- **L7a** (= corrected [1] Lemma 3.11): subsequential limits are ξ-additive local metrics. -/
def L7a_locality (d : ℕ) (ξ : ℝ) (κ : Rd d → ℝ) : Prop :=
  (∃ Q : ℝ, DGZ.DGZHyp d κ ξ Q ∧ DGZ.RealEpsAdapterShape d κ ξ Q) → DMarkovRd → ∀ εs : ℕ → ℝ, (∀ n, 0 < εs n) → Tendsto εs atTop (𝓝 0) →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistRd d)
    (Dh : Ω → ContMetric d), IsNormalizedLGF h P → Measurable Dh →
    StablyTendstoLU P h (fun n ω => lfppSeq κ ξ εs (h ω) n) (fun ω => (Dh ω).1) →
    IsXiAdditiveRd ξ P h Dh Dh

/-- **L7b** (= [1] p. 26, TeX l. 1246, omitted proof; LM Lemma 1.4): two ξ-additive local
metrics which are conditionally independent given `h` are jointly ξ-additive local. -/
def L7b_copies : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ (ξ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (D₁ D₂ : Ω → ContMetric d), IsNormalizedLGF h P →
    IsXiAdditiveRd ξ P h D₁ D₁ → IsXiAdditiveRd ξ P h D₂ D₂ →
    LQGMetric.CondIndepEv (fullSigmaRd h) (MeasurableSpace.comap D₁ inferInstance)
      (MeasurableSpace.comap D₂ inferInstance) P →
    IsXiAdditiveRd ξ P h D₁ D₂

/-- **G3 export (functional form of [S] Lemma A.1)**: `E ∏ F_i ≤ ∏ (E F_i^K)^{1/K}` for
`[0,1]`-valued functions of the field modulo constants on the shells `A_{a r_i, b r_i}(z)`. -/
def ShellDecouplingFun : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∀ a b q : ℝ, 0 < a → a < 1 → 1 < b → 0 < q → q < 1 →
  ∃ K : ℝ, 1 ≤ K ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistRd d), IsWholeSpaceLGF h P → ∀ (z : Rd d) (r : ℕ → ℝ),
      (∀ i, 0 < r i) → (∀ i, r (i + 1) ≤ q * r i) →
      ∀ (I : Finset ℕ) (F : ℕ → Ω → ℝ),
        (∀ i, Measurable[fieldSigmaRd (fun ω => addConst (h ω) (-sphereAvg (h ω) (r i) z))
          (shellOpen z (a * r i) (b * r i))] (F i)) →
        (∀ i ω, 0 ≤ F i ω ∧ F i ω ≤ 1) →
        ∫ ω, ∏ i ∈ I, F i ω ∂P ≤ ∏ i ∈ I, (∫ ω, F i ω ^ K ∂P) ^ K⁻¹

/-- the rescaled internal-metric family `e^{-ξ h_r(z)} D(·,·;·)` -/
def rescFam (ξ : ℝ) (h : Ω → DistRd d) (D : Ω → ContMetric d) (z : Rd d) (r : ℝ) :
    Ω → Set (Rd d) → Rd d → Rd d → ℝ≥0∞ :=
  fun ω V u v => ENNReal.ofReal (Real.exp (-ξ * sphereAvg (h ω) r z)) * (D ω).internal V u v

open Classical in
/-- **L7c** (= [1] Lemma 3.14 via D-E4′, separated shells): high marginal probabilities of
events measurable w.r.t. the shell field mod constants and the rescaled internal metrics give
exponential bounds on the number of failures. -/
def L7c_metricShell : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∀ a b q : ℝ, 0 < a → a < 1 → 1 < b → 0 < q → b * q < a →
  ∀ A θ : ℝ, 0 < A → 0 < θ → θ < 1 → ∃ p : ℝ, p < 1 ∧
    ∀ (ξ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistRd d) (D₁ D₂ : Ω → ContMetric d), IsNormalizedLGF h P →
      IsXiAdditiveRd ξ P h D₁ D₂ → ∀ (z : Rd d) (r : ℕ → ℝ), (∀ i, 0 < r i) →
      (∀ i, r (i + 1) ≤ q * r i) → ∀ E : ℕ → Set Ω,
      (∀ i, MeasurableSet[fieldSigmaRd (fun ω => addConst (h ω) (-sphereAvg (h ω) (r i) z))
          (shellOpen z (a * r i) (b * r i)) ⊔
        famSigmaRd (rescFam ξ h D₁ z (r i)) (shellOpen z (a * r i) (b * r i)) ⊔
        famSigmaRd (rescFam ξ h D₂ z (r i)) (shellOpen z (a * r i) (b * r i))] (E i)) →
      (∀ i, ENNReal.ofReal p ≤ P (E i)) →
      ∀ n : ℕ, P {ω | (((Finset.range n).filter fun i => ω ∈ E i).card : ℝ) < θ * n} ≤
        ENNReal.ofReal (Real.exp (-A * n))

/-- `sup_{u,v ∈ A} D(u,v;U)` -/
def internalDiamRd (D : ContMetric d) (A U : Set (Rd d)) : ℝ≥0∞ :=
  ⨆ u ∈ A, ⨆ v ∈ A, D.internal U u v

/-- **L7d** (= corrected [1] Prop. 3.13; stack chaining of MA1 A18): a universal `p` such that
the shell condition with probability `≥ p` at every centre and scale gives `D₂ ≤ C D₁` a.s. -/
def L7d_bilip : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∃ p : ℝ, 0 < p ∧ p < 1 ∧
    ∀ (ξ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistRd d) (D₁ D₂ : Ω → ContMetric d), IsNormalizedLGF h P →
      IsXiAdditiveRd ξ P h D₁ D₂ → ∀ C : ℝ, 0 < C →
      (∀ z : Rd d, ∀ r : ℝ, 0 < r → ENNReal.ofReal p ≤ P {ω |
        internalDiamRd (D₂ ω) (Metric.sphere z r) (shellOpen z (r / 2) (2 * r)) ≤
          ENNReal.ofReal C *
            infPairs (D₁ ω).1 (Metric.sphere z (r / 2)) (Metric.sphere z r)}) →
      ∀ᵐ ω ∂P, ∀ x y : Rd d, (D₂ ω).1 (x, y) ≤ C * (D₁ ω).1 (x, y)

/-- **L7e** (= corrected [1] Prop. 3.15; LM Thm 1.7, 2D D107 route): a local metric which is
bi-Lipschitz (deterministic constant) to a conditionally independent copy is determined by `h`
(no properness, no measurable selection of paths). -/
def L7e_measurable : Prop :=
  ∀ (d : ℕ) (ξ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (D D' : Ω → ContMetric d) (C : ℝ), IsNormalizedLGF h P →
    IsXiAdditiveRd ξ P h D D →
    LQGMetric.CondIndepEv (fullSigmaRd h) (MeasurableSpace.comap D inferInstance)
      (MeasurableSpace.comap D' inferInstance) P →
    P.map (fun ω => (h ω, D ω)) = P.map (fun ω => (h ω, D' ω)) → 0 < C →
    (∀ᵐ ω ∂P, ∀ x y : Rd d, (D' ω).1 (x, y) ≤ C * (D ω).1 (x, y)) →
    LQGMetric.AEDeterminedBy D h P

/-- **L7f** (= [1] Lemma 3.16): subsequential limits are determined by `h`, and the LFPP
converges in probability along the subsequence. -/
def L7f_determined (d : ℕ) (ξ : ℝ) (κ : Rd d → ℝ) : Prop :=
  (∃ Q : ℝ, DGZ.DGZHyp d κ ξ Q ∧ DGZ.RealEpsAdapterShape d κ ξ Q) → DMarkovRd → ShellDecouplingFun → ∀ εs : ℕ → ℝ, (∀ n, 0 < εs n) →
  Tendsto εs atTop (𝓝 0) →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistRd d)
    (Dh : Ω → ContMetric d), IsNormalizedLGF h P → Measurable Dh →
    StablyTendstoLU P h (fun n ω => lfppSeq κ ξ εs (h ω) n) (fun ω => (Dh ω).1) →
    LQGMetric.AEDeterminedBy Dh h P ∧
      TendstoInProbLU P (fun n ω => lfppSeq κ ξ εs (h ω) n) atTop (fun ω => (Dh ω).1)

end L7

/-! ## B3 statement, packet L8 (MA5 §14) -/

section L8
variable {d : ℕ}

/-- **L8** (= corrected [1] Theorem 1.3, for one nonnegative kernel; the global measurable
assignment is the patched truncated-kernel limit, Details (a) A18). -/
def L8_thm13 (d : ℕ) (ξ : ℝ) (κ : Rd d → ℝ) : Prop :=
  (∃ Q : ℝ, DGZ.DGZHyp d κ ξ Q ∧ DGZ.RealEpsAdapterShape d κ ξ Q) → DMarkovRd → ShellDecouplingFun →
  ∀ εs : ℕ → ℝ, (∀ n, 0 < εs n) → Tendsto εs atTop (𝓝 0) →
  ∃ (φ : ℕ → ℕ) (D : DistRd d → ContMetric d) (c : ℝ → ℝ), StrictMono φ ∧ IsWeakExpMetric d ξ D c ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistRd d),
      IsLGFPlusBddCont h P →
      TendstoInProbLU P (fun n ω => (aEps κ ξ (εs (φ n)))⁻¹ • lfppDist κ ξ (εs (φ n)) (h ω)) atTop
        (fun ω => (D (h ω)).1)

/-- the assembled B1/B3 statement: for every `d ≥ 2`, nonnegative admissible `κ` and `ξ` whose
kernel exponent exceeds `√(2d)`, [2]'s export implies [1] Theorem 1.3 -/
def B3Goal : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∀ κ : Rd d → ℝ, HigherDimLFPP.IsLFPPKernel κ → ∀ ξ Q : ℝ, 0 < ξ →
    IsKernelExponent d κ ξ Q → Real.sqrt (2 * d) < Q → L8_thm13 d ξ κ

end L8

end HigherDimLQGMetric
