import HigherDimLQGMetric.Frozen.IsWholeSpaceLGF
import HigherDimLQGMetric.Frozen.SphereAvg
import HigherDimLQGMetric.Frozen.ContMetricInternal

/-!
# Shared definitions of the packets (ruling M15 (iii))

The definitions that the planning audits' statement files (MA1, MA3, MA4, MA6) duplicate, defined once here,
verbatim from `planning/audits/statements/MA3Statements.lean.txt` (identical in MA4; `setDistIn` identical in
MA6). Orchestrator-owned: workers import this module and never edit it (WORKERS.md).

* `ann z a b` is the open annulus `A_{a,b}(z)` of [S] l. 174 (MA6's `shell` is the same set: `ann_eq_ball_diff`);
  `annCl z a b` the closed annulus.
* `sNorm ξ Q h r z = r^{ξQ} e^{ξ h_r(z)}`, the normalizer of [S].
* `setDistIn D V A B = inf_{u ∈ A, v ∈ B} D(u, v; V)`.
* `fieldSigma0 h V` (`σ(h|_V)` modulo additive constants: mean-zero pairings supported in `V`), `fieldSigmaOn h V`
  (all pairings supported in `V`) and `AEEventIn P m E` (`E` is a.s. equal to an `m`-event).
* `ShellInputA1 d`: [S] Lemma A.1 / (E4) in MA3's interface form (consumed by W1 and the source-section packets,
  proved by packet G3).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
-- the σ-algebras below are used through `MeasurableSet[...]`, not as instances
set_option warn.classDefReducibility false

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory Set
open HigherDimLFPP (Rd)
open scoped ENNReal

variable {d : ℕ}

/-- open annulus `A_{a,b}(z) = B_b(z) ∖ B̄_a(z)` ([S] l. 174) -/
def ann (z : Rd d) (a b : ℝ) : Set (Rd d) := {x | a < ‖x - z‖ ∧ ‖x - z‖ < b}

/-- closed annulus `Ā_{a,b}(z)` -/
def annCl (z : Rd d) (a b : ℝ) : Set (Rd d) := {x | a ≤ ‖x - z‖ ∧ ‖x - z‖ ≤ b}

theorem ann_eq_ball_diff (z : Rd d) (a b : ℝ) :
    ann z a b = Metric.ball z b \ Metric.closedBall z a := by
  ext x
  simp only [ann, mem_ofPred_eq, mem_sdiff, Metric.mem_ball, Metric.mem_closedBall, dist_eq_norm, not_le]
  exact and_comm

theorem isOpen_ann (z : Rd d) (a b : ℝ) : IsOpen (ann z a b) := by
  rw [ann_eq_ball_diff]
  exact Metric.isOpen_ball.sdiff Metric.isClosed_closedBall

theorem isClosed_annCl (z : Rd d) (a b : ℝ) : IsClosed (annCl z a b) :=
  (isClosed_le continuous_const (continuous_id.sub continuous_const).norm).inter
    (isClosed_le (continuous_id.sub continuous_const).norm continuous_const)

theorem ann_subset_annCl (z : Rd d) (a b : ℝ) : ann z a b ⊆ annCl z a b :=
  fun _ hx => ⟨hx.1.le, hx.2.le⟩

/-- the normalizer `𝔰_r(z) = r^{ξQ} e^{ξ h_r(z)}` of [S] -/
def sNorm (ξ Q : ℝ) (h : DistRd d) (r : ℝ) (z : Rd d) : ℝ :=
  r ^ (ξ * Q) * Real.exp (ξ * sphereAvg h r z)

/-- `D(A, B; V) = inf_{u ∈ A, v ∈ B} D(u, v; V)` -/
def setDistIn (D : ContMetric d) (V A B : Set (Rd d)) : ℝ≥0∞ :=
  ⨅ (u ∈ A) (v ∈ B), D.internal V u v

section Sigma

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `σ(h|_V)` modulo additive constants: mean-zero pairings supported in `V`
(port of LQGMetric `Blueprint.fieldSigma0On`) -/
def fieldSigma0 (h : Ω → DistRd d) (V : Set (Rd d)) : MeasurableSpace Ω :=
  MeasurableSpace.comap
    (fun ω (ψ : {φ : TestRd0 d // tsupport (φ.1 : Rd d → ℝ) ⊆ V}) => h ω ψ.1.1)
    MeasurableSpace.pi

/-- `σ(h|_V)`: all pairings supported in `V` -/
def fieldSigmaOn (h : Ω → DistRd d) (V : Set (Rd d)) : MeasurableSpace Ω :=
  MeasurableSpace.comap
    (fun ω (ψ : {φ : TestRd d // tsupport (φ : Rd d → ℝ) ⊆ V}) => h ω ψ.1)
    MeasurableSpace.pi

/-- `E` is a.s. equal to an event of `m` (LQGMetric `Blueprint.AEEventIn`, generic) -/
def AEEventIn (P : Measure Ω) (m : MeasurableSpace Ω) (E : Set Ω) : Prop :=
  ∃ F : Set Ω, MeasurableSet[m] F ∧ E =ᵐ[P] F

end Sigma

open Classical in
/-- **[S] Lemma A.1 / (E4)** in MA3's interface form, with a centre `z`: for `0 < a < 1 < b`, `q ∈ (0,1)`,
`A > 0`, `θ ∈ (0,1)` there is `p < 1` such that events determined modulo constants by the field on
`A_{a r_i, b r_i}(z)`, `r_{i+1} ≤ q r_i`, each of probability `≥ p`, occur fewer than `θ n` times among the first
`n` with probability `≤ e^{-An}`. -/
def ShellInputA1 (d : ℕ) : Prop :=
  ∀ a b q : ℝ, 0 < a → a < 1 → 1 < b → 0 < q → q < 1 →
  ∀ A θ : ℝ, 0 < A → 0 < θ → θ < 1 → ∃ p : ℝ, p < 1 ∧
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d), IsWholeSpaceLGF h P →
  ∀ (z : Rd d) (r : ℕ → ℝ), (∀ i, 0 < r i) → (∀ i, r (i + 1) ≤ q * r i) →
  ∀ E : ℕ → Set Ω, (∀ i, AEEventIn P (fieldSigma0 h (ann z (a * r i) (b * r i))) (E i)) →
    (∀ i, ENNReal.ofReal p ≤ P (E i)) →
    ∀ n : ℕ, P {ω | (((Finset.range n).filter (fun i => ω ∈ E i)).card : ℝ) < θ * n} ≤
      ENNReal.ofReal (Real.exp (-A * n))

end HigherDimLQGMetric
