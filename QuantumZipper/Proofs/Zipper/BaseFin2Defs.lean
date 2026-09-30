import QuantumZipper.Proofs.Zipper.BaseFinReduce
import QuantumZipper.Proofs.Zipper.LocLenDefs
import QuantumZipper.Proofs.Zipper.TruncFreeTipX
import QuantumZipper.Proofs.Zipper.TipXSLE

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# X1 (decision D75): the capacity-piece route for `BaseWeightStmt` — statements

Task X1-BASE (`handoff/X1-BASE.md`). `BaseWeightStmt` (`BaseFinReduce.lean`) asks, at a fixed
capacity time `q > 0`, for the integrability of `|F_q|^{−κ/2}` against the `Γ⁰` boundary measure
`ν_q` of the unzipped field `y_q` next to the base points `O^±_q`.

**Sources.** No published proof of X1 exists (searched: Sheffield arXiv:1012.4797 §5.4 pp. 69–72;
Berestycki–Powell arXiv:2404.16642 pp. 280–285, where "`L(1) < ∞`" and "no atoms at `0±`" are
asserted without proof; Duplantier–Miller–Sheffield arXiv:1409.7055; Powell–Sepúlveda
arXiv:2403.03902 Thm 1.2, p. 3, which identifies the quantum length of `η([r,s])` only for
`0 < r`). Sheffield's own route (p. 70: each side is a `γ`-quantum wedge "from Proposition 1.6",
and a `γ`-wedge has finite boundary length at its origin since `γ < Q`) needs the wedge
decomposition G1, which is open in this repository and depends on Theorem 1.3 nodes. The route
here is therefore our own (FIDELITY-TIP-MAX §3 route (b), in capacity pieces instead of spatial
shells): with `λ_k = min_{r ∈ [4^{-k-1}, 4^{-k}]} |η(r)|` and `L^±(t)` the `Γ⁰` open-arc lengths
of `η[0,t]`,
1. (`BaseCovStmt`, pathwise) the weighted integral near `O^±_q` is at most
   `Σ_{k ≥ N} λ_k^{−κ/2} L^±(4^{-k})` (the chart-`q` measure of the left image of `η[0,b]` is
   `L^-(b)` by the proved one-chart identity `LocLen.b5UniformArcStmt_holds`);
2. (`BaseScaleStmt`) Brownian/`Γ⁰` scaling by `a = 2^{-k}` turns the `k`-th term into
   `a^{2−κ/4} e^{(γ/2)h_a(0)}` times the unit term of the scaled pair;
3. (`BaseUnitMomStmt`) the unit term `λ_0^{−κ/2} L^±(1)` has a small moment;
4. (`baseSum_of_scale_unit`, file `BaseFin2Sum.lean`) summation:
   `E[term_k^p] ≤ C ρ^k`, `ρ < 1`, hence `Σ_k term_k < ∞` a.s. (`BaseSumStmt`).

Proved here: `baseWeight_of_cov_sum : BaseCovStmt → BaseSumStmt → BaseWeightStmt`
(own elementary bookkeeping).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace BaseFin2

open BaseFin WedgeUnzip

/-- `λ_k = min_{r ∈ [4^{-k-1}, 4^{-k}]} |η(r)|` (as an extended nonnegative real). -/
def winLam (κ : ℝ) {Ω : Type} (B : ℝ≥0 → Ω → ℝ) (ω : Ω) (k : ℕ) : ℝ≥0∞ :=
  ⨅ r ∈ Icc (radius (k + 1) ^ 2) (radius k ^ 2), ENNReal.ofReal ‖sleTrace κ B ω r‖

/-- The `Γ⁰` open-arc lengths `(L⁻(t), L⁺(t))` of the two sides of `η[0,t]`. -/
def lenArc (κ : ℝ) {Ω : Type} (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) (ω : Ω) (t : ℝ) :
    ℝ≥0∞ × ℝ≥0∞ :=
  LocLen.unzipLengthsArc (Real.sqrt κ) (B2.cfg κ B X ω) t

/-- The `k`-th left term `λ_k^{−κ/2} L⁻(4^{-k})`. -/
def termL (κ : ℝ) {Ω : Type} (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) (ω : Ω) (k : ℕ) :
    ℝ≥0∞ :=
  winLam κ B ω k ^ (-(κ / 2)) * (lenArc κ B X ω (radius k ^ 2)).1

/-- The `k`-th right term `λ_k^{−κ/2} L⁺(4^{-k})`. -/
def termR (κ : ℝ) {Ω : Type} (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) (ω : Ω) (k : ℕ) :
    ℝ≥0∞ :=
  winLam κ B ω k ^ (-(κ / 2)) * (lenArc κ B X ω (radius k ^ 2)).2

/-- **(X1-COV, pathwise)** At a fixed `q > 0`, a.s., for every `N` with `4^{-N} ≤ q` there is
`δ > 0` such that the weighted integrals of `BaseWeightStmt` on `(O⁻_q, O⁻_q + δ)` and
`(O⁺_q − δ, O⁺_q)` are bounded by the tails `Σ_{k ≥ N}` of the left/right terms. -/
def BaseCovStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample),
    IsBrownianReal B P → IsFreeGFFModConstH X P → IndepFun (pathOf B) X P →
    ∀ q : ℝ, 0 < q → ∀ᵐ ω ∂P, ∀ N : ℕ, radius N ^ 2 ≤ q → ∃ δ > 0,
      ∫⁻ s in Ioo (sideImages (drive κ B ω) q).1 ((sideImages (drive κ B ω) q).1 + δ),
          ENNReal.ofReal (‖F2.invBdry (drive κ B ω) q s‖ ^ (-(κ / 2)))
          ∂qBoundaryMeasure (Real.sqrt κ) (F2.unzY κ (X ω) (drive κ B ω) q) ≤
        ∑' k, termL κ B X ω (k + N) ∧
      ∫⁻ s in Ioo ((sideImages (drive κ B ω) q).2 - δ) (sideImages (drive κ B ω) q).2,
          ENNReal.ofReal (‖F2.invBdry (drive κ B ω) q s‖ ^ (-(κ / 2)))
          ∂qBoundaryMeasure (Real.sqrt κ) (F2.unzY κ (X ω) (drive κ B ω) q) ≤
        ∑' k, termR κ B X ω (k + N)

/-- **(X1-SUM)** a.s. the left and right term series converge. -/
def BaseSumStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample),
    IsBrownianReal B P → IsFreeGFFModConstH X P → IndepFun (pathOf B) X P →
    ∀ᵐ ω ∂P, ∑' k, termL κ B X ω k < ⊤ ∧ ∑' k, termR κ B X ω k < ⊤

/-- **(X1-SC, scaling)** For a `Γ⁰` pair and `a = 2^{-k}`, a.s. the `k`-th terms are
at most `a^{2−κ/4} e^{(γ/2) h_a(0)}` (`scFac`, see `WedgeUnzip.scFac_eq`) times the unit terms
of the scaled pair `(B^{(k)}, X^{(k)}) = (scB k B, scNrmR κ a X)` (a normalized pair,
`WedgeUnzip.scPairR_props`; the gauge of `X` sits in `scFac`). -/
def BaseScaleStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample),
    IsBrownianReal B P → IsFreeGFFModConstH X P → IndepFun (pathOf B) X P →
    ∀ k : ℕ, ∀ᵐ ω ∂P,
      termL κ B X ω k ≤ scFac κ (radius k) (X ω) *
          termL κ (scB k B) (fun ω => scNrmR κ (radius k) (X ω)) ω 0 ∧
      termR κ B X ω k ≤ scFac κ (radius k) (X ω) *
          termR κ (scB k B) (fun ω => scNrmR κ (radius k) (X ω)) ω 0

/-- **(X1-U, unit moments)** The unit terms have an a.e.-measurable majorant with a small
moment, uniformly over normalized `Γ⁰` pairs. -/
def BaseUnitMomStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∃ q : ℝ, 0 < q ∧ ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample),
    IsBrownianReal B P → IsFreeGFFModConstH X P → IndepFun (pathOf B) X P →
    RegUnif.IsNrmSample X →
    ∃ U : Ω → ℝ≥0∞, AEMeasurable U P ∧ ∫⁻ ω, U ω ^ q ∂P ≤ C ∧
      ∀ᵐ ω ∂P, termL κ B X ω 0 ≤ U ω ∧ termR κ B X ω 0 ≤ U ω

/-- **(X1-UL, unit lengths)** The `Γ⁰` open-arc lengths of `η[0,1]` have an a.e.-measurable
majorant with a small moment, uniformly over normalized `Γ⁰` pairs. -/
def BaseUnitLenMomStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∃ b : ℝ, 0 < b ∧ ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample),
    IsBrownianReal B P → IsFreeGFFModConstH X P → IndepFun (pathOf B) X P →
    RegUnif.IsNrmSample X →
    ∃ L : Ω → ℝ≥0∞, AEMeasurable L P ∧ ∫⁻ ω, L ω ^ b ∂P ≤ C ∧
      ∀ᵐ ω ∂P, (lenArc κ B X ω 1).1 ≤ L ω ∧ (lenArc κ B X ω 1).2 ≤ L ω

/-- `4^{-N} ≤ q` for some `N`. -/
theorem exists_radius_sq_le {q : ℝ} (hq : 0 < q) : ∃ N : ℕ, radius N ^ 2 ≤ q := by
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hq (by norm_num : (4 : ℝ)⁻¹ < 1)
  refine ⟨N, ?_⟩
  have e : radius N ^ 2 = (4 : ℝ)⁻¹ ^ N := by
    unfold radius; rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [e]; exact hN.le

/-- **`BaseWeightStmt` from the covering and the summation.** -/
theorem baseWeight_of_cov_sum (hC : BaseCovStmt) (hS : BaseSumStmt) : BaseWeightStmt := by
  intro κ hκ hκ4 Ω _ P _ B X hB hX hind q hq
  obtain ⟨N, hN⟩ := exists_radius_sq_le hq
  filter_upwards [hC κ hκ hκ4 P B X hB hX hind q hq, hS κ hκ hκ4 P B X hB hX hind] with ω hc hs
  obtain ⟨δ, hδ, hL, hR⟩ := hc N hN
  refine ⟨δ, hδ, hL.trans_lt ?_, hR.trans_lt ?_⟩
  · refine lt_of_le_of_lt ?_ hs.1
    have := tsum_tail_mono_of_le (termL κ B X ω) (Nat.zero_le N)
    simpa using this
  · refine lt_of_le_of_lt ?_ hs.2
    have := tsum_tail_mono_of_le (termR κ B X ω) (Nat.zero_le N)
    simpa using this

end BaseFin2
end QuantumZipper
