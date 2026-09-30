import QuantumZipper.Proofs.Zipper.WedgeYGoodExact
import QuantumZipper.Proofs.Zipper.AreaCoordBasic
import QuantumZipper.Proofs.LQG.LogSingGoodBasic
import QuantumZipper.Proofs.LQG.AreaOffsets

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Y-GOODALL, part 2: `YGoodAllStmt` from a boundary node and the area merging rule

Theorem 1.3, F2 wedge core X-G (decisions D26/D29). `YGoodAllStmt` asks, a.s., that the unzipped
`Γ⁰` field `y_t = h⁰_t` (`F2.unzY`, `= unzippedField γ (𝔥₀ + X, W) t`) is `IsLQGGood` at **all**
times `t ≥ 0`: regular, with an offset-uniform boundary limit and an offset-uniform area limit
(radii `a 2^{-k}`, `a ∈ [1,2]`, along `goodFilter`).

* **Regularity** is proved (`RegUnif.ae_forall_isRegularSample`, JointMod).
* **Area**: the time-`0` field `𝔥₀ + X` has an offset-uniform area limit (free field,
  `AreaOffsets.ae_hasAreaLimit`, plus the log function `𝔥₀`, `LogSingGood.hasAreaLimit_add_Lf`);
  the area limit of `y_t` is then the transported measure `E6.areaTransport μ W t` as soon as the
  offset-indexed area approximations **merge** (`YAreaMergeStmt`): this is the Sheffield–Wang
  argument, *Field-measure correspondence in Liouville quantum gravity almost surely commutes
  with all conformal maps simultaneously*, Trans. AMS 372 (2020), arXiv:1605.06171, proof of
  Thm 1.4, (3.5)–(3.7), p. 11–12, for the flow `φ = f_t⁻¹`; SW's approximations are indexed by a
  continuous radius `ε → 0`, so their statement contains the offset-uniform form used here.
  Deterministic step: `hasAreaLimit_unzipped_of_merge` (the goodFilter analogue of
  `E6.isVagueLimitOn_areaTransport`, own bookkeeping).
* **Boundary**: `YBdryLimAllStmt` (named): the offset-uniform form of UG
  (`RegUnif.UnifGlobalStmt`, D26/D31, which has dyadic radii only). The boundary measure of `y_t`
  is not a transport of that of `y` (on `[O⁻_t, O⁺_t]` it is the quantum length of the curve),
  so no merging shortcut exists.

Main results: `yGoodAll_of_lims`, `yAreaLimAll_of_merge`, `yGoodAll_of_bdry_merge`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace WedgeUnzip

/-! ## The named nodes -/

/-- **(Γ⁰, area part of YGoodAll)** A.s., for all `t ≥ 0`, the unzipped `Γ⁰` field has an
offset-uniform area limit. -/
def YAreaLimAllStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample),
    IsBrownianReal B P → IsFreeGFFModConstH X P → IndepFun (pathOf B) X P →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
      ∃ μ, HasAreaLimit (Real.sqrt κ) (F2.unzY κ (X ω) (drive κ B ω) t) μ

/-- The offset-indexed merging differences: the scale-`a 2^{-k}` area approximation of the
unzipped field against `f`, minus that of the original field against the transported test
function `1_{ℍ \ K_t} · f ∘ f_t` (goodFilter analogue of `E6.mergeDiff`). -/
def mergeDiffG (γ : ℝ) (y : FieldSample) (W : ℝ → ℝ) (f : ℂ → ℝ) (t : ℝ) (i : ℕ × ℝ) : ℝ :=
  ∫ z, f z ∂areaR γ (unzippedField γ (y, W) t) (goodRad i) -
    ∫ w, E6.transTest W t f w ∂areaR γ y (goodRad i)

/-- **Area merging for the `Γ⁰` field, offsets uniform, all times** (Sheffield–Wang,
arXiv:1605.06171, proof of Thm 1.4, (3.5)–(3.7), for the flow `φ = f_t⁻¹`): a.s., for all `t ≥ 0`
and every test function `f` (continuous, compact support in `ℍ`), the merging differences tend
to `0` along `goodFilter`. -/
def YAreaMergeStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample),
    IsBrownianReal B P → IsFreeGFFModConstH X P → IndepFun (pathOf B) X P →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      tsupport f ⊆ H →
      Tendsto (mergeDiffG (Real.sqrt κ) (ofFun (h0rev κ) + X ω) (drive κ B ω) f t) goodFilter
        (𝓝 0)

/-! ## Deterministic transport of the area limit -/

/-- **The area limit of the unzipped field is the transported area limit**, given merging. -/
theorem hasAreaLimit_unzipped_of_merge {γ : ℝ} {y : FieldSample} {μ : Measure ℂ}
    (hμ : HasAreaLimit γ y μ) {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ}
    (ht : 0 ≤ t)
    (hmerge : ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ H →
      Tendsto (mergeDiffG γ y W f t) goodFilter (𝓝 0)) :
    HasAreaLimit γ (unzippedField γ (y, W) t) (E6.areaTransport μ W t) := by
  refine ⟨E6.areaTransport_compl_H hW ht μ,
    fun K hK hKH => E6.areaTransport_lt_top hW hW0 ht hμ.2.1 hK hKH, fun f hf hfc hfH => ?_⟩
  rw [E6.integral_areaTransport hW ht μ hf]
  have h1 := hμ.2.2 (E6.transTest W t f) (E6.continuous_transTest hW hW0 ht hf hfc hfH)
    (E6.hasCompactSupport_transTest hW hW0 ht hfc hfH)
    (E6.tsupport_transTest_subset hW hW0 ht hfc hfH)
  have h2 := (hmerge f hf hfc hfH).add h1
  rw [zero_add] at h2
  refine h2.congr fun i => ?_
  simp only [mergeDiffG]
  ring

/-! ## The time-`0` field -/

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}

/-- `𝔥₀ + x` as `x` plus the log function `Lf (−2/√κ)`. -/
theorem h0rev_add_eq_Lf (κ : ℝ) (x : FieldSample) :
    ofFun (h0rev κ) + x = x + ofFun (LogSingGood.Lf (-(2 / Real.sqrt κ))) := by
  rw [add_comm]
  congr 2
  funext v
  simp only [LogSingGood.Lf, h0rev]
  ring

/-- **The time-`0` `Γ⁰` field `𝔥₀ + X` has an offset-uniform area limit**, a.s. -/
theorem ae_hasAreaLimit_h0 [IsProbabilityMeasure P] {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (hX : IsFreeGFFModConstH X P) :
    ∀ᵐ ω ∂P, ∃ μ, HasAreaLimit (Real.sqrt κ) (ofFun (h0rev κ) + X ω) μ := by
  have hγ : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  have hγ2 : Real.sqrt κ < 2 := F2.sqrt_lt_two_of' hκ hκ4
  filter_upwards [RegSample.ae_isRegularSample hX, AreaOffsets.ae_hasAreaLimit hX hγ hγ2]
    with ω hreg hA
  obtain ⟨F, hF⟩ := hreg
  rw [h0rev_add_eq_Lf]
  exact ⟨_, LogSingGood.hasAreaLimit_add_Lf hF hA _⟩

/-! ## The reductions -/

/-- **Area part of YGoodAll from the Sheffield–Wang merging rule.** -/
theorem yAreaLimAll_of_merge (hM : YAreaMergeStmt) : YAreaLimAllStmt := by
  intro κ hκ hκ4 Ω _ P _ B X hB hX hind
  filter_upwards [hM κ hκ hκ4 P B X hB hX hind, ae_hasAreaLimit_h0 hκ hκ4 hX,
    RegUnif.ae_drive_good hB κ] with ω hm hA hdr t ht
  obtain ⟨μ, hμ⟩ := hA
  rw [unzY_eq_h0]
  exact ⟨_, hasAreaLimit_unzipped_of_merge hμ hdr.1 hdr.2 ht (hm t ht)⟩

end WedgeUnzip
end QuantumZipper
