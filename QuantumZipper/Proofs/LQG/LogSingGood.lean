import QuantumZipper.Proofs.LQG.LogSingGoodBasic
import QuantumZipper.Proofs.LQG.AreaOffsets
import QuantumZipper.Proofs.LQG.WedgeGood
import QuantumZipper.Proofs.LQG.OffsetP3b

/-!
# `LogSingGoodAS`: the free field plus a boundary log singularity at `0` is a.s. good

Blueprint `M4_BLUEPRINT.md`, node M4-P4 ("log singularities of strength `α < Q`"), upgraded to
the offsets `a 2^{-k}`, `a ∈ [1,2]`, of `goodFilter`.

Main result `logSingGoodAS_of_offsetP3b`: for `0 < γ < 2` and `α < Q`, `LogSingGoodAS γ α`,
assuming `OffsetP3b γ`: the M4-P3(b) fractional-moment bound with the supremum over **all**
radii `0 < r ≤ 2^{-n}` (not only the dyadic ones) inside the expectation.

Sources. This follows the M4-P4 sketch of the blueprint: dyadic annuli around the singularity
plus fractional moments `p < 1` of the masses, the standard argument for Gaussian multiplicative
chaos with an `α`-log singularity, `α < Q` (see e.g. Berestycki–Powell, *Gaussian free field and
Liouville quantum gravity*, arXiv:2404.16642; exact theorem numbers not checked). No published
proof with the supremum over the continuum of offsets was found; that adaptation is our own.

Proof:
a.s. `Z = zField X 2` is good (`AreaOffsets.ae_isLQGGood`); `X + L` is `Z + L` plus a constant;
`Z + L` is regular, its area limit is `‖z‖^{−αγ} μ_Z` (deterministic, `LogSingGoodBasic`), and
its boundary limit is `|t|^{−αγ/2} ν_Z` on `ℝ \ {0}` once the approximations are uniformly
small near `0`; that smallness (`tight_offsets`) follows from an a.s. summable tail of
`2^{nαγ/2} sup_{r ≤ 2^{-n}} ν_r(Z)([−2^{−n}, 2^{−n}])`, which `OffsetP3b` gives by Borel–Cantelli
for fractional moments `p = min(1, (Q − α)/γ)` (exactly as `LogSing.ae_summable_tail`).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace LogSingGood

open GoodSample LogSing CircleFubini

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-- The M4-P3(b) fractional-moment bound, with the supremum over all radii `0 < r ≤ 2^{-n}`
(`annTo`) of the normalized field `Z = zField X R`, at the boundary point `0`. -/
def OffsetP3bBound (P : Measure Ω) (X : Ω → FieldSample) (γ R : ℝ) : Prop :=
  ∀ p : ℝ, 0 < p → p ≤ 1 → ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    ∫⁻ ω, annTo γ (BdryExist.zField X R ω) n ^ p ∂P ≤
      C * ENNReal.ofReal ((2 : ℝ) ^ ((n : ℝ) * (γ ^ 2 * p ^ 2 / 4 - p * (1 + γ ^ 2 / 4))))

/-- `OffsetP3bBound` for every free field (normalization radius `2`). -/
def OffsetP3b (γ : ℝ) : Prop :=
  ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (X : Ω → FieldSample),
    IsProbabilityMeasure P → IsFreeGFFModConstH X P → OffsetP3bBound P X γ 2

theorem measurable_bdryR_zField (hX : IsFreeGFFModConstH X P) (γ R r : ℝ) {S : Set ℝ}
    (hS : MeasurableSet S) :
    Measurable fun ω => bdryR γ (BdryExist.zField X R ω) r S := by
  simp only [bdryR, withDensity_apply _ hS]
  have hz : Measurable (fun p : Ω × ℝ => AllOffsets.zV X R r p.2 p.1) :=
    Measurable.comp (g := fun p : ℝ × Ω => AllOffsets.zV X R r p.1 p.2) (f := Prod.swap)
      (AllOffsets.measurable_zV hX R r) measurable_swap
  have hj : Measurable (fun p : Ω × ℝ =>
      ENNReal.ofReal (bdryDens γ (BdryExist.zField X R p.1) r p.2)) :=
    ENNReal.measurable_ofReal.comp
      (measurable_const.mul (Real.measurable_exp.comp (measurable_const.mul hz)))
  exact hj.lintegral_prod_right'

theorem measurable_annTo (hX : IsFreeGFFModConstH X P) (γ R : ℝ) (n : ℕ) :
    Measurable fun ω => annTo γ (BdryExist.zField X R ω) n :=
  Measurable.iSup fun q => Measurable.iSup fun _ =>
    measurable_bdryR_zField hX γ R q measurableSet_Icc

/-- A.s. the weighted offset-uniform interval masses have a summable tail (the argument of
`LogSing.ae_summable_tail`, with `annTo` in place of `annT`). -/
theorem ae_summable_tail_offsets [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    {γ : ℝ} (hγ : 0 < γ) (R : ℝ) {α : ℝ} (hα : α < Qc γ) (hP3 : OffsetP3bBound P X γ R) :
    ∀ᵐ ω ∂P, ∃ N : ℕ, ∑' n, annW γ α (n + N) *
      annTo γ (BdryExist.zField X R ω) (n + N) ≠ ⊤ := by
  set αp := max α 0 with hαp
  have hQ : γ * Qc γ = 2 + γ ^ 2 / 2 := by unfold Qc; field_simp
  have hQpos : 0 < Qc γ := by unfold Qc; positivity
  have hαQ : αp < Qc γ := max_lt hα hQpos
  set p := min 1 ((Qc γ - αp) / γ) with hpdef
  have hp0 : 0 < p := lt_min one_pos (div_pos (by linarith) hγ)
  have hp1 : p ≤ 1 := min_le_left _ _
  have hpγ : γ * p ≤ Qc γ - αp := by
    have := min_le_right 1 ((Qc γ - αp) / γ)
    rw [le_div_iff₀ hγ] at this; linarith
  set e := γ ^ 2 * p ^ 2 / 4 - p * (1 + γ ^ 2 / 4) with he
  have hneg : expB γ α * p + e < 0 := by
    have hin : αp * γ / 2 + γ ^ 2 * p / 4 - 1 - γ ^ 2 / 4 < 0 := by
      have h1 : γ * (γ * p) ≤ γ * (Qc γ - αp) := mul_le_mul_of_nonneg_left hpγ hγ.le
      have h2 : γ * (αp - Qc γ) < 0 := mul_neg_of_pos_of_neg hγ (by linarith)
      nlinarith
    have : expB γ α * p + e = p * (αp * γ / 2 + γ ^ 2 * p / 4 - 1 - γ ^ 2 / 4) := by
      rw [he]; unfold expB; ring
    rw [this]
    exact mul_neg_of_pos_of_neg hp0 hin
  obtain ⟨C, hC, n₀, hbd⟩ := hP3 p hp0 hp1
  set T : ℕ → Ω → ℝ≥0∞ := fun n ω => annTo γ (BdryExist.zField X R ω) n with hT
  set u : ℕ → ℝ := fun n => (radius (n + 1) ^ (-expB γ α)) ^ p * (2 : ℝ) ^ ((n : ℝ) * e)
    with hu
  have hu0 : ∀ n, 0 ≤ u n := fun n =>
    mul_nonneg (Real.rpow_nonneg (Real.rpow_nonneg (radius_pos _).le _) _) (by positivity)
  have husum : Summable u := summable_annuli hp0.le hneg
  have hmeas : ∀ n, Measurable fun ω => (annW γ α (n + n₀) * T (n + n₀) ω) ^ p := fun n =>
    (measurable_const.mul (measurable_annTo hX γ R _)).pow_const p
  have hterm : ∀ n, ∫⁻ ω, (annW γ α (n + n₀) * T (n + n₀) ω) ^ p ∂P ≤
      C * ENNReal.ofReal (u (n + n₀)) := by
    intro n'
    set n := n' + n₀ with hn
    have hw : annW γ α n ^ p = ENNReal.ofReal ((radius (n + 1) ^ (-expB γ α)) ^ p) :=
      ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg (radius_pos _).le _) hp0.le
    simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, hw]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    calc ENNReal.ofReal ((radius (n + 1) ^ (-expB γ α)) ^ p) * ∫⁻ ω, T n ω ^ p ∂P
        ≤ ENNReal.ofReal ((radius (n + 1) ^ (-expB γ α)) ^ p) *
            (C * ENNReal.ofReal ((2 : ℝ) ^ ((n : ℝ) * e))) := by
          gcongr; exact hbd n (Nat.le_add_left _ _)
      _ = C * ENNReal.ofReal (u n) := by
          rw [hu, ENNReal.ofReal_mul (Real.rpow_nonneg (Real.rpow_nonneg (radius_pos _).le _) _)]
          ring
  have hsumE : ∑' n, ∫⁻ ω, (annW γ α (n + n₀) * T (n + n₀) ω) ^ p ∂P ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hterm)
    rw [ENNReal.tsum_mul_left, ← ENNReal.ofReal_tsum_of_nonneg (fun n => hu0 _)
      ((summable_nat_add_iff n₀).2 husum)]
    exact ENNReal.mul_ne_top hC ENNReal.ofReal_ne_top
  have hlt : ∀ᵐ ω ∂P, ∑' n, (annW γ α (n + n₀) * T (n + n₀) ω) ^ p < ⊤ := by
    refine ae_lt_top' (AEMeasurable.ennreal_tsum fun n => (hmeas n).aemeasurable) ?_
    rw [lintegral_tsum fun n => (hmeas n).aemeasurable]
    exact hsumE
  filter_upwards [hlt] with ω hω
  set b : ℕ → ℝ≥0∞ := fun n => (annW γ α (n + n₀) * T (n + n₀) ω) ^ p with hb
  have hb0 : Tendsto b atTop (𝓝 0) := ENNReal.tendsto_atTop_zero_of_tsum_ne_top hω.ne
  obtain ⟨N, hN⟩ := (hb0.eventually (eventually_le_nhds zero_lt_one)).exists_forall_of_atTop
  refine ⟨N + n₀, ne_top_of_le_ne_top hω.ne ?_⟩
  calc ∑' n, annW γ α (n + (N + n₀)) * T (n + (N + n₀)) ω ≤ ∑' n, b (n + N) := by
        refine ENNReal.tsum_le_tsum fun n => ?_
        rw [← Nat.add_assoc]
        have h1 : b (n + N) ≤ 1 := hN (n + N) (Nat.le_add_left _ _)
        have ha1 : annW γ α (n + N + n₀) * T (n + N + n₀) ω ≤ 1 := by
          by_contra h
          push_neg at h
          exact absurd h1 (not_le.2 (ENNReal.one_lt_rpow h hp0))
        calc annW γ α (n + N + n₀) * T (n + N + n₀) ω =
              (annW γ α (n + N + n₀) * T (n + N + n₀) ω) ^ (1 : ℝ) :=
              (ENNReal.rpow_one _).symm
          _ ≤ b (n + N) := ENNReal.rpow_le_rpow_of_exponent_ge ha1 hp1
    _ ≤ ∑' n, b n := ENNReal.tsum_comp_le_tsum_of_injective (add_left_injective N) b

/-- Pathwise: if `z` is good and the offset-uniform annulus tail is summable, then `z + L` is
good. -/
theorem isLQGGood_add_Lf {γ α : ℝ} (hγ : 0 < γ) {z : FieldSample} (hz : IsLQGGood γ z)
    {N : ℕ} (hN : ∑' n, annW γ α (n + N) * annTo γ z (n + N) ≠ ⊤) :
    IsLQGGood γ (z + ofFun (Lf α)) := by
  obtain ⟨⟨F, hF⟩, ⟨ν, hν⟩, ⟨μ, hμ⟩⟩ := hz
  exact ⟨⟨_, regular_add_Lf hF α⟩, ⟨_, hasBdryLimit_add_Lf hF hν (tight_offsets hγ hF α hN)⟩,
    ⟨_, hasAreaLimit_add_Lf hF hμ α⟩⟩

/-- **`LogSingGoodAS γ α`** for `0 < γ < 2`, `α < Q`, given the offset-uniform fractional-moment
bound `OffsetP3b γ`. -/
theorem logSingGoodAS_of_offsetP3b {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < Qc γ)
    (h : OffsetP3b γ) : LogSingGoodAS γ α := by
  intro Ω _ P X hP hX
  have hP3 := h Ω _ P X hP hX
  filter_upwards [AreaOffsets.ae_isLQGGood hX hγ hγ2,
    ae_summable_tail_offsets hX hγ 2 hα hP3] with ω hg hsum
  obtain ⟨N, hN⟩ := hsum
  have hzL := isLQGGood_add_Lf hγ (hg.addConst (-X ω (foldedCircle 0 2))) hN
  have e : X ω + ofFun (fun z => α * -Real.log ‖z‖) =
      addConst (BdryExist.zField X 2 ω + ofFun (Lf α)) (X ω (foldedCircle 0 2)) := by
    rw [show (fun z : ℂ => α * -Real.log ‖z‖) = Lf α from rfl]
    funext m
    simp only [BdryExist.zField, addConst, Pi.add_apply]
    ring
  rw [e]
  exact hzL.addConst _

/-- **`OffsetP3b γ` holds** for `0 < γ < 2` (`OffsetP3b.lintegral_annTo_rpow_le`). -/
theorem offsetP3b_holds {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) : OffsetP3b γ := by
  intro Ω _ P X hP hX p hp0 hp1
  haveI := hP
  obtain ⟨C, hC0, hC⟩ := OffsetP3b.lintegral_annTo_rpow_le hX hγ hγ2 hp0 hp1
  refine ⟨ENNReal.ofReal C, ENNReal.ofReal_ne_top, 1, fun n hn => ?_⟩
  refine (hC n hn).trans (le_of_eq ?_)
  rw [ENNReal.ofReal_mul hC0, show (-(n : ℝ) * p * (1 + γ ^ 2 / 4) + n * (γ ^ 2 * p ^ 2 / 4))
    = (n : ℝ) * (γ ^ 2 * p ^ 2 / 4 - p * (1 + γ ^ 2 / 4)) by ring]

/-- **`LogSingGoodAS γ α`**, unconditionally, for `0 < γ < 2` and `α < Q`. -/
theorem logSingGoodAS_holds {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < Qc γ) :
    LogSingGoodAS γ α :=
  logSingGoodAS_of_offsetP3b hγ hγ2 hα (offsetP3b_holds hγ hγ2)

/-- **`WedgeRefGoodAS γ α`**, unconditionally, for `0 < γ < 2` and `α < Q`. -/
theorem wedgeRefGoodAS_holds {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < Qc γ) :
    NonVacuity.WedgeRefGoodAS γ α :=
  WedgeGood.wedgeRefGoodAS_of_logSing (logSingGoodAS_holds hγ hγ2 hα)

end LogSingGood
end QuantumZipper
