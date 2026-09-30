import QuantumZipper.Proofs.Zipper.BaseFin2Defs
import QuantumZipper.Proofs.Zipper.LogShiftW2Trace
import QuantumZipper.Proofs.Zipper.LocLenB5UPlus
import QuantumZipper.Proofs.Zipper.E1NuExist
import QuantumZipper.Proofs.Thm18.G4BSideGeom

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# X1-UL: unit-length moments `BaseUnitLenMomStmt` from three single estimates

Task X1-UL (`handoff/X1-BASE.md`, decision D75). Proves
`baseUnitLenMom_of_parts : BaseULConstStmt → BaseULRadStmt → BaseULNrmStmt → BaseUnitLenMomStmt`.

**Route (own elementary bookkeeping; no published proof of X1 exists, see `BaseFin2Defs.lean`).**
Write `y = h⁰_1` (chart `T = 1`), `c = y(ϖ₀)` with `ϖ₀ = fc(0,1)` (`ulNorm`, `ulConst`), `ỹ = y − c` (`ulShift`), and
`R = max(|O⁻_1|, |O⁺_1|)` (`ulRad`, with `O^±_1 = 0_∓^V(1)`). By the one-chart identity
(`LocLen.b5UniformArcStmt_holds` at `T = s = 1`) both `L^±(1) ≤ ν_y([−n,n])` with `n = ⌈R⌉`, and
`ν_y = e^{γc/2} ν_ỹ` (`LocalRule.qBoundaryMeasure_addConst'`). With `θ = |A| + 1`,
`L^b ≤ Σ_n e^{θ(1−n)} · u · v · w_n` where `u³ = 1 + e^{s c}`, `v³ ≥ e^{3θR}`,
`w_n³ = 1 + ν_ỹ([−n,n])^p` (only the term `n = ⌈R⌉` is needed, where `e^{θ(1−n)} e^{θR} ≥ 1`), and
`u v w ≤ u³ + v³ + w³`. The three open inputs:
* `BaseULConstStmt`: an exponential moment of the normalization constant `c` (open);
* `BaseULRadStmt`: exponential moments of `|O^±_1|` (Brownian driver only; proved in
  `BaseFin2ULRad.lean`);
* `BaseULNrmStmt`: a small moment of `ν_ỹ([−n,n])`, growing at most exponentially in `n`
  (reduced to the `Γ⁰` first moments `BaseULGamma0MomStmt` in `BaseFin2ULNrm.lean`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace BaseFin2

/-- The normalizer `ϖ₀ = fc(0, 1)`: the uniform measure on the unit semicircle (the gauge of
`B1Full.nrm`; `RegUnif.unzipConstExpMomStmt_holds` controls the constant there). -/
def ulNorm : Measure ℂ := foldedCircle 0 1

/-- The field `y − y(ϖ₀)`, normalized to have mean `0` on `ϖ₀`. -/
def ulShift (y : FieldSample) : FieldSample := addConst y (-(y ulNorm))

/-- The normalization constant `c = h⁰_1(ϖ₀)` of the chart-`1` field. -/
def ulConst (κ : ℝ) {Ω : Type} (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) (ω : Ω) : ℝ :=
  B2.h0f κ 1 B X ω ulNorm

/-- `R = max(|O⁻_1|, |O⁺_1|)`, with `O⁻_1 = 0₋^V(1)`, `O⁺_1 = 0₊^V(1)`, `V = vrev W 1`. -/
def ulRad (κ : ℝ) {Ω : Type} (B : ℝ≥0 → Ω → ℝ) (ω : Ω) : ℝ :=
  max |zeroMinus (B2.Vr κ 1 B ω) 1| |zeroPlus (B2.Vr κ 1 B ω) 1|

/-- **(X1-UL-C)** An exponential moment of the raw normalization constant, uniformly over
normalized `Γ⁰` pairs. -/
def BaseULConstStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∃ s : ℝ, 0 < s ∧ ∃ K : ℝ≥0∞, K ≠ ⊤ ∧
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample),
    IsBrownianReal B P → IsFreeGFFModConstH X P → IndepFun (pathOf B) X P →
    RegUnif.IsNrmSample X →
    ∃ M : Ω → ℝ≥0∞, AEMeasurable M P ∧ ∫⁻ ω, M ω ∂P ≤ K ∧
      ∀ᵐ ω ∂P, ENNReal.ofReal (Real.exp (s * ulConst κ B X ω)) ≤ M ω

/-- **(X1-UL-R)** Exponential moments of `|O^±_1|` (Brownian driver only). -/
def BaseULRadStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ s : ℝ, 0 < s → ∃ K : ℝ≥0∞, K ≠ ⊤ ∧
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ), IsBrownianReal B P →
    ∃ M : Ω → ℝ≥0∞, AEMeasurable M P ∧ ∫⁻ ω, M ω ∂P ≤ K ∧
      ∀ᵐ ω ∂P, ENNReal.ofReal (Real.exp (s * ulRad κ B ω)) ≤ M ω

/-- **(X1-UL-N)** A small moment of the normalized chart-`1` boundary measure of `[−n,n]`,
growing at most exponentially in `n`, uniformly over normalized `Γ⁰` pairs. -/
def BaseULNrmStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∃ p : ℝ, 0 < p ∧ ∃ A : ℝ, ∃ K : ℝ≥0∞, K ≠ ⊤ ∧
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample),
    IsBrownianReal B P → IsFreeGFFModConstH X P → IndepFun (pathOf B) X P →
    RegUnif.IsNrmSample X → ∀ n : ℕ,
    ∃ M : Ω → ℝ≥0∞, AEMeasurable M P ∧
      ∫⁻ ω, M ω ^ p ∂P ≤ K * ENNReal.ofReal (Real.exp (A * n)) ∧
      ∀ᵐ ω ∂P, qBoundaryMeasure (Real.sqrt κ) (ulShift (B2.h0f κ 1 B X ω))
        (Icc (-(n : ℝ)) n) ≤ M ω

/-! ## Elementary helpers -/

theorem ul_amgm (x y z : ℝ≥0∞) : x * y * z ≤ x ^ 3 + y ^ 3 + z ^ 3 := by
  obtain ⟨m, hm⟩ : ∃ m, m = max x (max y z) := ⟨_, rfl⟩
  have hx : x ≤ m := hm ▸ le_max_left _ _
  have hy : y ≤ m := hm ▸ (le_max_left _ _).trans (le_max_right _ _)
  have hz : z ≤ m := hm ▸ (le_max_right _ _).trans (le_max_right _ _)
  calc x * y * z ≤ m * m * m := by gcongr
    _ = m ^ 3 := by ring
    _ ≤ x ^ 3 + y ^ 3 + z ^ 3 := by
      rcases max_choice x (max y z) with h | h
      · rw [hm, h]; exact le_add_right (le_add_right le_rfl)
      · rcases max_choice y z with h' | h'
        · rw [hm, h, h']; exact le_add_right (le_add_left le_rfl)
        · rw [hm, h, h']; exact le_add_left le_rfl

theorem ul_le_cbrt {a c : ℝ≥0∞} (h : a ^ (3 : ℝ) ≤ c) : a ≤ c ^ ((3 : ℝ)⁻¹) := by
  calc a = (a ^ (3 : ℝ)) ^ ((3 : ℝ)⁻¹) := by
        rw [← ENNReal.rpow_mul, mul_inv_cancel₀ (by norm_num), ENNReal.rpow_one]
    _ ≤ c ^ ((3 : ℝ)⁻¹) := ENNReal.rpow_le_rpow h (by norm_num)

theorem ul_cbrt_cube (c : ℝ≥0∞) : (c ^ ((3 : ℝ)⁻¹)) ^ 3 = c := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

theorem ul_rpow_three (a : ℝ≥0∞) (b : ℝ) : (a ^ b) ^ (3 : ℝ) = a ^ (b * 3) := by
  rw [← ENNReal.rpow_mul]

theorem ul_ofReal_exp_rpow (x y : ℝ) :
    ENNReal.ofReal (Real.exp x) ^ y = ENNReal.ofReal (Real.exp (x * y)) := by
  rw [Real.exp_mul, ENNReal.ofReal_rpow_of_pos (Real.exp_pos x)]

theorem ul_exp_le {c e s : ℝ} (he : 0 ≤ e) (hes : e ≤ s) :
    ENNReal.ofReal (Real.exp (e * c)) ≤ 1 + ENNReal.ofReal (Real.exp (s * c)) := by
  rcases le_total 0 c with hc | hc
  · exact (ENNReal.ofReal_le_ofReal
      (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hes hc))).trans le_add_self
  · refine (ENNReal.ofReal_le_ofReal
      (Real.exp_le_one_iff.2 (mul_nonpos_of_nonneg_of_nonpos he hc))).trans ?_
    rw [ENNReal.ofReal_one]
    exact le_self_add

theorem ul_rpow_le_one_add {x : ℝ≥0∞} {q p : ℝ} (hq : 0 ≤ q) (hqp : q ≤ p) :
    x ^ q ≤ 1 + x ^ p := by
  rcases le_total x 1 with hx | hx
  · exact (ENNReal.rpow_le_one hx hq).trans le_self_add
  · exact (ENNReal.rpow_le_rpow_of_exponent_le hx hqp).trans le_add_self

theorem ul_geom {θ A : ℝ} (hθ : θ = |A| + 1) (n : ℕ) (a K : ℝ≥0∞) :
    ENNReal.ofReal (Real.exp (θ * (1 - n))) * (a + K * ENNReal.ofReal (Real.exp (A * n))) ≤
      ENNReal.ofReal (Real.exp θ) * (a + K) * ENNReal.ofReal (Real.exp (-1)) ^ n := by
  have hn : (0 : ℝ) ≤ n := n.cast_nonneg
  have e : ENNReal.ofReal (Real.exp θ) * ENNReal.ofReal (Real.exp (-1)) ^ n =
      ENNReal.ofReal (Real.exp (θ - n)) := by
    rw [← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul,
      ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2; ring
  have h1 : ENNReal.ofReal (Real.exp (θ * (1 - n))) ≤ ENNReal.ofReal (Real.exp (θ - n)) :=
    ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (by nlinarith [abs_nonneg A]))
  have h2 : ENNReal.ofReal (Real.exp (θ * (1 - n))) * ENNReal.ofReal (Real.exp (A * n)) ≤
      ENNReal.ofReal (Real.exp (θ - n)) := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (by nlinarith [le_abs_self A]))
  calc ENNReal.ofReal (Real.exp (θ * (1 - n))) * (a + K * ENNReal.ofReal (Real.exp (A * n)))
      = ENNReal.ofReal (Real.exp (θ * (1 - n))) * a +
          K * (ENNReal.ofReal (Real.exp (θ * (1 - n))) * ENNReal.ofReal (Real.exp (A * n))) := by
        ring
    _ ≤ ENNReal.ofReal (Real.exp (θ - n)) * a + K * ENNReal.ofReal (Real.exp (θ - n)) := by
        gcongr
    _ = ENNReal.ofReal (Real.exp θ) * (a + K) * ENNReal.ofReal (Real.exp (-1)) ^ n := by
        rw [mul_right_comm, e]; ring

/-- `ν_y = e^{γ c/2} ν_{y − c}` with `c = y(ϖ₀)`. -/
theorem ul_scale {y : FieldSample} (hy : LocalRule.RawConverges y Hbar) (γ : ℝ) (A : Set ℝ) :
    qBoundaryMeasure γ y A = ENNReal.ofReal (Real.exp (γ * y ulNorm / 2)) *
      qBoundaryMeasure γ (ulShift y) A := by
  rw [ulShift, LocalRule.qBoundaryMeasure_addConst' hy, Measure.smul_apply, smul_eq_mul,
    ← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  have : γ * y ulNorm / 2 + γ * -y ulNorm / 2 = 0 := by ring
  rw [this, Real.exp_zero, ENNReal.ofReal_one, one_mul]

theorem ul_geom_ne_top : ∑' n : ℕ, ENNReal.ofReal (Real.exp (-1)) ^ n ≠ ⊤ := by
  rw [ENNReal.tsum_geometric]
  refine ENNReal.inv_ne_top.2 (ne_of_gt (tsub_pos_of_lt ?_))
  rw [← ENNReal.ofReal_one]
  exact (ENNReal.ofReal_lt_ofReal_iff one_pos).2 (by simp)

/-! ## The glue -/

/-- **`BaseUnitLenMomStmt` from the three single estimates.** -/
theorem baseUnitLenMom_of_parts (hC : BaseULConstStmt) (hR : BaseULRadStmt)
    (hN : BaseULNrmStmt) : BaseUnitLenMomStmt := by
  intro κ hκ hκ4
  obtain ⟨s₁, hs₁, K₁, hK₁, hC'⟩ := hC κ hκ hκ4
  obtain ⟨p, hp, A, K₂, hK₂, hN'⟩ := hN κ hκ hκ4
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = |A| + 1 := ⟨_, rfl⟩
  have hθ0 : 0 < θ := by rw [hθ]; positivity
  obtain ⟨K₃, hK₃, hR'⟩ := hR κ hκ hκ4 (3 * θ) (by positivity)
  have hγ0 : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = min (2 * s₁ / (3 * Real.sqrt κ)) (p / 3) := ⟨_, rfl⟩
  have hb0 : 0 < b := by rw [hb]; exact lt_min (by positivity) (by positivity)
  have hbs : Real.sqrt κ / 2 * (b * 3) ≤ s₁ := by
    have h1 : b ≤ 2 * s₁ / (3 * Real.sqrt κ) := hb ▸ min_le_left _ _
    rw [le_div_iff₀ (by positivity)] at h1
    nlinarith
  have hbp : b * 3 ≤ p := by
    have h1 : b ≤ p / 3 := hb ▸ min_le_right _ _
    linarith
  refine ⟨b, hb0, ENNReal.ofReal (Real.exp θ) * (2 + K₁ + K₃ + K₂) *
      ∑' n : ℕ, ENNReal.ofReal (Real.exp (-1)) ^ n, ?_, ?_⟩
  · refine ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_) ul_geom_ne_top
    simp [hK₁, hK₂, hK₃]
  intro Ω _ P _ B X hB hX hind hNrm
  obtain ⟨M₁, hM₁m, hM₁i, hM₁⟩ := hC' P B X hB hX hind hNrm
  obtain ⟨M₃, hM₃m, hM₃i, hM₃⟩ := hR' P B hB
  choose M₂ hM₂m hM₂i hM₂ using hN' P B X hB hX hind hNrm
  let U : Ω → ℝ≥0∞ := fun ω => (1 + M₁ ω) ^ ((3 : ℝ)⁻¹)
  let V : Ω → ℝ≥0∞ := fun ω => M₃ ω ^ ((3 : ℝ)⁻¹)
  let Wn : ℕ → Ω → ℝ≥0∞ := fun n ω => (1 + M₂ n ω ^ p) ^ ((3 : ℝ)⁻¹)
  let S : Ω → ℝ≥0∞ := fun ω =>
    ∑' n : ℕ, ENNReal.ofReal (Real.exp (θ * (1 - n))) * (U ω * V ω * Wn n ω)
  have hUm : AEMeasurable U P := (aemeasurable_const.add hM₁m).pow_const _
  have hVm : AEMeasurable V P := hM₃m.pow_const _
  have hWm : ∀ n, AEMeasurable (Wn n) P := fun n =>
    (aemeasurable_const.add ((hM₂m n).pow_const p)).pow_const _
  have hTm : ∀ n : ℕ, AEMeasurable
      (fun ω => ENNReal.ofReal (Real.exp (θ * (1 - (n : ℝ)))) * (U ω * V ω * Wn n ω)) P :=
    fun n => aemeasurable_const.mul ((hUm.mul hVm).mul (hWm n))
  have hSm : AEMeasurable S P := AEMeasurable.tsum hTm
  refine ⟨fun ω => S ω ^ b⁻¹, hSm.pow_const _, ?_, ?_⟩
  · -- the moment bound
    have hLb : ∀ ω, (S ω ^ b⁻¹) ^ b = S ω := fun ω => by
      rw [← ENNReal.rpow_mul, inv_mul_cancel₀ hb0.ne', ENNReal.rpow_one]
    simp_rw [hLb]
    have hterm : ∀ n : ℕ, ∫⁻ ω, U ω * V ω * Wn n ω ∂P ≤
        (2 + K₁ + K₃) + K₂ * ENNReal.ofReal (Real.exp (A * n)) := by
      intro n
      calc ∫⁻ ω, U ω * V ω * Wn n ω ∂P
          ≤ ∫⁻ ω, (U ω ^ 3 + V ω ^ 3) + Wn n ω ^ 3 ∂P :=
            lintegral_mono fun ω => ul_amgm _ _ _
        _ = ∫⁻ ω, (1 + M₁ ω) + M₃ ω + (1 + M₂ n ω ^ p) ∂P := by
            simp only [U, V, Wn, ul_cbrt_cube]
        _ = (∫⁻ ω, (1 + M₁ ω) ∂P + ∫⁻ ω, M₃ ω ∂P) + ∫⁻ ω, (1 + M₂ n ω ^ p) ∂P := by
            rw [lintegral_add_left' (f := fun ω => 1 + M₁ ω + M₃ ω)
                ((aemeasurable_const.add hM₁m).add hM₃m),
              lintegral_add_left' (f := fun ω => 1 + M₁ ω) (aemeasurable_const.add hM₁m)]
        _ = ((1 + ∫⁻ ω, M₁ ω ∂P) + ∫⁻ ω, M₃ ω ∂P) + (1 + ∫⁻ ω, M₂ n ω ^ p ∂P) := by
            rw [lintegral_add_left' (f := fun _ => (1 : ℝ≥0∞)) aemeasurable_const,
              lintegral_add_left' (f := fun _ => (1 : ℝ≥0∞)) aemeasurable_const]
            simp
        _ ≤ ((1 + K₁) + K₃) + (1 + K₂ * ENNReal.ofReal (Real.exp (A * n))) := by
            exact add_le_add (add_le_add (add_le_add le_rfl hM₁i) hM₃i)
              (add_le_add le_rfl (hM₂i n))
        _ = (2 + K₁ + K₃) + K₂ * ENNReal.ofReal (Real.exp (A * n)) := by ring
    calc ∫⁻ ω, S ω ∂P
        = ∑' n : ℕ, ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * (1 - n))) * (U ω * V ω * Wn n ω) ∂P :=
          lintegral_tsum hTm
      _ = ∑' n : ℕ, ENNReal.ofReal (Real.exp (θ * (1 - n))) * ∫⁻ ω, U ω * V ω * Wn n ω ∂P := by
          congr 1; funext n
          exact lintegral_const_mul'' _ ((hUm.mul hVm).mul (hWm n))
      _ ≤ ∑' n : ℕ, ENNReal.ofReal (Real.exp θ) * ((2 + K₁ + K₃) + K₂) *
            ENNReal.ofReal (Real.exp (-1)) ^ n := by
          refine ENNReal.tsum_le_tsum fun n => ?_
          exact (mul_le_mul_of_nonneg_left (hterm n) bot_le).trans (ul_geom hθ n _ _)
      _ = ENNReal.ofReal (Real.exp θ) * (2 + K₁ + K₃ + K₂) *
            ∑' n : ℕ, ENNReal.ofReal (Real.exp (-1)) ^ n := ENNReal.tsum_mul_left
  · -- the pathwise domination
    filter_upwards [LocLen.b5UniformArcStmt_holds κ hκ hκ4 1 one_pos P B X hB hX hind,
      E1.ae_rawConverges_h0f (κ := κ) (T := 1) hB hX hind zero_le_one,
      F1.ae_lsw2_driver_facts hκ hκ4 hB, hM₁, hM₃, ae_all_iff.2 hM₂]
      with ω hU hraw hDF h1 h3 h2
    obtain ⟨hW, hW0, _⟩ := hDF
    set R := ulRad κ B ω with hRdef
    have hR0 : 0 ≤ R := (abs_nonneg _).trans (le_max_left _ _)
    set n := ⌈R⌉₊ with hndef
    have hRn : R ≤ n := Nat.le_ceil R
    have hnR : (n : ℝ) < R + 1 := Nat.ceil_lt_add_one hR0
    -- zero-time values
    have hVc : Continuous (B2.Vr κ 1 B ω) := B2.continuous_vrev hW 1
    have hV0 : B2.Vr κ 1 B ω 0 = 0 := B2.vrev_zero zero_le_one
    have hzm0 : zeroMinus (B2.Vr κ 1 B ω) 0 = 0 := B5.zeroMinus_zero_time hVc hV0
    have hzp0 : zeroPlus (B2.Vr κ 1 B ω) 0 = 0 := by
      rw [Thm18Asm.G4Core.zeroPlus_eq_neg_zeroMinus_neg hVc le_rfl,
        B5.zeroMinus_zero_time hVc.neg (by simp [hV0]), neg_zero]
    obtain ⟨e1, e2⟩ := hU 1 ⟨zero_le_one, le_rfl⟩
    rw [sub_self, hzm0] at e1
    rw [sub_self, hzp0] at e2
    have hm1 : |zeroMinus (B2.Vr κ 1 B ω) 1| ≤ R := le_max_left _ _
    have hp1 : |zeroPlus (B2.Vr κ 1 B ω) 1| ≤ R := le_max_right _ _
    have hsub1 : Ioo (zeroMinus (B2.Vr κ 1 B ω) 1) 0 ⊆ Icc (-(n : ℝ)) n := fun y hy =>
      ⟨by linarith [neg_abs_le (zeroMinus (B2.Vr κ 1 B ω) 1), hy.1],
        by linarith [hy.2, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]⟩
    have hsub2 : Ioo 0 (zeroPlus (B2.Vr κ 1 B ω) 1) ⊆ Icc (-(n : ℝ)) n := fun y hy =>
      ⟨by linarith [hy.1, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)],
        by linarith [le_abs_self (zeroPlus (B2.Vr κ 1 B ω) 1), hy.2]⟩
    -- the key bound for any `x ≤ ν_y([−n,n])`
    have key : ∀ x : ℝ≥0∞,
        x ≤ qBoundaryMeasure (Real.sqrt κ) (B2.h0f κ 1 B X ω) (Icc (-(n : ℝ)) n) →
        x ≤ S ω ^ b⁻¹ := by
      intro x hx
      rw [ul_scale hraw] at hx
      set Ec := ENNReal.ofReal (Real.exp (Real.sqrt κ * B2.h0f κ 1 B X ω ulNorm / 2))
      set νn := qBoundaryMeasure (Real.sqrt κ) (ulShift (B2.h0f κ 1 B X ω))
        (Icc (-(n : ℝ)) n)
      have hEc : Ec ^ b ≤ U ω := by
        refine ul_le_cbrt ?_
        rw [ul_rpow_three, ul_ofReal_exp_rpow]
        have e : Real.sqrt κ * B2.h0f κ 1 B X ω ulNorm / 2 * (b * 3) =
            (Real.sqrt κ / 2 * (b * 3)) * ulConst κ B X ω := by
          unfold ulConst; ring
        rw [e]
        exact (ul_exp_le (by positivity) hbs).trans (add_le_add le_rfl h1)
      have hνn : νn ^ b ≤ Wn n ω := by
        refine ul_le_cbrt ?_
        rw [ul_rpow_three]
        exact (ul_rpow_le_one_add (by positivity) hbp).trans
          (add_le_add le_rfl (ENNReal.rpow_le_rpow (h2 n) hp.le))
      have hV : ENNReal.ofReal (Real.exp (θ * R)) ≤ V ω := by
        refine ul_le_cbrt ?_
        rw [ul_ofReal_exp_rpow]
        have e : θ * R * 3 = 3 * θ * ulRad κ B ω := by rw [hRdef]; ring
        rw [e]
        exact h3
      have hone : 1 ≤ ENNReal.ofReal (Real.exp (θ * (1 - n))) * V ω := by
        calc (1 : ℝ≥0∞) ≤ ENNReal.ofReal (Real.exp (θ * (1 - n) + θ * R)) := by
              rw [← ENNReal.ofReal_one]
              exact ENNReal.ofReal_le_ofReal (Real.one_le_exp (by nlinarith))
          _ = ENNReal.ofReal (Real.exp (θ * (1 - n))) * ENNReal.ofReal (Real.exp (θ * R)) := by
              rw [Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
          _ ≤ _ := by gcongr
      have hxb : x ^ b ≤ S ω := by
        calc x ^ b ≤ (Ec * νn) ^ b := ENNReal.rpow_le_rpow hx hb0.le
          _ = Ec ^ b * νn ^ b := ENNReal.mul_rpow_of_nonneg _ _ hb0.le
          _ ≤ U ω * Wn n ω := by gcongr
          _ = U ω * Wn n ω * 1 := (mul_one _).symm
          _ ≤ U ω * Wn n ω * (ENNReal.ofReal (Real.exp (θ * (1 - n))) * V ω) := by gcongr
          _ = ENNReal.ofReal (Real.exp (θ * (1 - n))) * (U ω * V ω * Wn n ω) := by ring
          _ ≤ S ω := ENNReal.le_tsum (f := fun n : ℕ =>
              ENNReal.ofReal (Real.exp (θ * (1 - n))) * (U ω * V ω * Wn n ω)) n
      calc x = (x ^ b) ^ b⁻¹ := by
            rw [← ENNReal.rpow_mul, mul_inv_cancel₀ hb0.ne', ENNReal.rpow_one]
        _ ≤ S ω ^ b⁻¹ := ENNReal.rpow_le_rpow hxb (inv_nonneg.2 hb0.le)
    refine ⟨key _ ?_, key _ ?_⟩
    · rw [show lenArc κ B X ω 1 = LocLen.unzipLengthsArc (Real.sqrt κ) (B2.cfg κ B X ω) 1 from rfl,
        e1]
      exact measure_mono hsub1
    · rw [show lenArc κ B X ω 1 = LocLen.unzipLengthsArc (Real.sqrt κ) (B2.cfg κ B X ω) 1 from rfl,
        e2]
      exact measure_mono hsub2

end BaseFin2
end QuantumZipper
