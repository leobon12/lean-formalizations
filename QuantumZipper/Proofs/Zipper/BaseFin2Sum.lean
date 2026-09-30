import QuantumZipper.Proofs.Zipper.BaseFin2Defs
import QuantumZipper.Proofs.Zipper.ZipLenField

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# X1 (D75): summation of the capacity pieces, `BaseSumStmt ⇐ BaseScaleStmt ∧ BaseUnitMomStmt`

For a `Γ⁰` pair `(B, X)` and `a = 2^{-k}`, `BaseScaleStmt` bounds the `k`-th term by
`scFac κ a X · unit(B^{(k)}, X^{(k)})`, and `scFac κ a X = e^{(γ/2) c} a^{2−κ/4} e^{(γ/2) h_a(0)}`
with `c = X(fc(0,1))` the gauge constant and `h_a(0)` the semicircle average of the normalized
field `nrm X` (`WedgeUnzip.scFac_eq`, `evalReg_addConst_fc_of_regular`). With the unit majorants
`U_k` of `BaseUnitMomStmt` (applied to the normalized scaled pairs, `scPairR_props`) and
`M_k = a^{2−κ/4} e^{(γ/2) h_a(0)} U_k`, `E[M_k^p] ≤ (1 + C)^{1/2} ρ^k` with `ρ < 1`
(`WedgeUnzip.lintegral_scaled_moment_le`, as in `WedgeUnzip.tipXPieceMom_of_unit_raw`), so
`Σ_k M_k^p < ∞` a.s.; then `M_k ≤ S^{1/p}` with `S = Σ M_k^p` and `M_k ≤ M_k^p S^{(1−p)/p}`, hence
`Σ_k term_k ≤ e^{(γ/2) c} Σ_k M_k < ∞`.

Own elementary bookkeeping (the scaling rule: Sheffield arXiv:1012.4797, §5.1, pp. 60–62).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace BaseFin2

open WedgeUnzip RegUnif

/-- `y ≤ y^p R^{1−p}` for `y ≤ R`, `0 < p ≤ 1`. -/
theorem bf2_le_rpow_mul_rpow {y R : ℝ≥0∞} {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) (hy : y ≤ R) :
    y ≤ y ^ p * R ^ (1 - p) := by
  rcases eq_or_ne y 0 with h0 | h0
  · subst h0; exact zero_le
  rcases eq_or_ne y ⊤ with ht | ht
  · subst ht
    have hR : R = ⊤ := top_le_iff.1 hy
    subst hR
    rw [ENNReal.top_rpow_of_pos hp]
    exact le_top.trans (le_of_eq (by
      rcases eq_or_lt_of_le hp1 with h | h
      · rw [h, sub_self, ENNReal.rpow_zero, mul_one]
      · rw [ENNReal.top_rpow_of_pos (by linarith), ENNReal.top_mul_top]))
  calc y = y ^ (p + (1 - p)) := by rw [add_sub_cancel, ENNReal.rpow_one]
    _ = y ^ p * y ^ (1 - p) := ENNReal.rpow_add _ _ h0 ht
    _ ≤ y ^ p * R ^ (1 - p) := mul_le_mul' le_rfl (ENNReal.rpow_le_rpow hy (by linarith))

/-- **Summation.** If `Σ_k M_k^p < ∞` (`0 < p ≤ 1`) then `Σ_k M_k < ∞`. -/
theorem bf2_tsum_lt_top_of_rpow {M : ℕ → ℝ≥0∞} {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1)
    (hS : ∑' k, M k ^ p < ⊤) : ∑' k, M k < ⊤ := by
  set S := ∑' k, M k ^ p
  have hle : ∀ k, M k ≤ S ^ p⁻¹ := fun k => by
    have h1 : M k ^ p ≤ S := ENNReal.le_tsum (f := fun k => M k ^ p) k
    calc M k = (M k ^ p) ^ p⁻¹ := (ENNReal.rpow_rpow_inv hp.ne' _).symm
      _ ≤ S ^ p⁻¹ := ENNReal.rpow_le_rpow h1 (inv_nonneg.2 hp.le)
  calc ∑' k, M k ≤ ∑' k, M k ^ p * (S ^ p⁻¹) ^ (1 - p) :=
        ENNReal.tsum_le_tsum fun k => bf2_le_rpow_mul_rpow hp hp1 (hle k)
    _ = S * (S ^ p⁻¹) ^ (1 - p) := ENNReal.tsum_mul_right
    _ < ⊤ := ENNReal.mul_lt_top hS
        (ENNReal.rpow_lt_top_of_nonneg (by linarith)
          (ENNReal.rpow_lt_top_of_nonneg (inv_nonneg.2 hp.le) hS.ne).ne)

/-- **`BaseSumStmt` from the scaling and the unit moments.** -/
theorem baseSum_of_scale_unit (hSc : BaseScaleStmt) (hU : BaseUnitMomStmt) : BaseSumStmt := by
  intro κ hκ hκ4 Ω _ P _ B X hB hX hind
  obtain ⟨q₁, hq₁, C₁, hC₁, hU'⟩ := hU κ hκ hκ4
  set p : ℝ := min (q₁ / 2) (min 1 ((8 - κ) / (4 * κ))) with hpdef
  have hp : 0 < p := by
    refine lt_min (by linarith) (lt_min one_pos ?_)
    exact div_pos (by linarith) (by positivity)
  have hp1 : p ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hpq₁ : 2 * p ≤ q₁ := by
    have h' : p ≤ q₁ / 2 := min_le_left _ _
    linarith
  have hpκ : p ≤ (8 - κ) / (4 * κ) := (min_le_right _ _).trans (min_le_right _ _)
  set e : ℝ := p * (2 - κ / 4) - p ^ 2 * κ / 2 with hedef
  have he : 0 < e := by
    have h1 : p * κ ≤ (8 - κ) / 4 := by
      have := mul_le_mul_of_nonneg_right hpκ hκ.le
      rwa [show (8 - κ) / (4 * κ) * κ = (8 - κ) / 4 by field_simp] at this
    have : e = p * ((2 - κ / 4) - p * κ / 2) := by rw [hedef]; ring
    rw [this]
    exact mul_pos hp (by nlinarith)
  set ρ : ℝ≥0∞ := ENNReal.ofReal ((2 : ℝ) ^ (-e)) with hρdef
  have hρ : ρ < 1 := by
    rw [hρdef, ← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff one_pos).2
      (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith))
  -- unit majorants for the scaled pairs
  have hpair := fun k => scPairR_props (κ := κ) hB hX hind k
  have hUk : ∀ k : ℕ, ∃ U : Ω → ℝ≥0∞, AEMeasurable U P ∧ ∫⁻ ω, U ω ^ q₁ ∂P ≤ C₁ ∧
      ∀ᵐ ω ∂P, termL κ (scB k B) (fun ω => scNrmR κ (radius k) (X ω)) ω 0 ≤ U ω ∧
        termR κ (scB k B) (fun ω => scNrmR κ (radius k) (X ω)) ω 0 ≤ U ω := fun k =>
    hU' P (scB k B) _ (hpair k).1 (hpair k).2.1 (hpair k).2.2.1 (hpair k).2.2.2
  choose U hUm hUC hUd using hUk
  -- the normalized field and the gauge factor
  have hXn : IsFreeGFFModConstH (nrmF X) P := isFreeGFFModConstH_nrmF hX
  have hNn : IsNrmSample (nrmF X) := isNrmSample_nrmF X
  set g : ℕ → Ω → ℝ := fun k ω => evalReg (nrmF X ω) (foldedCircle 0 (radius k)) with hgdef
  have hgm : ∀ k, Measurable (g k) := fun k => measurable_evalReg_fc_of_free hXn 0 _
  set fac : ℕ → Ω → ℝ≥0∞ := fun k ω => ENNReal.ofReal (radius k ^ (2 - κ / 4) *
    Real.exp (Real.sqrt κ * g k ω / 2)) with hfacdef
  have hfacm : ∀ k, Measurable (fac k) := fun k =>
    ENNReal.measurable_ofReal.comp (measurable_const.mul (Real.measurable_exp.comp
      ((measurable_const.mul (hgm k)).div_const _)))
  have hmgf : ∀ k : ℕ, ∫⁻ ω, ENNReal.ofReal (Real.exp ((p * Real.sqrt κ) * g k ω)) ∂P =
      ENNReal.ofReal (Real.exp ((p * Real.sqrt κ) ^ 2 * ((k : ℝ) * Real.log 2))) := fun k =>
    lintegral_exp_evalReg_fc0_nrm hXn hNn (p * Real.sqrt κ) k
  set M : ℕ → Ω → ℝ≥0∞ := fun k ω => fac k ω * U k ω with hMdef
  have hMm : ∀ k, AEMeasurable (M k) P := fun k => (hfacm k).aemeasurable.mul (hUm k)
  have hMp : ∀ k, ∫⁻ ω, M k ω ^ p ∂P ≤ (1 + C₁) ^ (1 / 2 : ℝ) * ρ ^ k := fun k =>
    lintegral_scaled_moment_le hκ hp hpq₁ (hgm k) k (hmgf k) (hUm k) (hUC k)
  -- `Σ_k M_k^p < ∞` a.s.
  have hsum : ∫⁻ ω, ∑' k, M k ω ^ p ∂P < ⊤ := by
    rw [lintegral_tsum fun k => (hMm k).pow_const p]
    calc ∑' k, ∫⁻ ω, M k ω ^ p ∂P ≤ ∑' k, (1 + C₁) ^ (1 / 2 : ℝ) * ρ ^ k :=
          ENNReal.tsum_le_tsum hMp
      _ = (1 + C₁) ^ (1 / 2 : ℝ) * (1 - ρ)⁻¹ := by
          rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
      _ < ⊤ := ENNReal.mul_lt_top
          (ENNReal.rpow_lt_top_of_nonneg (by norm_num)
            (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, hC₁⟩))
          (ENNReal.inv_lt_top.2 (tsub_pos_of_lt hρ))
  have hae_sum : ∀ᵐ ω ∂P, ∑' k, M k ω ^ p < ⊤ :=
    ae_lt_top' (AEMeasurable.tsum fun k => (hMm k).pow_const p) hsum.ne
  -- pointwise comparison
  have hcmp : ∀ᵐ ω ∂P, ∀ k : ℕ,
      termL κ B X ω k ≤ ENNReal.ofReal (Real.exp (Real.sqrt κ * X ω (foldedCircle 0 1) / 2)) *
          M k ω ∧
        termR κ B X ω k ≤ ENNReal.ofReal (Real.exp (Real.sqrt κ * X ω (foldedCircle 0 1) / 2)) *
          M k ω := by
    rw [ae_all_iff]
    intro k
    filter_upwards [hSc κ hκ hκ4 P B X hB hX hind k, hUd k,
      RegSample.ae_isRegularSample hX] with ω hs hu hreg
    have hfac : scFac κ (radius k) (X ω) =
        ENNReal.ofReal (Real.exp (Real.sqrt κ * X ω (foldedCircle 0 1) / 2)) * fac k ω := by
      rw [scFac_eq hκ]
      have hev : evalReg (X ω) (foldedCircle 0 (radius k)) =
          g k ω + X ω (foldedCircle 0 1) := by
        simp only [hgdef, nrmF_apply, B1Full.nrm]
        rw [B3d.ZipLen.evalReg_addConst_fc_of_regular hreg _ 0 (radius_pos k)]
        ring
      rw [hev, hfacdef, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
      congr 1
      rw [mul_add, add_div, Real.exp_add]
      ring
    refine ⟨hs.1.trans ?_, hs.2.trans ?_⟩
    · rw [hfac, mul_assoc]; exact mul_le_mul' le_rfl (mul_le_mul' le_rfl hu.1)
    · rw [hfac, mul_assoc]; exact mul_le_mul' le_rfl (mul_le_mul' le_rfl hu.2)
  filter_upwards [hae_sum, hcmp] with ω hω hc
  have hM : ∑' k, M k ω < ⊤ := bf2_tsum_lt_top_of_rpow hp hp1 hω
  set E := ENNReal.ofReal (Real.exp (Real.sqrt κ * X ω (foldedCircle 0 1) / 2))
  have hE : E * ∑' k, M k ω < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hM
  refine ⟨lt_of_le_of_lt ?_ hE, lt_of_le_of_lt ?_ hE⟩
  · rw [← ENNReal.tsum_mul_left]; exact ENNReal.tsum_le_tsum fun k => (hc k).1
  · rw [← ENNReal.tsum_mul_left]; exact ENNReal.tsum_le_tsum fun k => (hc k).2

end BaseFin2
end QuantumZipper
