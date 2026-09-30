import QuantumZipper.Proofs.Thm18.G3PalmRBasic

/-!
# G3-PALMR, part 2: `G3GeoPalmRStmt` from a uniform rooted-measure bound

`G3GeoPalmRStmt γ` (`G3GeoStmt.lean`) is the Palm form of Sheffield's "we may choose `δ` small
enough so that with high probability `R(x) ∈ B₁(0)`" (arXiv:1012.4797, proof of Theorem 1.8,
§5.4, p. 71; the paper gives no argument):
`E[ν_h[−δ,0]; ν_h[0,½] < ν_h[−δ,0]] ≤ ε E ν_h[−δ,0]` for small `δ`.

Route (rooted measure; Duplantier–Sheffield, *Liouville quantum gravity and KPZ*, Invent. Math.
185 (2011), arXiv:0808.1560, §3.3, p. 22: under the rooted measure, given the root `x`, the field
is the GFF plus `γ ξ^x`, a `γ`-log singularity at `x`; here in the normalized free-field form
`S5.FieldLaw.Raw.palm_free_Ioo`):

1. `ν_h = |t| ν_Z` (`Z = N_S X₀`, unit-normalized free field), so pathwise the bad event
   `ν_h[0,½] < ν_h[−δ,0]` forces `ν_Z[¼,½] < 4δ ν_Z[−¼,0]` (`ae_hν_bad_imp`), and
   `ν_h[−δ,0] = ∫_{(−δ,0)} |t| dν_Z` (`ae_hν_Icc_eq_Ioo`).
2. Palm formula with `φ(c, t) = 1_{g3PalmEv δ}(c) |t|` and with `φ(c, t) = |t|`:
   `E[ν_h[−δ,0]; bad] ≤ ∫_{−δ}^0 ρ(x)|x| P(ν^x[¼,½] < 4δ ν^x[−¼,0]) dx` and
   `E ν_h[−δ,0] = ∫_{−δ}^0 ρ(x)|x| dx`, where `ν^x` is the boundary measure of the Palm-shifted
   field `palmFreeField γ refS X₀ x = N_S(X₀ + (γ/2)(neumannH x · − k_S))`.
3. The named input `G3PalmRTightStmt γ` bounds `P(ν^x[¼,½] < 4δ ν^x[−¼,0]) ≤ ε` uniformly in
   `x ∈ (−δ, 0)` for small `δ`, which closes the estimate (`g3GeoPalmRStmt_of_tight`).

Steps 1–2 and the assembly are proved (own bookkeeping around the cited Palm formula).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm

open S5.FieldLaw.Raw (freeFieldN palmFreeField)
open Factorization (coords)

local notation "Ω₀" => gffBase.Ω
local notation "X₀" => gffBase.X

/-- **Uniform rooted-measure bound (named input).** For every `ε > 0` and all small `δ > 0`,
uniformly in the root `x ∈ (−δ, 0)`, the Palm-shifted unit-normalized free field
`h^x = N_S(X₀ + (γ/2)(neumannH x · − k_S))` (a `γ`-log singularity at `x`, `γ < Q`) satisfies
`P(ν^x[¼, ½] < 4δ · ν^x[−¼, 0]) ≤ ε`.

Why it is true: `ν^x[¼,½] > 0` a.s. and `ν^x[−¼,0] < ∞` a.s. (log singularity of strength
`γ < Q`, M4-P4 `LogSing.ae_logSingularity`), so for each fixed `x` the probability tends to `0`
as `δ → 0`; uniformity in `x ∈ (−δ, 0)` follows from the horizontal translation invariance of
the free boundary GFF modulo constants (the Palm fields at different roots, translated to the
root `0`, differ modulo additive constants by a deterministic function bounded on `[−1, 1]`
uniformly in `x ∈ [−⅛, 0]`), after enlarging the windows to `[x−¼, x+¼]` and shrinking
`[¼,½]` to `[x+⅜, x+½]` (the event is invariant under additive constants). -/
def G3PalmRTightStmt (γ : ℝ) : Prop :=
  ∀ ε > 0, ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ x ∈ Ioo (-δ) 0,
    gffBase.P {ω | qBoundaryMeasure γ (palmFreeField γ refS X₀ x ω) (Icc (1 / 4) (1 / 2)) <
      ENNReal.ofReal (4 * δ) *
        qBoundaryMeasure γ (palmFreeField γ refS X₀ x ω) (Icc (-(1 / 4)) 0)} ≤ ENNReal.ofReal ε

/-- The bad-event test function `1_{g3PalmEv δ}(c) · |t|`. -/
def g3PalmBadφ (γ δ : ℝ) (c : ℕ → ℝ) (t : ℝ) : ℝ≥0∞ :=
  (g3PalmEv γ δ).indicator (fun _ => (1 : ℝ≥0∞)) c * ENNReal.ofReal |t|

/-- The mass test function `|t|`. -/
def g3PalmMassφ (_c : ℕ → ℝ) (t : ℝ) : ℝ≥0∞ := ENNReal.ofReal |t|

theorem measurable_g3PalmBadφ (γ δ : ℝ) : Measurable (Function.uncurry (g3PalmBadφ γ δ)) :=
  ((measurable_const.indicator (measurableSet_g3PalmEv γ δ)).comp measurable_fst).mul
    (by fun_prop : Measurable fun p : (ℕ → ℝ) × ℝ => ENNReal.ofReal |p.2|)

theorem measurable_g3PalmMassφ : Measurable (Function.uncurry g3PalmMassφ) :=
  (by fun_prop : Measurable fun p : (ℕ → ℝ) × ℝ => ENNReal.ofReal |p.2|)

theorem isAdmissibleH_refS : IsAdmissibleH refS :=
  D3Plus.isAdmissibleH_foldedCircle' 0 one_pos

theorem Icc_neg_zero_subset_one {δ : ℝ} (hδ : δ ≤ 1) :
    Icc (-δ) 0 ⊆ Icc (-((1 : ℕ) : ℝ)) ((1 : ℕ) : ℝ) :=
  Icc_subset_Icc (by push_cast; linarith) (by norm_num)

/-- **The Palm identity for the mass**: `E ∫_{(−δ,0)} |t| dν_Z = ∫_{−δ}^0 ρ(x) |x| dx`. -/
theorem lintegral_mass_palm {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {δ : ℝ} (hδ : δ ≤ 1) :
    ∫⁻ ω, ∫⁻ t in Ioo (-δ) 0, ENNReal.ofReal |t| ∂(g3Zν γ ω) ∂gffBase.P =
      ∫⁻ x in Ioo (-δ) 0, ENNReal.ofReal (PalmNorm.rhoNorm γ 0 refS x) *
        ENNReal.ofReal |x| := by
  have h := S5.FieldLaw.Raw.palm_free_Ioo (P := gffBase.P) (X := X₀) gffBase.gff hγ hγ2
    isAdmissibleH_refS measure_univ (Icc_neg_zero_subset_one hδ) measurable_g3PalmMassφ
  simp only [g3PalmMassφ, lintegral_const, measure_univ, mul_one] at h
  exact h

/-- **The Palm bound for the bad event**, given a uniform bound `q` on the rooted probabilities. -/
theorem lintegral_bad_palm_le {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {δ : ℝ} (hδ : δ ≤ 1)
    {q : ℝ≥0∞}
    (hq : ∀ x ∈ Ioo (-δ) 0,
      gffBase.P {ω | qBoundaryMeasure γ (palmFreeField γ refS X₀ x ω) (Icc (1 / 4) (1 / 2)) <
        ENNReal.ofReal (4 * δ) *
          qBoundaryMeasure γ (palmFreeField γ refS X₀ x ω) (Icc (-(1 / 4)) 0)} ≤ q) :
    ∫⁻ ω, ∫⁻ t in Ioo (-δ) 0, g3PalmBadφ γ δ (coords (freeFieldN refS X₀ ω)) t
        ∂(g3Zν γ ω) ∂gffBase.P ≤
      q * ∫⁻ x in Ioo (-δ) 0, ENNReal.ofReal (PalmNorm.rhoNorm γ 0 refS x) *
        ENNReal.ofReal |x| := by
  rw [S5.FieldLaw.Raw.palm_free_Ioo (P := gffBase.P) (X := X₀) gffBase.gff hγ hγ2
    isAdmissibleH_refS measure_univ (Icc_neg_zero_subset_one hδ) (measurable_g3PalmBadφ γ δ)]
  have hin : ∀ x ∈ Ioo (-δ) 0,
      ∫⁻ ω, g3PalmBadφ γ δ (coords (palmFreeField γ refS X₀ x ω)) x ∂gffBase.P ≤
        q * ENNReal.ofReal |x| := by
    intro x hx
    set T : Set Ω₀ := {ω | qBoundaryMeasure γ (palmFreeField γ refS X₀ x ω) (Icc (1 / 4) (1 / 2)) <
        ENNReal.ofReal (4 * δ) *
          qBoundaryMeasure γ (palmFreeField γ refS X₀ x ω) (Icc (-(1 / 4)) 0)} with hT
    unfold g3PalmBadφ
    rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
    refine mul_le_mul' ?_ le_rfl
    calc ∫⁻ ω, (g3PalmEv γ δ).indicator (fun _ => (1 : ℝ≥0∞))
          (coords (palmFreeField γ refS X₀ x ω)) ∂gffBase.P
        ≤ ∫⁻ ω, T.indicator (fun _ => (1 : ℝ≥0∞)) ω ∂gffBase.P := by
          refine lintegral_mono fun ω => ?_
          by_cases hω : coords (palmFreeField γ refS X₀ x ω) ∈ g3PalmEv γ δ
          · have hT' : ω ∈ T := coords_mem_g3PalmEv_imp γ δ _ hω
            rw [indicator_of_mem hω, indicator_of_mem hT']
          · rw [indicator_of_notMem hω]
            exact bot_le
      _ ≤ ∫⁻ _ in T, (1 : ℝ≥0∞) ∂gffBase.P := lintegral_indicator_le _ _
      _ = gffBase.P T := by rw [setLIntegral_const, one_mul]
      _ ≤ q := hq x hx
  have hρm : Measurable fun x => ENNReal.ofReal (PalmNorm.rhoNorm γ 0 refS x) :=
    (E1.measurable_rhoNorm measurable_const refS).ennreal_ofReal
  calc ∫⁻ x in Ioo (-δ) 0, ENNReal.ofReal (PalmNorm.rhoNorm γ 0 refS x) *
        ∫⁻ ω, g3PalmBadφ γ δ (coords (palmFreeField γ refS X₀ x ω)) x ∂gffBase.P
      ≤ ∫⁻ x in Ioo (-δ) 0, q * (ENNReal.ofReal (PalmNorm.rhoNorm γ 0 refS x) *
          ENNReal.ofReal |x|) := by
        refine setLIntegral_mono' measurableSet_Ioo fun x hx => ?_
        rw [mul_left_comm]
        exact mul_le_mul' le_rfl (hin x hx)
    _ = q * ∫⁻ x in Ioo (-δ) 0, ENNReal.ofReal (PalmNorm.rhoNorm γ 0 refS x) *
          ENNReal.ofReal |x| :=
        lintegral_const_mul q (hρm.mul (by fun_prop))

/-- **`G3GeoPalmRStmt` from the uniform rooted-measure bound.** -/
theorem g3GeoPalmRStmt_of_tight {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hT : G3PalmRTightStmt γ) : G3GeoPalmRStmt γ := by
  intro ε hε
  filter_upwards [hT ε hε, Ioc_mem_nhdsGT (show (0 : ℝ) < 1 / 4 by norm_num)] with δ hδT hδ
  have hδ1 : δ ≤ 1 := by linarith [hδ.2]
  have h1 : ∫⁻ ω, (if g3Hν γ ω (Icc 0 (1 / 2)) < g3Hν γ ω (Icc (-δ) 0) then
        g3Hν γ ω (Icc (-δ) 0) else 0) ∂gffBase.P ≤
      ∫⁻ ω, ∫⁻ t in Ioo (-δ) 0, g3PalmBadφ γ δ (coords (freeFieldN refS X₀ ω)) t
        ∂(g3Zν γ ω) ∂gffBase.P := by
    refine lintegral_mono_ae ?_
    filter_upwards [ae_hν_bad_imp hγ hγ2 hδ.1.le hδ.2, ae_hν_Icc_eq_Ioo hγ hγ2 δ]
      with ω hbad heq
    split_ifs with h
    · rw [heq]
      refine le_of_eq (lintegral_congr fun t => ?_)
      simp only [g3PalmBadφ, indicator_of_mem (hbad h), one_mul]
    · exact bot_le
  have h2 : ∫⁻ ω, g3Hν γ ω (Icc (-δ) 0) ∂gffBase.P =
      ∫⁻ x in Ioo (-δ) 0, ENNReal.ofReal (PalmNorm.rhoNorm γ 0 refS x) *
        ENNReal.ofReal |x| := by
    rw [← lintegral_mass_palm hγ hγ2 hδ1]
    exact lintegral_congr_ae (ae_hν_Icc_eq_Ioo hγ hγ2 δ)
  rw [h2]
  exact h1.trans (lintegral_bad_palm_le hγ hγ2 hδ1 hδT)

/-- **`G3GeoStmt` from the uniform rooted-measure bound.** -/
theorem g3GeoStmt_of_tight {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hT : G3PalmRTightStmt γ) :
    G3GeoStmt γ :=
  g3GeoStmt_of_palmR hγ hγ2 (g3GeoPalmRStmt_of_tight hγ hγ2 hT)

end Thm18Asm
end QuantumZipper
