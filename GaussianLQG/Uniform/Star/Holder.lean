import GaussianLQG.Uniform.Star.Basic
import LQGMetric.Papers.DDDF.S6Mul

/-!
# Route U, step U15 (★), part 2: the Hölder half

The Hölder half of the ledger statement `star_bound` (`blueprint/phaseB/uniform-ledger.tex`, U15),
in U-form (constants before the probability space and before `ξ`): for `p ≥ 1` there is `ξ₀ > 0`
such that for every compact `K` there is `C < ∞` with

  `E[A_{X_n}(K)^p] ≤ C`,   `X_n = λ_n⁻¹ D^{2⁻ⁿ}_h`,

for every white noise `W`, the normalized GFF `h = h₀ − (h₀)_1(0)` built from it, every
`ξ ∈ (0, ξ₀]` and every `n`. Here `λ_n = lambdaN ξ W P n`.

Proof (ledger U15 outline; audit B-0b, M-2). Let `K ⊆ V'_R = boxIn R`, `V_R = boxOut R`,
`W'_n = shiftWN 4⁻ⁿ W` and `S_n = sup_{V_R} |h*_{2⁻ⁿ} − φ_{0,n}[W'_n]|` (U14).
1. Pathwise, on `{S_n < ∞}` (`holderConst_lfppDist_le`): global `≤` internal on `V_R` and
   `e^{ξ(φ + g)} ≤ e^{ξ S_n} e^{ξ φ}` on `V_R` give `A_{X_n}(K) ≤ e^{ξ S_n} H_n`, where
   `H_n = A(V'_R)` of `λ_n⁻¹ D_{φ_{0,n}[W'_n]}(·, ·; V_R)`, which is finite-valued for every `ω`
   since `V_R` is convex and `φ_{0,n}` continuous.
2. AM–GM: `A^p ≤ e^{2pξS_n} + H_n^{2p} ≤ G_n + H_n^{2p}`, where `G_n` is the measurable majorant of
   `e^{2p S_n}` (`ξ ≤ 1`) given by the Gaussian tail of U14; `E G_n ≤ M` uniformly in `n`.
3. U12 (`Uniform.IfaceHolderMomentU`) at order `2p` applied at the noise `W'_n` (it is U-form), with
   `λ_n(W'_n) = λ_n(W)` (`FieldCmp.lambdaN_shiftWN`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace GaussianLQG
namespace StarBound

open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

/-! ### The pathwise comparison -/

/-- **Pathwise Hölder comparison.** If `|h*_ε − φ| ≤ s` on `V_R = boxOut R`, with `φ`
continuous, and `K ⊆ V'_R = boxIn R`, then `A(K)` of `a D^ε_g` is at most `e^{|ξ| s}` times
`A(V'_R)` of `a D_φ(·, ·; V_R)`. -/
theorem holderConst_lfppDist_le {ξ ε a : ℝ} (ha : 0 ≤ a) {g : DistC} {φ : ℂ → ℝ}
    (hφ : Continuous φ) {R : ℝ} {K : Set ℂ} (hK : K ⊆ Uniform.boxIn R) {s : ℝ}
    (hs : ∀ x ∈ Uniform.boxOut R, |heatMollify ε g x - φ x| ≤ s) :
    holderConst (fun q => a * lfppDist ξ ε g q) K ≤
      ENNReal.ofReal (Real.exp (|ξ| * s)) * holderConst
        (fun q => a * (LFPP.lfppDOn ξ φ (Uniform.boxOut R) q.1 q.2).toReal) (Uniform.boxIn R) := by
  refine (UniformLimit.holderConst_le_ofReal_mul (Real.exp_pos _).le fun z hz w hw => ?_).trans
    (mul_le_mul_right (holderConst_mono_set _ hK) _)
  have h1 := lfppDOn_univ_toReal_le (ξ := ξ) hφ (convex_boxOut R) hs
    (boxIn_subset_boxOut R (hK hz)) (boxIn_subset_boxOut R (hK hw))
  show a * (lfppDistE ξ ε g z w).toReal ≤
    Real.exp (|ξ| * s) * (a * (LFPP.lfppDOn ξ φ (Uniform.boxOut R) z w).toReal)
  rw [LFPP.lfppDistE_eq_lfppDOn]
  calc a * (LFPP.lfppDOn ξ (heatMollify ε g) univ z w).toReal
      ≤ a * (Real.exp (|ξ| * s) * (LFPP.lfppDOn ξ φ (Uniform.boxOut R) z w).toReal) :=
        mul_le_mul_of_nonneg_left h1 ha
    _ = Real.exp (|ξ| * s) * (a * (LFPP.lfppDOn ξ φ (Uniform.boxOut R) z w).toReal) := by ring

/-- On `{Y < ∞}`, every term of the supremum `Y = sup_{z ∈ V} |u z|` is at most `Y.toReal`. -/
theorem abs_le_toReal_iSup {V : Set ℂ} {u : ℂ → ℝ}
    (hY : (⨆ z ∈ V, ENNReal.ofReal |u z|) ≠ ⊤) {x : ℂ} (hx : x ∈ V) :
    |u x| ≤ (⨆ z ∈ V, ENNReal.ofReal |u z|).toReal := by
  have h1 : ENNReal.ofReal |u x| ≤ ⨆ z ∈ V, ENNReal.ofReal |u z| :=
    le_iSup₂ (f := fun z (_ : z ∈ V) => ENNReal.ofReal |u z|) x hx
  have h2 := ENNReal.toReal_mono hY h1
  rwa [ENNReal.toReal_ofReal (abs_nonneg _)] at h2

/-- The weight factor: for `0 ≤ ξ ≤ 1`, `s ≥ 0` and `p ≥ 0`, `(e^{ξ s})^{2p} ≤ e^{2p s}`. -/
theorem ofReal_exp_rpow_le {ξ s p : ℝ} (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1) (hs : 0 ≤ s) (hp : 0 ≤ p) :
    ENNReal.ofReal (Real.exp (|ξ| * s)) ^ (2 * p) ≤ ENNReal.ofReal (Real.exp (2 * p * s)) := by
  rw [ofReal_exp_rpow _ (by positivity), abs_of_nonneg hξ0]
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
  have : ξ * s ≤ s := by nlinarith
  nlinarith

/-! ### The Hölder half of `star_bound` -/

/-- **The Hölder half of (★), U-form.** For `p ≥ 1` there is `ξ₀ ∈ (0, 1]` such that for every
compact `K` there is `C < ∞` such that, for every white noise `W` on any probability space, the
normalized whole-plane GFF `h = h₀ − (h₀)_1(0)` built from it (`h₀(φ) = W(testL2 φ)` a.s.), every
`ξ ∈ (0, ξ₀]` and every `n`: `E[A_{X}(K)^p] ≤ C` for `X = λ_n⁻¹ D^{2⁻ⁿ}_h`,
`λ_n = lambdaN ξ W P n`. Only the Hölder interface U12 is assumed. -/
theorem holder_half (hU12 : Uniform.IfaceHolderMomentU) {p : ℝ} (hp : 1 ≤ p) :
    ∃ ξ₀ : ℝ, 0 < ξ₀ ∧ ξ₀ ≤ 1 ∧ ∀ K : Set ℂ, IsCompact K → ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ} {h₀ : Ω → DistC},
        IsWhiteNoise P W → IsWholePlaneGFF h₀ P →
        (∀ φ : TestC, (fun ω => h₀ ω φ) =ᵐ[P] W (GFFExist.testL2 φ)) →
        ∀ ξ ∈ Set.Ioc (0 : ℝ) ξ₀, ∀ n : ℕ,
          ∫⁻ ω, holderConst (fun z => (lambdaN ξ W P n)⁻¹ *
              lfppDist ξ ((2 : ℝ)⁻¹ ^ n) (addConst (h₀ ω) (-circleAvg (h₀ ω) 1 0)) z) K ^ p ∂P
            ≤ C := by
  have hp0 : 0 ≤ p := by linarith
  obtain ⟨ξq, hξq, hU⟩ := hU12 (2 * p) (by linarith)
  refine ⟨min ξq 1, lt_min hξq one_pos, min_le_right _ _, fun K hK => ?_⟩
  obtain ⟨R, hR0, hKR⟩ := exists_subset_boxIn hK.isBounded
  obtain ⟨C₁₂, hC₁₂, hU'⟩ := hU R hR0
  obtain ⟨Cv, cv, hCv, hcv, hT⟩ := FieldCmp.heatMollify_phiMN_tail_unif.{0} (isCompact_boxOut R)
  set M : ℝ≥0∞ := ENNReal.ofReal
    (2 * Cv * Real.exp (2 * p + (2 * p + Real.log 2) ^ 2 / (4 * cv))) with hM
  refine ⟨M + C₁₂, ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, hC₁₂⟩,
    fun {Ω} _ {P} {W} {h₀} hW hh hae ξ hξ n => ?_⟩
  -- the shifted noise `W'_n`, the field `φ_{0,n}[W'_n]` and the comparison supremum `S_n`
  set a : ℝ := ((2 : ℝ)⁻¹ ^ n) ^ 2 with ha
  have hW' : IsWhiteNoise P (FieldCmp.shiftWN a W) := FieldCmp.isWhiteNoise_shiftWN hW a
  have hφc : ∀ ω, Continuous fun x => phiMN (FieldCmp.shiftWN a W) P 0 n x ω :=
    (isPhiVersion_phiMN hW' (Nat.zero_le n)).cont
  set Y : Ω → ℝ≥0∞ := fun ω => ⨆ z ∈ Uniform.boxOut R, ENNReal.ofReal
    |heatMollify ((2 : ℝ)⁻¹ ^ n) (addConst (h₀ ω) (-circleAvg (h₀ ω) 1 0)) z -
      phiMN (FieldCmp.shiftWN a W) P 0 n z ω| with hY
  have htail : ∀ k : ℕ, P {ω | ENNReal.ofReal k ≤ Y ω} ≤
      ENNReal.ofReal (Cv * Real.exp (-cv * (k : ℝ) ^ 2)) :=
    fun k => hT hW hh hae n k (Nat.cast_nonneg k)
  obtain ⟨G, hGm, hGY, hGint⟩ :=
    exists_measurable_exp_majorant P Y (a := 2 * p) (by positivity) hCv.le hcv htail
  have hfin : ∀ᵐ ω ∂P, Y ω ≠ ⊤ := by
    refine ae_iff.2 ?_
    simpa only [ne_eq, not_not] using measure_eq_top_eq_zero_of_tail P Y hcv htail
  -- the normalization
  have hc : 0 < lambdaN ξ W P n := lambdaN_pos hW n
  have hlam : lambdaN ξ (FieldCmp.shiftWN a W) P n = lambdaN ξ W P n :=
    FieldCmp.lambdaN_shiftWN hW a ξ n
  have hξ0 : 0 ≤ ξ := hξ.1.le
  have hξ1 : ξ ≤ 1 := hξ.2.trans (min_le_right _ _)
  -- the U12 bound at `W'_n`
  have h12 := hU' hW' ξ ⟨hξ.1, hξ.2.trans (min_le_left _ _)⟩ n
  rw [hlam] at h12
  set H : Ω → ℝ≥0∞ := fun ω => holderConst (fun z => (lambdaN ξ W P n)⁻¹ *
    (LFPP.lfppDOn ξ (fun x => phiMN (FieldCmp.shiftWN a W) P 0 n x ω) (Uniform.boxOut R)
      z.1 z.2).toReal) (Uniform.boxIn R) with hH
  -- the pathwise bound
  have hpt : ∀ᵐ ω ∂P, holderConst (fun z => (lambdaN ξ W P n)⁻¹ *
      lfppDist ξ ((2 : ℝ)⁻¹ ^ n) (addConst (h₀ ω) (-circleAvg (h₀ ω) 1 0)) z) K ^ p ≤
      G ω + H ω ^ (2 * p) := by
    filter_upwards [hfin] with ω hω
    have hs : ∀ x ∈ Uniform.boxOut R,
        |heatMollify ((2 : ℝ)⁻¹ ^ n) (addConst (h₀ ω) (-circleAvg (h₀ ω) 1 0)) x -
          phiMN (FieldCmp.shiftWN a W) P 0 n x ω| ≤ (Y ω).toReal :=
      fun x hx => abs_le_toReal_iSup hω hx
    have hA := holderConst_lfppDist_le (ξ := ξ) (inv_pos.2 hc).le (hφc ω) hKR hs
    calc holderConst (fun z => (lambdaN ξ W P n)⁻¹ *
          lfppDist ξ ((2 : ℝ)⁻¹ ^ n) (addConst (h₀ ω) (-circleAvg (h₀ ω) 1 0)) z) K ^ p
        ≤ (ENNReal.ofReal (Real.exp (|ξ| * (Y ω).toReal)) * H ω) ^ p :=
          ENNReal.rpow_le_rpow hA hp0
      _ ≤ ENNReal.ofReal (Real.exp (|ξ| * (Y ω).toReal)) ^ (2 * p) + H ω ^ (2 * p) :=
          mul_rpow_le_add _ _ hp0
      _ ≤ G ω + H ω ^ (2 * p) := by
          refine add_le_add_left ((ofReal_exp_rpow_le hξ0 hξ1 ENNReal.toReal_nonneg hp0).trans ?_) _
          exact hGY ω hω
  calc ∫⁻ ω, holderConst (fun z => (lambdaN ξ W P n)⁻¹ *
        lfppDist ξ ((2 : ℝ)⁻¹ ^ n) (addConst (h₀ ω) (-circleAvg (h₀ ω) 1 0)) z) K ^ p ∂P
      ≤ ∫⁻ ω, (G ω + H ω ^ (2 * p)) ∂P := lintegral_mono_ae hpt
    _ = ∫⁻ ω, G ω ∂P + ∫⁻ ω, H ω ^ (2 * p) ∂P := lintegral_add_left' hGm.aemeasurable _
    _ ≤ M + C₁₂ := add_le_add hGint h12

end StarBound
end GaussianLQG
