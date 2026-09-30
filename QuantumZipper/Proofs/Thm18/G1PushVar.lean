import QuantumZipper.Proofs.Thm18.G1PushVarRad
import QuantumZipper.Proofs.Thm18.G1PathCoordFam

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-PUSHVAR, part 2: the variance modulus of the smoothed pushed-circle family

`pushVarOfRegStmt_holds : PushVarOfRegStmt`: for `ψ` continuous on `Hbar`, `ψ(Hbar) ⊆ Hbar`,
locally Hölder on `Hbar` (`LocHolderHbar`, exponent `α`) and with uniformly `1/3`-Frostman pushed
folded circles (`PushFrostman`), the smoothed family `pushFam ψ` has the Hölder variance modulus
`|kernelCov2 neumannH (μ_p, μ_p') (μ_p, μ_p')| ≤ K_R ‖p − p'‖^β` on each box, with
`β = min(α, 1)/6`.

Argument (the repository's own energy estimates, the Duplantier–Sheffield, Invent. Math. 185
(2011), Prop. 3.1-type argument, as in `RegCont.abs_kernelCov2_bindFc_le`):
* every member `μ_p` (`p = (q, t)`) is `1/3`-Frostman with constant `24 C_R`
  (`RegCont.isFrostman_bindFc`) and supported in `closedBall 0 (B + R)`;
* for such a `κ`, `∫ neuPot κ dμ_p = ∫ fcPot κ t⁺ (Φ_q θ) dθ` (`Φ_q = pushPhi ψ q`; for
  `t ≤ 0` use `fcPot κ 0 = neuPot κ` on `Hbar`), and `fcPot` is jointly `1/6`-Hölder in the
  centre and the radius (`abs_fcPot_sub_le_L`); the same-angle coupling gives
  `‖Φ_q θ − Φ_q' θ‖ ≲ ‖q − q'‖ + ‖q − q'‖^α` from the Hölder bound of `ψ`;
* `kernelCov2 = [∫neuPot μ dμ_p − ∫neuPot μ dμ_p'] − [same with μ_p']`.
Own bookkeeping for the parametrization (no separate source needed).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Metric Set Function Real
open scoped ENNReal NNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G1RC

open CircleFubini KolmD TwoPoint RegCont

/-! ## Elementary estimates -/

theorem abs_exp_sub_exp_le_aux {a b R : ℝ} (ha : a ≤ R) (hba : b ≤ a) :
    |Real.exp a - Real.exp b| ≤ Real.exp R * |a - b| := by
  rw [abs_of_nonneg (sub_nonneg.2 (Real.exp_le_exp.2 hba)), abs_of_nonneg (sub_nonneg.2 hba)]
  have h1 := Real.add_one_le_exp (b - a)
  have e : Real.exp b = Real.exp a * Real.exp (b - a) := by rw [← Real.exp_add]; congr 1; ring
  calc Real.exp a - Real.exp b = Real.exp a * (1 - Real.exp (b - a)) := by rw [e]; ring
    _ ≤ Real.exp a * (a - b) := mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos a).le
    _ ≤ Real.exp R * (a - b) :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ha) (by linarith)

/-- `exp` is `e^R`-Lipschitz on `(-∞, R]` (own elementary proof). -/
theorem abs_exp_sub_exp_le_of_le {a b R : ℝ} (ha : a ≤ R) (hb : b ≤ R) :
    |Real.exp a - Real.exp b| ≤ Real.exp R * |a - b| := by
  rcases le_total b a with h | h
  · exact abs_exp_sub_exp_le_aux ha h
  · rw [abs_sub_comm, abs_sub_comm a b]; exact abs_exp_sub_exp_le_aux hb h

/-- `δ^b ≤ D^{b−a} δ^a` for `0 ≤ δ ≤ D`, `0 < a ≤ b`. -/
theorem rpow_le_bound_mul_rpow {δ D a b : ℝ} (hδ : 0 ≤ δ) (hδD : δ ≤ D) (ha : 0 < a)
    (hab : a ≤ b) : δ ^ b ≤ D ^ (b - a) * δ ^ a := by
  calc δ ^ b = δ ^ a * δ ^ (b - a) := by
        rw [← Real.rpow_add' hδ (by linarith : a + (b - a) ≠ 0)]; congr 1; ring
    _ ≤ δ ^ a * D ^ (b - a) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hδ hδD (by linarith)) (by positivity)
    _ = _ := mul_comm _ _

theorem norm_cenQ_le (q : Fin 4 → ℝ) : ‖cenQ q‖ ≤ |q 0| + |q 1| := by
  unfold cenQ
  refine (norm_add_le _ _).trans (le_of_eq ?_)
  simp

theorem abs_apply_le_norm {n : ℕ} (q : Fin n → ℝ) (i : Fin n) : |q i| ≤ ‖q‖ := by
  rw [← Real.norm_eq_abs]; exact norm_le_pi_norm q i

theorem norm_cenQ_sub_le (q q' : Fin 4 → ℝ) : ‖cenQ q - cenQ q'‖ ≤ 2 * ‖q - q'‖ := by
  have e : cenQ q - cenQ q' = cenQ (q - q') := by simp only [cenQ, Pi.sub_apply]; push_cast; ring
  rw [e]
  refine (norm_cenQ_le _).trans ?_
  linarith [abs_apply_le_norm (q - q') 0, abs_apply_le_norm (q - q') 1]

/-- The centre-radius argument of `pushPhi` on a box. -/
theorem norm_pushArg_le {R : ℕ} {q : Fin 4 → ℝ} (hq : q ∈ boxD (d := 4) R) (θ : ℝ) :
    ‖foldH (circleMap (cenQ q) (Real.exp (q 2)) θ)‖ ≤ 2 * R + Real.exp R := by
  rw [norm_foldH]
  refine (norm_circleMap_le_add _ (Real.exp_pos _).le θ).trans ?_
  have h0 := hq 0
  have h1 := hq 1
  have h2 : Real.exp (q 2) ≤ Real.exp R := Real.exp_le_exp.2 (abs_le.1 (hq 2)).2
  linarith [norm_cenQ_le q]

/-! ## Same-angle displacement of the pushed circles -/

section Disp

variable {ψ : ℂ → ℂ} {R : ℕ} {α CH M : ℝ}

theorem norm_pushPhi_le (hM : ∀ z ∈ Hbar, ‖z‖ ≤ 2 * R + Real.exp R → ‖ψ z‖ ≤ M)
    {q : Fin 4 → ℝ} (hq : q ∈ boxD (d := 4) R) (θ : ℝ) :
    ‖pushPhi ψ q θ‖ ≤ Real.exp R * M := by
  unfold pushPhi
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hM' := hM _ (foldH_mem_Hbar' _) (norm_pushArg_le hq θ)
  have h0 : 0 ≤ M := (norm_nonneg _).trans hM'
  exact mul_le_mul (Real.exp_le_exp.2 (abs_le.1 (hq 3)).2) hM' (norm_nonneg _)
    (Real.exp_pos _).le

theorem norm_pushPhi_sub_le (hCH : 0 ≤ CH)
    (hM : ∀ z ∈ Hbar, ‖z‖ ≤ 2 * R + Real.exp R → ‖ψ z‖ ≤ M)
    (hH : ∀ z ∈ Hbar, ∀ w ∈ Hbar, ‖z‖ ≤ 2 * R + Real.exp R → ‖w‖ ≤ 2 * R + Real.exp R →
      ‖ψ z - ψ w‖ ≤ CH * ‖z - w‖ ^ α) (hα : 0 < α)
    {q q' : Fin 4 → ℝ} (hq : q ∈ boxD (d := 4) R) (hq' : q' ∈ boxD (d := 4) R) (θ : ℝ) :
    ‖pushPhi ψ q θ - pushPhi ψ q' θ‖ ≤
      Real.exp R * M * ‖q - q'‖ + Real.exp R * CH * ((2 + Real.exp R) * ‖q - q'‖) ^ α := by
  set z := foldH (circleMap (cenQ q) (Real.exp (q 2)) θ)
  set z' := foldH (circleMap (cenQ q') (Real.exp (q' 2)) θ)
  set δ := ‖q - q'‖
  have hδ : 0 ≤ δ := norm_nonneg _
  have heR := Real.exp_pos (R : ℝ)
  have hzb := norm_pushArg_le hq θ
  have hzb' := norm_pushArg_le hq' θ
  have hMz := hM z (foldH_mem_Hbar' _) hzb
  have hM0 : 0 ≤ M := (norm_nonneg _).trans hMz
  have hzz : ‖z - z'‖ ≤ (2 + Real.exp R) * δ := by
    refine (norm_foldH_sub_le _ _).trans ((norm_circleMap_sub_le _ _ _ _ θ).trans ?_)
    have h1 := norm_cenQ_sub_le q q'
    have h2 := abs_exp_sub_exp_le_of_le (abs_le.1 (hq 2)).2 (abs_le.1 (hq' 2)).2
    have h3 : |q 2 - q' 2| ≤ δ := by
      have := abs_apply_le_norm (q - q') 2; simpa using this
    nlinarith
  have hψ : ‖ψ z - ψ z'‖ ≤ CH * ((2 + Real.exp R) * δ) ^ α :=
    (hH z (foldH_mem_Hbar' _) z' (foldH_mem_Hbar' _) hzb hzb').trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) hzz hα.le) hCH)
  have hexp : |Real.exp (q 3) - Real.exp (q' 3)| ≤ Real.exp R * δ := by
    refine (abs_exp_sub_exp_le_of_le (abs_le.1 (hq 3)).2 (abs_le.1 (hq' 3)).2).trans ?_
    have := abs_apply_le_norm (q - q') 3
    simp only [Pi.sub_apply] at this
    exact mul_le_mul_of_nonneg_left this heR.le
  have e : pushPhi ψ q θ - pushPhi ψ q' θ =
      ((Real.exp (q 3) - Real.exp (q' 3) : ℝ) : ℂ) * ψ z + (Real.exp (q' 3) : ℂ) * (ψ z - ψ z') := by
    simp only [pushPhi, z, z']; push_cast; ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos (q' 3))]
  have hq3 : Real.exp (q' 3) ≤ Real.exp R := Real.exp_le_exp.2 (abs_le.1 (hq' 3)).2
  have hA : |Real.exp (q 3) - Real.exp (q' 3)| * ‖ψ z‖ ≤ Real.exp R * M * δ := by
    calc _ ≤ (Real.exp R * δ) * M := mul_le_mul hexp hMz (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hB : Real.exp (q' 3) * ‖ψ z - ψ z'‖ ≤ Real.exp R * CH * ((2 + Real.exp R) * δ) ^ α := by
    calc _ ≤ Real.exp R * (CH * ((2 + Real.exp R) * δ) ^ α) :=
          mul_le_mul hq3 hψ (norm_nonneg _) heR.le
      _ = _ := by ring
  linarith

end Disp

/-! ## The potential of a Frostman measure integrated against a member of the family -/

section Pot

variable {ψ : ℂ → ℂ}

end Pot

/-! ## Frostman bound, support and the energy increment of the family -/

section Family

variable {ψ : ℂ → ℂ}

theorem ae_norm_pushFam_le {B L : ℝ} {p : Fin (4 + 1) → ℝ}
    (hΦm : Measurable (pushPhi ψ (Fin.init p))) (hΦb : ∀ θ, ‖pushPhi ψ (Fin.init p) θ‖ ≤ B)
    (hL : 0 ≤ L) (htL : p (Fin.last 4) ≤ L) : ∀ᵐ y ∂pushFam ψ p, ‖y‖ ≤ B + L := by
  have hBμ : ∀ᵐ y ∂(circM.map (pushPhi ψ (Fin.init p))), ‖y‖ ≤ B :=
    (ae_map_iff hΦm.aemeasurable (measurableSet_le measurable_norm measurable_const)).2
      (ae_of_all _ hΦb)
  unfold pushFam smoothFam
  split_ifs with ht
  · exact (ae_norm_bindFc_le ht.le hBμ).mono fun y hy => by linarith
  · exact hBμ.mono fun y hy => by linarith

end Family

/-! ## The variance modulus -/

theorem abs_apply_sub_le_of_boxD {n R : ℕ} {p p' : Fin n → ℝ} (hp : p ∈ boxD (d := n) R)
    (hp' : p' ∈ boxD (d := n) R) : ‖p - p'‖ ≤ 2 * R := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  rw [Pi.sub_apply, Real.norm_eq_abs]
  linarith [abs_sub (p i) (p' i), hp i, hp' i]

theorem norm_init_sub_le {p p' : Fin (4 + 1) → ℝ} :
    ‖Fin.init p - Fin.init p'‖ ≤ ‖p - p'‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => by
    have := norm_le_pi_norm (p - p') (Fin.castSucc i)
    simpa [Fin.init] using this

end G1RC
end Thm18Asm
end QuantumZipper
