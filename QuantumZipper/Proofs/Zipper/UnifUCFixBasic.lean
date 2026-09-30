import QuantumZipper.Proofs.Zipper.UnifUCE2
import QuantumZipper.Proofs.Probability.KolmN

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# UNIF-RC3-FIX (decision D33), step 1: the three-parameter continuous modification

For a fixed Hölder driver `W`, the Gaussian family `(p, ρ) ↦ X(muUS W d k p ρ)` on
`tri T × [0,1]` has a continuous modification. The parameters are extended to all of `ℝ³` by a
`1`-Lipschitz (sup norm) retraction `q ↦ (piT T q, rhoP q)` onto `tri T × [0,1]`
(`piT T q = (u', max 0 (min (q 1) (T − u')))`, `u' = max 0 (min (q 0) T)`,
`rhoP q = max 0 (min (q 2) 1)`), and

* `energyUS_le`: `E(μ_{πq,ρq} − μ_{πq',ρq'}) ≤ K ‖q − q'‖^c` (E1 `energyRadStmt_holds` and E2
  `energyParStmt_holds`, glued by the triangle inequality for the energy through `μ_{πq,ρq'}`);
* `momentBound_US`: the Gaussian moment bound `E|Z q − Z q'|^{2m} ≤ K' ‖q − q'‖^{m c}`
  (`RegCont.lintegral_pow_diff_le`);
* `exists_contMod_US`: `KolmN.exists_continuous_modification_N` with `d = 3`, `m c > 3`.

Sources: Revuz–Yor, *Continuous Martingales and Brownian Motion*, 3rd ed., Ch. I, Thm (2.1)
(multiparameter Kolmogorov–Čentsov); Duplantier–Sheffield, Invent. Math. 185 (2011),
Prop. 3.1. The retraction and the exponent bookkeeping are own elementary steps; the pattern is
`JointModFixed.momentBound_ν4` / `exists_contMod_ν4`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal

namespace QuantumZipper
namespace RegUnif

open RegCont TwoPoint GFFExist B2 KolmD KolmG

variable {W : ℝ → ℝ}

/-- The clamped first time parameter. -/
def uT (T : ℝ) (q : Fin 3 → ℝ) : ℝ := max 0 (min (q 0) T)

/-- The retraction of `ℝ²` (first two coordinates) onto `tri T`. -/
def piT (T : ℝ) (q : Fin 3 → ℝ) : ℝ × ℝ := (uT T q, max 0 (min (q 1) (T - uT T q)))

/-- The clamped radius parameter. -/
def rhoP (q : Fin 3 → ℝ) : ℝ := max 0 (min (q 2) 1)

/-- The embedding of `tri T × [0,1]` into `ℝ³`. -/
def embP (p : ℝ × ℝ) (ρ : ℝ) : Fin 3 → ℝ := ![p.1, p.2, ρ]

theorem piT_mem {T : ℝ} (hT : 0 ≤ T) (q : Fin 3 → ℝ) : piT T q ∈ tri T := by
  have hu0 : 0 ≤ uT T q := le_max_left _ _
  have huT : uT T q ≤ T := max_le hT (min_le_right _ _)
  refine ⟨hu0, le_max_left _ _, ?_⟩
  have : max 0 (min (q 1) (T - uT T q)) ≤ T - uT T q :=
    max_le (by linarith) (min_le_right _ _)
  show uT T q + max 0 (min (q 1) (T - uT T q)) ≤ T
  linarith

theorem rhoP_mem (q : Fin 3 → ℝ) : rhoP q ∈ Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩

theorem piT_embP {T : ℝ} {p : ℝ × ℝ} (hp : p ∈ tri T) (ρ : ℝ) : piT T (embP p ρ) = p := by
  have hu : uT T (embP p ρ) = p.1 := by
    simp only [uT, embP, Matrix.cons_val_zero]
    rw [min_eq_left (by linarith [hp.2.1, hp.2.2]), max_eq_right hp.1]
  unfold piT
  rw [hu]
  simp only [embP, Matrix.cons_val_one, Matrix.cons_val_zero]
  rw [min_eq_left (by linarith [hp.2.2]), max_eq_right hp.2.1]

theorem rhoP_embP (p : ℝ × ℝ) {ρ : ℝ} (hρ : ρ ∈ Icc (0 : ℝ) 1) : rhoP (embP p ρ) = ρ := by
  simp only [rhoP, embP]
  have : (![p.1, p.2, ρ] : Fin 3 → ℝ) 2 = ρ := rfl
  rw [this, min_eq_left hρ.2, max_eq_right hρ.1]

theorem abs_clamp_sub_le (x y A B : ℝ) :
    |max 0 (min x A) - max 0 (min y B)| ≤ max |x - y| |A - B| := by
  refine (abs_max_sub_max_le_max _ _ _ _).trans (max_le ?_ ?_)
  · rw [sub_self, abs_zero]; positivity
  · exact abs_min_sub_min_le_max _ _ _ _

theorem abs_coord_le (q q' : Fin 3 → ℝ) (i : Fin 3) : |q i - q' i| ≤ ‖q - q'‖ := by
  have := norm_le_pi_norm (q - q') i
  rwa [Pi.sub_apply, Real.norm_eq_abs] at this

theorem dist_piT_le (T : ℝ) (q q' : Fin 3 → ℝ) : dist (piT T q) (piT T q') ≤ ‖q - q'‖ := by
  have hu : |uT T q - uT T q'| ≤ ‖q - q'‖ := by
    refine (abs_clamp_sub_le _ _ _ _).trans (max_le (abs_coord_le q q' 0) ?_)
    rw [sub_self, abs_zero]; exact norm_nonneg _
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
  refine max_le hu ((abs_clamp_sub_le _ _ _ _).trans (max_le (abs_coord_le q q' 1) ?_))
  rw [show T - uT T q - (T - uT T q') = -(uT T q - uT T q') by ring, abs_neg]
  exact hu

theorem abs_rhoP_sub_le (q q' : Fin 3 → ℝ) : |rhoP q - rhoP q'| ≤ ‖q - q'‖ := by
  refine (abs_clamp_sub_le _ _ _ _).trans (max_le (abs_coord_le q q' 2) ?_)
  rw [sub_self, abs_zero]; exact norm_nonneg _

/-- `x^e ≤ (1 + (L+1)^e) Δ^c` for `0 ≤ x ≤ Δ`, `x ≤ L`, `0 < c ≤ e`. -/
theorem rpow_le_of_le_both {x Δ L e c : ℝ} (hx : 0 ≤ x) (hxΔ : x ≤ Δ) (hxL : x ≤ L)
    (hc : 0 < c) (hce : c ≤ e) : x ^ e ≤ (1 + (L + 1) ^ e) * Δ ^ c := by
  have hΔ0 : 0 ≤ Δ := hx.trans hxΔ
  have hL1 : 0 ≤ L + 1 := by linarith
  have hLe : 0 ≤ (L + 1) ^ e := Real.rpow_nonneg hL1 _
  have hΔc : 0 ≤ Δ ^ c := Real.rpow_nonneg hΔ0 _
  have he : 0 ≤ e := hc.le.trans hce
  by_cases hΔ1 : Δ ≤ 1
  · have h1 : x ^ e ≤ Δ ^ e := Real.rpow_le_rpow hx hxΔ he
    have h2 : Δ ^ e ≤ Δ ^ c := Real.rpow_le_rpow_of_exponent_ge' hΔ0 hΔ1 hc.le hce
    nlinarith
  · push Not at hΔ1
    have h1 : x ^ e ≤ (L + 1) ^ e := Real.rpow_le_rpow hx (by linarith) he
    have h2 : 1 ≤ Δ ^ c := Real.one_le_rpow hΔ1.le hc.le
    nlinarith

/-- **Energy of increments in the retracted parameters.** -/
theorem energyUS_le (hW : Continuous W) (hW0 : W 0 = 0) {T a CH : ℝ} (hWH : HolderDrv W T a CH)
    (hT : 0 ≤ T) {Mw : ℝ} (hMw : ∀ t ∈ Icc (0 : ℝ) T, |W t| ≤ Mw) (d : ℂ) (k : ℕ) :
    ∃ K c : ℝ, 0 ≤ K ∧ 0 < c ∧ ∀ q q' : Fin 3 → ℝ,
      |kernelCov2 neumannH (muUS W d k (piT T q) (rhoP q), muUS W d k (piT T q') (rhoP q'))
        (muUS W d k (piT T q) (rhoP q), muUS W d k (piT T q') (rhoP q'))| ≤
        K * ‖q - q'‖ ^ c := by
  obtain ⟨C₁, a₁, hC₁, ha₁, hE1⟩ := energyRadStmt_holds T W hW hW0 d k
  obtain ⟨C₂, b, hC₂, hb, hE2⟩ := energyParStmt_holds T W a CH hWH d k
  set c := min (min a₁ b) 1 with hc
  have hc0 : 0 < c := lt_min (lt_min ha₁ hb) one_pos
  have hca : c ≤ a₁ := (min_le_left _ _).trans (min_le_left _ _)
  have hcb : c ≤ b := (min_le_left _ _).trans (min_le_right _ _)
  refine ⟨2 * (C₁ * (1 + (1 + 1) ^ a₁)) + 2 * (C₂ * (1 + (T + 1) ^ b)), c, by positivity, hc0,
    fun q q' => ?_⟩
  set p := piT T q
  set p' := piT T q'
  have hp : p ∈ tri T := piT_mem hT q
  have hp' : p' ∈ tri T := piT_mem hT q'
  obtain ⟨hA, hmA⟩ := admissible_muUS hW hW0 hMw d k hp (rhoP_mem q).1 (rhoP_mem q).2
  obtain ⟨hB, hmB⟩ := admissible_muUS hW hW0 hMw d k hp (rhoP_mem q').1 (rhoP_mem q').2
  obtain ⟨hC, hmC⟩ := admissible_muUS hW hW0 hMw d k hp' (rhoP_mem q').1 (rhoP_mem q').2
  rw [abs_of_nonneg (kernelCov2_self_nonneg hA hC (hmA.trans hmC.symm))]
  have ht := kernelCov2_self_triangle hA hB hC (hmA.trans hmB.symm) (hmB.trans hmC.symm)
  have e1 := (le_abs_self _).trans (hE1 p hp (rhoP q) (rhoP_mem q) (rhoP q') (rhoP_mem q'))
  have e2 := (le_abs_self _).trans (hE2 p hp p' hp' (rhoP q') (rhoP_mem q'))
  have hρL : |rhoP q - rhoP q'| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith [rhoP_mem q, rhoP_mem q', (rhoP_mem q).2,
      (rhoP_mem q').2, (rhoP_mem q).1, (rhoP_mem q').1]
  have hdT : dist p p' ≤ T := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    refine max_le ?_ ?_ <;> rw [abs_le] <;> constructor <;>
      linarith [hp.1, hp.2.1, hp.2.2, hp'.1, hp'.2.1, hp'.2.2]
  have f1 := rpow_le_of_le_both (abs_nonneg _) (abs_rhoP_sub_le q q') hρL hc0 hca
  have f2 := rpow_le_of_le_both dist_nonneg (dist_piT_le T q q') hdT hc0 hcb
  have g1 := mul_le_mul_of_nonneg_left f1 hC₁
  have g2 := mul_le_mul_of_nonneg_left f2 hC₂
  nlinarith

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-- **Continuous modification of `(p, ρ) ↦ X(muUS p ρ)`** (three-parameter Kolmogorov step). -/
theorem exists_contMod_US (hX : IsFreeGFFModConstH X P) {T a CH : ℝ} (hWH : HolderDrv W T a CH)
    (hT : 0 ≤ T) (d : ℂ) (k : ℕ) :
    ∃ Y : (Fin 3 → ℝ) → Ω → ℝ, (∀ ω, Continuous fun q => Y q ω) ∧
      ∀ q, (fun ω => Y q ω) =ᵐ[P] fun ω => X ω (muUS W d k (piT T q) (rhoP q)) := by
  have hWH' := hWH
  obtain ⟨hW, hW0, -, -, -, -⟩ := hWH'
  obtain ⟨Mw, hMw'⟩ := isCompact_Icc.exists_bound_of_continuousOn (hW.continuousOn (s := Icc 0 T))
  have hMw : ∀ t ∈ Icc (0 : ℝ) T, |W t| ≤ Mw := fun t ht => by
    simpa [Real.norm_eq_abs] using hMw' t ht
  obtain ⟨K, c, hK, hc, hE⟩ := energyUS_le hW hW0 hWH hT hMw d k
  set m : ℕ := ⌈3 / c⌉₊ + 1 with hm
  have hm0 : 0 < m := Nat.succ_pos _
  have hmc : ((3 : ℕ) : ℝ) < (m : ℝ) * c := by
    have h1 : 3 / c ≤ (⌈3 / c⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (3 / c) * c = 3 := div_mul_cancel₀ _ hc.ne'
    rw [hm]; push_cast
    nlinarith
  set g := gaussianAbsMoment (2 * m) with hg
  have hg0 : 0 ≤ g := gaussianAbsMoment_nonneg _
  obtain ⟨Y, hY, hYZ, -⟩ := KolmN.exists_continuous_modification_N (d := 3)
    (Z := fun q ω => X ω (muUS W d k (piT T q) (rhoP q))) (P := P)
    (fun q => (hX.measurable_coord _).aemeasurable) (p := 2 * m) (by omega) hmc
    (fun R => ⟨K ^ m * g, by positivity, fun q _ q' _ => by
      obtain ⟨hA, hmA⟩ := admissible_muUS hW hW0 hMw d k (piT_mem hT q) (rhoP_mem q).1
        (rhoP_mem q).2
      obtain ⟨hB, hmB⟩ := admissible_muUS hW hW0 hMw d k (piT_mem hT q') (rhoP_mem q').1
        (rhoP_mem q').2
      refine (lintegral_pow_diff_le hX hA hB (hmA.trans hmB.symm) m (hE q q')).trans ?_
      refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
      rw [mul_pow, ← Real.rpow_natCast (‖q - q'‖ ^ c), ← Real.rpow_mul (norm_nonneg _), hg,
        mul_comm c]
      ring⟩)
  exact ⟨Y, hY, hYZ⟩

end RegUnif
end QuantumZipper
