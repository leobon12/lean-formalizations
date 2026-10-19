import GaussianLQG.Probability.Gaussian
import QuantumZipper.Proofs.Probability.KolmN

/-!
# Kolmogorov–Chentsov on `[0, 1]`

One-parameter wrappers of `QuantumZipper.KolmN.exists_continuous_modification_N`
(Revuz–Yor, Ch. I, Thm (2.1)) for processes indexed by `[0, 1]`:

* `exists_continuous_modification_Icc`: if `E|X_y - X_{y'}|^p ≤ K |y - y'|^a` on `[0, 1]` with an
  integer `p ≥ 1` and `a > 1`, then `X` has a modification `Y` on `[0, 1]` whose paths
  `y ↦ Y y ω` are continuous on `ℝ` for every `ω`;
* `exists_continuous_modification_Icc_of_hasLaw`: the Gaussian case, where it suffices that the
  increments are centered Gaussians with `Var(X_y - X_{y'}) ≤ C |y - y'|^α` for some `α > 0`.

The process is extended to `ℝ` (and to `Fin 1 → ℝ`) through the nearest-point map onto `[0,1]`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace GaussianLQG

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The nearest-point map `Fin 1 → ℝ` onto `[0, 1]`. -/
def clampUnit (q : Fin 1 → ℝ) : ℝ := (projIcc (0 : ℝ) 1 zero_le_one (q 0) : ℝ)

theorem clampUnit_mem (q : Fin 1 → ℝ) : clampUnit q ∈ Icc (0 : ℝ) 1 :=
  (projIcc (0 : ℝ) 1 zero_le_one (q 0)).2

theorem abs_clampUnit_sub_le (q q' : Fin 1 → ℝ) : |clampUnit q - clampUnit q'| ≤ ‖q - q'‖ := by
  refine (abs_projIcc_sub_projIcc zero_le_one).trans ?_
  have h := norm_le_pi_norm (q - q') 0
  rwa [Pi.sub_apply, Real.norm_eq_abs] at h

theorem clampUnit_const {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) : clampUnit (fun _ => y) = y := by
  simp [clampUnit, projIcc_of_mem _ hy]

/-- **Kolmogorov–Chentsov on `[0, 1]`**: if `E|X_y - X_{y'}|^p ≤ K |y - y'|^a` for `y, y' ∈ [0,1]`,
with an integer `p ≥ 1` and `a > 1`, then `X` has a modification on `[0, 1]` with continuous
paths. -/
theorem exists_continuous_modification_Icc {X : ℝ → Ω → ℝ}
    (hX : ∀ y ∈ Icc (0 : ℝ) 1, AEMeasurable (X y) P) {p : ℕ} (hp : 0 < p) {a K : ℝ}
    (ha : 1 < a) (hK : 0 ≤ K)
    (hmom : ∀ y ∈ Icc (0 : ℝ) 1, ∀ y' ∈ Icc (0 : ℝ) 1,
      ∫⁻ ω, ENNReal.ofReal (|X y ω - X y' ω| ^ p) ∂P ≤ ENNReal.ofReal (K * |y - y'| ^ a)) :
    ∃ Y : ℝ → Ω → ℝ, (∀ ω, Continuous fun y => Y y ω) ∧
      ∀ y ∈ Icc (0 : ℝ) 1, Y y =ᵐ[P] X y := by
  set Z : (Fin 1 → ℝ) → Ω → ℝ := fun q => X (clampUnit q)
  have hZ : ∀ q, AEMeasurable (Z q) P := fun q => hX _ (clampUnit_mem q)
  have hmom' : ∀ R : ℕ, ∃ K', 0 ≤ K' ∧ QuantumZipper.KolmG.MomentBoundG Z P p a K' R := by
    intro R
    refine ⟨K, hK, fun q _ q' _ => (hmom _ (clampUnit_mem q) _ (clampUnit_mem q')).trans
      (ENNReal.ofReal_le_ofReal ?_)⟩
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (abs_nonneg _) (abs_clampUnit_sub_le q q')
      (by linarith)) hK
  obtain ⟨Y, hYc, hYZ, -⟩ := QuantumZipper.KolmN.exists_continuous_modification_N hZ hp
    (by norm_num; exact ha) hmom'
  refine ⟨fun y ω => Y (fun _ => y) ω, fun ω => (hYc ω).comp (continuous_pi fun _ =>
    continuous_id), fun y hy => ?_⟩
  have h := hYZ (fun _ => y)
  simp only [Z, clampUnit_const hy] at h
  exact h

/-- **Kolmogorov–Chentsov on `[0, 1]`, Gaussian case**: if the increments `X_y - X_{y'}`
(`y, y' ∈ [0, 1]`) are centered Gaussians with variance at most `C |y - y'|^α`, `α > 0`, then `X`
has a modification on `[0, 1]` with continuous paths. -/
theorem exists_continuous_modification_Icc_of_hasLaw {X : ℝ → Ω → ℝ} {C α : ℝ} (hC : 0 ≤ C)
    (hα : 0 < α) (hX : ∀ y ∈ Icc (0 : ℝ) 1, AEMeasurable (X y) P)
    (hinc : ∀ y ∈ Icc (0 : ℝ) 1, ∀ y' ∈ Icc (0 : ℝ) 1, ∃ v : ℝ≥0,
      (v : ℝ) ≤ C * |y - y'| ^ α ∧ HasLaw (fun ω => X y ω - X y' ω) (gaussianReal 0 v) P) :
    ∃ Y : ℝ → Ω → ℝ, (∀ ω, Continuous fun y => Y y ω) ∧
      ∀ y ∈ Icc (0 : ℝ) 1, Y y =ᵐ[P] X y := by
  set m : ℕ := ⌊1 / α⌋₊ + 1 with hm
  have hm1 : 1 / α < m := by
    rw [hm]; push_cast; exact Nat.lt_floor_add_one _
  have hm0 : (0 : ℝ) < m := lt_of_le_of_lt (by positivity) hm1
  set M : ℝ := ∫ x, |x| ^ ((2 * m : ℕ) : ℝ) ∂gaussianReal 0 1 with hM
  have hM0 : 0 ≤ M := integral_nonneg fun x => Real.rpow_nonneg (abs_nonneg x) _
  have hn2 : (((2 * m : ℕ) : ℝ) / 2) = m := by push_cast; ring
  refine exists_continuous_modification_Icc hX (p := 2 * m) (by omega) (a := α * m)
    (K := C ^ (m : ℝ) * M) ?_ (by positivity) fun y hy y' hy' => ?_
  · have := (div_lt_iff₀ hα).1 hm1
    linarith
  obtain ⟨v, hv, hlaw⟩ := hinc y hy y' hy'
  rw [lintegral_abs_pow_of_hasLaw_gaussianReal hlaw, hn2]
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 : (v : ℝ) ^ (m : ℝ) ≤ (C * |y - y'| ^ α) ^ (m : ℝ) :=
    Real.rpow_le_rpow v.coe_nonneg hv hm0.le
  rw [Real.mul_rpow hC (Real.rpow_nonneg (abs_nonneg _) _), ← Real.rpow_mul (abs_nonneg _)]
    at h1
  calc (v : ℝ) ^ (m : ℝ) * M ≤ C ^ (m : ℝ) * |y - y'| ^ (α * m) * M :=
        mul_le_mul_of_nonneg_right h1 hM0
    _ = C ^ (m : ℝ) * M * |y - y'| ^ (α * m) := by ring

/-! ## Two parameters -/

/-- The nearest-point map `Fin 2 → ℝ` onto `[0, 1]²`. -/
def clampUnit2 (q : Fin 2 → ℝ) : ℝ × ℝ :=
  ((projIcc (0 : ℝ) 1 zero_le_one (q 0) : ℝ), (projIcc (0 : ℝ) 1 zero_le_one (q 1) : ℝ))

theorem clampUnit2_fst_mem (q : Fin 2 → ℝ) : (clampUnit2 q).1 ∈ Icc (0 : ℝ) 1 :=
  (projIcc (0 : ℝ) 1 zero_le_one (q 0)).2

theorem clampUnit2_snd_mem (q : Fin 2 → ℝ) : (clampUnit2 q).2 ∈ Icc (0 : ℝ) 1 :=
  (projIcc (0 : ℝ) 1 zero_le_one (q 1)).2

theorem max_abs_clampUnit2_sub_le (q q' : Fin 2 → ℝ) :
    max |(clampUnit2 q).1 - (clampUnit2 q').1| |(clampUnit2 q).2 - (clampUnit2 q').2| ≤
      ‖q - q'‖ := by
  refine max_le ((abs_projIcc_sub_projIcc zero_le_one).trans ?_)
    ((abs_projIcc_sub_projIcc zero_le_one).trans ?_)
  · have h := norm_le_pi_norm (q - q') 0
    rwa [Pi.sub_apply, Real.norm_eq_abs] at h
  · have h := norm_le_pi_norm (q - q') 1
    rwa [Pi.sub_apply, Real.norm_eq_abs] at h

theorem clampUnit2_mk {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    clampUnit2 ![s, t] = (s, t) := by
  simp [clampUnit2, projIcc_of_mem _ hs, projIcc_of_mem _ ht]

/-- **Kolmogorov–Chentsov on `[0, 1]²`, Gaussian case**: if the increments of `X` on `[0,1]²` are
centered Gaussians with variance at most `C (|s - s'| ∨ |t - t'|)^α`, `α > 0`, then `X` has a
modification on `[0, 1]²` with jointly continuous paths. -/
theorem exists_continuous_modification_Icc2_of_hasLaw {X : ℝ → ℝ → Ω → ℝ} {C α : ℝ}
    (hC : 0 ≤ C) (hα : 0 < α)
    (hX : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, AEMeasurable (X s t) P)
    (hinc : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, ∀ s' ∈ Icc (0 : ℝ) 1,
      ∀ t' ∈ Icc (0 : ℝ) 1, ∃ v : ℝ≥0, (v : ℝ) ≤ C * (max |s - s'| |t - t'|) ^ α ∧
        HasLaw (fun ω => X s t ω - X s' t' ω) (gaussianReal 0 v) P) :
    ∃ Y : ℝ → ℝ → Ω → ℝ, (∀ ω, Continuous fun p : ℝ × ℝ => Y p.1 p.2 ω) ∧
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, Y s t =ᵐ[P] X s t := by
  set m : ℕ := ⌊2 / α⌋₊ + 1 with hm
  have hm1 : 2 / α < m := by
    rw [hm]; push_cast; exact Nat.lt_floor_add_one _
  have hm0 : (0 : ℝ) < m := lt_of_le_of_lt (by positivity) hm1
  set M : ℝ := ∫ x, |x| ^ ((2 * m : ℕ) : ℝ) ∂gaussianReal 0 1 with hM
  have hM0 : 0 ≤ M := integral_nonneg fun x => Real.rpow_nonneg (abs_nonneg x) _
  have hn2 : (((2 * m : ℕ) : ℝ) / 2) = m := by push_cast; ring
  set Z : (Fin 2 → ℝ) → Ω → ℝ := fun q => X (clampUnit2 q).1 (clampUnit2 q).2
  have hZ : ∀ q, AEMeasurable (Z q) P := fun q =>
    hX _ (clampUnit2_fst_mem q) _ (clampUnit2_snd_mem q)
  have ha : ((2 : ℕ) : ℝ) < α * m := by
    have := (div_lt_iff₀ hα).1 hm1
    push_cast
    linarith
  have hmom : ∀ R : ℕ, ∃ K', 0 ≤ K' ∧
      QuantumZipper.KolmG.MomentBoundG Z P (2 * m) (α * m) K' R := by
    intro R
    refine ⟨C ^ (m : ℝ) * M, by positivity, fun q _ q' _ => ?_⟩
    obtain ⟨v, hv, hlaw⟩ := hinc _ (clampUnit2_fst_mem q) _ (clampUnit2_snd_mem q) _
      (clampUnit2_fst_mem q') _ (clampUnit2_snd_mem q')
    rw [lintegral_abs_pow_of_hasLaw_gaussianReal hlaw, hn2]
    refine ENNReal.ofReal_le_ofReal ?_
    have hv' : (v : ℝ) ≤ C * ‖q - q'‖ ^ α :=
      hv.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (le_max_of_le_left (abs_nonneg _))
        (max_abs_clampUnit2_sub_le q q') hα.le) hC)
    have h1 : (v : ℝ) ^ (m : ℝ) ≤ (C * ‖q - q'‖ ^ α) ^ (m : ℝ) :=
      Real.rpow_le_rpow v.coe_nonneg hv' hm0.le
    rw [Real.mul_rpow hC (Real.rpow_nonneg (norm_nonneg _) _), ← Real.rpow_mul (norm_nonneg _)]
      at h1
    calc (v : ℝ) ^ (m : ℝ) * M ≤ C ^ (m : ℝ) * ‖q - q'‖ ^ (α * m) * M :=
          mul_le_mul_of_nonneg_right h1 hM0
      _ = C ^ (m : ℝ) * M * ‖q - q'‖ ^ (α * m) := by ring
  obtain ⟨Y, hYc, hYZ, -⟩ := QuantumZipper.KolmN.exists_continuous_modification_N hZ
    (p := 2 * m) (by omega) ha hmom
  refine ⟨fun s t ω => Y ![s, t] ω, fun ω => (hYc ω).comp ?_, fun s hs t ht => ?_⟩
  · refine continuous_pi fun i => ?_
    fin_cases i
    · exact continuous_fst
    · exact continuous_snd
  · have h := hYZ ![s, t]
    simp only [Z, clampUnit2_mk hs ht] at h
    exact h

end GaussianLQG
