import HigherDimLFPP.Field.BandsGraph
import HigherDimLFPP.Field.BandsMax
import HigherDimLFPP.Var.EnergyBall
import HigherDimLFPP.Var.Scaling
import LQGDimension.Gaussian.SudakovFernique

/-!
# Lemma 3.4(b): the expected supremum over an energy ball, and the `H⁻¹` lemma (packet P-F3b)

Source: `source/higher-dimensional-lfpp-limit.pdf`, §3.3, Lemma 3.4(b), second sentence; planning
audit HA2 (`planning/audits/HA2-section-3.md`), finding HA2-13 and Details D8(b) ("(b),
supremum"); HA4 (`planning/audits/HA4-section-5.md`), D5 step 3 (the consumer: the coarse-scale
error of Lemma 5.2, for a finite family `{g_j}` of energy `≤ E₀`).

**Statement** (`bandLemma34b_sup`; HA2's `Lemma34b`, second part, in the lattice convention).
There is `C = C(m, κ)` such that for all `δ, L > 0`, every `n`, `E₀` and every finite family
`F ⊆ V_n(ℝ^m)` of energy `≤ E₀`, the centered Gaussian family
`X(f) = δ^{-1/2} ⟨H_{δL,∞}, μ_{δf} - μ_0⟩` satisfies `E max_{f ∈ F} |X(f)| ≤ C √(E₀ / L)`
(`E max |X|` is the expected maximum of the sign-doubled family `(± X(f))`, `Bands.signK`).
`bandLemma34b` is the conjunction with (3.13), exactly HA2's `Lemma34b` (with `V m n` the frozen
`Vg (Rd m) n`); `bandLemma34b_explicit` gives one constant `C_b` with (3.13) and
`E max_F |X| ≤ 2 √(C_b m E₀ / L)` (the packet's form); `bandLemma34b_sup_wn` is the bound for the
pairings `W(bandVecM …)` of an actual white noise.

**Proof** (HA2 D8(b), with a finite-dimensional proof of the `H⁻¹` lemma).

* Comparison process: `Y(f) = σ ⟨f, Z⟩_{L²}` with `σ² = C_b / L`, `C_b` the constant of (3.13).
  By (3.13), `E(X(f) - X(g))² ≤ σ² ‖f - g‖²_{L²} = E(Y(f) - Y(g))²` on `F₀ = F ∪ {0}`, so
  Sudakov–Fernique (`LQGDimension.sudakovFernique`) gives `E max_{F₀} X ≤ E max_{F₀} Y`; the same
  holds for `-X`, and `max_F |X| ≤ max_{F₀} X + max_{F₀} (-X)` since `X(0) = 0`.
* **`H⁻¹` lemma** (`Bands.gEM_L2_le_sqrt`): `E max_{f ∈ F₀} ⟨f, Z⟩_{L²} ≤ √(2 m E₀)` for a finite
  family of `V_n(ℝ^m)` of energy `≤ E₀` and `Z` standard Gaussian on a finite-dimensional
  subspace of `L²([0,1]; ℝ^m)`.  Instead of the Volterra operator and Bessel's inequality, we use
  the **ramp decomposition** `f = Σ_k 2ⁿ w_k Δ_k f` on `[0,1]` (`Bands.Vg_eq_sum_ramp`), where
  `w_k(u) = clamp(u - k 2⁻ⁿ, 0, 2⁻ⁿ)` and `Δ_k f = f((k+1)2⁻ⁿ) - f(k 2⁻ⁿ)`.  Then
  `⟨f, z⟩ = Σ_{k,j} 2ⁿ (Δ_k f)_j ⟨w_k e_j, z⟩` (`Bands.inner_toL2I_eq_sum`), and the termwise
  inequality `|ab| ≤ α a² + b²/(4α)` together with `E(f) = 2ⁿ⁻¹ Σ_k |Δ_k f|²` gives
  `|⟨f, z⟩| ≤ 2λ E(f) + (2ⁿ / 4λ) Σ_{k,j} ⟨w_k e_j, z⟩²` for every `λ > 0`
  (`Bands.abs_inner_toL2I_le`).  The right side is affine in `E(f)` and its expectation is
  `2λE₀ + (2ⁿ/4λ) Σ_{k,j} ‖w_k e_j‖² ≤ 2λ E₀ + m/(4λ)`, since `‖w_k e_j‖² ≤ 4⁻ⁿ`; optimizing in
  `λ` gives `√(2 m E₀)`.  (HA2's Volterra/Bessel route gives `√(m E₀)`; only the constant
  differs.)  The Gaussian `Z` lives on the span of the `f ∈ F₀` and of the `w_k e_j`, so no
  orthogonal projection is needed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter
open scoped RealInnerProductSpace ENNReal

namespace HigherDimLFPP

namespace Bands

/-! ### Ramps and the ramp decomposition of `V_n` profiles -/

/-- The ramp `w_k(u) = clamp(u - k 2⁻ⁿ, 0, 2⁻ⁿ)`: the length of `[0, u] ∩ [k 2⁻ⁿ, (k+1) 2⁻ⁿ]`. -/
def ramp (n k : ℕ) (u : ℝ) : ℝ := max 0 (min (u - (k : ℝ) / 2 ^ n) (1 / 2 ^ n))

theorem ramp_nonneg (n k : ℕ) (u : ℝ) : 0 ≤ ramp n k u := le_max_left _ _

theorem ramp_le (n k : ℕ) (u : ℝ) : ramp n k u ≤ 1 / 2 ^ n :=
  max_le (by positivity) (min_le_right _ _)

theorem continuous_ramp (n k : ℕ) : Continuous (ramp n k) := by
  unfold ramp
  fun_prop

theorem ramp_of_succ_le {n k : ℕ} {u : ℝ} (h : ((k : ℝ) + 1) / 2 ^ n ≤ u) :
    ramp n k u = 1 / 2 ^ n := by
  unfold ramp
  have e : ((k : ℝ) + 1) / 2 ^ n = (k : ℝ) / 2 ^ n + 1 / 2 ^ n := by ring
  have h1 : 1 / 2 ^ n ≤ u - (k : ℝ) / 2 ^ n := by linarith
  rw [min_eq_right h1, max_eq_right (by positivity)]

theorem ramp_of_le {n k : ℕ} {u : ℝ} (h : u ≤ (k : ℝ) / 2 ^ n) : ramp n k u = 0 := by
  unfold ramp
  have h1 : u - (k : ℝ) / 2 ^ n ≤ 0 := by linarith
  exact max_eq_left ((min_le_left _ _).trans h1)

theorem ramp_of_mem {n k : ℕ} {u : ℝ}
    (h : u ∈ Icc ((k : ℝ) / 2 ^ n) (((k : ℝ) + 1) / 2 ^ n)) :
    ramp n k u = u - (k : ℝ) / 2 ^ n := by
  unfold ramp
  have e : ((k : ℝ) + 1) / 2 ^ n = (k : ℝ) / 2 ^ n + 1 / 2 ^ n := by ring
  have h0 : 0 ≤ u - (k : ℝ) / 2 ^ n := by linarith [h.1]
  have h1 : u - (k : ℝ) / 2 ^ n ≤ 1 / 2 ^ n := by linarith [h.2]
  rw [min_eq_left h1, max_eq_right h0]

/-- **Ramp decomposition**: for `f ∈ V_n(E)` and `u ∈ [0,1]`,
`f(u) = Σ_{k < 2ⁿ} (2ⁿ w_k(u)) • (f((k+1) 2⁻ⁿ) - f(k 2⁻ⁿ))`. -/
theorem Vg_eq_sum_ramp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
    {f : ℝ → E} (hf : f ∈ Vg E n) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    f u = ∑ k ∈ Finset.range (2 ^ n),
      ((2 : ℝ) ^ n * ramp n k u) • (f (((k : ℝ) + 1) / 2 ^ n) - f ((k : ℝ) / 2 ^ n)) := by
  obtain ⟨K, hK, huK⟩ := Var.exists_dyadic_piece n hu
  have hN : (0 : ℝ) < 2 ^ n := by positivity
  set t : ℕ → E := fun k =>
    ((2 : ℝ) ^ n * ramp n k u) • (f (((k : ℝ) + 1) / 2 ^ n) - f ((k : ℝ) / 2 ^ n)) with ht
  rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive t (Nat.zero_le K) hK.le,
    Finset.sum_eq_sum_Ico_succ_bot hK t]
  have h1 : ∑ k ∈ Finset.Ico 0 K, t k = f ((K : ℝ) / 2 ^ n) := by
    have hc : ∀ k ∈ Finset.Ico 0 K, t k = f (((k : ℝ) + 1) / 2 ^ n) - f ((k : ℝ) / 2 ^ n) := by
      intro k hk
      rw [Finset.mem_Ico] at hk
      have hle : ((k : ℝ) + 1) / 2 ^ n ≤ u := by
        have hk1 : (k : ℝ) + 1 ≤ K := by exact_mod_cast hk.2
        calc ((k : ℝ) + 1) / 2 ^ n ≤ (K : ℝ) / 2 ^ n := by gcongr
          _ ≤ u := huK.1
      simp only [ht, ramp_of_succ_le hle, mul_one_div_cancel hN.ne', one_smul]
    rw [Finset.sum_congr rfl hc, ← Finset.range_eq_Ico]
    have htel := Finset.sum_range_sub (fun k : ℕ => f ((k : ℝ) / 2 ^ n)) K
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_div, hf.1, sub_zero] at htel
    exact htel
  have h2 : ∑ k ∈ Finset.Ico (K + 1) (2 ^ n), t k = 0 := by
    refine Finset.sum_eq_zero fun k hk => ?_
    rw [Finset.mem_Ico] at hk
    have hle : u ≤ (k : ℝ) / 2 ^ n := by
      have hk1 : (K : ℝ) + 1 ≤ k := by exact_mod_cast hk.1
      calc u ≤ ((K : ℝ) + 1) / 2 ^ n := huK.2
        _ ≤ (k : ℝ) / 2 ^ n := by gcongr
    simp only [ht, ramp_of_le hle, mul_zero, zero_smul]
  have h3 : t K = ((2 : ℝ) ^ n * u - K) •
      (f (((K : ℝ) + 1) / 2 ^ n) - f ((K : ℝ) / 2 ^ n)) := by
    simp only [ht, ramp_of_mem huK]
    congr 1
    field_simp
  rw [h1, h2, h3, add_zero, Var.Vg_piece hf hK huK]

/-! ### `L²([0,1]; ℝ^m)` -/

variable {m : ℕ}

/-- `L²([0,1]; ℝ^m)` (for Lebesgue measure on `[0,1]`). -/
abbrev L2I (m : ℕ) : Type := Lp (Rd m) 2 (volume.restrict (Icc (0 : ℝ) 1))

/-- The class of `f` in `L²([0,1]; ℝ^m)` (junk `0` if `f` is not square integrable). -/
def toL2I (f : ℝ → Rd m) : L2I m := by
  classical
  exact if h : MemLp f 2 (volume.restrict (Icc (0 : ℝ) 1)) then h.toLp f else 0

theorem toL2I_eq {f : ℝ → Rd m} (h : MemLp f 2 (volume.restrict (Icc (0 : ℝ) 1))) :
    toL2I f = h.toLp f := by
  rw [toL2I, dite_eq_left h]

theorem coeFn_toL2I {f : ℝ → Rd m} (h : MemLp f 2 (volume.restrict (Icc (0 : ℝ) 1))) :
    (toL2I f : ℝ → Rd m) =ᵐ[volume.restrict (Icc (0 : ℝ) 1)] f := by
  rw [toL2I_eq h]
  exact MemLp.coeFn_toLp h

theorem memLp_of_continuous_of_bound {f : ℝ → Rd m} (hf : Continuous f) {M : ℝ}
    (hM : ∀ x, ‖f x‖ ≤ M) : MemLp f 2 (volume.restrict (Icc (0 : ℝ) 1)) :=
  MemLp.of_bound hf.aestronglyMeasurable M (Eventually.of_forall hM)

/-- Profiles of `V_n(ℝ^m)` are square integrable on `[0,1]`. -/
theorem memLp_of_Vg {n : ℕ} {f : ℝ → Rd m} (hf : f ∈ Vg (Rd m) n) :
    MemLp f 2 (volume.restrict (Icc (0 : ℝ) 1)) :=
  memLp_of_continuous_of_bound (Var.Vg_continuous hf) (Var.norm_le_sqrt_energy hf)

theorem inner_toL2I_left {f : ℝ → Rd m} (hf : MemLp f 2 (volume.restrict (Icc (0 : ℝ) 1)))
    (z : L2I m) :
    ⟪toL2I f, z⟫ = ∫ u, ⟪f u, (z : ℝ → Rd m) u⟫ ∂(volume.restrict (Icc (0 : ℝ) 1)) := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_toL2I hf] with u hu
  rw [hu]

theorem inner_toL2I {f g : ℝ → Rd m} (hf : MemLp f 2 (volume.restrict (Icc (0 : ℝ) 1)))
    (hg : MemLp g 2 (volume.restrict (Icc (0 : ℝ) 1))) :
    ⟪toL2I f, toL2I g⟫ = ∫ u in Icc (0 : ℝ) 1, ⟪f u, g u⟫ := by
  rw [inner_toL2I_left hf]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_toL2I hg] with u hu
  rw [hu]

/-- The ramp vectors `w_k e_j ∈ L²([0,1]; ℝ^m)`. -/
def rampVec (n k : ℕ) (j : Fin m) : L2I m :=
  toL2I fun u => ramp n k u • EuclideanSpace.single j (1 : ℝ)

theorem memLp_ramp (n k : ℕ) (j : Fin m) :
    MemLp (fun u => ramp n k u • EuclideanSpace.single j (1 : ℝ)) 2
      (volume.restrict (Icc (0 : ℝ) 1)) := by
  refine memLp_of_continuous_of_bound ((continuous_ramp n k).smul continuous_const)
    (M := 1 / 2 ^ n) fun u => ?_
  rw [norm_smul, PiLp.norm_single, norm_one, mul_one,
    Real.norm_of_nonneg (ramp_nonneg n k u)]
  exact ramp_le n k u

/-- `⟨w_k e_j, z⟩ = ∫₀¹ w_k(u) z_j(u) du`. -/
theorem inner_rampVec (n k : ℕ) (j : Fin m) (z : L2I m) :
    ⟪rampVec n k j, z⟫ =
      ∫ u, ramp n k u * ((z : ℝ → Rd m) u).ofLp j ∂(volume.restrict (Icc (0 : ℝ) 1)) := by
  rw [rampVec, inner_toL2I_left (memLp_ramp n k j)]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only [real_inner_smul_left, EuclideanSpace.inner_single_left, map_one, one_mul]

/-- `‖w_k e_j‖² ≤ 4⁻ⁿ`. -/
theorem norm_rampVec_sq_le (n k : ℕ) (j : Fin m) : ‖rampVec n k j‖ ^ 2 ≤ (1 / 2 ^ n) ^ 2 := by
  have := isProbabilityMeasure_volume_Icc
  rw [← real_inner_self_eq_norm_sq, rampVec, inner_toL2I (memLp_ramp n k j) (memLp_ramp n k j)]
  have hpt : ∀ u, ⟪ramp n k u • EuclideanSpace.single j (1 : ℝ),
      ramp n k u • EuclideanSpace.single j (1 : ℝ)⟫ ≤ (1 / 2 ^ n) ^ 2 := by
    intro u
    rw [real_inner_self_eq_norm_sq, norm_smul, PiLp.norm_single, norm_one, mul_one,
      Real.norm_of_nonneg (ramp_nonneg n k u)]
    exact pow_le_pow_left₀ (ramp_nonneg n k u) (ramp_le n k u) 2
  calc ∫ u in Icc (0 : ℝ) 1, ⟪ramp n k u • EuclideanSpace.single j (1 : ℝ),
        ramp n k u • EuclideanSpace.single j (1 : ℝ)⟫
      ≤ ∫ _u in Icc (0 : ℝ) 1, (1 / 2 ^ n : ℝ) ^ 2 := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun u => real_inner_self_nonneg)
          (integrable_const _) (Eventually.of_forall hpt)
    _ = (1 / 2 ^ n) ^ 2 := by rw [integral_const, probReal_univ, one_smul]

/-- Integrability of `u ↦ w_k(u) z_j(u)` for `z ∈ L²`. -/
theorem integrable_ramp_mul (n k : ℕ) (j : Fin m) (z : L2I m) :
    Integrable (fun u => ramp n k u * ((z : ℝ → Rd m) u).ofLp j)
      (volume.restrict (Icc (0 : ℝ) 1)) := by
  have hz : Integrable (z : ℝ → Rd m) (volume.restrict (Icc (0 : ℝ) 1)) :=
    (Lp.memLp z).integrable one_le_two
  have hzj : Integrable (fun u => ((z : ℝ → Rd m) u).ofLp j)
      (volume.restrict (Icc (0 : ℝ) 1)) := by
    exact (EuclideanSpace.proj j : StrongDual ℝ (Rd m)).integrable_comp hz
  refine hzj.bdd_mul (c := 1 / 2 ^ n) (continuous_ramp n k).aestronglyMeasurable
    (Eventually.of_forall fun u => ?_)
  rw [Real.norm_of_nonneg (ramp_nonneg n k u)]
  exact ramp_le n k u

/-- **The `L²` pairing in ramp coordinates**: for `f ∈ V_n(ℝ^m)` and `z ∈ L²([0,1]; ℝ^m)`,
`⟨f, z⟩ = Σ_{k < 2ⁿ} Σ_j 2ⁿ (Δ_k f)_j ⟨w_k e_j, z⟩`. -/
theorem inner_toL2I_eq_sum {n : ℕ} {f : ℝ → Rd m} (hf : f ∈ Vg (Rd m) n) (z : L2I m) :
    ⟪toL2I f, z⟫ = ∑ k ∈ Finset.range (2 ^ n), ∑ j : Fin m,
      (2 ^ n * (f (((k : ℝ) + 1) / 2 ^ n) - f ((k : ℝ) / 2 ^ n)).ofLp j) * ⟪rampVec n k j, z⟫ := by
  set c : ℕ → Fin m → ℝ := fun k j =>
    2 ^ n * (f (((k : ℝ) + 1) / 2 ^ n) - f ((k : ℝ) / 2 ^ n)).ofLp j with hc
  have hi : ∀ k j, Integrable (fun u => c k j * (ramp n k u * ((z : ℝ → Rd m) u).ofLp j))
      (volume.restrict (Icc (0 : ℝ) 1)) := fun k j => (integrable_ramp_mul n k j z).const_mul _
  rw [inner_toL2I_left (memLp_of_Vg hf)]
  calc ∫ u, ⟪f u, (z : ℝ → Rd m) u⟫ ∂(volume.restrict (Icc (0 : ℝ) 1))
      = ∫ u, ∑ k ∈ Finset.range (2 ^ n), ∑ j : Fin m,
          c k j * (ramp n k u * ((z : ℝ → Rd m) u).ofLp j) ∂(volume.restrict (Icc (0 : ℝ) 1)) := by
        refine integral_congr_ae ?_
        filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
        rw [Vg_eq_sum_ramp hf hu, sum_inner]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [real_inner_smul_left, PiLp.inner_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [hc, RCLike.inner_apply, conj_trivial]
        ring
    _ = ∑ k ∈ Finset.range (2 ^ n), ∫ u, ∑ j : Fin m,
          c k j * (ramp n k u * ((z : ℝ → Rd m) u).ofLp j) ∂(volume.restrict (Icc (0 : ℝ) 1)) :=
        integral_finsetSum _ fun k _ => integrable_finsetSum _ fun j _ => hi k j
    _ = ∑ k ∈ Finset.range (2 ^ n), ∑ j : Fin m, ∫ u,
          c k j * (ramp n k u * ((z : ℝ → Rd m) u).ofLp j) ∂(volume.restrict (Icc (0 : ℝ) 1)) :=
        Finset.sum_congr rfl fun k _ => integral_finsetSum _ fun j _ => hi k j
    _ = _ := by
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
        rw [integral_const_mul, inner_rampVec]

/-- **The deterministic `H⁻¹` bound**: for `f ∈ V_n(ℝ^m)`, `z ∈ L²([0,1]; ℝ^m)` and `λ > 0`,
`|⟨f, z⟩| ≤ 2λ E(f) + (2ⁿ / 4λ) Σ_{k,j} ⟨w_k e_j, z⟩²`. -/
theorem abs_inner_toL2I_le {n : ℕ} {f : ℝ → Rd m} (hf : f ∈ Vg (Rd m) n) (z : L2I m) {l : ℝ}
    (hl : 0 < l) :
    |⟪toL2I f, z⟫| ≤ 2 * l * energy f + 2 ^ n / (4 * l) *
      ∑ k ∈ Finset.range (2 ^ n), ∑ j : Fin m, ⟪rampVec n k j, z⟫ ^ 2 := by
  have hN : (0 : ℝ) < 2 ^ n := by positivity
  set α : ℝ := l / 2 ^ n with hα
  have hα0 : 0 < α := div_pos hl hN
  have amgm : ∀ c a : ℝ, |c * a| ≤ α * c ^ 2 + a ^ 2 / (4 * α) := by
    intro c a
    rw [abs_mul]
    have h4 : 0 < 4 * α := by positivity
    have e : α * c ^ 2 + a ^ 2 / (4 * α) - |c| * |a| = (2 * α * |c| - |a|) ^ 2 / (4 * α) := by
      field_simp
      rw [← sq_abs c, ← sq_abs a]
      ring
    have : 0 ≤ (2 * α * |c| - |a|) ^ 2 / (4 * α) := div_nonneg (sq_nonneg _) h4.le
    linarith
  set Δ : ℕ → Rd m := fun k => f (((k : ℝ) + 1) / 2 ^ n) - f ((k : ℝ) / 2 ^ n) with hΔ
  have hsq : ∀ k, ∑ j : Fin m, (2 ^ n * (Δ k).ofLp j) ^ 2 = (2 ^ n) ^ 2 * ‖Δ k‖ ^ 2 := by
    intro k
    rw [EuclideanSpace.norm_sq_eq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Real.norm_eq_abs, sq_abs]
    ring
  have hE := Var.Vg_energy hf
  rw [inner_toL2I_eq_sum hf z]
  calc |∑ k ∈ Finset.range (2 ^ n), ∑ j : Fin m, 2 ^ n * (Δ k).ofLp j * ⟪rampVec n k j, z⟫|
      ≤ ∑ k ∈ Finset.range (2 ^ n), ∑ j : Fin m, |2 ^ n * (Δ k).ofLp j * ⟪rampVec n k j, z⟫| :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ =>
          Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ k ∈ Finset.range (2 ^ n), ∑ j : Fin m,
          (α * (2 ^ n * (Δ k).ofLp j) ^ 2 + ⟪rampVec n k j, z⟫ ^ 2 / (4 * α)) :=
        Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun j _ => amgm _ _
    _ = α * ∑ k ∈ Finset.range (2 ^ n), (2 ^ n) ^ 2 * ‖Δ k‖ ^ 2 +
          1 / (4 * α) * ∑ k ∈ Finset.range (2 ^ n), ∑ j : Fin m, ⟪rampVec n k j, z⟫ ^ 2 := by
        simp only [Finset.sum_add_distrib, ← hsq, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
        ring
    _ = 2 * l * energy f + 2 ^ n / (4 * l) *
          ∑ k ∈ Finset.range (2 ^ n), ∑ j : Fin m, ⟪rampVec n k j, z⟫ ^ 2 := by
        rw [hE, ← Finset.mul_sum, hα]
        field_simp
        ring

/-- The `L²` kernel `(f, g) ↦ ∫₀¹ ⟨f, g⟩` is positive semidefinite on every finite family of square
integrable functions (it is a Gram kernel in `L²([0,1]; ℝ^m)`). -/
theorem psdOn_L2 (F₀ : Finset (ℝ → Rd m))
    (hF : ∀ f ∈ F₀, MemLp f 2 (volume.restrict (Icc (0 : ℝ) 1))) :
    LQGDimension.PSDOn F₀ (fun f g => ∫ u in Icc (0 : ℝ) 1, ⟪f u, g u⟫) := by
  unfold LQGDimension.PSDOn
  have e : (Matrix.of fun f g : F₀ => ∫ u in Icc (0 : ℝ) 1, ⟪(f : ℝ → Rd m) u, (g : ℝ → Rd m) u⟫) =
      Matrix.gram ℝ (fun f : F₀ => toL2I (f : ℝ → Rd m)) := by
    ext f g
    rw [Matrix.of_apply, Matrix.gram_apply, inner_toL2I (hF f f.2) (hF g g.2)]
  rw [e]
  exact Matrix.posSemidef_gram ℝ _

/-- **The `H⁻¹` lemma, `λ`-form** (HA2-13, D8(b)): for a finite family `F₀ ⊆ V_n(ℝ^m)` of energy
`≤ E₀` and every `λ > 0`, the expected maximum of the centered Gaussian family with covariance
`(f, g) ↦ ∫₀¹ ⟨f, g⟩` (that is, `⟨f, Z⟩` for a white noise `Z` on `[0,1]` with values in `ℝ^m`)
is at most `2λ E₀ + m / (4λ)`. -/
theorem gEM_L2_le {n : ℕ} (F₀ : Finset (ℝ → Rd m)) {E₀ : ℝ} (hE₀ : 0 ≤ E₀)
    (hF : ∀ f ∈ F₀, f ∈ Vg (Rd m) n ∧ energy f ≤ E₀) {l : ℝ} (hl : 0 < l) :
    LQGDimension.gaussianExpectedMax F₀ (fun f g => ∫ u in Icc (0 : ℝ) 1, ⟪f u, g u⟫) 0 ≤
      2 * l * E₀ + m / (4 * l) := by
  classical
  set R : Finset (L2I m) := (Finset.range (2 ^ n) ×ˢ (Finset.univ : Finset (Fin m))).image
    (fun p => rampVec n p.1 p.2) with hR
  set T : Finset (L2I m) := F₀.image toL2I ∪ R with hT
  set V : Submodule ℝ (L2I m) := Submodule.span ℝ (T : Set (L2I m)) with hV
  have : FiniteDimensional ℝ V := FiniteDimensional.span_finset ℝ T
  let _ : MeasurableSpace V := borel V
  have : BorelSpace V := ⟨rfl⟩
  have hmemF : ∀ f ∈ F₀, toL2I f ∈ V := fun f hf =>
    Submodule.subset_span (Finset.mem_coe.2
      (Finset.mem_union_left _ (Finset.mem_image_of_mem toL2I hf)))
  have hmemR : ∀ k ∈ Finset.range (2 ^ n), ∀ j : Fin m, rampVec n k j ∈ V := fun k hk j =>
    Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_union_right _
      (Finset.mem_image_of_mem (fun p : ℕ × Fin m => rampVec n p.1 p.2) (a := (k, j))
        (Finset.mem_product.2 ⟨hk, Finset.mem_univ j⟩))))
  set v : (ℝ → Rd m) → V := fun f => if h : f ∈ F₀ then ⟨toL2I f, hmemF f h⟩ else 0 with hv
  set r : ℕ → Fin m → V := fun k j =>
    if h : k ∈ Finset.range (2 ^ n) then ⟨rampVec n k j, hmemR k h j⟩ else 0 with hr
  have hgram : ∀ f ∈ F₀, ∀ g ∈ F₀, (∫ u in Icc (0 : ℝ) 1, ⟪f u, g u⟫) = ⟪v f, v g⟫ := by
    intro f hf g hg
    simp only [hv, dite_eq_left hf, dite_eq_left hg, Submodule.coe_inner]
    rw [inner_toL2I (memLp_of_Vg (hF f hf).1) (memLp_of_Vg (hF g hg).1)]
  rw [LQGDimension.gaussianExpectedMax_congr F₀ 0 hgram,
    LQGDimension.gaussianExpectedMax_gram_eq_vecExpectedMax]
  unfold LQGDimension.vecExpectedMax
  simp only [Pi.zero_apply, add_zero]
  set Q : V → ℝ := fun γ => ∑ k ∈ Finset.range (2 ^ n), ∑ j : Fin m, ⟪r k j, γ⟫ ^ 2 with hQ
  have hpt : ∀ γ : V, (⨆ f : F₀, ⟪v f, γ⟫) ≤ 2 * l * E₀ + 2 ^ n / (4 * l) * Q γ := by
    intro γ
    have hQ0 : 0 ≤ Q γ := Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun j _ => sq_nonneg _
    refine Real.iSup_le (fun f => ?_) (by positivity)
    obtain ⟨hfV, hfE⟩ := hF f f.2
    have e1 : ⟪v f, γ⟫ = ⟪toL2I (f : ℝ → Rd m), (γ : L2I m)⟫ := by
      simp only [hv, dite_eq_left f.2, Submodule.coe_inner]
    have e2 : Q γ = ∑ k ∈ Finset.range (2 ^ n), ∑ j : Fin m,
        ⟪rampVec n k j, (γ : L2I m)⟫ ^ 2 := by
      refine Finset.sum_congr rfl fun k hk => Finset.sum_congr rfl fun j _ => ?_
      simp only [hr, dite_eq_left hk, Submodule.coe_inner]
    rw [e1, e2]
    calc ⟪toL2I (f : ℝ → Rd m), (γ : L2I m)⟫ ≤ |⟪toL2I (f : ℝ → Rd m), (γ : L2I m)⟫| :=
          le_abs_self _
      _ ≤ 2 * l * energy (f : ℝ → Rd m) + 2 ^ n / (4 * l) *
            ∑ k ∈ Finset.range (2 ^ n), ∑ j : Fin m, ⟪rampVec n k j, (γ : L2I m)⟫ ^ 2 :=
          abs_inner_toL2I_le hfV _ hl
      _ ≤ 2 * l * E₀ + 2 ^ n / (4 * l) *
            ∑ k ∈ Finset.range (2 ^ n), ∑ j : Fin m, ⟪rampVec n k j, (γ : L2I m)⟫ ^ 2 := by
          gcongr
  have hint1 : Integrable (fun γ : V => ⨆ f : F₀, ⟪v f, γ⟫) (stdGaussian V) := by
    have := LQGDimension.integrable_iSup_inner_add F₀ v 0
    simpa only [Pi.zero_apply, add_zero] using this
  have hQi : Integrable Q (stdGaussian V) :=
    integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun j _ =>
      LQGDimension.GaussianMax.integrable_inner_sq (r k j)
  have hint2 : Integrable (fun γ : V => 2 * l * E₀ + 2 ^ n / (4 * l) * Q γ) (stdGaussian V) :=
    (integrable_const _).add (hQi.const_mul _)
  have hEQ : ∫ γ, Q γ ∂(stdGaussian V) ≤ m / 2 ^ n := by
    calc ∫ γ, Q γ ∂(stdGaussian V) = ∑ k ∈ Finset.range (2 ^ n), ∑ j : Fin m, ‖r k j‖ ^ 2 := by
          simp only [hQ]
          rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun j _ =>
            LQGDimension.GaussianMax.integrable_inner_sq (r k j)]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [integral_finsetSum _ fun j _ => LQGDimension.GaussianMax.integrable_inner_sq (r k j)]
          exact Finset.sum_congr rfl fun j _ => LQGDimension.GaussianMax.integral_inner_sq (r k j)
      _ ≤ ∑ k ∈ Finset.range (2 ^ n), ∑ j : Fin m, (1 / 2 ^ n : ℝ) ^ 2 := by
          refine Finset.sum_le_sum fun k hk => Finset.sum_le_sum fun j _ => ?_
          simp only [hr, dite_eq_left hk]
          exact norm_rampVec_sq_le n k j
      _ = m / 2 ^ n := by
          simp only [Finset.sum_const, Finset.card_range, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
          push_cast
          field_simp
  have hN : (0 : ℝ) < 2 ^ n := by positivity
  calc ∫ γ, (⨆ f : F₀, ⟪v f, γ⟫) ∂(stdGaussian V)
      ≤ ∫ γ, (2 * l * E₀ + 2 ^ n / (4 * l) * Q γ) ∂(stdGaussian V) :=
        integral_mono hint1 hint2 hpt
    _ = 2 * l * E₀ + 2 ^ n / (4 * l) * ∫ γ, Q γ ∂(stdGaussian V) := by
        rw [integral_add (integrable_const _) (hQi.const_mul _), integral_const,
          integral_const_mul, probReal_univ, one_smul]
    _ ≤ 2 * l * E₀ + 2 ^ n / (4 * l) * (m / 2 ^ n) := by gcongr
    _ = 2 * l * E₀ + m / (4 * l) := by field_simp

/-- Optimization in `λ`: if `X ≤ 2λA + M/(4λ)` for every `λ > 0`, with `A, M ≥ 0`, then
`X ≤ √(2 M A)`. -/
theorem le_sqrt_of_forall_le_add {X A M : ℝ} (hA : 0 ≤ A) (hM : 0 ≤ M)
    (h : ∀ l : ℝ, 0 < l → X ≤ 2 * l * A + M / (4 * l)) : X ≤ Real.sqrt (2 * M * A) := by
  rcases hA.lt_or_eq with hA' | hA'
  · rcases hM.lt_or_eq with hM' | hM'
    · set s := Real.sqrt (2 * M * A) with hs
      have hs0 : 0 < s := Real.sqrt_pos.2 (by positivity)
      have hs2 : s ^ 2 = 2 * M * A := Real.sq_sqrt (by positivity)
      have hl : 0 < s / (4 * A) := by positivity
      refine (h _ hl).trans (le_of_eq ?_)
      have e : M / (4 * (s / (4 * A))) = s / 2 := by
        field_simp
        nlinarith [hs2]
      rw [e]
      field_simp
      ring
    · subst hM'
      rw [mul_zero, zero_mul, Real.sqrt_zero]
      by_contra hX
      push Not at hX
      have h1 := h (X / (4 * A)) (by positivity)
      rw [zero_div, add_zero] at h1
      have e : 2 * (X / (4 * A)) * A = X / 2 := by field_simp; ring
      linarith
  · subst hA'
    rw [mul_zero, Real.sqrt_zero]
    by_contra hX
    push Not at hX
    rcases hM.lt_or_eq with hM' | hM'
    · have h1 := h (M / (2 * X)) (by positivity)
      have e : M / (4 * (M / (2 * X))) = X / 2 := by field_simp; ring
      rw [mul_zero, zero_add, e] at h1
      linarith
    · subst hM'
      have h1 := h 1 one_pos
      rw [mul_zero, zero_div, add_zero] at h1
      linarith

/-- **The `H⁻¹` lemma** (HA2-13, D8(b)): for a finite family `F₀ ⊆ V_n(ℝ^m)` of energy
`≤ E₀`, `E max_{f ∈ F₀} ⟨f, Z⟩ ≤ √(2 m E₀)`, where `(⟨f, Z⟩)_f` is the centered Gaussian family
with covariance `∫₀¹ ⟨f, g⟩` (lattice convention). -/
theorem gEM_L2_le_sqrt {n : ℕ} (F₀ : Finset (ℝ → Rd m)) {E₀ : ℝ} (hE₀ : 0 ≤ E₀)
    (hF : ∀ f ∈ F₀, f ∈ Vg (Rd m) n ∧ energy f ≤ E₀) :
    LQGDimension.gaussianExpectedMax F₀ (fun f g => ∫ u in Icc (0 : ℝ) 1, ⟪f u, g u⟫) 0 ≤
      Real.sqrt (2 * m * E₀) :=
  le_sqrt_of_forall_le_add hE₀ (Nat.cast_nonneg m) fun _ hl => gEM_L2_le F₀ hE₀ hF hl

/-- `√(max E₀ 0 / L) = √(E₀ / L)` for `L > 0`. -/
theorem sqrt_max_div {E₀ L : ℝ} (hL : 0 < L) :
    Real.sqrt (max E₀ 0 / L) = Real.sqrt (E₀ / L) := by
  rcases le_total 0 E₀ with h | h
  · rw [max_eq_left h]
  · rw [max_eq_right h, zero_div, Real.sqrt_zero,
      Real.sqrt_eq_zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg h hL.le)]

/-- `∫₀¹ ⟨f, f⟩ - 2 ∫₀¹ ⟨f, g⟩ + ∫₀¹ ⟨g, g⟩ = ∫₀¹ |f - g|²` for continuous `f, g`. -/
theorem integral_inner_sub_eq {f g : ℝ → Rd m} (hf : Continuous f) (hg : Continuous g) :
    (∫ u in Icc (0 : ℝ) 1, ⟪f u, f u⟫) - 2 * (∫ u in Icc (0 : ℝ) 1, ⟪f u, g u⟫) +
        (∫ u in Icc (0 : ℝ) 1, ⟪g u, g u⟫) = ∫ u in (0 : ℝ)..1, ‖f u - g u‖ ^ 2 := by
  have i1 : IntegrableOn (fun u => ⟪f u, f u⟫) (Icc (0 : ℝ) 1) :=
    (hf.inner hf).integrableOn_Icc
  have i2 : IntegrableOn (fun u => ⟪f u, g u⟫) (Icc (0 : ℝ) 1) :=
    (hf.inner hg).integrableOn_Icc
  have i3 : IntegrableOn (fun u => ⟪g u, g u⟫) (Icc (0 : ℝ) 1) :=
    (hg.inner hg).integrableOn_Icc
  have e : ∀ u, ‖f u - g u‖ ^ 2 = ⟪f u, f u⟫ - 2 * ⟪f u, g u⟫ + ⟪g u, g u⟫ := fun u => by
    rw [norm_sub_sq_real, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc]
  simp_rw [e]
  rw [integral_add ?_ i3, integral_sub i1 ?_, integral_const_mul]
  all_goals first
    | exact i1.sub (i2.const_mul 2)
    | exact i2.const_mul 2

end Bands

variable {m : ℕ} {κ : Rd (m + 1) → ℝ}

/-- **Reduction of the supremum bound to (3.13)** (HA2 D8(b)): if `C_b ≥ 0` is a constant for which
(3.13) holds (as given by `bandLemma34b_var`), then for all `δ, L > 0`, `E₀`, `n` and every finite
family `F ⊆ V_n(ℝ^m)` of energy `≤ E₀`, the sign-doubled family of
`X(f) = δ^{-1/2} ⟨H_{δL,∞}, μ_{δf} - μ_0⟩` satisfies
`E max_{f ∈ F} |X(f)| ≤ 2 √(2 C_b m) √(E₀ / L)` (lattice convention).  The hypothesis is the
proved statement (3.13); the target theorems below discharge it with `bandLemma34b_var`. -/
theorem bandLemma34b_sup_of_var (hκ : IsLFPPKernel κ) {Cb : ℝ} (hCb0 : 0 ≤ Cb)
    (hCb : ∀ (δ L : ℝ), 0 < δ → 0 < L → ∀ f g : ℝ → Rd m, Measurable f → Measurable g →
      MemLp (f - g) 2 (volume.restrict (Icc (0 : ℝ) 1)) →
      IsPairable κ (Ioi (δ * L)) (Bands.graphMeasure δ f) (Bands.graphMeasure δ g) ∧
      δ⁻¹ * scaleCov κ (Ioi (δ * L)) (Bands.graphMeasure δ f) (Bands.graphMeasure δ g)
          (Bands.graphMeasure δ f) (Bands.graphMeasure δ g) ≤
        Cb / L * ∫ x in (0 : ℝ)..1, ‖f x - g x‖ ^ 2)
    (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L) (E₀ : ℝ) (n : ℕ) (F : Finset (ℝ → Rd m))
    (hF : ∀ f ∈ F, f ∈ Vg (Rd m) n ∧ energy f ≤ E₀) :
    LQGDimension.gaussianExpectedMax (F ×ˢ (Finset.univ : Finset Bool))
      (fun p q => Bands.signK p.2 q.2 * (δ⁻¹ * scaleCov κ (Ioi (δ * L))
        (Bands.graphMeasure δ p.1) (Bands.graphMeasure δ 0) (Bands.graphMeasure δ q.1)
        (Bands.graphMeasure δ 0))) 0 ≤ 2 * Real.sqrt (2 * Cb * m) * Real.sqrt (E₀ / L) := by
  classical
  set E₁ : ℝ := max E₀ 0 with hE₁
  have hE₁0 : 0 ≤ E₁ := le_max_right _ _
  set F₀ : Finset (ℝ → Rd m) := insert 0 F with hF₀def
  have hF₀ : ∀ f ∈ F₀, f ∈ Vg (Rd m) n ∧ energy f ≤ E₁ := by
    intro f hf
    rcases Finset.mem_insert.1 hf with rfl | hf
    · exact ⟨Var.zero_mem_Vg n, by rw [Var.energy_zero]; exact hE₁0⟩
    · exact ⟨(hF f hf).1, (hF f hf).2.trans (le_max_left _ _)⟩
  have hsub : F ⊆ F₀ := Finset.subset_insert _ _
  have h0F₀ : (0 : ℝ → Rd m) ∈ F₀ := Finset.mem_insert_self _ _
  have hmem : ∀ f ∈ F₀, MemLp f 2 (volume.restrict (Icc (0 : ℝ) 1)) := fun f hf =>
    Bands.memLp_of_Vg (hF₀ f hf).1
  have hmeas : ∀ f ∈ F₀, Measurable f := fun f hf => (Var.Vg_continuous (hF₀ f hf).1).measurable
  -- the band vectors and their Gram vectors
  have hCXpsd : LQGDimension.PSDOn F₀ (fun f g => δ⁻¹ * scaleCov κ (Ioi (δ * L))
      (Bands.graphMeasure δ f) (Bands.graphMeasure δ 0) (Bands.graphMeasure δ g)
      (Bands.graphMeasure δ 0)) :=
    Var.psdOn_const_mul (psdOn_scaleCov (κ := κ) (Ioi (δ * L)) F₀ (fun f => Bands.graphMeasure δ f)
      fun _ => Bands.graphMeasure δ 0) (inv_nonneg.2 hδ.le)
  obtain ⟨x, hx⟩ := LQGDimension.exists_gram_of_psdOn F₀ _ hCXpsd
  -- the comparison kernel and its Gram vectors
  set σ : ℝ := Real.sqrt (Cb / L) with hσ
  have hσ0 : 0 ≤ σ := Real.sqrt_nonneg _
  have hσ2 : σ ^ 2 = Cb / L := Real.sq_sqrt (div_nonneg hCb0 hL.le)
  have hCYpsd : LQGDimension.PSDOn F₀ (fun f g => ∫ u in Icc (0 : ℝ) 1, ⟪f u, g u⟫) :=
    Bands.psdOn_L2 F₀ hmem
  obtain ⟨y, hy⟩ := LQGDimension.exists_gram_of_psdOn F₀
    (fun f g => σ ^ 2 * ∫ u in Icc (0 : ℝ) 1, ⟪f u, g u⟫) (Var.psdOn_const_mul hCYpsd (sq_nonneg σ))
  -- Step 1: the left side as the expected maximum of sign-doubled Gram vectors
  set u : (ℝ → Rd m) × Bool → EuclideanSpace ℝ F₀ := fun p => Bands.sgn p.2 • x p.1 with hu
  have hgramu : ∀ p ∈ F ×ˢ (Finset.univ : Finset Bool), ∀ q ∈ F ×ˢ (Finset.univ : Finset Bool),
      Bands.signK p.2 q.2 * (δ⁻¹ * scaleCov κ (Ioi (δ * L)) (Bands.graphMeasure δ p.1)
        (Bands.graphMeasure δ 0) (Bands.graphMeasure δ q.1) (Bands.graphMeasure δ 0)) =
        ⟪u p, u q⟫ := by
    intro p hp q hq
    rw [Finset.mem_product] at hp hq
    simp only [hu, real_inner_smul_left, real_inner_smul_right,
      hx p.1 (hsub hp.1) q.1 (hsub hq.1), Bands.signK_eq_mul]
    ring
  rw [LQGDimension.gaussianExpectedMax_congr _ 0 hgramu,
    LQGDimension.gaussianExpectedMax_gram_eq_vecExpectedMax]
  -- Step 2: `max_F |X| ≤ max_{F₀} X + max_{F₀} (-X)`, using `X(0) = 0`
  have hx0 : x 0 = 0 := by
    have h00 := hx 0 h0F₀ 0 h0F₀
    simp only [scaleCov_self, bandVecM_self, norm_zero] at h00
    have h2 : ‖x 0‖ ^ 2 = 0 := by
      rw [← real_inner_self_eq_norm_sq, h00]
      ring
    exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h2)
  have hle : LQGDimension.vecExpectedMax (F ×ˢ (Finset.univ : Finset Bool)) u 0 ≤
      LQGDimension.vecExpectedMax F₀ x 0 + LQGDimension.vecExpectedMax F₀ (fun f => -x f) 0 := by
    unfold LQGDimension.vecExpectedMax
    have i0 := LQGDimension.integrable_iSup_inner_add (F ×ˢ (Finset.univ : Finset Bool)) u 0
    have i1 := LQGDimension.integrable_iSup_inner_add F₀ x 0
    have i2 := LQGDimension.integrable_iSup_inner_add F₀ (fun f => -x f) 0
    rw [← integral_add i1 i2]
    refine integral_mono i0 (i1.add i2) fun γ => ?_
    simp only [Pi.zero_apply, add_zero]
    have hb1 : BddAbove (Set.range fun f : ↥F₀ => ⟪x f, γ⟫) := (Set.finite_range _).bddAbove
    have hb2 : BddAbove (Set.range fun f : ↥F₀ => ⟪-x f, γ⟫) := (Set.finite_range _).bddAbove
    have hM1 : 0 ≤ ⨆ f : ↥F₀, ⟪x f, γ⟫ := by
      have h := le_ciSup hb1 ⟨0, h0F₀⟩
      simp only [hx0, inner_zero_left] at h
      exact h
    have hM2 : 0 ≤ ⨆ f : ↥F₀, ⟪-x f, γ⟫ := by
      have h := le_ciSup hb2 ⟨0, h0F₀⟩
      simp only [hx0, neg_zero, inner_zero_left] at h
      exact h
    refine Real.iSup_le (fun p => ?_) (add_nonneg hM1 hM2)
    have hp := p.2
    rw [Finset.mem_product] at hp
    have hpF₀ : (p : (ℝ → Rd m) × Bool).1 ∈ F₀ := hsub hp.1
    cases hs : (p : (ℝ → Rd m) × Bool).2
    · have e : ⟪u p, γ⟫ = ⟪-x (p : (ℝ → Rd m) × Bool).1, γ⟫ := by
        simp only [hu, hs, Bands.sgn, Bool.false_eq_true, ↓reduceIte, neg_smul, one_smul]
      have h := le_ciSup hb2 ⟨_, hpF₀⟩
      rw [e]
      linarith
    · have e : ⟪u p, γ⟫ = ⟪x (p : (ℝ → Rd m) × Bool).1, γ⟫ := by
        simp only [hu, hs, Bands.sgn, ↓reduceIte, one_smul]
      have h := le_ciSup hb1 ⟨_, hpF₀⟩
      rw [e]
      linarith
  have hneg : LQGDimension.vecExpectedMax F₀ (fun f => -x f) 0 =
      LQGDimension.vecExpectedMax F₀ x 0 :=
    LQGDimension.vecExpectedMax_eq_of_gram_eq F₀ _ _ 0 fun i _ j _ => inner_neg_neg _ _
  -- Step 3: Sudakov–Fernique against the `L²` process, by (3.13)
  have hdist : ∀ f ∈ F₀, ∀ g ∈ F₀, ‖x f - x g‖ ≤ ‖y f - y g‖ := by
    intro f hf g hg
    have hfm := hmem f hf
    have hgm := hmem g hg
    have hf0 : MemLp (f - 0) 2 (volume.restrict (Icc (0 : ℝ) 1)) := by rw [sub_zero]; exact hfm
    have hg0 : MemLp (g - 0) 2 (volume.restrict (Icc (0 : ℝ) 1)) := by rw [sub_zero]; exact hgm
    obtain ⟨hpf, -⟩ := hCb δ L hδ hL f 0 (hmeas f hf) measurable_const hf0
    obtain ⟨hpg, -⟩ := hCb δ L hδ hL g 0 (hmeas g hg) measurable_const hg0
    obtain ⟨-, hvar⟩ := hCb δ L hδ hL f g (hmeas f hf) (hmeas g hg) (hfm.sub hgm)
    have hv : bandVecM κ (Ioi (δ * L)) (Bands.graphMeasure δ f) (Bands.graphMeasure δ 0) -
        bandVecM κ (Ioi (δ * L)) (Bands.graphMeasure δ g) (Bands.graphMeasure δ 0) =
        bandVecM κ (Ioi (δ * L)) (Bands.graphMeasure δ f) (Bands.graphMeasure δ g) := by
      rw [bandVecM_sub_bandVecM hκ hpf hpg, add_comm (Bands.graphMeasure δ 0),
        bandVecM_add_right hκ]
    have hsc : scaleCov κ (Ioi (δ * L)) (Bands.graphMeasure δ f) (Bands.graphMeasure δ g)
        (Bands.graphMeasure δ f) (Bands.graphMeasure δ g) =
        scaleCov κ (Ioi (δ * L)) (Bands.graphMeasure δ f) (Bands.graphMeasure δ 0)
          (Bands.graphMeasure δ f) (Bands.graphMeasure δ 0) -
        2 * scaleCov κ (Ioi (δ * L)) (Bands.graphMeasure δ f) (Bands.graphMeasure δ 0)
          (Bands.graphMeasure δ g) (Bands.graphMeasure δ 0) +
        scaleCov κ (Ioi (δ * L)) (Bands.graphMeasure δ g) (Bands.graphMeasure δ 0)
          (Bands.graphMeasure δ g) (Bands.graphMeasure δ 0) := by
      rw [scaleCov_self, ← hv, norm_sub_sq_real, ← real_inner_self_eq_norm_sq,
        ← real_inner_self_eq_norm_sq]
      rfl
    have hX : ‖x f - x g‖ ^ 2 = δ⁻¹ * scaleCov κ (Ioi (δ * L)) (Bands.graphMeasure δ f)
        (Bands.graphMeasure δ g) (Bands.graphMeasure δ f) (Bands.graphMeasure δ g) := by
      rw [norm_sub_sq_real, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
        hx f hf f hf, hx f hf g hg, hx g hg g hg, hsc]
      ring
    have hY : ‖y f - y g‖ ^ 2 = Cb / L * ∫ u in (0 : ℝ)..1, ‖f u - g u‖ ^ 2 := by
      rw [norm_sub_sq_real, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
        hy f hf f hf, hy f hf g hg, hy g hg g hg, hσ2,
        ← Bands.integral_inner_sub_eq (Var.Vg_continuous (hF₀ f hf).1)
          (Var.Vg_continuous (hF₀ g hg).1)]
      ring
    have h2 : ‖x f - x g‖ ^ 2 ≤ ‖y f - y g‖ ^ 2 := by
      rw [hX, hY]
      exact hvar
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h2
  have hSF : LQGDimension.vecExpectedMax F₀ x 0 ≤ LQGDimension.vecExpectedMax F₀ y 0 :=
    LQGDimension.sudakovFernique (ℝ → Rd m) (EuclideanSpace ℝ F₀) (EuclideanSpace ℝ F₀) F₀ x y 0
      hdist
  -- Step 4: the comparison process, by the `H⁻¹` lemma
  have hYval : LQGDimension.vecExpectedMax F₀ y 0 ≤ σ * Real.sqrt (2 * m * E₁) := by
    rw [← LQGDimension.gaussianExpectedMax_gram_eq_vecExpectedMax,
      LQGDimension.gaussianExpectedMax_congr F₀ 0 fun i hi j hj => hy i hi j hj]
    have h0 : (0 : (ℝ → Rd m) → ℝ) = fun i => σ * (0 : (ℝ → Rd m) → ℝ) i := by
      funext i
      simp only [Pi.zero_apply, mul_zero]
    rw [h0, Var.gEM_smul F₀ _ hCYpsd 0 hσ0]
    exact mul_le_mul_of_nonneg_left (Bands.gEM_L2_le_sqrt F₀ hE₁0 hF₀) hσ0
  -- Step 5: combine
  have halg : σ * Real.sqrt (2 * m * E₁) = Real.sqrt (2 * Cb * m) * Real.sqrt (E₀ / L) := by
    rw [← Bands.sqrt_max_div hL, ← hE₁, hσ, ← Real.sqrt_mul (div_nonneg hCb0 hL.le),
      ← Real.sqrt_mul (by positivity)]
    congr 1
    field_simp
  calc LQGDimension.vecExpectedMax (F ×ˢ (Finset.univ : Finset Bool)) u 0
      ≤ LQGDimension.vecExpectedMax F₀ x 0 + LQGDimension.vecExpectedMax F₀ (fun f => -x f) 0 :=
        hle
    _ = 2 * LQGDimension.vecExpectedMax F₀ x 0 := by rw [hneg]; ring
    _ ≤ 2 * (σ * Real.sqrt (2 * m * E₁)) := by linarith
    _ = 2 * Real.sqrt (2 * Cb * m) * Real.sqrt (E₀ / L) := by rw [halg]; ring

/-- **Lemma 3.4(b), the expected supremum** (HA2 D8(b); the second part of HA2's `Lemma34b`):
there is `C = C(m, κ)` such that for all `δ, L > 0`, `E₀`, `n` and every finite family
`F ⊆ V_n(ℝ^m)` of energy `≤ E₀`, the sign-doubled family of
`X(f) = δ^{-1/2} ⟨H_{δL,∞}, μ_{δf} - μ_0⟩` satisfies
`E max_{f ∈ F} |X(f)| ≤ C √(E₀ / L)` (lattice convention).  Explicitly `C = 2 √(2 C_b m)` with
`C_b` the constant of (3.13) (`bandLemma34b_var`). -/
theorem bandLemma34b_sup (hκ : IsLFPPKernel κ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (δ L : ℝ), 0 < δ → 0 < L → ∀ (E₀ : ℝ) (n : ℕ)
      (F : Finset (ℝ → Rd m)), (∀ f ∈ F, f ∈ Vg (Rd m) n ∧ energy f ≤ E₀) →
      LQGDimension.gaussianExpectedMax (F ×ˢ (Finset.univ : Finset Bool))
        (fun p q => Bands.signK p.2 q.2 * (δ⁻¹ * scaleCov κ (Ioi (δ * L))
          (Bands.graphMeasure δ p.1) (Bands.graphMeasure δ 0) (Bands.graphMeasure δ q.1)
          (Bands.graphMeasure δ 0))) 0 ≤ C * Real.sqrt (E₀ / L) := by
  obtain ⟨Cb, hCb0, hCb⟩ := bandLemma34b_var hκ
  exact ⟨2 * Real.sqrt (2 * Cb * m), by positivity, fun δ L hδ hL E₀ n F hF =>
    bandLemma34b_sup_of_var hκ hCb0 hCb δ L hδ hL E₀ n F hF⟩

/-- **Lemma 3.4(b) with the packet's constants** (HA2 D8(b)): there is `C_b = C_b(m, κ)` such
that (3.13) holds with `C_b` and, with the same `C_b`,
`E max_{f ∈ F} |X(f)| ≤ 2 √(C_b m E₀ / L)` for every finite family `F ⊆ V_n(ℝ^m)` of energy
`≤ E₀`.  (`C_b` is twice the constant of `bandLemma34b_var`; the factor `2` absorbs the `√2` lost
by the ramp proof of the `H⁻¹` lemma.) -/
theorem bandLemma34b_explicit (hκ : IsLFPPKernel κ) :
    ∃ Cb : ℝ, 0 ≤ Cb ∧ ∀ (δ L : ℝ), 0 < δ → 0 < L →
      (∀ f g : ℝ → Rd m, Measurable f → Measurable g →
        MemLp (f - g) 2 (volume.restrict (Icc (0 : ℝ) 1)) →
        IsPairable κ (Ioi (δ * L)) (Bands.graphMeasure δ f) (Bands.graphMeasure δ g) ∧
        δ⁻¹ * scaleCov κ (Ioi (δ * L)) (Bands.graphMeasure δ f) (Bands.graphMeasure δ g)
            (Bands.graphMeasure δ f) (Bands.graphMeasure δ g) ≤
          Cb / L * ∫ x in (0 : ℝ)..1, ‖f x - g x‖ ^ 2) ∧
      ∀ (E₀ : ℝ) (n : ℕ) (F : Finset (ℝ → Rd m)), (∀ f ∈ F, f ∈ Vg (Rd m) n ∧ energy f ≤ E₀) →
        LQGDimension.gaussianExpectedMax (F ×ˢ (Finset.univ : Finset Bool))
          (fun p q => Bands.signK p.2 q.2 * (δ⁻¹ * scaleCov κ (Ioi (δ * L))
            (Bands.graphMeasure δ p.1) (Bands.graphMeasure δ 0) (Bands.graphMeasure δ q.1)
            (Bands.graphMeasure δ 0))) 0 ≤ 2 * Real.sqrt (Cb * m * E₀ / L) := by
  obtain ⟨C₀, hC₀0, hC₀⟩ := bandLemma34b_var hκ
  refine ⟨2 * C₀, by positivity, fun δ L hδ hL => ⟨fun f g hf hg hfg => ?_,
    fun E₀ n F hF => ?_⟩⟩
  · obtain ⟨hp, hb⟩ := hC₀ δ L hδ hL f g hf hg hfg
    refine ⟨hp, hb.trans ?_⟩
    have hI : 0 ≤ ∫ x in (0 : ℝ)..1, ‖f x - g x‖ ^ 2 :=
      intervalIntegral.integral_nonneg zero_le_one fun x _ => sq_nonneg _
    have h2 : C₀ / L ≤ 2 * C₀ / L := by
      gcongr
      linarith
    exact mul_le_mul_of_nonneg_right h2 hI
  · refine (bandLemma34b_sup_of_var hκ hC₀0 hC₀ δ L hδ hL E₀ n F hF).trans (le_of_eq ?_)
    rw [mul_assoc, ← Real.sqrt_mul (by positivity)]
    congr 2
    ring

/-- **Lemma 3.4(b)** in the exact form of HA2's `Lemma34b` (with `V m n` the frozen
`Vg (Rd m) n`): one constant `C = C(m, κ)` for (3.13) and for the expected supremum. -/
theorem bandLemma34b (hκ : IsLFPPKernel κ) :
    ∃ C : ℝ, ∀ (δ L : ℝ), 0 < δ → 0 < L →
      (∀ f g : ℝ → Rd m, Measurable f → Measurable g →
        MemLp (f - g) 2 (volume.restrict (Icc (0 : ℝ) 1)) →
        IsPairable κ (Ioi (δ * L)) (Bands.graphMeasure δ f) (Bands.graphMeasure δ g) ∧
        δ⁻¹ * scaleCov κ (Ioi (δ * L)) (Bands.graphMeasure δ f) (Bands.graphMeasure δ g)
            (Bands.graphMeasure δ f) (Bands.graphMeasure δ g) ≤
          C / L * ∫ x in (0 : ℝ)..1, ‖f x - g x‖ ^ 2) ∧
      ∀ (E₀ : ℝ) (n : ℕ) (F : Finset (ℝ → Rd m)), (∀ f ∈ F, f ∈ Vg (Rd m) n ∧ energy f ≤ E₀) →
        LQGDimension.gaussianExpectedMax (F ×ˢ (Finset.univ : Finset Bool))
          (fun p q => Bands.signK p.2 q.2 * (δ⁻¹ * scaleCov κ (Ioi (δ * L))
            (Bands.graphMeasure δ p.1) (Bands.graphMeasure δ 0) (Bands.graphMeasure δ q.1)
            (Bands.graphMeasure δ 0))) 0 ≤ C * Real.sqrt (E₀ / L) := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := bandLemma34b_var hκ
  obtain ⟨C₂, hC₂0, hC₂⟩ := bandLemma34b_sup hκ
  refine ⟨max C₁ C₂, fun δ L hδ hL => ⟨fun f g hf hg hfg => ?_, fun E₀ n F hF => ?_⟩⟩
  · obtain ⟨hp, hb⟩ := hC₁ δ L hδ hL f g hf hg hfg
    refine ⟨hp, hb.trans ?_⟩
    have hI : 0 ≤ ∫ x in (0 : ℝ)..1, ‖f x - g x‖ ^ 2 :=
      intervalIntegral.integral_nonneg zero_le_one fun x _ => sq_nonneg _
    gcongr
    exact le_max_left _ _
  · refine (hC₂ δ L hδ hL E₀ n F hF).trans ?_
    gcongr
    exact le_max_right _ _

/-- **Lemma 3.4(b), the expected supremum for a white noise**: with the constant of
`bandLemma34b_sup`, for every white noise `W` (`IsWhiteNoise`), all `δ, L > 0` and every finite
family `F ⊆ V_n(ℝ^m)` of energy `≤ E₀`,
`E max_{f ∈ F} |δ^{-1/2} ⟨H_{δL,∞}, μ_{δf} - μ_0⟩| ≤ C √(E₀ / L)`, the pairing being
`W(bandVecM κ (δL, ∞) μ_{δf} μ_0)`. -/
theorem bandLemma34b_sup_wn (hκ : IsLFPPKernel κ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
      (W : WN (m + 1) → Ω → ℝ), IsWhiteNoise P W → ∀ (δ L : ℝ), 0 < δ → 0 < L →
      ∀ (E₀ : ℝ) (n : ℕ) (F : Finset (ℝ → Rd m)), (∀ f ∈ F, f ∈ Vg (Rd m) n ∧ energy f ≤ E₀) →
      ∫ ω, (⨆ f : F, |(Real.sqrt δ)⁻¹ * W (bandVecM κ (Ioi (δ * L)) (Bands.graphMeasure δ f)
        (Bands.graphMeasure δ 0)) ω|) ∂P ≤ C * Real.sqrt (E₀ / L) := by
  obtain ⟨C, hC0, hC⟩ := bandLemma34b_sup hκ
  refine ⟨C, hC0, fun P W hW δ L hδ hL E₀ n F hF => ?_⟩
  set c : ℝ := (Real.sqrt δ)⁻¹ with hc
  have hc2 : c ^ 2 = δ⁻¹ := by rw [hc, inv_pow, Real.sq_sqrt hδ.le]
  set v : (ℝ → Rd m) → WN (m + 1) := fun f => c • bandVecM κ (Ioi (δ * L))
    (Bands.graphMeasure δ f) (Bands.graphMeasure δ 0) with hv
  have hae : ∀ᵐ ω ∂P, ∀ f : ↥F, W (v f) ω = c * W (bandVecM κ (Ioi (δ * L))
      (Bands.graphMeasure δ f) (Bands.graphMeasure δ 0)) ω := by
    rw [ae_all_iff]
    intro f
    exact hW.smul_ae _ _
  have e1 : ∫ ω, (⨆ f : F, |c * W (bandVecM κ (Ioi (δ * L)) (Bands.graphMeasure δ f)
      (Bands.graphMeasure δ 0)) ω|) ∂P = ∫ ω, (⨆ f : F, |W (v f) ω|) ∂P := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with ω hω
    simp only [hω]
  have hgram : ∀ p ∈ F ×ˢ (Finset.univ : Finset Bool), ∀ q ∈ F ×ˢ (Finset.univ : Finset Bool),
      Bands.signK p.2 q.2 * ⟪v p.1, v q.1⟫ =
        Bands.signK p.2 q.2 * (δ⁻¹ * scaleCov κ (Ioi (δ * L)) (Bands.graphMeasure δ p.1)
          (Bands.graphMeasure δ 0) (Bands.graphMeasure δ q.1) (Bands.graphMeasure δ 0)) := by
    intro p _ q _
    simp only [hv, real_inner_smul_left, real_inner_smul_right, ← hc2, scaleCov]
    ring
  rw [e1, Bands.integral_iSup_abs_eq_gEM hW F v,
    LQGDimension.gaussianExpectedMax_congr _ 0 hgram]
  exact hC δ L hδ hL E₀ n F hF

end HigherDimLFPP
