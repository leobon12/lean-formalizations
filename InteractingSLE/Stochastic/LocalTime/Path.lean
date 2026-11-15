/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Stochastic.LocalTime.Grid

/-!
# Paths with a singular push on their zero set: pathwise grid limits

Packet PROVE-TANAKA. `IsTanakaPath a c N s ρ x β j b` says that on `[s, ρ]`

  `x u = x s + a (β u - β s) + ∫_s^u b + c (j u - j s)`,

with `x, β, j` continuous, `b` integrable, `j` nondecreasing and constant on every interval where
`x ≠ 0` (the Stieltjes measure of `j` is carried by the zero set of `x`), and with the localization
bounds `|x| ≤ N`, `∫_s^ρ |b| ≤ N`, `j ρ - j s ≤ N`. This is the pathwise content of the
decomposition `dX = dM + b dt - (1 + ρ/2) dI` of the specification's proof of Theorem 2.4 (p. 37),
with `β` the path of the Brownian motion `M / a`.

Along a `GridApprox` of `ρ` (alive cells `k < m n` of the uniform partition), this file proves the
pathwise limits used by the expectation form of Itô's formula: the telescoping sum
(`tendsto_telescope`), the drift-plus-singular sum (`tendsto_drift_singular`), the Riemann sums of
`f''(x)` (`tendsto_riemann_f''`), the vanishing of the square of the finite-variation increments
(`tendsto_sq_fv`), and the bound `∑ |Δx - a Δβ| ≤ (1 + |c|) N` (`sum_abs_fv_le`).
-/

noncomputable section

open Set Filter Topology MeasureTheory MathFin
open scoped NNReal

namespace InteractingSLE.LocalTime

/-- The pathwise hypotheses of the Tanaka argument on `[s, ρ]`. -/
def IsTanakaPath (a c N : ℝ) (s ρ : ℝ≥0) (x β j b : ℝ≥0 → ℝ) : Prop :=
  ContinuousOn x (Icc s ρ) ∧ ContinuousOn β (Icc s ρ) ∧ ContinuousOn j (Icc s ρ) ∧
  IntervalIntegrable (fun r : ℝ => b r.toNNReal) volume s ρ ∧
  (∀ u ∈ Icc s ρ, x u = x s + a * (β u - β s) + (∫ r in (s : ℝ)..u, b r.toNNReal) +
    c * (j u - j s)) ∧
  MonotoneOn j (Icc s ρ) ∧
  (∀ u v, s ≤ u → u ≤ v → v ≤ ρ → (∀ r ∈ Icc u v, x r ≠ 0) → j u = j v) ∧
  (∀ u ∈ Icc s ρ, |x u| ≤ N) ∧
  (∫ r in (s : ℝ)..ρ, |b r.toNNReal|) ≤ N ∧
  j ρ - j s ≤ N

section Path

variable {a c N : ℝ} {s t ρ : ℝ≥0} {x β j b : ℝ≥0 → ℝ} {m : ℕ → ℕ}

/-- The increment of the finite-variation part over a cell inside `[s, ρ]`. -/
lemma IsTanakaPath.fv_incr (hP : IsTanakaPath a c N s ρ x β j b) {u v : ℝ≥0}
    (hu : u ∈ Icc s ρ) (hv : v ∈ Icc s ρ) :
    x v - x u - a * (β v - β u) =
      (∫ r in (u : ℝ)..v, b r.toNNReal) + c * (j v - j u) := by
  have hsρ : (s : ℝ) ≤ ρ := by exact_mod_cast hu.1.trans hu.2
  have hu' : (u : ℝ) ∈ Icc (s : ℝ) ρ := ⟨by exact_mod_cast hu.1, by exact_mod_cast hu.2⟩
  have hv' : (v : ℝ) ∈ Icc (s : ℝ) ρ := ⟨by exact_mod_cast hv.1, by exact_mod_cast hv.2⟩
  have hsub := intervalIntegral.integral_interval_sub_left (a := (s : ℝ)) (b := (v : ℝ))
    (c := (u : ℝ)) (intervalIntegrable_of_sub hsρ hP.2.2.2.1 ⟨le_rfl, hsρ⟩ hv')
    (intervalIntegrable_of_sub hsρ hP.2.2.2.1 ⟨le_rfl, hsρ⟩ hu')
  rw [hP.2.2.2.2.1 v hv, hP.2.2.2.2.1 u hu, ← hsub]
  ring

lemma IsTanakaPath.abs_le (hP : IsTanakaPath a c N s ρ x β j b) {u : ℝ≥0} (hu : u ∈ Icc s ρ) :
    |x u| ≤ N := hP.2.2.2.2.2.2.2.1 u hu

lemma IsTanakaPath.N_nonneg (hP : IsTanakaPath a c N s ρ x β j b) (hsρ : s ≤ ρ) : 0 ≤ N :=
  (abs_nonneg _).trans (hP.abs_le ⟨le_rfl, hsρ⟩)

/-- `∑_{k<m} |Δx_k - a Δβ_k| ≤ (1 + |c|) N` over the alive cells. -/
lemma IsTanakaPath.sum_abs_fv_le (hP : IsTanakaPath a c N s ρ x β j b)
    (hm : GridApprox s t ρ m) {n : ℕ} (hn : n ≠ 0) :
    ∑ k ∈ Finset.range (m n), |x (unifPartIcc s t n (k + 1)) - x (unifPartIcc s t n k) -
      a * (β (unifPartIcc s t n (k + 1)) - β (unifPartIcc s t n k))| ≤ (1 + |c|) * N := by
  have hsρ : (s : ℝ) ≤ ρ := by exact_mod_cast hm.s_le
  have hjm := hP.2.2.2.2.2.1
  have hb := hP.2.2.2.1
  have hab : ∀ u v, u ∈ Icc (s : ℝ) ρ → v ∈ Icc (s : ℝ) ρ →
      IntervalIntegrable (fun r => |b r.toNNReal|) volume u v :=
    fun u v hu hv => intervalIntegrable_of_sub hsρ hb.abs hu hv
  have hterm : ∀ k < m n, |x (unifPartIcc s t n (k + 1)) - x (unifPartIcc s t n k) -
      a * (β (unifPartIcc s t n (k + 1)) - β (unifPartIcc s t n k))| ≤
      (∫ r in (unifPartIcc s t n k : ℝ)..(unifPartIcc s t n (k + 1)), |b r.toNNReal|) +
      |c| * (j (unifPartIcc s t n (k + 1)) - j (unifPartIcc s t n k)) := by
    intro k hk
    have hk0 := hm.mem_Icc hn hk.le
    have hk1 := hm.mem_Icc hn hk
    have hle : (unifPartIcc s t n k : ℝ) ≤ unifPartIcc s t n (k + 1) := by
      exact_mod_cast unifPartIcc_mono s t n (Nat.le_succ k)
    have hmono : j (unifPartIcc s t n k) ≤ j (unifPartIcc s t n (k + 1)) :=
      hjm hk0 hk1 (unifPartIcc_mono s t n (Nat.le_succ k))
    rw [hP.fv_incr hk0 hk1]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · exact intervalIntegral.abs_integral_le_integral_abs hle
    · rw [abs_mul, abs_of_nonneg (sub_nonneg.2 hmono)]
  refine (Finset.sum_le_sum fun k hk => hterm k (Finset.mem_range.1 hk)).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_sub_grid m j n,
    hm.sum_integral_cells hn hab]
  have htm := hm.coe_mem_Icc hn le_rfl
  have h1 : ∫ r in (s : ℝ)..(unifPartIcc s t n (m n)), |b r.toNNReal| ≤ N :=
    (intervalIntegral.integral_mono_interval le_rfl htm.1 htm.2
      (Eventually.of_forall fun _ => abs_nonneg _) (hab _ _ ⟨le_rfl, hsρ⟩ ⟨hsρ, le_rfl⟩)).trans
      hP.2.2.2.2.2.2.2.2.1
  have h2 : j (unifPartIcc s t n (m n)) - j s ≤ N :=
    (sub_le_sub_right (hjm (hm.mem_Icc hn le_rfl) ⟨hm.s_le, le_rfl⟩ (hm n hn).2.1) _).trans
      hP.2.2.2.2.2.2.2.2.2
  have h0 : 0 ≤ |c| := abs_nonneg c
  nlinarith

/-- Telescoping along the alive cells. -/
lemma IsTanakaPath.tendsto_telescope (hP : IsTanakaPath a c N s ρ x β j b)
    (hm : GridApprox s t ρ m) {f : ℝ → ℝ} (hf : Continuous f) :
    Tendsto (fun n => ∑ k ∈ Finset.range (m n),
      (f (x (unifPartIcc s t n (k + 1))) - f (x (unifPartIcc s t n k)))) atTop
      (𝓝 (f (x ρ) - f (x s))) := by
  have := (hm.tendsto_comp (hf.comp_continuousOn hP.1) hm.s_le).sub_const (f (x s))
  refine this.congr fun n => ?_
  rw [sum_sub_grid m (fun u => f (x u)) n]
  rfl

/-- Drift-plus-singular sums: `∑ f'(x_k) (Δx_k - a Δβ_k) → ∫_s^ρ f'(x) b + c f'(0) (j ρ - j s)`. -/
lemma IsTanakaPath.tendsto_drift_singular (hP : IsTanakaPath a c N s ρ x β j b)
    (hm : GridApprox s t ρ m) (hst : s ≤ t) {f' : ℝ → ℝ} (hf' : Continuous f') :
    Tendsto (fun n => ∑ k ∈ Finset.range (m n), f' (x (unifPartIcc s t n k)) *
      (x (unifPartIcc s t n (k + 1)) - x (unifPartIcc s t n k) -
        a * (β (unifPartIcc s t n (k + 1)) - β (unifPartIcc s t n k)))) atTop
      (𝓝 ((∫ r in (s : ℝ)..ρ, f' (x r.toNNReal) * b r.toNNReal) +
        c * f' 0 * (j ρ - j s))) := by
  have hG : ContinuousOn (fun u => f' (x u)) (Icc s ρ) := hf'.comp_continuousOn hP.1
  have hD := hm.tendsto_drift hst hG hP.2.2.2.1
  have hsupp : ∀ u v, s ≤ u → u ≤ v → v ≤ ρ → j u ≠ j v →
      ∃ r ∈ Icc u v, (fun u => f' (x u)) r = f' 0 := by
    intro u v hu huv hv hne
    by_contra hcon
    simp only [not_exists, not_and] at hcon
    exact hne (hP.2.2.2.2.2.2.1 u v hu huv hv fun r hr hx => hcon r hr (by simp [hx]))
  have hS := hm.tendsto_singular hst hG hP.2.2.1 hP.2.2.2.2.2.1 hsupp
  have hsum := hD.add (hS.const_mul c)
  rw [show c * (f' 0 * (j ρ - j s)) = c * f' 0 * (j ρ - j s) by ring] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_range.1 hk
  rw [hP.fv_incr (hm.mem_Icc hn hk'.le) (hm.mem_Icc hn hk')]
  ring

/-- Riemann sums of `f''(x)`. -/
lemma IsTanakaPath.tendsto_riemann_f'' (hP : IsTanakaPath a c N s ρ x β j b)
    (hm : GridApprox s t ρ m) (hst : s ≤ t) {f'' : ℝ → ℝ} (hf'' : Continuous f'') :
    Tendsto (fun n => ∑ k ∈ Finset.range (m n), f'' (x (unifPartIcc s t n k)) *
      (((t : ℝ) - s) / n)) atTop (𝓝 (∫ r in (s : ℝ)..ρ, f'' (x r.toNNReal))) :=
  hm.tendsto_riemann hst (hf''.comp_continuousOn hP.1)

/-- Eventually every alive increment of `x` and of `β` is at most `η`. -/
lemma IsTanakaPath.eventually_incr_le (hP : IsTanakaPath a c N s ρ x β j b)
    (hm : GridApprox s t ρ m) (hst : s ≤ t) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n in atTop, n ≠ 0 ∧ ∀ k < m n,
      |x (unifPartIcc s t n (k + 1)) - x (unifPartIcc s t n k)| ≤ η ∧
      |β (unifPartIcc s t n (k + 1)) - β (unifPartIcc s t n k)| ≤ η := by
  filter_upwards [hm.eventually_abs_sub_le hst hP.1 hη, hm.eventually_abs_sub_le hst hP.2.1 hη]
    with n ⟨hn, hx⟩ ⟨_, hβ⟩
  refine ⟨hn, fun k hk => ⟨?_, ?_⟩⟩
  · exact hx k hk _ ⟨unifPartIcc_mono s t n (Nat.le_succ k), le_rfl⟩
  · exact hβ k hk _ ⟨unifPartIcc_mono s t n (Nat.le_succ k), le_rfl⟩

/-- The squares of the finite-variation increments: `∑ f''(x_k) (Δx_k - a Δβ_k)² → 0`. -/
lemma IsTanakaPath.tendsto_sq_fv (hP : IsTanakaPath a c N s ρ x β j b)
    (hm : GridApprox s t ρ m) (hst : s ≤ t) {f'' : ℝ → ℝ} (hf'' : Continuous f'') :
    Tendsto (fun n => ∑ k ∈ Finset.range (m n), f'' (x (unifPartIcc s t n k)) *
      (x (unifPartIcc s t n (k + 1)) - x (unifPartIcc s t n k) -
        a * (β (unifPartIcc s t n (k + 1)) - β (unifPartIcc s t n k))) ^ 2) atTop (𝓝 0) := by
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hf''.comp_continuousOn hP.1)
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK s ⟨le_rfl, hm.s_le⟩)
  set V := (1 + |c|) * N
  have hV0 : 0 ≤ V := mul_nonneg (by positivity) (hP.N_nonneg hm.s_le)
  refine tendsto_of_forall_eventually_abs_le fun ε hε => ?_
  set η := ε / ((K + 1) * (V + 1) * (1 + |a|))
  have hη : 0 < η := by positivity
  filter_upwards [hP.eventually_incr_le hm hst hη] with n ⟨hn, hinc⟩
  rw [sub_zero]
  set D : ℕ → ℝ := fun k => x (unifPartIcc s t n (k + 1)) - x (unifPartIcc s t n k) -
    a * (β (unifPartIcc s t n (k + 1)) - β (unifPartIcc s t n k))
  have hDk : ∀ k < m n, |D k| ≤ η * (1 + |a|) := by
    intro k hk
    obtain ⟨h1, h2⟩ := hinc k hk
    calc |D k| ≤ |x (unifPartIcc s t n (k + 1)) - x (unifPartIcc s t n k)| +
          |a * (β (unifPartIcc s t n (k + 1)) - β (unifPartIcc s t n k))| := abs_sub _ _
      _ ≤ η + |a| * η := by rw [abs_mul]; gcongr
      _ = η * (1 + |a|) := by ring
  have hsumD : ∑ k ∈ Finset.range (m n), |D k| ≤ V := hP.sum_abs_fv_le hm hn
  calc |∑ k ∈ Finset.range (m n), f'' (x (unifPartIcc s t n k)) * D k ^ 2|
      ≤ ∑ k ∈ Finset.range (m n), |f'' (x (unifPartIcc s t n k)) * D k ^ 2| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range (m n), K * (η * (1 + |a|)) * |D k| := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hk' := Finset.mem_range.1 hk
        rw [abs_mul, abs_pow, sq, ← mul_assoc]
        have hKk : |f'' (x (unifPartIcc s t n k))| ≤ K := by
          have := hK _ (hm.mem_Icc hn hk'.le); rwa [Real.norm_eq_abs] at this
        have := hDk k hk'
        gcongr
    _ = K * (η * (1 + |a|)) * ∑ k ∈ Finset.range (m n), |D k| := by rw [Finset.mul_sum]
    _ ≤ K * (η * (1 + |a|)) * V := by gcongr
    _ ≤ (K + 1) * (η * (1 + |a|)) * (V + 1) := by gcongr <;> linarith
    _ = ε := by simp only [η]; field_simp

end Path

end InteractingSLE.LocalTime
