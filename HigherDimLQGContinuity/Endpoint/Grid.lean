import HigherDimLQGContinuity.Endpoint.Profile

/-!
# The Euclidean endpoint (packet E3), part 2: dyadic blocks and their grids

Blueprint Part C `c:def-end` (the grids of the endpoint), in the following explicit form (NA4 Details (a) A6,
F5.2d–e; the choices are recorded in the handoff `planning/handoffs/E3.md`).

* Block `k` is `[a_k, 2a_k]`, `a_k = 2^{-k}` (`endA`); its tolerance is `ε_k = √(a_k)` (`endEps`).
* The level-`q` grid of block `k` consists of the nodes `a_k + m a_k 2^{-q}`, `m ≤ 2^q` (`endNode k q m`); the
  largest level-`q'` node below the level-`q` node `m` has index `endPar q q' m = ⌊m 2^{q'} / 2^q⌋` and lies within
  `a_k 2^{-q'}` of it (`endNode_par_le`).
* The base level of block `k` is `L k`, the fine level `j` is `endLevel D k j = 2^{D(k+j)}`, where
  `D = endDexp B M = 2⌈B⌉ + ⌈M⌉ + 3` and `L = endLexp B M = D + ⌈M⌉ + 2` are computed from the constants `B, M` of
  `Prop37Shape` (the blueprint's `D_e`, `L`; the base spacing `a_k 2^{-Lk}` replaces the blueprint's relative
  dyadic spacing `≤ (c/16) a^{L+1/2}`, and the base grid need not be a subgrid of `G_0`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace HigherDimLQGContinuity

/-! ## Definitions -/

/-- `a_k = 2^{-k}`, the left end of the `k`-th dyadic block `[a_k, 2a_k]`. -/
def endA (k : ℕ) : ℝ := (1 / 2 : ℝ) ^ k

/-- The tolerance `ε_k = √(a_k)` of block `k`. -/
def endEps (k : ℕ) : ℝ := Real.sqrt (endA k)

/-- The node `a_k + m a_k 2^{-q}` (level `q`, index `m ≤ 2^q`) of block `k`. -/
def endNode (k q m : ℕ) : ℝ := endA k + m * endA (k + q)

/-- The index at level `q'` of the largest level-`q'` node below the level-`q` node `m`. -/
def endPar (q q' m : ℕ) : ℕ := m * 2 ^ q' / 2 ^ q

/-- Fine level `j` of block `k`: `2^{D(k+j)}`. -/
def endLevel (D k j : ℕ) : ℕ := 2 ^ (D * (k + j))

/-- The growth exponent of the fine levels: `D = 2⌈B⌉ + ⌈M⌉ + 3`. -/
def endDexp (B M : ℝ) : ℕ := 2 * ⌈B⌉₊ + ⌈M⌉₊ + 3

/-- The base exponent: the base level of block `k` is `L k`, `L = D + ⌈M⌉ + 2`. -/
def endLexp (B M : ℝ) : ℕ := endDexp B M + ⌈M⌉₊ + 2

/-- The tolerance `δ_j = ε_k 2^{-j-6}` of fine level `j` of block `k`. -/
def endDelta (k j : ℕ) : ℝ := endEps k * (1 / 2) ^ (j + 6)

/-! ## The block scale `a_k` and the tolerance `ε_k` -/

theorem endA_pos (k : ℕ) : 0 < endA k := by unfold endA; positivity

theorem endA_le_one (k : ℕ) : endA k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)

theorem endA_add (k q : ℕ) : endA (k + q) = endA k * endA q := pow_add _ _ _

theorem endA_mul_two_pow (k : ℕ) : endA k * 2 ^ k = 1 := by
  unfold endA
  rw [← mul_pow]
  norm_num

theorem endA_lt_one {k : ℕ} (hk : 1 ≤ k) : endA k < 1 :=
  pow_lt_one₀ (by norm_num) (by norm_num) (by omega)

theorem endA_anti {k k' : ℕ} (h : k ≤ k') : endA k' ≤ endA k :=
  pow_le_pow_of_le_one (by norm_num) (by norm_num) h

theorem endA_succ (k : ℕ) : endA (k + 1) = endA k / 2 := by
  unfold endA
  rw [pow_succ]
  ring

theorem tendsto_endA : Tendsto endA atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

theorem endEps_pos (k : ℕ) : 0 < endEps k := Real.sqrt_pos.2 (endA_pos k)

theorem endEps_sq (k : ℕ) : endEps k ^ 2 = endA k := Real.sq_sqrt (endA_pos k).le

theorem endEps_le_one (k : ℕ) : endEps k ≤ 1 := by
  unfold endEps
  rw [Real.sqrt_le_one]
  exact endA_le_one k

theorem endA_le_endEps (k : ℕ) : endA k ≤ endEps k := by
  have h0 := (endA_pos k).le
  have h1 : endA k ^ 2 ≤ endA k := by
    have := endA_le_one k
    nlinarith
  calc endA k = Real.sqrt (endA k ^ 2) := (Real.sqrt_sq h0).symm
    _ ≤ endEps k := Real.sqrt_le_sqrt h1

theorem endEps_lt_one {k : ℕ} (hk : 1 ≤ k) : endEps k < 1 := by
  unfold endEps
  rw [Real.sqrt_lt' one_pos, one_pow]
  exact endA_lt_one hk

theorem endEps_le_half {k : ℕ} (hk : 2 ≤ k) : endEps k ≤ 1 / 2 := by
  unfold endEps
  rw [Real.sqrt_le_left (by norm_num)]
  calc endA k ≤ endA 2 := endA_anti hk
    _ = (1 / 2) ^ 2 := rfl

theorem endEps_anti {k k' : ℕ} (h : k ≤ k') : endEps k' ≤ endEps k :=
  Real.sqrt_le_sqrt (endA_anti h)

theorem tendsto_endEps : Tendsto endEps atTop (𝓝 0) := by
  have h := (Real.continuous_sqrt.tendsto 0).comp tendsto_endA
  rwa [Real.sqrt_zero] at h

theorem endEps_pow_four (k : ℕ) : endEps k ^ 4 = endA k ^ 2 := by
  rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, endEps_sq]

theorem endDelta_pos (k j : ℕ) : 0 < endDelta k j := by
  unfold endDelta
  exact mul_pos (endEps_pos k) (by positivity)

theorem endDelta_le (k j : ℕ) : endDelta k j ≤ (1 / 2) ^ (j + 6) := by
  unfold endDelta
  calc endEps k * (1 / 2) ^ (j + 6) ≤ 1 * (1 / 2) ^ (j + 6) := by
        gcongr
        exact endEps_le_one k
    _ = (1 / 2) ^ (j + 6) := one_mul _

theorem endDelta_lt_eighth (k j : ℕ) : endDelta k j < 1 / 8 := by
  calc endDelta k j ≤ (1 / 2) ^ (j + 6) := endDelta_le k j
    _ ≤ (1 / 2) ^ 6 := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    _ < 1 / 8 := by norm_num

theorem le_endDelta (k j : ℕ) : (1 / 2 : ℝ) ^ (k + j + 6) ≤ endDelta k j := by
  unfold endDelta
  rw [show k + j + 6 = k + (j + 6) by ring, pow_add]
  gcongr
  exact endA_le_endEps k

/-! ## Nodes -/

theorem endNode_mem {k q m : ℕ} (hm : m ≤ 2 ^ q) : endNode k q m ∈ Icc (endA k) (2 * endA k) := by
  unfold endNode
  have h1 : 0 ≤ (m : ℝ) * endA (k + q) := mul_nonneg (Nat.cast_nonneg _) (endA_pos _).le
  have h2 : (m : ℝ) * endA (k + q) ≤ endA k := by
    rw [endA_add]
    have hm' : (m : ℝ) ≤ 2 ^ q := by exact_mod_cast hm
    calc (m : ℝ) * (endA k * endA q) ≤ 2 ^ q * (endA k * endA q) := by
          gcongr
          exact mul_nonneg (endA_pos k).le (endA_pos q).le
      _ = endA k * (endA q * 2 ^ q) := by ring
      _ = endA k := by rw [endA_mul_two_pow, mul_one]
  constructor <;> linarith

theorem endPar_le {q q' m : ℕ} (hm : m ≤ 2 ^ q) : endPar q q' m ≤ 2 ^ q' := by
  unfold endPar
  calc m * 2 ^ q' / 2 ^ q ≤ 2 ^ q * 2 ^ q' / 2 ^ q := Nat.div_le_div_right (Nat.mul_le_mul_right _ hm)
    _ = 2 ^ q' := Nat.mul_div_cancel_left _ (by positivity)

/-- The parent node lies below the node, within `a_k 2^{-q'}`. -/
theorem endNode_par_le (k q q' m : ℕ) :
    endNode k q' (endPar q q' m) ≤ endNode k q m ∧
      endNode k q m - endNode k q' (endPar q q' m) ≤ endA (k + q') := by
  set n := endPar q q' m with hn
  have hq : (0 : ℕ) < 2 ^ q := by positivity
  have h1 : n * 2 ^ q ≤ m * 2 ^ q' := Nat.div_mul_le_self _ _
  have h2 : m * 2 ^ q' < n * 2 ^ q + 2 ^ q := Nat.lt_div_mul_add hq
  have h1' : (n : ℝ) * 2 ^ q ≤ m * 2 ^ q' := by exact_mod_cast h1
  have h2' : (m : ℝ) * 2 ^ q' < n * 2 ^ q + 2 ^ q := by exact_mod_cast h2
  set A := endA k
  set x := endA q
  set y := endA q'
  have hA : 0 < A := endA_pos k
  have hx : 0 < x := endA_pos q
  have hy : 0 < y := endA_pos q'
  have hx2 : x * 2 ^ q = 1 := endA_mul_two_pow q
  have hy2 : y * 2 ^ q' = 1 := endA_mul_two_pow q'
  have hdiff : endNode k q m - endNode k q' n = A * x * y * (m * 2 ^ q' - n * 2 ^ q) := by
    unfold endNode
    rw [endA_add, endA_add]
    have e1 : A * x * y * ((m : ℝ) * 2 ^ q') = m * (A * x) * (y * 2 ^ q') := by ring
    have e2 : A * x * y * ((n : ℝ) * 2 ^ q) = n * (A * y) * (x * 2 ^ q) := by ring
    rw [mul_sub, e1, e2, hx2, hy2]
    ring
  have hAxy : 0 < A * x * y := by positivity
  constructor
  · have : 0 ≤ endNode k q m - endNode k q' n := by
      rw [hdiff]
      exact mul_nonneg hAxy.le (by linarith)
    linarith
  · rw [hdiff, endA_add]
    calc A * x * y * ((m : ℝ) * 2 ^ q' - n * 2 ^ q) ≤ A * x * y * 2 ^ q := by
          gcongr
          linarith
      _ = A * y * (x * 2 ^ q) := by ring
      _ = A * y := by rw [hx2, mul_one]

theorem abs_endNode_sub_par_le (k q q' m : ℕ) :
    |endNode k q' (endPar q q' m) - endNode k q m| ≤ endA (k + q') := by
  obtain ⟨h1, h2⟩ := endNode_par_le k q q' m
  rw [abs_sub_comm, abs_of_nonneg (by linarith)]
  exact h2

/-- Every point of block `k` is within `a_k 2^{-q}` of a level-`q` node. -/
theorem exists_endNode_near {k : ℕ} {ξ : ℝ} (hξ : ξ ∈ Icc (endA k) (2 * endA k)) (q : ℕ) :
    ∃ m ≤ 2 ^ q, |endNode k q m - ξ| ≤ endA (k + q) := by
  have he : 0 < endA (k + q) := endA_pos _
  set z := (ξ - endA k) / endA (k + q) with hz
  have hz0 : 0 ≤ z := div_nonneg (by linarith [hξ.1]) he.le
  have hz1 : z ≤ 2 ^ q := by
    rw [hz, div_le_iff₀ he, endA_add]
    have h := endA_mul_two_pow q
    calc ξ - endA k ≤ endA k := by linarith [hξ.2]
      _ = 2 ^ q * (endA k * endA q) := by
          calc endA k = endA k * (endA q * 2 ^ q) := by rw [h, mul_one]
            _ = 2 ^ q * (endA k * endA q) := by ring
  refine ⟨⌊z⌋₊, ?_, ?_⟩
  · have : (⌊z⌋₊ : ℝ) ≤ 2 ^ q := (Nat.floor_le hz0).trans hz1
    exact_mod_cast this
  · have hfl := Nat.floor_le hz0
    have hlt := Nat.lt_floor_add_one z
    have hξz : ξ = endA k + z * endA (k + q) := by
      rw [hz]
      field_simp
      ring
    unfold endNode
    rw [hξz]
    have : endA k + (⌊z⌋₊ : ℝ) * endA (k + q) - (endA k + z * endA (k + q)) =
        -((z - ⌊z⌋₊) * endA (k + q)) := by ring
    rw [this, abs_neg, abs_of_nonneg (mul_nonneg (by linarith) he.le)]
    calc (z - ⌊z⌋₊) * endA (k + q) ≤ 1 * endA (k + q) := by
          gcongr
          linarith
      _ = endA (k + q) := one_mul _

/-! ## The levels -/

theorem le_endLevel {D : ℕ} (hD : 1 ≤ D) (k j : ℕ) : k + j ≤ endLevel D k j := by
  unfold endLevel
  calc k + j ≤ D * (k + j) := Nat.le_mul_of_pos_left _ hD
    _ ≤ 2 ^ (D * (k + j)) := (Nat.lt_two_pow_self).le

theorem one_le_endLevel (D k j : ℕ) : 1 ≤ endLevel D k j := Nat.one_le_two_pow

theorem endLevel_succ (D k j : ℕ) : endLevel D k (j + 1) = 2 ^ D * endLevel D k j := by
  unfold endLevel
  rw [← pow_add]
  congr 1
  ring

theorem one_le_endDexp (B M : ℝ) : 1 ≤ endDexp B M := by unfold endDexp; omega

end HigherDimLQGContinuity
