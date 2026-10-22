import HigherDimLQGContinuity.Grid.Profile
import HigherDimLQGContinuity.Endpoint.Grid

/-!
# Parameter grids for a positive window

The level `k_j = 2^(j²)` is independent of the spatial radius.  Nodes at level `j` are the
equally spaced points of `[lo, hi]` with mesh `(hi-lo) 2^(-k_j)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set

namespace HigherDimLQGContinuity

/-- The radius-independent level `k_j = 2^(j²)`. -/
def posLevel (j : ℕ) : ℕ := 2 ^ (j * j)

/-- The mesh width `(hi-lo) 2^(-k_j)`. -/
def posWidth (lo hi : ℝ) (j : ℕ) : ℝ := (hi - lo) * endA (posLevel j)

/-- The `m`-th node at level `j`. -/
def posNode (lo hi : ℝ) (j m : ℕ) : ℝ := lo + m * posWidth lo hi j

/-- The profile tolerance `δ_j = 2^(-j-6)`. -/
def posDelta (j : ℕ) : ℝ := endA (j + 6)

/-- The floor of the depth allowed by Proposition 3.7 at mesh width `w_j`. -/
def posDepth (lo hi c : ℝ) (j : ℕ) : ℕ := ⌊c * posDelta j / posWidth lo hi j⌋₊

/-- The coarse index directly below a node of the next level. -/
def posBracket (j m : ℕ) : ℕ := endPar (posLevel (j + 1)) (posLevel j) m

theorem posLevel_mono : Monotone posLevel := by
  intro i j hij
  unfold posLevel
  exact Nat.pow_le_pow_right (by omega) (Nat.mul_self_le_mul_self hij)

theorem posWidth_pos {lo hi : ℝ} (h : lo < hi) (j : ℕ) : 0 < posWidth lo hi j :=
  mul_pos (sub_pos.2 h) (endA_pos _)

theorem posDelta_pos (j : ℕ) : 0 < posDelta j := endA_pos _

theorem posDelta_lt_eighth (j : ℕ) : posDelta j < 1 / 8 := by
  unfold posDelta
  calc endA (j + 6) ≤ endA 6 := endA_anti (by omega)
    _ < 1 / 8 := by norm_num [endA]

theorem posNode_mem {lo hi : ℝ} (h : lo < hi) {j m : ℕ}
    (hm : m ≤ 2 ^ posLevel j) : posNode lo hi j m ∈ Icc lo hi := by
  have hw : 0 < posWidth lo hi j := posWidth_pos h j
  have hm' : (m : ℝ) ≤ 2 ^ posLevel j := by exact_mod_cast hm
  have hbound : (m : ℝ) * posWidth lo hi j ≤ hi - lo := by
    unfold posWidth
    calc (m : ℝ) * ((hi - lo) * endA (posLevel j))
        ≤ 2 ^ posLevel j * ((hi - lo) * endA (posLevel j)) := by
            gcongr
      _ = hi - lo := by
          have hkey := endA_mul_two_pow (posLevel j)
          calc 2 ^ posLevel j * ((hi - lo) * endA (posLevel j))
              = (hi - lo) * (endA (posLevel j) * 2 ^ posLevel j) := by ring
            _ = hi - lo := by rw [hkey, mul_one]
  constructor
  · unfold posNode
    nlinarith [Nat.cast_nonneg (α := ℝ) m]
  · unfold posNode
    linarith

theorem posBracket_le {j m : ℕ} (hm : m ≤ 2 ^ posLevel (j + 1)) :
    posBracket j m ≤ 2 ^ posLevel j := endPar_le hm

private theorem posNode_eq_endNode {lo hi : ℝ} (j m : ℕ) :
    posNode lo hi j m = lo + (hi - lo) * (endNode 0 (posLevel j) m - 1) := by
  simp only [posNode, posWidth, endNode, endA, pow_zero, zero_add]
  ring

/-- A fine node is above its coarse bracket. -/
theorem posNode_bracket_le {lo hi : ℝ} (h : lo < hi) (j m : ℕ) :
    posNode lo hi j (posBracket j m) ≤ posNode lo hi (j + 1) m := by
  rw [posNode_eq_endNode, posNode_eq_endNode]
  unfold posBracket
  have hbase := (endNode_par_le 0 (posLevel (j + 1)) (posLevel j) m).1
  simpa only [add_comm] using
    (add_le_add_left (mul_le_mul_of_nonneg_left (sub_le_sub_right hbase 1) (sub_pos.2 h).le) lo)

/-- The fine node is no more than one coarse mesh above its bracket. -/
theorem posNode_sub_bracket_le {lo hi : ℝ} (h : lo < hi) (j m : ℕ) :
    posNode lo hi (j + 1) m - posNode lo hi j (posBracket j m) ≤ posWidth lo hi j := by
  rw [posNode_eq_endNode, posNode_eq_endNode]
  unfold posBracket
  have hbase := (endNode_par_le 0 (posLevel (j + 1)) (posLevel j) m).2
  simp only [zero_add] at hbase
  calc
    lo + (hi - lo) * (endNode 0 (posLevel (j + 1)) m - 1) -
        (lo + (hi - lo) * (endNode 0 (posLevel j)
          (endPar (posLevel (j + 1)) (posLevel j) m) - 1))
      = (hi - lo) * (endNode 0 (posLevel (j + 1)) m -
          endNode 0 (posLevel j) (endPar (posLevel (j + 1)) (posLevel j) m)) := by ring
    _ ≤ (hi - lo) * endA (posLevel j) := by gcongr
    _ = posWidth lo hi j := rfl

theorem posNode_succ (lo hi : ℝ) (j m : ℕ) :
    posNode lo hi j (m + 1) = posNode lo hi j m + posWidth lo hi j := by
  unfold posNode
  push_cast
  ring

theorem posNode_upper_mem {lo hi : ℝ} (h : lo < hi) {j m : ℕ}
    (hm : posBracket j m < 2 ^ posLevel j) :
    posNode lo hi j (posBracket j m + 1) ∈ Icc lo hi :=
  posNode_mem h (Nat.succ_le_iff.2 hm)

theorem abs_posNode_sub_upper_le {lo hi : ℝ} (h : lo < hi) (j m : ℕ) :
    |posNode lo hi (j + 1) m - posNode lo hi j (posBracket j m + 1)| ≤
      posWidth lo hi j := by
  have hlower := posNode_bracket_le h j m
  have hgap := posNode_sub_bracket_le h j m
  have hw : 0 < posWidth lo hi j := posWidth_pos h j
  rw [posNode_succ]
  rw [abs_of_nonpos (by linarith)]
  linarith

theorem pos_nat_le_two_pow (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [pow_succ]
      have hpos : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      omega

theorem pos_nat_succ_le_two_pow {n : ℕ} (hn : 1 ≤ n) : n + 1 ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n _ ih =>
      rw [pow_succ]
      omega

theorem posLevel_ge (j : ℕ) : j ≤ posLevel j := by
  unfold posLevel
  calc j ≤ j * j := by
        cases j with
        | zero => norm_num
        | succ j => nlinarith
    _ ≤ 2 ^ (j * j) := pos_nat_le_two_pow _

/-- A coarse quadratic lower bound for `2^(j²)`, sufficient for all fixed
exponential-in-`j` comparison requirements. -/
theorem posLevel_ge_two_sq {j : ℕ} (hj : 2 ≤ j) :
    2 * j ^ 2 + 1 ≤ posLevel j := by
  have hsq : 2 * j ≤ j * j := by nlinarith
  calc 2 * j ^ 2 + 1 ≤ 2 ^ (2 * j) := Nat.two_mul_sq_add_one_le_two_pow_two_mul j
    _ ≤ 2 ^ (j * j) := Nat.pow_le_pow_right (by omega) hsq
    _ = posLevel j := rfl

theorem posLevel_ge_quadratic (K : ℕ) {j : ℕ} (hj : K + 8 ≤ j) :
    (j + 1) ^ 2 + K * (j + 6) ≤ posLevel j := by
  have hbase := posLevel_ge_two_sq (by omega : 2 ≤ j)
  have hjR : (K : ℝ) + 8 ≤ j := by exact_mod_cast hj
  have hp : 0 ≤ ((j : ℝ) - (K + 8)) * ((j : ℝ) + 6) := by
    apply mul_nonneg
    · linarith
    · positivity
  have hpol : ((j + 1 : ℕ) ^ 2 + K * (j + 6) : ℕ) ≤ 2 * j ^ 2 + 1 := by
    exact_mod_cast (show ((j : ℝ) + 1) ^ 2 + (K : ℝ) * ((j : ℝ) + 6) ≤
      2 * (j : ℝ) ^ 2 + 1 by nlinarith)
  exact hpol.trans hbase

theorem posLevel_ge_pow_linear (K : ℕ) {j : ℕ} (hj : K + 8 ≤ j) :
    2 ^ (K * (j + 6)) ≤ posLevel j := by
  have hjR : (K : ℝ) + 8 ≤ j := by exact_mod_cast hj
  have hp : 0 ≤ ((j : ℝ) - (K + 8)) * ((j : ℝ) + 6) := by
    apply mul_nonneg
    · linarith
    · positivity
  have hexp : K * (j + 6) ≤ j * j := by
    exact_mod_cast (show (K : ℝ) * ((j : ℝ) + 6) ≤ (j : ℝ) * j by nlinarith)
  unfold posLevel
  exact Nat.pow_le_pow_right (by omega) hexp

theorem posLevel_succ_le_sq {j : ℕ} (hj : 3 ≤ j) :
    posLevel (j + 1) ≤ posLevel j ^ 2 := by
  have hexp : (j + 1) * (j + 1) ≤ 2 * (j * j) := by nlinarith
  unfold posLevel
  calc 2 ^ ((j + 1) * (j + 1)) ≤ 2 ^ (2 * (j * j)) :=
        Nat.pow_le_pow_right (by omega) hexp
    _ = (2 ^ (j * j)) ^ 2 := by rw [← pow_mul]; ring

theorem tendsto_posLevel : Tendsto posLevel atTop atTop :=
  Filter.tendsto_atTop_mono posLevel_ge tendsto_id

theorem tendsto_posWidth {lo hi : ℝ} : Tendsto (posWidth lo hi) atTop (𝓝 0) := by
  have h := (tendsto_endA.comp tendsto_posLevel).const_mul (hi - lo)
  change Tendsto (fun j => (hi - lo) * endA (posLevel j)) atTop (𝓝 0)
  simpa only [Function.comp_def, mul_zero] using h

/-- Every point of a window is within one mesh width of a grid node. -/
theorem exists_posNode_near {lo hi ξ : ℝ} (h : lo < hi) (hξ : ξ ∈ Icc lo hi) (j : ℕ) :
    ∃ m ≤ 2 ^ posLevel j, |posNode lo hi j m - ξ| ≤ posWidth lo hi j := by
  let ζ : ℝ := 1 + (ξ - lo) / (hi - lo)
  have hL : 0 < hi - lo := sub_pos.2 h
  have hζ : ζ ∈ Icc (endA 0) (2 * endA 0) := by
    simp only [ζ, endA, pow_zero]
    constructor
    · have : 0 ≤ (ξ - lo) / (hi - lo) := div_nonneg (sub_nonneg.2 hξ.1) hL.le
      linarith
    · have : (ξ - lo) / (hi - lo) ≤ 1 := (div_le_one hL).2 (by linarith [hξ.2])
      linarith
  obtain ⟨m, hm, hnear⟩ := exists_endNode_near hζ (posLevel j)
  refine ⟨m, hm, ?_⟩
  have hξeq : ξ = lo + (hi - lo) * (ζ - 1) := by
    dsimp [ζ]
    field_simp
    ring
  rw [posNode_eq_endNode, hξeq]
  have hkey :
      lo + (hi - lo) * (endNode 0 (posLevel j) m - 1) -
        (lo + (hi - lo) * (ζ - 1)) =
      (hi - lo) * (endNode 0 (posLevel j) m - ζ) := by ring
  rw [hkey, abs_mul, abs_of_pos hL]
  unfold posWidth
  simpa only [endA_add, zero_add, one_mul] using mul_le_mul_of_nonneg_left hnear hL.le

theorem posNode_last (lo hi : ℝ) (j : ℕ) :
    posNode lo hi j (2 ^ posLevel j) = hi := by
  unfold posNode posWidth
  have h := endA_mul_two_pow (posLevel j)
  push_cast
  calc
    lo + (2 : ℝ) ^ posLevel j * ((hi - lo) * endA (posLevel j))
      = lo + (hi - lo) * (endA (posLevel j) * (2 : ℝ) ^ posLevel j) := by ring
    _ = hi := by rw [h]; ring

/-- Every point of a window belongs to a cell of the level-`j` grid. -/
theorem exists_posNode_cell {lo hi ξ : ℝ} (h : lo < hi) (hξ : ξ ∈ Icc lo hi) (j : ℕ) :
    ∃ m < 2 ^ posLevel j,
      ξ ∈ Icc (posNode lo hi j m) (posNode lo hi j (m + 1)) := by
  let N := 2 ^ posLevel j
  let w := posWidth lo hi j
  let z := (ξ - lo) / w
  have hw : 0 < w := posWidth_pos h j
  have hN : 1 ≤ N := Nat.one_le_two_pow
  have hzw : ξ = lo + z * w := by
    dsimp [z]
    field_simp
    ring
  have hlast : posNode lo hi j N = hi := posNode_last lo hi j
  have hz0 : 0 ≤ z := div_nonneg (sub_nonneg.2 hξ.1) hw.le
  have hzN : z ≤ N := by
    rw [div_le_iff₀ hw]
    have hNW : (N : ℝ) * w = hi - lo := by
      have hh := hlast
      change lo + (N : ℝ) * w = hi at hh
      linarith
    linarith [hξ.2]
  by_cases hξhi : ξ = hi
  · refine ⟨N - 1, by omega, ?_⟩
    have hplus : N - 1 + 1 = N := by omega
    rw [hξhi, hplus, hlast]
    exact ⟨(posNode_mem h (by omega : N - 1 ≤ N)).2, le_refl _⟩
  · let m := ⌊z⌋₊
    have hmz : (m : ℝ) ≤ z := Nat.floor_le hz0
    have hzm : z < m + 1 := Nat.lt_floor_add_one z
    have hzlt : z < N := by
      have hξlt : ξ < hi := lt_of_le_of_ne hξ.2 hξhi
      dsimp [z]
      rw [div_lt_iff₀ hw]
      have hNW : (N : ℝ) * w = hi - lo := by
        have hh := hlast
        change lo + (N : ℝ) * w = hi at hh
        linarith
      linarith
    have hmN : m < N := by
      have : (m : ℝ) < N := hmz.trans_lt hzlt
      exact_mod_cast this
    refine ⟨m, hmN, ?_⟩
    constructor
    · rw [hzw]
      change lo + (m : ℝ) * w ≤ lo + z * w
      simpa only [add_comm] using
        (add_le_add_left (mul_le_mul_of_nonneg_right hmz hw.le) lo)
    · rw [hzw]
      change lo + z * w ≤ lo + ((m + 1 : ℕ) : ℝ) * w
      have hzm' : z ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast hzm.le
      simpa only [add_comm] using
        (add_le_add_left (mul_le_mul_of_nonneg_right hzm' hw.le) lo)

/-- Refinement factor from level `j` to level `j+1`. -/
def posFactor (j : ℕ) : ℕ := 2 ^ (posLevel (j + 1) - posLevel j)

theorem posFactor_pow (j : ℕ) :
    2 ^ posLevel j * posFactor j = 2 ^ posLevel (j + 1) := by
  have hlev : posLevel j ≤ posLevel (j + 1) := posLevel_mono (Nat.le_succ _)
  have hadd : posLevel j + (posLevel (j + 1) - posLevel j) = posLevel (j + 1) := by omega
  simp only [posFactor, ← pow_add, hadd]

theorem posBracket_lt_of_lt {j m : ℕ} (hm : m < 2 ^ posLevel (j + 1)) :
    posBracket j m < 2 ^ posLevel j := by
  unfold posBracket endPar
  apply (Nat.div_lt_iff_lt_mul (by positivity : 0 < 2 ^ posLevel (j + 1))).2
  have hmul := Nat.mul_lt_mul_of_pos_right hm
    (by positivity : 0 < 2 ^ posLevel j)
  simpa only [mul_comm] using hmul

theorem posBracket_next_le_factor (j m : ℕ) :
    m + 1 ≤ (posBracket j m + 1) * posFactor j := by
  have hlev : posLevel j ≤ posLevel (j + 1) := posLevel_mono (Nat.le_succ _)
  have hpow : 2 ^ posLevel (j + 1) = 2 ^ posLevel j * posFactor j := by
    simpa only [mul_comm] using (posFactor_pow j).symm
  have hdiv : m * 2 ^ posLevel j <
      posBracket j m * 2 ^ posLevel (j + 1) + 2 ^ posLevel (j + 1) :=
    Nat.lt_div_mul_add (by positivity : 0 < 2 ^ posLevel (j + 1))
  rw [hpow] at hdiv
  have hmul : m * 2 ^ posLevel j <
      ((posBracket j m + 1) * posFactor j) * 2 ^ posLevel j := by
    convert hdiv using 1; ring
  have hlt := (Nat.mul_lt_mul_right (by positivity : 0 < 2 ^ posLevel j)).1 hmul
  omega

theorem posWidth_factor (lo hi : ℝ) (j : ℕ) :
    posWidth lo hi (j + 1) * posFactor j = posWidth lo hi j := by
  have hlev : posLevel j ≤ posLevel (j + 1) := posLevel_mono (Nat.le_succ _)
  have hadd : posLevel j + (posLevel (j + 1) - posLevel j) = posLevel (j + 1) := by omega
  have hpow : endA (posLevel (j + 1)) =
      endA (posLevel j) * endA (posLevel (j + 1) - posLevel j) := by
    calc
      endA (posLevel (j + 1)) = endA (posLevel j + (posLevel (j + 1) - posLevel j)) :=
        congrArg endA hadd.symm
      _ = endA (posLevel j) * endA (posLevel (j + 1) - posLevel j) := endA_add _ _
  have hfactor := endA_mul_two_pow (posLevel (j + 1) - posLevel j)
  unfold posWidth posFactor
  rw [hpow]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  calc
    (hi - lo) * (endA (posLevel j) * endA (posLevel (j + 1) - posLevel j)) *
        2 ^ (posLevel (j + 1) - posLevel j)
      = (hi - lo) * endA (posLevel j) *
          (endA (posLevel (j + 1) - posLevel j) *
            2 ^ (posLevel (j + 1) - posLevel j)) := by ring
    _ = (hi - lo) * endA (posLevel j) := by rw [hfactor, mul_one]

/-- A fine grid cell lies within the coarse cell indexed by its left endpoint. -/
theorem posFineCell_mem_coarse {lo hi : ℝ} (h : lo < hi) (j m : ℕ) :
    posNode lo hi (j + 1) m ∈
      Icc (posNode lo hi j (posBracket j m))
        (posNode lo hi j (posBracket j m + 1)) ∧
    posNode lo hi (j + 1) (m + 1) ∈
      Icc (posNode lo hi j (posBracket j m))
        (posNode lo hi j (posBracket j m + 1)) := by
  have hw := posWidth_pos h (j + 1)
  have hfac := posWidth_factor lo hi j
  have hidx := posBracket_next_le_factor j m
  have hidxR : ((m + 1 : ℕ) : ℝ) ≤
      ((posBracket j m + 1 : ℕ) : ℝ) * posFactor j := by
    exact_mod_cast hidx
  have hupper : posNode lo hi (j + 1) (m + 1) ≤
      posNode lo hi j (posBracket j m + 1) := by
    unfold posNode
    push_cast at *
    nlinarith [mul_le_mul_of_nonneg_right hidxR hw.le]
  have hlower := posNode_bracket_le h j m
  have hfmono : posNode lo hi (j + 1) m ≤ posNode lo hi (j + 1) (m + 1) := by
    unfold posNode
    push_cast
    nlinarith [hw]
  exact ⟨⟨hlower, hfmono.trans hupper⟩, ⟨hlower.trans hfmono, hupper⟩⟩

theorem posNode_refine (lo hi : ℝ) (j m : ℕ) :
    posNode lo hi (j + 1) (m * posFactor j) = posNode lo hi j m := by
  unfold posNode
  rw [Nat.cast_mul]
  have h := posWidth_factor lo hi j
  calc
    lo + (m : ℝ) * (posFactor j : ℝ) * posWidth lo hi (j + 1)
      = lo + (m : ℝ) * (posWidth lo hi (j + 1) * posFactor j) := by ring
    _ = lo + (m : ℝ) * posWidth lo hi j := by rw [h]

theorem posRefine_le {j m : ℕ} (hm : m ≤ 2 ^ posLevel j) :
    m * posFactor j ≤ 2 ^ posLevel (j + 1) := by
  calc m * posFactor j ≤ 2 ^ posLevel j * posFactor j := Nat.mul_le_mul_right _ hm
    _ = 2 ^ posLevel (j + 1) := posFactor_pow j

theorem exists_posNode_refine {lo hi : ℝ} {j i m : ℕ} (hji : j ≤ i)
    (hm : m ≤ 2 ^ posLevel j) :
    ∃ n ≤ 2 ^ posLevel i, posNode lo hi i n = posNode lo hi j m := by
  induction i, hji using Nat.le_induction with
  | base => exact ⟨m, hm, rfl⟩
  | succ i _ ih =>
      obtain ⟨n, hn, heq⟩ := ih
      exact ⟨n * posFactor i, posRefine_le hn, (posNode_refine lo hi i n).trans heq⟩

theorem posDepth_drift {lo hi c : ℝ} (h : lo < hi) (hc : 0 ≤ c) (j : ℕ) :
    posWidth lo hi j * (posDepth lo hi c j : ℝ) ≤ c * posDelta j := by
  have hw : 0 < posWidth lo hi j := posWidth_pos h j
  have hx : 0 ≤ c * posDelta j / posWidth lo hi j :=
    div_nonneg (mul_nonneg hc (posDelta_pos j).le) hw.le
  have hfl := Nat.floor_le hx
  unfold posDepth at hfl ⊢
  have h := mul_le_mul_of_nonneg_left hfl hw.le
  rw [mul_div_cancel₀ _ hw.ne'] at h
  simpa only [mul_comm] using h

theorem posDepth_half {lo hi c : ℝ} (h : lo < hi) (j : ℕ)
    (hx : 2 ≤ c * posDelta j / posWidth lo hi j) :
    c * posDelta j / (2 * posWidth lo hi j) ≤ (posDepth lo hi c j : ℝ) := by
  have hfl := Nat.lt_floor_add_one (c * posDelta j / posWidth lo hi j)
  have hw : 0 < posWidth lo hi j := posWidth_pos h j
  have hcast :
      (posDepth lo hi c j : ℝ) = (⌊c * posDelta j / posWidth lo hi j⌋₊ : ℝ) := rfl
  rw [hcast]
  have : c * posDelta j / (2 * posWidth lo hi j) =
      (c * posDelta j / posWidth lo hi j) / 2 := by ring
  rw [this]
  linarith

end HigherDimLQGContinuity
