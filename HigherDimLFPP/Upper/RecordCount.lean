import HigherDimLFPP.Upper.Records
import Mathlib.Data.List.GetD

/-!
# Counting records: HA3 D6 (i), the finite record set, and the chain counting of D7

Source: `source/higher-dimensional-lfpp-limit.pdf`, §4.3, Lemma 4.4 (the counts (4.17) and
`C_{n,d} δ^{-4d}`) and §4.4 (the generating functions (4.21)–(4.22)), as corrected by the planning
audit HA3 (`planning/audits/HA3-section-4.md`), Details D6 (i) and the counting paragraph of D7;
fix F1 (the counted records are the valid ones, whose families carry the length constraints).

2D source: `LQGDimension/LFPP/RecordsAux1.lean` (`gridBox`, `card_gridBox_le`) and
`RecordsAux4.lean` (`ballSet`, `tgtSet`, `card_tgtSet_le`, `count_le`, `recSet`), with grids
`ℤ²` replaced by `ℤ^d`; the chain counting is `LQGDimension.ChainUnion.sum_chain_le`
(`LQGDimension/LFPP/ChainUnionAux.lean`), reused as is.

Main results (namespace `HigherDimLFPP.Upper`):

* `card_cubeBox_le`: at most `(2r/s + 2)^d` lattice cubes of side `s` meet a closed ball of
  radius `r`;
* **D6 (i)**: `card_filter_good_le` / `goodRecs_finite`, `ncard_goodRecs_le`: at most
  `N_g(k) = 3K (c_d K √(k+1))^{2d}` (`Ng`, `c_d = 10 + 4√d`) valid good records have a given
  location and bin `k`; `card_filter_bad_le` / `badRecs_finite`, `ncard_badRecs_le`: at most
  `N_b = 3 (c'_d/δ)^{2d} (c'_d K/δ)^{2d}` (`Nb`, `c'_d = 4ρ₀ + 4√d + 2`) valid bad records have a
  given location (`0 < δ ≤ 1`, implied by the standing `δ ≤ 1/(16√d K)`);
* the finite record set `recSet d n δ ε` of a cutoff `ε`: valid records with scale indices in
  `[0, ⌊log₂(2K/ε)⌋]`, cube indices in a box containing every cube that meets `[-2, 2]^d` at
  these scales, and bins `k ≤ ⌊a₀/δ²⌋`;
* **chain counting** (`sum_chain_weight_le`): for weights `w(ρ)` depending only on the type and
  the bin, `Σ_{chain records of length l} Π_i w(ρ_i) ≤ (Z_g + Z_b)^l` with
  `Z_g = Σ_k N_g(k) w_g(k)` and `Z_b = N_b w_b`; summed over the lengths `l ≤ M`,
  `Σ_{l ≤ M} Z^l ≤ (1 + Z)^M` (`sum_range_pow_le_one_add_pow`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped RealInnerProductSpace

namespace HigherDimLFPP.Upper

/-! ## Lattice cubes meeting a ball -/

section CubeBox

variable {d : ℕ}

/-- The integer vectors `p` whose lattice cube `s (p + [0,1)^d)` may meet the closed ball
`B̄(c, r)`: `p_i ∈ [⌊(c_i - r)/s⌋, ⌊(c_i + r)/s⌋]`. -/
def cubeBox (s : ℝ) (c : Rd d) (r : ℝ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset fun i => Finset.Icc ⌊(c i - r) / s⌋ ⌊(c i + r) / s⌋

theorem abs_apply_sub_le (z c : Rd d) (i : Fin d) : |z i - c i| ≤ ‖z - c‖ := by
  have := PiLp.norm_apply_le (z - c) i
  rwa [Real.norm_eq_abs] at this

theorem cubeIdx_mem_cubeBox {s : ℝ} (hs : 0 < s) {c z : Rd d} {r : ℝ} (h : ‖z - c‖ ≤ r) :
    cubeIdx s z ∈ cubeBox s c r := by
  rw [cubeBox, Fintype.mem_piFinset]
  intro i
  have hi := (abs_apply_sub_le z c i).trans h
  rw [abs_le] at hi
  rw [Finset.mem_Icc]
  constructor
  · exact Int.floor_mono (div_le_div_of_nonneg_right (by linarith) hs.le)
  · exact Int.floor_mono (div_le_div_of_nonneg_right (by linarith) hs.le)

theorem card_Icc_floor_le {a b : ℝ} (h : a ≤ b) :
    ((Finset.Icc ⌊a⌋ ⌊b⌋).card : ℝ) ≤ b - a + 2 := by
  have hab : ⌊a⌋ ≤ ⌊b⌋ := Int.floor_mono h
  rw [Int.card_Icc]
  have hm : 0 ≤ ⌊b⌋ + 1 - ⌊a⌋ := by omega
  have e : (((⌊b⌋ + 1 - ⌊a⌋).toNat : ℕ) : ℝ) = ((⌊b⌋ + 1 - ⌊a⌋ : ℤ) : ℝ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hm]
  rw [e]
  push_cast
  have h1 := Int.floor_le b
  have h2 := Int.sub_one_lt_floor a
  linarith

/-- At most `(2r/s + 2)^d` lattice cubes of side `s` meet a closed ball of radius `r`. -/
theorem card_cubeBox_le {s : ℝ} (hs : 0 < s) (c : Rd d) {r : ℝ} (hr : 0 ≤ r) :
    ((cubeBox s c r).card : ℝ) ≤ (2 * r / s + 2) ^ d := by
  rw [cubeBox, Fintype.card_piFinset, Nat.cast_prod]
  calc ∏ i, ((Finset.Icc ⌊(c i - r) / s⌋ ⌊(c i + r) / s⌋).card : ℝ)
      ≤ ∏ _i : Fin d, (2 * r / s + 2) := by
        refine Finset.prod_le_prod₀ (fun i _ => Nat.cast_nonneg _) fun i _ => ?_
        have hle : (c i - r) / s ≤ (c i + r) / s :=
          div_le_div_of_nonneg_right (by linarith) hs.le
        calc _ ≤ (c i + r) / s - (c i - r) / s + 2 := card_Icc_floor_le hle
          _ = 2 * r / s + 2 := by ring
    _ = (2 * r / s + 2) ^ d := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end CubeBox

/-! ## The constants of D6 (i) -/

/-- `c_d = 10 + 4√d` (HA3 D6 (i)). -/
def cGood (d : ℕ) : ℝ := 10 + 4 * Real.sqrt d

/-- `N_g(k) = 3K (c_d K √(k+1))^{2d}` with `K = 2ⁿ` (HA3 D6 (i); the paper's `e^{C_d n}(k+1)^d`,
(4.17)). -/
def Ng (d n k : ℕ) : ℝ := 3 * 2 ^ n * (cGood d * 2 ^ n * Real.sqrt ((k : ℝ) + 1)) ^ (2 * d)

/-- `c'_d = 4ρ₀ + 4√d + 2` with `ρ₀ = max(4, 2√d)` (an explicit choice of HA3's `c'_d`). -/
def cBad (d : ℕ) : ℝ := 4 * rho0 d + 4 * Real.sqrt d + 2

/-- `N_b = 3 (c'_d/δ)^{2d} (c'_d K/δ)^{2d}` with `K = 2ⁿ` (HA3 D6 (i); the paper's
`C_{n,d} δ^{-4d}`). -/
def Nb (d n : ℕ) (δ : ℝ) : ℝ := 3 * (cBad d / δ) ^ (2 * d) * (cBad d * 2 ^ n / δ) ^ (2 * d)

theorem cGood_pos (d : ℕ) : 0 < cGood d := by unfold cGood; positivity

theorem cBad_pos (d : ℕ) : 0 < cBad d := by
  have := rho0_pos d; unfold cBad; positivity

theorem Ng_nonneg (d n k : ℕ) : 0 ≤ Ng d n k := by
  have := cGood_pos d; unfold Ng; positivity

theorem Nb_nonneg (d n : ℕ) {δ : ℝ} (hδ : 0 < δ) : 0 ≤ Nb d n δ := by
  have := cBad_pos d; unfold Nb; positivity

/-- The standing assumption `δ ≤ 1/(16√d K)` of HA3 D6 implies `δ ≤ 1`. -/
theorem le_one_of_le_inv {d n : ℕ} [NeZero d] {δ : ℝ}
    (hδ : δ ≤ 1 / (16 * Real.sqrt d * 2 ^ n)) : δ ≤ 1 := by
  have hd : (1 : ℝ) ≤ d := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne d)
  have hs : 1 ≤ Real.sqrt d := by rw [Real.one_le_sqrt]; exact hd
  have h2 : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  have h16 : 1 ≤ 16 * Real.sqrt d * 2 ^ n := by nlinarith
  calc δ ≤ 1 / (16 * Real.sqrt d * 2 ^ n) := hδ
    _ ≤ 1 := by rw [div_le_one (by linarith)]; exact h16

/-! ## Good records: the count `N_g(k)` -/

section GoodCount

variable {d : ℕ}

/-- The predicted position `c_p + (i/K)(c_q - c_p)` of the vertex `z_i` of a good polygon whose
parent chord has location `λ = (j, p, q)`; `c_p, c_q` are the corners of `Q_j(p)`, `Q_j(q)`. -/
def predPt (n : ℕ) (δ : ℝ) (l : Loc d) (i : ℕ) : Rd d :=
  corner (side δ l.1) l.2.1 +
    ((i : ℝ) / 2 ^ n) • (corner (side δ l.1) l.2.2 - corner (side δ l.1) l.2.1)

/-- The radius `(2√(k+1) + √d) δ 2^{-j}` of the vertex uncertainty in bin `k`. -/
def goodRad (d : ℕ) (δ : ℝ) (j : ℤ) (k : ℕ) : ℝ :=
  (2 * Real.sqrt ((k : ℝ) + 1) + Real.sqrt d) * side δ j

/-- The vertices of the polygons of a good family lie within `goodRad` of their predicted
positions (HA3 D6 (i): D4 (c) and the uncertainty of the parent endpoints in their cubes). -/
theorem goodFam_vertex_near {n : ℕ} {δ : ℝ} (hδ : 0 < δ) {g : GoodRec d} {c : Config d}
    (hc : c ∈ goodFam n δ g) {i : ℕ} (hi : i ≤ 2 ^ n) :
    ‖c.2.getD i 0 - predPt n δ g.loc i‖ ≤ goodRad d δ g.loc.1 g.bin := by
  obtain ⟨x, y, -, hloc, hQ, -, hbin, -, -⟩ := hc
  set s := side δ g.loc.1 with hsdef
  have hs : 0 < s := side_pos hδ _
  have hxy := hloc.ne
  have hRle : ‖y - x‖ ≤ (2 : ℝ) ^ (-g.loc.1) := hloc.2.1
  have hx := norm_sub_corner_le hs hloc.2.2.1
  have hy := norm_sub_corner_le hs hloc.2.2.2
  have hlen : c.2.length = 2 ^ n + 1 := hQ.1
  have hvc := goodFamily_vertex_close hQ hxy (a0_le_one n) i (by omega)
  rw [← List.getD_eq_getElem c.2 0 (by omega)] at hvc
  have hsqrt : Real.sqrt (Real.log (polyLen c.2 / ‖y - x‖)) ≤
      δ * Real.sqrt ((g.bin : ℝ) + 1) := by
    calc Real.sqrt (Real.log (polyLen c.2 / ‖y - x‖))
        ≤ Real.sqrt (((g.bin : ℝ) + 1) * δ ^ 2) := Real.sqrt_le_sqrt hbin.le
      _ = δ * Real.sqrt ((g.bin : ℝ) + 1) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hδ.le, mul_comm]
  have hcast : ((2 ^ n : ℕ) : ℝ) = (2 : ℝ) ^ n := by push_cast; ring
  rw [hcast] at hvc
  have hvc' : ‖c.2.getD i 0 - x - ((i : ℝ) / 2 ^ n) • (y - x)‖ ≤
      2 * Real.sqrt ((g.bin : ℝ) + 1) * s := by
    calc _ ≤ 2 * ‖y - x‖ * Real.sqrt (Real.log (polyLen c.2 / ‖y - x‖)) := hvc
      _ ≤ 2 * (2 : ℝ) ^ (-g.loc.1) * (δ * Real.sqrt ((g.bin : ℝ) + 1)) := by gcongr
      _ = 2 * Real.sqrt ((g.bin : ℝ) + 1) * s := by rw [hsdef, side]; ring
  set t : ℝ := (i : ℝ) / 2 ^ n with ht
  have ht0 : 0 ≤ t := by positivity
  have ht1 : t ≤ 1 := by
    rw [ht, div_le_one (by positivity)]; exact_mod_cast hi
  have e : c.2.getD i 0 - predPt n δ g.loc i =
      (c.2.getD i 0 - x - t • (y - x)) + ((1 - t) • (x - corner s g.loc.2.1) +
        t • (y - corner s g.loc.2.2)) := by
    simp only [predPt, ← hsdef, ← ht]; module
  have hcorner : ‖(1 - t) • (x - corner s g.loc.2.1) + t • (y - corner s g.loc.2.2)‖ ≤
      Real.sqrt d * s := by
    calc _ ≤ ‖(1 - t) • (x - corner s g.loc.2.1)‖ + ‖t • (y - corner s g.loc.2.2)‖ :=
          norm_add_le _ _
      _ = (1 - t) * ‖x - corner s g.loc.2.1‖ + t * ‖y - corner s g.loc.2.2‖ := by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith), Real.norm_of_nonneg ht0]
      _ ≤ (1 - t) * (Real.sqrt d * s) + t * (Real.sqrt d * s) :=
          add_le_add (mul_le_mul_of_nonneg_left hx (by linarith))
            (mul_le_mul_of_nonneg_left hy ht0)
      _ = Real.sqrt d * s := by ring
  rw [e]
  calc _ ≤ ‖c.2.getD i 0 - x - t • (y - x)‖ +
        ‖(1 - t) • (x - corner s g.loc.2.1) + t • (y - corner s g.loc.2.2)‖ := norm_add_le _ _
    _ ≤ 2 * Real.sqrt ((g.bin : ℝ) + 1) * s + Real.sqrt d * s := add_le_add hvc' hcorner
    _ = goodRad d δ g.loc.1 g.bin := by rw [goodRad]; ring

/-- The candidate good records with location `λ` and bin `k` (HA3 D6 (i)): followed-child index
`ι < K`, next scale `j' ∈ {j+n-1, j+n, j+n+1}`, and the cubes of `z_ι, z_{ι+1}` at scale `j'`
among those meeting the balls of radius `goodRad` around the predicted positions. -/
def goodTargets (n : ℕ) (δ : ℝ) (l : Loc d) (k : ℕ) : Finset (Record d) :=
  (Finset.range (2 ^ n)).biUnion fun ι =>
    (Finset.Icc (l.1 + n - 1) (l.1 + n + 1)).biUnion fun j' =>
      (cubeBox (side δ j') (predPt n δ l ι) (goodRad d δ l.1 k) ×ˢ
        cubeBox (side δ j') (predPt n δ l (ι + 1)) (goodRad d δ l.1 k)).image fun pq =>
          (Sum.inl ⟨k, ι, l, (j', pq.1, pq.2)⟩ : Record d)

/-- Every valid good record is a candidate for its location and bin. -/
theorem mem_goodTargets {n : ℕ} {δ : ℝ} (hδ : 0 < δ) {g : GoodRec d}
    (hg : RecValid n δ (Sum.inl g : Record d)) :
    (Sum.inl g : Record d) ∈ goodTargets n δ g.loc g.bin := by
  obtain ⟨⟨c, hc⟩, hidx, hstep⟩ := hg
  have hc' := hc
  obtain ⟨x, y, -, -, hQ, -, -, -, hnext⟩ := hc'
  have hlen : c.2.length = 2 ^ n + 1 := hQ.1
  have hs := side_pos hδ g.next.1
  have hp := (mem_latCube_iff hs).1 hnext.2.2.1
  have hq := (mem_latCube_iff hs).1 hnext.2.2.2
  unfold ScaleStep at hstep
  simp only [goodTargets, Finset.mem_biUnion, Finset.mem_range, Finset.mem_Icc, Finset.mem_image,
    Finset.mem_product]
  refine ⟨g.idx, hidx, g.next.1, ⟨by omega, by omega⟩, (g.next.2.1, g.next.2.2), ⟨?_, ?_⟩, rfl⟩
  · rw [← hp]
    exact cubeIdx_mem_cubeBox hs (goodFam_vertex_near hδ hc (by omega))
  · rw [← hq]
    exact cubeIdx_mem_cubeBox hs (goodFam_vertex_near hδ hc (by omega))

theorem side_add_succ (δ : ℝ) (j : ℤ) (n : ℕ) :
    side δ (j + n + 1) = side δ j / (2 * 2 ^ n) := by
  have e : -(j + n + 1) = -j - ((n + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [side, side, e, two_zpow_sub_natCast, pow_succ]
  ring

/-- The scale step bounds the next lattice side from below: `side δ j' ≥ side δ j / (2K)`. -/
theorem side_div_le {δ : ℝ} (hδ : 0 ≤ δ) {j j' : ℤ} {n : ℕ} (h : j' ≤ j + n + 1) :
    side δ j / (2 * 2 ^ n) ≤ side δ j' := by
  rw [← side_add_succ]
  exact side_anti hδ h

theorem card_Icc_three (a : ℤ) (n : ℕ) :
    (Finset.Icc (a + n - 1) (a + n + 1)).card = 3 := by
  rw [Int.card_Icc]
  have e : a + n + 1 + 1 - (a + n - 1) = 3 := by ring
  rw [e]
  rfl

/-- The lattice-count factor of a good record: `(2r/s' + 2) ≤ c_d K √(k+1)` for the cubes at the
next scale. -/
theorem goodBox_factor_le {n : ℕ} {δ : ℝ} (hδ : 0 < δ) {j j' : ℤ} (hj' : j' ≤ j + n + 1)
    (k : ℕ) :
    2 * goodRad d δ j k / side δ j' + 2 ≤ cGood d * 2 ^ n * Real.sqrt ((k : ℝ) + 1) := by
  have hs := side_pos hδ j
  have hs' := side_pos hδ j'
  have hK : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  have hσ : (1 : ℝ) ≤ Real.sqrt ((k : ℝ) + 1) := by
    rw [Real.one_le_sqrt]; have := (Nat.cast_nonneg k : (0 : ℝ) ≤ k); linarith
  have hτ : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
  have hr : 0 ≤ goodRad d δ j k := by unfold goodRad; positivity
  have h1 : 2 * goodRad d δ j k / side δ j' ≤ 2 * goodRad d δ j k / (side δ j / (2 * 2 ^ n)) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (side_div_le hδ.le hj')
  have h2 : 2 * goodRad d δ j k / (side δ j / (2 * 2 ^ n)) =
      4 * 2 ^ n * (2 * Real.sqrt ((k : ℝ) + 1) + Real.sqrt d) := by
    rw [goodRad]; field_simp; ring
  rw [h2] at h1
  have h3 : 4 * 2 ^ n * (2 * Real.sqrt ((k : ℝ) + 1) + Real.sqrt d) + 2 ≤
      cGood d * 2 ^ n * Real.sqrt ((k : ℝ) + 1) := by
    unfold cGood
    have hKσ : 1 ≤ (2 : ℝ) ^ n * Real.sqrt ((k : ℝ) + 1) := by nlinarith
    have : 0 ≤ (2 : ℝ) ^ n * Real.sqrt d * (Real.sqrt ((k : ℝ) + 1) - 1) :=
      mul_nonneg (by positivity) (by linarith)
    nlinarith
  linarith

/-- The number of candidate good records with a given location and bin is at most `N_g(k)`. -/
theorem card_goodTargets_le {n : ℕ} {δ : ℝ} (hδ : 0 < δ) (l : Loc d) (k : ℕ) :
    ((goodTargets n δ l k).card : ℝ) ≤ Ng d n k := by
  set M : ℝ := (cGood d * 2 ^ n * Real.sqrt ((k : ℝ) + 1)) ^ d with hM
  have hr : 0 ≤ goodRad d δ l.1 k := by
    have := side_pos hδ l.1; unfold goodRad; positivity
  have hbox : ∀ j' ∈ Finset.Icc (l.1 + n - 1) (l.1 + n + 1), ∀ c : Rd d,
      ((cubeBox (side δ j') c (goodRad d δ l.1 k)).card : ℝ) ≤ M := by
    intro j' hj' c
    rw [Finset.mem_Icc] at hj'
    calc _ ≤ (2 * goodRad d δ l.1 k / side δ j' + 2) ^ d := card_cubeBox_le (side_pos hδ _) c hr
      _ ≤ M := by
        have h0 : 0 ≤ 2 * goodRad d δ l.1 k / side δ j' + 2 := by
          have := side_pos hδ j'; positivity
        exact pow_le_pow_left₀ h0 (goodBox_factor_le hδ hj'.2 k) d
  have hM0 : 0 ≤ M := by have := cGood_pos d; positivity
  calc ((goodTargets n δ l k).card : ℝ)
      ≤ ∑ ι ∈ Finset.range (2 ^ n), ∑ j' ∈ Finset.Icc (l.1 + n - 1) (l.1 + n + 1),
          (((cubeBox (side δ j') (predPt n δ l ι) (goodRad d δ l.1 k) ×ˢ
            cubeBox (side δ j') (predPt n δ l (ι + 1)) (goodRad d δ l.1 k)).card : ℕ) : ℝ) := by
        unfold goodTargets
        refine (Nat.cast_le.2 Finset.card_biUnion_le).trans ?_
        push_cast
        refine Finset.sum_le_sum fun ι _ => ?_
        refine (Nat.cast_le.2 Finset.card_biUnion_le).trans ?_
        push_cast
        exact Finset.sum_le_sum fun j' _ => Nat.cast_le.2 Finset.card_image_le
    _ ≤ ∑ _ι ∈ Finset.range (2 ^ n), ∑ _j' ∈ Finset.Icc (l.1 + n - 1) (l.1 + n + 1), M * M := by
        refine Finset.sum_le_sum fun ι _ => Finset.sum_le_sum fun j' hj' => ?_
        rw [Finset.card_product, Nat.cast_mul]
        exact mul_le_mul (hbox j' hj' _) (hbox j' hj' _) (Nat.cast_nonneg _) hM0
    _ = Ng d n k := by
        rw [Finset.sum_const, Finset.sum_const, card_Icc_three, Finset.card_range, nsmul_eq_mul,
          nsmul_eq_mul, Ng, hM, pow_mul]
        push_cast
        ring

end GoodCount

/-! ## Bad records: the count `N_b` -/

section BadCount

variable {d : ℕ}

/-- The radius `(ρ₀ + √d δ) 2^{-j}`: every endpoint of a child chord (adverse or followed) of a
parent chord of location `(j, p, q)` lies within this distance of the corner of `Q_j(p)`. -/
def badRad (d : ℕ) (δ : ℝ) (j : ℤ) : ℝ := (rho0 d + Real.sqrt d * δ) * (2 : ℝ) ^ (-j)

/-- Endpoints of child chords are near the parent's start cube. -/
theorem norm_sub_corner_le_badRad {δ : ℝ} (hδ : 0 < δ) {l : Loc d} {x y z : Rd d}
    (hloc : HasLoc δ l x y) (hz : ‖z - x‖ ≤ rho0 d * ‖y - x‖) :
    ‖z - corner (side δ l.1) l.2.1‖ ≤ badRad d δ l.1 := by
  have hx := norm_sub_corner_le (side_pos hδ l.1) hloc.2.2.1
  have hR : ‖y - x‖ ≤ (2 : ℝ) ^ (-l.1) := hloc.2.1
  have hρ := rho0_pos d
  calc ‖z - corner (side δ l.1) l.2.1‖
      ≤ ‖z - x‖ + ‖x - corner (side δ l.1) l.2.1‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ rho0 d * (2 : ℝ) ^ (-l.1) + Real.sqrt d * side δ l.1 :=
        add_le_add (hz.trans (mul_le_mul_of_nonneg_left hR hρ.le)) hx
    _ = badRad d δ l.1 := by rw [badRad, side]; ring

/-- The candidate bad records with location `λ = (j, p, q)` (HA3 D6 (i)): adverse cubes at scale
`j` and followed-child cubes at the next scale `j' ∈ {j+n-1, j+n, j+n+1}`, all meeting the ball of
radius `badRad` around the corner of `Q_j(p)`. -/
def badTargets (n : ℕ) (δ : ℝ) (l : Loc d) : Finset (Record d) :=
  (cubeBox (side δ l.1) (corner (side δ l.1) l.2.1) (badRad d δ l.1) ×ˢ
    cubeBox (side δ l.1) (corner (side δ l.1) l.2.1) (badRad d δ l.1)).biUnion fun pq =>
  (Finset.Icc (l.1 + n - 1) (l.1 + n + 1)).biUnion fun j' =>
    (cubeBox (side δ j') (corner (side δ l.1) l.2.1) (badRad d δ l.1) ×ˢ
      cubeBox (side δ j') (corner (side δ l.1) l.2.1) (badRad d δ l.1)).image fun pq' =>
        (Sum.inr ⟨l, pq.1, pq.2, (j', pq'.1, pq'.2)⟩ : Record d)

theorem mem_badFam_pair {n : ℕ} {δ : ℝ} {b : BadRec d} {x y x' y' : Rd d}
    (h : ([x, y], [x', y']) ∈ badFam n δ b) :
    HasLoc δ b.loc x y ∧ x' ∈ Qcube δ b.loc.1 b.advP ∧ y' ∈ Qcube δ b.loc.1 b.advQ ∧
      ChildChord n x y x' y' := by
  obtain ⟨x₀, y₀, x₀', y₀', he, h1, h2, h3, h4⟩ := h
  simp only [Prod.mk.injEq, List.cons.injEq, and_true] at he
  obtain ⟨⟨rfl, rfl⟩, rfl, rfl⟩ := he
  exact ⟨h1, h2, h3, h4⟩

/-- Every valid bad record is a candidate for its location. -/
theorem mem_badTargets {n : ℕ} {δ : ℝ} (hδ : 0 < δ) {b : BadRec d}
    (hb : RecValid n δ (Sum.inr b : Record d)) :
    (Sum.inr b : Record d) ∈ badTargets n δ b.loc := by
  obtain ⟨-, hstep, x, y, x', y', x₁, y₁, hfam, hnext, hch⟩ := hb
  obtain ⟨hloc, hx', hy', hadv⟩ := mem_badFam_pair hfam
  have hs := side_pos hδ b.loc.1
  have hs' := side_pos hδ b.next.1
  unfold ScaleStep at hstep
  simp only [badTargets, Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_image,
    Finset.mem_product]
  refine ⟨(b.advP, b.advQ), ⟨?_, ?_⟩, b.next.1, ⟨by omega, by omega⟩,
    (b.next.2.1, b.next.2.2), ⟨?_, ?_⟩, rfl⟩
  · rw [← (mem_latCube_iff hs).1 hx']
    exact cubeIdx_mem_cubeBox hs (norm_sub_corner_le_badRad hδ hloc hadv.2.2.1)
  · rw [← (mem_latCube_iff hs).1 hy']
    exact cubeIdx_mem_cubeBox hs (norm_sub_corner_le_badRad hδ hloc hadv.2.2.2)
  · rw [← (mem_latCube_iff hs').1 hnext.2.2.1]
    exact cubeIdx_mem_cubeBox hs' (norm_sub_corner_le_badRad hδ hloc hch.2.2.1)
  · rw [← (mem_latCube_iff hs').1 hnext.2.2.2]
    exact cubeIdx_mem_cubeBox hs' (norm_sub_corner_le_badRad hδ hloc hch.2.2.2)

/-- The number of candidate bad records with a given location is at most `N_b`, for
`0 < δ ≤ 1`. -/
theorem card_badTargets_le {n : ℕ} {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (l : Loc d) :
    ((badTargets n δ l).card : ℝ) ≤ Nb d n δ := by
  set s := side δ l.1 with hsdef
  set c := corner s l.2.1 with hc
  set r := badRad d δ l.1 with hrdef
  set M₁ : ℝ := (cBad d / δ) ^ d with hM₁
  set M₂ : ℝ := (cBad d * 2 ^ n / δ) ^ d with hM₂
  have hs : 0 < s := side_pos hδ _
  have hρ := rho0_pos d
  have hτ : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
  have hK : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  have hr : 0 ≤ r := by rw [hrdef, badRad]; positivity
  have hrs : 2 * r / s = 2 * (rho0 d + Real.sqrt d * δ) / δ := by
    rw [hrdef, hsdef, badRad, side]; field_simp
  have hM₁0 : 0 ≤ M₁ := by have := cBad_pos d; positivity
  have hM₂0 : 0 ≤ M₂ := by have := cBad_pos d; positivity
  have hbox₁ : ((cubeBox s c r).card : ℝ) ≤ M₁ := by
    refine (card_cubeBox_le hs c hr).trans (pow_le_pow_left₀ (by positivity) ?_ d)
    rw [hrs, le_div_iff₀ hδ, cBad]
    have e : (2 * (rho0 d + Real.sqrt d * δ) / δ + 2) * δ =
        2 * rho0 d + (2 * Real.sqrt d + 2) * δ := by field_simp; ring
    rw [e]
    nlinarith
  have hbox₂ : ∀ j' ∈ Finset.Icc (l.1 + n - 1) (l.1 + n + 1),
      ((cubeBox (side δ j') c r).card : ℝ) ≤ M₂ := by
    intro j' hj'
    rw [Finset.mem_Icc] at hj'
    have hs' := side_pos hδ j'
    refine (card_cubeBox_le hs' c hr).trans (pow_le_pow_left₀ (by positivity) ?_ d)
    have h1 : 2 * r / side δ j' ≤ 2 * r / (s / (2 * 2 ^ n)) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (side_div_le hδ.le hj'.2)
    have h2 : 2 * r / (s / (2 * 2 ^ n)) = 4 * 2 ^ n * (rho0 d + Real.sqrt d * δ) / δ := by
      rw [hrdef, hsdef, badRad, side]; field_simp; ring
    rw [h2] at h1
    have h3 : 4 * 2 ^ n * (rho0 d + Real.sqrt d * δ) / δ + 2 ≤ cBad d * 2 ^ n / δ := by
      rw [div_add' _ _ _ hδ.ne', div_le_div_iff_of_pos_right hδ, cBad]
      have : 0 ≤ (2 : ℝ) ^ n * Real.sqrt d * (1 - δ) := mul_nonneg (by positivity) (by linarith)
      nlinarith
    linarith
  calc ((badTargets n δ l).card : ℝ)
      ≤ ∑ pq ∈ cubeBox s c r ×ˢ cubeBox s c r, ∑ j' ∈ Finset.Icc (l.1 + n - 1) (l.1 + n + 1),
          (((cubeBox (side δ j') c r ×ˢ cubeBox (side δ j') c r).card : ℕ) : ℝ) := by
        unfold badTargets
        rw [← hsdef, ← hc, ← hrdef]
        refine (Nat.cast_le.2 Finset.card_biUnion_le).trans ?_
        push_cast
        refine Finset.sum_le_sum fun pq _ => ?_
        refine (Nat.cast_le.2 Finset.card_biUnion_le).trans ?_
        push_cast
        exact Finset.sum_le_sum fun j' _ => Nat.cast_le.2 Finset.card_image_le
    _ ≤ ∑ _pq ∈ cubeBox s c r ×ˢ cubeBox s c r,
          ∑ _j' ∈ Finset.Icc (l.1 + n - 1) (l.1 + n + 1), M₂ * M₂ := by
        refine Finset.sum_le_sum fun pq _ => Finset.sum_le_sum fun j' hj' => ?_
        rw [Finset.card_product, Nat.cast_mul]
        exact mul_le_mul (hbox₂ j' hj') (hbox₂ j' hj') (Nat.cast_nonneg _) hM₂0
    _ = ((cubeBox s c r).card : ℝ) * (cubeBox s c r).card * (3 * (M₂ * M₂)) := by
        rw [Finset.sum_const, Finset.sum_const, card_Icc_three, Finset.card_product,
          nsmul_eq_mul, nsmul_eq_mul]
        push_cast
        ring
    _ ≤ M₁ * M₁ * (3 * (M₂ * M₂)) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact mul_le_mul hbox₁ hbox₁ (Nat.cast_nonneg _) hM₁0
    _ = Nb d n δ := by
        rw [Nb, hM₁, hM₂, pow_mul, pow_mul]
        ring

end BadCount

/-! ## HA3 D6 (i): the counts of valid records -/

section Counts

variable {d : ℕ} {n : ℕ} {δ : ℝ}

/-- Any finite set of valid good records with location `λ` and bin `k` has at most `N_g(k)`
elements. -/
theorem card_good_le {T : Finset (Record d)} (hδ : 0 < δ) {l : Loc d} {k : ℕ}
    (hT : ∀ ρ ∈ T, RecValid n δ ρ ∧ ρ.isLeft = true ∧ ρ.loc = l ∧ ρ.bin = k) :
    (T.card : ℝ) ≤ Ng d n k := by
  refine le_trans (Nat.cast_le.2 (Finset.card_le_card fun ρ hρ => ?_)) (card_goodTargets_le hδ l k)
  obtain ⟨hv, hleft, hloc, hbin⟩ := hT ρ hρ
  rcases ρ with g | b
  · simp only [Record.loc_inl, Record.bin_inl] at hloc hbin
    subst hloc hbin
    exact mem_goodTargets hδ hv
  · simp only [Sum.isLeft_inr, Bool.false_eq_true] at hleft

/-- Any finite set of valid bad records with location `λ` has at most `N_b` elements
(`0 < δ ≤ 1`). -/
theorem card_bad_le {T : Finset (Record d)} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {l : Loc d}
    (hT : ∀ ρ ∈ T, RecValid n δ ρ ∧ ρ.isRight = true ∧ ρ.loc = l) :
    (T.card : ℝ) ≤ Nb d n δ := by
  refine le_trans (Nat.cast_le.2 (Finset.card_le_card fun ρ hρ => ?_)) (card_badTargets_le hδ hδ1 l)
  obtain ⟨hv, hright, hloc⟩ := hT ρ hρ
  rcases ρ with g | b
  · simp only [Sum.isRight_inl, Bool.false_eq_true] at hright
  · simp only [Record.loc_inr] at hloc
    subst hloc
    exact mem_badTargets hδ hv

/-- **HA3 D6 (i), good records**, for a finite set of valid records: at most `N_g(k)` of them are
good with location `λ` and bin `k`. -/
theorem card_filter_good_le (hδ : 0 < δ) (S : Finset (Record d))
    (hS : ∀ ρ ∈ S, RecValid n δ ρ) (l : Loc d) (k : ℕ) :
    ((S.filter fun ρ => ρ.isLeft = true ∧ ρ.loc = l ∧ ρ.bin = k).card : ℝ) ≤ Ng d n k :=
  card_good_le hδ fun ρ hρ => by
    rw [Finset.mem_filter] at hρ
    exact ⟨hS ρ hρ.1, hρ.2⟩

/-- **HA3 D6 (i), bad records**, for a finite set of valid records: at most `N_b` of them are bad
with location `λ`. -/
theorem card_filter_bad_le (hδ : 0 < δ) (hδ1 : δ ≤ 1) (S : Finset (Record d))
    (hS : ∀ ρ ∈ S, RecValid n δ ρ) (l : Loc d) :
    ((S.filter fun ρ => ρ.isRight = true ∧ ρ.loc = l).card : ℝ) ≤ Nb d n δ :=
  card_bad_le hδ hδ1 fun ρ hρ => by
    rw [Finset.mem_filter] at hρ
    exact ⟨hS ρ hρ.1, hρ.2⟩

/-- The valid good records (`ρ ∈ 𝓡`) with location `λ` and bin `k`. -/
def goodRecs (n : ℕ) (δ : ℝ) (l : Loc d) (k : ℕ) : Set (Record d) :=
  {ρ | RecValid n δ ρ ∧ ρ.isLeft = true ∧ ρ.loc = l ∧ ρ.bin = k}

/-- The valid bad records (`ρ ∈ 𝓡`) with location `λ`. -/
def badRecs (n : ℕ) (δ : ℝ) (l : Loc d) : Set (Record d) :=
  {ρ | RecValid n δ ρ ∧ ρ.isRight = true ∧ ρ.loc = l}

theorem goodRecs_subset (hδ : 0 < δ) (l : Loc d) (k : ℕ) :
    goodRecs n δ l k ⊆ ↑(goodTargets n δ l k) := by
  intro ρ hρ
  obtain ⟨hv, hleft, hloc, hbin⟩ := hρ
  rcases ρ with g | b
  · simp only [Record.loc_inl, Record.bin_inl] at hloc hbin
    subst hloc hbin
    exact mem_goodTargets hδ hv
  · simp only [Sum.isLeft_inr, Bool.false_eq_true] at hleft

theorem badRecs_subset (hδ : 0 < δ) (l : Loc d) : badRecs n δ l ⊆ ↑(badTargets n δ l) := by
  intro ρ hρ
  obtain ⟨hv, hright, hloc⟩ := hρ
  rcases ρ with g | b
  · simp only [Sum.isRight_inl, Bool.false_eq_true] at hright
  · simp only [Record.loc_inr] at hloc
    subst hloc
    exact mem_badTargets hδ hv

/-- The valid good records with a given location and bin form a finite set. -/
theorem goodRecs_finite (hδ : 0 < δ) (l : Loc d) (k : ℕ) : (goodRecs n δ l k).Finite :=
  (goodTargets n δ l k).finite_toSet.subset (goodRecs_subset hδ l k)

/-- The valid bad records with a given location form a finite set. -/
theorem badRecs_finite (hδ : 0 < δ) (l : Loc d) : (badRecs n δ l).Finite :=
  (badTargets n δ l).finite_toSet.subset (badRecs_subset hδ l)

/-- **HA3 D6 (i), good records**: the number of `ρ ∈ 𝓡` that are good with location `λ` and bin
`k` is at most `N_g(k) = 3K (c_d K √(k+1))^{2d}`, `c_d = 10 + 4√d`. -/
theorem ncard_goodRecs_le (hδ : 0 < δ) (l : Loc d) (k : ℕ) :
    ((goodRecs n δ l k).ncard : ℝ) ≤ Ng d n k := by
  refine le_trans ?_ (card_goodTargets_le hδ l k)
  rw [← Set.ncard_coe_finset]
  exact_mod_cast Set.ncard_le_ncard (goodRecs_subset hδ l k) (Finset.finite_toSet _)

/-- **HA3 D6 (i), bad records**: for `0 < δ ≤ 1` (in particular for `δ ≤ 1/(16√d K)`), the number
of `ρ ∈ 𝓡` that are bad with location `λ` is at most `N_b = 3 (c'_d/δ)^{2d} (c'_d K/δ)^{2d}`. -/
theorem ncard_badRecs_le (hδ : 0 < δ) (hδ1 : δ ≤ 1) (l : Loc d) :
    ((badRecs n δ l).ncard : ℝ) ≤ Nb d n δ := by
  refine le_trans ?_ (card_badTargets_le hδ hδ1 l)
  rw [← Set.ncard_coe_finset]
  exact_mod_cast Set.ncard_le_ncard (badRecs_subset hδ l) (Finset.finite_toSet _)

end Counts

/-! ## The finite record set of a cutoff -/

section RecSet

variable {d : ℕ}

/-- The largest scale index of a record at cutoff `ε`: `J_ε = ⌊log₂(2K/ε)⌋` (`≤ ⌈log₂(2K/ε)⌉`);
records sit at internal nodes (`R > ε`) and their children (`R > ε/(2K)`). -/
def scaleMax (n : ℕ) (ε : ℝ) : ℤ := Int.log 2 (2 * 2 ^ n / ε)

/-- The bound `B = ⌈2/(δ 2^{-J_ε})⌉` on the cube indices: every lattice cube of a scale
`j ≤ J_ε` meeting `[-2, 2]^d` has indices in `[-B, B]^d`. -/
def idxMax (n : ℕ) (δ ε : ℝ) : ℤ := ⌈2 / side δ (scaleMax n ε)⌉

/-- The largest bin `⌊a₀/δ²⌋` of a good record. -/
def binMax (n : ℕ) (δ : ℝ) : ℕ := ⌊a0 n / δ ^ 2⌋₊

/-- The cube indices `[-B, B]^d`. -/
def cubeRange (d : ℕ) (B : ℤ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset fun _ => Finset.Icc (-B) B

/-- The locations with scale index in `[0, J]` and cube indices in `[-B, B]^d`. -/
def locRange (d : ℕ) (J B : ℤ) : Finset (Loc d) :=
  Finset.Icc 0 J ×ˢ (cubeRange d B ×ˢ cubeRange d B)

/-- All records whose entries lie in the ranges of the cutoff `ε`. -/
def recBox (d n : ℕ) (δ ε : ℝ) : Finset (Record d) :=
  ((Finset.range (binMax n δ + 1) ×ˢ Finset.range (2 ^ n) ×ˢ
      locRange d (scaleMax n ε) (idxMax n δ ε) ×ˢ locRange d (scaleMax n ε) (idxMax n δ ε)).image
    fun t => (⟨t.1, t.2.1, t.2.2.1, t.2.2.2⟩ : GoodRec d)).disjSum
  ((locRange d (scaleMax n ε) (idxMax n δ ε) ×ˢ cubeRange d (idxMax n δ ε) ×ˢ
      cubeRange d (idxMax n δ ε) ×ˢ locRange d (scaleMax n ε) (idxMax n δ ε)).image
    fun t => (⟨t.1, t.2.1, t.2.2.1, t.2.2.2⟩ : BadRec d))

/-- Validity of records is decided classically (it quantifies over configurations). -/
noncomputable instance recValidDecidable (n : ℕ) (δ : ℝ) : DecidablePred (RecValid (d := d) n δ) :=
  Classical.decPred _

/-- **The finite record set of the cutoff `ε`** (HA3 §4, "Union bounds over records"): the valid
records with scale indices in `[0, ⌊log₂(2K/ε)⌋]`, cube indices in `[-B, B]^d` (`idxMax`), and
bins at most `⌊a₀/δ²⌋`.  Every chain record assigned to a leaf of the partition tree of an
admissible path is made of records of this set (`HigherDimLFPP.Upper.chainRecord_assignment`). -/
def recSet (d n : ℕ) (δ ε : ℝ) : Finset (Record d) := (recBox d n δ ε).filter (RecValid n δ)

theorem recValid_of_mem_recSet {n : ℕ} {δ ε : ℝ} {ρ : Record d} (h : ρ ∈ recSet d n δ ε) :
    RecValid n δ ρ :=
  (Finset.mem_filter.1 h).2

theorem mem_locRange {J B : ℤ} {l : Loc d} :
    l ∈ locRange d J B ↔ (0 ≤ l.1 ∧ l.1 ≤ J) ∧ l.2.1 ∈ cubeRange d B ∧ l.2.2 ∈ cubeRange d B := by
  simp only [locRange, Finset.mem_product, Finset.mem_Icc]

theorem good_mem_recSet {n : ℕ} {δ ε : ℝ} {g : GoodRec d} (hv : RecValid n δ (Sum.inl g))
    (hbin : g.bin ≤ binMax n δ) (hidx : g.idx < 2 ^ n)
    (hloc : g.loc ∈ locRange d (scaleMax n ε) (idxMax n δ ε))
    (hnext : g.next ∈ locRange d (scaleMax n ε) (idxMax n δ ε)) :
    (Sum.inl g : Record d) ∈ recSet d n δ ε := by
  refine Finset.mem_filter.2 ⟨?_, hv⟩
  rw [recBox, Finset.mem_disjSum]
  left
  refine ⟨g, Finset.mem_image.2 ⟨(g.bin, g.idx, g.loc, g.next), ?_, rfl⟩, rfl⟩
  simp only [Finset.mem_product, Finset.mem_range]
  exact ⟨by omega, hidx, hloc, hnext⟩

theorem bad_mem_recSet {n : ℕ} {δ ε : ℝ} {b : BadRec d} (hv : RecValid n δ (Sum.inr b))
    (hloc : b.loc ∈ locRange d (scaleMax n ε) (idxMax n δ ε))
    (hp : b.advP ∈ cubeRange d (idxMax n δ ε)) (hq : b.advQ ∈ cubeRange d (idxMax n δ ε))
    (hnext : b.next ∈ locRange d (scaleMax n ε) (idxMax n δ ε)) :
    (Sum.inr b : Record d) ∈ recSet d n δ ε := by
  refine Finset.mem_filter.2 ⟨?_, hv⟩
  rw [recBox, Finset.mem_disjSum]
  right
  refine ⟨b, Finset.mem_image.2 ⟨(b.loc, b.advP, b.advQ, b.next), ?_, rfl⟩, rfl⟩
  simp only [Finset.mem_product]
  exact ⟨hloc, hp, hq, hnext⟩

/-- Chords longer than `ε/(2K)` have scale index at most `J_ε`. -/
theorem scaleIdx_le_scaleMax {n : ℕ} {ε R : ℝ} (hε : 0 < ε) (hR : ε / (2 * 2 ^ n) < R) :
    scaleIdx R ≤ scaleMax n ε := by
  have h := scaleIdx_le_log (by positivity) hR
  rwa [inv_div] at h

/-- The cube indices of the points of `U = (-2,2)^d` at scales `j ≤ J` lie in
`[-B, B]^d`, `B = ⌈2/(δ 2^{-J})⌉`. -/
theorem cubeIdx_mem_cubeRange {δ : ℝ} (hδ : 0 < δ) {j J : ℤ} (hj : j ≤ J) {z : Rd d}
    (hz : z ∈ cube d) : cubeIdx (side δ j) z ∈ cubeRange d ⌈2 / side δ J⌉ := by
  rw [cubeRange, Fintype.mem_piFinset]
  intro i
  have hs := side_pos hδ j
  have hsJ := side_pos hδ J
  have hle : side δ J ≤ side δ j := side_anti hδ.le hj
  have hzi : |z i| < 2 := hz i
  rw [abs_lt] at hzi
  have h2 : 2 / side δ j ≤ 2 / side δ J := div_le_div_of_nonneg_left (by norm_num) hsJ hle
  have hup : z i / side δ j ≤ 2 / side δ J :=
    (div_le_div_of_nonneg_right hzi.2.le hs.le).trans h2
  have hlo : -(2 / side δ J) ≤ z i / side δ j := by
    have : -2 / side δ j ≤ z i / side δ j := div_le_div_of_nonneg_right hzi.1.le hs.le
    rw [neg_div] at this
    linarith
  rw [Finset.mem_Icc]
  constructor
  · rw [← Int.floor_neg]
    exact Int.floor_mono hlo
  · exact (Int.floor_mono hup).trans (Int.floor_le_ceil _)

end RecSet

/-! ## Chain counting (HA3 D7, "Counting") -/

section ChainCount

variable {d : ℕ} {n : ℕ} {δ : ℝ}

/-- Record weights depending only on the record type and the bin: `w_g(k)` for a good record in
bin `k` and `w_b` for a bad record. -/
def recWeight (wg : ℕ → ℝ) (wb : ℝ) : Record d → ℝ
  | .inl g => wg g.bin
  | .inr _ => wb

theorem recWeight_nonneg {wg : ℕ → ℝ} {wb : ℝ} (hwg : ∀ k, 0 ≤ wg k) (hwb : 0 ≤ wb)
    (ρ : Record d) : 0 ≤ recWeight wg wb ρ := by
  rcases ρ with g | b
  · exact hwg _
  · exact hwb

/-- **One step of the chain counting**: the weights of the valid records of a finite set with a
given location sum to at most `Z_g + Z_b`, `Z_g = Σ_k N_g(k) w_g(k)`, `Z_b = N_b w_b`. -/
theorem sum_filter_loc_weight_le (hδ : 0 < δ) (hδ1 : δ ≤ 1) (S : Finset (Record d))
    (hS : ∀ ρ ∈ S, RecValid n δ ρ) {wg : ℕ → ℝ} {wb : ℝ} (hwg : ∀ k, 0 ≤ wg k) (hwb : 0 ≤ wb)
    (hsum : Summable fun k => Ng d n k * wg k) (l : Loc d) :
    ∑ ρ ∈ S.filter (fun ρ => ρ.loc = l), recWeight wg wb ρ ≤
      ∑' k, Ng d n k * wg k + Nb d n δ * wb := by
  set Sl := S.filter (fun ρ => ρ.loc = l) with hSl
  rw [← Finset.sum_filter_add_sum_filter_not Sl (fun ρ => ρ.isLeft = true)]
  refine add_le_add ?_ ?_
  · -- good records, grouped by bins
    set G := Sl.filter (fun ρ => ρ.isLeft = true) with hG
    rw [← Finset.sum_fiberwise_of_maps_to (s := G) (t := G.image Record.bin)
      (g := Record.bin) (fun ρ hρ => Finset.mem_image_of_mem _ hρ)]
    calc ∑ k ∈ G.image Record.bin, ∑ ρ ∈ G with ρ.bin = k, recWeight wg wb ρ
        ≤ ∑ k ∈ G.image Record.bin, Ng d n k * wg k := by
          refine Finset.sum_le_sum fun k _ => ?_
          have hw : ∀ ρ ∈ G.filter (fun ρ => ρ.bin = k), recWeight wg wb ρ = wg k := by
            intro ρ hρ
            simp only [hG, hSl, Finset.mem_filter] at hρ
            obtain ⟨⟨⟨-, -⟩, hleft⟩, hbin⟩ := hρ
            rcases ρ with g | b
            · simp only [Record.bin_inl] at hbin
              simp only [recWeight, hbin]
            · simp only [Sum.isLeft_inr, Bool.false_eq_true] at hleft
          rw [Finset.sum_congr rfl hw, Finset.sum_const, nsmul_eq_mul]
          refine mul_le_mul_of_nonneg_right (card_good_le (l := l) hδ fun ρ hρ => ?_) (hwg k)
          simp only [hG, hSl, Finset.mem_filter] at hρ
          obtain ⟨⟨⟨hρS, hloc⟩, hleft⟩, hbin⟩ := hρ
          exact ⟨hS ρ hρS, hleft, hloc, hbin⟩
      _ ≤ ∑' k, Ng d n k * wg k :=
          hsum.sum_le_tsum _ fun k _ => mul_nonneg (Ng_nonneg d n k) (hwg k)
  · -- bad records
    set B := Sl.filter (fun ρ => ¬ ρ.isLeft = true) with hB
    have hw : ∀ ρ ∈ B, recWeight wg wb ρ = wb := by
      intro ρ hρ
      simp only [hB, Finset.mem_filter] at hρ
      rcases ρ with g | b
      · simp only [Sum.isLeft_inl, not_true_eq_false, and_false] at hρ
      · rfl
    rw [Finset.sum_congr rfl hw, Finset.sum_const, nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_right (card_bad_le (l := l) hδ hδ1 fun ρ hρ => ?_) hwb
    simp only [hB, hSl, Finset.mem_filter] at hρ
    obtain ⟨⟨hρS, hloc⟩, hleft⟩ := hρ
    refine ⟨hS ρ hρS, ?_, hloc⟩
    rcases ρ with g | b
    · simp only [Sum.isLeft_inl, not_true_eq_false] at hleft
    · rfl

open scoped Classical in
/-- **Chain counting** (HA3 D7, "Counting"; 2D `ChainUnion.sum_chain_le`): for any finite set `S`
of valid records and weights depending only on the record type and the bin,
`Σ_{chain records of length l in S} Π_i w(ρ_i) ≤ (Z_g + Z_b)^l`, where
`Z_g = Σ_k N_g(k) w_g(k)` and `Z_b = N_b w_b`.  Here `0 < δ ≤ 1`. -/
theorem sum_chain_weight_le (hδ : 0 < δ) (hδ1 : δ ≤ 1) (S : Finset (Record d))
    (hS : ∀ ρ ∈ S, RecValid n δ ρ) {wg : ℕ → ℝ} {wb : ℝ} (hwg : ∀ k, 0 ≤ wg k) (hwb : 0 ≤ wb)
    (hsum : Summable fun k => Ng d n k * wg k) (l : ℕ) :
    ∑ ρ : Fin l → S, (if IsChainRec δ (fun i => (ρ i).1) then
        ∏ i, recWeight wg wb (ρ i).1 else 0) ≤
      (∑' k, Ng d n k * wg k + Nb d n δ * wb) ^ l := by
  set Z := ∑' k, Ng d n k * wg k + Nb d n δ * wb with hZ
  have hZ0 : 0 ≤ Z := add_nonneg
    (tsum_nonneg fun k => mul_nonneg (Ng_nonneg d n k) (hwg k))
    (mul_nonneg (Nb_nonneg d n hδ) hwb)
  have key : ∀ m : Loc d,
      ∑ y : S, (if y.1.loc = m then recWeight wg wb y.1 else 0) ≤ Z := by
    intro m
    rw [Finset.sum_coe_sort S (fun y => if y.loc = m then recWeight wg wb y else 0),
      ← Finset.sum_filter]
    exact sum_filter_loc_weight_le hδ hδ1 S hS hwg hwb hsum m
  exact LQGDimension.ChainUnion.sum_chain_le (R := S)
    (fun x y => y.1.loc = x.1.nextLoc) (fun y => recWeight wg wb y.1)
    (fun y => recWeight_nonneg hwg hwb y.1) Z hZ0 (fun x => by convert key x.1.nextLoc) l
    (fun y => y.1.loc = rootLoc d δ) (by convert key (rootLoc d δ))

open scoped Classical in
/-- Chain counting for the finite record set of the cutoff `ε` (`0 < δ ≤ 1`). -/
theorem sum_chain_weight_le_recSet (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ε : ℝ) {wg : ℕ → ℝ} {wb : ℝ}
    (hwg : ∀ k, 0 ≤ wg k) (hwb : 0 ≤ wb) (hsum : Summable fun k => Ng d n k * wg k) (l : ℕ) :
    ∑ ρ : Fin l → recSet d n δ ε, (if IsChainRec δ (fun i => (ρ i).1) then
        ∏ i, recWeight wg wb (ρ i).1 else 0) ≤
      (∑' k, Ng d n k * wg k + Nb d n δ * wb) ^ l :=
  sum_chain_weight_le hδ hδ1 _ (fun _ hρ => recValid_of_mem_recSet hρ) hwg hwb hsum l

/-- Summing the chain counts over the lengths `l ≤ M` (HA3 D7):
`Σ_{l ≤ M} Z^l ≤ (1 + Z)^M` for `Z ≥ 0`. -/
theorem sum_range_pow_le_one_add_pow {Z : ℝ} (hZ : 0 ≤ Z) (M : ℕ) :
    ∑ l ∈ Finset.range (M + 1), Z ^ l ≤ (1 + Z) ^ M := by
  induction M with
  | zero => simp only [zero_add, Finset.range_one, Finset.sum_singleton, pow_zero, le_refl]
  | succ M ih =>
    rw [Finset.sum_range_succ, pow_succ (1 + Z) M]
    have h1 : Z ^ (M + 1) ≤ Z * (1 + Z) ^ M := by
      rw [pow_succ, mul_comm]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hZ (by linarith) M) hZ
    nlinarith

end ChainCount

end HigherDimLFPP.Upper
