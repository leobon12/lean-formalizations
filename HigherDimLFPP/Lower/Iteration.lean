import HigherDimLFPP.Lower.Transfer
import HigherDimLFPP.Var.EnergyBall
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# The iteration (5.27) of the lower comparison

Packet P-L4, target T1 (ruling H6; audit HA4, §1 "order of choices", "Details for later use" D7,
"Iteration").

* **The parameters of §5** (source (5.1), (5.2), (5.6)): `gPad n = g_n = ⌈20 log₂(n + 2)⌉`,
  `blockK n = K = 2^{n + g_n}`, `qStep d n δ = q = (1 + δ²(e_{n,d} + 1))/K` (P-L1's `qOf`) and
  `rhoStep n δ = ρ = δ (n + 2)⁴`; the coupling constant is `ζ = δ^{3/2}`.
* **The selector (5.7)**, Riemann version (HA4 D5–D6): `selStat` is
  `-δ^{-1/2} (⟨φ, ν_j^N⟩ - ⟨φ, ν_0^N⟩)` with `ν_j^N = (KN)⁻¹ Σ_{i<K, l<N} δ_{T_i^j((l/N) e₁)}` and
  `ν_0^N = N⁻¹ Σ_{l<N} δ_{(l/N) e₁}`, read on the root band `φ = Y(ρq, ρ, ·)` at the finite set
  `selPts`.  `lowerParams d n N δ v` is P-L2a's construction (`LParams`) with these choices.
* **`Lemma53Holds d κ`**: Lemma 5.3 (i)–(iii) for this construction, in exactly the form consumed
  by P-L2a's `Good.mu_inCDelta` and `Good.mm_le_pow`: for every `n ≥ N₀` there are `J` and the
  geometric constants `M, B > 0` such that for every `θ > 0` and all small `δ` there are
  replacement polygons `v j` from `0` to `e₁` with `K` edges of length `q`, with (i) every edge
  similarity mapping `V_δ` into itself and `V_δ ⊆ U`, and, for all large Riemann parameters `N`,
  (ii) `T μ ∈ C_δ` and (iii) `E ∫ e^{ζ H} dν_{I,μ} ≤ 1 - δ²(4e_{n,d} - 5) + θ δ²` for every
  finitely supported `μ ∈ C_δ`.  It is the only hypothesis of the lower comparison (P-L3 proves
  Lemma 5.3).  `Lemma53HoldsGen` is the same statement for an arbitrary measurable selection
  statistic reading finitely many root-band values (`lemma53HoldsGen_of_lemma53`); it is an
  integration entry point in case Lemma 5.3 is proved for another normalization of (5.7).
* **The iteration (5.27)**: `LParams.Good.mm_le_exp` (generic: `m₀ = 1`, `μ₀ ∈ C_δ`, the recursion
  (5.26) and the two parts of Lemma 5.3 give `m_r ≤ e^{-r a}` once `Kq b ≤ e^{-a}`),
  `LParams.Good.mm_le_exp_beta` (the constants of §5, Lemma 5.3 with `θ = 1`:
  `Kq (1 - δ²(4e - 6)) ≤ e^{δ²(e+1)} e^{-δ²(4e-6)} = e^{-δ²(β - 7)}`, `β = 3e`) and `iteration`
  (`m_r ≤ e^{-r δ² (β_{n,d} - 7)}` for all `r`, all small `δ` and all large `N`).
* **`IterD d κ`**: (5.27) in the form consumed by the existence-free lower comparison (node
  S5-ITER of HA4's DAG): the replacement polygons are fixed before the Riemann parameter `N`, and
  for every large `N` the construction (with a selection statistic reading finitely many
  root-band values) satisfies the standing hypotheses, its polygons lie in `U`, and
  `m_r ≤ e^{-r δ²(β_{n,d} - 7)}`.  `iterD_of_lemma53` (and `iterD_of_lemma53Gen`) prove it.

2D source: `LQGDimension/LFPP/BlockConstruction.lean` (`Good.mm_le_pow`, `block_main`), redone
with the invariant class `C_δ` (HA4 §5 table).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped RealInnerProductSpace

namespace HigherDimLFPP.Lower

variable {d : ℕ}

/-! ## The parameters of §5 -/

/-- `g_n = ⌈20 log₂(n + 2)⌉` (5.1). -/
def gPad (n : ℕ) : ℕ := ⌈20 * Real.logb 2 ((n : ℝ) + 2)⌉₊

/-- The number `K = 2^{n + g_n}` of edges of a replacement polygon (5.2). -/
def blockK (n : ℕ) : ℕ := 2 ^ (n + gPad n)

/-- The common edge length `q = s/K` of the replacement polygons, `s = 1 + δ² E₀`,
`E₀ = e_{n,d} + 1` (5.2). -/
def qStep (d n : ℕ) (δ : ℝ) : ℝ := qOf (blockK n) (eN n d + 1) δ

/-- The top `ρ = δ L`, `L = (n + 2)⁴`, of the root band `H = H_{ρq, ρ}` (5.2), (5.6). -/
def rhoStep (n : ℕ) (δ : ℝ) : ℝ := δ * ((n : ℝ) + 2) ^ 4

theorem gPad_pos (n : ℕ) : 0 < gPad n := by
  unfold gPad
  refine Nat.lt_ceil.2 ?_
  have h : 0 < Real.logb 2 ((n : ℝ) + 2) := Real.logb_pos one_lt_two (by
    have := n.cast_nonneg (α := ℝ)
    linarith)
  push_cast
  linarith

theorem two_le_blockK (n : ℕ) : 2 ≤ blockK n := by
  unfold blockK
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ (n + gPad n) := Nat.pow_le_pow_right (by norm_num) (by have := gPad_pos n; omega)

theorem blockK_pos (n : ℕ) : 0 < blockK n := lt_of_lt_of_le two_pos (two_le_blockK n)

theorem qStep_eq (d n : ℕ) (δ : ℝ) :
    qStep d n δ = (1 + δ ^ 2 * (eN n d + 1)) / (blockK n : ℝ) := rfl

theorem qStep_pos (d n : ℕ) (δ : ℝ) : 0 < qStep d n δ := by
  rw [qStep_eq]
  have := Var.eN_nonneg n d
  have hK : (0 : ℝ) < blockK n := by exact_mod_cast blockK_pos n
  positivity

/-- `K q = s = 1 + δ² (e_{n,d} + 1)`. -/
theorem blockK_mul_qStep (d n : ℕ) (δ : ℝ) :
    (blockK n : ℝ) * qStep d n δ = 1 + δ ^ 2 * (eN n d + 1) := by
  rw [qStep_eq]
  have hK : (blockK n : ℝ) ≠ 0 := by exact_mod_cast (blockK_pos n).ne'
  field_simp

theorem continuous_qStep (d n : ℕ) : Continuous (qStep d n) := by
  have h : qStep d n = fun δ => (1 + δ ^ 2 * (eN n d + 1)) / (blockK n : ℝ) :=
    funext (qStep_eq d n)
  rw [h]
  fun_prop

theorem qStep_zero (d n : ℕ) : qStep d n 0 = 1 / (blockK n : ℝ) := by
  rw [qStep_eq]
  simp

/-- `q < 1` for all small `δ` (`q → 1/K < 1`). -/
theorem eventually_qStep_lt_one (d n : ℕ) : ∀ᶠ δ in 𝓝[>] 0, qStep d n δ < 1 := by
  have h0 : qStep d n 0 < 1 := by
    rw [qStep_zero, div_lt_one (by exact_mod_cast blockK_pos n)]
    exact_mod_cast (two_le_blockK n : 2 ≤ blockK n)
  exact nhdsWithin_le_nhds (((continuous_qStep d n).tendsto 0).eventually (gt_mem_nhds h0))

theorem rhoStep_pos (n : ℕ) {δ : ℝ} (hδ : 0 < δ) : 0 < rhoStep n δ := by
  unfold rhoStep
  positivity

/-- `ρ < 1` for all small `δ`. -/
theorem eventually_rhoStep_lt_one (n : ℕ) : ∀ᶠ δ in 𝓝[>] 0, rhoStep n δ < 1 := by
  have hc : Continuous (rhoStep n) := by
    unfold rhoStep
    fun_prop
  have h0 : rhoStep n 0 < 1 := by simp [rhoStep]
  exact nhdsWithin_le_nhds ((hc.tendsto 0).eventually (gt_mem_nhds h0))

/-! ## The selector (5.7) and the construction -/

/-- The points read by the selector (5.7) (Riemann version): the reference points `(l/N) e₁` of
`ν₀^N` and the left Riemann points `T_i^j((l/N) e₁)` of the edges of all replacement polygons. -/
def selPts (K N : ℕ) (q : ℝ) {J : ℕ} (v : Fin (J + 1) → ℕ → Rd d) : Finset (Rd d) :=
  refSet N ∪ Finset.univ.biUnion fun j =>
    (Finset.range K).biUnion fun i => (refSet N).image (edgeSim q (v j) i).app

/-- **The selection statistic (5.7)**, Riemann version (HA4 D5–D6): for the root band field `φ`,
`-δ^{-1/2} (⟨φ, ν_j^N⟩ - ⟨φ, ν_0^N⟩)` with `ν_j^N = (KN)⁻¹ Σ_{i<K, l<N} δ_{T_i^j((l/N) e₁)}`
and `ν_0^N = N⁻¹ Σ_{l<N} δ_{(l/N) e₁}`.  The selector `I` is its least argmax (`LParams.sel`). -/
def selStat (K N : ℕ) (δ q : ℝ) {J : ℕ} (v : Fin (J + 1) → ℕ → Rd d) (j : Fin (J + 1))
    (φ : Rd d → ℝ) : ℝ :=
  -(δ ^ (-(1 / 2 : ℝ))) *
    ((1 / ((K : ℝ) * N)) * ∑ i ∈ Finset.range K, ∑ l ∈ Finset.range N,
        φ ((edgeSim q (v j) i).app (refPt N l)) -
      (1 / (N : ℝ)) * ∑ l ∈ Finset.range N, φ (refPt N l))

/-- **The construction of §5** at block level `n`, Riemann parameter `N` and small parameter
`δ`, with replacement polygons `v` and the selector (5.7): `K = 2^{n + g_n}` edges of length
`q = (1 + δ²(e_{n,d} + 1))/K`, `ζ = δ^{3/2}`, root band `(ρq, ρ]` with `ρ = δ (n + 2)⁴`. -/
def lowerParams (d n N : ℕ) (δ : ℝ) {J : ℕ} (v : Fin (J + 1) → ℕ → Rd d) : LParams d :=
  ⟨J, blockK n, N, δ ^ (3 / 2 : ℝ), rhoStep n δ, qStep d n δ, v,
    selPts (blockK n) N (qStep d n δ) v, selStat (blockK n) N δ (qStep d n δ) v⟩

theorem measurable_selStat (K N : ℕ) (δ q : ℝ) {J : ℕ} (v : Fin (J + 1) → ℕ → Rd d)
    (j : Fin (J + 1)) : Measurable (selStat K N δ q v j) := by
  unfold selStat
  refine measurable_const.mul (Measurable.sub ?_ ?_)
  · exact measurable_const.mul (Finset.measurable_sum _ fun i _ =>
      Finset.measurable_sum _ fun l _ => measurable_pi_apply _)
  · exact measurable_const.mul (Finset.measurable_sum _ fun l _ => measurable_pi_apply _)

/-- The selection statistic reads the field only at `selPts`. -/
theorem selStat_congr (K N : ℕ) (δ q : ℝ) {J : ℕ} (v : Fin (J + 1) → ℕ → Rd d)
    (j : Fin (J + 1)) (φ φ' : Rd d → ℝ) (h : ∀ z ∈ selPts K N q v, φ z = φ' z) :
    selStat K N δ q v j φ = selStat K N δ q v j φ' := by
  have h0 : ∀ l ∈ Finset.range N, φ (refPt N l) = φ' (refPt N l) := fun l hl =>
    h _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hl))
  have h1 : ∀ i ∈ Finset.range K, ∀ l ∈ Finset.range N,
      φ ((edgeSim q (v j) i).app (refPt N l)) = φ' ((edgeSim q (v j) i).app (refPt N l)) :=
    fun i hi l hl => h _ (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨j, Finset.mem_univ _,
      Finset.mem_biUnion.2 ⟨i, hi, Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ hl)⟩⟩))
  unfold selStat
  rw [Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun l hl => h1 i hi l hl,
    Finset.sum_congr rfl h0]

/-- The construction `⟨J, K, N, δ^{3/2}, ρ, q, v, R, stat⟩` with the §5 parameters satisfies
P-L2a's standing hypotheses as soon as the replacement polygons run from `0` to `e₁` with all
edges of length `q`, `N ≥ 1`, `δ > 0`, `q ≤ 1`, and the selection statistic is measurable and
reads the root band only at the points of `R`. -/
theorem mkParams_good (hd : 0 < d) {n N : ℕ} (hN : 0 < N) {δ : ℝ} (hδ : 0 < δ)
    (hq1 : qStep d n δ ≤ 1) {J : ℕ} {v : Fin (J + 1) → ℕ → Rd d} {R : Finset (Rd d)}
    {stat : Fin (J + 1) → (Rd d → ℝ) → ℝ}
    (hv : ∀ j, v j 0 = 0 ∧ v j (blockK n) = e₁ d ∧
      ∀ i < blockK n, ‖v j (i + 1) - v j i‖ = qStep d n δ)
    (hmeas : ∀ j, Measurable (stat j))
    (hloc : ∀ j, ∀ φ φ' : Rd d → ℝ, (∀ z ∈ R, φ z = φ' z) → stat j φ = stat j φ') :
    (LParams.mk J (blockK n) N (δ ^ (3 / 2 : ℝ)) (rhoStep n δ) (qStep d n δ) v R stat).Good where
  d_pos := hd
  K_pos := blockK_pos n
  N_pos := hN
  ρ_pos := rhoStep_pos n hδ
  q_pos := qStep_pos d n δ
  q_le_one := hq1
  start j := (hv j).1
  finish j := (hv j).2.1
  edge_len j := (hv j).2.2
  stat_meas := hmeas
  stat_loc := hloc

/-- The construction `lowerParams` (selector (5.7)) satisfies P-L2a's standing hypotheses as soon
as the replacement polygons run from `0` to `e₁` with all edges of length `q`, `N ≥ 1`, `δ > 0`
and `q ≤ 1`. -/
theorem lowerParams_good (hd : 0 < d) {n N : ℕ} (hN : 0 < N) {δ : ℝ} (hδ : 0 < δ)
    (hq1 : qStep d n δ ≤ 1) {J : ℕ} {v : Fin (J + 1) → ℕ → Rd d}
    (hv : ∀ j, v j 0 = 0 ∧ v j (blockK n) = e₁ d ∧
      ∀ i < blockK n, ‖v j (i + 1) - v j i‖ = qStep d n δ) :
    (lowerParams d n N δ v).Good :=
  mkParams_good hd hN hδ hq1 hv (fun j => measurable_selStat _ _ _ _ v j)
    (fun j => selStat_congr _ _ _ _ v j)

/-! ## Lemma 5.3, as consumed by the iteration -/

/-- **Lemma 5.3** (source §5.2; HA4 D6, Claim (i)–(iii)) for the construction `lowerParams`, in
the form consumed by P-L2a's `Good.mu_inCDelta` and `Good.mm_le_pow`.  For every block level
`n ≥ N₀` there are the number `J + 1` of profiles and the geometric constants `M, B > 0` (chosen
before `δ`) such that for every `θ > 0` and all sufficiently small `δ` there are replacement
polygons `v j` (from `0` to `e₁`, `K` edges of length `q`) with

* (i) `T_i^j(V_δ) ⊆ V_δ` for every edge similarity, and `V_δ ⊆ U`;

and, for every sufficiently large Riemann parameter `N`, for every finitely supported
`μ = Σ_{z ∈ Sμ} μ z δ_z ∈ C_δ`:

* (ii) `T μ ∈ C_δ` (`T` = P-L2a's `Tmap`, the deterministic transformation (5.14));
* (iii) `E ∫ e^{ζ H} dν_{I,μ} ≤ 1 - δ²(4 e_{n,d} - 5) + θ δ²` (5.15), the expectation being over
  the root band `H = H_{ρq,ρ}` and `I` the selector (5.7).

This is the only hypothesis of the lower comparison; P-L3's Lemma 5.3 discharges it. -/
def Lemma53Holds (d : ℕ) (κ : Rd d → ℝ) : Prop :=
  ∃ N₀ : ℕ, ∀ n ≥ N₀, ∃ (J : ℕ) (M B : ℝ), 0 < M ∧ 0 < B ∧ ∀ θ > 0, ∀ᶠ δ in 𝓝[>] 0,
    ∃ v : Fin (J + 1) → ℕ → Rd d,
      (∀ j, v j 0 = 0 ∧ v j (blockK n) = e₁ d ∧
        ∀ i < blockK n, ‖v j (i + 1) - v j i‖ = qStep d n δ) ∧
      Vdelta δ M B ⊆ cube d ∧
      (∀ j, ∀ i < blockK n,
        MapsTo (edgeSim (qStep d n δ) (v j) i).app (Vdelta δ M B) (Vdelta δ M B)) ∧
      ∀ᶠ N in atTop, ∀ (Sμ : Finset (Rd d)) (μ : Rd d → ℝ), InCDelta δ M B Sμ μ →
        InCDelta δ M B ((lowerParams d n N δ v).stepPts Sμ)
            ((lowerParams d n N δ v).Tmap κ Sμ μ) ∧
          ∫ Y, (lowerParams d n N δ v).tiltMass Sμ μ Y
              ∂gLawD κ ((lowerParams d n N δ v).stepTris Sμ) ≤
            1 - δ ^ 2 * (4 * eN n d - 5) + θ * δ ^ 2

/-- **Lemma 5.3 for an arbitrary selection rule** (a weaker form of `Lemma53Holds`, for
integration): as `Lemma53Holds`, except that for each Riemann parameter `N` the selection
statistic `stat N` may be any measurable function of the root band field that reads it only on
a finite set `R N` (`Lemma53Holds` is the case of the selector (5.7),
`lemma53HoldsGen_of_lemma53`). -/
def Lemma53HoldsGen (d : ℕ) (κ : Rd d → ℝ) : Prop :=
  ∃ N₀ : ℕ, ∀ n ≥ N₀, ∃ (J : ℕ) (M B : ℝ), 0 < M ∧ 0 < B ∧ ∀ θ > 0, ∀ᶠ δ in 𝓝[>] 0,
    ∃ (v : Fin (J + 1) → ℕ → Rd d) (R : ℕ → Finset (Rd d))
      (stat : ℕ → Fin (J + 1) → (Rd d → ℝ) → ℝ),
      (∀ j, v j 0 = 0 ∧ v j (blockK n) = e₁ d ∧
        ∀ i < blockK n, ‖v j (i + 1) - v j i‖ = qStep d n δ) ∧
      Vdelta δ M B ⊆ cube d ∧
      (∀ j, ∀ i < blockK n,
        MapsTo (edgeSim (qStep d n δ) (v j) i).app (Vdelta δ M B) (Vdelta δ M B)) ∧
      ∀ᶠ N in atTop, (∀ j, Measurable (stat N j)) ∧
        (∀ j, ∀ φ φ' : Rd d → ℝ, (∀ z ∈ R N, φ z = φ' z) → stat N j φ = stat N j φ') ∧
        ∀ (Sμ : Finset (Rd d)) (μ : Rd d → ℝ), InCDelta δ M B Sμ μ →
          InCDelta δ M B ((LParams.mk J (blockK n) N (δ ^ (3 / 2 : ℝ)) (rhoStep n δ)
              (qStep d n δ) v (R N) (stat N)).stepPts Sμ)
            ((LParams.mk J (blockK n) N (δ ^ (3 / 2 : ℝ)) (rhoStep n δ) (qStep d n δ) v (R N)
              (stat N)).Tmap κ Sμ μ) ∧
          ∫ Y, (LParams.mk J (blockK n) N (δ ^ (3 / 2 : ℝ)) (rhoStep n δ) (qStep d n δ) v (R N)
              (stat N)).tiltMass Sμ μ Y
              ∂gLawD κ ((LParams.mk J (blockK n) N (δ ^ (3 / 2 : ℝ)) (rhoStep n δ)
                (qStep d n δ) v (R N) (stat N)).stepTris Sμ) ≤
            1 - δ ^ 2 * (4 * eN n d - 5) + θ * δ ^ 2

/-- `Lemma53Holds` (the selector (5.7)) is a case of `Lemma53HoldsGen`. -/
theorem lemma53HoldsGen_of_lemma53 {κ : Rd d → ℝ} (h53 : Lemma53Holds d κ) :
    Lemma53HoldsGen d κ := by
  obtain ⟨N₀, h⟩ := h53
  refine ⟨N₀, fun n hn => ?_⟩
  obtain ⟨J, M, B, hM, hB, hθ⟩ := h n hn
  refine ⟨J, M, B, hM, hB, fun θ hθ0 => (hθ θ hθ0).mono fun δ hδ => ?_⟩
  obtain ⟨v, hv, hcube, hmaps, hN⟩ := hδ
  exact ⟨v, fun N => selPts (blockK n) N (qStep d n δ) v,
    fun N => selStat (blockK n) N δ (qStep d n δ) v, hv, hcube, hmaps,
    hN.mono fun N hN => ⟨fun j => measurable_selStat _ _ _ _ v j,
      fun j => selStat_congr _ _ _ _ v j, hN⟩⟩

/-! ## The iteration (5.27) -/

/-- `(1 + x)(1 - y) ≤ e^{-(y - x)}` for `1 - y ≥ 0` (from `1 + t ≤ eᵗ`). -/
theorem one_add_mul_one_sub_le_exp {x y : ℝ} (hy : 0 ≤ 1 - y) :
    (1 + x) * (1 - y) ≤ Real.exp (-(y - x)) := by
  have h1 : 1 + x ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
  have h2 : 1 - y ≤ Real.exp (-y) := by linarith [Real.add_one_le_exp (-y)]
  calc (1 + x) * (1 - y) ≤ Real.exp x * Real.exp (-y) :=
        mul_le_mul h1 h2 hy (Real.exp_pos _).le
    _ = Real.exp (-(y - x)) := by
        rw [← Real.exp_add]
        ring_nf

/-- `0 ∈ V_δ` for `B δ² ≥ 0` and `M δ ≥ 0`. -/
theorem zero_mem_Vdelta {δ M B : ℝ} (hB : 0 ≤ B * δ ^ 2) (hM : 0 ≤ M * δ) :
    (0 : Rd d) ∈ Vdelta δ M B := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [horiz_zero]
    linarith
  · rw [horiz_zero]
    linarith
  · rw [transv_zero, norm_zero]
    exact hM

/-- `e₁ ∈ V_δ` for `B δ² ≥ 0` and `M δ ≥ 0`. -/
theorem e₁_mem_Vdelta (hd : 0 < d) {δ M B : ℝ} (hB : 0 ≤ B * δ ^ 2) (hM : 0 ≤ M * δ) :
    e₁ d ∈ Vdelta δ M B := by
  have ht : transv (e₁ d) = 0 := by
    have h := transv_smul_e₁ hd 1
    rwa [one_smul] at h
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [horiz_e₁ hd]
    linarith
  · rw [horiz_e₁ hd]
    linarith
  · rw [ht, norm_zero]
    exact hM

namespace LParams

variable {P : LParams d} (κ : Rd d → ℝ)

/-- **The iteration (5.27), generic form** (HA4 D7, "Iteration"): if `μ₀ ∈ C_δ`, `T` preserves
`C_δ` (Lemma 5.3 (ii)) and the gain `E ∫ e^{ζH} dν_{I,μ} ≤ b` holds on `C_δ` (Lemma 5.3 (iii)),
with `K q b ≤ e^{-a}` whenever `b ≥ 0`, then `m_r ≤ e^{-r a}` for every depth `r`. -/
theorem Good.mm_le_exp (hP : P.Good) (hκ : IsLFPPKernel κ) {δ M B b a : ℝ}
    (h0 : InCDelta δ M B (P.S 0) (P.mu κ 0))
    (hT : ∀ (Sμ : Finset (Rd d)) (μ : Rd d → ℝ), InCDelta δ M B Sμ μ →
      InCDelta δ M B (P.stepPts Sμ) (P.Tmap κ Sμ μ))
    (hb : ∀ (Sμ : Finset (Rd d)) (μ : Rd d → ℝ), InCDelta δ M B Sμ μ →
      ∫ Y, P.tiltMass Sμ μ Y ∂gLawD κ (P.stepTris Sμ) ≤ b)
    (hab : 0 ≤ b → (P.K : ℝ) * P.q * b ≤ Real.exp (-a)) (r : ℕ) :
    P.mm κ r ≤ Real.exp (-(r * a)) := by
  have hb0 : 0 ≤ b := (hP.integral_tiltMass_pos κ hκ 0).le.trans (hb _ _ h0)
  have hKq : 0 ≤ (P.K : ℝ) * P.q := mul_nonneg (Nat.cast_nonneg _) hP.q_pos.le
  calc P.mm κ r ≤ ((P.K : ℝ) * P.q * b) ^ r := hP.mm_le_pow κ hκ h0 hT hb r
    _ ≤ Real.exp (-a) ^ r := pow_le_pow_left₀ (mul_nonneg hKq hb0) (hab hb0) r
    _ = Real.exp (-(r * a)) := by
        rw [← Real.exp_nat_mul]
        ring_nf

/-- **The iteration (5.27) with the constants of §5** (HA4 D7): if `K q = s = 1 + δ²(e_{n,d}+1)`,
`ν₀^N ∈ C_δ` (`M δ ≥ 0`, `1/N ≤ B δ²`), and Lemma 5.3 (ii) and (iii) hold with `θ = 1`, then
`m_r ≤ e^{-r δ² (β_{n,d} - 7)}` for every depth `r`:
`s (1 - δ²(4e - 6)) ≤ e^{δ²(e+1)} e^{-δ²(4e - 6)} = e^{-δ²(β - 7)}` with `β = 3e`. -/
theorem Good.mm_le_exp_beta (hP : P.Good) (hκ : IsLFPPKernel κ) {n : ℕ} {δ M B : ℝ}
    (hKq : (P.K : ℝ) * P.q = 1 + δ ^ 2 * (eN n d + 1)) (hM : 0 ≤ M * δ)
    (hNB : 1 / (P.N : ℝ) ≤ B * δ ^ 2)
    (hT : ∀ (Sμ : Finset (Rd d)) (μ : Rd d → ℝ), InCDelta δ M B Sμ μ →
      InCDelta δ M B (P.stepPts Sμ) (P.Tmap κ Sμ μ))
    (hb : ∀ (Sμ : Finset (Rd d)) (μ : Rd d → ℝ), InCDelta δ M B Sμ μ →
      ∫ Y, P.tiltMass Sμ μ Y ∂gLawD κ (P.stepTris Sμ) ≤
        1 - δ ^ 2 * (4 * eN n d - 5) + 1 * δ ^ 2) (r : ℕ) :
    P.mm κ r ≤ Real.exp (-(r * (δ ^ 2 * (betaN n d - 7)))) := by
  refine hP.mm_le_exp κ hκ (hP.mu_zero_inCDelta κ hκ hM hNB) hT hb (fun hb0 => ?_) r
  have hy : 0 ≤ 1 - δ ^ 2 * (4 * eN n d - 6) := by linarith
  have key := one_add_mul_one_sub_le_exp (x := δ ^ 2 * (eN n d + 1)) hy
  have e1 : 1 - δ ^ 2 * (4 * eN n d - 5) + 1 * δ ^ 2 = 1 - δ ^ 2 * (4 * eN n d - 6) := by ring
  have e2 : -(δ ^ 2 * (4 * eN n d - 6) - δ ^ 2 * (eN n d + 1)) =
      -(δ ^ 2 * (betaN n d - 7)) := by
    rw [betaN]
    ring
  rw [hKq, e1]
  rw [e2] at key
  exact key

/-- All polygons of all depths lie in `U` when every edge similarity maps `V_δ ⊆ U` into itself
(Lemma 5.3 (i)). -/
theorem Good.polyOf_mem_cube (hP : P.Good) {δ M B : ℝ} (hBδ : 0 ≤ B * δ ^ 2) (hMδ : 0 ≤ M * δ)
    (hcube : Vdelta δ M B ⊆ cube d)
    (hmaps : ∀ j, ∀ i < P.K, MapsTo (P.T j i).app (Vdelta δ M B) (Vdelta δ M B))
    (r : ℕ) (T : DT P.J P.K r) : ∀ z ∈ P.polyOf r T, z ∈ cube d := fun z hz =>
  hcube (hP.mem_polyOf_of_mapsTo hmaps (zero_mem_Vdelta hBδ hMδ)
    (e₁_mem_Vdelta hP.d_pos hBδ hMδ) r T z hz)

end LParams

/-- `1/N ≤ B δ²` for `N ≥ ⌈1/(B δ²)⌉₊` (`B δ² > 0`, `N ≥ 1`). -/
theorem one_div_le_of_ceil_le {N : ℕ} {x : ℝ} (hx : 0 < x) (hN1 : 1 ≤ N)
    (hN : ⌈1 / x⌉₊ ≤ N) : 1 / (N : ℝ) ≤ x := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  exact (one_div_le hNpos hx).2 ((Nat.le_ceil _).trans (by exact_mod_cast hN))

/-- **The iteration (5.27)** under Lemma 5.3 (HA4 D7): for every block level `n ≥ N₀` there is
`J` such that for all small `δ` there are replacement polygons `v` with, for every large Riemann
parameter `N`: the standing hypotheses, all polygons of all depths inside `U`, and
`m_r ≤ e^{-r δ² (β_{n,d} - 7)}` for every depth `r`. -/
theorem iteration (hd : 0 < d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) (h53 : Lemma53Holds d κ) :
    ∃ N₀ : ℕ, ∀ n ≥ N₀, ∃ J : ℕ, ∀ᶠ δ in 𝓝[>] 0, ∃ v : Fin (J + 1) → ℕ → Rd d,
      ∀ᶠ N in atTop, (lowerParams d n N δ v).Good ∧
        (∀ (r : ℕ) (T : DT J (blockK n) r), ∀ z ∈ (lowerParams d n N δ v).polyOf r T,
          z ∈ cube d) ∧
        ∀ r : ℕ, (lowerParams d n N δ v).mm κ r ≤
          Real.exp (-(r * (δ ^ 2 * (betaN n d - 7)))) := by
  obtain ⟨N₀, h⟩ := h53
  refine ⟨N₀, fun n hn => ?_⟩
  obtain ⟨J, M, B, hM, hB, hθ⟩ := h n hn
  refine ⟨J, ?_⟩
  filter_upwards [hθ 1 one_pos, self_mem_nhdsWithin, eventually_qStep_lt_one d n] with
    δ hδ hδ0 hq1
  have hδ0 : 0 < δ := hδ0
  obtain ⟨v, hv, hcube, hmaps, hN⟩ := hδ
  refine ⟨v, ?_⟩
  have hBδ : 0 < B * δ ^ 2 := by positivity
  have hMδ : 0 ≤ M * δ := mul_nonneg hM.le hδ0.le
  filter_upwards [hN, eventually_ge_atTop 1, eventually_ge_atTop ⌈1 / (B * δ ^ 2)⌉₊] with
    N hN hN1 hNB
  have hG : (lowerParams d n N δ v).Good := lowerParams_good hd hN1 hδ0 hq1.le hv
  exact ⟨hG, hG.polyOf_mem_cube hBδ.le hMδ hcube fun j i hi => hmaps j i hi,
    hG.mm_le_exp_beta κ hκ (blockK_mul_qStep d n δ) hMδ (one_div_le_of_ceil_le hBδ hN1 hNB)
      (fun Sμ μ hμ => (hN Sμ μ hμ).1) (fun Sμ μ hμ => (hN Sμ μ hμ).2)⟩

/-! ## The iteration in the form consumed by the existence-free lower comparison -/

/-- **(5.27) with the polygon family fixed before the Riemann parameter** (node S5-ITER of HA4's
DAG, in P-L2a's language).  For every block level `n ≥ N₀` there is `J` such that for all small
`δ` there are replacement polygons `v` and, for each Riemann parameter `N`, a selection statistic
`stat N` reading the root band at the finite set `R N`, such that for all large `N` the
construction `⟨J, K, N, δ^{3/2}, ρ, q, v, R N, stat N⟩` (`K = 2^{n+g_n}`, `ρ = δ(n+2)⁴`,
`q = q_δ`) satisfies the standing hypotheses, all its polygons lie in `U = (-2,2)^d`, and
`m_r ≤ e^{-r δ² (β_{n,d} - 7)}` for every depth `r`. -/
def IterD (d : ℕ) (κ : Rd d → ℝ) : Prop :=
  ∃ N₀ : ℕ, ∀ n ≥ N₀, ∃ J : ℕ, ∀ᶠ δ in 𝓝[>] 0, ∃ (v : Fin (J + 1) → ℕ → Rd d)
      (R : ℕ → Finset (Rd d)) (stat : ℕ → Fin (J + 1) → (Rd d → ℝ) → ℝ),
    ∀ᶠ N in atTop,
      (LParams.mk J (blockK n) N (δ ^ (3 / 2 : ℝ)) (rhoStep n δ) (qStep d n δ) v (R N)
        (stat N)).Good ∧
      (∀ (r : ℕ) (T : DT J (blockK n) r), ∀ z ∈ (LParams.mk J (blockK n) N (δ ^ (3 / 2 : ℝ))
        (rhoStep n δ) (qStep d n δ) v (R N) (stat N)).polyOf r T, z ∈ cube d) ∧
      ∀ r : ℕ, (LParams.mk J (blockK n) N (δ ^ (3 / 2 : ℝ)) (rhoStep n δ) (qStep d n δ) v (R N)
        (stat N)).mm κ r ≤ Real.exp (-(r * (δ ^ 2 * (betaN n d - 7))))

/-- **(5.27)**, node S5-ITER, from Lemma 5.3 for an arbitrary (measurable, local) selection
rule. -/
theorem iterD_of_lemma53Gen (hd : 0 < d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ)
    (h53 : Lemma53HoldsGen d κ) : IterD d κ := by
  obtain ⟨N₀, h⟩ := h53
  refine ⟨N₀, fun n hn => ?_⟩
  obtain ⟨J, M, B, hM, hB, hθ⟩ := h n hn
  refine ⟨J, ?_⟩
  filter_upwards [hθ 1 one_pos, self_mem_nhdsWithin, eventually_qStep_lt_one d n] with
    δ hδ hδ0 hq1
  have hδ0 : 0 < δ := hδ0
  obtain ⟨v, R, stat, hv, hcube, hmaps, hN⟩ := hδ
  refine ⟨v, R, stat, ?_⟩
  have hBδ : 0 < B * δ ^ 2 := by positivity
  have hMδ : 0 ≤ M * δ := mul_nonneg hM.le hδ0.le
  filter_upwards [hN, eventually_ge_atTop 1, eventually_ge_atTop ⌈1 / (B * δ ^ 2)⌉₊] with
    N hN hN1 hNB
  obtain ⟨hmeas, hloc, h23⟩ := hN
  have hG := mkParams_good hd hN1 hδ0 hq1.le hv hmeas hloc
  exact ⟨hG, hG.polyOf_mem_cube hBδ.le hMδ hcube fun j i hi => hmaps j i hi,
    hG.mm_le_exp_beta κ hκ (blockK_mul_qStep d n δ) hMδ (one_div_le_of_ceil_le hBδ hN1 hNB)
      (fun Sμ μ hμ => (h23 Sμ μ hμ).1) (fun Sμ μ hμ => (h23 Sμ μ hμ).2)⟩

/-- **(5.27)**, node S5-ITER, from Lemma 5.3 (with the selector (5.7)). -/
theorem iterD_of_lemma53 (hd : 0 < d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ)
    (h53 : Lemma53Holds d κ) : IterD d κ :=
  iterD_of_lemma53Gen hd hκ (lemma53HoldsGen_of_lemma53 h53)

end HigherDimLFPP.Lower
