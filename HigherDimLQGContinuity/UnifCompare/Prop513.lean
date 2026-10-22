import HigherDimLQGContinuity.Unif5.Cover
import HigherDimLQGMetric.DGZ.CompareProp51

/-!
# The deterministic comparison of DGZ §5 with thresholds uniform in `ξ` (packet U3)

Blueprint Part D, `d:lem-u510` ([1] Prop. 5.10, Lemmas 5.11, 5.12(1), Prop. 5.13; NA3 §2.5, §2.15 rows 14–15;
[8]-bp `r2:prop:510`–`r2:prop:513`). The blueprint tags this node "reused verbatim" (`DGZ.exists_bypassCover`,
`DGZ.bypass`, `DGZ.lemma512`, `DGZ.prop513`). That is true of the deterministic constructions (`bypass`, `lemma512`,
the cover construction), but **not of the statements** `DGZ.prop513`, `DGZ.prop513_setDist` and
`DGZ.cmp_lfppDistance_le`: each of them chooses its threshold `∃ N₀` after `(ξ, Q)` (it is the threshold of
`DGZ.exists_bypassCover`), so the uniform Proposition 5.1 cannot use them (U2's finding, handoff U2 Details M8; erratum
recorded in the U3 handoff). U2's `exists_bypassCover_unif` chooses `N₀ = N₀(d, θ, R)` before `(ξ, Q)`; the proofs below
repeat the sealed proofs with it:

* `prop513_unif`, `prop513_setDist_unif`: `DGZ.prop513`, `DGZ.prop513_setDist` with `∃ N₀` moved in front of
  `∀ ξ Q, 0 < ξ`;
* `cmp_lfppDistance_le_unif`: `DGZ.cmp_lfppDistance_le` with `∃ N₀` in front of `∀ ξ Q, 0 < ξ`, for a general
  sequence parameter `0 < λ ≤ 1/4` (the uniform `λ = uLambda d b μ` of U2's `uNiceParams` in the application) and a
  general `p : NiceParams` with `p.a = dgzSeq λ p.K` (instead of `dgzParams`, which fixes `λ = dgzLambda d Q`);
* `prop513Const_le_of_le`: the constant `prop513Const d ξ L = 2·(4√d·41^d e^{2ξ(L+1)})·L` is monotone in `ξ`, so it is
  bounded on `(0, b]` by its value at `b` (the role of the blueprint's `4 C_L(b)`; the numerical constants differ, the
  dependence on `(d, b, L)` is the same).

The `K`-condition `6ξK + K ≤ K^{3/2}` of the cover is supplied in the application by `DGZ.cmp_exists_K` at `b`
(`6bK + K ≤ K^{3/2}` and `ξ ≤ b`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set

namespace HigherDimLQGContinuity

open HigherDimLQGMetric HigherDimLQGMetric.DGZ
open HigherDimLFPP HigherDimLFPP.Perc
open HigherDimLFPP.DGZ (latPt latPt_apply cbox obox)

variable {d : ℕ}

/-! ## Proposition 5.13, first inequality, with a uniform threshold -/

/-- **DGZ Proposition 5.13, first inequality, path form, with a threshold uniform in `ξ`** (port of
`DGZ.prop513`; `d:lem-u510`): the statement of `DGZ.prop513` with `∃ N₀` (depending only on `d, θ, R`) moved in
front of `∀ ξ Q, 0 < ξ`. -/
theorem prop513_unif (hd : 2 ≤ d) {θ : ℝ} (hθ : 0 < θ) {R : ℕ} (hR : 100 ≤ R) :
    ∃ N₀ : ℕ, ∀ ξ Q : ℝ, 0 < ξ → ∀ p : NiceParams, p.ξ = ξ → p.Q = Q → p.θ = θ → p.R = R →
      ∀ H : ℕ → Rd d → ℝ, (∀ q, Continuous (H q)) → ∀ m : ℕ, 1 ≤ m →
      ∀ {lam : ℝ}, 0 ≤ lam → lam ≤ 3 → 2 ≤ p.K → p.a = dgzSeq lam p.K →
      ∀ {g : ℕ}, 3 ≤ g → (g : ℝ) ≤ lam * (p.K : ℝ) ^ 4 →
      p.a m ≤ p.n → N₀ ≤ p.a 1 → 4 * R ≤ 2 ^ (p.n - p.a m + 1) →
      (∀ j, j < m → 40 * (p.R : ℝ) * p.s j ≤ p.s (j + 1)) →
      6 * p.ξ * p.K + p.K ≤ (p.K : ℝ) ^ ((3 : ℝ) / 2) →
      Real.log 2 ≤ lam * (p.K : ℝ) ^ 3 / 3 → 8 * (41 : ℝ) ^ d ≤ Real.exp ((p.K : ℝ) ^ 3) →
      p.s m ≤ 1 / 100 → 0 < p.L →
      EventJ1 p H m → EventJ2' p H m →
      ∀ {P : ℝ → Rd d} {x y : Rd d}, IsPcwC1Path P x y → MapsTo P (Icc 0 1) (obox (0 : Rd d) 2) →
        y ∉ cbox x (10 * p.s m) →
        ∃ γ' : ℝ → Rd d, IsPcwC1Path γ' (γ' 0) (γ' 1) ∧
          MapsTo γ' (Icc 0 1) (obox (0 : Rd d) 2) ∧
          γ' 0 ∈ cbox x (10 * p.s m) ∧ γ' 1 ∈ cbox y (10 * p.s m) ∧
          lfppLength ξ (H p.n) γ' ≤
            prop513Const d ξ p.L * (2 : ℝ) ^ ((1 - ξ * Q + p.ε) * p.k) *
              lfppLength ξ (H (p.n + p.k)) P := by
  obtain ⟨N₀, hcov₀⟩ := exists_bypassCover_unif hd hθ (by omega : 1 ≤ R)
  refine ⟨N₀, fun ξ Q hξ => ?_⟩
  have hcov := hcov₀ ξ Q hξ
  intro p hpξ hpQ hpθ hpR H hc m hm lam hlam0 hlam3 hK ha g hg3 hg ham hN hCube hgap hKm hr hc8
    hsm hL hJ1 hJ2 P x y hP hPB hxy
  obtain ⟨X, hXlat, hXcov, hsite⟩ := hcov p hpξ hpQ hpθ hpR H hc m hm hlam0 hK ha hg3 hg ham hN
    hCube (fun j _ hjm => hgap j hjm) hKm hJ1 hJ2
  have hmono : Monotone p.a := by
    rw [ha]
    exact dgzSeq_monotone hlam0 (by omega)
  have ha0 : p.a 0 = 0 := by
    rw [ha]
    rfl
  have hs0 : 0 < p.s 0 := p.s_pos 0
  have hRpos : (0 : ℝ) < p.R := by
    rw [hpR]
    exact_mod_cast (by omega : 0 < R)
  -- Lemma 5.12(1) for `P`
  set U : Set (Rd d) := coverU (p.R : ℝ) m p.s X with hUdef
  set T : ℝ := p.L⁻¹ * (2 : ℝ) ^ (-(p.n : ℝ) - (1 - ξ * Q + p.ε) * p.k) with hTdef
  have hT : 0 < T := mul_pos (inv_pos.2 hL) (Real.rpow_pos_of_pos two_pos _)
  have hUo : IsOpen U :=
    isOpen_iUnion fun _ => isOpen_iUnion fun _ => isOpen_iUnion fun _ => isOpen_iUnion fun _ =>
      HigherDimLFPP.DGZ.isOpen_obox _ _
  have hUsat : ∀ x : Zd d, latPt (p.s 0) x ∈ U → obox (latPt (p.s 0) x) (p.s 0) ⊆ U :=
    cmp_coverU_saturated p ha0 hmono ham hXlat
  have hA : ∀ w : Zd d, obox (latPt (p.s 0) w) (p.s 0) ⊆ obox (0 : Rd d) 2 →
      latPt (p.s 0) w ∉ U →
      (∀ v ∈ cbox (latPt (p.s 0) w) (2 * p.s 0), ∀ v' ∈ cbox (latPt (p.s 0) w) (2 * p.s 0),
        |H p.n v - H p.n v'| ≤ p.L + 1) ∧
      T < acrossDist ξ (fun v => H (p.n + p.k) v - H p.n v) (latPt (p.s 0) w) (2 * p.s 0)
        (p.s 0) := by
    intro w h1 h2
    have := hsite w h1 h2
    rw [hpξ, hpQ] at this
    exact this
  have hN1 : 1 ≤ 2 ^ (p.n - p.a 0 + 1) := Nat.one_le_two_pow
  have hsN : p.s 0 * ((2 ^ (p.n - p.a 0 + 1) : ℕ) : ℝ) = 2 := p.s_mul_two_pow 0
  have hsm0 : p.s 0 ≤ p.s m := p.s_le_s hmono (Nat.zero_le m)
  have hxy4 : y ∉ cbox x (4 * p.s 0) := fun h => hxy fun i => (h i).trans (by linarith)
  obtain ⟨γt, hγt, hγtB, hγtlen⟩ := lemma512 hξ.le (hc p.n) (hc (p.n + p.k)) hs0 hN1 hsN hUo
    hUsat hT hA hP hPB hxy4
  -- the bypass
  set s' : ℕ → ℝ := cmpScale p.s m (p.R : ℝ) with hs'def
  set X' : ℕ → Set (Rd d) := fun j => if 1 ≤ j ∧ j < m then X j else ∅ with hX'def
  have hs'le : ∀ j, j ≤ m → s' j = p.s j := fun j hj => cmpScale_of_le hj
  have hXcov' : IsBypassCover ξ (H p.n) (p.R : ℝ) m s' (coverWeight p) X' := by
    have := cmp_isBypassCover_restrict hXcov hs'le
    rwa [hpξ] at this
  have hU' : coverU (p.R : ℝ) m s' X' = U :=
    cmp_coverU_congr (fun j _ hjm => hs'le j hjm.le) fun j hj1 hjm => by
      simp only [hX'def]
      rw [ite_eq_left ⟨hj1, hjm⟩]
  have hweights : (∑ j ∈ Finset.Ico 1 m, 2 * (41 : ℝ) ^ d * coverWeight p j) ≤ 1 / 2 := by
    unfold coverWeight
    rw [ha]
    exact dgz_weights_le hlam0 hlam3 (by omega : 1 ≤ p.K) hr d hc8 m
  have hR100 : (100 : ℝ) ≤ p.R := by
    rw [hpR]
    exact_mod_cast hR
  have hs'm : s' m = p.s m := hs'le m le_rfl
  have hγt0 : γt 0 = x := hγt.source
  have hγt1 : γt 1 = y := hγt.target
  obtain ⟨γ', hγ', hγ'B, hγ'0, hγ'1, hγ'len⟩ := bypass d hd ξ (H p.n) (hc p.n) (p.R : ℝ) m s'
    (coverWeight p) X' hR100 (cmpScale_pos (fun j => p.s_pos j) hRpos)
    (cmpScale_gap hgap) (fun j => (Real.exp_pos _).le) hweights (by rw [hs'm]; exact hsm)
    hXcov' γt (by rw [hγt0, hγt1]; exact hγt) hγtB (by rw [hγt0, hγt1, hs'm]; exact hxy)
  rw [hγt0, hs'm] at hγ'0
  rw [hγt1, hs'm] at hγ'1
  rw [hU'] at hγ'len
  refine ⟨γ', hγ', fun t ht => (hγ'B ht).1, hγ'0, hγ'1, ?_⟩
  have hs0eq : p.s 0 = (2 : ℝ)⁻¹ ^ p.n := by
    unfold NiceParams.s
    rw [ha0, Nat.sub_zero]
  have hratio : p.s 0 / T = p.L * (2 : ℝ) ^ ((1 - ξ * Q + p.ε) * p.k) := by
    rw [hs0eq, hTdef]
    exact cmp_s0_div p.n hL _
  calc lfppLength ξ (H p.n) γ' ≤ 2 * lfppLengthIn ξ (H p.n) γt (obox 0 2 \ U) := hγ'len
    _ ≤ 2 * (lemma512Const d ξ p.L * (p.s 0 / T) * lfppLength ξ (H (p.n + p.k)) P) :=
        mul_le_mul_of_nonneg_left hγtlen (by norm_num)
    _ = prop513Const d ξ p.L * (2 : ℝ) ^ ((1 - ξ * Q + p.ε) * p.k) *
          lfppLength ξ (H (p.n + p.k)) P := by
        rw [hratio, prop513Const]
        ring

/-- **DGZ Proposition 5.13, first inequality, set-distance form, with a threshold uniform in `ξ`** (port of
`DGZ.prop513_setDist`; `d:lem-u510`): on `𝒥₁ ∩ 𝒥₂′`, for `x, y ∈ B₂(0)` with `y ∉ B̄_{10 s_m}(x)`,
`D_n(B̄_{10 s_m}(x), B̄_{10 s_m}(y); B₂(0)) ≤ C 2^{(1-ξQ+ε)k} D_{n+k}(x, y; B₂(0))`, `C = prop513Const d ξ L`, with
`N₀ = N₀(d, θ, R)` chosen before `ξ`. -/
theorem prop513_setDist_unif (hd : 2 ≤ d) {θ : ℝ} (hθ : 0 < θ) {R : ℕ} (hR : 100 ≤ R) :
    ∃ N₀ : ℕ, ∀ ξ Q : ℝ, 0 < ξ → ∀ p : NiceParams, p.ξ = ξ → p.Q = Q → p.θ = θ → p.R = R →
      ∀ H : ℕ → Rd d → ℝ, (∀ q, Continuous (H q)) → ∀ m : ℕ, 1 ≤ m →
      ∀ {lam : ℝ}, 0 ≤ lam → lam ≤ 3 → 2 ≤ p.K → p.a = dgzSeq lam p.K →
      ∀ {g : ℕ}, 3 ≤ g → (g : ℝ) ≤ lam * (p.K : ℝ) ^ 4 →
      p.a m ≤ p.n → N₀ ≤ p.a 1 → 4 * R ≤ 2 ^ (p.n - p.a m + 1) →
      (∀ j, j < m → 40 * (p.R : ℝ) * p.s j ≤ p.s (j + 1)) →
      6 * p.ξ * p.K + p.K ≤ (p.K : ℝ) ^ ((3 : ℝ) / 2) →
      Real.log 2 ≤ lam * (p.K : ℝ) ^ 3 / 3 → 8 * (41 : ℝ) ^ d ≤ Real.exp ((p.K : ℝ) ^ 3) →
      p.s m ≤ 1 / 100 → 0 < p.L →
      EventJ1 p H m → EventJ2' p H m →
      ∀ {x y : Rd d}, x ∈ obox (0 : Rd d) 2 → y ∈ obox (0 : Rd d) 2 →
        y ∉ cbox x (10 * p.s m) →
        lfppSetDist ξ (H p.n) (obox (0 : Rd d) 2) (cbox x (10 * p.s m)) (cbox y (10 * p.s m)) ≤
          prop513Const d ξ p.L * (2 : ℝ) ^ ((1 - ξ * Q + p.ε) * p.k) *
            lfppDistOn ξ (H (p.n + p.k)) (obox (0 : Rd d) 2) x y := by
  obtain ⟨N₀, h⟩ := prop513_unif hd hθ hR
  refine ⟨N₀, fun ξ Q hξ p hpξ hpQ hpθ hpR H hc m hm lam hlam0 hlam3 hK ha g hg3 hg ham hN hCube
    hgap hKm hr hc8 hsm hL hJ1 hJ2 x y hx hy hxy => ?_⟩
  have hC : 0 ≤ prop513Const d ξ p.L * (2 : ℝ) ^ ((1 - ξ * Q + p.ε) * p.k) :=
    mul_nonneg (prop513Const_nonneg d ξ hL.le) (Real.rpow_pos_of_pos two_pos _).le
  refine le_mul_lfppDistOn_of_forall
    (PcwJoined.of_convex (HigherDimLFPP.DGZ.convex_obox 0 2) hx hy) hC fun P hP hPB => ?_
  obtain ⟨γ', hγ', hγ'B, hγ'0, hγ'1, hlen⟩ := h ξ Q hξ p hpξ hpQ hpθ hpR H hc m hm hlam0 hlam3 hK
    ha hg3 hg ham hN hCube hgap hKm hr hc8 hsm hL hJ1 hJ2 hP hPB hxy
  calc lfppSetDist ξ (H p.n) (obox (0 : Rd d) 2) (cbox x (10 * p.s m)) (cbox y (10 * p.s m))
      ≤ lfppDistOn ξ (H p.n) (obox (0 : Rd d) 2) (γ' 0) (γ' 1) := lfppSetDist_le hγ'0 hγ'1
    _ ≤ lfppLength ξ (H p.n) γ' := lfppDistOn_le_lfppLength hγ' hγ'B
    _ ≤ _ := hlen

/-! ## The constant at `b` -/

/-- `ξ ↦ prop513Const d ξ L` is monotone (`L ≥ 0`): on `(0, b]` the constant of Proposition 5.13 is at most its value
at `b` (the role of the blueprint's `4 C_L(b)`, with the repository's bookkeeping constants). -/
theorem prop513Const_le_of_le {ξ ξ' L : ℝ} (hξξ' : ξ ≤ ξ') (hL : 0 ≤ L) :
    prop513Const d ξ L ≤ prop513Const d ξ' L := by
  unfold prop513Const lemma512Const
  have hexp : Real.exp (2 * ξ * (L + 1)) ≤ Real.exp (2 * ξ' * (L + 1)) := by
    refine Real.exp_le_exp.2 ?_
    have h1 : 0 ≤ L + 1 := by linarith
    have h2 : 2 * ξ ≤ 2 * ξ' := by linarith
    exact mul_le_mul_of_nonneg_right h2 h1
  have hc : 0 ≤ 4 * √(d : ℝ) * (41 : ℝ) ^ d := by positivity
  have h3 : 4 * √(d : ℝ) * (41 : ℝ) ^ d * Real.exp (2 * ξ * (L + 1)) ≤
      4 * √(d : ℝ) * (41 : ℝ) ^ d * Real.exp (2 * ξ' * (L + 1)) :=
    mul_le_mul_of_nonneg_left hexp hc
  have h4 := mul_le_mul_of_nonneg_left h3 (by norm_num : (0 : ℝ) ≤ 2)
  exact mul_le_mul_of_nonneg_right h4 hL


/-! ## DGZ's numerical regime -/

/-- **The numerical regime of DGZ's comparison** (the bookkeeping inside `DGZ.cmp_lfppDistance_le`, extracted): for
`0 < λ ≤ 1/4`, `p.a = dgzSeq λ p.K`, `K = p.K ≥ 2` with `40R ≤ 2^{λK⁴}`, and `n = p.n` with `K⁴ ≤ (1-λ)n`,
`8/λ ≤ n` and `4R/λ ≤ n`, the top level `m = dgzLevel λ K n` satisfies the numerical conditions of Proposition 5.13:
`1 ≤ m`, `a_m ≤ n`, `4R ≤ 2^{n-a_m+1}`, `40R s_j ≤ s_{j+1}` for `j < m`, `s_m ≤ 1/100`; moreover
`10 s_m ≤ 2^{-⌊λn/2⌋}` (the radius of Lemma 5.14's good event at `λ' = λ/2`). -/
theorem u3_regime {lam : ℝ} (hlam0 : 0 < lam) (hlam4 : lam ≤ 1 / 4) {R : ℕ} (p : NiceParams)
    (hpR : p.R = R) (hpa : p.a = dgzSeq lam p.K) (hK2 : 2 ≤ p.K)
    (hK40 : 40 * (R : ℝ) ≤ (2 : ℝ) ^ (lam * (p.K : ℝ) ^ 4))
    (hnK : ((p.K ^ 4 : ℕ) : ℝ) ≤ (1 - lam) * p.n) (hn8 : 8 / lam ≤ p.n)
    (hnR : 4 * (R : ℝ) / lam ≤ p.n) :
    1 ≤ dgzLevel lam p.K p.n ∧ p.a (dgzLevel lam p.K p.n) ≤ p.n ∧
      4 * R ≤ 2 ^ (p.n - p.a (dgzLevel lam p.K p.n) + 1) ∧
      (∀ j, j < dgzLevel lam p.K p.n → 40 * (p.R : ℝ) * p.s j ≤ p.s (j + 1)) ∧
      p.s (dgzLevel lam p.K p.n) ≤ 1 / 100 ∧
      10 * p.s (dgzLevel lam p.K p.n) ≤ (2 : ℝ)⁻¹ ^ ⌊lam / 2 * p.n⌋₊ := by
  set K : ℕ := p.K with hKdef
  set n : ℕ := p.n with hndef
  set m : ℕ := dgzLevel lam K n with hmdef
  have hK1 : 1 ≤ K := by omega
  have hmonoa : Monotone p.a := by
    rw [hpa]
    exact dgzSeq_monotone hlam0.le hK1
  obtain ⟨hm1, ham, -⟩ := dgzLevel_spec hlam0.le hK1 hnK
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  -- `a_m ≤ n` and `n - a_m ≥ λ n`
  have hamn' : (dgzSeq lam K m : ℝ) ≤ n := ham.trans (by nlinarith)
  have hpam : p.a m = dgzSeq lam K m := by rw [hpa]
  have hamn : p.a m ≤ p.n := by
    rw [hpam]
    exact_mod_cast hamn'
  have hgapn : lam * n ≤ ((p.n - p.a m : ℕ) : ℝ) := by
    rw [hpam, Nat.cast_sub (by exact_mod_cast hamn')]
    linarith
  have hlamn8 : 8 ≤ lam * n := by
    rw [div_le_iff₀ hlam0] at hn8
    linarith
  have hlamnR : 4 * (R : ℝ) ≤ lam * n := by
    rw [div_le_iff₀ hlam0] at hnR
    linarith
  -- the cube condition
  have hCube : 4 * R ≤ 2 ^ (p.n - p.a m + 1) := by
    have h1 : 4 * R ≤ p.n - p.a m := by
      have : ((4 * R : ℕ) : ℝ) ≤ ((p.n - p.a m : ℕ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    have h2 := Nat.lt_two_pow_self (n := p.n - p.a m + 1)
    omega
  -- the gaps `40 R s_j ≤ s_{j+1}`
  have hgap : ∀ j, j < m → 40 * (p.R : ℝ) * p.s j ≤ p.s (j + 1) := by
    intro j hj
    have hj1n : p.a (j + 1) ≤ p.n := (hmonoa (by omega : j + 1 ≤ m)).trans hamn
    rw [hpR]
    rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · have e := p.s_succ_eq (i := 0) (hmonoa (Nat.zero_le 1)) hj1n
      have ha01 : p.a (0 + 1) - p.a 0 = K ^ 4 := by
        rw [hpa]
        rfl
      rw [ha01] at e
      rw [e]
      refine mul_le_mul_of_nonneg_right ?_ (p.s_pos 0).le
      have hK4nn : (0 : ℝ) ≤ (K : ℝ) ^ 4 := by positivity
      have h1 : (2 : ℝ) ^ (lam * (K : ℝ) ^ 4) ≤ (2 : ℝ) ^ ((K : ℝ) ^ 4) :=
        Real.rpow_le_rpow_of_exponent_le one_le_two (by nlinarith)
      have h2 : (2 : ℝ) ^ ((K : ℝ) ^ 4) = (2 : ℝ) ^ (K ^ 4) := by
        rw [← Real.rpow_natCast 2 (K ^ 4), Nat.cast_pow]
      rw [← h2]
      exact hK40.trans h1
    · have := dgz_rpow_mul_s_le p hlam0.le hK1 hpa hjpos hj1n
      exact (mul_le_mul_of_nonneg_right hK40 (p.s_pos j).le).trans this
  -- `s_m ≤ 1/100` and `10 s_m ≤ 2^{-⌊λn/2⌋}`
  have hsm_le : ∀ t : ℕ, t ≤ p.n - p.a m → p.s m ≤ (2 : ℝ)⁻¹ ^ t := fun t ht =>
    pow_le_pow_of_le_one (by norm_num) (by norm_num) ht
  have hsm : p.s m ≤ 1 / 100 := by
    have h7 : 7 ≤ p.n - p.a m := by
      have : ((7 : ℕ) : ℝ) ≤ ((p.n - p.a m : ℕ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    exact (hsm_le 7 h7).trans (by norm_num)
  have hrad : 10 * p.s m ≤ (2 : ℝ)⁻¹ ^ ⌊lam / 2 * n⌋₊ := by
    set r' : ℕ := ⌊lam / 2 * n⌋₊
    have hr' : (r' : ℝ) ≤ lam / 2 * n := Nat.floor_le (by positivity)
    have h4 : r' + 4 ≤ p.n - p.a m := by
      have : ((r' + 4 : ℕ) : ℝ) ≤ ((p.n - p.a m : ℕ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    calc 10 * p.s m ≤ 10 * (2 : ℝ)⁻¹ ^ (r' + 4) := by linarith [hsm_le (r' + 4) h4]
      _ = 10 / 16 * (2 : ℝ)⁻¹ ^ r' := by rw [pow_add]; norm_num; ring
      _ ≤ (2 : ℝ)⁻¹ ^ r' := by
        have : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ r' := by positivity
        linarith
  exact ⟨hm1, hamn, hCube, hgap, hsm, hrad⟩

/-- **The numerical conditions on `K`, for all large `K`** (the threshold form of `DGZ.cmp_exists_K`, whose proof
gives every `K ≥ ⌈M⌉`): there is `K₁` such that every `K ≥ K₁` has `K ≥ 2`, `N₀ ≤ K⁴`, `3 ≤ λK⁴`,
`40R ≤ 2^{λK⁴}`, `6ξK + K ≤ K^{3/2}`, `log 2 ≤ λK³/3` and `8·41^d ≤ e^{K³}`. -/
theorem u3_exists_K_threshold {lam : ℝ} (ξ : ℝ) (hlam : 0 < lam) (R N₀ d : ℕ) :
    ∃ K₁ : ℕ, ∀ K : ℕ, K₁ ≤ K → 2 ≤ K ∧ N₀ ≤ K ^ 4 ∧ (3 : ℝ) ≤ lam * (K : ℝ) ^ 4 ∧
      40 * (R : ℝ) ≤ (2 : ℝ) ^ (lam * (K : ℝ) ^ 4) ∧
      6 * ξ * K + K ≤ (K : ℝ) ^ ((3 : ℝ) / 2) ∧
      Real.log 2 ≤ lam * (K : ℝ) ^ 3 / 3 ∧ 8 * (41 : ℝ) ^ d ≤ Real.exp ((K : ℝ) ^ 3) := by
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  set M : ℝ := max (max (max 2 (N₀ : ℝ)) (max (3 / lam) (40 * R / (lam * Real.log 2))))
    (max (max ((6 * ξ + 1) ^ 2) (3 * Real.log 2 / lam)) (8 * 41 ^ d)) with hMdef
  refine ⟨⌈M⌉₊, fun K hK => ?_⟩
  have hKM : M ≤ (K : ℝ) := (Nat.le_ceil M).trans (by exact_mod_cast hK)
  have hall := hKM
  simp only [hMdef, max_le_iff] at hall
  obtain ⟨⟨⟨h2, hN⟩, h3, h40⟩, ⟨h6, hl⟩, h8⟩ := hall
  have hK1 : (1 : ℝ) ≤ K := by linarith
  have hKpos : (0 : ℝ) < K := by linarith
  have hK4 : (K : ℝ) ≤ (K : ℝ) ^ 4 := le_self_pow₀ hK1 (by norm_num)
  have hK3' : (K : ℝ) ≤ (K : ℝ) ^ 3 := le_self_pow₀ hK1 (by norm_num)
  refine ⟨by exact_mod_cast h2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : (N₀ : ℝ) ≤ ((K ^ 4 : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  · rw [div_le_iff₀ hlam] at h3
    nlinarith
  · have hy : 40 * (R : ℝ) ≤ lam * (K : ℝ) ^ 4 * Real.log 2 := by
      rw [div_le_iff₀ (mul_pos hlam hlog)] at h40
      have := mul_le_mul_of_nonneg_right hK4 (mul_pos hlam hlog).le
      nlinarith
    have hexp := Real.add_one_le_exp (Real.log 2 * (lam * (K : ℝ) ^ 4))
    rw [Real.rpow_def_of_pos two_pos]
    nlinarith
  · rw [cmp_rpow_three_halves hKpos]
    have hs : 6 * ξ + 1 ≤ √(K : ℝ) :=
      (le_abs_self _).trans (Real.abs_le_sqrt h6)
    nlinarith
  · rw [div_le_iff₀ hlam] at hl
    nlinarith
  · have := Real.add_one_le_exp ((K : ℝ) ^ 3)
    linarith

/-! ## The deterministic comparison of Proposition 5.1 -/

/-- **The comparison of D-5.1, deterministic, with a threshold uniform in `ξ`** (port of `DGZ.cmp_lfppDistance_le`;
`d:lem-u510` with `d:lem-u514`'s good event): there is `N₀ = N₀(d, θ, R)` such that for every `ξ > 0`, `Q`, every
sequence parameter `0 < λ ≤ 1/4` and every `p : NiceParams` with `p.a = dgzSeq λ p.K`: on `𝒥₁ ∩ 𝒥₂′` (top level
`m = dgzLevel λ K n`) and the good event of Lemma 5.14 (`λ' = λ/2`), in DGZ's parameter regime,
`D_n(0, e₁; B₂(0)) ≤ (3/2) C_13 2^{(1-ξQ+ε)k} D_{n+k}(0, e₁; B₂(0))`, `C_13 = prop513Const d ξ L`. -/
theorem cmp_lfppDistance_le_unif (hd : 2 ≤ d) {θ : ℝ} (hθ : 0 < θ) {R : ℕ} (hR : 100 ≤ R) :
    ∃ N₀ : ℕ, ∀ ξ Q : ℝ, 0 < ξ → ∀ lam : ℝ, 0 < lam → lam ≤ 1 / 4 →
      ∀ p : NiceParams, p.ξ = ξ → p.Q = Q → p.θ = θ → p.R = R → p.a = dgzSeq lam p.K →
      ∀ (u : ℝ) (H : ℕ → Rd d → ℝ), (∀ q, Continuous (H q)) →
      2 ≤ p.K → N₀ ≤ p.K ^ 4 → (3 : ℝ) ≤ lam * (p.K : ℝ) ^ 4 →
      40 * (R : ℝ) ≤ (2 : ℝ) ^ (lam * (p.K : ℝ) ^ 4) →
      6 * ξ * p.K + p.K ≤ (p.K : ℝ) ^ ((3 : ℝ) / 2) →
      Real.log 2 ≤ lam * (p.K : ℝ) ^ 3 / 3 → 8 * (41 : ℝ) ^ d ≤ Real.exp ((p.K : ℝ) ^ 3) →
      0 < p.L → ((p.K ^ 4 : ℕ) : ℝ) ≤ (1 - lam) * p.n → 8 / lam ≤ p.n →
      4 * (R : ℝ) / lam ≤ p.n →
      EventJ1 p H (dgzLevel lam p.K p.n) → EventJ2' p H (dgzLevel lam p.K p.n) →
      Lemma514Good ξ Q u (lam / 2) (H p.n) p.n →
      lfppDistance d ξ (H p.n) ≤
        3 / 2 * prop513Const d ξ p.L * (2 : ℝ) ^ ((1 - ξ * Q + p.ε) * p.k) *
          lfppDistance d ξ (H (p.n + p.k)) := by
  obtain ⟨N₀, h513⟩ := prop513_unif hd hθ hR
  refine ⟨N₀, fun ξ Q hξ lam hlam0 hlam4 p hpξ hpQ hpθ hpR hpa u H hc hK2 hKN₀ hK3 hK40 hK6 hKlog
    hK8 hL hnK hn8 hnR hJ1 hJ2 hG => ?_⟩
  obtain ⟨hm1, hamn, hCube, hgap, hsm, hrad⟩ :=
    u3_regime hlam0 hlam4 p hpR hpa hK2 hK40 hnK hn8 hnR
  set n : ℕ := p.n with hndef
  set m : ℕ := dgzLevel lam p.K n with hmdef
  have he₁ : e₁ d ∉ cbox (0 : Rd d) (10 * p.s m) := by
    intro h
    have h0 := h ⟨0, by omega⟩
    rw [PiLp.zero_apply, sub_zero, e₁_ofLp] at h0
    simp only [ite_true, abs_one] at h0
    linarith
  have hcbox : ∀ {c x : Rd d}, x ∈ cbox c (10 * p.s m) →
      x ∈ cbox c ((2 : ℝ)⁻¹ ^ ⌊lam / 2 * n⌋₊) :=
    fun hx i => (hx i).trans hrad
  -- every path from `0` to `e₁` controls `D_n(0, e₁)`
  have hC : 0 ≤ 3 / 2 * prop513Const d ξ p.L * (2 : ℝ) ^ ((1 - ξ * Q + p.ε) * p.k) := by
    have : 0 ≤ prop513Const d ξ p.L := prop513Const_nonneg d ξ hL.le
    positivity
  have hK6' : 6 * p.ξ * p.K + p.K ≤ (p.K : ℝ) ^ ((3 : ℝ) / 2) := by
    rw [hpξ]
    exact hK6
  have hN₀a : N₀ ≤ p.a 1 := by
    rw [hpa]
    exact hKN₀
  have key : ∀ P : ℝ → Rd d, IsPcwC1Path P 0 (e₁ d) → MapsTo P (Icc 0 1) (obox (0 : Rd d) 2) →
      lfppDistance d ξ (H n) ≤ 3 / 2 * prop513Const d ξ p.L *
        (2 : ℝ) ^ ((1 - ξ * Q + p.ε) * p.k) * lfppLength ξ (H (n + p.k)) P := by
    intro P hP hPB
    obtain ⟨γ', hγ', hγ'B, hγ'0, hγ'1, hγ'len⟩ := h513 ξ Q hξ p hpξ hpQ hpθ hpR H hc m hm1
      hlam0.le (by linarith) hK2 hpa (g := 3) le_rfl (by push_cast; exact hK3) hamn hN₀a hCube
      hgap hK6' hKlog hK8 hsm hL hJ1 hJ2 hP hPB he₁
    have h1 := lfppDistance_le_of_lemma514Good (hc n) hG hγ' hγ'B (hcbox hγ'0) (hcbox hγ'1)
    calc lfppDistance d ξ (H n) ≤ 3 / 2 * lfppLength ξ (H n) γ' := h1
      _ ≤ 3 / 2 * (prop513Const d ξ p.L * (2 : ℝ) ^ ((1 - ξ * Q + p.ε) * p.k) *
            lfppLength ξ (H (n + p.k)) P) := mul_le_mul_of_nonneg_left hγ'len (by norm_num)
      _ = 3 / 2 * prop513Const d ξ p.L * (2 : ℝ) ^ ((1 - ξ * Q + p.ε) * p.k) *
            lfppLength ξ (H (n + p.k)) P := by ring
  rw [cmp_lfppDistance_eq_obox ξ (H (n + p.k))]
  exact le_mul_lfppDistOn_of_forall (PcwJoined.of_convex (HigherDimLFPP.DGZ.convex_obox 0 2)
    cmp_zero_mem_obox_two cmp_e₁_mem_obox_two) hC key

/-! ## The blueprint form of `d:lem-u510` -/

/-- **The deterministic comparison of DGZ §5, uniformly** (`d:lem-u510` in the blueprint's quantifier order; [1]
Prop. 5.10, Lemmas 5.11, 5.12(1), Prop. 5.13): for `d ≥ 2`, `θ > 0`, `0 < λ ≤ 1/4`, `R ≥ 100` and `b` there is `K₁`
such that for every `K ≥ K₁` there is `n₀` such that for every `ξ ∈ (0, b]`, `Q`, and every `p : NiceParams` with
`p.ξ = ξ`, `p.Q = Q`, `p.θ = θ`, `p.R = R`, `p.K = K`, `p.a = dgzSeq λ K`, `p.n ≥ n₀`, `p.L > 0`: on `𝒥₁ ∩ 𝒥₂′`
(top level `m = dgzLevel λ K n`), for all `x, y ∈ B₂(0)` with `|x - y|_∞ > 10 s_m`,
`D_n(B̄_{10 s_m}(x), B̄_{10 s_m}(y); B₂(0)) ≤ C_13(b, L) 2^{(1-ξQ+ε)k} D_{n+k}(x, y; B₂(0))`, with
`C_13(b, L) = prop513Const d b L = 8√d·41^d e^{2b(L+1)} L` (in place of the blueprint's
`4 C_L(b) = 4(2+√d)5^d L e^{2b(L+1)}`: the repository's Lemma 5.12(1) has the bookkeeping constant
`lemma512Const = 4√d·41^d e^{2ξ(L+1)}`). -/
theorem lemma510_unif (hd : 2 ≤ d) {b θ lam : ℝ} (hθ : 0 < θ) (hlam0 : 0 < lam)
    (hlam4 : lam ≤ 1 / 4) {R : ℕ} (hR : 100 ≤ R) :
    ∃ K₁ : ℕ, ∀ K : ℕ, K₁ ≤ K → ∃ n₀ : ℕ, ∀ ξ Q : ℝ, 0 < ξ → ξ ≤ b →
      ∀ p : NiceParams, p.ξ = ξ → p.Q = Q → p.θ = θ → p.R = R → p.K = K →
      p.a = dgzSeq lam K → n₀ ≤ p.n → 0 < p.L →
      ∀ H : ℕ → Rd d → ℝ, (∀ q, Continuous (H q)) →
      EventJ1 p H (dgzLevel lam K p.n) → EventJ2' p H (dgzLevel lam K p.n) →
      ∀ {x y : Rd d}, x ∈ obox (0 : Rd d) 2 → y ∈ obox (0 : Rd d) 2 →
        y ∉ cbox x (10 * p.s (dgzLevel lam K p.n)) →
        lfppSetDist ξ (H p.n) (obox (0 : Rd d) 2) (cbox x (10 * p.s (dgzLevel lam K p.n)))
            (cbox y (10 * p.s (dgzLevel lam K p.n))) ≤
          prop513Const d b p.L * (2 : ℝ) ^ ((1 - ξ * Q + p.ε) * p.k) *
            lfppDistOn ξ (H (p.n + p.k)) (obox (0 : Rd d) 2) x y := by
  obtain ⟨N₀, h513⟩ := prop513_setDist_unif hd hθ hR
  obtain ⟨K₁, hK₁⟩ := u3_exists_K_threshold b hlam0 R N₀ d
  refine ⟨K₁, fun K hK => ?_⟩
  obtain ⟨hK2, hKN₀, hK3, hK40, hK6, hKlog, hK8⟩ := hK₁ K hK
  have h1lam : 0 < 1 - lam := by linarith
  set M : ℝ := max (((K ^ 4 : ℕ) : ℝ) / (1 - lam)) (max (8 / lam) (4 * (R : ℝ) / lam)) with hMdef
  refine ⟨⌈M⌉₊, fun ξ Q hξ hξb p hpξ hpQ hpθ hpR hpK hpa hn hL H hc hJ1 hJ2 x y hx hy hxy => ?_⟩
  subst hpK
  have hnM : M ≤ p.n := (Nat.le_ceil _).trans (by exact_mod_cast hn)
  simp only [hMdef, max_le_iff] at hnM
  obtain ⟨hnK, hn8, hnR⟩ := hnM
  rw [div_le_iff₀ h1lam] at hnK
  have hnK' : ((p.K ^ 4 : ℕ) : ℝ) ≤ (1 - lam) * p.n := by linarith
  obtain ⟨hm1, hamn, hCube, hgap, hsm, -⟩ := u3_regime hlam0 hlam4 p hpR hpa hK2 hK40 hnK' hn8 hnR
  have hK6ξ : 6 * p.ξ * p.K + p.K ≤ (p.K : ℝ) ^ ((3 : ℝ) / 2) := by
    have hK0 : (0 : ℝ) ≤ p.K := Nat.cast_nonneg _
    have : 6 * p.ξ * p.K ≤ 6 * b * p.K := by
      rw [hpξ]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hξb (by norm_num)) hK0
    linarith
  have hN₀a : N₀ ≤ p.a 1 := by
    rw [hpa]
    exact hKN₀
  have hmain := h513 ξ Q hξ p hpξ hpQ hpθ hpR H hc (dgzLevel lam p.K p.n) hm1 hlam0.le
    (by linarith) hK2 hpa (g := 3) le_rfl (by push_cast; exact hK3) hamn hN₀a hCube hgap hK6ξ hKlog
    hK8 hsm hL hJ1 hJ2 hx hy hxy
  refine hmain.trans ?_
  have hX : 0 ≤ (2 : ℝ) ^ ((1 - ξ * Q + p.ε) * p.k) := (Real.rpow_pos_of_pos two_pos _).le
  have hD : 0 ≤ lfppDistOn ξ (H (p.n + p.k)) (obox (0 : Rd d) 2) x y := lfppDistOn_nonneg _ _ _ _ _
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (prop513Const_le_of_le hξb hL.le) hX) hD

end HigherDimLQGContinuity
