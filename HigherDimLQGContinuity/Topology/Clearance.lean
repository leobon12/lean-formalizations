import HigherDimLQGContinuity.Topology.ConvexBall
import HigherDimLQGContinuity.Topology.Junction

/-!
# Lemma 4.1′: clearance around an arc in `d ≥ 3` (bisection on NS-3 with junction balls)

Packet Q1 (ruling N9; replaces the Alexander-duality proof of [C] Lemma 4.1, p. 11, l. 528–549).
Source: planning audit `planning/audits/NA2-section-4.md`, Details (c) **R1** ("Parameters",
"Bisection").

**Statement** (`lemma41_clearance`, explicit form `lemma41_clearance_explicit`). Let `d ≥ 3`,
`A ≥ 1`, `0 < α, β ≤ 1`, and let `γ : [0, 1] → ℝ^d` satisfy the arc moduli (4.1). Let `Ω ⊆ ℝ^d` be
open and convex with `B̄(γ(t), b₀) ⊆ Ω` for all `t`, and `0 < u ≤ min{1, b₀/2}`. Points `x, y ∈ Ω` at
distance `≥ u` from the arc are joined by a path in `Ω` at distance `> c u^{1/(αβ)²}` from the arc,
where `c = [c′_A/(12(1 + 2A^{1+α}))]^{1/(αβ)}`, `c′_A = (3A)^{-1/(αβ)}(2A)^{-1/β}`
(`clearanceConst`, `clearanceConstAux`, `clearanceConstAux_eq`).

**Proof.** Put `r = c u^{1/(αβ)²}`, `ρ = r + A^{1+α}(2r)^{αβ}` and let `m` be least with
`A 2^{-mα} ≤ u/3`. Then (`clearance_params`) `ρ ≤ u/12` (P1) and `A(2ρ + r)^β < 2^{-m}` (P2). By
downward induction on `k ≤ m` (`joinedIn_diff_junctionSet`), `x, y` are joined in `Ω ∖ S_J` for each
dyadic `J = [i 2^{-k}, (i+1) 2^{-k}]`: at `k = m`, `S_J ⊆ B̄(γ(i 2^{-m}), A 2^{-mα} + ρ)` and the
leaves lemma applies; for `k < m`, NS-3 (`HigherDimLQGMetric.Topology.joinedIn_inter_of_joinedIn`)
with `G_i = Ω ∖ S_{J_i}` applies, since `G₁ ∪ G₂ = Ω ∖ B̄(γ(t), ρ)` (splitting identity) has
contractible loops (NS-2′). At `k = 0` the path avoids `S_{[0,1]} ⊇ N̄_r(γ([0, 1]))`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric
open HigherDimLFPP (Rd)

namespace HigherDimLQGContinuity.Topology

open HigherDimLQGMetric.Topology (LoopsContractibleIn joinedIn_inter_of_joinedIn)

variable {d : ℕ}

/-! ### The constants of R1 -/

/-- The constant `c′_A = (3A)^{-1/(αβ)} (2A)^{-1/β}` of R1, written as `(2A (3A)^{1/α})^{-1/β}`
(`clearanceConstAux_eq`). -/
def clearanceConstAux (A α β : ℝ) : ℝ := (2 * A * (3 * A) ^ α⁻¹)⁻¹ ^ β⁻¹

/-- The clearance constant `c = [c′_A / (12 (1 + 2 A^{1+α}))]^{1/(αβ)}` of R1. -/
def clearanceConst (A α β : ℝ) : ℝ :=
  (clearanceConstAux A α β / (12 * (1 + 2 * A ^ (1 + α)))) ^ (α * β)⁻¹

lemma clearanceConstAux_eq {A α β : ℝ} (hA : 0 < A) :
    clearanceConstAux A α β = (3 * A) ^ (-(α * β)⁻¹) * (2 * A) ^ (-β⁻¹) := by
  have h3 : (0 : ℝ) ≤ 3 * A := by positivity
  have h2 : (0 : ℝ) ≤ 2 * A := by positivity
  rw [clearanceConstAux, mul_inv, Real.mul_rpow (inv_nonneg.2 h2)
    (inv_nonneg.2 (Real.rpow_nonneg h3 _)), Real.inv_rpow h2, Real.inv_rpow (Real.rpow_nonneg h3 _),
    ← Real.rpow_mul h3, Real.rpow_neg h3, Real.rpow_neg h2, mul_inv, mul_comm]

lemma clearanceConstAux_pos {A α β : ℝ} (hA : 0 < A) : 0 < clearanceConstAux A α β := by
  unfold clearanceConstAux
  positivity

lemma clearanceConstAux_le_one {A α β : ℝ} (hA : 1 ≤ A) (hα : 0 < α) (hβ : 0 < β) :
    clearanceConstAux A α β ≤ 1 := by
  unfold clearanceConstAux
  have hY : 1 ≤ (3 * A) ^ α⁻¹ := Real.one_le_rpow (by linarith) (inv_nonneg.2 hα.le)
  have hbase : 1 ≤ 2 * A * (3 * A) ^ α⁻¹ := by nlinarith
  exact Real.rpow_le_one (inv_nonneg.2 (by linarith)) (inv_le_one_of_one_le₀ hbase)
    (inv_nonneg.2 hβ.le)

lemma clearanceConst_pos {A α β : ℝ} (hA : 0 < A) : 0 < clearanceConst A α β := by
  unfold clearanceConst
  have := clearanceConstAux_pos (α := α) (β := β) hA
  positivity

lemma clearanceConst_le_one {A α β : ℝ} (hA : 1 ≤ A) (hα : 0 < α) (hβ : 0 < β) :
    clearanceConst A α β ≤ 1 := by
  unfold clearanceConst
  have h1 := clearanceConstAux_le_one hA hα hβ
  have h0 := clearanceConstAux_pos (α := α) (β := β) (by linarith : (0 : ℝ) < A)
  have hK : 1 ≤ 12 * (1 + 2 * A ^ (1 + α)) := by
    have : 0 ≤ A ^ (1 + α) := Real.rpow_nonneg (by linarith) _
    linarith
  refine Real.rpow_le_one (by positivity) ?_ (inv_nonneg.2 (by positivity))
  rw [div_le_one (by linarith)]
  linarith

/-! ### The parameters (P1), (P2) -/

/-- The bisection level: some `m` has `A 2^{-mα} ≤ u/3` and `2^{-m} ≥ ½ (u/(3A))^{1/α}` (the least
`m` with the first property). -/
lemma exists_clearance_level {A α u : ℝ} (hA : 1 ≤ A) (hα : 0 < α) (hu : 0 < u) (hu1 : u ≤ 1) :
    ∃ m : ℕ, A * ((2 : ℝ)⁻¹ ^ m) ^ α ≤ u / 3 ∧
      u ^ α⁻¹ / (2 * (3 * A) ^ α⁻¹) ≤ (2 : ℝ)⁻¹ ^ m := by
  classical
  have hA0 : 0 < A := by linarith
  have hq : ∀ n : ℕ, ((2 : ℝ)⁻¹ ^ n) ^ α = ((2 : ℝ)⁻¹ ^ α) ^ n := by
    intro n
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm, Real.rpow_mul (by norm_num),
      Real.rpow_natCast]
  have hq1 : (2 : ℝ)⁻¹ ^ α < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hα
  have hex : ∃ n : ℕ, A * ((2 : ℝ)⁻¹ ^ n) ^ α ≤ u / 3 := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (show 0 < u / (3 * A) by positivity) hq1
    refine ⟨n, ?_⟩
    rw [hq, ← le_div_iff₀' hA0, div_div]
    exact hn.le
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  -- `X = ½ (u/(3A))^{1/α}`
  have hX : u ^ α⁻¹ / (2 * (3 * A) ^ α⁻¹) = (u / (3 * A)) ^ α⁻¹ / 2 := by
    rw [Real.div_rpow hu.le (by positivity)]
    ring
  rw [hX]
  rcases hm : Nat.find hex with _ | k
  · have : (u / (3 * A)) ^ α⁻¹ ≤ 1 :=
      Real.rpow_le_one (by positivity) (by rw [div_le_one (by positivity)]; linarith)
        (inv_nonneg.2 hα.le)
    rw [pow_zero]
    linarith
  · have hmin := Nat.find_min hex (show k < Nat.find hex by omega)
    push Not at hmin
    have h1 : u / (3 * A) < ((2 : ℝ)⁻¹ ^ k) ^ α := by
      rw [div_lt_iff₀ (by positivity)]
      linarith
    have h2 : (u / (3 * A)) ^ α⁻¹ < (2 : ℝ)⁻¹ ^ k := by
      have := Real.rpow_lt_rpow (by positivity) h1 (inv_pos.2 hα)
      rwa [Real.rpow_rpow_inv (by positivity) hα.ne'] at this
    rw [pow_succ]
    linarith

/-- The parameters of R1: with `r = c u^{1/(αβ)²}` and `ρ = r + A^{1+α}(2r)^{αβ}`, `0 < r`,
`ρ ≤ u/12` (P1), and some level `m` has `A 2^{-mα} ≤ u/3` and `A(2ρ + r)^β < 2^{-m}` (P2). -/
lemma clearance_params {A α β u r ρ : ℝ} (hA : 1 ≤ A) (hα : 0 < α) (hα1 : α ≤ 1) (hβ : 0 < β)
    (hβ1 : β ≤ 1) (hu : 0 < u) (hu1 : u ≤ 1)
    (hr : r = clearanceConst A α β * u ^ ((α * β) ^ 2)⁻¹)
    (hρ : ρ = r + A ^ (1 + α) * (2 * r) ^ (α * β)) :
    0 < r ∧ ρ ≤ u / 12 ∧ ∃ m : ℕ, A * ((2 : ℝ)⁻¹ ^ m) ^ α ≤ u / 3 ∧
      A * (2 * ρ + r) ^ β < (2 : ℝ)⁻¹ ^ m := by
  have hA0 : 0 < A := by linarith
  set ab := α * β with hab_def
  have hab : 0 < ab := mul_pos hα hβ
  have hab1 : ab ≤ 1 := by nlinarith
  set c' := clearanceConstAux A α β with hc'
  set K := 1 + 2 * A ^ (1 + α) with hK
  have hAα : 0 ≤ A ^ (1 + α) := Real.rpow_nonneg hA0.le _
  have hKpos : 0 < K := by rw [hK]; linarith
  have hc'pos : 0 < c' := clearanceConstAux_pos hA0
  have hc'1 : c' ≤ 1 := clearanceConstAux_le_one hA hα hβ
  set c := clearanceConst A α β with hc
  have hcab : c ^ ab = c' / (12 * K) := Real.rpow_inv_rpow (by positivity) hab.ne'
  have hcpos : 0 < c := clearanceConst_pos hA0
  have hc1 : c ≤ 1 := clearanceConst_le_one hA hα hβ
  set w := u ^ ab⁻¹ with hw
  have hwpos : 0 < w := Real.rpow_pos_of_pos hu _
  have hwu : w ≤ u := by
    have := Real.rpow_le_rpow_of_exponent_ge hu hu1 ((one_le_inv₀ hab).2 hab1)
    rwa [Real.rpow_one] at this
  have hr0 : 0 < r := by rw [hr]; exact mul_pos hcpos (Real.rpow_pos_of_pos hu _)
  have hr1 : r ≤ 1 := by
    rw [hr]
    have : u ^ ((α * β) ^ 2)⁻¹ ≤ 1 := Real.rpow_le_one hu.le hu1 (by positivity)
    have h0 : 0 ≤ u ^ ((α * β) ^ 2)⁻¹ := Real.rpow_nonneg hu.le _
    nlinarith
  have hrab : r ^ ab = c' / (12 * K) * w := by
    rw [hr, Real.mul_rpow hcpos.le (Real.rpow_nonneg hu.le _), hcab, ← Real.rpow_mul hu.le, hw]
    congr 2
    field_simp
  -- (P1): `ρ ≤ K r^{αβ} = (c′/12) w ≤ u/12`
  have hρK : ρ ≤ K * r ^ ab := by
    have h1 : r ≤ r ^ ab := Real.self_le_rpow_of_le_one hr0.le hr1 hab1
    have h2 : (2 * r) ^ ab ≤ 2 * r ^ ab := by
      rw [Real.mul_rpow (by norm_num) hr0.le]
      have : (2 : ℝ) ^ ab ≤ 2 := by
        have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hab1
        rwa [Real.rpow_one] at this
      have : 0 ≤ r ^ ab := Real.rpow_nonneg hr0.le _
      nlinarith
    have h3 : A ^ (1 + α) * (2 * r) ^ ab ≤ A ^ (1 + α) * (2 * r ^ ab) :=
      mul_le_mul_of_nonneg_left h2 hAα
    rw [hρ, hK]
    nlinarith
  have hρw : ρ ≤ c' / 12 * w := by
    calc ρ ≤ K * r ^ ab := hρK
      _ = c' / 12 * w := by rw [hrab]; field_simp
  have hρu : ρ ≤ u / 12 := by
    calc ρ ≤ c' / 12 * w := hρw
      _ ≤ 1 / 12 * u := by gcongr
      _ = u / 12 := by ring
  have hrρ : r ≤ ρ := by
    have : 0 ≤ A ^ (1 + α) * (2 * r) ^ ab := by positivity
    rw [hρ]
    linarith
  refine ⟨hr0, hρu, ?_⟩
  -- (P2): `A(2ρ + r)^β ≤ X / 4^β < X ≤ 2^{-m}`, `X = u^{1/α} / (2 (3A)^{1/α})`
  obtain ⟨m, hm1, hm2⟩ := exists_clearance_level hA hα hu hu1
  refine ⟨m, hm1, lt_of_lt_of_le ?_ hm2⟩
  set Y := (3 * A) ^ α⁻¹ with hY
  have hYpos : 0 < Y := Real.rpow_pos_of_pos (by linarith) _
  have h3 : 2 * ρ + r ≤ c' / 4 * w := by linarith
  have hc'β : c' ^ β = (2 * A * Y)⁻¹ := Real.rpow_inv_rpow (by positivity) hβ.ne'
  have hwβ : w ^ β = u ^ α⁻¹ := by
    rw [hw, ← Real.rpow_mul hu.le]
    congr 1
    rw [hab_def]
    field_simp
  have h4 : (2 * ρ + r) ^ β ≤ (2 * A * Y)⁻¹ / 4 ^ β * u ^ α⁻¹ := by
    calc (2 * ρ + r) ^ β ≤ (c' / 4 * w) ^ β :=
          Real.rpow_le_rpow (by linarith) h3 hβ.le
      _ = (2 * A * Y)⁻¹ / 4 ^ β * u ^ α⁻¹ := by
          rw [Real.mul_rpow (by positivity) hwpos.le, Real.div_rpow hc'pos.le (by norm_num),
            hc'β, hwβ]
  have h4β : 1 < (4 : ℝ) ^ β := Real.one_lt_rpow (by norm_num) hβ
  have huα : 0 < u ^ α⁻¹ := Real.rpow_pos_of_pos hu _
  calc A * (2 * ρ + r) ^ β ≤ A * ((2 * A * Y)⁻¹ / 4 ^ β * u ^ α⁻¹) :=
        mul_le_mul_of_nonneg_left h4 hA0.le
    _ = u ^ α⁻¹ / (2 * Y) / 4 ^ β := by field_simp
    _ < u ^ α⁻¹ / (2 * Y) := div_lt_self (by positivity) h4β

/-! ### The bisection -/

/-- **Bisection of Lemma 4.1′.** Under the separation condition `A(2ρ + r)^β < 2^{-m}` and the leaf
condition `A 2^{-mα} + ρ < u ≤ b₀`, points `x, y ∈ Ω` at distance `≥ u` from the arc are joined in
`Ω ∖ S_J` for every dyadic interval `J = [i 2^{-k}, (i+1) 2^{-k}]` of level `k ≤ m`. -/
theorem joinedIn_diff_junctionSet (hd : 3 ≤ d) {γ : ℝ → Rd d} {A α β : ℝ}
    (hγ : ArcModuli γ A α β) (hA : 1 ≤ A) (hα : 0 < α) (hβ : 0 < β)
    {Ω : Set (Rd d)} (hΩ : IsOpen Ω) (hΩc : Convex ℝ Ω) {b₀ : ℝ}
    (hγΩ : ∀ t ∈ Icc (0 : ℝ) 1, closedBall (γ t) b₀ ⊆ Ω)
    {r ρ u : ℝ} (hr : 0 ≤ r) (hρ : ρ = r + A ^ (1 + α) * (2 * r) ^ (α * β)) {m : ℕ}
    (hsep : A * (2 * ρ + r) ^ β < (2 : ℝ)⁻¹ ^ m) (hleaf : A * ((2 : ℝ)⁻¹ ^ m) ^ α + ρ < u)
    (hub₀ : u ≤ b₀) {x y : Rd d} (hx : x ∈ Ω) (hy : y ∈ Ω)
    (hxu : ∀ t ∈ Icc (0 : ℝ) 1, u ≤ dist x (γ t)) (hyu : ∀ t ∈ Icc (0 : ℝ) 1, u ≤ dist y (γ t)) :
    ∀ k ≤ m, ∀ i : ℕ, i < 2 ^ k →
      JoinedIn (Ω \ junctionSet γ m r ρ ((i : ℝ) / 2 ^ k) (((i : ℝ) + 1) / 2 ^ k)) x y := by
  have hA0 : 0 ≤ A := by linarith
  have hρ0 : 0 ≤ ρ := by rw [hρ]; positivity
  have hrρ : r ≤ ρ := by
    have : 0 ≤ A ^ (1 + α) * (2 * r) ^ (α * β) := by positivity
    rw [hρ]
    linarith
  have hleaf0 : 0 ≤ A * ((2 : ℝ)⁻¹ ^ m) ^ α := by positivity
  have hρu : ρ < u := by linarith
  -- dyadic endpoints
  have hend : ∀ k i : ℕ, i < 2 ^ k → 0 ≤ (i : ℝ) / 2 ^ k ∧
      (i : ℝ) / 2 ^ k ≤ ((i : ℝ) + 1) / 2 ^ k ∧ ((i : ℝ) + 1) / 2 ^ k ≤ 1 := by
    intro k i hi
    have h2 : (0 : ℝ) < 2 ^ k := by positivity
    have hi' : (i : ℝ) + 1 ≤ 2 ^ k := by exact_mod_cast hi
    refine ⟨by positivity, div_le_div_of_nonneg_right (by linarith) h2.le, ?_⟩
    rw [div_le_one h2]
    exact hi'
  suffices H : ∀ n k : ℕ, k + n = m → ∀ i : ℕ, i < 2 ^ k →
      JoinedIn (Ω \ junctionSet γ m r ρ ((i : ℝ) / 2 ^ k) (((i : ℝ) + 1) / 2 ^ k)) x y by
    intro k hk i hi
    exact H (m - k) k (by omega) i hi
  intro n
  induction n with
  | zero =>
    -- the leaves: `S_J` lies in a ball `B̄(γ(i 2^{-m}), A 2^{-mα} + ρ)` avoided by `x, y`
    intro k hk i hi
    have hkm : k = m := by omega
    subst hkm
    obtain ⟨ha, hab, hb⟩ := hend k i hi
    have haI : (i : ℝ) / 2 ^ k ∈ Icc (0 : ℝ) 1 := ⟨ha, hab.trans hb⟩
    have hba : ((i : ℝ) + 1) / 2 ^ k - (i : ℝ) / 2 ^ k = (2 : ℝ)⁻¹ ^ k := by
      rw [div_sub_div_same, add_sub_cancel_left, inv_pow, one_div]
    have hsub := junctionSet_subset_closedBall (m := k) hγ hA0 hα hr hrρ ha hab hb
    rw [hba] at hsub
    have hball : closedBall (γ ((i : ℝ) / 2 ^ k)) (A * ((2 : ℝ)⁻¹ ^ k) ^ α + ρ) ⊆ Ω :=
      (closedBall_subset_closedBall (by linarith)).trans (hγΩ _ haI)
    have hfar : ∀ z ∈ Ω, (∀ t ∈ Icc (0 : ℝ) 1, u ≤ dist z (γ t)) →
        z ∈ Ω \ closedBall (γ ((i : ℝ) / 2 ^ k)) (A * ((2 : ℝ)⁻¹ ^ k) ^ α + ρ) := by
      intro z hz hzu
      refine ⟨hz, ?_⟩
      rw [mem_closedBall, not_le]
      have := hzu _ haI
      linarith
    exact (joinedIn_convex_diff_closedBall (by omega) hΩ hΩc hball (hfar x hx hxu)
      (hfar y hy hyu)).mono (sdiff_subset_sdiff_right hsub)
  | succ n ih =>
    -- NS-3 at the midpoint, with the splitting identity and NS-2′
    intro k hk i hi
    have hi1 : 2 * i < 2 ^ (k + 1) := by rw [pow_succ]; omega
    have hi2 : 2 * i + 1 < 2 ^ (k + 1) := by rw [pow_succ]; omega
    have h1 := ih (k + 1) (by omega) (2 * i) hi1
    have h2 := ih (k + 1) (by omega) (2 * i + 1) hi2
    have h2k : (0 : ℝ) < 2 ^ k := by positivity
    have e1 : ((2 * i : ℕ) : ℝ) / 2 ^ (k + 1) = (i : ℝ) / 2 ^ k := by
      push_cast
      rw [pow_succ]
      field_simp
    have e2 : ((2 * i : ℕ) : ℝ) + 1 = ((2 * i + 1 : ℕ) : ℝ) := by push_cast; ring
    have e3 : (((2 * i + 1 : ℕ) : ℝ) + 1) / 2 ^ (k + 1) = ((i : ℝ) + 1) / 2 ^ k := by
      push_cast
      rw [pow_succ]
      field_simp
      ring
    rw [e1, e2] at h1
    rw [e3] at h2
    set a := (i : ℝ) / 2 ^ k with ha_def
    set b := ((i : ℝ) + 1) / 2 ^ k with hb_def
    set t := ((2 * i + 1 : ℕ) : ℝ) / 2 ^ (k + 1) with ht_def
    obtain ⟨ha, -, hb⟩ := hend k i hi
    have hat : a ≤ t := by
      rw [← e1, ht_def]
      exact div_le_div_of_nonneg_right (by push_cast; linarith) (by positivity)
    have htb : t ≤ b := by
      rw [← e3, ht_def]
      exact div_le_div_of_nonneg_right (by linarith) (by positivity)
    have htI : t ∈ Icc (0 : ℝ) 1 := ⟨ha.trans hat, htb.trans hb⟩
    -- `t` is a dyadic point of level `m`
    have htj : ∃ j : ℕ, j ≤ 2 ^ m ∧ t = (j : ℝ) / 2 ^ m := by
      refine ⟨(2 * i + 1) * 2 ^ n, ?_, ?_⟩
      · rw [← hk, show k + (n + 1) = (k + 1) + n by omega, pow_add]
        exact Nat.mul_le_mul_right _ hi2.le
      · have hpow : (2 : ℝ) ^ m = 2 ^ (k + 1) * 2 ^ n := by
          rw [← pow_add, ← hk]
          congr 1
          omega
        rw [ht_def, hpow]
        push_cast
        field_simp
    have hsplit := junctionSet_inter hγ hA hα hβ hr hρ hsep ha hat htb hb htj
    have hballt : closedBall (γ t) ρ ⊆ Ω :=
      (closedBall_subset_closedBall (by linarith)).trans (hγΩ t htI)
    have hW : LoopsContractibleIn
        ((Ω \ junctionSet γ m r ρ a t) ∪ (Ω \ junctionSet γ m r ρ t b)) := by
      rw [← sdiff_inter, hsplit]
      exact loopsContractibleIn_convex_diff_closedBall hd hΩ hΩc hballt
    have hyG : y ∈ (Ω \ junctionSet γ m r ρ a t) ∩ (Ω \ junctionSet γ m r ρ t b) := by
      have hnot : ∀ a' b', 0 ≤ a' → b' ≤ 1 → y ∉ junctionSet γ m r ρ a' b' := by
        intro a' b' ha' hb' hmem
        obtain ⟨s, hs, hys⟩ := exists_dist_le_of_mem_junctionSet hγ hα hr ha' hb' hmem
        rw [max_eq_right hrρ] at hys
        have := hyu s hs
        linarith
      exact ⟨⟨hy, hnot a t ha (htb.trans hb)⟩, ⟨hy, hnot t b (ha.trans hat) hb⟩⟩
    have hJ := joinedIn_inter_of_joinedIn (hΩ.sdiff (isClosed_junctionSet a t))
      (hΩ.sdiff (isClosed_junctionSet t b)) hW hyG h1 h2
    rw [sdiff_inter_sdiff] at hJ
    exact hJ.mono (sdiff_subset_sdiff_right (junctionSet_subset_union hat htb))

/-! ### Lemma 4.1′ -/

/-- **Lemma 4.1′, explicit constant** (R1): clearance `c u^{1/(αβ)²}` with
`c = clearanceConst A α β`. -/
theorem lemma41_clearance_explicit (hd : 3 ≤ d) {A α β : ℝ} (hA : 1 ≤ A) (hα : 0 < α)
    (hα1 : α ≤ 1) (hβ : 0 < β) (hβ1 : β ≤ 1) {γ : ℝ → Rd d} (hγ : ArcModuli γ A α β)
    {Ω : Set (Rd d)} (hΩ : IsOpen Ω) (hΩc : Convex ℝ Ω) {b₀ : ℝ}
    (hγΩ : ∀ t ∈ Icc (0 : ℝ) 1, closedBall (γ t) b₀ ⊆ Ω) {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1)
    (hub : u ≤ b₀ / 2) {x y : Rd d} (hx : x ∈ Ω) (hy : y ∈ Ω)
    (hxu : ∀ t ∈ Icc (0 : ℝ) 1, u ≤ dist x (γ t)) (hyu : ∀ t ∈ Icc (0 : ℝ) 1, u ≤ dist y (γ t)) :
    JoinedIn {w | w ∈ Ω ∧ ∀ t ∈ Icc (0 : ℝ) 1,
      clearanceConst A α β * u ^ ((α * β) ^ 2)⁻¹ < dist w (γ t)} x y := by
  set r := clearanceConst A α β * u ^ ((α * β) ^ 2)⁻¹ with hr
  set ρ := r + A ^ (1 + α) * (2 * r) ^ (α * β) with hρ
  obtain ⟨hr0, hρu, m, hm1, hsep⟩ := clearance_params hA hα hα1 hβ hβ1 hu hu1 hr hρ
  have hub₀ : u ≤ b₀ := by
    have : 0 < b₀ := by linarith
    linarith
  have hJ := joinedIn_diff_junctionSet hd hγ hA hα hβ hΩ hΩc hγΩ hr0.le hρ hsep
    (by linarith) hub₀ hx hy hxu hyu 0 (Nat.zero_le m) 0 (by norm_num)
  simp only [Nat.cast_zero, zero_add, pow_zero, div_one] at hJ
  refine hJ.mono fun w hw => ⟨hw.1, fun t ht => ?_⟩
  by_contra hle
  push Not at hle
  exact hw.2 (mem_junctionSet_iff.2 (Or.inl
    (mem_cthickening_of_dist_le w (γ t) r _ (mem_image_of_mem γ ht) hle)))

/-- **Lemma 4.1′** (clearance; replaces [C] Lemma 4.1's Alexander-duality proof for `d ≥ 3`).
Points at distance `≥ u` from the arc are joined at distance `> c u^{1/(αβ)²}` from it, inside any
convex open `Ω` containing the `b₀`-neighbourhood of the arc. -/
theorem lemma41_clearance (hd : 3 ≤ d) {A α β : ℝ} (hA : 1 ≤ A) (hα : 0 < α) (hα1 : α ≤ 1)
    (hβ : 0 < β) (hβ1 : β ≤ 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ γ : ℝ → Rd d, ArcModuli γ A α β →
    ∀ Ω : Set (Rd d), IsOpen Ω → Convex ℝ Ω → ∀ b₀ : ℝ, 0 < b₀ →
      (∀ t ∈ Icc (0 : ℝ) 1, closedBall (γ t) b₀ ⊆ Ω) →
    ∀ u : ℝ, 0 < u → u ≤ 1 → u ≤ b₀ / 2 → ∀ x y : Rd d, x ∈ Ω → y ∈ Ω →
      (∀ t ∈ Icc (0 : ℝ) 1, u ≤ dist x (γ t)) → (∀ t ∈ Icc (0 : ℝ) 1, u ≤ dist y (γ t)) →
      JoinedIn {w | w ∈ Ω ∧ ∀ t ∈ Icc (0 : ℝ) 1, c * u ^ ((α * β) ^ 2)⁻¹ < dist w (γ t)} x y :=
  ⟨clearanceConst A α β, clearanceConst_pos (by linarith),
    fun _ hγ _ hΩ hΩc _ _ hγΩ _ hu hu1 hub _ _ hx hy hxu hyu =>
      lemma41_clearance_explicit hd hA hα hα1 hβ hβ1 hγ hΩ hΩc hγΩ hu hu1 hub hx hy hxu hyu⟩

end HigherDimLQGContinuity.Topology

end
