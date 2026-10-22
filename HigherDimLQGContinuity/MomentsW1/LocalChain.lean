import HigherDimLQGContinuity.Core.Interfaces
import HigherDimLQGContinuity.MomentsW1.BadScaleDefs
import HigherDimLQGMetric.DGZ.Functionals
import HigherDimLQGMetric.DGZ.ChainLink
import HigherDimLQGMetric.DGZ.Chain

/-!
# Local deterministic estimates for Appendix A, W1

The direct segment estimate is the terminal-scale case of the localized chaining argument.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Relation

namespace HigherDimLQGContinuity

open HigherDimLFPP HigherDimLFPP.Perc
open HigherDimLFPP.DGZ (latPt latPt_apply obox convex_obox mem_obox_self roundLat
  abs_latPt_roundLat_sub_lt)
open HigherDimLQGMetric.DGZ

variable {d : ℕ}

/-- The direct segment part of localized chaining. -/
theorem wnLocalChain_segment {φ : Rd d → ℝ} (hφ : Continuous φ)
    (ξ : ℝ) (z : Rd d) {s M : ℝ} (hs : 0 < s)
    (hM : ∀ w ∈ ball z (3 / 2 * s), ξ * φ w ≤ M)
    {x y : Rd d} (hx : x ∈ ball z s) (hy : y ∈ ball z s) :
    lfppDistOn ξ φ (ball z (3 / 2 * s)) x y ≤ 2 * s * Real.exp M := by
  have hscale : s ≤ 3 / 2 * s := by nlinarith
  have hx' : x ∈ ball z (3 / 2 * s) := ball_subset_ball hscale hx
  have hy' : y ∈ ball z (3 / 2 * s) := ball_subset_ball hscale hy
  have hxy : ‖y - x‖ ≤ 2 * s := by
    have h1 : dist x y < 2 * s := by
      calc
        dist x y ≤ dist x z + dist z y := dist_triangle _ _ _
        _ < s + s := add_lt_add (mem_ball.1 hx) (by simpa only [dist_comm] using (mem_ball.1 hy))
        _ = 2 * s := by ring
    simpa only [dist_eq_norm, norm_sub_rev] using h1.le
  calc
    lfppDistOn ξ φ (ball z (3 / 2 * s)) x y
        ≤ Real.exp M * ‖y - x‖ :=
          lfppDistOn_le_exp_mul_norm_of_convex hφ (convex_ball _ _) hx' hy' hM
    _ ≤ Real.exp M * (2 * s) := mul_le_mul_of_nonneg_left hxy (Real.exp_pos _).le
    _ = 2 * s * Real.exp M := mul_comm _ _

/-- A free-site link in an arbitrary box, with margins at both endpoints. -/
theorem wnLocalChain_link {φ : Rd d → ℝ} (hφ : Continuous φ)
    {ξ c ρ s : ℝ} (hs : 0 < s) (hc : 0 ≤ c) (w : Rd d)
    {O : Set (Zd d)} {D L : ℕ} (hsmall : SmallClusters O D)
    {u v : Zd d} (hu : FreeSite O u) (hv : FreeSite O v)
    (huv : WithinInf (L : ℤ) u v)
    (hmu : ∀ i, |latPt s u i - w i| + ((D + 3 : ℕ) : ℝ) * s ≤ ρ)
    (hmv : ∀ i, |latPt s v i - w i| + ((D + 3 : ℕ) : ℝ) * s ≤ ρ)
    (hcost : ∀ z ∈ O, obox (latPt s z) (2 * s) ⊆ obox w ρ →
      ∀ z', LAdj z z' →
        lfppDistOn ξ φ (obox (latPt s z) (2 * s)) (latPt s z) (latPt s z') ≤ c) :
    lfppDistOn ξ φ (obox w ρ) (latPt s u) (latPt s v) ≤
      (((2 * (L + D + 1) + 1 : ℕ) : ℝ) ^ d) * c := by
  classical
  let hull : Set (Zd d) := {z | ∀ i, min (u i) (v i) ≤ z i ∧ z i ≤ max (u i) (v i)}
  have huh : u ∈ hull := fun i => ⟨min_le_left _ _, le_max_left _ _⟩
  obtain ⟨γ, hγ, hγh, hγl, hγS⟩ := exists_lAdj_chain_of_reflTransGen huh
    (reflTransGen_of_forall_between (S := hull) fun z hz => hz)
  have hsurg := freeSurgery d O D hsmall γ u v hγ hγh hγl hu hv
  let T : Set (Zd d) := {y | y ∈ O ∧ ∃ x ∈ γ, WithinInf ((D : ℤ) + 1) y x}
  have huT : u ∈ T :=
    ⟨hu.1, u, List.mem_of_mem_head? hγh, withinInf_refl (by positivity) u⟩
  obtain ⟨l, hnd, hch, hlh, hll, hlT⟩ :=
    HigherDimLFPP.DGZ.exists_nodup_isChain_of_reflTransGen huT hsurg
  have hTint : ∀ y ∈ T, WithinInf ((L + D + 1 : ℕ) : ℤ) y u := by
    rintro y ⟨-, x, hxγ, hyx⟩ i
    have hx := hγS x hxγ i
    have hxu : |x i - u i| ≤ (L : ℤ) := by
      have hvu := huv i
      rw [abs_le] at hvu ⊢
      rcases le_total (u i) (v i) with h | h
      · rw [min_eq_left h, max_eq_right h] at hx
        omega
      · rw [min_eq_right h, max_eq_left h] at hx
        omega
    have hyx' := hyx i
    rw [abs_le] at hxu hyx' ⊢
    push_cast
    omega
  have hTreal : ∀ y ∈ T, ∀ i, |latPt s y i - w i| + 2 * s ≤ ρ := by
    rintro y ⟨-, x, hxγ, hyx⟩ i
    have hx := hγS x hxγ i
    have hxmin : min (latPt s u i) (latPt s v i) ≤ latPt s x i := by
      rw [latPt_apply, latPt_apply, latPt_apply]
      have hxu : min (u i : ℝ) (v i : ℝ) ≤ (x i : ℝ) := by exact_mod_cast hx.1
      rw [← mul_min_of_nonneg (u i:ℝ) (v i:ℝ) hs.le]
      exact mul_le_mul_of_nonneg_left hxu hs.le
    have hxmax : latPt s x i ≤ max (latPt s u i) (latPt s v i) := by
      rw [latPt_apply, latPt_apply, latPt_apply]
      have hxv : (x i : ℝ) ≤ max (u i : ℝ) (v i : ℝ) := by exact_mod_cast hx.2
      rw [← mul_max_of_nonneg (u i:ℝ) (v i:ℝ) hs.le]
      exact mul_le_mul_of_nonneg_left hxv hs.le
    have hxm : |latPt s x i - w i| + ((D + 3 : ℕ) : ℝ) * s ≤ ρ := by
      have hu' := hmu i
      have hv' := hmv i
      rcases le_total (latPt s u i) (latPt s v i) with h | h
      · rw [min_eq_left h] at hxmin
        rw [max_eq_right h] at hxmax
        have habs : |latPt s x i - w i| ≤ ρ - ((D + 3 : ℕ) : ℝ) * s := by
          apply (abs_le).2
          constructor
          · linarith [neg_le_abs (latPt s u i - w i)]
          · linarith [le_abs_self (latPt s v i - w i)]
        linarith
      · rw [min_eq_right h] at hxmin
        rw [max_eq_left h] at hxmax
        have habs : |latPt s x i - w i| ≤ ρ - ((D + 3 : ℕ) : ℝ) * s := by
          apply (abs_le).2
          constructor
          · linarith [neg_le_abs (latPt s v i - w i)]
          · linarith [le_abs_self (latPt s u i - w i)]
        linarith
    have h1 := abs_latPt_sub_le_of_withinInf hs.le hyx i
    have h3 := abs_sub_le (latPt s y i) (latPt s x i) (w i)
    push_cast at h1
    have hcoeff : s * ((D : ℝ) + 1) + 2 * s =
        ((D + 3 : ℕ) : ℝ) * s := by push_cast; ring
    linarith
  have hTV : ∀ y ∈ T, latPt s y ∈ obox w ρ := by
    intro y hy i
    have h := hTreal y hy i
    exact lt_of_lt_of_le (by nlinarith : |latPt s y i - w i| <
      |latPt s y i - w i| + 2 * s) h
  have hTbox : ∀ y ∈ T, obox (latPt s y) (2 * s) ⊆ obox w ρ := by
    intro y hy z hz i
    have h1 := hz i
    have h2 := hTreal y hy i
    have h3 := abs_sub_le (z i) (latPt s y i) (w i)
    linarith
  have hstep : ∀ x ∈ T, ∀ y ∈ T, LAdj x y →
      lfppDistOn ξ φ (obox w ρ) (latPt s x) (latPt s y) ≤ c := by
    intro x hx y _ hxy
    have hyb : latPt s y ∈ obox (latPt s x) (2 * s) := fun i => by
      have h1 := abs_latPt_sub_le_of_withinInf hs.le (LAdj.withinInf hxy).symm i
      push_cast at h1
      linarith
    calc
      lfppDistOn ξ φ (obox w ρ) (latPt s x) (latPt s y)
          ≤ lfppDistOn ξ φ (obox (latPt s x) (2 * s)) (latPt s x) (latPt s y) :=
            lfppDistOn_mono (hTbox x hx)
              (PcwJoined.of_convex (convex_obox _ _) (mem_obox_self _ (by positivity)) hyb)
      _ ≤ c := hcost x hx.1 (hTbox x hx) y hxy
  have hchain := lfppDistOn_le_mul_of_isChain hφ (convex_obox w ρ) hTV hstep l u v hch
    hlh hll hlT
  have hlen : l.length ≤ (2 * (L + D + 1) + 1) ^ d := by
    rw [← List.toFinset_card_of_nodup hnd, ← card_boxF u (L + D + 1)]
    refine Finset.card_le_card fun y hy => ?_
    rw [List.mem_toFinset] at hy
    exact (mem_boxF).2 (hTint y (hlT y hy))
  calc
    lfppDistOn ξ φ (obox w ρ) (latPt s u) (latPt s v)
        ≤ ((l.length - 1 : ℕ) : ℝ) * c := hchain
    _ ≤ (((2 * (L + D + 1) + 1 : ℕ) : ℝ) ^ d) * c := by
      refine mul_le_mul_of_nonneg_right ?_ hc
      rw [← Nat.cast_pow]
      exact_mod_cast (Nat.sub_le _ _).trans hlen

/-- A free lattice point approximating any prescribed position, with a fine-scale free refinement. -/
theorem wnLocalChain_point (hd : 2 ≤ d) {O : ℕ → Set (Zd d)} {ℓ n : ℕ}
    (hℓ : 110 ≤ ℓ) (hℓn : ℓ < n)
    (hE : SmallClusters (O ℓ) (wnBadDiameter ℓ))
    (hF : ℓ + 1 < n → ∀ x : Zd d, ∃ y : Zd d,
      WithinInf (((ℓ + 1 : ℕ) : ℤ) ^ 2) x (2 • y) ∧
      FreeSite (O (ℓ + 1)) (2 • y) ∧ FreeSite (O ℓ) y)
    (v : Rd d) :
    ∃ u : Zd d, FreeSite (O ℓ) u ∧
      (∀ i, |latPt ((2 : ℝ)⁻¹ ^ ℓ) u i - v i| ≤
        (ℓ : ℝ) ^ 2 * (2 : ℝ)⁻¹ ^ ℓ) ∧
      (ℓ + 1 < n → FreeSite (O (ℓ + 1)) (2 • u)) := by
  rcases Nat.lt_or_ge (ℓ + 1) n with h | h
  · let s : ℝ := (2 : ℝ)⁻¹ ^ (ℓ + 1)
    have hs : 0 < s := by dsimp [s]; positivity
    obtain ⟨u, hu, hu₂, hu₁⟩ := hF h (roundLat s v)
    refine ⟨u, hu₁, fun i => ?_, fun _ => hu₂⟩
    have h1 := abs_latPt_sub_le_of_withinInf hs.le hu.symm i
    have h2 := abs_latPt_roundLat_sub_lt hs v i
    push_cast at h1
    have h3 : |latPt s (2 • u) i - v i| ≤
        s * ((ℓ : ℝ) + 1)^2 + s := by
      have := abs_sub_le (latPt s (2 • u) i) (latPt s (roundLat s v) i) (v i)
      linarith
    have hsℓ : s = (2 : ℝ)⁻¹ ^ ℓ / 2 := by
      dsimp [s]
      rw [pow_succ]
      ring
    have hℓ' : (110:ℝ) ≤ ℓ := by exact_mod_cast hℓ
    have hε : (0:ℝ) < (2:ℝ)⁻¹ ^ ℓ := by positivity
    calc
      |latPt ((2:ℝ)⁻¹ ^ ℓ) u i - v i| = |latPt s (2 • u) i - v i| := by
        dsimp [s]
        rw [latPt_two_smul]
      _ ≤ s * ((ℓ:ℝ)+1)^2 + s := h3
      _ ≤ (ℓ:ℝ)^2 * (2:ℝ)⁻¹ ^ ℓ := by
        rw [hsℓ]
        have hpoly : ((ℓ:ℝ)+1)^2 + 1 ≤ 2*(ℓ:ℝ)^2 := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_right hpoly hε.le]
  · have hℓ1 : ℓ + 1 = n := by omega
    let s : ℝ := (2 : ℝ)⁻¹ ^ ℓ
    have hs : 0 < s := by dsimp [s]; positivity
    obtain ⟨u, hu, huO⟩ := holeLemma d hd _ _ hE (roundLat s v)
    refine ⟨u, huO, fun i => ?_, fun h' => absurd h' (by omega)⟩
    have h1 := abs_latPt_sub_le_of_withinInf hs.le hu i
    have h2 := abs_latPt_roundLat_sub_lt hs v i
    push_cast at h1
    have hD : (wnBadDiameter ℓ:ℝ) + 2 ≤ (ℓ:ℝ)^2 := by
      have h101 : 101^2 ≤ ℓ^2 := Nat.pow_le_pow_left (by omega) 2
      have hNat : wnBadDiameter ℓ + 2 ≤ ℓ^2 := by
        dsimp [wnBadDiameter]
        omega
      exact_mod_cast hNat
    have h3 := abs_sub_le (latPt s u i) (latPt s (roundLat s v) i) (v i)
    calc
      |latPt s u i - v i| ≤ s * ((wnBadDiameter ℓ:ℝ) + 2) := by linarith
      _ ≤ s * (ℓ:ℝ)^2 := mul_le_mul_of_nonneg_left hD hs.le
      _ = (ℓ:ℝ)^2 * (2:ℝ)⁻¹ ^ ℓ := by dsimp [s]; ring

/-- Straight-segment bound inside a convex local box. -/
theorem wnLocalChain_segment_box {φ : Rd d → ℝ} (hφ : Continuous φ)
    {ξ e ρ : ℝ} (w : Rd d) {x y : Rd d}
    (hx : x ∈ obox w ρ) (hy : y ∈ obox w ρ)
    (he : ∀ z ∈ obox w ρ, Real.exp (ξ * φ z) ≤ e)
    {n : ℕ} {L : ℝ}
    (hxy : ∀ i, |y i - x i| ≤ L * (2:ℝ)⁻¹ ^ n) :
    lfppDistOn ξ φ (obox w ρ) x y ≤
      Real.sqrt (d:ℝ) * L * (2:ℝ)⁻¹ ^ n * e := by
  have hseg := lfppDistOn_le_of_segment hφ
    (mapsTo_segPath (convex_obox w ρ) hx hy)
    (fun u hu => he _ (segPath_mem_of_convex (convex_obox w ρ) hx hy hu))
  have hnorm := norm_sub_le_of_forall_abs_le hxy
  have he0 : 0 ≤ e := by
    have := he x hx
    exact (Real.exp_pos _).le.trans this
  calc
    lfppDistOn ξ φ (obox w ρ) x y ≤ e * ‖y-x‖ := hseg
    _ ≤ e * (Real.sqrt d * (L * (2:ℝ)⁻¹ ^ n)) :=
      mul_le_mul_of_nonneg_left hnorm he0
    _ = Real.sqrt d * L * (2:ℝ)⁻¹ ^ n * e := by ring

private theorem wnContract_abs_le {ρ δ t : ℝ} (hρ : 0 < ρ)
    (hδρ : δ ≤ ρ) (ht : |t| < ρ) :
    |(1-δ/ρ)*t| ≤ ρ-δ := by
  have hc : 0 ≤ 1-δ/ρ := by
    rw [sub_nonneg, div_le_one hρ]
    exact hδρ
  rw [abs_mul, abs_of_nonneg hc]
  calc
    (1-δ/ρ)*|t| ≤ (1-δ/ρ)*ρ := mul_le_mul_of_nonneg_left ht.le hc
    _ = ρ-δ := by field_simp

private theorem wnContract_sub_le {ρ δ t : ℝ} (hρ : 0 < ρ)
    (hδ : 0 ≤ δ) (ht : |t| < ρ) :
    |t-(1-δ/ρ)*t| ≤ δ := by
  have he : t-(1-δ/ρ)*t = (δ/ρ)*t := by ring
  rw [he, abs_mul, abs_of_nonneg (div_nonneg hδ hρ.le)]
  calc
    δ/ρ*|t| ≤ δ/ρ*ρ := mul_le_mul_of_nonneg_left ht.le (div_nonneg hδ hρ.le)
    _ = δ := by field_simp

private theorem wnContract_two_le {ρ δ δ' t : ℝ} (hρ : 0 < ρ)
    (hδ'δ : δ' ≤ δ) (ht : |t| < ρ) :
    |(1-δ/ρ)*t-(1-δ'/ρ)*t| ≤ δ-δ' := by
  have he : (1-δ/ρ)*t-(1-δ'/ρ)*t = -((δ-δ')/ρ*t) := by ring
  rw [he, abs_neg, abs_mul, abs_of_nonneg (div_nonneg (by linarith) hρ.le)]
  calc
    (δ-δ')/ρ*|t| ≤ (δ-δ')/ρ*ρ :=
      mul_le_mul_of_nonneg_left ht.le (div_nonneg (by linarith) hρ.le)
    _ = δ-δ' := by field_simp

/-- Numerical form of a local free-site link at scale `k`. -/
theorem wnLocalChain_link_cost {φ : Rd d → ℝ} (hφ : Continuous φ)
    {ξ c ρ : ℝ} (w : Rd d) {O : Set (Zd d)} {k : ℕ}
    (hk : 110 ≤ k) (hc : 0 ≤ c)
    (hsmall : SmallClusters O (wnBadDiameter k))
    {u v : Zd d} (hu : FreeSite O u) (hv : FreeSite O v)
    (huv : ∀ i, |latPt ((2:ℝ)⁻¹ ^ k) u i - latPt ((2:ℝ)⁻¹ ^ k) v i| ≤
      1003*(k:ℝ)^2*(2:ℝ)⁻¹ ^ k)
    (hmu : ∀ i, |latPt ((2:ℝ)⁻¹ ^ k) u i - w i| ≤
      ρ - ((k:ℝ)^2+3)*(2:ℝ)⁻¹ ^ k)
    (hmv : ∀ i, |latPt ((2:ℝ)⁻¹ ^ k) v i - w i| ≤
      ρ - ((k:ℝ)^2+3)*(2:ℝ)⁻¹ ^ k)
    (hcost : ∀ z ∈ O, obox (latPt ((2:ℝ)⁻¹ ^ k) z) (2*(2:ℝ)⁻¹ ^ k) ⊆ obox w ρ →
      ∀ z', LAdj z z' →
        lfppDistOn ξ φ (obox (latPt ((2:ℝ)⁻¹ ^ k) z) (2*(2:ℝ)⁻¹ ^ k))
          (latPt ((2:ℝ)⁻¹ ^ k) z) (latPt ((2:ℝ)⁻¹ ^ k) z') ≤ c) :
    lfppDistOn ξ φ (obox w ρ)
      (latPt ((2:ℝ)⁻¹ ^ k) u) (latPt ((2:ℝ)⁻¹ ^ k) v) ≤
      (2011:ℝ)^d * (k:ℝ)^(2*d) * c := by
  let s : ℝ := (2:ℝ)⁻¹ ^ k
  have hs : 0 < s := by dsimp [s]; positivity
  let D : ℕ := wnBadDiameter k
  have hDk : D ≤ k^2 := Nat.sub_le _ _
  have hDkr : (D:ℝ) ≤ (k:ℝ)^2 := by exact_mod_cast hDk
  have hR : WithinInf ((1003*k^2:ℕ):ℤ) u v :=
    withinInf_of_abs_latPt_sub_le hs (fun i => by
      have := huv i
      dsimp [s]
      push_cast
      linarith)
  have hmu' : ∀ i, |latPt s u i - w i| + ((D+3:ℕ):ℝ)*s ≤ ρ := by
    intro i
    have h := hmu i
    have hsum : ((D+3:ℕ):ℝ) ≤ (k:ℝ)^2+3 := by push_cast; linarith [hDkr]
    have hprod := mul_le_mul_of_nonneg_right hsum hs.le
    dsimp [s] at *
    linarith
  have hmv' : ∀ i, |latPt s v i - w i| + ((D+3:ℕ):ℝ)*s ≤ ρ := by
    intro i
    have h := hmv i
    have hsum : ((D+3:ℕ):ℝ) ≤ (k:ℝ)^2+3 := by push_cast; linarith [hDkr]
    have hprod := mul_le_mul_of_nonneg_right hsum hs.le
    dsimp [s] at *
    linarith
  have hL := wnLocalChain_link hφ hs hc w hsmall hu hv hR hmu' hmv'
    (by simpa only [s] using hcost)
  have hk2 : 1 ≤ k^2 := Nat.one_le_pow _ _ (by omega)
  have hcnt : 2*(1003*k^2+D+1)+1 ≤ 2011*k^2 := by omega
  have hcnt' : (((2*(1003*k^2+D+1)+1:ℕ):ℝ))^d ≤
      (2011:ℝ)^d * (k:ℝ)^(2*d) := by
    have h1 : (((2*(1003*k^2+D+1)+1:ℕ):ℝ)) ≤ 2011*(k:ℝ)^2 := by
      exact_mod_cast hcnt
    calc
      (((2*(1003*k^2+D+1)+1:ℕ):ℝ))^d ≤ (2011*(k:ℝ)^2)^d :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) h1 d
      _ = (2011:ℝ)^d * (k:ℝ)^(2*d) := by rw [mul_pow, pow_mul]
  calc
    lfppDistOn ξ φ (obox w ρ) (latPt s u) (latPt s v) ≤
        (((2*(1003*k^2+D+1)+1:ℕ):ℝ))^d*c := hL
    _ ≤ ((2011:ℝ)^d * (k:ℝ)^(2*d))*c :=
      mul_le_mul_of_nonneg_right hcnt' hc
    _ = (2011:ℝ)^d * (k:ℝ)^(2*d)*c := by ring

/-- A selected point retains a large margin inside its contracted local box. -/
theorem wnLocalChain_point_margin {w x X : Rd d} {ρ : ℝ} {k : ℕ}
    (hρ : 0 < ρ) (hx : x ∈ obox w ρ) (hδ : chainDelta k ≤ ρ)
    (hX : ∀ i, |X i - (w i + (1-chainDelta k/ρ)*(x i-w i))| ≤
      (k:ℝ)^2*(2:ℝ)⁻¹ ^ k) :
    ∀ i, |X i-w i| ≤ ρ - 999*(k:ℝ)^2*(2:ℝ)⁻¹ ^ k := by
  intro i
  have hxi : |x i-w i| < ρ := hx i
  have hcontr := wnContract_abs_le hρ hδ hxi
  have htri := abs_sub_le (X i) (w i+(1-chainDelta k/ρ)*(x i-w i)) (w i)
  have hxi' := hX i
  have he : w i+(1-chainDelta k/ρ)*(x i-w i)-w i =
      (1-chainDelta k/ρ)*(x i-w i) := by ring
  rw [he] at htri
  dsimp [chainDelta] at hcontr htri hxi' ⊢
  linarith

private theorem wnChainDelta_le {j k : ℕ} (hj : 110 ≤ j) (hjk : j ≤ k) :
    chainDelta k ≤ chainDelta j := by
  induction k, hjk using Nat.le_induction with
  | base => exact le_rfl
  | succ k hle ih =>
    exact (chainDelta_succ_le (by omega : 3 ≤ k)).trans ih

/-- The terminal straight segment from a point to its finest lattice approximation. -/
theorem wnLocalChain_terminal {φ : Rd d → ℝ} (hφ : Continuous φ)
    {ξ e ρ : ℝ} (w x : Rd d) {n : ℕ} (hn : 111 ≤ n)
    (hρ : 0 < ρ) (hx : x ∈ obox w ρ)
    {u : Zd d} (hu : latPt ((2:ℝ)⁻¹ ^ (n-1)) u ∈ obox w ρ)
    (happrox : ∀ i,
      |latPt ((2:ℝ)⁻¹ ^ (n-1)) u i -
        (w i+(1-chainDelta (n-1)/ρ)*(x i-w i))| ≤
        ((n-1:ℕ):ℝ)^2*(2:ℝ)⁻¹ ^ (n-1))
    (he : ∀ z ∈ obox w ρ, Real.exp (ξ * φ z) ≤ e) :
    lfppDistOn ξ φ (obox w ρ) x (latPt ((2:ℝ)⁻¹ ^ (n-1)) u) ≤
      2002 * Real.sqrt (d:ℝ) * (n:ℝ)^2 * (2:ℝ)⁻¹ ^ n * e := by
  have hn1 : n-1+1=n := by omega
  have hcoord : ∀ i,
      |latPt ((2:ℝ)⁻¹ ^ (n-1)) u i - x i| ≤
        (2002*(n:ℝ)^2)*(2:ℝ)⁻¹ ^ n := by
    intro i
    have hxi : |x i-w i| < ρ := hx i
    have e1 := happrox i
    have e2 := wnContract_sub_le hρ (chainDelta_nonneg (n-1)) hxi
    have e2' : |(w i+(1-chainDelta (n-1)/ρ)*(x i-w i))-x i| ≤
        chainDelta (n-1) := by
      have heq : w i+(1-chainDelta (n-1)/ρ)*(x i-w i)-x i =
          -((x i-w i)-(1-chainDelta (n-1)/ρ)*(x i-w i)) := by ring
      simpa only [heq, abs_neg] using e2
    have e3 := abs_sub_le (latPt ((2:ℝ)⁻¹ ^ (n-1)) u i)
      (w i+(1-chainDelta (n-1)/ρ)*(x i-w i)) (x i)
    have hε : (2:ℝ)⁻¹ ^ (n-1) = 2*(2:ℝ)⁻¹ ^ n := by
      have hpow : (2:ℝ)⁻¹ ^ n = (2:ℝ)⁻¹ ^ (n-1) * 2⁻¹ := by
        rw [← pow_succ, hn1]
      rw [hpow]
      ring
    have hsq : ((n-1:ℕ):ℝ)^2 ≤ (n:ℝ)^2 := by
      gcongr
      exact_mod_cast Nat.sub_le n 1
    have hbd : ((n-1:ℕ):ℝ)^2*(2:ℝ)⁻¹ ^ (n-1) + chainDelta (n-1) ≤
        (2002*(n:ℝ)^2)*(2:ℝ)⁻¹ ^ n := by
      unfold chainDelta
      rw [hε]
      calc
        ((n-1:ℕ):ℝ)^2*(2*(2:ℝ)⁻¹ ^ n) +
          1000*((n-1:ℕ):ℝ)^2*(2*(2:ℝ)⁻¹ ^ n) =
            2002*((n-1:ℕ):ℝ)^2*(2:ℝ)⁻¹ ^ n := by ring
        _ ≤ 2002*(n:ℝ)^2*(2:ℝ)⁻¹ ^ n := by gcongr
    linarith
  have h := wnLocalChain_segment_box hφ w hx hu he hcoord
  calc
    lfppDistOn ξ φ (obox w ρ) x (latPt ((2:ℝ)⁻¹ ^ (n-1)) u) ≤
      Real.sqrt d*(2002*(n:ℝ)^2)*(2:ℝ)⁻¹ ^ n*e := h
    _ = 2002*Real.sqrt d*(n:ℝ)^2*(2:ℝ)⁻¹ ^ n*e := by ring

/-- The link between selected points at consecutive scales. -/
theorem wnLocalChain_consecutive {φ : Rd d → ℝ} (hφ : Continuous φ)
    {ξ c ρ : ℝ} (w x : Rd d) {O : ℕ → Set (Zd d)} {ℓ : ℕ}
    (hℓ : 110 ≤ ℓ) (hρ : 0 < ρ) (hx : x ∈ obox w ρ)
    (hδℓ : chainDelta ℓ ≤ ρ) (hδk : chainDelta (ℓ+1) ≤ ρ)
    (hc : 0 ≤ c) (hsmall : SmallClusters (O (ℓ+1)) (wnBadDiameter (ℓ+1)))
    {u v : Zd d}
    (hu : FreeSite (O (ℓ+1)) (2 • u)) (hv : FreeSite (O (ℓ+1)) v)
    (hu2 : ∀ i, |latPt ((2:ℝ)⁻¹ ^ ℓ) u i -
      (w i+(1-chainDelta ℓ/ρ)*(x i-w i))| ≤
      (ℓ:ℝ)^2*(2:ℝ)⁻¹ ^ ℓ)
    (hv2 : ∀ i, |latPt ((2:ℝ)⁻¹ ^ (ℓ+1)) v i -
      (w i+(1-chainDelta (ℓ+1)/ρ)*(x i-w i))| ≤
      ((ℓ+1:ℕ):ℝ)^2*(2:ℝ)⁻¹ ^ (ℓ+1))
    (hcost : ∀ z ∈ O (ℓ+1),
      obox (latPt ((2:ℝ)⁻¹ ^ (ℓ+1)) z) (2*(2:ℝ)⁻¹ ^ (ℓ+1)) ⊆ obox w ρ →
      ∀ z', LAdj z z' →
        lfppDistOn ξ φ (obox (latPt ((2:ℝ)⁻¹ ^ (ℓ+1)) z) (2*(2:ℝ)⁻¹ ^ (ℓ+1)))
          (latPt ((2:ℝ)⁻¹ ^ (ℓ+1)) z) (latPt ((2:ℝ)⁻¹ ^ (ℓ+1)) z') ≤ c) :
    lfppDistOn ξ φ (obox w ρ)
      (latPt ((2:ℝ)⁻¹ ^ ℓ) u) (latPt ((2:ℝ)⁻¹ ^ (ℓ+1)) v) ≤
      (2011:ℝ)^d * ((ℓ+1:ℕ):ℝ)^(2*d) * c := by
  let s : ℝ := (2:ℝ)⁻¹ ^ (ℓ+1)
  have hs : 0 < s := by dsimp [s]; positivity
  have hsℓ : (2:ℝ)⁻¹ ^ ℓ = 2*s := by
    dsimp [s]
    rw [pow_succ]
    ring
  have hlat : latPt s (2 • u) = latPt ((2:ℝ)⁻¹ ^ ℓ) u := by
    dsimp [s]
    exact latPt_two_smul ℓ u
  have hℓr : (110:ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hkcast : ((ℓ+1:ℕ):ℝ) = (ℓ:ℝ)+1 := by push_cast; ring
  have huv : ∀ i, |latPt s v i - latPt s (2 • u) i| ≤
      1003*((ℓ+1:ℕ):ℝ)^2*s := by
    intro i
    rw [hlat]
    have e1 := hv2 i
    have e2 := hu2 i
    have e3 := wnContract_two_le hρ (chainDelta_succ_le (by omega : 3 ≤ ℓ))
      (show |x i-w i| < ρ from hx i)
    have e4 := chainDelta_sub_succ_le ℓ
    have hcon : |(w i+(1-chainDelta (ℓ+1)/ρ)*(x i-w i)) -
        (w i+(1-chainDelta ℓ/ρ)*(x i-w i))| ≤
        1000*((ℓ+1:ℕ):ℝ)^2*s := by
      have heq : (w i+(1-chainDelta (ℓ+1)/ρ)*(x i-w i)) -
          (w i+(1-chainDelta ℓ/ρ)*(x i-w i)) =
          -((1-chainDelta ℓ/ρ)*(x i-w i) -
            (1-chainDelta (ℓ+1)/ρ)*(x i-w i)) := by ring
      rw [heq, abs_neg]
      exact e3.trans (by simpa only [s, Nat.cast_add, Nat.cast_one] using e4)
    have e5 := abs_sub_le (latPt s v i)
      (w i+(1-chainDelta (ℓ+1)/ρ)*(x i-w i))
      (latPt ((2:ℝ)⁻¹ ^ ℓ) u i)
    have e6 := abs_sub_le (w i+(1-chainDelta (ℓ+1)/ρ)*(x i-w i))
      (w i+(1-chainDelta ℓ/ρ)*(x i-w i))
      (latPt ((2:ℝ)⁻¹ ^ ℓ) u i)
    have hpoly : (ℓ:ℝ)^2 ≤ ((ℓ+1:ℕ):ℝ)^2 := by
      rw [hkcast]
      nlinarith
    have hpoly' := mul_le_mul_of_nonneg_right hpoly hs.le
    have e2' : |(w i+(1-chainDelta ℓ/ρ)*(x i-w i)) -
        latPt ((2:ℝ)⁻¹ ^ ℓ) u i| ≤ 2*(ℓ:ℝ)^2*s := by
      rw [abs_sub_comm]
      calc
        |latPt ((2:ℝ)⁻¹ ^ ℓ) u i -
            (w i+(1-chainDelta ℓ/ρ)*(x i-w i))| ≤
            (ℓ:ℝ)^2*(2:ℝ)⁻¹ ^ ℓ := e2
        _ = 2*(ℓ:ℝ)^2*s := by rw [hsℓ]; ring
    dsimp [s] at e1 e2' hcon hpoly' e5 e6 ⊢
    linarith
  have hmargu := wnLocalChain_point_margin hρ hx hδℓ hu2
  have hmargv := wnLocalChain_point_margin hρ hx hδk hv2
  have hmu : ∀ i, |latPt s (2 • u) i-w i| ≤
      ρ-(((ℓ+1:ℕ):ℝ)^2+3)*s := by
    intro i
    rw [hlat]
    have h : |latPt ((2:ℝ)⁻¹ ^ ℓ) u i-w i| ≤ ρ-1998*(ℓ:ℝ)^2*s := by
      calc
        _ ≤ ρ-999*(ℓ:ℝ)^2*(2:ℝ)⁻¹ ^ ℓ := hmargu i
        _ = _ := by rw [hsℓ]; ring
    rw [hkcast]
    have hpoly : ((ℓ:ℝ)+1)^2+3 ≤ 1998*(ℓ:ℝ)^2 := by nlinarith
    have hprod := mul_le_mul_of_nonneg_right hpoly hs.le
    linarith
  have hmv : ∀ i, |latPt s v i-w i| ≤
      ρ-(((ℓ+1:ℕ):ℝ)^2+3)*s := by
    intro i
    have h := hmargv i
    dsimp [s]
    have hpoly : 3 ≤ 998*((ℓ+1:ℕ):ℝ)^2 := by
      have : (1:ℝ) ≤ ((ℓ+1:ℕ):ℝ) := by exact_mod_cast (by omega : 1 ≤ ℓ+1)
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hpoly (show 0 ≤ (2:ℝ)⁻¹ ^ (ℓ+1) by positivity)]
  have hL := wnLocalChain_link_cost hφ w (by omega : 110 ≤ ℓ+1) hc
    hsmall hv hu huv hmv hmu hcost
  rw [hlat, lfppDistOn_comm] at hL
  exact hL

/-- One half of the localized multiscale chain, for selected lattice points. -/
theorem wnLocalChain_half {φ : Rd d → ℝ} (hφ : Continuous φ)
    {ξ e ρ : ℝ} (w x : Rd d) {O : ℕ → Set (Zd d)} {c : ℕ → ℝ}
    {j n : ℕ} (hj : 110 ≤ j) (hjn : j < n) (hρ : 0 < ρ)
    (hx : x ∈ obox w ρ) (hδj : chainDelta j ≤ ρ/100)
    (hE : ∀ k, j ≤ k → k < n → SmallClusters (O k) (wnBadDiameter k))
    (hc : ∀ k, j ≤ k → k < n → 0 ≤ c k)
    (hcost : ∀ k, j ≤ k → k < n → ∀ z ∈ O k,
      obox (latPt ((2:ℝ)⁻¹ ^ k) z) (2*(2:ℝ)⁻¹ ^ k) ⊆ obox w ρ →
      ∀ z', LAdj z z' →
        lfppDistOn ξ φ (obox (latPt ((2:ℝ)⁻¹ ^ k) z) (2*(2:ℝ)⁻¹ ^ k))
          (latPt ((2:ℝ)⁻¹ ^ k) z) (latPt ((2:ℝ)⁻¹ ^ k) z') ≤ c k)
    (he : ∀ z ∈ obox w ρ, Real.exp (ξ * φ z) ≤ e)
    {U : ℕ → Zd d}
    (hU1 : ∀ ℓ, j ≤ ℓ → ℓ < n → FreeSite (O ℓ) (U ℓ))
    (hU2 : ∀ ℓ, j ≤ ℓ → ℓ < n → ∀ i,
      |latPt ((2:ℝ)⁻¹ ^ ℓ) (U ℓ) i -
        (w i+(1-chainDelta ℓ/ρ)*(x i-w i))| ≤
        (ℓ:ℝ)^2*(2:ℝ)⁻¹ ^ ℓ)
    (hU3 : ∀ ℓ, j ≤ ℓ → ℓ+1 < n → FreeSite (O (ℓ+1)) (2 • U ℓ)) :
    lfppDistOn ξ φ (obox w ρ) x (latPt ((2:ℝ)⁻¹ ^ j) (U j)) ≤
      2002*Real.sqrt (d:ℝ)*(n:ℝ)^2*(2:ℝ)⁻¹ ^ n*e +
      (2011:ℝ)^d * ∑ k ∈ Finset.Ico (j+1) n, (k:ℝ)^(2*d)*c k := by
  let X : ℕ → Rd d := fun ℓ => latPt ((2:ℝ)⁻¹ ^ ℓ) (U ℓ)
  let f : ℕ → ℝ := fun k => (k:ℝ)^(2*d)*c k
  have hδall : ∀ ℓ, j ≤ ℓ → chainDelta ℓ ≤ ρ := by
    intro ℓ h1
    have := (wnChainDelta_le hj h1).trans hδj
    linarith
  have hXV : ∀ ℓ, j ≤ ℓ → ℓ < n → X ℓ ∈ obox w ρ := by
    intro ℓ h1 h2 i
    have hmar := wnLocalChain_point_margin hρ hx (hδall ℓ h1)
      (hU2 ℓ h1 h2)
    have hpos : 0 < 999*(ℓ:ℝ)^2*(2:ℝ)⁻¹ ^ ℓ := by
      have : (1:ℝ) ≤ ℓ := by exact_mod_cast (by omega : 1 ≤ ℓ)
      positivity
    have h := hmar i
    change |latPt ((2:ℝ)⁻¹ ^ ℓ) (U ℓ) i-w i| < ρ
    linarith
  have hjN : j ≤ n-1 := by omega
  have hseg : lfppDistOn ξ φ (obox w ρ) x (X (n-1)) ≤
      2002*Real.sqrt (d:ℝ)*(n:ℝ)^2*(2:ℝ)⁻¹ ^ n*e :=
    wnLocalChain_terminal hφ w x (by omega : 111 ≤ n) hρ hx
      (hXV (n-1) hjN (by omega)) (hU2 (n-1) hjN (by omega)) he
  have hlink : ∀ ℓ, j ≤ ℓ → ℓ+1 < n →
      lfppDistOn ξ φ (obox w ρ) (X ℓ) (X (ℓ+1)) ≤ (2011:ℝ)^d*f (ℓ+1) := by
    intro ℓ h1 h2
    simpa only [X, f, mul_assoc] using wnLocalChain_consecutive hφ w x
      (by omega : 110 ≤ ℓ) hρ hx
      (hδall ℓ h1) (hδall (ℓ+1) (by omega)) (hc (ℓ+1) (by omega) h2)
      (hE (ℓ+1) (by omega) h2) (hU3 ℓ h1 h2) (hU1 (ℓ+1) (by omega) h2)
      (hU2 ℓ h1 (by omega)) (hU2 (ℓ+1) (by omega) h2)
      (hcost (ℓ+1) (by omega) h2)
  have hchain : lfppDistOn ξ φ (obox w ρ) (X j) (X (n-1)) ≤
      (2011:ℝ)^d * ∑ k ∈ Finset.Ico (j+1) n, f k := by
    have hsum := lfppDistOn_le_sum (ζ := ξ) hφ (fun i => X (j+i))
      (fun _ => obox w ρ) (fun _ => subset_rfl) (n-1-j) (fun i hi =>
        PcwJoined.of_convex (convex_obox w ρ)
          (hXV (j+i) (by omega) (by omega))
          (hXV (j+(i+1)) (by omega) (by omega)))
    have eN : j+(n-1-j)=n-1 := by omega
    simp only [Nat.add_zero, eN] at hsum
    rw [Finset.mul_sum, Finset.sum_Ico_eq_sum_range,
      show n-(j+1)=n-1-j by omega]
    refine hsum.trans (Finset.sum_le_sum fun i hi => ?_)
    rw [Finset.mem_range] at hi
    have h := hlink (j+i) (by omega) (by omega)
    rw [show j+(i+1)=j+i+1 by omega, show j+1+i=j+i+1 by omega]
    exact h
  calc
    lfppDistOn ξ φ (obox w ρ) x (X j) ≤
        lfppDistOn ξ φ (obox w ρ) x (X (n-1)) +
          lfppDistOn ξ φ (obox w ρ) (X (n-1)) (X j) :=
            lfppDistOn_triangle hφ
              (PcwJoined.of_convex (convex_obox w ρ) hx (hXV (n-1) hjN (by omega)))
              (PcwJoined.of_convex (convex_obox w ρ) (hXV (n-1) hjN (by omega))
                (hXV j le_rfl hjn))
    _ ≤ _ := by
      rw [lfppDistOn_comm ξ φ (obox w ρ) (X (n-1)) (X j)]
      exact add_le_add hseg hchain

end HigherDimLQGContinuity
