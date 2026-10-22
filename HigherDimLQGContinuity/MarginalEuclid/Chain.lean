import HigherDimLQGContinuity.MarginalEuclid.Holder
import QuantumZipper.Proofs.GFF.CoordRegKolm
import QuantumZipper.Proofs.LQG.RegularSampleKolmogorov

/-! Deterministic dyadic chaining for a continuous metric on `ℝ^d`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd)
open QuantumZipper.KolmD (boxD InRangeD lptD rndD norm_rndD_sub_le)
open QuantumZipper.KolmG (GoodG level_mod_G)

private theorem n5_tendsto_rndD {d : ℕ} (q : Fin d → ℝ) :
    Tendsto (fun n => rndD n q) atTop (𝓝 q) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun n => norm_rndD_sub_le n q) ?_
  simp_rw [one_div]
  exact tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))

private theorem n5_continuous_metric_left {d : ℕ} (D : ContMetric d) (z : Rd d) :
    Continuous fun q : Fin d → ℝ => D.1 (WithLp.toLp 2 q, z) := by
  exact D.continuous_apply.comp
    ((PiLp.continuous_toLp 2 _).prodMk continuous_const)

private theorem n5_metric_reverse_triangle {d : ℕ} (D : ContMetric d)
    (x y z : Rd d) : |D.1 (x, z) - D.1 (y, z)| ≤ D.1 (x, y) := by
  have h1 := D.apply_triangle x y z
  have h2 := D.apply_triangle y x z
  rw [D.apply_comm y x] at h2
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- A simultaneous bound on all dyadic coordinate edges gives a metric modulus. -/
theorem n5_metric_mod_of_good {d R n : ℕ} {θ : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (D : ContMetric d)
    (hgood : ∀ j : ℕ, ∀ a : Fin d → ℤ, InRangeD R j a → ∀ i : Fin d,
      D.1 (WithLp.toLp 2 (lptD j (a + Pi.single i 1)),
        WithLp.toLp 2 (lptD j a)) ≤ θ ^ j)
    {q q' : Fin d → ℝ} (hq : q ∈ boxD R) (hq' : q' ∈ boxD R)
    (hnear : ∀ i, |q i - q' i| < 1 / 2 ^ n) :
    D.1 (WithLp.toLp 2 q, WithLp.toLp 2 q') ≤
      (2 * (d / (1 - θ)) + d) * θ ^ n := by
  let z : Rd d := WithLp.toLp 2 q'
  let f : (Fin d → ℝ) → ℝ := fun v => D.1 (WithLp.toLp 2 v, z)
  have hf : Continuous f := n5_continuous_metric_left D z
  have hg : ∀ j : ℕ, GoodG θ f R j := by
    intro j a ha i
    exact (n5_metric_reverse_triangle D _ _ z).trans (hgood j a ha i)
  have hbound (M : ℕ) (hM : n ≤ M) :
      |f (rndD M q) - f (rndD M q')| ≤
        (2 * (d / (1 - θ)) + d) * θ ^ n :=
    level_mod_G hθ0 hθ1 hq hq' (fun j _ => hg j) (Nat.zero_le n) hnear hM
  have hlim : Tendsto (fun M => |f (rndD M q) - f (rndD M q')|)
      atTop (𝓝 |f q - f q'|) :=
    (((hf.tendsto q).comp (n5_tendsto_rndD q)).sub
      ((hf.tendsto q').comp (n5_tendsto_rndD q'))).abs
  have hh : |f q - f q'| ≤ (2 * (d / (1 - θ)) + d) * θ ^ n :=
    le_of_tendsto hlim (eventually_atTop.2 ⟨n, hbound⟩)
  dsimp [f, z] at hh ⊢
  rw [D.apply_self, sub_zero, abs_of_nonneg (D.nonneg _ _)] at hh
  exact hh

/-- Scaled form of the dyadic metric modulus. -/
theorem n5_metric_mod_of_edge_bound {d R n : ℕ} {θ M : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hM : 0 < M) (D : ContMetric d)
    (hgood : ∀ j : ℕ, ∀ a : Fin d → ℤ, InRangeD R j a → ∀ i : Fin d,
      D.1 (WithLp.toLp 2 (lptD j (a + Pi.single i 1)),
        WithLp.toLp 2 (lptD j a)) ≤ M * θ ^ j)
    {q q' : Fin d → ℝ} (hq : q ∈ boxD R) (hq' : q' ∈ boxD R)
    (hnear : ∀ i, |q i - q' i| < 1 / 2 ^ n) :
    D.1 (WithLp.toLp 2 q, WithLp.toLp 2 q') ≤
      M * ((2 * (d / (1 - θ)) + d) * θ ^ n) := by
  let E : ContMetric d := D.smul M⁻¹ (inv_pos.mpr hM)
  have hgoodE : ∀ j : ℕ, ∀ a : Fin d → ℤ, InRangeD R j a → ∀ i : Fin d,
      E.1 (WithLp.toLp 2 (lptD j (a + Pi.single i 1)),
        WithLp.toLp 2 (lptD j a)) ≤ θ ^ j := by
    intro j a ha i
    simp only [E, ContMetric.smul_apply]
    have hh := hgood j a ha i
    have hi := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr hM.le)
    rw [← mul_assoc, inv_mul_cancel₀ hM.ne', one_mul] at hi
    exact hi
  have hh := n5_metric_mod_of_good hθ0 hθ1 E hgoodE hq hq' hnear
  simp only [E, ContMetric.smul_apply] at hh
  have hmul := mul_le_mul_of_nonneg_left hh hM.le
  rw [← mul_assoc, mul_inv_cancel₀ hM.ne', one_mul] at hmul
  exact hmul

/-- The dyadic modulus controls the metric on the entire coordinate box. -/
theorem n5_metric_global_box {d R : ℕ} {θ M : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hM : 0 < M) (D : ContMetric d)
    (hgood : ∀ j : ℕ, ∀ a : Fin d → ℤ, InRangeD R j a → ∀ i : Fin d,
      D.1 (WithLp.toLp 2 (lptD j (a + Pi.single i 1)),
        WithLp.toLp 2 (lptD j a)) ≤ M * θ ^ j)
    {q q' : Fin d → ℝ} (hq : q ∈ boxD R) (hq' : q' ∈ boxD R) :
    D.1 (WithLp.toLp 2 q, WithLp.toLp 2 q') ≤
      ((2 * R + 2 : ℕ) : ℝ) * (M * (2 * (d / (1 - θ)) + d)) := by
  let N : ℕ := 2 * R + 2
  have hN : 0 < (N : ℝ) := by dsimp [N]; positivity
  have hRN : (2 : ℝ) * R < N := by dsimp [N]; push_cast; linarith
  let z : ℕ → Fin d → ℝ := fun k i => q i + (k : ℝ) / N * (q' i - q i)
  have hz0 : z 0 = q := by funext i; simp [z]
  have hzN : z N = q' := by funext i; simp [z, hN.ne']
  have hzbox (k : ℕ) (hk : k ≤ N) : z k ∈ boxD R := by
    intro i
    have hk0 : 0 ≤ (k : ℝ) / N := by positivity
    have hk1 : (k : ℝ) / N ≤ 1 := (div_le_one hN).2 (by exact_mod_cast hk)
    have hqi := hq i
    have hq'i := hq' i
    rw [abs_le] at hqi hq'i ⊢
    dsimp [z]
    constructor <;> nlinarith
  have hznear (k : ℕ) (hk : k < N) (i : Fin d) :
      |z (k + 1) i - z k i| < 1 / 2 ^ (0 : ℕ) := by
    have hqi := hq i
    have hq'i := hq' i
    rw [abs_le] at hqi hq'i
    have h2 : |q' i - q i| ≤ (2 : ℝ) * R := by rw [abs_le]; constructor <;> linarith
    have he : z (k + 1) i - z k i = (q' i - q i) / N := by
      dsimp [z]; push_cast; ring
    rw [he, abs_div, abs_of_pos hN]
    have hlt : |q' i - q i| / (N : ℝ) < 1 := by
      rw [div_lt_iff₀ hN]
      nlinarith
    simpa using hlt
  have hstep (k : ℕ) (hk : k < N) :
      D.1 (WithLp.toLp 2 (z k), WithLp.toLp 2 (z (k + 1))) ≤
        M * (2 * (d / (1 - θ)) + d) := by
    have hh := n5_metric_mod_of_edge_bound hθ0 hθ1 hM D hgood
      (hzbox k (Nat.le_of_lt hk)) (hzbox (k+1) hk) (by
        intro i
        simpa only [abs_sub_comm] using hznear k hk i)
    simpa using hh
  have hind (k : ℕ) (hk : k ≤ N) :
      D.1 (WithLp.toLp 2 (z 0), WithLp.toLp 2 (z k)) ≤
        (k : ℝ) * (M * (2 * (d / (1 - θ)) + d)) := by
    induction k with
    | zero => simp [D.apply_self]
    | succ k ih =>
      have hk' : k < N := by omega
      calc
        D.1 (WithLp.toLp 2 (z 0), WithLp.toLp 2 (z (k+1)))
            ≤ D.1 (WithLp.toLp 2 (z 0), WithLp.toLp 2 (z k)) +
              D.1 (WithLp.toLp 2 (z k), WithLp.toLp 2 (z (k+1))) :=
                D.apply_triangle _ _ _
        _ ≤ (k : ℝ) * (M * (2 * (d / (1 - θ)) + d)) +
              M * (2 * (d / (1 - θ)) + d) := add_le_add (ih (by omega)) (hstep k hk')
        _ = ((k+1 : ℕ) : ℝ) * (M * (2 * (d / (1 - θ)) + d)) := by push_cast; ring
  simpa [hz0, hzN, N] using hind N le_rfl

/-- A uniform dyadic edge envelope bounds the Hölder quotient on a ball. -/
theorem n5_metric_holder_of_edge_bound {d R : ℕ} {β M : ℝ}
    (hβ : 0 < β) (_hβ1 : β < 1) (hM : 0 < M) (D : ContMetric d)
    (hgood : ∀ j : ℕ, ∀ a : Fin d → ℤ, InRangeD R j a → ∀ i : Fin d,
      D.1 (WithLp.toLp 2 (lptD j (a + Pi.single i 1)),
        WithLp.toLp 2 (lptD j a)) ≤ M * ((1 / 2 : ℝ) ^ β) ^ j)
    {x y : Rd d} (hx : x ∈ Metric.closedBall 0 (R : ℝ))
    (hy : y ∈ Metric.closedBall 0 (R : ℝ)) :
    D.1 (x, y) ≤ M * ((2 * (d / (1 - (1 / 2 : ℝ) ^ β)) + d) *
      (4 ^ β + (2 * R + 2 : ℝ) / ((1 / 2 : ℝ) ^ β))) * dist x y ^ β := by
  let θ : ℝ := (1 / 2 : ℝ) ^ β
  let c : ℝ := 2 * (d / (1 - θ)) + d
  let N : ℝ := 2 * R + 2
  have hθ0 : 0 < θ := Real.rpow_pos_of_pos (by norm_num) _
  have hθ1 : θ < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hβ
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hq : WithLp.ofLp x ∈ boxD R := by
    intro i
    have hi := PiLp.norm_apply_le x i
    have hn : ‖x‖ ≤ (R : ℝ) := by simpa using hx
    simpa only [Real.norm_eq_abs] using hi.trans hn
  have hq' : WithLp.ofLp y ∈ boxD R := by
    intro i
    have hi := PiLp.norm_apply_le y i
    have hn : ‖y‖ ≤ (R : ℝ) := by simpa using hy
    simpa only [Real.norm_eq_abs] using hi.trans hn
  have hdist : 0 ≤ dist x y := dist_nonneg
  by_cases hsmall : dist x y < 1 / 2
  · by_cases hzero : x = y
    · subst y
      rw [D.apply_self, dist_self, Real.zero_rpow hβ.ne']
      positivity
    have hpos : 0 < dist x y := dist_pos.mpr hzero
    obtain ⟨n, hnlo, hnhi⟩ :=
      exists_nat_pow_near_of_lt_one (show 0 < 2 * dist x y by positivity)
        (by linarith) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
    have hnear : ∀ i : Fin d,
        |(WithLp.ofLp x) i - (WithLp.ofLp y) i| < 1 / 2 ^ n := by
      intro i
      have hi := PiLp.norm_apply_le (x - y) i
      have hi' : |(WithLp.ofLp x) i - (WithLp.ofLp y) i| ≤ dist x y := by
        simpa only [Real.norm_eq_abs, PiLp.sub_apply, dist_eq_norm] using hi
      have hpow : (0 : ℝ) ≤ (1 / 2) ^ n := pow_nonneg (by norm_num) _
      have hstrict : dist x y < (1 / 2 : ℝ) ^ n := by linarith
      simpa [one_div, inv_pow] using lt_of_le_of_lt hi' hstrict
    have hθpow : θ ^ n ≤ 4 ^ β * dist x y ^ β := by
      have hbase : (1 / 2 : ℝ) ^ n ≤ 4 * dist x y := by
        have he : (1 / 2 : ℝ) ^ (n + 1) = (1 / 2) ^ n / 2 := by rw [pow_succ]; ring
        rw [he] at hnlo
        linarith
      have hpow := Real.rpow_le_rpow (pow_nonneg (by norm_num) n) hbase hβ.le
      have he : θ ^ n = ((1 / 2 : ℝ) ^ n) ^ β := by
        dsimp [θ]
        rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 1 / 2) β n,
          mul_comm β, Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      calc θ ^ n = ((1 / 2 : ℝ) ^ n) ^ β := he
        _ ≤ (4 * dist x y) ^ β := hpow
        _ = 4 ^ β * dist x y ^ β := Real.mul_rpow (by norm_num) hdist
    have hh := n5_metric_mod_of_edge_bound hθ0 hθ1 hM D hgood hq hq' hnear
    change D.1 (x, y) ≤ M * (c * θ ^ n) at hh
    calc
      D.1 (x, y) ≤ M * (c * θ ^ n) := hh
      _ ≤ M * (c * (4 ^ β * dist x y ^ β)) := by gcongr
      _ ≤ M * (c * ((4 ^ β + N / θ) * dist x y ^ β)) := by
        gcongr
        have : 0 ≤ N / θ := by positivity
        linarith
      _ = M * ((2 * (d / (1 - (1 / 2 : ℝ) ^ β)) + d) *
          (4 ^ β + (2 * R + 2 : ℝ) / ((1 / 2 : ℝ) ^ β))) * dist x y ^ β := by
            dsimp [c, N, θ]; ring
  · have hbig : 1 / 2 ≤ dist x y := le_of_not_gt hsmall
    have hθdist : θ ≤ dist x y ^ β :=
      Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1 / 2) hbig hβ.le
    have hh := n5_metric_global_box hθ0 hθ1 hM D hgood hq hq'
    have hh' : D.1 (x, y) ≤ N * (M * c) := by simpa [N, c] using hh
    have hbound : N ≤ N / θ * dist x y ^ β := by
      have hθne : θ ≠ 0 := hθ0.ne'
      calc N = (N / θ) * θ := by field_simp
        _ ≤ (N / θ) * dist x y ^ β := mul_le_mul_of_nonneg_left hθdist (by positivity)
    calc
      D.1 (x, y) ≤ N * (M * c) := hh'
      _ ≤ M * (c * (N / θ * dist x y ^ β)) := by
        simpa only [mul_assoc, mul_left_comm, mul_comm] using
          mul_le_mul_of_nonneg_right hbound (mul_nonneg hM.le hc)
      _ ≤ M * (c * ((4 ^ β + N / θ) * dist x y ^ β)) := by
        gcongr
        have : 0 ≤ (4 : ℝ) ^ β := Real.rpow_nonneg (by norm_num) _
        linarith
      _ = M * ((2 * (d / (1 - (1 / 2 : ℝ) ^ β)) + d) *
          (4 ^ β + (2 * R + 2 : ℝ) / ((1 / 2 : ℝ) ^ β))) * dist x y ^ β := by
            dsimp [c, N, θ]; ring

/-- Supremum of the normalized dyadic coordinate edges in the box. -/
def metricEdgeAmp {d : ℕ} (D : ContMetric d) (R : ℕ) (β : ℝ) : ℝ≥0∞ :=
  ⨆ j : ℕ, ⨆ a : Fin d → ℤ, ⨆ (_ : InRangeD R j a), ⨆ i : Fin d,
    ENNReal.ofReal (D.1 (WithLp.toLp 2 (lptD j (a + Pi.single i 1)),
      WithLp.toLp 2 (lptD j a)) / (((1 / 2 : ℝ) ^ β) ^ j))

/-- The normalized coordinate-edge envelope controls the full Hölder functional. -/
theorem holderConstRd_le_chain {d R : ℕ} {β : ℝ}
    (hd : 0 < d) (hβ : 0 < β) (hβ1 : β < 1) (D : ContMetric d) :
    holderConstRd D.1 (Metric.closedBall 0 (R : ℝ)) β ≤
      ENNReal.ofReal ((2 * (d / (1 - (1 / 2 : ℝ) ^ β)) + d) *
        (4 ^ β + (2 * R + 2 : ℝ) / ((1 / 2 : ℝ) ^ β))) *
        (1 + metricEdgeAmp D R β) := by
  let A := metricEdgeAmp D R β
  by_cases hA : A = ⊤
  · have hθ : (1 / 2 : ℝ) ^ β < 1 :=
      Real.rpow_lt_one (by norm_num) (by norm_num) hβ
    have hCpos : 0 < (2 * (d / (1 - (1 / 2 : ℝ) ^ β)) + d) *
        (4 ^ β + (2 * R + 2 : ℝ) / ((1 / 2 : ℝ) ^ β)) := by
      have : (0 : ℝ) < d := by exact_mod_cast hd
      positivity
    rw [show metricEdgeAmp D R β = ⊤ from hA]
    simp only [add_top]
    rw [ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr hCpos)]
    exact le_top
  let M := 1 + A.toReal
  have hM : 0 < M := by dsimp [M]; positivity
  have hθ : 0 < (1 / 2 : ℝ) ^ β := Real.rpow_pos_of_pos (by norm_num) _
  have hgood : ∀ j : ℕ, ∀ a : Fin d → ℤ, InRangeD R j a → ∀ i : Fin d,
      D.1 (WithLp.toLp 2 (lptD j (a + Pi.single i 1)),
        WithLp.toLp 2 (lptD j a)) ≤ M * ((1 / 2 : ℝ) ^ β) ^ j := by
    intro j a ha i
    let e := D.1 (WithLp.toLp 2 (lptD j (a + Pi.single i 1)),
      WithLp.toLp 2 (lptD j a))
    have he : 0 ≤ e := D.nonneg _ _
    have hp : 0 < ((1 / 2 : ℝ) ^ β) ^ j := pow_pos hθ _
    have hle : ENNReal.ofReal (e / (((1 / 2 : ℝ) ^ β) ^ j)) ≤ A := by
      exact le_iSup_of_le j (le_iSup_of_le a (le_iSup_of_le ha
        (le_iSup_of_le i le_rfl)))
    have hr : e / (((1 / 2 : ℝ) ^ β) ^ j) ≤ A.toReal :=
      (ENNReal.ofReal_le_iff_le_toReal hA).mp hle
    have h0 : 0 ≤ A.toReal := ENNReal.toReal_nonneg
    rw [div_le_iff₀ hp] at hr
    calc e ≤ A.toReal * (((1 / 2 : ℝ) ^ β) ^ j) := hr
      _ ≤ M * (((1 / 2 : ℝ) ^ β) ^ j) := by
        apply mul_le_mul_of_nonneg_right _ hp.le
        dsimp [M]
        linarith
  have hC : 0 ≤ (2 * (d / (1 - (1 / 2 : ℝ) ^ β)) + d) *
        (4 ^ β + (2 * R + 2 : ℝ) / ((1 / 2 : ℝ) ^ β)) := by
    have hh : (1 / 2 : ℝ) ^ β < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hβ
    positivity
  have hpoint : ∀ x ∈ Metric.closedBall (0 : Rd d) (R : ℝ),
      ∀ y ∈ Metric.closedBall (0 : Rd d) (R : ℝ), x ≠ y →
      ENNReal.ofReal (D.1 (x, y) / ‖x - y‖ ^ β) ≤
        ENNReal.ofReal ((2 * (d / (1 - (1 / 2 : ℝ) ^ β)) + d) *
          (4 ^ β + (2 * R + 2 : ℝ) / ((1 / 2 : ℝ) ^ β))) * (1 + A) := by
    intro x hx y hy hxy
    have hh := n5_metric_holder_of_edge_bound hβ hβ1 hM D hgood hx hy
    have hd : 0 < ‖x - y‖ ^ β :=
      Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) _
    have hdiv : D.1 (x, y) / ‖x - y‖ ^ β ≤
        M * ((2 * (d / (1 - (1 / 2 : ℝ) ^ β)) + d) *
          (4 ^ β + (2 * R + 2 : ℝ) / ((1 / 2 : ℝ) ^ β))) := by
      rw [div_le_iff₀ hd]
      simpa only [dist_eq_norm, mul_assoc, mul_comm, mul_left_comm] using hh
    have hreal := ENNReal.ofReal_le_ofReal hdiv
    rw [ENNReal.ofReal_mul' hC] at hreal
    have hMenn : ENNReal.ofReal M = 1 + A := by
      dsimp [M]
      rw [ENNReal.ofReal_add (by norm_num) ENNReal.toReal_nonneg, ENNReal.ofReal_one,
        ENNReal.ofReal_toReal hA]
    simpa only [hMenn, mul_comm] using hreal
  unfold holderConstRd
  exact iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy =>
    hpoint x hx y hy hxy

end HigherDimLQGContinuity
