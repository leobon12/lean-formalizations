import QuantumZipper.Proofs.Thm18.G3ZqL10Cert
import QuantumZipper.Proofs.GFF.CircleContinuity
import QuantumZipper.Proofs.Thm18.G3ZqFLoc
import QuantumZipper.Proofs.Zipper.D3PlusIII
import QuantumZipper.Proofs.Zipper.D3PlusN2H3WinPsi
import QuantumZipper.Proofs.Section5.Prop16PalmGlobalMeas

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ZQ-REG (1): the local certificate `LocCertC` from a D3⁺ model near `0`

* `locCertC_congr`: `LocCertC` only depends on the raw values at the dyadic folded circles near
  `0` (`AgreeNear`).
* `locCertC_of_agree_model`: if the reconstructed field of `c` agrees near `0` with a D3⁺ model
  field `zoomModel γ α L ρ₀ x' g` (`x'` regular with an area limit on `ℍ` charging every nonempty
  open subset of `ℍ`, `g` continuous near `0`), then `LocCertC γ c` holds: the dyadic values at
  a fixed small radius are those of a continuous function of the centre (the regular version of
  `x' + ofFun (g + const)` plus the explicit circle average `α(−log max(s, ‖d‖))` of the log
  singularity), and the local area measure of the model is the positive measure of
  `D3Plus.qAreaMeasureOn_zoomModel` (Sheffield, arXiv:1012.4797, proof of Prop. 1.6, p. 25: the
  area measure charges every neighbourhood of the marked point).

Own elementary bookkeeping (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm
namespace ZqR

open Factorization G3ZqL D3Plus LQGMeas

/-! ## Dyadic points are fixed by finer roundings -/

theorem dyadicRound_idem {n m : ℕ} (hnm : n ≤ m) (t : ℝ) :
    dyadicRound m (dyadicRound n t) = dyadicRound n t := by
  unfold dyadicRound
  set j : ℤ := ⌊(2 : ℝ) ^ n * t⌋ with hj
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  have e : (2 : ℝ) ^ m * ((j : ℝ) / 2 ^ n) = ((j * 2 ^ (m - n) : ℤ) : ℝ) := by
    have : (2 : ℝ) ^ m = 2 ^ (m - n) * 2 ^ n := by
      rw [← pow_add, Nat.sub_add_cancel hnm]
    rw [this]
    push_cast
    field_simp
  rw [e, Int.floor_intCast]
  have : (2 : ℝ) ^ m = 2 ^ (m - n) * 2 ^ n := by
    rw [← pow_add, Nat.sub_add_cancel hnm]
  rw [this]
  push_cast
  field_simp

theorem dyadicRoundC_idem {n m : ℕ} (hnm : n ≤ m) (z : ℂ) :
    dyadicRoundC m (dyadicRoundC n z) = dyadicRoundC n z := by
  apply Complex.ext
  · show dyadicRound m (dyadicRound n z.re) = dyadicRound n z.re
    exact dyadicRound_idem hnm _
  · show dyadicRound m (dyadicRound n z.im) = dyadicRound n z.im
    exact dyadicRound_idem hnm _

/-- A regular sample is exact at the dyadic folded circles. -/
theorem eq_of_isRegularWith_dyadic {x : FieldSample} {F : ℂ × ℝ → ℝ} (hF : IsRegularWith x F)
    (n k : ℕ) {z : ℂ} (hz : dyadicRoundC n z ∈ Hbar) :
    x (foldedCircle (dyadicRoundC n z) (radius k)) = F (dyadicRoundC n z, radius k) := by
  have ht := hF.2.1 k _ hz
  refine tendsto_nhds_unique (tendsto_const_nhds.congr' ?_) ht
  filter_upwards [eventually_ge_atTop n] with m hm
  rw [dyadicRoundC_idem hm]

/-- Dyadic roundings of points of a small ball stay in a slightly larger ball. -/
theorem norm_dyadicRoundC_lt {z : ℂ} {a b : ℝ} (hz : ‖z‖ < a) {n : ℕ}
    (hn : 2 * (1 / 2 ^ n : ℝ) < b) : ‖dyadicRoundC n z‖ < a + b := by
  have h1 := CircleCont.norm_dyadicRoundC_sub_le n z
  have h2 := norm_add_le z (dyadicRoundC n z - z)
  rw [add_sub_cancel] at h2
  linarith

theorem exists_pow_small {b : ℝ} (hb : 0 < b) : ∃ N : ℕ, ∀ n, N ≤ n → 2 * (1 / 2 ^ n : ℝ) < b := by
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (show 0 < b / 2 by positivity)
    (show (1 / 2 : ℝ) < 1 by norm_num)
  refine ⟨N, fun n hn => ?_⟩
  have h2 : (1 / 2 : ℝ) ^ n ≤ (1 / 2) ^ N := pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
  have h3 : (1 : ℝ) / 2 ^ n = (1 / 2) ^ n := by rw [one_div_pow]
  rw [h3]
  linarith

/-! ## Congruence of the certificate -/

/-- **`LocCertC` only depends on the raw values near `0`.** -/
theorem locCertC_congr {γ r : ℝ} (hr : 0 < r) {c c' : ℕ → ℝ} (h : LocCertC γ c)
    (hag : AgreeNear (reconstruct c) (reconstruct c') r) : LocCertC γ c' := by
  obtain ⟨ρ, hρ, k₀, h1, h2⟩ := h
  obtain ⟨ρ', hρ'0, hρ'⟩ := exists_rat_btwn (lt_min hρ (show 0 < r / 4 by positivity))
  have hρ'ρ : (ρ' : ℝ) < ρ := lt_of_lt_of_le hρ' (min_le_left _ _)
  have hρ'r : (ρ' : ℝ) < r / 4 := lt_of_lt_of_le hρ' (min_le_right _ _)
  obtain ⟨k₁, hk₁⟩ := AtomlessUncond.exists_radius_lt (show 0 < r / 4 by positivity)
  obtain ⟨N₀, hN₀⟩ := exists_pow_small (show 0 < r / 4 by positivity)
  have hclose : ∀ k, k₁ ≤ k → ∀ n, N₀ ≤ n → ∀ z : ℂ, ‖z‖ < ρ' →
      rawAt c' n k z = rawAt c n k z := by
    intro k hk n hn z hz
    have h3 := norm_dyadicRoundC_lt hz (hN₀ n hn)
    have h4 := hk₁ k hk
    exact (hag n k z (by linarith)).symm
  refine ⟨ρ', hρ'0, max k₀ k₁, fun k hk ε hε => ?_, fun q hq hqρ => ?_⟩
  · obtain ⟨N, hN⟩ := h1 k (le_of_max_le_left hk) ε hε
    refine ⟨max N N₀, fun n hn n' hn' z hz => ?_⟩
    have hz' : ‖z‖ < ρ' := by simpa using hz.1
    rw [hclose k (le_of_max_le_right hk) n (le_of_max_le_right hn) z hz',
      hclose k (le_of_max_le_right hk) n' (le_of_max_le_right hn') z hz']
    exact hN n (le_of_max_le_left hn) n' (le_of_max_le_left hn') z
      ⟨ball_subset_ball hρ'ρ.le hz.1, hz.2⟩
  · obtain ⟨n, ⟨l, hl⟩, hpos⟩ := h2 q hq (hqρ.trans hρ'ρ)
    set f := openBump (ball (0 : ℂ) q ∩ H) n with hf
    have hev : (fun k => ∫ z, f z ∂areaApprox γ (reconstruct c) k) =ᶠ[atTop]
        fun k => ∫ z, f z ∂areaApprox γ (reconstruct c') k := by
      filter_upwards [eventually_ge_atTop k₁] with k hk
      set K := tsupport f with hK
      have hKm : MeasurableSet K := (isClosed_tsupport f).measurableSet
      have hKq : K ⊆ ball (0 : ℂ) q ∩ H := tsupport_openBump_subset _ n
      have hvan : ∀ z, z ∉ K → f z = 0 := fun z hz => image_eq_zero_of_notMem_tsupport hz
      have hmeq : (areaApprox γ (reconstruct c) k).restrict K =
          (areaApprox γ (reconstruct c') k).restrict K := by
        rw [areaApprox, areaApprox, restrict_withDensity hKm, restrict_withDensity hKm]
        refine withDensity_congr_ae ((ae_restrict_iff' hKm).2 (Eventually.of_forall fun z hz => ?_))
        have hzq := (hKq hz).1
        rw [mem_ball, dist_zero_right] at hzq
        have hzk : ‖z‖ + radius k < r := by linarith [hk₁ k hk]
        simp only [avgReg_congr hag hzk]
      have e1 : ∫ z, f z ∂(areaApprox γ (reconstruct c) k) =
          ∫ z in K, f z ∂(areaApprox γ (reconstruct c) k) :=
        (setIntegral_eq_integral_of_forall_compl_eq_zero hvan).symm
      have e2 : ∫ z, f z ∂(areaApprox γ (reconstruct c') k) =
          ∫ z in K, f z ∂(areaApprox γ (reconstruct c') k) :=
        (setIntegral_eq_integral_of_forall_compl_eq_zero hvan).symm
      rw [e1, e2, hmeq]
    refine ⟨n, ⟨l, hl.congr' hev⟩, ?_⟩
    rwa [← liminf_congr hev]

/-! ## The certificate for a field agreeing near `0` with a D3⁺ model -/

/-- The model field on small folded circles: a regular part plus the explicit circle average of
the log singularity. -/
theorem zoomModel_fc_split {γ α L r : ℝ} {ρ₀ : Measure ℂ} {x' : FieldSample} {g g' : ℂ → ℝ}
    (hg' : ContinuousOn g' Hbar) (heq : EqOn g' g (closedBall (0 : ℂ) r)) {d : ℂ}
    (hd : d ∈ Hbar) {s : ℝ} (hs : 0 < s) (hds : ‖d‖ + s ≤ r) :
    zoomModel γ α L ρ₀ x' g (foldedCircle d s) =
      (x' + ofFun (fun z => g' (foldH z) + (L / γ - x' ρ₀))) (foldedCircle d s) +
        α * -Real.log (max s ‖d‖) := by
  set C₀ := L / γ - x' ρ₀ with hC₀
  have hg₂ : Continuous fun z => g' (foldH z) + C₀ :=
    (hg'.comp_continuous TwoPoint.continuous_foldH CircleFubini.foldH_mem_Hbar').add
      continuous_const
  have hint₁ : Integrable (fun u : ℂ => α * -Real.log ‖u‖) (foldedCircle d s) :=
    (CoordReg.integrable_log_norm_foldedCircle d s).neg.const_mul α
  have hint₂ : Integrable (fun z => g' (foldH z) + C₀) (foldedCircle d s) :=
    Prop16Asm.integrable_foldedCircle_of_continuous_pg hg₂ hd hs
  have hcongr : ∫ u, (α * -Real.log ‖u‖ + g u + C₀) ∂foldedCircle d s =
      ∫ u, (α * -Real.log ‖u‖ + (g' (foldH u) + C₀)) ∂foldedCircle d s := by
    refine integral_congr_ae ?_
    filter_upwards [TwoPoint.foldedCircle_ae_mem_H d hs, LocalRule.ae_fc_mem_closedBall hd hs]
      with u hu hub
    have hub' : u ∈ closedBall (0 : ℂ) r := by
      rw [mem_closedBall, dist_zero_right]
      rw [mem_closedBall, dist_eq_norm] at hub
      have := norm_sub_norm_le u d
      linarith [norm_nonneg d]
    rw [CircleFubini.foldH_of_mem' (H_subset_Hbar hu), heq hub']
    ring
  simp only [zoomModel, Pi.add_apply, ofFun]
  rw [hcongr, integral_add hint₁ hint₂, integral_const_mul, integral_neg,
    D3Plus.integral_log_norm_fc d hs]
  ring

/-- **The certificate from agreement near `0` with a D3⁺ model.** -/
theorem locCertC_of_agree_model {γ α L r : ℝ} (hγ : γ ≠ 0) (hr : 0 < r) {ρ₀ : Measure ℂ}
    {x' : FieldSample} {g : ℂ → ℝ} (hx : IsRegularSample x') {μ : Measure ℂ}
    (hμ : IsVagueLimitOn H (areaApprox γ x') μ)
    (hpos : ∀ V : Set ℂ, IsOpen V → V ⊆ H → V.Nonempty → 0 < μ V)
    (hg : ContinuousOn g (ball (0 : ℂ) r ∩ Hbar)) {c : ℕ → ℝ}
    (hag : AgreeNear (reconstruct c) (zoomModel γ α L ρ₀ x' g) r) : LocCertC γ c := by
  set M := zoomModel γ α L ρ₀ x' g with hM
  -- a continuous cut-off of `g`
  obtain ⟨δ, hδ, g', hg'c, hg'eq⟩ := LocalRule.exists_cutoff isOpen_ball hg
    (isCompact_closedBall (0 : ℂ) (r / 2)) (closedBall_subset_ball (by linarith))
  have heq : EqOn g' g (closedBall (0 : ℂ) (r / 2)) := fun u hu =>
    hg'eq (self_subset_cthickening _ hu)
  set C₀ := L / γ - x' ρ₀ with hC₀
  have hg₂ : Continuous fun z => g' (foldH z) + C₀ :=
    (hg'c.comp_continuous TwoPoint.continuous_foldH CircleFubini.foldH_mem_Hbar').add
      continuous_const
  obtain ⟨F, hF⟩ := GoodSample.gs_add_ofFun_sample hx hg₂.continuousOn
  -- the local area limit of the model and its positivity
  have hres := AtomlessUncond.isVagueLimitOn_restrict (isOpen_halfDisc r) (halfDisc_subset_H r) hμ
  have hv := LocalRule.isVagueLimitOn_add_ofFun hx (isOpen_halfDisc r) (halfDisc_subset_H r) hres
    (isOpen_ball.sdiff isClosed_singleton) (halfDisc_subset_ball_diff r)
    (continuousOn_zoomPot (γ := γ) (α := α) (L := L) (ρ₀ := ρ₀) (x := x') hg)
  set m := ((μ.restrict (halfDisc r)).withDensity fun z => ENNReal.ofReal
    (Real.exp (γ * (α * -Real.log ‖z‖ + g z + (L / γ - x' ρ₀))))) with hm
  have hvM : IsVagueLimitOn (halfDisc r) (areaApprox γ M) m := hv
  have hmq : ∀ q : ℝ, 0 < q → 0 < m (ball 0 q ∩ H) := by
    intro q hq
    have e1 := LocalRule.qAreaMeasureOn_eq (isOpen_halfDisc r) hvM
    rw [qAreaMeasureOn_zoomModel hγ hx hμ hg] at e1
    rw [← e1, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_pos (ENNReal.ofReal_pos.2 (Real.exp_pos L)).ne'
      (zoomMeasure_pos hr hpos hg q hq).ne'
  have hvu : IsVagueLimitOn (halfDisc r) (areaApprox γ (reconstruct c)) m :=
    isVagueLimitOn_halfDisc_of_agree hag.symm' hvM
  -- the radii
  obtain ⟨ρ, hρ0, hρ⟩ := exists_rat_btwn (show 0 < r / 8 by positivity)
  obtain ⟨k₀, hk₀⟩ := AtomlessUncond.exists_radius_lt (show 0 < r / 8 by positivity)
  refine ⟨ρ, hρ0, k₀, fun k hk ε hε => ?_, fun q hq hqρ => ?_⟩
  · set s := radius k with hs
    have hs0 : 0 < s := radius_pos k
    have hsr : s < r / 8 := hk₀ k hk
    set G : ℂ → ℝ := fun d => F (d, s) + α * -Real.log (max s ‖d‖) with hG
    have hGc : ContinuousOn G Hbar := by
      refine (hF.1.comp (continuousOn_id.prodMk continuousOn_const)
        fun z hz => ⟨hz, hs0⟩).add ?_
      refine (Continuous.continuousOn ?_)
      exact continuous_const.mul ((continuous_const.max continuous_norm).log
        fun d => (lt_of_lt_of_le hs0 (le_max_left _ _)).ne').neg
    set K : Set ℂ := closedBall (0 : ℂ) (r / 2) ∩ Hbar with hK
    have hKc : IsCompact K := (isCompact_closedBall _ _).inter_right isClosed_Hbar
    obtain ⟨δ', hδ', hU⟩ := Metric.uniformContinuousOn_iff.1
      (hKc.uniformContinuousOn_of_continuous (hGc.mono inter_subset_right)) ε hε
    obtain ⟨N, hN⟩ := exists_pow_small (show 0 < min (δ' / 2) (r / 8) by positivity)
    -- the raw values are values of `G`
    have hval : ∀ n, N ≤ n → ∀ z ∈ ball (0 : ℂ) ρ ∩ H,
        rawAt c n k z = G (dyadicRoundC n z) ∧ dyadicRoundC n z ∈ K ∧
          ‖dyadicRoundC n z - z‖ < δ' / 2 := by
      intro n hn z hz
      have hz' : ‖z‖ < ρ := by simpa using hz.1
      have hsm := hN n hn
      have h1 := norm_dyadicRoundC_lt hz' (lt_of_lt_of_le hsm (min_le_right _ _))
      have h2 := CircleCont.norm_dyadicRoundC_sub_le n z
      have hdH : dyadicRoundC n z ∈ Hbar :=
        CircleCont.dyadicRoundC_mem_Hbar (H_subset_Hbar hz.2) n
      refine ⟨?_, ⟨?_, hdH⟩, by linarith [min_le_left (δ' / 2) (r / 8)]⟩
      · unfold rawAt
        rw [hag n k z (by linarith)]
        have e := zoomModel_fc_split (γ := γ) (α := α) (L := L) (ρ₀ := ρ₀) (x' := x') hg'c heq hdH
          (radius_pos k) (by linarith)
        show zoomModel γ α L ρ₀ x' g _ = _
        rw [e, eq_of_isRegularWith_dyadic hF n k hdH]
      · rw [mem_closedBall, dist_zero_right]; linarith
    refine ⟨N, fun n hn n' hn' z hz => ?_⟩
    obtain ⟨e1, m1, d1⟩ := hval n hn z hz
    obtain ⟨e2, m2, d2⟩ := hval n' hn' z hz
    have hd : dist (dyadicRoundC n z) (dyadicRoundC n' z) < δ' := by
      rw [dist_eq_norm]
      have := norm_sub_le (dyadicRoundC n z - z) (dyadicRoundC n' z - z)
      have e : dyadicRoundC n z - z - (dyadicRoundC n' z - z) =
          dyadicRoundC n z - dyadicRoundC n' z := by ring
      rw [e] at this
      linarith
    have hlt := hU _ m1 _ m2 hd
    rw [Real.dist_eq] at hlt
    rw [e1, e2]
    exact hlt.le
  · have hqr : (q : ℝ) ≤ r := by linarith
    have hp : 0 < areaProxy γ (reconstruct c) q := by
      rw [G3ZqF.areaProxy_eq_of_local hvu hqr]
      exact hmq q hq
    unfold areaProxy at hp
    obtain ⟨n, hn⟩ := lt_iSup_iff.1 hp
    have hUb : Bornology.IsBounded (ball (0 : ℂ) q ∩ H) := isBounded_ball.subset inter_subset_left
    have ht := hvu.2.2 (openBump (ball (0 : ℂ) q ∩ H) n) (continuous_openBump _ n)
      (hasCompactSupport_openBump hUb n)
      ((tsupport_openBump_subset _ n).trans fun z hz =>
        ⟨ball_subset_ball hqr hz.1, hz.2⟩)
    refine ⟨n, ⟨_, ht⟩, ?_⟩
    have e : areaFun γ (openBump (ball (0 : ℂ) q ∩ H) n) (reconstruct c) =
        liminf (fun k => ∫ z, openBump (ball (0 : ℂ) q ∩ H) n z
          ∂areaApprox γ (reconstruct c) k) atTop := rfl
    rw [← e]
    exact ENNReal.ofReal_pos.1 hn

end ZqR
end Thm18Asm
end QuantumZipper
