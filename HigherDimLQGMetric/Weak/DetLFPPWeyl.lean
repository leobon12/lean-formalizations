import HigherDimLQGMetric.Weak.DetLFPPMetric
import LQGMetric.LFPP.Chain
import HigherDimLFPP.Paths.Compare

/-!
# LFPP and Weyl scaling in `ℝ^d`

Port of the deterministic path estimates in LQGMetric/LFPP/WeylLower.lean
and WeylUpper.lean, using HigherDimLFPP's path calculus.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ} {ξ : ℝ} {φ : Rd d → ℝ}

theorem lfppIntegrand_add (ξ : ℝ) (φ g : Rd d → ℝ) (P : ℝ → Rd d) (t : ℝ) :
    ENNReal.ofReal (HigherDimLFPP.lfppIntegrand ξ (φ + g) P t) =
      ENNReal.ofReal (Real.exp (ξ * g (P t))) *
        ENNReal.ofReal (HigherDimLFPP.lfppIntegrand ξ φ P t) := by
  unfold HigherDimLFPP.lfppIntegrand
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
  simp only [Pi.add_apply, mul_add, Real.exp_add]
  ring_nf

/-- The Weyl distance of a subpath is bounded by a uniform weight times its LFPP cost. -/
theorem weylScale_le_lfpp_piece (hφ : Continuous φ) (g : C(Rd d, ℝ))
    {P : ℝ → Rd d} {z w : Rd d} (hP : IsPiecewiseC1Path P z w)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1) {b : ℝ}
    (hb : ∀ τ ∈ Icc s t, ξ * g (P τ) ≤ b) :
    weylScale ξ g (fieldLfppMetric ξ ⟨φ, hφ⟩) (P s) (P t) ≤
      ENNReal.ofReal (Real.exp b) *
        ∫⁻ τ in Icc s t, ENNReal.ofReal (HigherDimLFPP.lfppIntegrand ξ φ P τ) := by
  set D := fieldLfppMetric ξ ⟨φ, hφ⟩
  set U : Set (Rd d) := {x | ξ * g x ≤ b}
  calc
    weylScale ξ g D (P s) (P t) ≤ weylScaleOn ξ g D U (P s) (P t) :=
      weylScale_le_weylScaleOn
    _ ≤ ENNReal.ofReal (Real.exp b) * D.internal U (P s) (P t) :=
      weylScaleOn_le_of_le (fun x hx => hx)
    _ ≤ ENNReal.ofReal (Real.exp b) * D.len P s t := by
      gcongr
      exact D.internal_le_len hst
        (hP.continuousOn.mono (Icc_subset_Icc hs ht)) (fun τ hτ => hb τ hτ)
    _ ≤ ENNReal.ofReal (Real.exp b) *
        ∫⁻ τ in Icc s t, ENNReal.ofReal (HigherDimLFPP.lfppIntegrand ξ φ P τ) := by
      gcongr
      exact fieldLfppMetric_len_le_lfppLen (ξ := ξ) ⟨φ, hφ⟩ hP hs ht

/-- First half of the LFPP Weyl identity: reweighting costs at most LFPP of the summed field. -/
theorem weylScale_le_fieldLfppE (hφ : Continuous φ) (g : C(Rd d, ℝ))
    (z w : Rd d) :
    weylScale ξ g (fieldLfppMetric ξ ⟨φ, hφ⟩) z w ≤
      fieldLfppE ξ (fun x => φ x + g x) z w := by
  refine le_iInf fun P => ?_
  obtain ⟨P, hP⟩ := P
  show _ ≤ lfppLen ξ (fun x => φ x + g x) P
  set L := lfppLen ξ (fun x => φ x + g x) P
  set D := fieldLfppMetric ξ ⟨φ, hφ⟩
  have key : ∀ ω : ℝ, 0 < ω →
      weylScale ξ g D z w ≤ ENNReal.ofReal (Real.exp (2 * ω)) * L := by
    intro ω hω
    have hgc : ContinuousOn (fun s => ξ * g (P s)) (Icc 0 1) :=
      (continuous_const.mul g.continuous).comp_continuousOn hP.continuousOn
    obtain ⟨τ, hτ, hτg⟩ := Metric.uniformContinuousOn_iff.1
      (isCompact_Icc.uniformContinuousOn_of_continuous hgc) ω hω
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hτ
    set t : ℕ → ℝ := fun i => i / ((N : ℝ) + 1)
    have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have ht_mono : Monotone t := fun i j hij => by simp only [t]; gcongr
    have ht_mem : ∀ i, i ≤ N + 1 → t i ∈ Icc (0 : ℝ) 1 := fun i hi => by
      refine ⟨by positivity, ?_⟩
      rw [div_le_one hN1]
      exact_mod_cast hi
    have ht0 : t 0 = 0 := by simp [t]
    have ht1 : t (N + 1) = 1 := by simp only [t]; push_cast; exact div_self hN1.ne'
    have ht_step : ∀ i, t (i + 1) - t i = 1 / ((N : ℝ) + 1) := fun i => by
      simp only [t]; push_cast; ring
    have hchain := weylScaleOn_le_sum (ξ := ξ) (f := g) (D := D) (U := univ)
      (fun i => P (t i)) (mem_univ _) (N + 1)
    simp only [weylScaleOn_univ, ht0, ht1, hP.source, hP.target] at hchain
    refine hchain.trans ?_
    have hpiece : ∀ i, i ≤ N →
        weylScale ξ g D (P (t i)) (P (t (i + 1))) ≤
          ∫⁻ s in Ioc (t i) (t (i + 1)),
            ENNReal.ofReal (Real.exp (2 * ω)) *
              ENNReal.ofReal (HigherDimLFPP.lfppIntegrand ξ (fun x => φ x + g x) P s) := by
      intro i hi
      have hti := ht_mem i (by omega)
      have hti1 := ht_mem (i + 1) (by omega)
      have hclose : ∀ s ∈ Icc (t i) (t (i + 1)),
          |ξ * g (P s) - ξ * g (P (t i))| < ω := by
        intro s hs
        have h := hτg s ⟨hti.1.trans hs.1, hs.2.trans hti1.2⟩ _ hti (by
          rw [Real.dist_eq, abs_of_nonneg (by linarith [hs.1])]
          linarith [hs.2, ht_step i])
        rwa [Real.dist_eq] at h
      refine (weylScale_le_lfpp_piece hφ g hP hti.1
        (ht_mono (Nat.le_succ i)) hti1.2
        (b := ξ * g (P (t i)) + ω)
        (fun s hs => by linarith [(abs_lt.1 (hclose s hs)).2])).trans ?_
      rw [setLIntegral_congr Ioc_ae_eq_Icc,
        ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine setLIntegral_mono' measurableSet_Icc fun s hs => ?_
      have hadd : ENNReal.ofReal
          (HigherDimLFPP.lfppIntegrand ξ (fun x => φ x + g x) P s) =
          ENNReal.ofReal (Real.exp (ξ * g (P s))) *
            ENNReal.ofReal (HigherDimLFPP.lfppIntegrand ξ φ P s) := by
        have hfg : (φ + (g : Rd d → ℝ)) = (fun x => φ x + g x) := rfl
        rw [← hfg]
        exact lfppIntegrand_add ξ φ (⇑g) P s
      rw [hadd]
      have hexp : Real.exp (ξ * g (P (t i)) + ω) ≤
          Real.exp (2 * ω) * Real.exp (ξ * g (P s)) := by
        rw [← Real.exp_add]
        exact Real.exp_le_exp.2 (by linarith [(abs_lt.1 (hclose s hs)).1])
      calc
        ENNReal.ofReal (Real.exp (ξ * g (P (t i)) + ω)) *
            ENNReal.ofReal (HigherDimLFPP.lfppIntegrand ξ φ P s) ≤
          ENNReal.ofReal (Real.exp (2 * ω) * Real.exp (ξ * g (P s))) *
            ENNReal.ofReal (HigherDimLFPP.lfppIntegrand ξ φ P s) :=
              mul_le_mul' (ENNReal.ofReal_le_ofReal hexp) le_rfl
        _ = _ := by rw [ENNReal.ofReal_mul (Real.exp_pos _).le, mul_assoc]
    refine (Finset.sum_le_sum fun i hi =>
      hpiece i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))).trans ?_
    rw [LQGMetric.LFPP.sum_setLIntegral_Ioc _ t ht_mono, ht0, ht1,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact mul_le_mul_right (lintegral_mono_set Ioc_subset_Icc_self) _
  have hT : Tendsto (fun ω : ℝ => ENNReal.ofReal (Real.exp (2 * ω)) * L)
      (𝓝[>] 0) (𝓝 L) := by
    have hc : Continuous fun ω : ℝ => ENNReal.ofReal (Real.exp (2 * ω)) :=
      ENNReal.continuous_ofReal.comp
        (Real.continuous_exp.comp (continuous_const.mul continuous_id))
    have h1 : Tendsto (fun ω : ℝ => ENNReal.ofReal (Real.exp (2 * ω)))
        (𝓝[>] 0) (𝓝 1) := by
      simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    simpa using ENNReal.Tendsto.mul_const h1 (Or.inl one_ne_zero)
  exact ge_of_tendsto hT (eventually_nhdsWithin_of_forall fun ω hω => key ω hω)

/-- The LFPP cost of a prefix is at most the whole path cost. -/
theorem lfppLength_subPath_le (hφ : Continuous φ)
    {P : ℝ → Rd d} {z w : Rd d} (hP : IsPiecewiseC1Path P z w)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    HigherDimLFPP.lfppLength ξ φ (HigherDimLFPP.subPath P 0 t) ≤
      HigherDimLFPP.lfppLength ξ φ P := by
  have hI := hP.intervalIntegrable_lfppIntegrand hφ ξ
  have hI₀ := HigherDimLFPP.intervalIntegrable_of_sub hI le_rfl ht.1 ht.2
  have hI₁ := HigherDimLFPP.intervalIntegrable_of_sub hI ht.1 ht.2 le_rfl
  rw [HigherDimLFPP.lfppLength_subPath ξ φ P ht.1,
    HigherDimLFPP.lfppLength_eq_integral,
    ← intervalIntegral.integral_add_adjacent_intervals hI₀ hI₁]
  exact le_add_of_nonneg_right
    (HigherDimLFPP.integral_lfppIntegrand_nonneg ξ φ P ht.2)

/-- Local LFPP field comparison when a near-optimal base path cannot leave the ball. -/
theorem lfppDistOn_add_le_local (hφ : Continuous φ) (g : C(Rd d, ℝ))
    {x y : Rd d} {r a c δ : ℝ} (_hr : 0 < r)
    (ha : ∀ u ∈ Metric.closedBall x r, a ≤ ξ * φ u)
    (hc : ∀ u ∈ Metric.closedBall x r, ξ * g u ≤ c)
    (hδ : 0 < δ)
    (hsmall : HigherDimLFPP.lfppDistOn ξ φ univ x y + δ ≤ Real.exp a * r) :
    HigherDimLFPP.lfppDistOn ξ (fun u => φ u + g u) univ x y ≤
      Real.exp c * (HigherDimLFPP.lfppDistOn ξ φ univ x y + δ) := by
  have hj := HigherDimLFPP.PcwJoined.of_convex convex_univ (mem_univ x) (mem_univ y)
  have hlt : HigherDimLFPP.lfppDistOn ξ φ univ x y <
      HigherDimLFPP.lfppDistOn ξ φ univ x y + δ := lt_add_of_pos_right _ hδ
  obtain ⟨P, hP, -, hPcost⟩ := HigherDimLFPP.exists_lfppLength_lt hj hlt
  have hin : ∀ t ∈ Icc (0 : ℝ) 1, P t ∈ Metric.closedBall x r := by
    intro t ht
    by_contra hout
    have hgt : r < ‖P t - x‖ := by
      simpa only [Metric.mem_closedBall, dist_eq_norm, not_le] using hout
    have hsub := hP.subPath le_rfl ht.1 ht.2
    have hrsub : r ≤ ‖P t - P 0‖ := by simpa only [hP.source] using hgt.le
    have hasub : ∀ u ∈ Metric.closedBall (P 0) r, a ≤ ξ * φ u := by
      simpa only [hP.source] using ha
    have hbase := HigherDimLFPP.IsPcwC1Path.exp_mul_le_lfppLength hφ hsub
      hrsub hasub
    have hcost := lfppLength_subPath_le (ξ := ξ) hφ hP ht
    exact not_lt_of_ge (hbase.trans hcost) (hPcost.trans_le hsmall)
  have hcomp := hP.lfppLength_le_mul_of_exp_le (hφ.add g.continuous)
    hφ (ζ := ξ) (C := Real.exp c) (φ := fun u => φ u + g u)
    (ψ := φ) (fun t ht => by
      rw [show ξ * (φ (P t) + g (P t)) = ξ * φ (P t) + ξ * g (P t) by ring,
        Real.exp_add]
      calc
        Real.exp (ξ * φ (P t)) * Real.exp (ξ * g (P t)) =
            Real.exp (ξ * g (P t)) * Real.exp (ξ * φ (P t)) := mul_comm _ _
        _ ≤ Real.exp c * Real.exp (ξ * φ (P t)) :=
          mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (hc _ (hin t ht)))
            (Real.exp_pos _).le)
  exact (HigherDimLFPP.lfppDistOn_le_lfppLength hP (fun _ _ => mem_univ _)).trans
    (hcomp.trans (mul_le_mul_of_nonneg_left hPcost.le (Real.exp_pos _).le))

end HigherDimLQGMetric
