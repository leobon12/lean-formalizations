import HigherDimLQGMetric.Weak.DetLFPPWeyl

/-!
# The reverse LFPP Weyl bound

Port of LQGMetric/LFPP/WeylUpper.lean to the HigherDimLFPP path and field definitions.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ} {ξ : ℝ} {φ : Rd d → ℝ}

private theorem le_sum_of_triangle {X : Type*} (δ : X → X → ℝ≥0∞)
    (hself : ∀ x, δ x x = 0) (htri : ∀ x y z, δ x z ≤ δ x y + δ y z)
    (v : ℕ → X) (N : ℕ) :
    δ (v 0) (v N) ≤ ∑ i ∈ Finset.range N, δ (v i) (v (i + 1)) := by
  induction N with
  | zero => simp [hself]
  | succ N ih =>
      rw [Finset.sum_range_succ]
      exact (htri _ (v N) _).trans (add_le_add ih le_rfl)

private theorem fieldLfppE_triangle (hφ : Continuous φ) (x y z : Rd d) :
    fieldLfppE ξ φ x z ≤ fieldLfppE ξ φ x y + fieldLfppE ξ φ y z := by
  rw [fieldLfppE_eq_ofReal_lfppDistOn hφ,
    fieldLfppE_eq_ofReal_lfppDistOn hφ,
    fieldLfppE_eq_ofReal_lfppDistOn hφ,
    ← ENNReal.ofReal_add
      (HigherDimLFPP.lfppDistOn_nonneg ξ φ univ x y)
      (HigherDimLFPP.lfppDistOn_nonneg ξ φ univ y z)]
  exact ENNReal.ofReal_le_ofReal (HigherDimLFPP.lfppDistOn_triangle hφ
    (HigherDimLFPP.PcwJoined.of_convex convex_univ (mem_univ x) (mem_univ y))
    (HigherDimLFPP.PcwJoined.of_convex convex_univ (mem_univ y) (mem_univ z)))

private theorem fieldLfppE_add_le_local (hφ : Continuous φ) (g : C(Rd d, ℝ))
    {x y : Rd d} {r a c δ : ℝ} (hr : 0 < r)
    (ha : ∀ u ∈ Metric.closedBall x r, a ≤ ξ * φ u)
    (hc : ∀ u ∈ Metric.closedBall x r, ξ * g u ≤ c)
    (hδ : 0 < δ)
    (hsmall : HigherDimLFPP.lfppDistOn ξ φ univ x y + δ ≤ Real.exp a * r) :
    fieldLfppE ξ (fun u => φ u + g u) x y ≤
      ENNReal.ofReal (Real.exp c) *
        (fieldLfppE ξ φ x y + ENNReal.ofReal δ) := by
  have hsum : Continuous (fun u => φ u + g u) := hφ.add g.continuous
  rw [fieldLfppE_eq_ofReal_lfppDistOn hsum,
    fieldLfppE_eq_ofReal_lfppDistOn hφ,
    ← ENNReal.ofReal_add (HigherDimLFPP.lfppDistOn_nonneg ξ φ univ x y) hδ.le,
    ← ENNReal.ofReal_mul (Real.exp_pos c).le]
  exact ENNReal.ofReal_le_ofReal
    (lfppDistOn_add_le_local hφ g hr ha hc hδ hsmall)

/-- Reverse half of the LFPP Weyl identity. -/
theorem fieldLfppE_le_weylScale (hφ : Continuous φ) (g : C(Rd d, ℝ))
    (z w : Rd d) :
    fieldLfppE ξ (fun u => φ u + g u) z w ≤
      weylScale ξ g (fieldLfppMetric ξ ⟨φ, hφ⟩) z w := by
  set D := fieldLfppMetric ξ ⟨φ, hφ⟩
  have hsum : Continuous (fun u => φ u + g u) := hφ.add g.continuous
  refine le_iInf fun L => le_iInf fun Q => le_iInf fun hL => le_iInf fun hc =>
    le_iInf fun hu => le_iInf fun h0 => le_iInf fun hL1 => ?_
  set I := ∫⁻ t in Icc 0 L, ENNReal.ofReal (Real.exp (ξ * g (Q t)))
  rcases hL.lt_or_eq with hLpos | hL0
  swap
  · subst hL0
    obtain rfl : z = w := h0.symm.trans hL1
    rw [fieldLfppE_eq_ofReal_lfppDistOn hsum]
    simp only [HigherDimLFPP.lfppDistOn_self, ENNReal.ofReal_zero]
    exact zero_le
  have key : ∀ ω : ℝ, 0 < ω →
      fieldLfppE ξ (fun u => φ u + g u) z w ≤
        ENNReal.ofReal ((1 + ω) * Real.exp (2 * ω)) * I := by
    intro ω hω
    have hQc : ContinuousOn Q (Icc 0 L) := D.continuous_unpt.comp_continuousOn hc
    set E : Rd d → ℝ := fun x => Real.exp (ξ * φ x)
    have hE : Continuous E := Real.continuous_exp.comp (continuous_const.mul hφ)
    set K := Q '' Icc 0 L
    have hK : IsCompact K := isCompact_Icc.image_of_continuousOn hQc
    set K' := Metric.cthickening 1 K
    have hK' : IsCompact K' := hK.cthickening
    have hKK' : K ⊆ K' := Metric.self_subset_cthickening K
    have hQK : ∀ t ∈ Icc 0 L, Q t ∈ K := fun t ht => mem_image_of_mem Q ht
    obtain ⟨x₀, -, hx₀⟩ := hK'.exists_isMinOn
      ⟨Q 0, hKK' (hQK 0 ⟨le_rfl, hL⟩)⟩ hE.continuousOn
    set m := E x₀
    have hm : 0 < m := Real.exp_pos _
    obtain ⟨η, hη, hηg⟩ := Metric.uniformContinuousOn_iff.1
      (hK'.uniformContinuousOn_of_continuous (f := fun x => ξ * g x)
        (continuous_const.mul g.continuous).continuousOn) ω hω
    set r := min (η / 2) 1
    have hr : 0 < r := lt_min (by positivity) one_pos
    obtain ⟨τ, hτ, hτQ⟩ := Metric.uniformContinuousOn_iff.1
      (isCompact_Icc.uniformContinuousOn_of_continuous hQc) (η / 2) (by positivity)
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt (lt_min (div_pos hτ hLpos)
      (div_pos (mul_pos hm hr) (mul_pos (by linarith : (0 : ℝ) < 1 + ω) hLpos)))
    have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    set Δ := L / ((N : ℝ) + 1)
    have hΔ : 0 < Δ := by positivity
    have hΔτ : Δ < τ := by
      have h := hN.trans_le (min_le_left _ _)
      rw [lt_div_iff₀ hLpos] at h
      simp only [Δ]
      rw [div_eq_mul_one_div, mul_comm]
      exact h
    have hΔr : (1 + ω) * Δ ≤ m * r := by
      have h := hN.trans_le (min_le_right _ _)
      rw [lt_div_iff₀ (by positivity)] at h
      have e : (1 + ω) * Δ = 1 / ((N : ℝ) + 1) * ((1 + ω) * L) := by
        simp only [Δ]
        ring
      rw [e]
      exact h.le
    set t : ℕ → ℝ := fun i => L * (i / ((N : ℝ) + 1))
    have ht_mono : Monotone t := fun i j hij => by simp only [t]; gcongr
    have ht_mem : ∀ i, i ≤ N + 1 → t i ∈ Icc (0 : ℝ) L := fun i hi => by
      refine ⟨by positivity, ?_⟩
      have h : (i : ℝ) / ((N : ℝ) + 1) ≤ 1 := by
        rw [div_le_one hN1]
        exact_mod_cast hi
      simp only [t]
      nlinarith
    have ht0 : t 0 = 0 := by simp [t]
    have ht1 : t (N + 1) = L := by
      simp only [t]
      push_cast
      rw [div_self hN1.ne', mul_one]
    have ht_step : ∀ i, t (i + 1) - t i = Δ := fun i => by
      simp only [t, Δ]
      push_cast
      ring
    have hchain := le_sum_of_triangle
      (fieldLfppE ξ (fun u => φ u + g u))
      (fun x => by
        rw [fieldLfppE_eq_ofReal_lfppDistOn hsum]
        simp only [HigherDimLFPP.lfppDistOn_self, ENNReal.ofReal_zero])
      (fieldLfppE_triangle hsum) (fun i => Q (t i)) (N + 1)
    simp only [ht0, ht1, h0, hL1] at hchain
    refine hchain.trans ?_
    have hpiece : ∀ i, i ≤ N →
        fieldLfppE ξ (fun u => φ u + g u) (Q (t i)) (Q (t (i + 1))) ≤
          ∫⁻ s in Ioc (t i) (t (i + 1)),
            ENNReal.ofReal ((1 + ω) * Real.exp (2 * ω)) *
              ENNReal.ofReal (Real.exp (ξ * g (Q s))) := by
      intro i hi
      have hti := ht_mem i (by omega)
      have hti1 := ht_mem (i + 1) (by omega)
      have hmono := ht_mono (Nat.le_succ i)
      set x := Q (t i)
      have hxK := hQK _ hti
      have hD : HigherDimLFPP.lfppDistOn ξ φ univ x (Q (t (i + 1))) ≤ Δ := by
        have h1 := eVariationOn.edist_le (D.pt ∘ Q)
          (s := Icc 0 L ∩ Icc (t i) (t (i + 1)))
          ⟨hti, le_rfl, hmono⟩ ⟨hti1, hmono, le_rfl⟩
        rw [hu hti hti1, NNReal.coe_one, one_mul, ht_step i] at h1
        change edist ((fieldLfppMetric ξ ⟨φ, hφ⟩).pt (Q (t i)))
          ((fieldLfppMetric ξ ⟨φ, hφ⟩).pt (Q (t (i + 1)))) ≤ ENNReal.ofReal Δ at h1
        rw [fieldLfppMetric_edist] at h1
        change fieldLfppE ξ φ x (Q (t (i + 1))) ≤ ENNReal.ofReal Δ at h1
        rw [fieldLfppE_eq_ofReal_lfppDistOn hφ] at h1
        exact (ENNReal.ofReal_le_ofReal_iff hΔ.le).1 h1
      have hsmall : HigherDimLFPP.lfppDistOn ξ φ univ x (Q (t (i + 1))) + ω * Δ ≤
          m * r := by
        linarith [hΔr]
      have hball : ∀ u ∈ Metric.closedBall x r, u ∈ K' := fun u hu =>
        Metric.mem_cthickening_of_dist_le u x 1 K hxK
          (hu.trans (min_le_right _ _))
      have hloc := fieldLfppE_add_le_local hφ g
        (a := ξ * φ x₀) (c := ξ * g x + ω) (δ := ω * Δ) hr
        (fun u hu => Real.exp_le_exp.mp (hx₀ (hball u hu)))
        (fun u hu => by
          have h := hηg u (hball u hu) x (hKK' hxK)
            ((Metric.mem_closedBall.1 hu).trans_lt
              ((min_le_left _ _).trans_lt (by linarith)))
          rw [Real.dist_eq, abs_lt] at h
          linarith)
        (by positivity : (0 : ℝ) < ω * Δ) hsmall
      refine hloc.trans ?_
      have hD' : fieldLfppE ξ φ x (Q (t (i + 1))) + ENNReal.ofReal (ω * Δ) ≤
          ENNReal.ofReal ((1 + ω) * Δ) := by
        rw [fieldLfppE_eq_ofReal_lfppDistOn hφ,
          ← ENNReal.ofReal_add
            (HigherDimLFPP.lfppDistOn_nonneg ξ φ univ x (Q (t (i + 1))))
            (mul_nonneg hω.le hΔ.le)]
        exact ENNReal.ofReal_le_ofReal (by linarith)
      refine (mul_le_mul' le_rfl hD').trans ?_
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
      have hvol : ENNReal.ofReal (Real.exp (ξ * g x + ω) * ((1 + ω) * Δ)) =
          ∫⁻ _ in Ioc (t i) (t (i + 1)),
            ENNReal.ofReal (Real.exp (ξ * g x + ω) * (1 + ω)) := by
        rw [setLIntegral_const, Real.volume_Ioc, ht_step i,
          ← ENNReal.ofReal_mul (by positivity)]
        ring_nf
      rw [hvol]
      refine setLIntegral_mono' measurableSet_Ioc fun s hs => ?_
      have hsI : s ∈ Icc 0 L := ⟨hti.1.trans hs.1.le, hs.2.trans hti1.2⟩
      have hQs : dist (Q s) x < η / 2 := by
        refine hτQ s hsI _ hti ?_
        rw [Real.dist_eq, abs_of_nonneg (by linarith [hs.1])]
        linarith [hs.2, ht_step i]
      have h := hηg _ (hKK' (hQK s hsI)) x (hKK' hxK) (by linarith)
      rw [Real.dist_eq, abs_lt] at h
      rw [← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have hexp : Real.exp (ξ * g x + ω) ≤
          Real.exp (2 * ω) * Real.exp (ξ * g (Q s)) := by
        rw [← Real.exp_add]
        exact Real.exp_le_exp.2 (by linarith)
      nlinarith [Real.exp_pos (ξ * g x + ω)]
    refine (Finset.sum_le_sum fun i hi =>
      hpiece i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))).trans ?_
    rw [LQGMetric.LFPP.sum_setLIntegral_Ioc _ t ht_mono, ht0, ht1,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact mul_le_mul' le_rfl (lintegral_mono_set Ioc_subset_Icc_self)
  have hT : Tendsto (fun ω : ℝ => ENNReal.ofReal ((1 + ω) * Real.exp (2 * ω)) * I)
      (𝓝[>] 0) (𝓝 I) := by
    have hc' : Continuous fun ω : ℝ => ENNReal.ofReal ((1 + ω) * Real.exp (2 * ω)) :=
      ENNReal.continuous_ofReal.comp ((continuous_const.add continuous_id).mul
        (Real.continuous_exp.comp (continuous_const.mul continuous_id)))
    have h1 : Tendsto (fun ω : ℝ => ENNReal.ofReal ((1 + ω) * Real.exp (2 * ω)))
        (𝓝[>] 0) (𝓝 1) := by
      simpa using (hc'.tendsto 0).mono_left nhdsWithin_le_nhds
    simpa using ENNReal.Tendsto.mul_const h1 (Or.inl one_ne_zero)
  exact ge_of_tendsto hT (eventually_nhdsWithin_of_forall fun ω hω => key ω hω)

/-- MA5 L6e: Weyl scaling of whole-space LFPP is LFPP of the summed field. -/
theorem l6e_weylLfpp : L6e_weylLfpp := by
  intro d ξ φ g hD z w
  have hEq : (⟨toCMapRd (fieldLfpp ξ ⇑φ), hD⟩ : ContMetric d) =
      fieldLfppMetric ξ φ := by
    apply Subtype.ext
    apply ContinuousMap.ext
    intro p
    exact toCMapRd_apply_of_continuous (continuous_fieldLfpp φ.continuous) p
  rw [hEq]
  have hfg : ((⇑φ : Rd d → ℝ) + (⇑g : Rd d → ℝ)) =
      (fun x => φ x + g x) := rfl
  rw [hfg]
  exact le_antisymm (weylScale_le_fieldLfppE φ.continuous g z w)
    (fieldLfppE_le_weylScale φ.continuous g z w)

end HigherDimLQGMetric
