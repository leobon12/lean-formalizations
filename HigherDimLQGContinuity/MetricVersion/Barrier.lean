import HigherDimLQGContinuity.MetricVersion.Dilation

/-!
# Metric-valued versions (packet E5): common barriers on rational windows

Part C, `c:lem-opt-proper` ((5.12)–(5.13)): almost surely, for every rational window `J = [c, c'] ⊆ S_d` and every
`L`, some dyadic annulus `∂B_{2^j} × ∂B_{2^{j+1}}` has `X(ξ)(g)`-distance `> L` for every `ξ ∈ J`
(`ae_barrier_version`). The proof is described in `MetricVersion/Dilation.lean`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric ProbabilityTheory
open scoped ENNReal NNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- The scale factor at the dyadic scale `2^j` is at least `e^{j m log 2 / 2}` when `m ≤ ϕ(q)`, `0 < q ≤ c'` and
`|g_{2^j}(0)| ≤ (m log 2 / (2c')) j`. -/
theorem mv_scaleS_lower {q c' m : ℝ} (hq : 0 < q) (hqc : q ≤ c') (hc' : 0 < c') (hm : m ≤ phiXi d q)
    (j : ℕ) (g : DistRd d) (hsm : |sphereAvg g ((2 : ℝ) ^ j) 0| ≤ Real.log 2 * m / (2 * c') * j) :
    Real.exp (j * (Real.log 2 * m / 2)) ≤ scaleS d q 1 ((2 : ℝ) ^ j) 0 g := by
  rw [scaleS_eq_exp d q 1 (pow_pos two_pos j), one_mul, Real.log_pow]
  apply Real.exp_le_exp.2
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg one_le_two
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  set Y := sphereAvg g ((2 : ℝ) ^ j) 0
  have h1 : m * (j * Real.log 2) ≤ phiXi d q * (j * Real.log 2) :=
    mul_le_mul_of_nonneg_right hm (mul_nonneg hj hlog)
  have h2 : -(q * |Y|) ≤ q * Y := by
    have := neg_abs_le Y
    nlinarith [abs_nonneg Y]
  have h3 : q * |Y| ≤ c' * (Real.log 2 * m / (2 * c') * j) :=
    mul_le_mul hqc hsm (abs_nonneg _) hc'.le
  have h4 : c' * (Real.log 2 * m / (2 * c') * j) = j * (Real.log 2 * m / 2) := by
    field_simp
  nlinarith

/-- **`c:lem-opt-proper`, the barrier**: almost surely, for every rational window `[c, c'] ⊆ S_d` and every `L`, the
distances across some dyadic annulus exceed `L` for every parameter of the window. -/
theorem ae_barrier_version (hd : 3 ≤ d) (F : PairingFrame d) {X : ℝ → DistRd d → C(Rd d × Rd d, ℝ)}
    (hX : PosVersionStmt d X) :
    ∀ᵐ g ∂(normLGFLaw d), ∀ c c' : ℚ, (c : ℝ) < c' → Icc (c : ℝ) c' ⊆ subcritSet d → ∀ L : ℝ,
      ∃ a b : ℝ, 0 < a ∧ a < b ∧ ∀ ξ ∈ Icc (c : ℝ) c', ∀ u w : Rd d, ‖u‖ = a → ‖w‖ = b →
        L < X ξ g (u, w) := by
  have hd2 : 2 ≤ d := by omega
  have := (normLGFLaw_spec_holds d hd2).1
  have hNT : Nontrivial (Rd d) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; omega)
  obtain ⟨E, -, hEae, -, hcont, -, -⟩ := weyl_translates_ae hd F hX
  have hpos := ae_forall_pos_version hd F hX
  have hscale := ae_version_dilationTwoPow hd hX
  rw [ae_all_iff]
  intro c
  rw [ae_all_iff]
  intro c'
  by_cases hcond : (c : ℝ) < c' ∧ Icc (c : ℝ) c' ⊆ subcritSet d
  swap
  · exact Eventually.of_forall fun g h1 h2 => absurd ⟨h1, h2⟩ hcond
  obtain ⟨hcc, hJ⟩ := hcond
  set J := Icc (c : ℝ) c' with hJdef
  have hJne : J.Nonempty := nonempty_Icc.2 hcc.le
  have hc'J : (c' : ℝ) ∈ J := ⟨hcc.le, le_rfl⟩
  have hc'pos : (0 : ℝ) < c' := (hJ hc'J).1
  -- the unit annulus
  set K₁₂ : Set (Rd d × Rd d) := sphere (0 : Rd d) 1 ×ˢ sphere (0 : Rd d) 2 with hK₁₂
  have hK : IsCompact K₁₂ := (isCompact_sphere _ _).prod (isCompact_sphere _ _)
  have hKne : K₁₂.Nonempty :=
    (NormedSpace.sphere_nonempty.2 zero_le_one).prod (NormedSpace.sphere_nonempty.2 zero_le_two)
  have hKd : ∀ p ∈ K₁₂, p.1 ≠ p.2 := by
    rintro ⟨u, w⟩ ⟨hu, hw⟩ huw
    simp only at huw
    rw [mem_sphere_zero_iff_norm] at hu hw
    rw [huw] at hu
    linarith
  -- the events `G k`
  set G : ℕ → Set (DistRd d) := fun k =>
    ⋂ q ∈ {q : ℚ | (q : ℝ) ∈ J}, {g | 1 / ((k : ℝ) + 1) ≤ mvInf K₁₂ (X q g)} with hGdef
  have hGm : ∀ k, MeasurableSet (G k) := fun k =>
    MeasurableSet.biInter (Set.to_countable _) fun q _ =>
      measurableSet_le measurable_const ((measurable_mvInf hK).comp (mv_measurable_section hX.1 q))
  have hmemG : ∀ k g, g ∈ G k ↔ ∀ q : ℚ, (q : ℝ) ∈ J → 1 / ((k : ℝ) + 1) ≤ mvInf K₁₂ (X q g) := by
    intro k g
    simp only [hGdef, mem_iInter, mem_ofPred_eq]
  have hGmono : Monotone G := by
    intro k k' hkk' g hg
    rw [hmemG] at hg ⊢
    intro q hq
    refine le_trans ?_ (hg q hq)
    gcongr
  have hGae : ∀ᵐ g ∂(normLGFLaw d), g ∈ ⋃ k, G k := by
    filter_upwards [hEae, hpos] with g hgE hgpos
    have hm : ContinuousOn (fun ξ => mvInf K₁₂ (X ξ g)) J :=
      (mv_continuousOn_mvInf (hcont g hgE) hK).mono hJ
    obtain ⟨ξ₀, hξ₀, hmin⟩ := isCompact_Icc.exists_isMinOn hJne hm
    have hpos₀ : 0 < mvInf K₁₂ (X ξ₀ g) := (lt_mvInf_iff hK hKne _ 0).2 fun p hp => by
      have := hgpos ξ₀ (hJ hξ₀) p.1 p.2 (hKd p hp)
      rwa [Prod.mk.eta] at this
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hpos₀
    refine mem_iUnion.2 ⟨k, (hmemG k g).2 fun q hq => hk.le.trans ?_⟩
    exact hmin hq
  have hGone : Tendsto (fun k => normLGFLaw d (G k)) atTop (𝓝 1) := by
    have h1 := tendsto_measure_iUnion_atTop (μ := normLGFLaw d) hGmono
    have h2 : normLGFLaw d (⋃ k, G k) = 1 := by
      rw [← prob_compl_eq_zero_iff (MeasurableSet.iUnion hGm)]
      refine measure_eq_zero_iff_ae_notMem.2 ?_
      filter_upwards [hGae] with g hg
      exact not_not.2 hg
    rwa [h2] at h1
  -- the exponent `m = min_J ϕ`
  obtain ⟨ξφ, hξφ, hφmin⟩ := isCompact_Icc.exists_isMinOn hJne (phiXi_continuous hd2).continuousOn
  set m := phiXi d ξφ with hmdef
  have hmpos : 0 < m := by
    rw [hmdef, phiXi_of_pos (hJ hξφ).1]
    exact mul_pos (hJ hξφ).1 ((Real.sqrt_nonneg _).trans_lt (hJ hξφ).2)
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  set ε := Real.log 2 * m / (2 * c') with hεdef
  have hεpos : 0 < ε := by positivity
  set κ := Real.log 2 * m / 2 with hκdef
  have hκpos : 0 < κ := by positivity
  -- the events `Sm j` and `Fv k j`
  set Sm : ℕ → Set (DistRd d) := fun j => {g | |sphereAvg g ((2 : ℝ) ^ j) 0| ≤ ε * j} with hSm
  have hSmm : ∀ j, MeasurableSet (Sm j) := fun j =>
    measurableSet_le (continuous_abs.measurable.comp (measurable_sphereAvg_left _ _)) measurable_const
  set Fv : ℕ → ℕ → Set (DistRd d) := fun k j => dilationTwoPow d j ⁻¹' G k ∩ Sm j with hFv
  have hFvm : ∀ k j, MeasurableSet (Fv k j) := fun k j =>
    (measurable_dilationTwoPow j (hGm k)).inter (hSmm j)
  have hfreq : ∀ k, normLGFLaw d (G k) ≤
      normLGFLaw d (⋂ N : ℕ, ⋃ j : ℕ, ⋃ (_ : N ≤ j), Fv k j) := by
    intro k
    refine mv_le_measure_limsup (hFvm k) fun δ hδ => ?_
    have hcheb := mv_tendsto_prob_sphereAvg_large hd2 hεpos
    filter_upwards [(ENNReal.tendsto_nhds_zero.1 hcheb) δ (by exact_mod_cast hδ)] with j hj
    have hpre : normLGFLaw d (dilationTwoPow d j ⁻¹' G k) = normLGFLaw d (G k) := by
      rw [← Measure.map_apply (measurable_dilationTwoPow j) (hGm k), map_dilationTwoPow hd2 j]
    calc normLGFLaw d (G k) = normLGFLaw d (dilationTwoPow d j ⁻¹' G k) := hpre.symm
      _ ≤ normLGFLaw d (Fv k j ∪ {g | ε * j < |sphereAvg g ((2 : ℝ) ^ j) 0|}) := by
          refine measure_mono fun g hg => ?_
          by_cases hs : |sphereAvg g ((2 : ℝ) ^ j) 0| ≤ ε * j
          · exact Or.inl ⟨hg, hs⟩
          · exact Or.inr (not_le.1 hs)
      _ ≤ normLGFLaw d (Fv k j) + normLGFLaw d {g | ε * j < |sphereAvg g ((2 : ℝ) ^ j) 0|} :=
          measure_union_le _ _
      _ ≤ normLGFLaw d (Fv k j) + δ := by gcongr
  set Freq : Set (DistRd d) := ⋃ k : ℕ, ⋂ N : ℕ, ⋃ j : ℕ, ⋃ (_ : N ≤ j), Fv k j with hFreq
  have hFreqm : MeasurableSet Freq :=
    MeasurableSet.iUnion fun k => MeasurableSet.iInter fun N =>
      MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun _ => hFvm k j
  have hFreq1 : normLGFLaw d Freq = 1 := by
    refine le_antisymm prob_le_one (le_of_tendsto' hGone fun k => (hfreq k).trans (measure_mono ?_))
    exact subset_iUnion (fun k => ⋂ N : ℕ, ⋃ j : ℕ, ⋃ (_ : N ≤ j), Fv k j) k
  have hFreqae : ∀ᵐ g ∂(normLGFLaw d), g ∈ Freq := by
    rw [← prob_compl_eq_zero_iff hFreqm] at hFreq1
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hFreq1] with g hg
    exact not_not.1 hg
  -- the conclusion
  filter_upwards [hFreqae, hscale, hEae] with g hgF hgs hgE
  intro _ _ L
  obtain ⟨k, hk⟩ := mem_iUnion.1 hgF
  simp only [mem_iInter, mem_iUnion] at hk
  have hgrow : Tendsto (fun j : ℕ => Real.exp (j * κ)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_natCast_atTop_atTop.atTop_mul_const hκpos)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hgrow.eventually_gt_atTop (((k : ℝ) + 1) * (|L| + 1)))
  obtain ⟨j, hjN, hjF⟩ := hk N
  obtain ⟨hjG, hjS⟩ := hjF
  have hjG' : dilationTwoPow d j g ∈ G k := hjG
  have hjS' : |sphereAvg g ((2 : ℝ) ^ j) 0| ≤ ε * j := hjS
  set a : ℝ := (2 : ℝ) ^ j with hadef
  have ha : 0 < a := pow_pos two_pos j
  set Kab : Set (Rd d × Rd d) := sphere (0 : Rd d) a ×ˢ sphere (0 : Rd d) (2 * a) with hKab
  have hKabc : IsCompact Kab := (isCompact_sphere _ _).prod (isCompact_sphere _ _)
  have hKabne : Kab.Nonempty :=
    (NormedSpace.sphere_nonempty.2 ha.le).prod (NormedSpace.sphere_nonempty.2 (by positivity))
  set B : ℝ := Real.exp (j * κ) / ((k : ℝ) + 1) with hBdef
  -- the lower bound at rational parameters
  have hratq : ∀ q : ℚ, (q : ℝ) ∈ J → B ≤ mvInf Kab (X q g) := by
    intro q hq
    rw [le_mvInf_iff hKabc hKabne]
    rintro ⟨u', w'⟩ ⟨hu', hw'⟩
    rw [mem_sphere_zero_iff_norm] at hu' hw'
    set u : Rd d := a⁻¹ • u' with hudef
    set w : Rd d := a⁻¹ • w' with hwdef
    have hu : u ∈ sphere (0 : Rd d) 1 := by
      rw [mem_sphere_zero_iff_norm, hudef, norm_smul, hu', Real.norm_eq_abs, abs_of_pos (inv_pos.2 ha),
        inv_mul_cancel₀ ha.ne']
    have hw : w ∈ sphere (0 : Rd d) 2 := by
      rw [mem_sphere_zero_iff_norm, hwdef, norm_smul, hw', Real.norm_eq_abs, abs_of_pos (inv_pos.2 ha)]
      field_simp
    have hu'eq : u' = a • u := by rw [hudef, smul_smul, mul_inv_cancel₀ ha.ne', one_smul]
    have hw'eq : w' = a • w := by rw [hwdef, smul_smul, mul_inv_cancel₀ ha.ne', one_smul]
    have hscq := hgs j ⟨q, hJ hq⟩ u w
    show B ≤ X q g (u', w')
    rw [hu'eq, hw'eq, hscq]
    have hT : 1 / ((k : ℝ) + 1) ≤ X q (dilationTwoPow d j g) (u, w) :=
      ((hmemG k _).1 hjG' q hq).trans (mvInf_le hK _ ⟨hu, hw⟩)
    have hS' := mv_scaleS_lower (d := d) (q := q) (c' := c') (m := m) (hJ hq).1 hq.2 hc'pos
      (hφmin hq) j g hjS'
    have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    calc B = Real.exp (j * κ) * (1 / ((k : ℝ) + 1)) := by rw [hBdef, mul_one_div]
      _ ≤ scaleS d q 1 a 0 g * X q (dilationTwoPow d j g) (u, w) :=
          mul_le_mul hS' hT (by positivity) (scaleS_pos d q 1 ha 0 g).le
  -- extension to every parameter of the window
  refine ⟨a, 2 * a, ha, by linarith, fun ξ hξ u w hu hw => ?_⟩
  have hall := mv_mem_of_rat_Icc hcc ((mv_continuousOn_mvInf (hcont g hgE) hKabc).mono hJ)
    (C := Ici B) isClosed_Ici (fun q hq => hratq q hq) ξ hξ
  have h1 : mvInf Kab (X ξ g) ≤ X ξ g (u, w) :=
    mvInf_le hKabc _ ⟨mem_sphere_zero_iff_norm.2 hu, mem_sphere_zero_iff_norm.2 hw⟩
  have h2 : |L| + 1 < B := by
    rw [hBdef, lt_div_iff₀ (by positivity)]
    have := hN j hjN
    linarith
  have h3 : B ≤ mvInf Kab (X ξ g) := hall
  linarith [le_abs_self L]

end HigherDimLQGContinuity
