import HigherDimLFPP.Lower.Lemma52Aux

/-!
# Lemma 5.2: `lim inf_{δ↓0} w_{n,d,δ} ≥ 4e_{n,d} - 4` (source §5.1, (5.8))

Packet P-L3, target T1 (ruling H6; audit HA4, "Details for later use" D5, steps 1–5;
finding HA4-8).

`w_{n,d,δ} = E max_j (-δ^{-1/2}⟨H_{ρq,ρ}, ν_j - ν₀⟩)` (`LowerData.w`, (5.7)).  Proof (HA4 D5):
on mass-zero measures the all-scale pairing splits over the disjoint scale sets
`(0, ρq)`, `(ρq, ρ)`, `(ρ, ∞)` (`bandVecM_Ioi_split`), so with one white noise and
`max (a + r) ≥ max a - max |r|` (`gEM_gram_ge`),

`w ≥ E max_j A_j^δ - E max_j |fine_j| - E max_j |coarse_j|`,

where `A_j^δ` is the all-scale statistic of the moving graphs `μ_{δ g_{j,δ}}`:

1. **all scales** (`w_ge_aux`, `tendsto_gem_graphVec`): the polygon is coupled with the graph
   within `δ² E₀` (equal edges, `coupledWithin_polyM_graph`), so by Lemma 3.1
   (`transport_var_bound`) the polygon-to-graph error has `δ⁻¹ Var ≤ C δ E₀ → 0`; the graph
   statistics converge in covariance to `G_d(g_j)` by (3.8) with moving profiles
   (`tendsto_gEM_graph_scaleCov`, Chatterjee);
2. **fine scales**: Lemma 3.4(a) (`bandLemma34a`), `δ⁻¹ Var ≤ C L q`;
3. **coarse scales**: the polygon-to-graph part again by Lemma 3.1 and cutoff domination, the
   graph part by Lemma 3.4(b) (`emaxAbs_coarse_le`, energy `≤ E₀ + 1`);
4. **padding** (5.9) (`gem_le_gem_prof₀`);
5. **constants**: for `n ≥ N₀` each of the three `n`-dependent errors is `≤ 1`
   (`Hyp.fine_err_le`, `Hyp.pad_err_le`, `Hyp.coarse_err_le`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped RealInnerProductSpace ENNReal

namespace HigherDimLFPP.Lower

open LQGDimension (gaussianExpectedMax)

variable {d : ℕ} {κ : Rd d → ℝ}

/-- `‖δ^{-1/2} v‖ ≤ √(X/δ)` when `‖v‖² = Var ≤ X`. -/
theorem norm_inv_sqrt_smul_bandVecM_le {S : Set ℝ} {μ ν : Measure (Rd d)} {δ X : ℝ}
    (hδ : 0 < δ) (h : scaleCov κ S μ ν μ ν ≤ X) :
    ‖(Real.sqrt δ)⁻¹ • bandVecM κ S μ ν‖ ≤ Real.sqrt (X / δ) := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 (Real.sqrt_pos.2 hδ)),
    ← Real.sqrt_sq (norm_nonneg (bandVecM κ S μ ν)), ← Real.sqrt_inv,
    ← Real.sqrt_mul (inv_nonneg.2 hδ.le)]
  refine Real.sqrt_le_sqrt ?_
  rw [← scaleCov_self, inv_mul_eq_div]
  exact div_le_div_of_nonneg_right h hδ.le

namespace LowerData

variable (D : LowerData d)

/-- The all-scale vectors `-δ^{-1/2}⟨h, μ_{δ g_{j,δ}} - μ₀⟩` of the moving graphs. -/
def graphVec (κ : Rd d → ℝ) (δ : ℝ) (j : Fin (D.J + 1)) : WN d :=
  -((Real.sqrt δ)⁻¹ • bandVecM κ (Ioi 0) (graphMeasure d δ (D.prof δ j)) (graphMeasure d δ 0))

theorem K_ge_four (hn : 1 ≤ D.n) (hg : 1 ≤ D.g) : (4 : ℝ) ≤ D.K := by
  have h : (4 : ℕ) ≤ D.K := by
    show 4 ≤ 2 ^ (D.n + D.g)
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (D.n + D.g) := Nat.pow_le_pow_right (by norm_num) (by omega)
  exact_mod_cast h

theorem one_div_K_le_q (he : 0 ≤ D.e) (δ : ℝ) : 1 / (D.K : ℝ) ≤ D.q δ := by
  simp only [LowerData.q, qOf]
  have := D.K_cast_pos
  have hE : 0 ≤ δ ^ 2 * D.E₀ := mul_nonneg (sq_nonneg δ) (by simp only [LowerData.E₀]; linarith)
  exact div_le_div_of_nonneg_right (by linarith) this.le

theorem q_pos (he : 0 ≤ D.e) (δ : ℝ) : 0 < D.q δ :=
  lt_of_lt_of_le (div_pos one_pos D.K_cast_pos) (D.one_div_K_le_q he δ)

theorem q_le_two_div_K {δ : ℝ} (hδE : δ ^ 2 * D.E₀ ≤ 1) : D.q δ ≤ 2 / (D.K : ℝ) := by
  simp only [LowerData.q, qOf]
  exact div_le_div_of_nonneg_right (by linarith) D.K_cast_pos.le

theorem q_lt_one (hn : 1 ≤ D.n) (hg : 1 ≤ D.g) {δ : ℝ} (hδE : δ ^ 2 * D.E₀ ≤ 1) : D.q δ < 1 := by
  have h4 := D.K_ge_four hn hg
  calc D.q δ ≤ 2 / (D.K : ℝ) := D.q_le_two_div_K hδE
    _ ≤ 2 / 4 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) h4
    _ < 1 := by norm_num

end LowerData

/-- **The estimate of Lemma 5.2 at a fixed small `δ`** (HA4 D5, steps 1–3): with constants
depending only on `d` and `κ`,
`w ≥ 𝕄(A^δ) - (2√(A δ E₀) + √(B L q)) √(2 log 2(J+1)) - C_b √((E₀ + 1)/L)`, where `𝕄(A^δ)` is the
expected maximum of the all-scale statistics of the moving graphs `μ_{δ g_{j,δ}}`. -/
theorem w_ge_aux (hd : 2 ≤ d) (hκ : IsLFPPKernel κ) :
    ∃ A B Cb : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ 0 ≤ Cb ∧
    ∀ (D : LowerData d) (δ : ℝ) {M₀ c : ℝ}, 0 < δ → 0 ≤ D.e →
      (∀ j, D.f j ∈ Vg (Rd (d - 1)) D.n) → 1 ≤ D.n → 1 ≤ D.g →
      (∀ j, EqualEdgeData D.K δ (D.q δ) D.E₀ M₀ c (D.vert δ j)) → c * δ ≤ 1 / 2 →
      δ ^ 2 * D.E₀ ≤ 1 → (∀ j, energy (D.prof δ j) ≤ D.E₀ + 1) →
      gaussianExpectedMax (Finset.univ : Finset (Fin (D.J + 1)))
          (fun j k => ⟪D.graphVec κ δ j, D.graphVec κ δ k⟫) 0 -
        (2 * Real.sqrt (A * δ * D.E₀) + Real.sqrt (B * D.L * D.q δ)) *
          Real.sqrt (2 * Real.log (2 * ((D.J : ℝ) + 1))) -
        Cb * Real.sqrt ((D.E₀ + 1) / D.L) ≤ D.w κ δ := by
  obtain ⟨Ct, hCt0, hCt⟩ := transport_var_bound hκ 4
  obtain ⟨Ca, hCa⟩ := bandLemma34a hκ 4
  obtain ⟨Cb, hCb0, hCb⟩ := emaxAbs_coarse_le (by omega : 1 ≤ d) hκ
  refine ⟨Ct, max Ca 0, Cb, hCt0, le_max_right _ _, hCb0,
    fun D δ M₀ c hδ he hmem hn hg hE hcδ hδE henergy => ?_⟩
  have hd0 : 0 < d := by omega
  have hK : 0 < D.K := D.K_pos
  have hq0 : 0 < D.q δ := D.q_pos he δ
  have hqK : 1 / (D.K : ℝ) ≤ D.q δ := D.one_div_K_le_q he δ
  have hq1 : D.q δ < 1 := D.q_lt_one hn hg hδE
  have hρ : 0 < D.ρ δ := mul_pos hδ D.L_pos
  have hρq : 0 < D.ρ δ * D.q δ := mul_pos hρ hq0
  have hρqρ : D.ρ δ * D.q δ < D.ρ δ := mul_lt_of_lt_one_right hρ hq1
  have hE₀ : 0 ≤ D.E₀ := by simp only [LowerData.E₀]; linarith
  set ν₀ : Measure (Rd d) := Upper.segMeasure 0 (e₁ d) with hν₀
  have hν₀g : graphMeasure d δ 0 = ν₀ := graphMeasure_zero δ
  set c' : ℝ := (Real.sqrt δ)⁻¹ with hc'
  set μ : Fin (D.J + 1) → Measure (Rd d) := fun j => graphMeasure d δ (D.prof δ j) with hμ
  -- probability, growth and couplings
  have hpν : ∀ j, IsProbabilityMeasure (D.ν δ j) := fun j => isProbabilityMeasure_polyM hK _
  have hgν : ∀ j, GrowthBound (D.ν δ j) 4 1 := fun j =>
    growthBound_polyM hd0 hK hqK fun i hi => half_le_horiz_edge hd0 (hE j) hq0 hcδ hi
  have hprofV : ∀ j, D.prof δ j ∈ Vg (Rd (d - 1)) (D.n + D.g) := fun j =>
    padProf_mem_Vg hg (hmem j) D.v _
  have hmeas : ∀ j, Measurable (D.prof δ j) := fun j =>
    (Var.Vg_continuous (hprofV j)).measurable
  have hgμ : ∀ j, GrowthBound (μ j) 4 1 := fun j =>
    (graphMeasure_growthBound hd0 (hmeas j)).mono_const one_pos (by norm_num)
  have hgν₀ : GrowthBound ν₀ 4 1 := by
    rw [← hν₀g]
    exact (graphMeasure_growthBound hd0 measurable_const).mono_const one_pos (by norm_num)
  have hcpl : ∀ j, CoupledWithin (D.ν δ j) (μ j) (δ ^ 2 * D.E₀) := fun j =>
    coupledWithin_polyM_graph hd0 hg (hmem j) D.v (hE j)
  -- the polygon-to-graph errors (Lemma 3.1)
  have htr : ∀ j, IsPairable κ (Ioi 0) (D.ν δ j) (μ j) ∧
      scaleCov κ (Ioi 0) (D.ν δ j) (μ j) (D.ν δ j) (μ j) ≤ Ct * (δ ^ 2 * D.E₀) / 1 := fun j =>
    hCt (Ioi 0) measurableSet_Ioi subset_rfl (D.ν δ j) (μ j) 1 (δ ^ 2 * D.E₀) one_pos
      (by positivity) (hgν j) (hgμ j) (hcpl j)
  -- graphs to the reference segment
  have hpair_μν₀ : ∀ j, IsPairable κ (Ioi 0) (μ j) ν₀ := by
    intro j
    obtain ⟨Mg, hMg⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (Var.Vg_continuous (hprofV j)).continuousOn
    have hMg0 : 0 ≤ Mg := (norm_nonneg _).trans (hMg 0 ⟨le_rfl, zero_le_one⟩)
    have hc := coupledWithin_graphMeasure (d := d) hδ.le (hmeas j) (g := 0) measurable_const
      (M := Mg) fun x hx => by rw [Pi.zero_apply, sub_zero]; exact hMg x hx
    rw [hν₀g] at hc
    exact (hCt (Ioi 0) measurableSet_Ioi subset_rfl (μ j) ν₀ 1 (δ * Mg) one_pos
      (mul_nonneg hδ.le hMg0) (hgμ j) hgν₀ hc).1
  have hpair_νν₀ : ∀ j, IsPairable κ (Ioi 0) (D.ν δ j) ν₀ := fun j =>
    isPairable_trans (htr j).1 (hpair_μν₀ j)
  -- the four error families
  set t1 : Fin (D.J + 1) → WN d := fun j => -(c' • bandVecM κ (Ioi 0) (D.ν δ j) (μ j)) with ht1
  set t2 : Fin (D.J + 1) → WN d := fun j => c' • bandVecM κ (Ioo 0 (D.ρ δ * D.q δ)) (D.ν δ j) ν₀
    with ht2
  set t3 : Fin (D.J + 1) → WN d := fun j => c' • bandVecM κ (Ioi (D.ρ δ)) (D.ν δ j) (μ j)
    with ht3
  set t4 : Fin (D.J + 1) → WN d := fun j => c' • bandVecM κ (Ioi (D.ρ δ)) (μ j) ν₀ with ht4
  have hdec : ∀ j, D.selVec κ δ j - D.graphVec κ δ j = ((t1 j + t2 j) + t3 j) + t4 j := by
    intro j
    have h1 := bandVecM_Ioi_split hρq hρqρ (hpair_νν₀ j)
    have h2 := bandVecM_trans (htr j).1 (hpair_μν₀ j)
    have h3 := bandVecM_trans ((htr j).1.mono_set measurableSet_Ioi (Ioi_subset_Ioi hρ.le))
      ((hpair_μν₀ j).mono_set measurableSet_Ioi (Ioi_subset_Ioi hρ.le))
    simp only [LowerData.selVec, LowerData.graphVec, ht1, ht2, ht3, ht4, LowerData.band]
    rw [hν₀g]
    rw [h2] at h1
    have hb : bandVecM κ (Ioo (D.ρ δ * D.q δ) (D.ρ δ)) (D.ν δ j) ν₀ =
        bandVecM κ (Ioi 0) (D.ν δ j) (μ j) + bandVecM κ (Ioi 0) (μ j) ν₀ -
          bandVecM κ (Ioo 0 (D.ρ δ * D.q δ)) (D.ν δ j) ν₀ -
          bandVecM κ (Ioi (D.ρ δ)) (D.ν δ j) ν₀ := by
      rw [h1]
      abel
    rw [hb, h3]
    simp only [smul_sub, smul_add]
    abel
  -- the expected maximum
  have hmain := gEM_gram_ge (D.selVec κ δ) (D.graphVec κ δ)
  have hS₂ : Real.sqrt (2 * Real.log (2 * (Fintype.card (Fin (D.J + 1)) : ℝ))) =
      Real.sqrt (2 * Real.log (2 * ((D.J : ℝ) + 1))) := by
    rw [Fintype.card_fin]
    push_cast
    ring_nf
  have he1 : emaxAbs t1 ≤ Real.sqrt (Ct * δ * D.E₀) *
      Real.sqrt (2 * Real.log (2 * ((D.J : ℝ) + 1))) := by
    rw [← hS₂]
    have h := emaxAbs_le (fun j => c' • bandVecM κ (Ioi 0) (D.ν δ j) (μ j))
      (Real.sqrt_nonneg (Ct * δ * D.E₀)) fun j => by
        refine (norm_inv_sqrt_smul_bandVecM_le hδ (htr j).2).trans (le_of_eq ?_)
        congr 1
        field_simp
    rwa [← emaxAbs_neg] at h
  have he2 : emaxAbs t2 ≤ Real.sqrt (max Ca 0 * D.L * D.q δ) *
      Real.sqrt (2 * Real.log (2 * ((D.J : ℝ) + 1))) := by
    rw [← hS₂]
    refine emaxAbs_le t2 (Real.sqrt_nonneg _) fun j => ?_
    have := hpν j
    obtain ⟨-, -, -, hv⟩ := hCa (D.ρ δ * D.q δ) hρq (D.ν δ j) ν₀ (hgν j) hgν₀
    refine (norm_inv_sqrt_smul_bandVecM_le hδ
      (hv.trans (mul_le_mul_of_nonneg_right (le_max_left Ca 0) hρq.le))).trans (le_of_eq ?_)
    congr 1
    simp only [LowerData.ρ]
    field_simp
  have he3 : emaxAbs t3 ≤ Real.sqrt (Ct * δ * D.E₀) *
      Real.sqrt (2 * Real.log (2 * ((D.J : ℝ) + 1))) := by
    rw [← hS₂]
    refine emaxAbs_le t3 (Real.sqrt_nonneg _) fun j => ?_
    refine (norm_inv_sqrt_smul_bandVecM_le hδ ((scaleCov_self_le_of_subset measurableSet_Ioi
      (Ioi_subset_Ioi hρ.le) (htr j).1).trans (htr j).2)).trans (le_of_eq ?_)
    congr 1
    field_simp
  have he4 : emaxAbs t4 ≤ Cb * Real.sqrt ((D.E₀ + 1) / D.L) := by
    have h := hCb δ D.L hδ D.L_pos (D.E₀ + 1) (D.n + D.g) (D.prof δ) fun j =>
      ⟨hprofV j, henergy j⟩
    rw [hν₀g] at h
    exact h
  have hsum : emaxAbs (fun j => D.selVec κ δ j - D.graphVec κ δ j) ≤
      emaxAbs t1 + emaxAbs t2 + emaxAbs t3 + emaxAbs t4 := by
    have e : (fun j => D.selVec κ δ j - D.graphVec κ δ j) =
        fun j => ((t1 j + t2 j) + t3 j) + t4 j := funext hdec
    rw [e]
    refine (emaxAbs_add _ _).trans (add_le_add ?_ le_rfl)
    refine (emaxAbs_add _ _).trans (add_le_add ?_ le_rfl)
    exact emaxAbs_add _ _
  have hw : D.w κ δ = gaussianExpectedMax (Finset.univ : Finset (Fin (D.J + 1)))
      (fun j k => ⟪D.selVec κ δ j, D.selVec κ δ k⟫) 0 := rfl
  rw [hw]
  have hS0 : 0 ≤ Real.sqrt (2 * Real.log (2 * ((D.J : ℝ) + 1))) := Real.sqrt_nonneg _
  nlinarith [hmain, hsum, he1, he2, he3, he4]

/-! ## The all-scale limit (HA4 D5, step 1) -/

namespace LowerData

variable (D : LowerData d)

theorem prof_sub_prof₀ (hv : ‖D.v‖ = 1) (δ : ℝ) (j : Fin (D.J + 1)) (x : ℝ) :
    ‖D.prof δ j x - D.prof₀ j x‖ ≤ |D.amp δ j - aLim D.e (D.f j)| / D.K := by
  simp only [prof, prof₀, padProf, add_sub_add_left_eq_sub, ← sub_smul, ← sub_mul]
  rw [norm_smul, hv, mul_one, Real.norm_eq_abs, abs_mul]
  calc |D.amp δ j - aLim D.e (D.f j)| * |psiK D.K x|
      ≤ |D.amp δ j - aLim D.e (D.f j)| * (1 / D.K) :=
        mul_le_mul_of_nonneg_left (abs_psiK_le _ _) (abs_nonneg _)
    _ = |D.amp δ j - aLim D.e (D.f j)| / D.K := by rw [mul_one_div]

/-- **The all-scale limit** (HA4 D5, step 1, graph part): if `a_{j,δ} → a_j`, the expected maximum
of the all-scale statistics of the moving graphs converges to `E max_j G_d(g_j)` ((3.8) with
moving profiles and Chatterjee's bound, P-F3a's `tendsto_gEM_graph_scaleCov`). -/
theorem tendsto_gem_graphVec (hd : 0 < d) (hκ : IsLFPPKernel κ)
    (hmem : ∀ j, D.f j ∈ Vg (Rd (d - 1)) D.n) (hg : 1 ≤ D.g) (hv : ‖D.v‖ = 1)
    (hamp : ∀ j, Tendsto (fun δ => D.amp δ j) (𝓝[>] 0) (𝓝 (aLim D.e (D.f j)))) :
    Tendsto (fun δ => gaussianExpectedMax (Finset.univ : Finset (Fin (D.J + 1)))
        (fun j k => ⟪D.graphVec κ δ j, D.graphVec κ δ k⟫) 0) (𝓝[>] 0)
      (𝓝 (gaussianExpectedMax (Finset.univ : Finset (Fin (D.J + 1)))
        (fun j k => gCov (D.prof₀ j) (D.prof₀ k)) 0)) := by
  have hK : (0 : ℝ) < D.K := D.K_cast_pos
  have hcont : ∀ j, Continuous (D.prof₀ j) := fun j =>
    Var.Vg_continuous (padProf_mem_Vg hg (hmem j) D.v _)
  have hcontδ : ∀ δ j, Continuous (D.prof δ j) := fun δ j =>
    Var.Vg_continuous (padProf_mem_Vg hg (hmem j) D.v _)
  have hunif : ∀ j, TendstoUniformlyOn (fun δ => D.prof δ j) (D.prof₀ j) (𝓝[>] 0) (Icc 0 1) := by
    intro j
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have h := (hamp j).sub_const (aLim D.e (D.f j))
    rw [sub_self] at h
    have h2 : ∀ᶠ δ in 𝓝[>] 0, |D.amp δ j - aLim D.e (D.f j)| < ε * D.K := by
      have := h.abs
      rw [abs_zero] at this
      exact this.eventually (gt_mem_nhds (mul_pos hε hK))
    filter_upwards [h2] with δ hδ x _
    rw [dist_comm, dist_eq_norm]
    refine lt_of_le_of_lt (D.prof_sub_prof₀ hv δ j x) ?_
    rwa [div_lt_iff₀ hK]
  have h := tendsto_gEM_graph_scaleCov hd hκ (Finset.univ : Finset (Fin (D.J + 1))) D.prof₀
    (fun δ j => D.prof δ j) 0 (fun _ => 0) (fun j _ => hcont j)
    (Eventually.of_forall fun δ j _ => hcontδ δ j) (fun j _ => hunif j)
    (fun j _ => tendsto_const_nhds)
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  have hδ' : (0 : ℝ) < δ := hδ
  refine LQGDimension.gaussianExpectedMax_congr _ _ fun j _ k _ => ?_
  simp only [graphVec, inner_neg_neg, real_inner_smul_left, real_inner_smul_right, scaleCov]
  rw [← mul_assoc, ← mul_inv, Real.mul_self_sqrt hδ'.le]

end LowerData

/-! ## The `n`-dependent errors (HA4 §2.2(e)) -/

theorem pow_div_pow_le_inv {x : ℝ} (hx : 1 ≤ x) {a b : ℕ} (hab : a + 1 ≤ b) :
    x ^ a / x ^ b ≤ 1 / x := by
  have hx0 : 0 < x := by linarith
  rw [div_le_div_iff₀ (pow_pos hx0 b) hx0, one_mul]
  calc x ^ a * x = x ^ (a + 1) := by ring
    _ ≤ x ^ b := pow_le_pow_right₀ hx hab

theorem sqrt_le_one_of_le {X : ℝ} (h : X ≤ 1) : Real.sqrt X ≤ 1 :=
  (Real.sqrt_le_sqrt h).trans_eq Real.sqrt_one

namespace LowerData

variable {D : LowerData d} {C : ℝ}

theorem Hyp.K_ge (hD : D.Hyp C) : ((D.n : ℝ) + 2) ^ 20 * 2 ^ D.n ≤ D.K := by
  have e : ((D.K : ℕ) : ℝ) = 2 ^ D.n * 2 ^ D.g := by
    rw [LowerData.K, pow_add]
    push_cast
    ring
  rw [e, mul_comm]
  exact mul_le_mul_of_nonneg_left hD.pad (by positivity)

theorem Hyp.log_le (hD : D.Hyp C) :
    2 * Real.log (2 * ((D.J : ℝ) + 1)) ≤ 2 * C * D.n * 2 ^ D.n := by
  have := hD.log_card
  linarith

theorem log_two_mul_nonneg (J : ℕ) : 0 ≤ 2 * Real.log (2 * ((J : ℝ) + 1)) := by
  have : (1 : ℝ) ≤ 2 * ((J : ℝ) + 1) := by
    have := Nat.cast_nonneg (α := ℝ) J
    linarith
  have := Real.log_nonneg this
  linarith

/-- The fine-scale error `√(B L q₀) √(2 log 2(J+1))` (`q₀ = 2/K`) is `≤ 1` once `n + 2 ≥ 4BC`. -/
theorem Hyp.fine_err_le (hD : D.Hyp C) {B : ℝ} (hB : 0 ≤ B) (hx : 4 * B * C ≤ (D.n : ℝ) + 2) :
    Real.sqrt (B * D.L * (2 / D.K)) * Real.sqrt (2 * Real.log (2 * ((D.J : ℝ) + 1))) ≤ 1 := by
  have hC := hD.C_nonneg
  set x : ℝ := (D.n : ℝ) + 2 with hxdef
  have hx1 : 1 ≤ x := by rw [hxdef]; have := Nat.cast_nonneg (α := ℝ) D.n; linarith
  have hx0 : 0 < x := by linarith
  have hnx : (D.n : ℝ) ≤ x := by rw [hxdef]; linarith
  set P : ℝ := 2 ^ D.n with hP
  have hP0 : 0 < P := by positivity
  rw [← Real.sqrt_mul (by have := D.K_cast_pos; positivity)]
  refine sqrt_le_one_of_le ?_
  have hK := hD.K_ge
  have hlog := hD.log_le
  have hlog0 := log_two_mul_nonneg D.J
  calc B * D.L * (2 / D.K) * (2 * Real.log (2 * ((D.J : ℝ) + 1)))
      ≤ B * x ^ 4 * (2 / (x ^ 20 * P)) * (2 * C * D.n * P) := by
        have h2K : 2 / (D.K : ℝ) ≤ 2 / (x ^ 20 * P) :=
          div_le_div_of_nonneg_left (by norm_num) (by positivity) hK
        gcongr
    _ = 4 * B * C * (D.n * x ^ 4 / x ^ 20) := by
        field_simp
        ring
    _ ≤ 4 * B * C * (x ^ 5 / x ^ 20) := by
        gcongr
        calc (D.n : ℝ) * x ^ 4 ≤ x * x ^ 4 := by gcongr
          _ = x ^ 5 := by ring
    _ ≤ 4 * B * C * (1 / x) :=
        mul_le_mul_of_nonneg_left (pow_div_pow_le_inv hx1 (by norm_num)) (by positivity)
    _ ≤ 1 := by
        rw [mul_one_div, div_le_one hx0]
        exact hx

/-- The padding error `√(2π√(2E₀)/K) √(2 log 2(J+1))` is `≤ 1` once `n + 2 ≥ 4πC(2C + 3)`. -/
theorem Hyp.pad_err_le (hD : D.Hyp C) (hx : 4 * Real.pi * C * (2 * C + 3) ≤ (D.n : ℝ) + 2) :
    Real.sqrt (2 * Real.pi * (√(2 * (D.e + 1)) / D.K)) *
      Real.sqrt (2 * Real.log (2 * ((D.J : ℝ) + 1))) ≤ 1 := by
  have hC := hD.C_nonneg
  have he := hD.e_nonneg
  set x : ℝ := (D.n : ℝ) + 2 with hxdef
  have hx1 : 1 ≤ x := by rw [hxdef]; have := Nat.cast_nonneg (α := ℝ) D.n; linarith
  have hx0 : 0 < x := by linarith
  have hnx : (D.n : ℝ) ≤ x := by rw [hxdef]; linarith
  set P : ℝ := 2 ^ D.n with hP
  have hP0 : 0 < P := by positivity
  have hsq : √(2 * (D.e + 1)) ≤ (2 * C + 3) * x := by
    rw [Real.sqrt_le_left]
    · have h1 : 2 * (D.e + 1) ≤ 2 * C * D.n + 2 := by nlinarith [hD.e_le]
      have h2 : 2 * C * D.n + 2 ≤ (2 * C + 3) * x - 1 := by nlinarith
      nlinarith
    · positivity
  rw [← Real.sqrt_mul (by have := D.K_cast_pos; positivity)]
  refine sqrt_le_one_of_le ?_
  have hK := hD.K_ge
  have hlog := hD.log_le
  have hlog0 := log_two_mul_nonneg D.J
  calc 2 * Real.pi * (√(2 * (D.e + 1)) / D.K) * (2 * Real.log (2 * ((D.J : ℝ) + 1)))
      ≤ 2 * Real.pi * ((2 * C + 3) * x / (x ^ 20 * P)) * (2 * C * D.n * P) := by
        gcongr
    _ = 4 * Real.pi * C * (2 * C + 3) * (D.n * x / x ^ 20) := by
        field_simp
        ring
    _ ≤ 4 * Real.pi * C * (2 * C + 3) * (x ^ 2 / x ^ 20) := by
        gcongr
        calc (D.n : ℝ) * x ≤ x * x := by gcongr
          _ = x ^ 2 := by ring
    _ ≤ 4 * Real.pi * C * (2 * C + 3) * (1 / x) :=
        mul_le_mul_of_nonneg_left (pow_div_pow_le_inv hx1 (by norm_num)) (by positivity)
    _ ≤ 1 := by
        rw [mul_one_div, div_le_one hx0]
        exact hx

/-- The coarse-scale error `C_b √((E₀ + 1)/L)` is `≤ 1` once `n + 2 ≥ C_b²(C + 2)`. -/
theorem Hyp.coarse_err_le (hD : D.Hyp C) {Cb : ℝ} (hCb : 0 ≤ Cb)
    (hx : Cb ^ 2 * (C + 2) ≤ (D.n : ℝ) + 2) : Cb * Real.sqrt ((D.E₀ + 1) / D.L) ≤ 1 := by
  have hC := hD.C_nonneg
  have he := hD.e_nonneg
  set x : ℝ := (D.n : ℝ) + 2 with hxdef
  have hx1 : 1 ≤ x := by rw [hxdef]; have := Nat.cast_nonneg (α := ℝ) D.n; linarith
  have hx0 : 0 < x := by linarith
  have hnx : (D.n : ℝ) ≤ x := by rw [hxdef]; linarith
  rw [← Real.sqrt_sq hCb, ← Real.sqrt_mul (sq_nonneg Cb)]
  refine sqrt_le_one_of_le ?_
  have hL : D.L = x ^ 4 := rfl
  rw [hL]
  calc Cb ^ 2 * ((D.E₀ + 1) / x ^ 4) ≤ Cb ^ 2 * ((C + 2) * x / x ^ 4) := by
        gcongr
        simp only [LowerData.E₀]
        nlinarith [hD.e_le]
    _ = Cb ^ 2 * (C + 2) * (x / x ^ 4) := by ring
    _ ≤ Cb ^ 2 * (C + 2) * (1 / x) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have h := pow_div_pow_le_inv hx1 (a := 1) (b := 4) (by norm_num)
        rwa [pow_one] at h
    _ ≤ 1 := by
        rw [mul_one_div, div_le_one hx0]
        exact hx

/-- The size condition `√(2(e + 1)) + 1 ≤ K` of Lemma 5.1, once `n + 2 ≥ 2C + 4`. -/
theorem Hyp.sqrt_le_K (hD : D.Hyp C) (hx : 2 * C + 4 ≤ (D.n : ℝ) + 2) :
    √(2 * (D.e + 1)) + 1 ≤ ((2 ^ (D.n + D.g) : ℕ) : ℝ) := by
  have hC := hD.C_nonneg
  have he := hD.e_nonneg
  set x : ℝ := (D.n : ℝ) + 2 with hxdef
  have hx1 : 1 ≤ x := by rw [hxdef]; have := Nat.cast_nonneg (α := ℝ) D.n; linarith
  have hnx : (D.n : ℝ) ≤ x := by rw [hxdef]; linarith
  have hsq : √(2 * (D.e + 1)) ≤ 2 * C * x + 3 := by
    rw [Real.sqrt_le_left]
    · nlinarith [hD.e_le]
    · positivity
  have hK := hD.K_ge
  have hP : (1 : ℝ) ≤ 2 ^ D.n := one_le_pow₀ (by norm_num)
  have h20 : x ^ 2 ≤ x ^ 20 := pow_le_pow_right₀ hx1 (by norm_num)
  calc √(2 * (D.e + 1)) + 1 ≤ 2 * C * x + 4 := by linarith
    _ ≤ x * x := by nlinarith
    _ = x ^ 2 := by ring
    _ ≤ x ^ 20 := h20
    _ ≤ x ^ 20 * 2 ^ D.n := le_mul_of_one_le_right (by positivity) hP
    _ ≤ D.K := hK

end LowerData

theorem tendsto_zero_of_continuous {f : ℝ → ℝ} (hf : Continuous f) (h0 : f 0 = 0) :
    Tendsto f (𝓝[>] 0) (𝓝 0) := by
  have h := hf.tendsto 0
  rw [h0] at h
  exact tendsto_nhdsWithin_of_tendsto_nhds h

/-- **Lemma 5.2** (source (5.8); HA4 D5): for every `C` there is `N₀` such that for all data
`D` with the standing hypotheses (the Lemma 2.2 family with constant `C`, `e ≤ Cn`, padding
`2^g ≥ (n+2)^{20}`, `‖v‖ = 1`) and `n ≥ N₀`,
`lim inf_{δ ↓ 0} w_{n,d,δ} ≥ 4 e - 4`, i.e. for every `θ > 0`, eventually
`w_{n,d,δ} ≥ 4e - 4 - θ`. -/
theorem lemma52 (hd : 2 ≤ d) (hκ : IsLFPPKernel κ) (C : ℝ) :
    ∃ N₀ : ℕ, ∀ D : LowerData d, D.Hyp C → N₀ ≤ D.n →
      ∀ θ > 0, ∀ᶠ δ in 𝓝[>] 0, 4 * D.e - 4 - θ ≤ D.w κ δ := by
  obtain ⟨A, B, Cb, hA, hB, hCb, haux⟩ := w_ge_aux hd hκ
  refine ⟨⌈4 * Real.pi * C * (2 * C + 3) + 4 * B * C + Cb ^ 2 * (C + 2) + 2 * C + 4⌉₊,
    fun D hD hN θ hθ => ?_⟩
  have hd0 : 0 < d := by omega
  have hC := hD.C_nonneg
  have he := hD.e_nonneg
  have hx : 4 * Real.pi * C * (2 * C + 3) + 4 * B * C + Cb ^ 2 * (C + 2) + 2 * C + 4 ≤
      (D.n : ℝ) + 2 := by
    have h1 := Nat.le_ceil (4 * Real.pi * C * (2 * C + 3) + 4 * B * C + Cb ^ 2 * (C + 2) +
      2 * C + 4)
    have h2 : (⌈4 * Real.pi * C * (2 * C + 3) + 4 * B * C + Cb ^ 2 * (C + 2) + 2 * C + 4⌉₊ : ℝ)
        ≤ D.n := by exact_mod_cast hN
    linarith
  have t1 : 0 ≤ 4 * Real.pi * C * (2 * C + 3) := by positivity
  have t2 : 0 ≤ 4 * B * C := by positivity
  have t3 : 0 ≤ Cb ^ 2 * (C + 2) := by positivity
  have hK51 := hD.sqrt_le_K (by linarith)
  have hpad := hD.pad_err_le (by linarith)
  have hfine := hD.fine_err_le hB (by linarith)
  have hcoarse := hD.coarse_err_le hCb (by linarith)
  -- the amplitudes and the polygons (Lemma 5.1)
  have hspec := fun j => ampl_spec hd0 hD.one_le_g (hD.mem j) (hD.energy_le j) hD.v_norm hK51
  choose hamp hδ₁ using hspec
  choose δ₁ hδ₁pos hδ₁spec using hδ₁
  have hamp' : ∀ j, Tendsto (fun δ => D.amp δ j) (𝓝[>] 0) (𝓝 (aLim D.e (D.f j))) := hamp
  -- the limit of the all-scale term, and the padding (5.9)
  have hlim := D.tendsto_gem_graphVec hd0 hκ hD.mem hD.one_le_g hD.v_norm hamp'
  set G := gaussianExpectedMax (Finset.univ : Finset (Fin (D.J + 1)))
    (fun j k => gCov (D.prof₀ j) (D.prof₀ k)) 0 with hG
  have hGe : 4 * D.e - 2 ≤ G := by
    have h1 := hD.gem
    have h2 := D.gem_le_gem_prof₀ hD.v_norm hD.mem hD.one_le_g
    linarith
  set S₂ := Real.sqrt (2 * Real.log (2 * ((D.J : ℝ) + 1))) with hS₂
  -- eventual smallness
  have ev1 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ j, δ ∈ Ioo 0 (δ₁ j) :=
    eventually_all.2 fun j => Ioo_mem_nhdsGT (hδ₁pos j)
  have ev2 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), √2 * incrConst D.n D.e * δ < 1 / 2 :=
    (tendsto_zero_of_continuous (continuous_const.mul continuous_id) (by simp)).eventually
      (gt_mem_nhds (by norm_num))
  have ev3 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ ^ 2 * D.E₀ < 1 :=
    (tendsto_zero_of_continuous ((continuous_pow 2).mul continuous_const) (by simp)).eventually
      (gt_mem_nhds (by norm_num))
  have ev4 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ j, energy (D.prof δ j) < D.E₀ + 1 := by
    refine eventually_all.2 fun j => ?_
    have hlimE : Tendsto (fun δ => energy (D.f j) + D.amp δ j ^ 2 / 2) (𝓝[>] 0)
        (𝓝 (energy (D.f j) + aLim D.e (D.f j) ^ 2 / 2)) :=
      tendsto_const_nhds.add (((hamp' j).pow 2).div_const 2)
    have hE₀ : energy (D.f j) + aLim D.e (D.f j) ^ 2 / 2 = D.E₀ := by
      rw [aLim_sq (hD.energy_le j)]
      ring
    rw [hE₀] at hlimE
    filter_upwards [hlimE.eventually (gt_mem_nhds (lt_add_one D.E₀))] with δ hδ
    rw [LowerData.prof, energy_padProf hD.one_le_g (hD.mem j) hD.v_norm]
    exact hδ
  have ev5 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), G - θ / 2 < gaussianExpectedMax
      (Finset.univ : Finset (Fin (D.J + 1))) (fun j k => ⟪D.graphVec κ δ j, D.graphVec κ δ k⟫) 0 :=
    hlim.eventually (lt_mem_nhds (by linarith))
  have ev6 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 2 * Real.sqrt (A * δ * D.E₀) * S₂ < θ / 2 :=
    (tendsto_zero_of_continuous (((continuous_const.mul ((continuous_const.mul continuous_id).mul
      continuous_const).sqrt)).mul continuous_const) (by simp)).eventually
      (gt_mem_nhds (by linarith))
  filter_upwards [ev1, ev2, ev3, ev4, ev5, ev6, self_mem_nhdsWithin] with δ h1 h2 h3 h4 h5 h6 hδ
  have hδ' : (0 : ℝ) < δ := hδ
  have hE : ∀ j, EqualEdgeData D.K δ (D.q δ) D.E₀ (√D.e + 1) (√2 * incrConst D.n D.e)
      (D.vert δ j) := fun j => ((hδ₁spec j) δ (h1 j)).2
  have hmain := haux D δ hδ' he hD.mem hD.one_le_n hD.one_le_g hE h2.le h3.le
    fun j => (h4 j).le
  have hq2 : D.q δ ≤ 2 / D.K := D.q_le_two_div_K h3.le
  have hsqrt : Real.sqrt (B * D.L * D.q δ) ≤ Real.sqrt (B * D.L * (2 / D.K)) :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hq2 (mul_nonneg hB D.L_pos.le))
  have hS0 : 0 ≤ S₂ := Real.sqrt_nonneg _
  have hfine' : Real.sqrt (B * D.L * D.q δ) * S₂ ≤ 1 :=
    (mul_le_mul_of_nonneg_right hsqrt hS0).trans hfine
  nlinarith [hmain, hfine', hcoarse, hpad, h5, h6, hGe]

end HigherDimLFPP.Lower
