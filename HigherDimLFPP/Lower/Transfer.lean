import HigherDimLFPP.Lower.Recursion

/-!
# The unused bands and the transfer to the white-noise field (lower comparison, D8)

Packet P-L2a, target T4 (ruling H6; audit HA4, "Details for later use" D8, findings HA4-1 and
HA4-13).  Fix a depth `r` and a cutoff `ε` with `ρ q^{r+1} ≤ ε ≤ ρ q^r`, `ρ ≤ 1`.

* **Unused bands** (`Good.integral_RCe`, `Good.integral_RCe_eq`, `Good.integral_RCe_le`).  The
  cutoff field `Y(ε, 1, ·)` splits into the bands `(ε, ρq^r]`, `(ρq^r, ρ]` (the cost band of the
  construction) and `(ρ, 1]`.  The first and the last are disjoint from every band read by
  `dec_r` and from the cost band, hence independent of them, and

  `E RiemannCost_N(poly(dec_r Y), Y(ε,1,·)) = Σ_p M_r(p) · E e^{ζY(ε,ρq^r,p)} · E e^{ζY(ρ,1,p)}
     = (ρq^r/ε)^{ζ²/2} ρ^{-ζ²/2} m_r ≤ (ρq)^{-ζ²/2} m_r`.

  The law is `gLawD κ (QsE r ε)`, where `QsE r ε` adds the triples `(ε,1,p)`, `(ε,ρq^r,p)`,
  `(ρ,1,p)` (`p ∈ S r`) to `Qs r`.
* **Transfer** (`Good.measure_allCostGt_eq`, `Good.measure_allCostGt_le`).  For every white
  noise `W` (any probability space) and every version `H` of the band field `H_{ε,1}`
  (`IsBandVersion`), the probability that **every** depth-`r` polygon has Riemann cost `> t'`
  under `H` equals the same probability for `Y(ε,1,·)` in the finite model (the finitely many
  Riemann point values have the same centered Gaussian law, `measure_gLawD_eq_whiteNoise`), and
  hence (Markov, applied to the selected polygon `poly(dec_r Y)`) it is at most
  `(ρq)^{-ζ²/2} m_r / t'`.  The family of depth-`r` polygons `{polyOf r T : T ∈ DT J K r}` does
  not depend on `N`.

2D source: `LQGDimension/LFPP/LowerAssemblyAux2.lean` (`prob_all_cost_gt_le`,
`measure_preimage_eq_stdGaussian`, `stdGaussian_ge_le_integral_div`), simplified: the field is
the band field itself (no coupling to circle averages, no oscillation event), and the unused
bands are handled by independence.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace

namespace HigherDimLFPP.Lower

variable {d : ℕ}

namespace LParams

variable (P : LParams d) (κ : Rd d → ℝ)

/-! ## The extended set of triples and the cutoff cost -/

/-- `Qs r` together with the cutoff triples `(ε, 1, p)` and the unused bands `(ε, ρq^r, p)`,
`(ρ, 1, p)` at the Riemann points `p ∈ S r`. -/
def QsE (r : ℕ) (ε : ℝ) : Finset (TriD d) :=
  P.Qs r ∪ (P.S r).image (fun p => (ε, 1, p)) ∪ (P.S r).image (fun p => (ε, P.ρ * P.q ^ r, p)) ∪
    (P.S r).image (fun p => (P.ρ, 1, p))

/-- The Riemann cost of the selected depth-`r` polygon under the cutoff field `Y(ε, 1, ·)`. -/
def RCe (r : ℕ) (ε : ℝ) (Y : TriD d → ℝ) : ℝ :=
  riemannCost P.ζ P.N (P.polyOf r (P.dec r Y)) fun z => Y (ε, 1, z)

/-- The occupation of `p` under the cutoff field. -/
def occE (r : ℕ) (ε : ℝ) (p : Rd d) (Y : TriD d → ℝ) : ℝ :=
  rcW P.N (P.polyOf r (P.dec r Y)) (dlt p fun z => Real.exp (P.ζ * Y (ε, 1, z)))

/-- The event that every depth-`r` polygon has Riemann cost `> t'` under the field `φ`. -/
def AllCostGt (r : ℕ) (t' : ℝ) (φ : Rd d → ℝ) : Prop :=
  ∀ T : DT P.J P.K r, t' < riemannCost P.ζ P.N (P.polyOf r T) φ

variable {P}

theorem mem_QsE_Qs {r : ℕ} {ε : ℝ} {t : TriD d} (ht : t ∈ P.Qs r) : t ∈ P.QsE r ε :=
  Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ ht))

theorem Qs_subset_QsE (r : ℕ) (ε : ℝ) : P.Qs r ⊆ P.QsE r ε := fun _ ht => mem_QsE_Qs ht

theorem mem_QsE_cut {r : ℕ} {ε : ℝ} {p : Rd d} (hp : p ∈ P.S r) : (ε, 1, p) ∈ P.QsE r ε :=
  Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _
    (Finset.mem_image_of_mem _ hp)))

theorem mem_QsE_low {r : ℕ} {ε : ℝ} {p : Rd d} (hp : p ∈ P.S r) :
    (ε, P.ρ * P.q ^ r, p) ∈ P.QsE r ε :=
  Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hp))

theorem mem_QsE_high {r : ℕ} {ε : ℝ} {p : Rd d} (hp : p ∈ P.S r) : (P.ρ, 1, p) ∈ P.QsE r ε :=
  Finset.mem_union_right _ (Finset.mem_image_of_mem _ hp)

theorem Good.QsE_pos (hP : P.Good) (r : ℕ) {ε : ℝ} (hε : 0 < ε) : ∀ t ∈ P.QsE r ε, 0 < t.1 := by
  intro t ht
  simp only [QsE, Finset.mem_union, Finset.mem_image] at ht
  rcases ht with ((ht | ⟨p, -, rfl⟩) | ⟨p, -, rfl⟩) | ⟨p, -, rfl⟩
  · exact hP.Qs_pos r t ht
  · exact hε
  · exact hε
  · exact hP.ρ_pos

/-! ## Measurability, locality, integrability -/

theorem occE_eq (r : ℕ) (ε : ℝ) (p : Rd d) (Y : TriD d → ℝ) :
    P.occE r ε p Y = Real.exp (P.ζ * Y (ε, 1, p)) *
      rcW P.N (P.polyOf r (P.dec r Y)) (dlt p fun _ => 1) := by
  unfold occE
  rw [rcW_dlt]

theorem occE_nonneg (r : ℕ) (ε : ℝ) (p : Rd d) (Y : TriD d → ℝ) : 0 ≤ P.occE r ε p Y := by
  rw [occE_eq]
  exact mul_nonneg (Real.exp_pos _).le (rcW_nonneg _ _ (dlt_one_nonneg p))

theorem occE_le (r : ℕ) (ε : ℝ) (p : Rd d) (Y : TriD d → ℝ) :
    P.occE r ε p Y ≤ P.Lb r p * Real.exp (P.ζ * Y (ε, 1, p)) := by
  rw [occE_eq, mul_comm (P.Lb r p)]
  exact mul_le_mul_of_nonneg_left (rcW_le_Lb r p _) (Real.exp_pos _).le

theorem Good.measurable_occE (hP : P.Good) (r : ℕ) (ε : ℝ) (p : Rd d) :
    Measurable (P.occE r ε p) :=
  hP.measurable_of_dec (Φ := fun t Y => rcW P.N (P.polyOf r t)
    (dlt p fun z => Real.exp (P.ζ * Y (ε, 1, z))))
    fun _ => measurable_rcW _ _ fun w => by
      unfold dlt
      split_ifs
      · exact measurable_exp_eval _ _
      · exact measurable_const

theorem Good.RCe_eq_sum (hP : P.Good) (r : ℕ) (ε : ℝ) (Y : TriD d → ℝ) :
    P.RCe r ε Y = ∑ p ∈ P.S r, P.occE r ε p Y := by
  unfold RCe occE
  rw [riemannCost_eq_rcW, rcW_eq_sum_dlt _ _ _ (hP.riemannPts_polyOf_subset r _)]

theorem Good.measurable_RCe (hP : P.Good) (r : ℕ) (ε : ℝ) : Measurable (P.RCe r ε) := by
  have h : P.RCe r ε = fun Y => ∑ p ∈ P.S r, P.occE r ε p Y := funext (hP.RCe_eq_sum r ε)
  rw [h]
  exact Finset.measurable_sum _ fun p _ => hP.measurable_occE r ε p

theorem Good.integrable_occE (hP : P.Good) (hκ : IsLFPPKernel κ) (r : ℕ) {ε : ℝ} (hε : 0 < ε)
    {p : Rd d} (hp : p ∈ P.S r) : Integrable (P.occE r ε p) (gLawD κ (P.QsE r ε)) :=
  Integrable.mono' ((integrable_exp_gLawD hκ (hP.QsE_pos r hε) (mem_QsE_cut hp) P.ζ).const_mul
    (P.Lb r p)) (hP.measurable_occE r ε p).aestronglyMeasurable (ae_of_all _ fun Y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (occE_nonneg r ε p Y)]
      exact occE_le r ε p Y)

theorem Good.integrable_RCe (hP : P.Good) (hκ : IsLFPPKernel κ) (r : ℕ) {ε : ℝ} (hε : 0 < ε) :
    Integrable (P.RCe r ε) (gLawD κ (P.QsE r ε)) := by
  have h : P.RCe r ε = fun Y => ∑ p ∈ P.S r, P.occE r ε p Y := funext (hP.RCe_eq_sum r ε)
  rw [h]
  exact integrable_finsetSum _ fun p hp => hP.integrable_occE κ hκ r hε hp

theorem RCe_nonneg (r : ℕ) (ε : ℝ) (Y : TriD d → ℝ) : 0 ≤ P.RCe r ε Y :=
  riemannCost_nonneg _ _ _ _

/-! ## The unused bands -/

/-- The cutoff band splits into the unused band `(ε, ρq^r]`, the cost band `(ρq^r, ρ]` and the
unused band `(ρ, 1]`. -/
theorem Good.kapD_cut_rel (hP : P.Good) (hκ : IsLFPPKernel κ) (r : ℕ) {ε : ℝ} (hε : 0 < ε)
    (hεr : ε ≤ P.ρ * P.q ^ r) (hρ1 : P.ρ ≤ 1) (p : Rd d) {t' : TriD d} (ht' : 0 < t'.1) :
    kapD κ t' (ε, 1, p) =
      kapD κ t' (ε, P.ρ * P.q ^ r, p) + kapD κ t' (P.ρ * P.q ^ r, P.ρ, p) +
        kapD κ t' (P.ρ, 1, p) := by
  rw [kapD_split_right hκ hε hεr ((hP.rho_q_pow_le r).trans hρ1) p ht',
    kapD_split_right hκ (hP.rho_q_pow_pos r) (hP.rho_q_pow_le r) hρ1 p ht', add_assoc]

/-- The three-band relation holds almost surely in the finite model. -/
theorem Good.ae_cut_rel (hP : P.Good) (hκ : IsLFPPKernel κ) (r : ℕ) {ε : ℝ} (hε : 0 < ε)
    (hεr : ε ≤ P.ρ * P.q ^ r) (hρ1 : P.ρ ≤ 1) :
    ∀ᵐ Y ∂gLawD κ (P.QsE r ε), ∀ p ∈ P.S r,
      Y (ε, 1, p) = Y (ε, P.ρ * P.q ^ r, p) + Y (P.ρ * P.q ^ r, P.ρ, p) + Y (P.ρ, 1, p) := by
  rw [Filter.eventually_all_finset]
  intro p hp
  have h := ae_gLawOn_eq_sum (kapD κ) (kapD_psd hκ _ (hP.QsE_pos r hε))
    (Finset.univ : Finset (Fin 3)) (ε, 1, p)
    ![(ε, P.ρ * P.q ^ r, p), (P.ρ * P.q ^ r, P.ρ, p), (P.ρ, 1, p)] (mem_QsE_cut hp)
    (fun k _ => by
      fin_cases k
      · exact mem_QsE_low hp
      · exact mem_QsE_Qs (mem_Qs_cost hp)
      · exact mem_QsE_high hp)
    (fun j hj => by
      rw [Fin.sum_univ_three]
      exact hP.kapD_cut_rel κ hκ r hε hεr hρ1 p (hP.QsE_pos r hε j hj))
  filter_upwards [h] with Y hY
  rw [hY, Fin.sum_univ_three]
  rfl

/-- **The unused bands are independent of the construction**:
`E RiemannCost_N(poly(dec_r Y), Y(ε,1,·)) = Σ_p M_r(p) · E e^{ζY(ε,ρq^r,p)} · E e^{ζY(ρ,1,p)}`. -/
theorem Good.integral_RCe (hP : P.Good) (hκ : IsLFPPKernel κ) (r : ℕ) {ε : ℝ} (hε : 0 < ε)
    (hεr : ε ≤ P.ρ * P.q ^ r) (hρ1 : P.ρ ≤ 1) :
    ∫ Y, P.RCe r ε Y ∂gLawD κ (P.QsE r ε) =
      ∑ p ∈ P.S r, P.Mw κ r p *
        (∫ Y, Real.exp (P.ζ * Y (ε, P.ρ * P.q ^ r, p)) ∂gLawD κ (P.QsE r ε)) *
        (∫ Y, Real.exp (P.ζ * Y (P.ρ, 1, p)) ∂gLawD κ (P.QsE r ε)) := by
  have hF := hP.QsE_pos r hε
  simp_rw [hP.RCe_eq_sum r ε]
  rw [integral_finsetSum _ fun p hp => hP.integrable_occE κ hκ r hε hp]
  refine Finset.sum_congr rfl fun p hp => ?_
  -- the factorization, almost surely
  have hfac : ∀ᵐ Y ∂gLawD κ (P.QsE r ε), P.occE r ε p Y =
      Real.exp (P.ζ * Y (ε, P.ρ * P.q ^ r, p)) *
        (Real.exp (P.ζ * Y (P.ρ, 1, p)) * P.occ r p Y) := by
    filter_upwards [hP.ae_cut_rel κ hκ r hε hεr hρ1] with Y hY
    rw [occE_eq, occ_eq, hY p hp, mul_add, mul_add, Real.exp_add, Real.exp_add]
    ring
  rw [integral_congr_ae hfac]
  -- first independence: `(ε, ρq^r]` against `(ρ, 1]` and `Qs r`
  have hloc1 : IsLoc {(ε, P.ρ * P.q ^ r, p)} fun Y : TriD d → ℝ =>
      Real.exp (P.ζ * Y (ε, P.ρ * P.q ^ r, p)) :=
    (isLoc_eval (Finset.mem_singleton_self _)).comp fun y => Real.exp (P.ζ * y)
  have hloc2 : IsLoc {(P.ρ, 1, p)} fun Y : TriD d → ℝ => Real.exp (P.ζ * Y (P.ρ, 1, p)) :=
    (isLoc_eval (Finset.mem_singleton_self _)).comp fun y => Real.exp (P.ζ * y)
  have hloc3 : IsLoc (P.Qs r) (P.occ r p) := hP.occ_loc r p
  have hloc23 : IsLoc ({(P.ρ, 1, p)} ∪ P.Qs r) fun Y : TriD d → ℝ =>
      Real.exp (P.ζ * Y (P.ρ, 1, p)) * P.occ r p Y :=
    hloc2.union_left.comp₂ hloc3.union_right fun a b => a * b
  have hsub1 : ({(ε, P.ρ * P.q ^ r, p)} : Finset (TriD d)) ⊆ P.QsE r ε :=
    Finset.singleton_subset_iff.2 (mem_QsE_low hp)
  have hsub2 : ({(P.ρ, 1, p)} : Finset (TriD d)) ⊆ P.QsE r ε :=
    Finset.singleton_subset_iff.2 (mem_QsE_high hp)
  have hsub23 : ({(P.ρ, 1, p)} ∪ P.Qs r : Finset (TriD d)) ⊆ P.QsE r ε :=
    Finset.union_subset hsub2 (Qs_subset_QsE r ε)
  have hband := hP.Qs_band r
  rw [integral_mul_gLawD_of_disjoint (Φ := fun Y => Real.exp (P.ζ * Y (ε, P.ρ * P.q ^ r, p)))
    (Ψ := fun Y => Real.exp (P.ζ * Y (P.ρ, 1, p)) * P.occ r p Y) hκ hsub1 hsub23 hF
    (fun t ht t' ht' => by
      rw [Finset.mem_singleton] at ht
      subst ht
      rcases Finset.mem_union.1 ht' with ht' | ht'
      · rw [Finset.mem_singleton] at ht'
        subst ht'
        exact Or.inl (hP.rho_q_pow_le r)
      · exact Or.inl (hband t' ht').1)
    (measurable_exp_eval _ _) ((measurable_exp_eval _ _).mul (hP.measurable_occ r p))
    hloc1 hloc23]
  -- second independence: `(ρ, 1]` against `Qs r`
  rw [integral_mul_gLawD_of_disjoint (Φ := fun Y => Real.exp (P.ζ * Y (P.ρ, 1, p)))
    (Ψ := P.occ r p) hκ hsub2 (Qs_subset_QsE r ε) hF (fun t ht t' ht' => by
      rw [Finset.mem_singleton] at ht
      subst ht
      exact Or.inr (hband t' ht').2.2)
    (measurable_exp_eval _ _) (hP.measurable_occ r p) hloc2 hloc3]
  -- the occupation factor is `M_r(p)`
  rw [← integral_gLawD_eq_of_subset hκ (Qs_subset_QsE r ε) hF (hP.measurable_occ r p) hloc3]
  rw [← Mw]
  ring

/-- **The unused-band identity, evaluated**: `E RiemannCost_N(poly(dec_r Y), Y(ε,1,·)) =
e^{ζ² log(ρq^r/ε)/2} e^{ζ² log(1/ρ)/2} m_r`. -/
theorem Good.integral_RCe_eq (hP : P.Good) (hκ : IsLFPPKernel κ) (r : ℕ) {ε : ℝ} (hε : 0 < ε)
    (hεr : ε ≤ P.ρ * P.q ^ r) (hρ1 : P.ρ ≤ 1) :
    ∫ Y, P.RCe r ε Y ∂gLawD κ (P.QsE r ε) =
      Real.exp (P.ζ ^ 2 * Real.log (P.ρ * P.q ^ r / ε) / 2) *
        Real.exp (P.ζ ^ 2 * Real.log (1 / P.ρ) / 2) * P.mm κ r := by
  have hF := hP.QsE_pos r hε
  rw [hP.integral_RCe κ hκ r hε hεr hρ1, hP.mm_eq_sum κ hκ r, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [integral_exp_gLawD hκ hF (mem_QsE_low hp) hεr, integral_exp_gLawD hκ hF (mem_QsE_high hp)
    hρ1]
  ring

/-- **The unused-band bound**: for `ρ q^{r+1} ≤ ε ≤ ρ q^r` and `ρ ≤ 1`,
`E RiemannCost_N(poly(dec_r Y), Y(ε,1,·)) ≤ (ρq)^{-ζ²/2} m_r`. -/
theorem Good.integral_RCe_le (hP : P.Good) (hκ : IsLFPPKernel κ) (r : ℕ) {ε : ℝ}
    (hε1 : P.ρ * P.q ^ (r + 1) ≤ ε) (hε2 : ε ≤ P.ρ * P.q ^ r) (hρ1 : P.ρ ≤ 1) :
    ∫ Y, P.RCe r ε Y ∂gLawD κ (P.QsE r ε) ≤
      (P.ρ * P.q) ^ (-(P.ζ ^ 2) / 2) * P.mm κ r := by
  have hε : 0 < ε := (hP.rho_q_pow_pos (r + 1)).trans_le hε1
  rw [hP.integral_RCe_eq κ hκ r hε hε2 hρ1]
  refine mul_le_mul_of_nonneg_right ?_ (hP.mm_nonneg κ hκ r)
  have hq := hP.q_pos
  have hρ := hP.ρ_pos
  have hlog : Real.log (P.ρ * P.q ^ r / ε) ≤ Real.log (1 / P.q) := by
    refine Real.log_le_log (div_pos (hP.rho_q_pow_pos r) hε) ?_
    rw [div_le_div_iff₀ hε hq, one_mul, mul_assoc, ← pow_succ]
    exact hε1
  have h1 : Real.log (1 / P.q) = -Real.log P.q := by rw [one_div, Real.log_inv]
  have h2 : Real.log (1 / P.ρ) = -Real.log P.ρ := by rw [one_div, Real.log_inv]
  rw [h1] at hlog
  rw [Real.rpow_def_of_pos (mul_pos hρ hq), Real.log_mul hρ.ne' hq.ne', ← Real.exp_add,
    Real.exp_le_exp, h2]
  have hζ2 : 0 ≤ P.ζ ^ 2 / 2 := by positivity
  have h3 := mul_le_mul_of_nonneg_left hlog hζ2
  linarith

/-! ## Transfer to the white-noise field -/

theorem measurableSet_allCostGt (r : ℕ) (ε t' : ℝ) :
    MeasurableSet {Y : TriD d → ℝ | P.AllCostGt r t' fun z => Y (ε, 1, z)} := by
  have h : {Y : TriD d → ℝ | P.AllCostGt r t' fun z => Y (ε, 1, z)} =
      ⋂ T : DT P.J P.K r, {Y | t' < riemannCost P.ζ P.N (P.polyOf r T) fun z => Y (ε, 1, z)} := by
    ext Y
    simp only [AllCostGt, mem_ofPred_eq, mem_iInter]
  rw [h]
  refine MeasurableSet.iInter fun T => measurableSet_lt measurable_const ?_
  rw [show (fun Y : TriD d → ℝ => riemannCost P.ζ P.N (P.polyOf r T) fun z => Y (ε, 1, z)) =
    fun Y => rcW P.N (P.polyOf r T) fun z => Real.exp (P.ζ * Y (ε, 1, z)) from
    funext fun Y => riemannCost_eq_rcW _ _ _ _]
  exact measurable_rcW _ _ fun _ => measurable_exp_eval _ _

theorem Good.allCostGt_loc (hP : P.Good) (r : ℕ) (ε t' : ℝ) :
    IsLoc (P.QsE r ε) fun Y : TriD d → ℝ => Y ∈ {Y : TriD d → ℝ | P.AllCostGt r t'
      fun z => Y (ε, 1, z)} := by
  intro Y Y' h
  simp only [mem_ofPred_eq, AllCostGt]
  have hT : ∀ T : DT P.J P.K r, riemannCost P.ζ P.N (P.polyOf r T) (fun z => Y (ε, 1, z)) =
      riemannCost P.ζ P.N (P.polyOf r T) fun z => Y' (ε, 1, z) := fun T =>
    riemannCost_congr _ _ _ fun z hz =>
      h _ (mem_QsE_cut (hP.riemannPts_polyOf_subset r T hz))
  simp only [hT]

section WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} {W : WN d → Ω → ℝ}

/-- **Transfer** (HA4 D8): the probability that every depth-`r` polygon has Riemann cost `> t'`
under a version `H` of the band field `H_{ε,1}` equals the corresponding probability for the
finite model `Y(ε,1,·)` (same centered Gaussian law of the finitely many Riemann point values). -/
theorem Good.measure_allCostGt_eq (hP : P.Good) (hκ : IsLFPPKernel κ) (hW : IsWhiteNoise Pr W)
    (r : ℕ) {ε : ℝ} (hε : 0 < ε) {H : Rd d → Ω → ℝ} (hH : IsBandVersion Pr W κ ε 1 H)
    (t' : ℝ) :
    Pr {ω | P.AllCostGt r t' fun z => H z ω} =
      gLawD κ (P.QsE r ε) {Y | P.AllCostGt r t' fun z => Y (ε, 1, z)} := by
  rw [measure_gLawD_eq_whiteNoise hκ (hP.QsE_pos r hε) hW (measurableSet_allCostGt (P := P) r ε t')
    (hP.allCostGt_loc r ε t')]
  refine measure_congr ?_
  have hae : ∀ᵐ ω ∂Pr, ∀ p ∈ P.S r, H p ω = W (bandVec κ ε 1 p) ω :=
    (Filter.eventually_all_finset _).2 fun p _ => hH.ae_eq p
  filter_upwards [hae] with ω hω
  have hT : ∀ T : DT P.J P.K r, riemannCost P.ζ P.N (P.polyOf r T) (fun z => H z ω) =
      riemannCost P.ζ P.N (P.polyOf r T) fun z => W (triVec κ (ε, 1, z)) ω := fun T =>
    riemannCost_congr _ _ _ fun z hz => hω z (hP.riemannPts_polyOf_subset r T hz)
  show (P.AllCostGt r t' fun z => H z ω) =
    ((fun t => W (triVec κ t) ω) ∈ {Y : TriD d → ℝ | P.AllCostGt r t' fun z => Y (ε, 1, z)})
  simp only [mem_ofPred_eq, AllCostGt, hT]

/-- Markov's inequality for a nonnegative integrable function, in `ENNReal` form. -/
theorem measure_lt_le_integral_div {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {g : α → ℝ} (hg0 : ∀ x, 0 ≤ g x) (hint : Integrable g μ) {c : ℝ}
    (hc : 0 < c) : μ {x | c < g x} ≤ ENNReal.ofReal ((∫ x, g x ∂μ) / c) := by
  calc μ {x | c < g x} ≤ μ {x | c ≤ g x} :=
        measure_mono fun x (hx : c < g x) => show c ≤ g x from hx.le
    _ = ENNReal.ofReal (μ.real {x | c ≤ g x}) := (ofReal_measureReal (measure_ne_top _ _)).symm
    _ ≤ ENNReal.ofReal ((∫ x, g x ∂μ) / c) := by
      refine ENNReal.ofReal_le_ofReal ?_
      rw [le_div_iff₀ hc]
      have := mul_meas_ge_le_integral_of_nonneg (ae_of_all _ hg0) hint c
      linarith

/-- **The transfer estimate** (HA4 D8): for `ρ q^{r+1} ≤ ε ≤ ρ q^r`, `ρ ≤ 1` and `t' > 0`,
`P(every depth-r polygon has Riemann cost > t' under H_{ε,1}) ≤ (ρq)^{-ζ²/2} m_r / t'`. -/
theorem Good.measure_allCostGt_le (hP : P.Good) (hκ : IsLFPPKernel κ) (hW : IsWhiteNoise Pr W)
    (r : ℕ) {ε : ℝ} (hε1 : P.ρ * P.q ^ (r + 1) ≤ ε) (hε2 : ε ≤ P.ρ * P.q ^ r)
    (hρ1 : P.ρ ≤ 1) {H : Rd d → Ω → ℝ} (hH : IsBandVersion Pr W κ ε 1 H) {t' : ℝ}
    (ht' : 0 < t') :
    Pr {ω | P.AllCostGt r t' fun z => H z ω} ≤
      ENNReal.ofReal ((P.ρ * P.q) ^ (-(P.ζ ^ 2) / 2) * P.mm κ r / t') := by
  have hε : 0 < ε := (hP.rho_q_pow_pos (r + 1)).trans_le hε1
  rw [hP.measure_allCostGt_eq κ hκ hW r hε hH t']
  calc gLawD κ (P.QsE r ε) {Y | P.AllCostGt r t' fun z => Y (ε, 1, z)}
      ≤ gLawD κ (P.QsE r ε) {Y | t' < P.RCe r ε Y} :=
        measure_mono fun Y hY => hY (P.dec r Y)
    _ ≤ ENNReal.ofReal ((∫ Y, P.RCe r ε Y ∂gLawD κ (P.QsE r ε)) / t') :=
        measure_lt_le_integral_div (RCe_nonneg r ε) (hP.integrable_RCe κ hκ r hε) ht'
    _ ≤ ENNReal.ofReal ((P.ρ * P.q) ^ (-(P.ζ ^ 2) / 2) * P.mm κ r / t') :=
        ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right
          (hP.integral_RCe_le κ hκ r hε1 hε2 hρ1) ht'.le)

end WhiteNoise

end LParams

end HigherDimLFPP.Lower
