import MeshRates.Theorem11RateAux
import MeshRates.Section5Energy
import MeshRates.WellPosed
import MeshRates.Theorem11Qualitative
import MeshRates.Statement.Theorem11Rate

/-!
# MR Theorem 1.1 (10): the rate `ε^{4/(d+4)}` (MR pp. 14–15, (72)–(81))
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped Topology ENNReal NNReal

namespace BouRabeeGwynne.MeshRates

/-- Rescaling a discrete Dirichlet solution together with its boundary data. -/
lemma solvesDirichlet_const_smul {d : ℕ} {T : OrthogonalTiling d} {U : Set (Euc d)}
    {h : Euc d → ℝ} {hD : T.V → ℝ} (c : ℝ)
    (hsol : T.SolvesDirichlet U (fun v => h (T.pos v)) hD) :
    T.SolvesDirichlet U (fun v => (c • h) (T.pos v)) (c • hD) := by
  refine ⟨fun w hw => ?_, fun w hw => ?_⟩
  · obtain ⟨hfn, h0⟩ := hsol.1 w hw
    refine ⟨hfn, ?_⟩
    unfold OrthogonalTiling.discreteLaplacian at h0 ⊢
    simp only [Pi.smul_apply, smul_eq_mul, ← mul_sub, mul_left_comm _ c, ← Finset.mul_sum, h0,
      mul_zero]
  · simp [hsol.2 w hw]

/-- Rescaling the Hessian. -/
lemma fderiv_fderiv_const_smul {d : ℕ} (h : Euc d → ℝ) {c : ℝ} (hc : c ≠ 0) (x : Euc d) :
    fderiv ℝ (fderiv ℝ (c • h)) x = c • fderiv ℝ (fderiv ℝ h) x := by
  letI : Invertible c := invertibleOfNonzero hc
  have : fderiv ℝ (c • h) = c • fderiv ℝ h := funext fun y => fderiv_const_smul_of_invertible c
  rw [this]; exact fderiv_const_smul_of_invertible (f := fderiv ℝ h) c

theorem theorem11_rate : MeshRatesTheorem11RateStatement := by
  intro d hd U K hUb hK hKb hUK
  obtain ⟨ρ, hρ, hρK⟩ := hUb.isCompact_closure.exists_cthickening_subset_open hK hUK
  obtain ⟨ε₁, hε₁, h51⟩ := lemma51_energy_and_l2_error hd hUb hK hKb hUK
  obtain ⟨ε₂, hε₂, hWP⟩ := wellPosed_of_mesh_le (d := d) (by omega) hUb hK hUK
  obtain ⟨C₆, hC₆, H61⟩ := lemma61_expectedExitTime_le hd
  set r := ρ / 4 with hr
  have hr0 : 0 < r := by positivity
  set C₅ := max (lemma51Constant d K) 0
  have hC₅ : 0 ≤ C₅ := le_max_right _ _
  set ε₀ := min (min 1 (r / 4)) (min ε₁ ε₂) with hε₀
  have hε₀0 : 0 < ε₀ := lt_min (lt_min one_pos (by positivity)) (lt_min hε₁ hε₂)
  refine ⟨ε₀, hε₀0, theorem11RateConst d r C₅ C₆,
    theorem11RateConst_nonneg d hr0 hC₅ hC₆, ?_⟩
  intro T hcol hmeshle
  have hmesh : T.mesh ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hmeshle
  have hεle : T.mesh.toReal ≤ ε₀ := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmeshle
    rwa [ENNReal.toReal_ofReal hε₀0.le] at this
  set ε := T.mesh.toReal with hεdef
  have hε0 : 0 ≤ ε := ENNReal.toReal_nonneg
  have hε1 : ε ≤ 1 := hεle.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hεr : ε ≤ r / 4 := hεle.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hmle : ∀ {e : ℝ}, ε₀ ≤ e → T.mesh ≤ ENNReal.ofReal e :=
    fun he => hmeshle.trans (ENNReal.ofReal_le_ofReal he)
  obtain ⟨hfin, hL51⟩ := h51 T hcol (hmle ((min_le_right _ _).trans (min_le_left _ _)))
  refine ⟨hWP T hcol (hmle ((min_le_right _ _).trans (min_le_right _ _))), ?_⟩
  intro h hhK M hM hD hsol v hv
  letI : Fintype (T.closedVertices U) := hfin.fintype
  obtain ⟨W, hWo, hKW, hhW⟩ := hhK
  have hKint : K ⊆ interior T.domain := subset_closure.trans hcol
  have hvU : T.pos v ∈ U := hv
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM (T.pos v) (hUK (subset_closure hvU))).1
  have hcellU : ∀ w : T.V, T.pos w ∈ U → (T.cell w).carrier ⊆ interior T.domain :=
    fun w hw => ((T.toTilingData.cell_subset_cthickening hw hmesh (by linarith)).trans
      hρK).trans hKint
  have hposK : ∀ w : T.closedVertices U, T.pos w ∈ K := by
    rintro ⟨w, hw | ⟨_, u, hu, hadj⟩⟩
    · exact hUK (subset_closure hw)
    · refine hρK (Metric.mem_cthickening_of_dist_le _ (T.pos u) ρ _ (subset_closure hu) ?_)
      rw [dist_comm]
      exact (T.toTilingData.edge_dist_le_two_mesh hadj hmesh).trans (by linarith)
  -- maximum principle: `|h_D| ≤ M` on the closed region
  let N := T.finiteNetwork (T.closedVertices U)
  have ha : N.BoundaryAccessible (T.finiteInterior U) :=
    T.finiteNetwork_boundaryAccessible_of_cell_interior (by omega)
      (EuclideanSpace.single ⟨0, by omega⟩ 1) (by simp) (T.closedVertices U) (T.finiteInterior U)
      (fun w hw u hwu => T.neighbor_mem_closedVertices hw hwu) (fun w hw => hcellU w hw)
  have hsolR := T.solvesDirichlet_restrict hsol
  have hbd : ∀ w : T.closedVertices U, |hD w| ≤ M := by
    intro w
    rw [abs_le]
    constructor
    · have := N.maximum_principle (T.finiteInterior U) ha (fun u => -hD u) (-(-M))
        (fun u hu => by
          rw [show (fun u : T.closedVertices U => -hD u) = -(fun u : T.closedVertices U => hD u) from rfl,
            N.laplacian_neg, hsolR.1 u hu, neg_zero])
        (fun u hu => by
          have e := hsolR.2 u hu; simp only at e; rw [e]; linarith [(abs_le.mp (hM _ (hposK u)).1).1]) w
      linarith
    · exact N.maximum_principle (T.finiteInterior U) ha (fun u => hD u) M
        (fun u hu => (hsolR.1 u hu).ge)
        (fun u hu => by have e := hsolR.2 u hu; simp only at e; rw [e]; exact (abs_le.mp (hM _ (hposK u)).1).2) w
  have hball : Metric.closedBall (T.pos v) (2 * r) ⊆ K :=
    ((Metric.closedBall_subset_cthickening (subset_closure hvU) _).trans
      (Metric.cthickening_mono (by linarith) _)).trans hρK
  rcases hM0.eq_or_lt with hM0' | hMpos
  · subst hM0'
    have h1 := hbd ⟨v, Or.inl hv⟩
    have h2 := (hM (T.pos v) (hUK (subset_closure hvU))).1
    have e1 : hD v = 0 := abs_nonpos_iff.mp h1
    have e2 : h (T.pos v) = 0 := abs_nonpos_iff.mp h2
    simp [e1, e2]
  -- normalized estimate for `c = ±M⁻¹`
  have hL2 := hL51 h W hD M hM0 hWo hKW hhW (fun x hx => (hM x hx).2.2) hsol
  have hnorm : ∀ c : ℝ, |c| * M = 1 →
      c * (hD v - h (T.pos v)) ≤ theorem11RateConst d r C₅ C₆ * ε ^ (4 / ((d : ℝ) + 4)) := by
    intro c hc
    have hc0 : c ≠ 0 := by rintro rfl; simp at hc
    have hcore := theorem11_rate_core hd hC₅ hC₆ H61 T hmesh hε1 U hcellU (c • h) (c • hD)
      (solvesDirichlet_const_smul c hsol) ?_ ?_ ⟨v, Or.inl hv⟩ hvU hr0 (by linarith)
      (hball.trans hKint) hWo (hball.trans (subset_closure.trans hKW))
      (hhW.1.const_smul c) ?_
    · simpa [mul_sub] using hcore
    · intro w
      have h1 := hbd w
      have h2 := (hM _ (hposK w)).1
      simp only [Pi.smul_apply, smul_eq_mul, ← mul_sub]
      calc c * (hD w - h (T.pos w)) ≤ |c * (hD w - h (T.pos w))| := le_abs_self _
        _ = |c| * |hD w - h (T.pos w)| := abs_mul _ _
        _ ≤ |c| * (M + M) :=
          mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add h1 h2)) (abs_nonneg _)
        _ = 2 := by linarith
    · simp only [Pi.smul_apply, smul_eq_mul, ← mul_sub, mul_pow, ← mul_assoc,
        mul_comm _ (c ^ 2)]
      simp_rw [mul_assoc (c ^ 2)]; rw [← Finset.mul_sum]
      have hc2 : c ^ 2 * M ^ 2 = 1 := by
        rw [← mul_pow, ← sq_abs, abs_mul, abs_of_nonneg hM0, hc]; norm_num
      calc c ^ 2 * ∑ w : T.closedVertices U, (T.cell w).volume.toReal *
            (hD w - h (T.pos w)) ^ 2 ≤ c ^ 2 * (lemma51Constant d K * M ^ 2 * ε ^ 2) :=
          mul_le_mul_of_nonneg_left (by
            simpa [mul_comm] using le_trans (le_add_of_nonneg_left (N.energy_nonneg _)) hL2) (sq_nonneg _)
        _ ≤ c ^ 2 * (C₅ * M ^ 2 * ε ^ 2) := by gcongr; exact le_max_left _ _
        _ = C₅ * ε ^ 2 := by linear_combination (C₅ * ε ^ 2) * hc2
    · intro x hx
      rw [fderiv_fderiv_const_smul h hc0]
      refine (ContinuousLinearMap.opNorm_smul_le c (fderiv ℝ (fderiv ℝ h) x)).trans ?_
      rw [Real.norm_eq_abs, ← hc]
      exact mul_le_mul_of_nonneg_left (hM x (hball hx)).2.2 (abs_nonneg _)
  have hp := hnorm M⁻¹ (by rw [abs_of_pos (inv_pos.mpr hMpos), inv_mul_cancel₀ hMpos.ne'])
  have hn := hnorm (-M⁻¹) (by rw [abs_neg, abs_of_pos (inv_pos.mpr hMpos),
    inv_mul_cancel₀ hMpos.ne'])
  have hMi : M * M⁻¹ = 1 := mul_inv_cancel₀ hMpos.ne'
  unfold meshRateExponent
  rw [abs_le]
  constructor
  · have := mul_le_mul_of_nonneg_left hn hM0
    rw [show M * (-M⁻¹ * (hD v - h (T.pos v))) = -(hD v - h (T.pos v)) by field_simp] at this
    linarith [show M * (theorem11RateConst d r C₅ C₆ * ε ^ (4 / ((d : ℝ) + 4))) =
      theorem11RateConst d r C₅ C₆ * M * ε ^ (4 / ((d : ℝ) + 4)) by ring]
  · have := mul_le_mul_of_nonneg_left hp hM0
    rw [show M * (M⁻¹ * (hD v - h (T.pos v))) = hD v - h (T.pos v) by field_simp] at this
    linarith [show M * (theorem11RateConst d r C₅ C₆ * ε ^ (4 / ((d : ℝ) + 4))) =
      theorem11RateConst d r C₅ C₆ * M * ε ^ (4 / ((d : ℝ) + 4)) by ring]

theorem theorem11_full : MeshRatesTheorem11Statement := ⟨theorem11_qualitative, theorem11_rate⟩

end BouRabeeGwynne.MeshRates
