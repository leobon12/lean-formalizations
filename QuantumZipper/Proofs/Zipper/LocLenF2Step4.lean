import QuantumZipper.Proofs.Zipper.LocLenF2Chain
import QuantumZipper.Proofs.Zipper.LocLenF2Loc
import QuantumZipper.Proofs.Zipper.LocLenRules
import QuantumZipper.Proofs.Zipper.TruncFreeCore
import QuantumZipper.Proofs.Zipper.F2Gamma0ScaleDet

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# D75, task R7-S14 (2): F2 step (4) with open-arc lengths (`step4Arc_of_scale`)

Source: Sheffield, arXiv:1012.4797, §5.4 pp. 70–72 (step 4: scale invariance of `Γ⁰`, Brownian
scaling) and §5.1 pp. 60–62 (`z ↦ a z`, `h ↦ h(a·) + Q log a` preserves quantum surfaces).
Copies, with `unzipLengths ↦ LocLen.unzipLengthsArc`, of
* `F2.GammaZeroScaleStmt` (F2LocalScale.lean) as `GammaZeroScaleArcStmt`;
* `F2.unzipLengths_scale` / `F2.lenAgree_scale` (F2Gamma0ScaleDet.lean) as
  `unzipLengthsArc_scale` / `lenAgreeArc_scale`: the global `qBoundaryMeasure_rescale` is
  replaced by the local rule `arcLen_rescale_of_hasBdryLimitOn` (goodness off the tip `{0}`
  suffices, since the open arcs `(O⁻,0)`, `(0,O⁺)` avoid `0`);
* `F2.gammaZeroScaleStmt_of_raw'` (TruncFreeCore.lean) as `gammaZeroScaleArc_of_loc`, from
  `LocLen.ScaleGeomAeLocStmt'` (proved: `scaleGeomAeLoc_of_yMergeOffTip`);
* `F2.step4_of_scale` as `step4Arc_of_scale`.
No TipCore / TIP-X / global goodness at variable times is used.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace LocLen

/-- Open-arc copy of `F2.GammaZeroScaleStmt`. -/
def GammaZeroScaleArcStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample),
    IsBrownianReal B P → IsFreeGFFModConstH X P → IndepFun (pathOf B) X P →
    ∀ c : ℝ≥0, c ≠ 0 → ∃ X' : Ω → FieldSample, IsFreeGFFModConstH X' P ∧
      IndepFun (pathOf (F2.bmScale c B)) X' P ∧
      ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
        (unzipLengthsArc (Real.sqrt κ)
            (ofFun (h0rev κ) + X' ω, drive κ (F2.bmScale c B) ω) t).1 =
            (unzipLengthsArc (Real.sqrt κ)
              (ofFun (h0rev κ) + X' ω, drive κ (F2.bmScale c B) ω) t).2 →
          (unzipLengthsArc (Real.sqrt κ) (ofFun (h0rev κ) + X ω, drive κ B ω) (c * t)).1 =
            (unzipLengthsArc (Real.sqrt κ) (ofFun (h0rev κ) + X ω, drive κ B ω) (c * t)).2

/-- **Scale equivariance of open-arc lengths** (copy of `F2.unzipLengths_scale`, goodness only
off the tip `{0}`). -/
theorem unzipLengthsArc_scale {γ : ℝ} {x x' : FieldSample} {W : ℝ → ℝ} {a t : ℝ}
    (hγ : 0 < γ) (ha : 0 < a) (ht : 0 ≤ t)
    (hL : ∃ l, Tendsto (fun r : ℝ => (fwdMap W (a ^ 2 * t) r).re) (𝓝[<] (0 : ℝ)) (𝓝 l))
    (hR : ∃ l, Tendsto (fun r : ℝ => (fwdMap W (a ^ 2 * t) r).re) (𝓝[>] (0 : ℝ)) (𝓝 l))
    (hgood : IsLQGGoodOff γ (unzippedField γ (x, W) (a ^ 2 * t)) {0})
    (hfield : RegEq (unzippedField γ (x', fun s => W (a ^ 2 * s) / a) t)
      (rescale (unzippedField γ (x, W) (a ^ 2 * t)) (Qc γ) a)) :
    unzipLengthsArc γ (x', fun s => W (a ^ 2 * s) / a) t =
      unzipLengthsArc γ (x, W) (a ^ 2 * t) := by
  obtain ⟨l, hl⟩ := hL
  obtain ⟨m, hm⟩ := hR
  obtain ⟨hreg, ⟨ν, hν⟩, -⟩ := hgood
  set y := unzippedField γ (x, W) (a ^ 2 * t) with hy
  have hOl : (sideImages (fun s => W (a ^ 2 * s) / a) t).1 = l / a :=
    B3d.sideImages_fst_scale W ha ht hl
  have hOr : (sideImages (fun s => W (a ^ 2 * s) / a) t).2 = m / a :=
    B3d.sideImages_snd_scale W ha ht hm
  have hRl : (sideImages W (a ^ 2 * t)).1 = l := hl.limUnder_eq
  have hRr : (sideImages W (a ^ 2 * t)).2 = m := hm.limUnder_eq
  have hav := B3d.avgReg_eq_of_regEq hfield
  have hsub : ∀ p q : ℝ, (p < 0 ∧ q ≤ 0) ∨ (0 ≤ p ∧ 0 < q) → Ioo p q ⊆ ({0} : Set ℝ)ᶜ := by
    rintro p q h u hu hu0
    rw [mem_singleton_iff] at hu0
    subst hu0
    rcases h with h | h
    · exact absurd hu.2 (not_lt.2 h.2)
    · exact absurd hu.1 (not_lt.2 h.1)
  have hma : ∀ u : ℝ, a * (u / a) = u := fun u => mul_div_cancel₀ u ha.ne'
  have key : ∀ p q : ℝ, Ioo p q ⊆ ({0} : Set ℝ)ᶜ →
      arcLen γ (unzippedField γ (x', fun s => W (a ^ 2 * s) / a) t) (p / a) (q / a) =
        arcLen γ y p q := by
    intro p q hpq
    rw [arcLen_congr hav, arcLen_rescale_of_hasBdryLimitOn hreg hγ ha hν (by rwa [hma, hma]),
      hma, hma, arcLen_eq_of_hasBdryLimitOn hreg hν hpq]
  simp only [unzipLengthsArc]
  rw [hOl, hOr, hRl, hRr]
  refine Prod.ext ?_ ?_
  · show arcLen γ _ (l / a) 0 = arcLen γ y l 0
    by_cases hl0 : l < 0
    · have := key l 0 (hsub l 0 (Or.inl ⟨hl0, le_rfl⟩))
      rwa [zero_div] at this
    · have e1 : Ioo (l / a) 0 = ∅ := Ioo_eq_empty (not_lt.2 (div_nonneg (not_lt.1 hl0) ha.le))
      have e2 : Ioo l 0 = ∅ := Ioo_eq_empty hl0
      simp only [arcLen, e1, e2, measure_empty]
  · show arcLen γ _ 0 (m / a) = arcLen γ y 0 m
    by_cases hm0 : 0 < m
    · have := key 0 m (hsub 0 m (Or.inr ⟨le_rfl, hm0⟩))
      rwa [zero_div] at this
    · have e1 : Ioo 0 (m / a) = ∅ := Ioo_eq_empty (not_lt.2 (div_nonpos_of_nonpos_of_nonneg
        (not_lt.1 hm0) ha.le))
      have e2 : Ioo 0 m = ∅ := Ioo_eq_empty hm0
      simp only [arcLen, e1, e2, measure_empty]

/-- Open-arc lengths only read `avgReg` of the configuration field. -/
theorem unzipLengthsArc_congr_avgReg (γ : ℝ) {x y : FieldSample} (h : avgReg x = avgReg y)
    (W : ℝ → ℝ) (t : ℝ) : unzipLengthsArc γ (x, W) t = unzipLengthsArc γ (y, W) t := by
  have hcc : unzippedField γ (x, W) t = unzippedField γ (y, W) t := by
    funext μ
    show coordChange _ (fwdMapInv W t) (Qc γ) μ = coordChange _ (fwdMapInv W t) (Qc γ) μ
    unfold coordChange
    rw [F2.evalReg_congr_avgReg h]
  simp only [unzipLengthsArc, hcc]

/-- Raw and regularized dilation witnesses have the same open-arc lengths, a.s. (copy of
`F2.ae_unzipLengths_rawRescale`). -/
theorem ae_unzipLengthsArc_rawRescale {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → FieldSample} (hX : IsFreeGFFModConstH X P)
    (γ Q : ℝ) {a : ℝ} (ha : 0 < a) (g : ℂ → ℝ) (c : ℝ) :
    ∀ᵐ ω ∂P, ∀ (W : ℝ → ℝ) (t : ℝ),
      unzipLengthsArc γ (ofFun g + addConst (F2.rawRescale (X ω) Q a) c, W) t =
        unzipLengthsArc γ (ofFun g + addConst (rescale (X ω) Q a) c, W) t := by
  filter_upwards [F2.ae_rawRescale_fc_dyadic hX Q ha] with ω hω W t
  refine unzipLengthsArc_congr_avgReg γ (F2.avgReg_eq_of_fc_dyadic fun k n z => ?_) W t
  simp only [Pi.add_apply, addConst, hω k n z]

/-- **`GammaZeroScaleArcStmt` from the local scale geometry** (copy of
`F2.gammaZeroScaleStmt_of_raw'`). -/
theorem gammaZeroScaleArc_of_loc (hG : ScaleGeomAeLocStmt') : GammaZeroScaleArcStmt := by
  intro κ hκ hκ4 Ω _ P _ B X hB hX hind c hc
  have hc0 : (0 : ℝ) < (c : ℝ) := by
    have h : (0 : ℝ≥0) < c := pos_iff_ne_zero.2 hc
    exact_mod_cast h
  set a : ℝ := Real.sqrt (c : ℝ) with ha
  have ha0 : 0 < a := by rw [ha]; exact Real.sqrt_pos.2 hc0
  have ha2 : a ^ 2 = (c : ℝ) := by rw [ha]; exact Real.sq_sqrt hc0.le
  have h2 : (√c)⁻¹ = a⁻¹ := by rw [ha]
  refine ⟨fun ω => addConst (F2.rawRescale (X ω) (Qc (Real.sqrt κ)) a)
      (2 / Real.sqrt κ * Real.log a),
    S5.FieldLaw.Raw.isFreeGFFModConstH_addConst
      (F2.isFreeGFFModConstH_rawRescale hX (Qc (Real.sqrt κ)) ha0) measurable_const, ?_, ?_⟩
  · have hΦ : Measurable fun b : ℝ≥0 → ℝ => (fun t : ℝ≥0 => (√c)⁻¹ * b (c * t)) := by
      rw [measurable_pi_iff]
      exact fun t => measurable_const.mul (measurable_pi_apply (c * t))
    rw [show pathOf (F2.bmScale c B) = fun ω => (fun t : ℝ≥0 => (√c)⁻¹ * (pathOf B ω) (c * t))
      from rfl]
    exact F2.indepFun_comp_left hΦ (F2.indepFun_addConst_right
      (F2.indepFun_rawRescale hind (Qc (Real.sqrt κ)) a) _)
  · filter_upwards [hG κ hκ hκ4 P B X hB hX hind a ha0,
      ae_unzipLengthsArc_rawRescale hX (Real.sqrt κ) (Qc (Real.sqrt κ)) ha0 (h0rev κ)
        (2 / Real.sqrt κ * Real.log a)] with ω hω hraw t ht
    obtain ⟨hgood, hL, hR, hfield⟩ := hω t ht
    have hdrv : drive κ (F2.bmScale c B) ω = fun s => drive κ B ω (a ^ 2 * s) / a := by
      funext r
      rw [F2.drive_bmScale_all κ c B ω r, h2, ← ha2, div_eq_mul_inv]
      ring
    intro hA
    rw [hdrv, hraw, unzipLengthsArc_scale (Real.sqrt_pos.2 hκ) ha0 ht hL hR hgood hfield] at hA
    rw [← ha2]
    exact hA

/-- **F2 step (4), open arcs** (copy of `F2.step4_of_scale`). -/
theorem step4Arc_of_scale (hS : GammaZeroScaleArcStmt) : Step4ArcStmt := by
  intro hL κ hκ hκ4 Ω _ P _ B X hB hX hind
  obtain ⟨t₀, M, ht₀, hM, hloc⟩ := hL κ hκ hκ4
  set c : ℕ → ℝ≥0 := fun n => ((n : ℝ≥0) + 1) ^ 2 with hc
  have hc0 : ∀ n, c n ≠ 0 := fun n => pow_ne_zero _ (by positivity)
  have hsq : ∀ n, √(c n : ℝ) = (n : ℝ) + 1 := fun n => by
    simp only [hc, NNReal.coe_pow, NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one]
    exact Real.sqrt_sq (by positivity)
  have hS' : ∀ n, ∃ X' : Ω → FieldSample, IsFreeGFFModConstH X' P ∧
      IndepFun (pathOf (F2.bmScale (c n) B)) X' P ∧ _ := fun n =>
    hS κ hκ hκ4 P B X hB hX hind (c n) (hc0 n)
  choose X' hX' hind' himp using hS'
  have hloc' : ∀ n, ∀ᵐ ω ∂P, SmallTimeAgreeArc (Real.sqrt κ) (ofFun (h0rev κ) + X' n ω)
      (drive κ (F2.bmScale (c n) B) ω) t₀ M := fun n =>
    hloc P (F2.bmScale (c n) B) (X' n) (hB.smul (hc0 n)) (hX' n) (hind' n)
  have himp' := ae_all_iff.2 himp
  have hloc'' := ae_all_iff.2 hloc'
  filter_upwards [himp', hloc'', hB.cont] with ω hI hA hcont t ht
  have hW : Continuous (drive κ B ω) := continuous_const.mul (hcont.comp continuous_real_toNNReal)
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := t)).exists_bound_of_continuousOn
    hW.continuousOn
  obtain ⟨n, hn⟩ := exists_nat_ge (max (K / M) (t / t₀))
  have hn1 : K / M ≤ (n : ℝ) + 1 := (le_max_left _ _).trans (hn.trans (by linarith))
  have hn2 : t / t₀ ≤ (n : ℝ) + 1 := (le_max_right _ _).trans (hn.trans (by linarith))
  have hcn : (c n : ℝ) = ((n : ℝ) + 1) ^ 2 := by simp [hc]
  have hcpos : (0 : ℝ) < c n := by rw [hcn]; positivity
  set s := t / (c n : ℝ) with hs
  have hs0 : 0 ≤ s := div_nonneg ht hcpos.le
  have hcs : (c n : ℝ) * s = t := by rw [hs]; field_simp
  have hst₀ : s ≤ t₀ := by
    rw [hs, div_le_iff₀ hcpos, hcn]
    have h1 : t ≤ ((n : ℝ) + 1) * t₀ := by rwa [div_le_iff₀ ht₀] at hn2
    have h2 : ((n : ℝ) + 1) * t₀ ≤ t₀ * ((n : ℝ) + 1) ^ 2 := by nlinarith
    linarith
  have hagree := hA n s hs0 hst₀ (fun r hr => by
    rw [F2.drive_bmScale κ (c n) B ω hr.1, hsq n, abs_mul, abs_inv,
      abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1), inv_mul_le_iff₀ (by positivity)]
    have hmem : (c n : ℝ) * r ∈ Icc (0 : ℝ) t :=
      ⟨mul_nonneg hcpos.le hr.1, by rw [← hcs]; exact mul_le_mul_of_nonneg_left hr.2 hcpos.le⟩
    have h1 := hK _ hmem
    rw [Real.norm_eq_abs] at h1
    have h2 : K ≤ ((n : ℝ) + 1) * M := by rwa [div_le_iff₀ hM] at hn1
    linarith)
  have := hI n s hs0 hagree
  rwa [hcs] at this

/-! ## Closed forms -/

theorem gammaZeroScaleArc_of_yMergeOffTip (hYO : WedgeUnzip.YMergeOffTipStmt) :
    GammaZeroScaleArcStmt :=
  gammaZeroScaleArc_of_loc (scaleGeomAeLoc_of_yMergeOffTip hYO)

theorem step4Arc_of_yMergeOffTip (hYO : WedgeUnzip.YMergeOffTipStmt) : Step4ArcStmt :=
  step4Arc_of_scale (gammaZeroScaleArc_of_yMergeOffTip hYO)

end LocLen
end QuantumZipper
