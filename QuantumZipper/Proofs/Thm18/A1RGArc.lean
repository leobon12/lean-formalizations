import QuantumZipper.Proofs.Thm18.A1R2YCont
import QuantumZipper.Proofs.Thm18.R18G1ArcWire
import QuantumZipper.Proofs.Thm18.G1RegRepMeas
import QuantumZipper.Proofs.Zipper.B2Reg
import QuantumZipper.Proofs.Zipper.F1PStarShiftRegDet
import QuantumZipper.Proofs.Zipper.FieldLawler4Final
import QuantumZipper.Proofs.Zipper.BaseFin2Main
import QuantumZipper.Proofs.Zipper.BaseFin2SleFL

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# A1RG (arc): log growth of the unzipped field at the open-arc unzipping time, all radii

The consumer of the growth node (`g1ZA1bSideExactArcStmt_of_sideRTX`, G1A1bMain.lean) uses the
unzipped field `U_t = coordChange Y f_t⁻¹ Q` only at `t = lenTimeArc γ ℓ c₀`. At that time the
rescaled field is the field of `Z^LEN_{−ℓ} c₀` (`zipLenDownArc`), whose full data has the law of
the data of `c₀` (open-arc E6, `e6Arc_thm18`). Log growth of the regularized circle averages at
all radii (Hu–Miller–Peres, Ann. Probab. 38 (2010), Prop. 2.1; `A1R2.a1r2_ae_evalReg_growth`) is
an event of the circle coordinates (`growthSetC`: rational centres and radii, then continuity of
the regular witness), so it transfers, as in `unzGrowthStmt_holds` (RT6bGrowth.lean) and as
proposed in D90 ("cheaper variant").

* `A1RG.ae_arcGrowth`: a.s., if `unzipScaleArc > 0`, every regularity witness `F` of
  `U_{lenTimeArc}` satisfies `|F(z, ρ)| ≤ C (1 + |log ρ|)` for `z ∈ ℍ̄`, `‖z‖ ≤ R`, `0 < ρ ≤ R`.

Own bookkeeping on top of the cited project results.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace R18
namespace A1RG

open Thm18Asm CoordsFull LocLen

/-- The rational parameter point `a + b i`. -/
def ratC (q : ℚ × ℚ × ℚ) : ℂ := ⟨(q.1 : ℝ), (q.2.1 : ℝ)⟩

/-- Coordinate vectors whose regularized circle averages at rational parameters have log growth
on bounded sets. -/
def growthSetC : Set (ℕ → ℝ) :=
  ⋂ R : ℕ, ⋃ C : ℕ, ⋂ q : ℚ × ℚ × ℚ,
    {c | (0 : ℝ) ≤ q.2.1 → (0 : ℝ) < q.2.2 → ‖ratC q‖ ≤ R → (q.2.2 : ℝ) ≤ R →
      |evalReg (E1.fromC c) (foldedCircle (ratC q) q.2.2)| ≤ C * (1 + |Real.log q.2.2|)}

theorem measurableSet_growthSetC : MeasurableSet growthSetC := by
  refine MeasurableSet.iInter fun R => MeasurableSet.iUnion fun C =>
    MeasurableSet.iInter fun q => ?_
  refine MeasurableSet.imp (MeasurableSet.const _) (MeasurableSet.imp (MeasurableSet.const _)
    (MeasurableSet.imp (MeasurableSet.const _) (MeasurableSet.imp (MeasurableSet.const _) ?_)))
  exact measurableSet_le
    (continuous_abs.measurable.comp
      ((measurable_evalReg (foldedCircle (ratC q) q.2.2)).comp G1Meas.measurable_fromC'))
    measurable_const

theorem mem_growthSetC_of {x : FieldSample}
    (h : ∀ Rr : ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ c ∈ Hbar, ‖c‖ ≤ Rr → ∀ ρ : ℝ, 0 < ρ → ρ ≤ Rr →
      |evalReg x (foldedCircle c ρ)| ≤ C * (1 + |Real.log ρ|)) :
    coordsFull x ∈ growthSetC := by
  simp only [growthSetC, mem_iInter, mem_iUnion, mem_ofPred_eq]
  intro R
  obtain ⟨C, hC, hb⟩ := h R
  refine ⟨⌈C⌉₊, fun q hq1 hq2 hn hr => ?_⟩
  rw [B2.evalReg_congr_coordsFull (E1.coordsFull_fromC x)]
  exact (hb _ hq1 hn _ hq2 hr).trans
    (mul_le_mul_of_nonneg_right (Nat.le_ceil C) (by positivity))

/-- Rational approximation from above. -/
theorem exists_rat_seq (x : ℝ) : ∃ a : ℕ → ℚ, (∀ n, x < a n) ∧
    (∀ n, (a n : ℝ) < x + 1 / ((n : ℝ) + 1)) ∧ Tendsto (fun n => (a n : ℝ)) atTop (𝓝 x) := by
  have h : ∀ n : ℕ, ∃ q : ℚ, x < q ∧ (q : ℝ) < x + 1 / ((n : ℝ) + 1) := fun n =>
    exists_rat_btwn (lt_add_of_pos_right x (by positivity))
  choose a ha1 ha2 using h
  refine ⟨a, ha1, ha2, ?_⟩
  have hup : Tendsto (fun n : ℕ => x + 1 / ((n : ℝ) + 1)) atTop (𝓝 x) := by
    have h0 := (tendsto_const_nhds (x := x)).add
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa using h0
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
    (fun n => (ha1 n).le) (fun n => (ha2 n).le)

/-- **Growth at all parameters from growth at the rational ones**, for a field whose circle
averages are given by a function continuous on `ℍ̄ × (0, ∞)`. -/
theorem growth_of_mem {x : FieldSample} {G : ℂ × ℝ → ℝ} (hGc : ContinuousOn G (Hbar ×ˢ Ioi 0))
    (hGx : ∀ u ∈ Hbar, ∀ r : ℝ, 0 < r → evalReg x (foldedCircle u r) = G (u, r))
    (hmem : coordsFull x ∈ growthSetC) (Rr : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u ∈ Hbar, ‖u‖ ≤ Rr → ∀ ρ : ℝ, 0 < ρ → ρ ≤ Rr →
      |G (u, ρ)| ≤ C * (1 + |Real.log ρ|) := by
  simp only [growthSetC, mem_iInter, mem_iUnion, mem_ofPred_eq] at hmem
  obtain ⟨C, hC⟩ := hmem ⌈2 * |Rr| + 3⌉₊
  have hR : 2 * |Rr| + 3 ≤ (⌈2 * |Rr| + 3⌉₊ : ℝ) := Nat.le_ceil _
  refine ⟨C, by positivity, fun u hu huR ρ hρ hρR => ?_⟩
  obtain ⟨a, ha1, ha2, ha⟩ := exists_rat_seq u.re
  obtain ⟨b, hb1, hb2, hb⟩ := exists_rat_seq u.im
  obtain ⟨r, hr1, hr2, hr⟩ := exists_rat_seq ρ
  set q : ℕ → ℚ × ℚ × ℚ := fun n => (a n, b n, r n) with hq
  have hu0 : 0 ≤ u.im := hu
  have hinv : ∀ n : ℕ, 1 / ((n : ℝ) + 1) ≤ 1 := fun n => by
    rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hbound : ∀ n, |G (ratC (q n), (r n : ℝ))| ≤ C * (1 + |Real.log (r n : ℝ)|) := by
    intro n
    have hbn : (0 : ℝ) ≤ (b n : ℝ) := hu0.trans (hb1 n).le
    have hrn : (0 : ℝ) < (r n : ℝ) := hρ.trans (hr1 n)
    have hre : |u.re| ≤ ‖u‖ := Complex.abs_re_le_norm u
    have him : |u.im| ≤ ‖u‖ := Complex.abs_im_le_norm u
    have hRr : Rr ≤ |Rr| := le_abs_self Rr
    have hnorm : ‖ratC (q n)‖ ≤ (⌈2 * |Rr| + 3⌉₊ : ℝ) := by
      have h1 := Complex.norm_le_abs_re_add_abs_im (ratC (q n))
      have h2 : |(a n : ℝ)| ≤ |u.re| + 1 := by
        rw [abs_le]; constructor
        · linarith [neg_abs_le u.re, ha1 n]
        · linarith [le_abs_self u.re, ha2 n, hinv n]
      have h3 : |(b n : ℝ)| ≤ |u.im| + 1 := by
        rw [abs_le]; constructor
        · linarith [neg_abs_le u.im, hb1 n]
        · linarith [le_abs_self u.im, hb2 n, hinv n]
      have e1 : (ratC (q n)).re = (a n : ℝ) := rfl
      have e2 : (ratC (q n)).im = (b n : ℝ) := rfl
      rw [e1, e2] at h1
      linarith
    have hrR : (r n : ℝ) ≤ (⌈2 * |Rr| + 3⌉₊ : ℝ) := by
      linarith [hr2 n, hinv n, abs_nonneg Rr]
    have hmemH : ratC (q n) ∈ Hbar := hbn
    rw [← hGx _ hmemH _ hrn, ← B2.evalReg_congr_coordsFull (E1.coordsFull_fromC x)]
    exact hC (q n) hbn hrn hnorm hrR
  -- pass to the limit
  have hc : Tendsto (fun n => (ratC (q n), (r n : ℝ))) atTop (𝓝 (u, ρ)) := by
    have hz : Tendsto (fun n => ratC (q n)) atTop (𝓝 u) := by
      have e : ∀ n, ratC (q n) = ((a n : ℝ) : ℂ) + ((b n : ℝ) : ℂ) * Complex.I := fun n => by
        apply Complex.ext <;> simp [ratC, hq]
      simp only [e]
      have hu' : u = ((u.re : ℝ) : ℂ) + ((u.im : ℝ) : ℂ) * Complex.I := (Complex.re_add_im u).symm
      rw [hu']
      exact ((Complex.continuous_ofReal.tendsto _).comp ha).add
        (((Complex.continuous_ofReal.tendsto _).comp hb).mul tendsto_const_nhds)
    exact hz.prodMk_nhds hr
  have hin : ∀ n, (ratC (q n), (r n : ℝ)) ∈ Hbar ×ˢ Ioi (0 : ℝ) := fun n =>
    ⟨show (0 : ℝ) ≤ (b n : ℝ) from hu0.trans (hb1 n).le, hρ.trans (hr1 n)⟩
  have hGt : Tendsto (fun n => G (ratC (q n), (r n : ℝ))) atTop (𝓝 (G (u, ρ))) := by
    have hcw := hGc (u, ρ) ⟨hu, hρ⟩
    exact hcw.tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hc, Eventually.of_forall hin⟩)
  have hlt : Tendsto (fun n => C * (1 + |Real.log (r n : ℝ)|)) atTop
      (𝓝 (C * (1 + |Real.log ρ|))) :=
    tendsto_const_nhds.mul (tendsto_const_nhds.add
      (((Real.continuousAt_log hρ.ne').tendsto.comp hr).abs))
  exact le_of_tendsto_of_tendsto' hGt.abs hlt hbound

/-- The field of `Z^LEN_{−ℓ} c₀` has log growth at all radii, a.s. (open-arc E6 transfer). -/
theorem ae_zipArc_growthSetC {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} {Y : Ω → FieldSample}
    (hS : Thm18Setting γ P B Y) (hIn : Thm18Inputs γ P B Y) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ∀ᵐ ω ∂P, coordsFull (zipLenDownArc γ ℓ (wedgeConfig γ B Y ω)).1 ∈ growthSetC := by
  have hX1 : BaseFin.BaseFiniteStmt :=
    BaseFin2.baseFinite_of_yMerge_tail SWCore.yMergeOffTipStmt_holds
      (BaseFin2.sleBaseTail_of_fieldLawler FieldLawler.fieldLawlerReturn_holds)
  have hE : MeasurableSet {d : E6.FullData | d.1.1 ∈ growthSetC} :=
    measurableSet_growthSetC.preimage (measurable_fst.comp measurable_fst)
  have hX0 : AEMeasurable (fun ω => cfgData (wedgeConfig γ B Y ω)) P :=
    aemeasurable_cfgData_wedgeConfig hS hIn
  have hXz := aemeasurable_cfgData_zipLenDownArc (unzipMeasArc_of_X1 hX1) hS hℓ
  have h0 : ∀ᵐ ω ∂P, cfgData (wedgeConfig γ B Y ω) ∈ {d : E6.FullData | d.1.1 ∈ growthSetC} := by
    filter_upwards [A1R2.a1r2_ae_evalReg_growth hS hIn] with ω h
    exact mem_growthSetC_of h
  have h' := (ae_map_iff hX0 hE).2 h0
  have hlaw := e6Arc_thm18 (e6StmtArc_of_X1 hX1) hS ℓ hℓ
  rw [configLawFull_eq_map_cfgData, configLawFull_eq_map_cfgData] at hlaw
  rw [← hlaw] at h'
  filter_upwards [(ae_map_iff hXz hE).1 h'] with ω h
  exact h

/-- **Log growth of the unzipped field at the open-arc unzipping time, all radii.** -/
theorem ae_arcGrowth {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} {Y : Ω → FieldSample}
    (hS : Thm18Setting γ P B Y) (hIn : Thm18Inputs γ P B Y) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ∀ᵐ ω ∂P, 0 < unzipScaleArc γ ℓ (wedgeConfig γ B Y ω) → ∀ F : ℂ × ℝ → ℝ,
      IsRegularWith (coordChange (Y ω) (fwdMapInv (drive (γ ^ 2) B ω)
        (lenTimeArc γ ℓ (wedgeConfig γ B Y ω))) (Qc γ)) F →
      ∀ Rr : ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ Hbar, ‖z‖ ≤ Rr → ∀ ρ : ℝ, 0 < ρ → ρ ≤ Rr →
        |F (z, ρ)| ≤ C * (1 + |Real.log ρ|) := by
  filter_upwards [ae_zipArc_growthSetC hS hIn hℓ] with ω hmem ha F hF Rr
  set U := coordChange (Y ω) (fwdMapInv (drive (γ ^ 2) B ω)
    (lenTimeArc γ ℓ (wedgeConfig γ B Y ω))) (Qc γ) with hU
  set a := unzipScaleArc γ ℓ (wedgeConfig γ B Y ω) with hadef
  have hfld : (zipLenDownArc γ ℓ (wedgeConfig γ B Y ω)).1 = rescale U (Qc γ) a := rfl
  rw [hfld] at hmem
  set Q := Qc γ with hQ
  set G : ℂ × ℝ → ℝ := fun p => F ((a : ℂ) * p.1, a * p.2) + (Q * Real.log a + 0) with hGdef
  have hmapsH : ∀ u ∈ Hbar, (a : ℂ) * u ∈ Hbar := fun u hu => by
    show 0 ≤ ((a : ℂ) * u).im
    rw [Complex.im_ofReal_mul]; exact mul_nonneg ha.le hu
  have hGc : ContinuousOn G (Hbar ×ˢ Ioi 0) := by
    have hm : Continuous fun p : ℂ × ℝ => ((a : ℂ) * p.1, a * p.2) := by fun_prop
    refine ContinuousOn.add ?_ continuousOn_const
    exact hF.1.comp hm.continuousOn fun p hp =>
      ⟨hmapsH _ hp.1, mul_pos ha (show (0 : ℝ) < p.2 from hp.2)⟩
  have hGx : ∀ u ∈ Hbar, ∀ r : ℝ, 0 < r →
      evalReg (rescale U Q a) (foldedCircle u r) = G (u, r) := by
    intro u hu r hr
    have hav : avgReg (rescale U Q a) = avgReg (addConst (rescale U Q a) 0) := by
      congr 1; funext μ; simp [addConst]
    rw [F1.evalReg_fc_of_avgReg_rescale ⟨F, hF⟩ Q ha 0 hav hu hr,
      hF.evalReg_fc_of_mem (hmapsH u hu) (mul_pos ha hr)]
  obtain ⟨C₁, hC₁, hb⟩ := growth_of_mem hGc hGx hmem (Rr / a)
  set L := |Real.log a| with hL
  refine ⟨C₁ * (1 + L) + |Q * Real.log a|, by positivity, fun z hz hzR ρ hρ hρR => ?_⟩
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hz' : z / a ∈ Hbar := by
    show 0 ≤ (z / (a : ℂ)).im
    rw [Complex.div_ofReal_im]; exact div_nonneg hz ha.le
  have hzn : ‖z / (a : ℂ)‖ ≤ Rr / a := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
    exact div_le_div_of_nonneg_right hzR ha.le
  have hρa : 0 < ρ / a := div_pos hρ ha
  have hρaR : ρ / a ≤ Rr / a := div_le_div_of_nonneg_right hρR ha.le
  have h1 := hb _ hz' hzn _ hρa hρaR
  have e1 : G (z / a, ρ / a) = F (z, ρ) + (Q * Real.log a + 0) := by
    simp only [hGdef]
    congr 2; field_simp
  rw [e1] at h1
  have hlog : |Real.log (ρ / a)| ≤ |Real.log ρ| + L := by
    rw [Real.log_div hρ.ne' ha.ne']
    exact (abs_sub _ _).trans le_rfl
  have hl0 : 0 ≤ |Real.log ρ| := abs_nonneg _
  have hL0 : 0 ≤ L := abs_nonneg _
  have h2 : |F (z, ρ)| ≤ |F (z, ρ) + (Q * Real.log a + 0)| + |Q * Real.log a| := by
    have := abs_sub (F (z, ρ) + (Q * Real.log a + 0)) (Q * Real.log a + 0)
    simp only [add_zero, add_sub_cancel_right] at this ⊢
    exact this
  have h3 : C₁ * (1 + |Real.log (ρ / a)|) ≤ C₁ * (1 + (|Real.log ρ| + L)) := by gcongr
  have hQ0 := abs_nonneg (Q * Real.log a)
  nlinarith [mul_nonneg hC₁ (mul_nonneg hl0 hL0), mul_nonneg hQ0 hl0]

end A1RG
end R18
end QuantumZipper
