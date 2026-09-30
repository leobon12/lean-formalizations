import QuantumZipper.Proofs.Zipper.E5PartsBIndep
import QuantumZipper.Proofs.Zipper.E5PartsBFlow
import QuantumZipper.Proofs.Zipper.E5PartsVague

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# E5-PARTSB, part 2: the germ-independent representation `E5LvlZoomPartsBStmt`

Task E5-PARTSB (Theorem 1.3, node E5, decisions D39/D40; Sheffield, arXiv:1012.4797, §5.4,
pp. 66–72, proof of Lemma 5.6: the germ-free part of the zoom data is a function of the level
collision time, the driver after the germ and the independent field).

Representation space `𝕍 = (ℝ × C([0,T], ℝ)) × Ω'` and
`V z = ((t, π), ω')`, where `t = T − T_ℓ` (`lvlTime`) and `π ∈ C([0,T], ℝ)` is the continuous
path `y ↦ D^{+u₀}((y − T + t − u₀)⁺)` built from the shifted germ `D^{+u₀} = shiftP u₀ D`
(`lvlPathB`). On `[0, max (t − u₀) 0]` the level driver equals `vrPath κ T π`
(`lvlDrv_eqOn_vrPath`, from `E5Final5d.lvlDrv_eqOn_shiftP`), so the germ-free correction `lvlGF`
equals the switched collision correction `gV` of the path parameter (`lvlGF_eq_gV`).

* `V` is measurable (`measurable_lvlVB`) and even measurable for `σ(t, ω', D^{+u₀})`, because the
  evaluations of `π` are evaluations of the continuous path `D^{+u₀}` at a `t`-measurable time
  (`StrongMarkov.measurable_randomTime_eval`); hence `V` is independent of the germ on `[0,u₀]`
  by `E5PartsBIndep.indepFun_lvl_germFree_data` (`indepFun_lvlVB`).
* On `𝕍` with the reference measure `δ_{(0,0)} ⊗ P'` the switched correction `gV` satisfies the
  D3⁺ `Setup` (`setup_gV`, via `E5IncSwitch.setup_locCorr_switch_reg` and the path-parameter flow
  measurability of `E5PartsBFlow`), and it is continuous for every parameter, so the local
  scale and local data are measurable (`E5PartsMeas`, `E5PartsVague.lvlZoomVague_holds`).

Main result: `e5LvlZoomPartsB_holds : E5LvlZoomPartsBStmt`. Own bookkeeping.
-/

noncomputable section
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace E5

open ESM LengthMarkov LengthMarkov.GermDensity StrongMarkov B2 E1 E4Grid D3Plus

/-! ## 1. The path parameter -/

/-- The continuous path `y ↦ d((y − T + τ₀)⁺)` on `[0, T]`. -/
def pathC (T τ₀ : ℝ) (d : ℝ≥0 → ℝ) (hd : Continuous d) : C(Icc (0 : ℝ) T, ℝ) :=
  ⟨fun y => d ((y.1 - T + τ₀).toNNReal), hd.comp (continuous_real_toNNReal.comp
    ((continuous_subtype_val.sub continuous_const).add continuous_const))⟩

theorem continuous_shiftP_e5b {d : ℝ≥0 → ℝ} (hd : Continuous d) (u₀ : ℝ≥0) :
    Continuous (shiftP u₀ d) :=
  (hd.comp (continuous_const.add continuous_id)).sub continuous_const

/-- **Measurability of the path parameter** built from a continuous path family at a measurable
time (for any σ-algebra on the source). -/
theorem measurable_pathData {α Ω' : Type} {mα : MeasurableSpace α} [MeasurableSpace Ω'] (T : ℝ)
    (u₀ : ℝ≥0) {t : α → ℝ} (ht : Measurable t) {d : α → ℝ≥0 → ℝ} (hdc : ∀ a, Continuous (d a))
    (hdm : ∀ s, Measurable fun a => d a s) {w : α → Ω'} (hw : Measurable w) :
    Measurable fun a => ((t a, pathC T (t a - u₀) (d a) (hdc a)), w a) := by
  refine (ht.prodMk (ContinuousMap.measurable_iff_eval.2 fun y => ?_)).prodMk hw
  exact measurable_randomTime_eval (B := fun s a => d a s) hdc hdm
    (measurable_real_toNNReal.comp (measurable_const.add (ht.sub_const _)))

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ T : ℝ} {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample} {ϖ : Measure ℂ}
  {Ω' : Type} [MeasurableSpace Ω']

/-- The path parameter at a level point. -/
def lvlPathB (κ T : ℝ) (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) (P : Measure Ω)
    (hBc : ∀ ω, Continuous (B · ω)) (u₀ : ℝ≥0) (p : ℝ≥0 × NullMeasurableSpace Ω P) :
    C(Icc (0 : ℝ) T, ℝ) :=
  pathC T (lvlTime κ T B X P p - u₀) (shiftP u₀ (esmGerm κ T B X P p))
    (continuous_shiftP_e5b (continuous_esmGerm hBc p) u₀)

/-- **The germ-free representation map** `V z = ((T − T_ℓ, π), ω')`. -/
def lvlVB (κ T : ℝ) (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) (P : Measure Ω) (Ω' : Type)
    (hBc : ∀ ω, Continuous (B · ω)) (u₀ : ℝ≥0) (z : lvl Ω P Ω') :
    (ℝ × C(Icc (0 : ℝ) T, ℝ)) × Ω' :=
  ((lvlTime κ T B X P z.1, lvlPathB κ T B X P hBc u₀ z.1), z.2)

theorem measurable_lvlVB (hS : E5.Setup κ T P B X ϖ) (hBc : ∀ ω, Continuous (B · ω))
    (u₀ : ℝ≥0) : Measurable (lvlVB κ T B X P Ω' hBc u₀) := by
  obtain ⟨hκ, hκ4, hT, hB, hX, hind, -⟩ := id hS
  have hG := measurable_esmGerm hκ hκ4 hT hB hX hind hBc
  exact measurable_pathData (Ω' := Ω') T u₀ ((measurable_lvlTime hS hBc).comp measurable_fst)
    (fun z : lvl Ω P Ω' => continuous_shiftP_e5b (continuous_esmGerm hBc z.1) u₀)
    (fun s => (((measurable_pi_apply _).comp hG).sub ((measurable_pi_apply _).comp hG)).comp
      measurable_fst) measurable_snd

/-- **`V` is independent of the germ on `[0, u₀]`.** -/
theorem indepFun_lvlVB (hS : E5.Setup κ T P B X ϖ) (hBc : ∀ ω, Continuous (B · ω))
    (hpos : esmMeas κ T B X P lvlMu univ ≠ 0) (P' : Measure Ω') [IsProbabilityMeasure P']
    (u₀ : ℝ≥0) :
    IndepFun (lvlVB κ T B X P Ω' hBc u₀) (fun z => pathRestr u₀ (esmGerm κ T B X P z.1))
      ((esmRr κ T B X P lvlMu).prod P') := by
  have hI := indepFun_lvl_germFree_data (P := P) hS hBc hpos P' u₀
  set f : lvl Ω P Ω' → (ℝ × Ω') × (ℝ≥0 → ℝ) := fun z =>
    ((lvlTime κ T B X P z.1, z.2), shiftP u₀ (esmGerm κ T B X P z.1)) with hfdef
  have hf : Measurable[MeasurableSpace.comap f inferInstance] f := comap_measurable f
  have hVm : Measurable[MeasurableSpace.comap f inferInstance] (lvlVB κ T B X P Ω' hBc u₀) :=
    measurable_pathData (mα := MeasurableSpace.comap f inferInstance) (Ω' := Ω') T u₀
      (t := fun z : lvl Ω P Ω' => (f z).1.1) (measurable_fst.comp (measurable_fst.comp hf))
      (d := fun z : lvl Ω P Ω' => (f z).2)
      (fun z : lvl Ω P Ω' => continuous_shiftP_e5b (continuous_esmGerm hBc z.1) u₀)
      (fun s => (measurable_pi_apply s).comp (measurable_snd.comp hf))
      (w := fun z : lvl Ω P Ω' => (f z).1.2) (measurable_snd.comp (measurable_fst.comp hf))
  have hle := measurable_iff_comap_le.1 hVm
  rw [IndepFun_iff_Indep] at hI ⊢
  exact indep_of_indep_of_le_left hI hle

/-! ## 2. The level driver is the path-parameter driver -/

theorem lvlDrv_eqOn_vrev_max (p : ℝ≥0 × NullMeasurableSpace Ω P) (u₀ : ℝ≥0) :
    EqOn (lvlDrv κ T B P p)
      (vrev (drvMap κ (shiftP u₀ (esmGerm κ T B X P p))) (lvlTime κ T B X P p - u₀))
      (Icc 0 (max (lvlTime κ T B X P p - u₀) 0)) := by
  intro s hs
  by_cases h : 0 ≤ lvlTime κ T B X P p - u₀
  · rw [max_eq_left h] at hs
    exact lvlDrv_eqOn_shiftP p u₀ hs
  · rw [max_eq_right (le_of_lt (not_le.1 h))] at hs
    have ha : lvlTime κ T B X P p - u₀ ≤ 0 := le_of_lt (not_le.1 h)
    have hs0 : s = 0 := le_antisymm hs.2 hs.1
    subst hs0
    have hL : Vr κ T B (ofCompl P p.2) 0 = 0 := by
      simp only [Vr, vrev, max_self]
      rcases le_total 0 T with hT | hT
      · rw [min_eq_left hT, sub_zero, sub_self]
      · rw [min_eq_right hT, sub_self]
        simp [drive, Real.toNNReal_of_nonpos hT]
    have hR : vrev (drvMap κ (shiftP u₀ (esmGerm κ T B X P p))) (lvlTime κ T B X P p - u₀) 0 =
        0 := by
      simp only [vrev, max_self, min_eq_right ha, sub_self]
      simp [drvMap, Real.toNNReal_of_nonpos ha]
    show Vr κ T B (ofCompl P p.2) 0 = _
    rw [hL, hR]

theorem lvlDrv_eqOn_vrPath (hT : 0 < T) (hBc : ∀ ω, Continuous (B · ω))
    (p : ℝ≥0 × NullMeasurableSpace Ω P) (u₀ : ℝ≥0) :
    EqOn (lvlDrv κ T B P p) (vrPath κ T hT.le (lvlPathB κ T B X P hBc u₀ p))
      (Icc 0 (max (lvlTime κ T B X P p - u₀) 0)) := by
  intro s hs
  rw [lvlDrv_eqOn_vrev_max p u₀ hs]
  set τ₀ := lvlTime κ T B X P p - u₀ with hτ₀
  have hτT : τ₀ ≤ T := by
    have h1 := NNReal.coe_nonneg (levelTime (lenA κ T B X) T.toNNReal p.1 (ofCompl P p.2))
    have h2 := NNReal.coe_nonneg u₀
    simp only [hτ₀, lvlTime]
    linarith
  set D := shiftP u₀ (esmGerm κ T B X P p) with hD
  by_cases h : 0 ≤ τ₀
  · rw [max_eq_left h] at hs
    have hsT : s ≤ T := hs.2.trans hτT
    have hm : T - s ∈ Icc (0 : ℝ) T := ⟨by linarith, by linarith [hs.1]⟩
    simp only [vrev, vrPath, lvlPathB, pathC, drvMap, ContinuousMap.coe_mk, max_eq_left hs.1,
      min_eq_left hs.2, min_eq_left hsT, ← hτ₀, ← hD]
    rw [Set.projIcc_of_mem hT.le hm, Set.projIcc_right]
    simp only
    rw [show T - s - T + τ₀ = τ₀ - s by ring, show T - T + τ₀ = τ₀ by ring]
  · rw [max_eq_right (le_of_lt (not_le.1 h))] at hs
    have hs0 : s = 0 := le_antisymm hs.2 hs.1
    subst hs0
    have ha : τ₀ ≤ 0 := le_of_lt (not_le.1 h)
    simp only [vrev, vrPath, drvMap, max_self, min_eq_right ha, min_eq_left hT.le, sub_self,
      sub_zero, Real.toNNReal_of_nonpos ha, Real.toNNReal_zero]

/-! ## 3. The switched correction of the path parameter -/

/-- The switched collision correction of the path parameter (germ-free, clipped time). -/
def gV (κ T : ℝ) (hT : 0 ≤ T) (ϖ ρ₀ : Measure ℂ) (X₁ : Ω' → FieldSample) (r' : ℝ) (u₀ : ℝ≥0) :
    (ℝ × C(Icc (0 : ℝ) T, ℝ)) × Ω' → ℂ → ℝ :=
  switchG (radiusBad (fun v : (ℝ × C(Icc (0 : ℝ) T, ℝ)) × Ω' =>
      varpiT (vrPath κ T hT v.1.2) (max (v.1.1 - u₀) 0) ϖ) r')
    (fun v => locCorr κ (vrPath κ T hT v.1.2) (max (v.1.1 - u₀) 0) ϖ ρ₀ (regField ϖ ρ₀ (X₁ v.2)))
    (fun _ _ => 0)

theorem lvlGF_eq_gV (hT : 0 < T) (hBc : ∀ ω, Continuous (B · ω)) (ρ₀ : Measure ℂ)
    (X₁ : Ω' → FieldSample) (r' : ℝ) (u₀ : ℝ≥0) (z : lvl Ω P Ω') :
    lvlGF P Ω' κ T B X ϖ ρ₀ X₁ r' u₀ z =
      gV κ T hT.le ϖ ρ₀ X₁ r' u₀ (lvlVB κ T B X P Ω' hBc u₀ z) := by
  classical
  have hE := lvlDrv_eqOn_vrPath (κ := κ) (X := X) hT hBc z.1 u₀
  have hv : varpiT (lvlDrv κ T B P z.1) (max (lvlTime κ T B X P z.1 - u₀) 0) ϖ =
      varpiT (vrPath κ T hT.le (lvlPathB κ T B X P hBc u₀ z.1))
        (max (lvlTime κ T B X P z.1 - u₀) 0) ϖ := by
    unfold varpiT
    rw [show revMap (lvlDrv κ T B P z.1) (max (lvlTime κ T B X P z.1 - u₀) 0) =
      revMap (vrPath κ T hT.le (lvlPathB κ T B X P hBc u₀ z.1))
        (max (lvlTime κ T B X P z.1 - u₀) 0) from
      funext fun w => ReverseFlow.revMap_congr_drive w hE]
  have hl := locCorr_congr_drive (κ := κ) hE ϖ ρ₀ (lvlField ϖ ρ₀ X₁ z)
  simp only [lvlGF, gV, switchG, Set.piecewise, radiusBad, Set.mem_setOf_eq, lvlVB]
  rw [hv, hl]
  rfl

theorem continuous_gV (hT : 0 ≤ T) (hϖ : IsNormalizer ϖ) (ρ₀ : Measure ℂ)
    (X₁ : Ω' → FieldSample) (r' : ℝ) (u₀ : ℝ≥0) (v : (ℝ × C(Icc (0 : ℝ) T, ℝ)) × Ω') :
    Continuous (gV κ T hT ϖ ρ₀ X₁ r' u₀ v) :=
  continuous_switchG_zero (continuous_locCorr ρ₀ _ hϖ (continuous_vrPath κ T hT v.1.2)
    (le_max_right _ _))

/-- **The D3⁺ `Setup` of the path-parameter correction** under `δ_{(0,0)} ⊗ P'`. -/
theorem setup_gV (hκ : 0 < κ) (hκ4 : κ < 4) (hT : 0 ≤ T) (hϖ : IsNormalizer ϖ)
    {P' : Measure Ω'} [IsProbabilityMeasure P'] {ρ₀ : Measure ℂ} {X₁ : Ω' → FieldSample}
    (hY : IsFreeGFFModConstH (fun ω' => regField ϖ ρ₀ (X₁ ω')) P')
    {r r' : ℝ} (hr : 0 < r) (hrr : r < r') (hρ₀ : IsAdmissibleH ρ₀) (hρ1 : ρ₀ Set.univ = 1)
    (hρr : ρ₀ (Metric.ball (0 : ℂ) r) = 0) (hρr' : ρ₀ (Metric.ball (0 : ℂ) r') = 0)
    (u₀ : ℝ≥0) :
    D3Plus.Setup (Real.sqrt κ) (Real.sqrt κ - 2 / Real.sqrt κ) r ρ₀
      ((Measure.dirac ((0, 0) : ℝ × C(Icc (0 : ℝ) T, ℝ))).prod P')
      (fun v : (ℝ × C(Icc (0 : ℝ) T, ℝ)) × Ω' => regField ϖ ρ₀ (X₁ v.2))
      (Prod.fst : (ℝ × C(Icc (0 : ℝ) T, ℝ)) × Ω' → ℝ × C(Icc (0 : ℝ) T, ℝ))
      (gV κ T hT ϖ ρ₀ X₁ r' u₀) := by
  have hbase : D3Plus.Setup (Real.sqrt κ) (Real.sqrt κ - 2 / Real.sqrt κ) r ρ₀
      ((Measure.dirac ((0, 0) : ℝ × C(Icc (0 : ℝ) T, ℝ))).prod P')
      (fun v : (ℝ × C(Icc (0 : ℝ) T, ℝ)) × Ω' => regField ϖ ρ₀ (X₁ v.2))
      (Prod.fst : (ℝ × C(Icc (0 : ℝ) T, ℝ)) × Ω' → ℝ × C(Icc (0 : ℝ) T, ℝ))
      (fun _ _ => 0) :=
    { hγ := Real.sqrt_pos.2 hκ
      hγ2 := (Real.sqrt_lt' two_pos).2 (by linarith)
      hα := by
        have hγ : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
        have hγ2 : Real.sqrt κ < 2 := (Real.sqrt_lt' two_pos).2 (by linarith)
        have h : 1 < 2 / Real.sqrt κ := (one_lt_div hγ).2 hγ2
        simp only [Qc]
        linarith
      hr := hr
      hX := isFreeGFFModConstH_snd_prod hY
      hΞ := measurable_fst
      hind := indep_fst_freeIncrSigma_snd hY
      hρ := hρ₀
      hρ1 := hρ1
      hρB := hρr
      harm := fun _ => InnerProductSpace.harmonicOnNhd_const 0
      gmeas := fun _ => measurable_const }
  have hτm : Measurable fun e : ℝ × C(Icc (0 : ℝ) T, ℝ) => max (e.1 - u₀) 0 :=
    (measurable_fst.sub_const _).max measurable_const
  have hfst : Measurable[MeasurableSpace.comap
      (Prod.fst : (ℝ × C(Icc (0 : ℝ) T, ℝ)) × Ω' → ℝ × C(Icc (0 : ℝ) T, ℝ)) inferInstance]
      (Prod.fst : (ℝ × C(Icc (0 : ℝ) T, ℝ)) × Ω' → ℝ × C(Icc (0 : ℝ) T, ℝ)) :=
    comap_measurable _
  exact setup_locCorr_switch_reg (X := fun v : (ℝ × C(Icc (0 : ℝ) T, ℝ)) × Ω' => X₁ v.2)
    hrr κ hbase hρr' hϖ (fun v => vrPath κ T hT v.1.2) (fun v => max (v.1.1 - u₀) 0)
    (fun v => continuous_vrPath κ T hT v.1.2) (fun _ => le_max_right _ _)
    (fun A hA => (measurable_varpiT_pg (κ := κ) hT hϖ measurable_snd hτm
      (fun _ => le_max_right _ _) hA).comp hfst)
    (fun z => (measurable_locCorrDrv_pg (κ := κ) hT hϖ measurable_snd hτm
      (fun _ => le_max_right _ _) z).comp hfst)

/-! ## 4. The germ-independent representation -/

/-- **Conjunct (b) of `E5LvlZoomParts3Stmt` holds.** -/
theorem e5LvlZoomPartsB_holds : E5LvlZoomPartsBStmt := by
  intro κ T Ω _ P _ B X ϖ hBc hS _ hpos w hw hw1 Ω' _ P' _ X₁ ρ₀ hX₁ hρ₀ hρ1 hX'g R r r' hr
    hrr hρr' u₀ _
  obtain ⟨hκ, hκ4, hT, hB, hX, hind, hϖ⟩ := id hS
  have hY := isFreeGFFModConstH_regField hX₁ hϖ hρ₀
  have hρr : ρ₀ (Metric.ball (0 : ℂ) r) = 0 :=
    measure_mono_null (Metric.ball_subset_ball hrr.le) hρr'
  have hS1 := setup_gV hκ hκ4 hT.le hϖ hY hr hrr hρ₀ hρ1 hρr hρr' u₀
  have hgood : ∀ (C : ℝ) (v : (ℝ × C(Icc (0 : ℝ) T, ℝ)) × Ω'), ∃ m,
      IsVagueLimitOn (D3Plus.halfDisc r) (areaApprox (Real.sqrt κ)
        (D3Plus.zoomModel (Real.sqrt κ) (Real.sqrt κ - 2 / Real.sqrt κ) C ρ₀
          (regField ϖ ρ₀ (X₁ v.2)) (gV κ T hT.le ϖ ρ₀ X₁ r' u₀ v))) m := fun C v =>
    lvlZoomVague_holds κ hκ hκ4 _ _ ρ₀ C r hr (continuous_gV hT.le hϖ ρ₀ X₁ r' u₀ v) (hX'g v.2)
  have hsc : ∀ C : ℝ, Measurable fun v : (ℝ × C(Icc (0 : ℝ) T, ℝ)) × Ω' =>
      zScale (Real.sqrt κ) (Real.sqrt κ - 2 / Real.sqrt κ) r ρ₀ C (regField ϖ ρ₀ (X₁ v.2))
        (gV κ T hT.le ϖ ρ₀ X₁ r' u₀ v) := fun C =>
    measurable_zScale_of_goodAll_e5p hS1 (hgood C)
  have hgm : Measurable fun q : ((ℝ × C(Icc (0 : ℝ) T, ℝ)) × Ω') × ℂ =>
      gV κ T hT.le ϖ ρ₀ X₁ r' u₀ q.1 q.2 := by
    have h := measurable_uncurry_of_continuous_of_measurable
      (u := fun (z : ℂ) (v : (ℝ × C(Icc (0 : ℝ) T, ℝ)) × Ω') => gV κ T hT.le ϖ ρ₀ X₁ r' u₀ v z)
      (fun v => continuous_gV hT.le hϖ ρ₀ X₁ r' u₀ v)
      (fun z => (hS1.gmeas z).mono (D3Plus.condSigma_le hS1) le_rfl)
    have h2 := h.comp measurable_swap
    simp only [Function.comp_def, Function.uncurry_def, Prod.fst_swap, Prod.snd_swap] at h2
    exact h2
  refine ⟨(ℝ × C(Icc (0 : ℝ) T, ℝ)) × Ω', inferInstance, lvlVB κ T B X P Ω' hBc u₀, ?_, ?_, ?_⟩
  · exact measurable_lvlVB hS hBc u₀
  · exact indepFun_lvlVB hS hBc hpos P' u₀
  refine ⟨fun C v => zScale (Real.sqrt κ) (Real.sqrt κ - 2 / Real.sqrt κ) r ρ₀ C
      (regField ϖ ρ₀ (X₁ v.2)) (gV κ T hT.le ϖ ρ₀ X₁ r' u₀ v),
    fun C v => zLoc D3Plus.locFieldFull (Real.sqrt κ) (Real.sqrt κ - 2 / Real.sqrt κ) r ρ₀ R C
      (regField ϖ ρ₀ (X₁ v.2)) (gV κ T hT.le ϖ ρ₀ X₁ r' u₀ v), hsc, fun C => ?_,
    fun C z => ⟨?_, ?_⟩⟩
  · exact measurable_zLoc_of_scale_e5p R (measurable_coords_zoomModel_e5p _ _ C ρ₀
      (fun μ => hS1.hX.measurable_coord μ) hgm) (hsc C)
  · rw [lvlGF_eq_gV hT hBc ρ₀ X₁ r' u₀ z]
    rfl
  · rw [lvlGF_eq_gV hT hBc ρ₀ X₁ r' u₀ z]
    rfl

end E5
end QuantumZipper
