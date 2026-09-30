import QuantumZipper.Proofs.Thm18.G1SSRDefs
import QuantumZipper.Proofs.Thm18.R18G1ArcReg
import QuantumZipper.Proofs.Thm18.G1ZA1aAff
import QuantumZipper.Proofs.Zipper.F1PStarShiftRegDet
import QuantumZipper.Proofs.Zipper.RegShiftUnifBasic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1SSR (2): the area-only shifted regularity from the continuum limit at the pushed circles

Theorem 1.8, G1 zoom, node B2-C. Sheffield, arXiv:1012.4797, proof of Proposition 1.7
(pp. 25–26); the regularity facts are the coordinate change at a map independent of the field
(Duplantier–Sheffield, Invent. Math. 185 (2011), Prop. 2.1; Sheffield (1.3)).

`G1SideShiftRegAStmt` (D89, G1SSRDefs.lean) is derived from

* the proved a.s. core regularity of the side field (`g1RegRepRestStmt_holds`, transported to the
  chosen uniformizer by `G1.choiceRegularCore_invFunOn_of_normalized`),
* the area node of the side field (`G1Z2SideGoodStmt`, its area clause),
* the positivity of the scale parameter of `Y + C` (`canonConfig_shift_facts`),
* the new node `G1SidePushContStmt`: a.s. the circle-smoothed pairings of `Y` against every pushed
  folded circle `ψ_* fc(d, r)` of the side map converge as the smoothing radius tends to `0`
  (`F1.ContData`; the continuum smoothing limit of Duplantier–Sheffield 2011 Prop. 3.1 at a map
  independent of the field, as in `G1RC.exists_pushed_limit`).

The deterministic part (`shiftRegA_of_det`) is own bookkeeping: `RegShift` from the continuum limit
(`F1.regShift_of_contData`), so `coordChange (y + C) ψ Q` agrees with `coordChange y ψ Q + C` at
every folded circle; regularity, RC3, PAIR-LIM and the area limit pass to the shifted field (rule
(5.1)); scale consistency at the scaled dilated chart from the continuum limit
(`G1.scaleConsistentAt_of_continuum`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm

open D3Plus Factorization CoordsFull

/-- **Node: continuum limit of the smoothed pairings of `Y` at the pushed circles of the side map.** -/
def G1SidePushContStmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    Thm18Setting γ P B Y → Thm18Inputs γ P B Y → ∀ left : Bool, ∀ᵐ ω ∂P,
      ∀ d : ℂ, ∀ r > 0,
        F1.ContData (Y ω) ((foldedCircle d r).map (g1zSideMap left (drive (γ ^ 2) B ω)))

/-- The continuum limit passes to a field whose circle values differ by a constant on `ℍ̄`. -/
theorem g1ssr_contData_shift {x x' : FieldSample} {C : ℝ} {m : Measure ℂ} [IsFiniteMeasure m]
    (hm : ∀ᵐ u ∂m, u ∈ Hbar)
    (heq : ∀ u ∈ Hbar, ∀ ρ : ℝ, 0 < ρ →
      evalReg x' (foldedCircle u ρ) = evalReg x (foldedCircle u ρ) + C)
    (h : F1.ContData x m) : F1.ContData x' m := by
  obtain ⟨hint, L, hL⟩ := h
  have hae : ∀ ρ : ℝ, 0 < ρ → (fun u => evalReg x' (foldedCircle u ρ)) =ᵐ[m]
      fun u => evalReg x (foldedCircle u ρ) + C := fun ρ hρ =>
    hm.mono fun u hu => heq u hu ρ hρ
  refine ⟨fun ρ hρ => ((hint ρ hρ).add (integrable_const C)).congr (hae ρ hρ).symm,
    L + m.real univ * C, ?_⟩
  refine (hL.add_const (m.real univ * C)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ρ (hρ : 0 < ρ)
  rw [integral_congr_ae (hae ρ hρ), integral_add (hint ρ hρ) (integrable_const C),
    integral_const, smul_eq_mul]

/-- `HasAreaLimit` depends on the field only through `avgReg` (local copy). -/
theorem g1ssr_hasAreaLimit_congr {γ : ℝ} {x x' : FieldSample} (h : avgReg x = avgReg x')
    {μ : Measure ℂ} (hμ : HasAreaLimit γ x μ) : HasAreaLimit γ x' μ := by
  have hb : ∀ r, areaR γ x r = areaR γ x' r := fun r => by
    unfold areaR areaDens
    simp_rw [Factorization.evalReg_congr h]
  refine ⟨hμ.1, hμ.2.1, fun f hf hfc hfS => ?_⟩
  simp_rw [← hb]
  exact hμ.2.2 f hf hfc hfS

/-- Small balls about `0` carry small mass, for a measure finite on one of them. -/
theorem g1ssr_small_ball {μ : Measure ℂ} {a₀ : ℝ} (ha₀ : 0 < a₀)
    (h₀ : μ (Metric.ball (0 : ℂ) a₀ ∩ H) < 1) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ a : ℝ, 0 < a ∧ μ (Metric.ball (0 : ℂ) a ∩ H) < ε := by
  set s : ℕ → Set ℂ := fun n => Metric.ball (0 : ℂ) (a₀ / ((n : ℝ) + 1)) ∩ H with hs
  have hanti : Antitone s := fun m n hmn => inter_subset_inter_left _ (Metric.ball_subset_ball
    (div_le_div_of_nonneg_left ha₀.le (by positivity) (by
      have : (m : ℝ) ≤ n := by exact_mod_cast hmn
      linarith)))
  have hmeas : ∀ n, NullMeasurableSet (s n) μ := fun n =>
    (Metric.isOpen_ball.inter isOpen_H).measurableSet.nullMeasurableSet
  have hfin : ∃ n, μ (s n) ≠ ⊤ := ⟨0, by
    have e : s 0 = Metric.ball (0 : ℂ) a₀ ∩ H := by simp [hs]
    rw [e]; exact (h₀.trans ENNReal.one_lt_top).ne⟩
  have hempty : (⋂ n, s n) = ∅ := by
    refine eq_empty_iff_forall_notMem.2 fun z hz => ?_
    have hz0 : z ∈ H := (mem_iInter.1 hz 0).2
    have hpos : 0 < ‖z‖ := norm_pos_iff.2 fun h => by
      have : (0 : ℝ) < z.im := hz0
      rw [h] at this; simp at this
    obtain ⟨n, hn⟩ := exists_nat_gt (a₀ / ‖z‖)
    have hmem := (mem_iInter.1 hz n).1
    rw [Metric.mem_ball, dist_zero_right] at hmem
    have h1 : a₀ < ‖z‖ * ((n : ℝ) + 1) := by
      rw [div_lt_iff₀ hpos] at hn; nlinarith
    have h2 : a₀ / ((n : ℝ) + 1) < ‖z‖ := by
      rw [div_lt_iff₀ (by positivity)]; exact h1
    linarith
  have ht := tendsto_measure_iInter_atTop hmeas hanti hfin
  rw [hempty, measure_empty] at ht
  obtain ⟨n, hn⟩ := (ht.eventually (gt_mem_nhds hε)).exists
  exact ⟨a₀ / ((n : ℝ) + 1), by positivity, hn⟩

/-- **The area-only shifted regularity, deterministic form.** -/
theorem shiftRegA_of_det {γ : ℝ} {y : FieldSample} (hy : IsRegularSample y) {ψ : ℂ → ℂ}
    (hψm : Measurable ψ) (hψH : ∀ w ∈ H, ψ w ∈ Hbar) (hcore : G1.ChoiceRegularCore γ y ψ)
    {μ : Measure ℂ} (hμ : HasAreaLimit γ (coordChange y ψ (Qc γ)) μ)
    (hsmall : ∃ a : ℝ, 0 < a ∧ μ (Metric.ball (0 : ℂ) a ∩ H) < 1) (htop : μ H = ⊤)
    (hN : ∀ d : ℂ, ∀ r > 0, F1.ContData y ((foldedCircle d r).map ψ)) (C : ℝ)
    (hs : 0 < scaleParam γ (addConst y C)) : ShiftRegA γ y C ψ := by
  set x := coordChange y ψ (Qc γ) with hxdef
  set xC := coordChange (addConst y C) ψ (Qc γ) with hxCdef
  obtain ⟨F, hF⟩ := hcore.1
  obtain ⟨Fy, hFy⟩ := hy
  have hpush : ∀ d : ℂ, ∀ r > 0, ∀ᵐ u ∂((foldedCircle d r).map ψ), u ∈ Hbar := fun d r hr =>
    (ae_map_iff hψm.aemeasurable isClosed_Hbar.measurableSet).2
      ((TwoPoint.foldedCircle_ae_mem_H d hr).mono fun w hw => hψH w hw)
  have hRS : ∀ d : ℂ, ∀ r > 0, E1.RegShift y ((foldedCircle d r).map ψ) := fun d r hr =>
    F1.regShift_of_contData ⟨Fy, hFy⟩ (hpush d r hr) (hN d r hr)
  have hfc : ∀ d : ℂ, ∀ r > 0, xC (foldedCircle d r) = addConst x C (foldedCircle d r) :=
    fun d r hr => by
      rw [hxCdef, F2.coordChange_addConst_fc C (hRS d r hr)]
      simp [addConst, hxdef]
  have havg : avgReg xC = avgReg (addConst x C) := by
    funext k w
    unfold avgReg
    congr 1
    funext n
    exact hfc _ _ (radius_pos k)
  have hFC : IsRegularWith xC (fun q => F q + C) :=
    RegUnif.isRegularWith_of_raw_eq (fun n k z => hfc _ _ (radius_pos k)) (hF.addConst' C)
  have hshx : ∀ u ∈ Hbar, ∀ ρ : ℝ, 0 < ρ →
      evalReg xC (foldedCircle u ρ) = evalReg x (foldedCircle u ρ) + C := fun u hu ρ hρ => by
    rw [hFC.evalReg_fc_of_mem hu hρ, hF.evalReg_fc_of_mem hu hρ]
  have hshy : ∀ u ∈ Hbar, ∀ ρ : ℝ, 0 < ρ →
      evalReg (addConst y C) (foldedCircle u ρ) = evalReg y (foldedCircle u ρ) + C :=
    fun u hu ρ hρ => by
      rw [(hFy.addConst' C).evalReg_fc_of_mem hu hρ, hFy.evalReg_fc_of_mem hu hρ]
  -- RC3 of the shifted side field
  have hex : ∀ d ∈ Hbar, ∀ r > 0, evalReg xC (foldedCircle d r) = xC (foldedCircle d r) := by
    intro d hd r hr
    have hxfc : x (foldedCircle d r) = F (d, r) := by
      rw [hxdef, ← hcore.2.1 d hd r hr, hF.evalReg_fc_of_mem hd hr]
    rw [hFC.evalReg_fc_of_mem hd hr, hfc d r hr]
    simp [addConst, hxfc]
  -- PAIR-LIM of the shifted side field
  have hpair : ∀ c : ℝ, 0 < c → ∀ ρ : TestFun H, ∀ σ : ℂ → ℝ, (σ = ρ.1 ∨ σ = fun z => -ρ.1 z) →
      F1.ContData xC ((G1.tmeas σ).map fun z => (c : ℂ) * z) := by
    intro c hc ρ σ hσ
    obtain ⟨hsm, hsc, hsH⟩ := ρ.2
    have hσc : Continuous σ ∧ HasCompactSupport σ ∧ tsupport σ ⊆ H := by
      rcases hσ with rfl | rfl
      · exact ⟨hsm.continuous, hsc, hsH⟩
      · exact ⟨hsm.continuous.neg, hsc.neg, by
          rw [show (fun z => -ρ.1 z) = -ρ.1 from rfl, tsupport_neg]; exact hsH⟩
    obtain ⟨hσ1, hσ2, hσ3⟩ := hσc
    have := G1.isFiniteMeasure_tmeas hσ1 hσ2
    exact g1ssr_contData_shift (G1.ae_tmeas_map_mem_Hbar hσ1 hσ3 hc) hshx
      (hcore.2.2 c hc ρ σ hσ)
  have hcoreC : G1.ChoiceRegularCore γ (addConst y C) ψ := ⟨⟨_, hFC⟩, hex, hpair⟩
  -- the area limit of the shifted side field
  set cst : ℝ≥0∞ := ENNReal.ofReal (Real.exp (γ * C)) with hcst
  have hc0 : cst ≠ 0 := by
    rw [hcst, Ne, ENNReal.ofReal_eq_zero, not_le]; exact Real.exp_pos _
  have hcT : cst ≠ ⊤ := ENNReal.ofReal_ne_top
  have hμC : HasAreaLimit γ xC (cst • μ) := by
    have h1 := GoodSample.hasAreaLimit_add_ofFun ⟨F, hF⟩ hμ (φ := fun _ => C) continuousOn_const
    rw [← GoodSample.addConst_eq_add_ofFun, withDensity_const] at h1
    exact g1ssr_hasAreaLimit_congr havg.symm h1
  -- positivity of its scale parameter
  obtain ⟨a₀, ha₀, h₀⟩ := hsmall
  have hε : 0 < ENNReal.ofReal (Real.exp (-(γ * C))) := ENNReal.ofReal_pos.2 (Real.exp_pos _)
  obtain ⟨a, ha, hlt⟩ := g1ssr_small_ball ha₀ h₀ hε
  have hsmallC : (cst • μ) (Metric.ball ((0 : ℝ) : ℂ) a ∩ H) < 1 := by
    rw [Complex.ofReal_zero, Measure.smul_apply, smul_eq_mul]
    calc cst * μ (Metric.ball (0 : ℂ) a ∩ H) < cst * ENNReal.ofReal (Real.exp (-(γ * C))) :=
          ENNReal.mul_lt_mul_right hc0 hcT hlt
      _ = 1 := by
          rw [hcst, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, add_neg_cancel,
            Real.exp_zero, ENNReal.ofReal_one]
  have htopC : (cst • μ) H = ⊤ := by
    rw [Measure.smul_apply, smul_eq_mul, htop, ENNReal.mul_top hc0]
  obtain ⟨-, hbig⟩ := g1z2_translate_mass 0 ⟨a, ha, hsmallC⟩ htopC
  have hmap : ((cst • μ).map fun z : ℂ => z - ((0 : ℝ) : ℂ)) = cst • μ := by
    simp only [Complex.ofReal_zero, sub_zero, Measure.map_id']
  rw [hmap] at hbig
  have hsC : 0 < scaleParam γ xC := by
    refine g1z2_scaleParam_pos ⟨_, hFC⟩ hμC ⟨a, ha, ?_⟩ hbig
    simpa using hsmallC
  refine ⟨⟨⟨_, hFC⟩, hex, ⟨_, hμC⟩, hsC, fun b hb c hc ρ σ hσ =>
    G1ZA1b.g1za1b_scaleConsistent_of_core hcoreC hb hc ρ σ hσ⟩, hRS, ?_⟩
  -- scale consistency of `y + C` at the scaled dilated chart
  intro b hb d r hr
  set s := scaleParam γ (addConst y C) with hsdef
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hm : Measurable (fun w : ℂ => (s : ℂ)⁻¹ * ψ ((b : ℂ) * w)) :=
    measurable_const.mul (hψm.comp (measurable_const_mul _))
  have hν : ∀ᵐ u ∂((foldedCircle d r).map fun w => (s : ℂ)⁻¹ * ψ ((b : ℂ) * w)), u ∈ Hbar := by
    refine (ae_map_iff hm.aemeasurable isClosed_Hbar.measurableSet).2
      ((TwoPoint.foldedCircle_ae_mem_H d hr).mono fun w hw => ?_)
    have h1 := hψH _ (G1.mul_mem_H hb hw)
    have h2 := RegClosure.mapsTo_mul_pos (inv_pos.2 hs) h1
    have e : (s : ℂ)⁻¹ * ψ ((b : ℂ) * w) = ((s⁻¹ : ℝ) : ℂ) * ψ ((b : ℂ) * w) := by
      push_cast; ring
    show (s : ℂ)⁻¹ * ψ ((b : ℂ) * w) ∈ Hbar
    rw [e]; exact h2
  have hmap2 : ((foldedCircle d r).map fun w => (s : ℂ)⁻¹ * ψ ((b : ℂ) * w)).map
      (fun z => (s : ℂ) * z) = (foldedCircle ((b : ℂ) * d) (b * r)).map ψ := by
    rw [Measure.map_map (measurable_const_mul _) hm, ← WedgeTK.fc_map_mul d r hb,
      Measure.map_map hψm (measurable_const_mul _)]
    congr 1
    funext w
    simp only [Function.comp_apply]
    exact mul_inv_cancel_left₀ hs' _
  have hbr : 0 < b * r := mul_pos hb hr
  obtain ⟨hi, L, hL⟩ := g1ssr_contData_shift (hpush _ _ hbr) hshy (hN _ _ hbr)
  exact G1.scaleConsistentAt_of_continuum (x := addConst y C) ⟨_, hFy.addConst' C⟩ (Qc γ) hs hν
    (L := L) (fun ρ hρ => by rw [hmap2]; exact hi ρ hρ) (by rw [hmap2]; exact hL)

/-- **`G1SideShiftRegAStmt` from the side area node and the pushed-circle continuum limit.** -/
theorem g1SideShiftRegAStmt_of_pushCont (hZ2 : G1Z2SideGoodStmt) (hN : G1SidePushContStmt) :
    G1SideShiftRegAStmt := by
  intro γ Ω _ P _ B Y hS hIn left C
  have hR : G1RegExSide γ P B Y left := by
    have := g1RegExStmt_of_rest g1RegRepRestStmt_holds γ P B Y hS hIn
    cases left
    · exact this.2
    · exact this.1
  obtain ⟨hpos, -, -, -⟩ := canonConfig_shift_facts hS C
  filter_upwards [hpos, hR, hZ2 γ P B Y hS hIn left, hN γ P B Y hS hIn left, hIn.1, hIn.2.2]
    with ω hs hRω hZω hNω hYω hin
  obtain ⟨φ, hφ, hcore⟩ := hRω
  have hU : IsNormalizedUniformizer (sideDom (sleTrace (γ ^ 2) B ω) left)
      (uniformizer (sideDom (sleTrace (γ ^ 2) B ω) left)) := by
    cases left
    · exact hin.2.2.2
    · exact hin.2.2.1
  have hcore' := G1.choiceRegularCore_invFunOn_of_normalized hin.1 left hφ hU hcore
  obtain ⟨-, -, hψm, hψD⟩ := G1.invFunOn_props (G1.isOpen_component hin.1 left) hU
  obtain ⟨⟨μ, hμ, hsm, htop⟩, -⟩ := hZω _ hU
  have hsmall : ∃ a : ℝ, 0 < a ∧ μ (Metric.ball (0 : ℂ) a ∩ H) < 1 := by
    obtain ⟨a, ha, h⟩ := hsm 0
    exact ⟨a, ha, by simpa using h⟩
  have hψH : ∀ w ∈ H, invFunOn (uniformizer (sideDom (sleTrace (γ ^ 2) B ω) left))
      (sideDom (sleTrace (γ ^ 2) B ω) left) w ∈ Hbar := fun w hw => by
    have h1 := G1ZA1a.sideDom_subset_H _ left (hψD hw)
    simp only [H, Hbar, Set.mem_ofPred_eq] at h1 ⊢
    exact h1.le
  exact shiftRegA_of_det hYω.1.1 hψm hψH hcore' hμ hsmall htop hNω C hs

end Thm18Asm
end QuantumZipper
