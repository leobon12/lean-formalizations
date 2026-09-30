import QuantumZipper.Proofs.Thm18.G3ZqO2Trunc

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G3PATH-G1 (3): the one-window Palm limit from the core

**`g3ZqO1PathEpsStmt_of_core : G3ZqO2CoreStmt → G3ZqO1PathEpsStmt`**, hence
**`g1WedgePalmLimStmt_of_core : G3ZqL1ResclIdStmt → G3ZqO2CoreStmt → G1WedgePalmLimStmt`**.

Choice of the window (before the path): first `U = 1/(n+1)` so small that the quarter segment of
the unscaled wedge has boundary mass `≤ U` with probability `≤ e` (the mass is a.s. positive,
`ae_wedgeU_bdry`); then `η = 1/(m+5)` so small that `E min(U, ν(0, η)) ≤ e U` (dominated
convergence; `ν` is finite near the root and `⋂ (0, η) = ∅`). With the window mass exactly `U`
(`window_facts`) the full functional differs from the core functional by at most `2 e U` in
expectation, and the core mass `E ν(W ∩ T)` is within `2 e U` of `U`.

Sheffield, arXiv:1012.4797, pp. 70–71. Own elementary bookkeeping (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G3ZqO

open G3Z2b2 D3Plus G1Zm G3Zq G3ZqL Factorization

/-- The boundary measure of the unscaled wedge is a.e.-measurable in the sample. -/
theorem aemeasurable_bdryM_wedgeU (γ : ℝ) {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {X : Ω' → FieldSample} {A : ℝ → Ω' → ℝ}
    (hcu : AEMeasurable (fun ω' => coords (wedgeU γ X A ω')) P') :
    AEMeasurable (fun ω' => bdryM γ (wedgeU γ X A ω')) P' := by
  refine (((measurable_bdryM γ).comp measurable_reconstruct).comp_aemeasurable hcu).congr
    (ae_of_all _ fun ω' => ?_)
  exact R18.bdryM_congr (avgReg_reconstruct_coords _)

/-- `ν(0, 1/(n+5)) → 0` for a measure finite on compact intervals. -/
theorem tendsto_measure_nearSet (μ : Measure ℝ) (hfin : μ (Icc (-1) 1) ≠ ⊤) (left : Bool) :
    Tendsto (fun n : ℕ => μ (nearSet left (1 / ((n : ℝ) + 5)))) atTop (𝓝 0) := by
  have hanti : Antitone fun n : ℕ => nearSet left (1 / ((n : ℝ) + 5)) := by
    intro n m hnm
    have h : 1 / ((m : ℝ) + 5) ≤ 1 / ((n : ℝ) + 5) :=
      one_div_le_one_div_of_le (by positivity)
        (by have := (Nat.cast_le (α := ℝ)).2 hnm; linarith)
    cases left
    · exact Ioo_subset_Ioo_right h
    · exact Ioo_subset_Ioo_left (neg_le_neg h)
  have hsub : ∀ n : ℕ, nearSet left (1 / ((n : ℝ) + 5)) ⊆ Icc (-1) 1 := by
    intro n x hx
    have h1 : 1 / ((n : ℝ) + 5) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
    cases left
    · simp only [nearSet, Bool.false_eq_true, ite_false, mem_Ioo] at hx
      exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
    · simp only [nearSet, ite_true, mem_Ioo] at hx
      exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hempty : (⋂ n : ℕ, nearSet left (1 / ((n : ℝ) + 5))) = ∅ := by
    ext x
    simp only [mem_iInter, mem_empty_iff_false, iff_false, not_forall]
    cases left
    · by_cases hx : 0 < x
      · obtain ⟨n, hn⟩ := exists_nat_one_div_lt hx
        refine ⟨n, fun h => ?_⟩
        simp only [nearSet, Bool.false_eq_true, ite_false, mem_Ioo] at h
        have : 1 / ((n : ℝ) + 5) ≤ 1 / ((n : ℝ) + 1) :=
          one_div_le_one_div_of_le (by positivity) (by linarith)
        linarith [h.2]
      · refine ⟨0, fun h => ?_⟩
        simp only [nearSet, Bool.false_eq_true, ite_false, mem_Ioo] at h
        exact hx h.1
    · by_cases hx : x < 0
      · obtain ⟨n, hn⟩ := exists_nat_one_div_lt (neg_pos.2 hx)
        refine ⟨n, fun h => ?_⟩
        simp only [nearSet, ite_true, mem_Ioo] at h
        have : 1 / ((n : ℝ) + 5) ≤ 1 / ((n : ℝ) + 1) :=
          one_div_le_one_div_of_le (by positivity) (by linarith)
        linarith [h.1]
      · refine ⟨0, fun h => ?_⟩
        simp only [nearSet, ite_true, mem_Ioo] at h
        exact hx h.2
  have h := tendsto_measure_iInter_atTop (μ := μ)
    (fun n => (measurableSet_nearSet left _).nullMeasurableSet) hanti
    ⟨0, ne_top_of_le_ne_top hfin (measure_mono (hsub 0))⟩
  rwa [hempty, measure_empty] at h

/-- **The one-window fixed-path limit from the core node.** -/
theorem g3ZqO1PathEpsStmt_of_core (hC : G3ZqO2CoreStmt) : G3ZqO1PathEpsStmt := by
  intro γ hγ hγ2 Ψ hsel Ω' _ P' _ X A hX hA hXA Ω'' _ P'' _ Y'' hW Ω _ P _ B hB left R Γ hΓ hΓ1
    ε hε
  set c := ∫⁻ ω'', Γ (locFieldFull R (Y'' ω'')) ∂P'' with hcdef
  have hc1 : c ≤ 1 := by
    calc c ≤ ∫⁻ _ω'', (1 : ℝ≥0∞) ∂P'' := lintegral_mono fun ω'' => hΓ1 _
      _ = 1 := by simp
  -- the error size
  set e : ℝ≥0∞ := min ε 1 / 4 with he
  have he0 : 0 < e := ENNReal.div_pos (lt_min hε one_pos).ne' (by norm_num)
  have he3 : e + (e + e) ≤ ε := by
    have h4 : e * 4 = min ε 1 := ENNReal.div_mul_cancel (by norm_num) (by norm_num)
    calc e + (e + e) ≤ e + (e + e) + e := le_self_add
      _ = e * 4 := by ring
      _ ≤ ε := by rw [h4]; exact min_le_left _ _
  have hcu : AEMeasurable (fun ω' => coords (wedgeU γ X A ω')) P' :=
    WedgeMeas.aemeasurable_coords_wedgeField hX.measurable_coord hA
  have hν := aemeasurable_bdryM_wedgeU γ hcu
  set ν : Ω' → Measure ℝ := fun ω' => bdryM γ (wedgeU γ X A ω') with hνdef
  have hfacts := ae_wedgeU_bdry hγ hγ2 hX hA hXA
  have hseg : MeasurableSet (g1SideSeg left (quarterPt left)) := by
    cases left <;> simp [g1SideSeg, measurableSet_Icc]
  -- step 1: the window length `U`
  set S : ℕ → Set Ω' := fun n => {ω' | ν ω' (g1SideSeg left (quarterPt left)) ≤
    ENNReal.ofReal (1 / ((n : ℝ) + 1))} with hSdef
  have hSm : ∀ n, NullMeasurableSet (S n) P' := fun n =>
    hν.nullMeasurable (measurableSet_le (Measure.measurable_coe hseg) measurable_const)
  have hSanti : Antitone S := by
    intro n m hnm ω' hω'
    refine le_trans hω' (ENNReal.ofReal_le_ofReal ?_)
    exact one_div_le_one_div_of_le (by positivity)
      (by have := (Nat.cast_le (α := ℝ)).2 hnm; linarith)
  have hSnull : P' (⋂ n, S n) = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hfacts] with ω' ⟨h1, h2, h3, h4⟩ hmem
    have hpos := (window_facts h1 h2 h3 h4 left (U := 1) zero_le_one).2
    have hle : ν ω' (g1SideSeg left (quarterPt left)) ≤ 0 := by
      have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
        have := ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat
        simpa using this
      exact ge_of_tendsto' hlim fun n => mem_iInter.1 hmem n
    exact (lt_irrefl _ (hpos.trans_le hle))
  have hSlim := tendsto_measure_iInter_atTop (μ := P') hSm hSanti ⟨0, measure_ne_top _ _⟩
  rw [hSnull] at hSlim
  obtain ⟨n, hn⟩ := ((ENNReal.tendsto_nhds_zero.1 hSlim) e he0).exists
  set U : ℝ := 1 / ((n : ℝ) + 1) with hUdef
  have hU : 0 < U := by positivity
  have hU0 : ENNReal.ofReal U ≠ 0 := by simpa using hU
  have hUt : ENNReal.ofReal U ≠ ⊤ := ENNReal.ofReal_ne_top
  have heU : 0 < e * ENNReal.ofReal U := ENNReal.mul_pos he0.ne' hU0
  -- step 2: the core radius `η`
  set g : ℕ → Ω' → ℝ≥0∞ := fun m ω' =>
    min (ENNReal.ofReal U) (ν ω' (nearSet left (1 / ((m : ℝ) + 5)))) with hgdef
  have hglim : Tendsto (fun m => ∫⁻ ω', g m ω' ∂P') atTop (𝓝 0) := by
    have h0 : (0 : ℝ≥0∞) = ∫⁻ _ω', 0 ∂P' := by simp
    rw [h0]
    refine tendsto_lintegral_filter_of_dominated_convergence' (fun _ => ENNReal.ofReal U)
      (Eventually.of_forall fun m => (measurable_const.min
        (Measure.measurable_coe (measurableSet_nearSet left _))).comp_aemeasurable hν)
      (Eventually.of_forall fun m => Eventually.of_forall fun ω' => min_le_left _ _)
      (by simp) ?_
    refine ae_of_all _ fun ω' => ?_
    have hfin : ν ω' (Icc (-1) 1) ≠ ⊤ := R18.bdryM_Icc_ne_top γ _ _ _
    have h := (tendsto_const_nhds (x := ENNReal.ofReal U)).min
      (tendsto_measure_nearSet (ν ω') hfin left)
    rw [min_eq_right zero_le] at h
    exact h
  obtain ⟨m, hm⟩ := ((ENNReal.tendsto_nhds_zero.1 hglim) (e * ENNReal.ofReal U) heU).exists
  set η : ℝ := 1 / ((m : ℝ) + 5) with hηdef
  have hη : 0 < η := by positivity
  have hη4 : η < 1 / 4 := by
    rw [hηdef]
    exact one_div_lt_one_div_of_lt (by norm_num) (by linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)])
  -- the expected truncation error
  set D : ℝ≥0∞ := ∫⁻ ω', truncErr left U η (ν ω') ∂P' with hDdef
  have hDm : AEMeasurable (fun ω' => truncErr left U η (ν ω')) P' :=
    (measurable_truncErr left U η).comp_aemeasurable hν
  have hD : D ≤ (e + e) * ENNReal.ofReal U := by
    have hsplit : D = ∫⁻ ω', g m ω' ∂P' + ∫⁻ ω', (if ν ω' (g1SideSeg left (quarterPt left)) ≤
        ENNReal.ofReal U then ENNReal.ofReal U else 0) ∂P' := by
      rw [hDdef]
      exact lintegral_add_left' ((measurable_const.min
        (Measure.measurable_coe (measurableSet_nearSet left _))).comp_aemeasurable hν) _
    have h2 : ∫⁻ ω', (if ν ω' (g1SideSeg left (quarterPt left)) ≤ ENNReal.ofReal U
        then ENNReal.ofReal U else 0) ∂P' ≤ ENNReal.ofReal U * e := by
      have e2 : (fun ω' => if ν ω' (g1SideSeg left (quarterPt left)) ≤ ENNReal.ofReal U
          then ENNReal.ofReal U else 0) = (S n).indicator fun _ => ENNReal.ofReal U := by
        funext ω'
        simp only [indicator, hSdef, mem_setOf_eq, hUdef]
      rw [e2]
      exact (lintegral_indicator_const_le _ _).trans (mul_le_mul' le_rfl hn)
    rw [hsplit]
    calc ∫⁻ ω', g m ω' ∂P' + _ ≤ e * ENNReal.ofReal U + ENNReal.ofReal U * e := add_le_add hm h2
      _ = (e + e) * ENNReal.ofReal U := by ring
  -- the window mass
  have hWU : ∀ᵐ ω' ∂P', ν ω' (winSet γ left U (wedgeU γ X A ω')) = ENNReal.ofReal U := by
    filter_upwards [hfacts] with ω' ⟨h1, h2, h3, h4⟩
    exact (window_facts h1 h2 h3 h4 left hU.le).1
  set M : ℝ≥0∞ := ∫⁻ ω', winCore γ left U η (wedgeU γ X A ω') ∂P' with hMdef
  have hMU : M ≤ ENNReal.ofReal U := by
    calc M ≤ ∫⁻ _ω', ENNReal.ofReal U ∂P' := lintegral_mono fun ω' =>
          (measure_mono inter_subset_left).trans (measure_g1Win_le _ left _)
      _ = ENNReal.ofReal U := by simp
  have hUM : ENNReal.ofReal U ≤ M + D := by
    calc ENNReal.ofReal U = ∫⁻ ω', ν ω' (winSet γ left U (wedgeU γ X A ω')) ∂P' := by
          rw [lintegral_congr_ae hWU]; simp
      _ ≤ ∫⁻ ω', (winCore γ left U η (wedgeU γ X A ω') + truncErr left U η (ν ω')) ∂P' := by
          refine lintegral_mono fun ω' => ?_
          exact (measure_le_inter_add_sdiff _ _ (coreSet left η)).trans
            (add_le_add le_rfl (measure_winDiff_le γ left U η _))
      _ = M + D := lintegral_add_right' _ hDm
  -- step 3: the core
  refine ⟨U, hU, ?_⟩
  filter_upwards [hC γ hγ hγ2 Ψ hsel P' X A hX hA hXA P'' Y'' hW P B hB left R Γ hΓ hΓ1 U hU η
    hη hη4] with a ha hac hsc
  filter_upwards [ha hac hsc (e * ENNReal.ofReal U) heU] with L hL
  set I := ∫⁻ ω', g1PhiM γ L R Γ Ψ left U (wedgeU γ X A ω', a) ∂P' with hIdef
  set J := ∫⁻ ω', g1PhiT γ L R Γ Ψ left U η (wedgeU γ X A ω', a) ∂P' with hJdef
  have hIJ : I ≤ J + D := by
    calc I ≤ ∫⁻ ω', (g1PhiT γ L R Γ Ψ left U η (wedgeU γ X A ω', a) +
          truncErr left U η (ν ω')) ∂P' := by
          refine lintegral_mono fun ω' => ?_
          exact (g1PhiM_le_phiT_add hsel L R hΓ hΓ1 left U η _).trans
            (add_le_add le_rfl (measure_winDiff_le γ left U η _))
      _ = J + D := lintegral_add_right' _ hDm
  have hJI : J ≤ I := lintegral_mono fun ω' => g1PhiT_le_g1PhiM _
  have hcancel : ∀ x : ℝ≥0∞, (ENNReal.ofReal U)⁻¹ * (x * ENNReal.ofReal U) = x := by
    intro x
    rw [mul_comm x, ← mul_assoc, ENNReal.inv_mul_cancel hU0 hUt, one_mul]
  constructor
  · have h1 : I ≤ (c + (e + (e + e))) * ENNReal.ofReal U := by
      calc I ≤ J + D := hIJ
        _ ≤ (c * M + e * ENNReal.ofReal U) + (e + e) * ENNReal.ofReal U := add_le_add hL.1 hD
        _ ≤ (c * ENNReal.ofReal U + e * ENNReal.ofReal U) + (e + e) * ENNReal.ofReal U :=
            add_le_add (add_le_add (mul_le_mul' le_rfl hMU) le_rfl) le_rfl
        _ = (c + (e + (e + e))) * ENNReal.ofReal U := by ring
    calc (ENNReal.ofReal U)⁻¹ * I ≤ (ENNReal.ofReal U)⁻¹ * ((c + (e + (e + e))) *
          ENNReal.ofReal U) := mul_le_mul' le_rfl h1
      _ = c + (e + (e + e)) := hcancel _
      _ ≤ c + ε := add_le_add le_rfl he3
  · have h1 : c * ENNReal.ofReal U ≤ I + (e + (e + e)) * ENNReal.ofReal U := by
      calc c * ENNReal.ofReal U ≤ c * (M + D) := mul_le_mul' le_rfl hUM
        _ = c * M + c * D := mul_add _ _ _
        _ ≤ (J + e * ENNReal.ofReal U) + D :=
            add_le_add hL.2 (mul_le_of_le_one_left zero_le hc1)
        _ ≤ (I + e * ENNReal.ofReal U) + (e + e) * ENNReal.ofReal U :=
            add_le_add (add_le_add hJI le_rfl) hD
        _ = I + (e + (e + e)) * ENNReal.ofReal U := by ring
    calc c = (ENNReal.ofReal U)⁻¹ * (c * ENNReal.ofReal U) := (hcancel c).symm
      _ ≤ (ENNReal.ofReal U)⁻¹ * (I + (e + (e + e)) * ENNReal.ofReal U) := mul_le_mul' le_rfl h1
      _ = (ENNReal.ofReal U)⁻¹ * I + (e + (e + e)) := by rw [mul_add, hcancel]
      _ ≤ (ENNReal.ofReal U)⁻¹ * I + ε := add_le_add le_rfl he3

/-- **`G1WedgePalmLimStmt` from the rescaling identity and the core node.** -/
theorem g1WedgePalmLimStmt_of_core (hId : G3ZqL1ResclIdStmt) (hC : G3ZqO2CoreStmt) :
    G1WedgePalmLimStmt :=
  g1WedgePalmLimStmt_of_pathEps hId (g3ZqO1PathEpsStmt_of_core hC)

end G3ZqO
end Thm18Asm
end QuantumZipper
