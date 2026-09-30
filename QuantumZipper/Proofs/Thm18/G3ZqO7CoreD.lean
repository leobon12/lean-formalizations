import QuantumZipper.Proofs.Thm18.G3ZqO6Shift
import QuantumZipper.Proofs.Thm18.G3ZqO3Wire

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G3PATH-G1 (7): the core limit from the core limit with the shifted window condition

**`g3ZqO2CoreStmt_of_coreD : G3ZqO6CoreDStmt → G3ZqO2CoreStmt`** and hence
**`g1WedgePalmLimStmt_of_coreD : G3ZqL1ResclIdStmt → G3ZqO6CoreDStmt → G1WedgePalmLimStmt`**.

With `δ_k = η/(k+3)`, the error mass `ν(T ∩ (winD δ_k \ winSet))` tends to `0` a.s. (the sets
decrease to `∅` because `ν[0, x) = sup_k ν[0, x − δ_k]` and `ν` has no atoms), and in expectation
by dominated convergence with the integrable bound `ν(T)` (`lintegral_bdryM_core_lt_top`). Both
the functional and the core mass move by at most this error when the window condition is shifted.

Own elementary bookkeeping (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G3ZqO

open G3Z2b2 D3Plus G1Zm G3Zq G3ZqL Factorization

variable {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ}

/-- The shifts `δ_k = η/(k+3)`. -/
def dk (η : ℝ) (k : ℕ) : ℝ := η / ((k : ℝ) + 3)

theorem dk_pos {η : ℝ} (hη : 0 < η) (k : ℕ) : 0 < dk η k := by unfold dk; positivity

theorem dk_lt {η : ℝ} (hη : 0 < η) (k : ℕ) : dk η k < η / 2 := by
  unfold dk
  exact div_lt_div_of_pos_left hη (by norm_num) (by linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)])

theorem dk_anti {η : ℝ} (hη : 0 < η) : Antitone (dk η) := by
  intro k k' hkk'
  unfold dk
  exact div_le_div_of_nonneg_left hη.le (by positivity)
    (by have := (Nat.cast_le (α := ℝ)).2 hkk'; linarith)

theorem exists_dk_lt {η : ℝ} (hη : 0 < η) {s : ℝ} (hs : 0 < s) : ∃ k : ℕ, dk η k < s := by
  obtain ⟨k, hk⟩ := exists_nat_gt (η / s)
  refine ⟨k, ?_⟩
  unfold dk
  rw [div_lt_iff₀ (by positivity)]
  rw [div_lt_iff₀ hs] at hk
  nlinarith

theorem winD_mono (γ : ℝ) (left : Bool) (U : ℝ) {δ δ' : ℝ} (h : δ' ≤ δ) (y : FieldSample) :
    winD γ left U δ' y ⊆ winD γ left U δ y := by
  intro x hx
  refine ⟨hx.1, le_trans (measure_mono ?_) hx.2⟩
  cases left
  · simp only [g1SideSeg, shPt, Bool.false_eq_true, ite_false]
    exact Icc_subset_Icc_right (by linarith)
  · simp only [g1SideSeg, shPt, ite_true]
    exact Icc_subset_Icc_left (by linarith)

/-- **The error sets decrease to `∅`** for an atomless measure. -/
theorem iInter_errSet_eq_empty {γ : ℝ} {y : FieldSample} (hat : ∀ t : ℝ, bdryM γ y {t} = 0)
    (left : Bool) (U : ℝ) {η : ℝ} (hη : 0 < η) :
    (⋂ k : ℕ, errSet γ left U η (dk η k) y) = ∅ := by
  set μ := bdryM γ y
  ext x
  simp only [mem_iInter, mem_empty_iff_false, iff_false, not_forall]
  by_contra hall
  push_neg at hall
  have hD : ∀ k : ℕ, μ (g1SideSeg left (shPt left (dk η k) x)) ≤ ENNReal.ofReal U :=
    fun k => (hall k).2.1.2
  have hside : x ∈ g1SideHalf left := (hall 0).2.1.1
  have hnot : ¬ μ (g1SideSeg left x) ≤ ENNReal.ofReal U := fun h => (hall 0).2.2 ⟨hside, h⟩
  apply hnot
  cases left
  · simp only [g1SideHalf, Bool.false_eq_true, ite_false, mem_Ioi] at hside
    simp only [g1SideSeg, shPt, Bool.false_eq_true, ite_false] at hD ⊢
    have hmono : Monotone fun k : ℕ => Icc (0 : ℝ) (x - dk η k) := fun k k' h =>
      Icc_subset_Icc_right (by linarith [dk_anti hη h])
    have hU : μ (⋃ k : ℕ, Icc (0 : ℝ) (x - dk η k)) ≤ ENNReal.ofReal U := by
      rw [hmono.measure_iUnion]; exact iSup_le hD
    have hsub : Icc 0 x ⊆ {x} ∪ ⋃ k : ℕ, Icc (0 : ℝ) (x - dk η k) := by
      intro t ht
      rcases eq_or_lt_of_le ht.2 with h | h
      · exact Or.inl h
      · obtain ⟨k, hk⟩ := exists_dk_lt hη (sub_pos.2 h)
        exact Or.inr (mem_iUnion.2 ⟨k, ht.1, by linarith⟩)
    calc μ (Icc 0 x) ≤ μ {x} + μ (⋃ k : ℕ, Icc (0 : ℝ) (x - dk η k)) :=
          (measure_mono hsub).trans (measure_union_le _ _)
      _ ≤ ENNReal.ofReal U := by rw [hat, zero_add]; exact hU
  · simp only [g1SideHalf, ite_true, mem_Iio] at hside
    simp only [g1SideSeg, shPt, ite_true] at hD ⊢
    have hmono : Monotone fun k : ℕ => Icc (x + dk η k) (0 : ℝ) := fun k k' h =>
      Icc_subset_Icc_left (by linarith [dk_anti hη h])
    have hU : μ (⋃ k : ℕ, Icc (x + dk η k) (0 : ℝ)) ≤ ENNReal.ofReal U := by
      rw [hmono.measure_iUnion]; exact iSup_le hD
    have hsub : Icc x 0 ⊆ {x} ∪ ⋃ k : ℕ, Icc (x + dk η k) (0 : ℝ) := by
      intro t ht
      rcases eq_or_lt_of_le ht.1 with h | h
      · exact Or.inl h.symm
      · obtain ⟨k, hk⟩ := exists_dk_lt hη (sub_pos.2 h)
        exact Or.inr (mem_iUnion.2 ⟨k, by linarith, ht.2⟩)
    calc μ (Icc x 0) ≤ μ {x} + μ (⋃ k : ℕ, Icc (x + dk η k) (0 : ℝ)) :=
          (measure_mono hsub).trans (measure_union_le _ _)
      _ ≤ ENNReal.ofReal U := by rw [hat, zero_add]; exact hU

/-- The core is a closed interval of finite boundary mass. -/
theorem bdryM_coreSet_ne_top (γ : ℝ) (y : FieldSample) (left : Bool) (η : ℝ) :
    bdryM γ y (coreSet left η) ≠ ⊤ := by
  cases left <;> simp only [coreSet, Bool.false_eq_true, ite_false, ite_true] <;>
    exact R18.bdryM_Icc_ne_top γ y _ _

/-- **The error mass tends to `0`** for an atomless boundary measure. -/
theorem tendsto_errMass {γ : ℝ} {y : FieldSample} (hat : ∀ t : ℝ, bdryM γ y {t} = 0)
    (left : Bool) (U : ℝ) {η : ℝ} (hη : 0 < η) :
    Tendsto (fun k : ℕ => bdryM γ y (errSet γ left U η (dk η k) y)) atTop (𝓝 0) := by
  have hanti : Antitone fun k : ℕ => errSet γ left U η (dk η k) y := by
    intro k k' h x hx
    exact ⟨hx.1, winD_mono γ left U (dk_anti hη h) y hx.2.1, hx.2.2⟩
  have h := tendsto_measure_iInter_atTop (μ := bdryM γ y)
    (fun k => (measurableSet_errSet γ left U η (dk η k) y).nullMeasurableSet) hanti
    ⟨0, ne_top_of_le_ne_top (bdryM_coreSet_ne_top γ y left η)
      (measure_mono inter_subset_left)⟩
  rwa [iInter_errSet_eq_empty hat left U hη, measure_empty] at h

/-- The truncated functional is below the shifted one. -/
theorem g1PhiT_le_g1PhiD {γ L : ℝ} {R : ℕ} {Γ : (ℕ → ℝ) × (TestFun H → ℝ) → ℝ≥0∞}
    {left : Bool} {U η δ : ℝ} (hδ : 0 ≤ δ) (p : FieldSample × (ℝ≥0 → ℝ)) :
    g1PhiT γ L R Γ Ψ left U η p ≤ g1PhiD γ L R Γ Ψ left U η δ p := by
  classical
  refine lintegral_mono fun x => ?_
  by_cases hT : x ∈ coreSet left η
  · rw [indicator_of_mem hT]
    unfold g1IntM
    split_ifs with h
    · rw [indicator_of_mem (show x ∈ coreSet left η ∩ winD γ left U δ p.1 from
        ⟨hT, winSet_subset_winD γ left U hδ p.1 h⟩)]
    · exact bot_le
  · rw [indicator_of_notMem hT]; exact bot_le

/-- The shifted functional is at most the truncated one plus the error mass. -/
theorem g1PhiD_le {γ : ℝ} (hsel : G1PsiSel γ Ψ) (L : ℝ) (R : ℕ)
    {Γ : (ℕ → ℝ) × (TestFun H → ℝ) → ℝ≥0∞} (hΓ : Measurable Γ) (hΓ1 : ∀ y, Γ y ≤ 1)
    (left : Bool) (U η δ : ℝ) (p : FieldSample × (ℝ≥0 → ℝ)) :
    g1PhiD γ L R Γ Ψ left U η δ p ≤ g1PhiT γ L R Γ Ψ left U η p +
      bdryM γ p.1 (errSet γ left U η δ p.1) := by
  classical
  have hm : Measurable fun x => (coreSet left η).indicator
      (fun x => g1IntM γ L R Γ Ψ left U (p, x)) x :=
    ((measurable_g1IntM hsel L R hΓ left U).comp (measurable_const.prodMk measurable_id)).indicator
      (measurableSet_coreSet left η)
  have hpt : ∀ x, (coreSet left η ∩ winD γ left U δ p.1).indicator
      (fun x => Γ (g1zLocData R (g1zM γ L Ψ left (p, x)))) x ≤
      (coreSet left η).indicator (fun x => g1IntM γ L R Γ Ψ left U (p, x)) x +
        (errSet γ left U η δ p.1).indicator 1 x := by
    intro x
    by_cases hx : x ∈ coreSet left η ∩ winD γ left U δ p.1
    · rw [indicator_of_mem hx, indicator_of_mem hx.1]
      by_cases hw : x ∈ winSet γ left U p.1
      · have e : g1IntM γ L R Γ Ψ left U (p, x) =
            Γ (g1zLocData R (g1zM γ L Ψ left (p, x))) := by
          unfold g1IntM; exact if_pos hw
        rw [e]; exact le_self_add
      · rw [indicator_of_mem (show x ∈ errSet γ left U η δ p.1 from ⟨hx.1, hx.2, hw⟩)]
        exact (hΓ1 _).trans le_add_self
    · rw [indicator_of_notMem hx]; exact bot_le
  calc g1PhiD γ L R Γ Ψ left U η δ p
      ≤ ∫⁻ x, ((coreSet left η).indicator (fun x => g1IntM γ L R Γ Ψ left U (p, x)) x +
          (errSet γ left U η δ p.1).indicator 1 x) ∂(bdryM γ p.1) := lintegral_mono hpt
    _ = g1PhiT γ L R Γ Ψ left U η p + ∫⁻ x, (errSet γ left U η δ p.1).indicator 1 x
          ∂(bdryM γ p.1) := lintegral_add_left hm _
    _ = _ := by rw [lintegral_indicator_one (measurableSet_errSet γ left U η δ p.1)]

theorem winCore_le_winCoreD (γ : ℝ) (left : Bool) (U η : ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    (y : FieldSample) : winCore γ left U η y ≤ winCoreD γ left U η δ y :=
  measure_mono (inter_subset_inter_left _ (winSet_subset_winD γ left U hδ y))

theorem winCoreD_le (γ : ℝ) (left : Bool) (U η δ : ℝ) (y : FieldSample) :
    winCoreD γ left U η δ y ≤ winCore γ left U η y + bdryM γ y (errSet γ left U η δ y) := by
  refine (measure_mono ?_).trans (measure_union_le _ _)
  intro x hx
  by_cases hw : x ∈ winSet γ left U y
  · exact Or.inl ⟨hw, hx.2⟩
  · exact Or.inr ⟨hx.2, hx.1, hw⟩

/-- **The core limit from the core limit with the shifted window condition.** -/
theorem g3ZqO2CoreStmt_of_coreD (hD : G3ZqO6CoreDStmt) : G3ZqO2CoreStmt := by
  intro γ hγ hγ2 Ψ hsel Ω' _ P' _ X A hX hA hXA Ω'' _ P'' _ Y'' hW Ω _ P _ B hB left R Γ hΓ hΓ1
    U hU η hη hη4
  set c := ∫⁻ ω'', Γ (locFieldFull R (Y'' ω'')) ∂P'' with hcdef
  have hc1 : c ≤ 1 := by
    calc c ≤ ∫⁻ _ω'', (1 : ℝ≥0∞) ∂P'' := lintegral_mono fun ω'' => hΓ1 _
      _ = 1 := by simp
  have hcu : AEMeasurable (fun ω' => coords (wedgeU γ X A ω')) P' :=
    WedgeMeas.aemeasurable_coords_wedgeField hX.measurable_coord hA
  have hfacts := ae_wedgeU_bdry hγ hγ2 hX hA hXA
  set Er : ℕ → Ω' → ℝ≥0∞ := fun k ω' =>
    bdryM γ (wedgeU γ X A ω') (errSet γ left U η (dk η k) (wedgeU γ X A ω')) with hErdef
  have hErm : ∀ k, AEMeasurable (Er k) P' := by
    intro k
    refine (((measurable_errMass γ left U η (dk η k)).comp
      measurable_reconstruct).comp_aemeasurable hcu).congr (ae_of_all _ fun ω' => ?_)
    have hb : bdryM γ (reconstruct (coords (wedgeU γ X A ω'))) = bdryM γ (wedgeU γ X A ω') :=
      R18.bdryM_congr (avgReg_reconstruct_coords _)
    simp only [Function.comp, hErdef, errSet, winD, winSet, hb]
  have hgfin := (lintegral_bdryM_core_lt_top hγ hγ2 P' X A hX hA hXA left hη hη4).ne
  have hErlim : Tendsto (fun k => ∫⁻ ω', Er k ω' ∂P') atTop (𝓝 0) := by
    have h0 : (0 : ℝ≥0∞) = ∫⁻ _ω', 0 ∂P' := by simp
    rw [h0]
    refine tendsto_lintegral_filter_of_dominated_convergence'
      (fun ω' => bdryM γ (wedgeU γ X A ω') (coreSet left η)) (Eventually.of_forall hErm)
      (Eventually.of_forall fun k => Eventually.of_forall fun ω' =>
        measure_mono inter_subset_left) hgfin ?_
    filter_upwards [hfacts] with ω' hω'
    exact tendsto_errMass hω'.1 left U hη
  have hpathD := ae_all_iff.2 fun k : ℕ => hD γ hγ hγ2 Ψ hsel P' X A hX hA hXA P'' Y'' hW P B hB
    left R Γ hΓ hΓ1 U hU η hη hη4 (dk η k) (dk_pos hη k) (dk_lt hη k)
  filter_upwards [hpathD] with a ha hac hsc e he
  have he4 : 0 < e / 4 := ENNReal.div_pos he.ne' (by norm_num)
  have hee : e / 4 + e / 4 ≤ e := by
    have h4 : e / 4 * 4 = e := ENNReal.div_mul_cancel (by norm_num) (by norm_num)
    calc e / 4 + e / 4 ≤ e / 4 + e / 4 + (e / 4 + e / 4) := le_self_add
      _ = e / 4 * 4 := by ring
      _ = e := h4
  obtain ⟨k, hk⟩ := ((ENNReal.tendsto_nhds_zero.1 hErlim) (e / 4) he4).exists
  filter_upwards [ha k hac hsc (e / 4) he4] with L hL
  have hδ0 : 0 ≤ dk η k := (dk_pos hη k).le
  have hJJD : ∫⁻ ω', g1PhiT γ L R Γ Ψ left U η (wedgeU γ X A ω', a) ∂P' ≤
      ∫⁻ ω', g1PhiD γ L R Γ Ψ left U η (dk η k) (wedgeU γ X A ω', a) ∂P' :=
    lintegral_mono fun ω' => g1PhiT_le_g1PhiD hδ0 _
  have hJDJ : ∫⁻ ω', g1PhiD γ L R Γ Ψ left U η (dk η k) (wedgeU γ X A ω', a) ∂P' ≤
      ∫⁻ ω', g1PhiT γ L R Γ Ψ left U η (wedgeU γ X A ω', a) ∂P' + ∫⁻ ω', Er k ω' ∂P' :=
    (lintegral_mono fun ω' => g1PhiD_le hsel L R hΓ hΓ1 left U η (dk η k) _).trans_eq
      (lintegral_add_right' _ (hErm k))
  have hMMD : ∫⁻ ω', winCore γ left U η (wedgeU γ X A ω') ∂P' ≤
      ∫⁻ ω', winCoreD γ left U η (dk η k) (wedgeU γ X A ω') ∂P' :=
    lintegral_mono fun ω' => winCore_le_winCoreD γ left U η hδ0 _
  have hMDM : ∫⁻ ω', winCoreD γ left U η (dk η k) (wedgeU γ X A ω') ∂P' ≤
      ∫⁻ ω', winCore γ left U η (wedgeU γ X A ω') ∂P' + ∫⁻ ω', Er k ω' ∂P' :=
    (lintegral_mono fun ω' => winCoreD_le γ left U η (dk η k) _).trans_eq
      (lintegral_add_right' _ (hErm k))
  have hcE : c * ∫⁻ ω', Er k ω' ∂P' ≤ e / 4 := (mul_le_of_le_one_left zero_le hc1).trans hk
  constructor
  · calc ∫⁻ ω', g1PhiT γ L R Γ Ψ left U η (wedgeU γ X A ω', a) ∂P'
        ≤ ∫⁻ ω', g1PhiD γ L R Γ Ψ left U η (dk η k) (wedgeU γ X A ω', a) ∂P' := hJJD
      _ ≤ c * ∫⁻ ω', winCoreD γ left U η (dk η k) (wedgeU γ X A ω') ∂P' + e / 4 := hL.1
      _ ≤ c * (∫⁻ ω', winCore γ left U η (wedgeU γ X A ω') ∂P' + ∫⁻ ω', Er k ω' ∂P') + e / 4 :=
          add_le_add (mul_le_mul' le_rfl hMDM) le_rfl
      _ = c * ∫⁻ ω', winCore γ left U η (wedgeU γ X A ω') ∂P' +
            c * ∫⁻ ω', Er k ω' ∂P' + e / 4 := by rw [mul_add]
      _ ≤ c * ∫⁻ ω', winCore γ left U η (wedgeU γ X A ω') ∂P' + e / 4 + e / 4 :=
          add_le_add (add_le_add le_rfl hcE) le_rfl
      _ = c * ∫⁻ ω', winCore γ left U η (wedgeU γ X A ω') ∂P' + (e / 4 + e / 4) := by ring
      _ ≤ c * ∫⁻ ω', winCore γ left U η (wedgeU γ X A ω') ∂P' + e := add_le_add le_rfl hee
  · calc c * ∫⁻ ω', winCore γ left U η (wedgeU γ X A ω') ∂P'
        ≤ c * ∫⁻ ω', winCoreD γ left U η (dk η k) (wedgeU γ X A ω') ∂P' :=
          mul_le_mul' le_rfl hMMD
      _ ≤ ∫⁻ ω', g1PhiD γ L R Γ Ψ left U η (dk η k) (wedgeU γ X A ω', a) ∂P' + e / 4 := hL.2
      _ ≤ (∫⁻ ω', g1PhiT γ L R Γ Ψ left U η (wedgeU γ X A ω', a) ∂P' +
            ∫⁻ ω', Er k ω' ∂P') + e / 4 := add_le_add hJDJ le_rfl
      _ ≤ (∫⁻ ω', g1PhiT γ L R Γ Ψ left U η (wedgeU γ X A ω', a) ∂P' + e / 4) + e / 4 :=
          add_le_add (add_le_add le_rfl hk) le_rfl
      _ = ∫⁻ ω', g1PhiT γ L R Γ Ψ left U η (wedgeU γ X A ω', a) ∂P' + (e / 4 + e / 4) := by ring
      _ ≤ ∫⁻ ω', g1PhiT γ L R Γ Ψ left U η (wedgeU γ X A ω', a) ∂P' + e := add_le_add le_rfl hee

/-- **`G1WedgePalmLimStmt` from the rescaling identity and the shifted-window core node.** -/
theorem g1WedgePalmLimStmt_of_coreD (hId : G3ZqL1ResclIdStmt) (hD : G3ZqO6CoreDStmt) :
    G1WedgePalmLimStmt :=
  g1WedgePalmLimStmt_of_core hId (g3ZqO2CoreStmt_of_coreD hD)

end G3ZqO
end Thm18Asm
end QuantumZipper
