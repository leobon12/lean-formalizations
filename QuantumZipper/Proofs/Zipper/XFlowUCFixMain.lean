import QuantumZipper.Proofs.Zipper.XFlowUCFix

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# XFLOW-UC: the six-parameter Kolmogorov step and the fixed-driver `Γ⁰` node

* `exists_contMod_flow`: a continuous modification of `q ↦ X(μ_{ptQ q, rhQ q})` on `ℝ⁶`
  (`KolmN.exists_continuous_modification_N` with `d = 6`; Revuz–Yor, 3rd ed., Ch. I, Thm (2.1));
  the pattern is `RegUnif.exists_contMod_US`.
* `xFlowFixedUCQAllStmt_of`: `FlowEnergyStmt → FlowAdmStmt → FlowIdentStmt → FlowDetStmt →
  XFlowFixedUCQAllStmt` (the pattern is `RegUnif.fixedUCStmt_of_id_det`).
* `xFlowUCStmt_of_nodes`: hence `XFlowUCStmt` from the four nodes and the log node
  `XFlowLogUCStmt` (proved separately as `xFlowLogUCStmt_holds`, `XFlowUCLog.lean`).

Own bookkeeping (as D33).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal

namespace QuantumZipper
namespace F1

open RegCont TwoPoint GFFExist RegUnif

/-- **Continuous modification of the six-parameter Gaussian family.** -/
theorem exists_contMod_flow {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → FieldSample} (hX : IsFreeGFFModConstH X P) (hA : FlowAdmStmt) {m : ℕ}
    {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {K c : ℝ} (hK : 0 ≤ K) (hc : 0 < c)
    (hE : ∀ p ∈ flowBox m, ∀ p' ∈ flowBox m, ∀ ρ ∈ Icc (0 : ℝ) 1, ∀ ρ' ∈ Icc (0 : ℝ) 1,
      |kernelCov2 neumannH (flowMu W p ρ, flowMu W p' ρ') (flowMu W p ρ, flowMu W p' ρ')| ≤
        K * (dist p p' + |ρ - ρ'|) ^ c) :
    ∃ Y : (Fin 6 → ℝ) → Ω → ℝ, (∀ ω, Continuous fun q => Y q ω) ∧
      ∀ q, (fun ω => Y q ω) =ᵐ[P] fun ω => X ω (flowMu W (ptQ m q) (rhQ q)) := by
  have hEq : ∀ q q' : Fin 6 → ℝ,
      |kernelCov2 neumannH (flowMu W (ptQ m q) (rhQ q), flowMu W (ptQ m q') (rhQ q'))
        (flowMu W (ptQ m q) (rhQ q), flowMu W (ptQ m q') (rhQ q'))| ≤
        (K * 3 ^ c) * ‖q - q'‖ ^ c := by
    intro q q'
    refine (hE _ (ptQ_mem m q) _ (ptQ_mem m q') _ (rhQ_mem q) _ (rhQ_mem q')).trans ?_
    have h1 : dist (ptQ m q) (ptQ m q') + |rhQ q - rhQ q'| ≤ 3 * ‖q - q'‖ := by
      linarith [dist_ptQ_le m q q', abs_rhQ_sub_le q q']
    have h2 := Real.rpow_le_rpow (add_nonneg dist_nonneg (abs_nonneg _)) h1 hc.le
    calc K * (dist (ptQ m q) (ptQ m q') + |rhQ q - rhQ q'|) ^ c
        ≤ K * (3 * ‖q - q'‖) ^ c := mul_le_mul_of_nonneg_left h2 hK
      _ = (K * 3 ^ c) * ‖q - q'‖ ^ c := by
        rw [Real.mul_rpow (by norm_num) (norm_nonneg _)]; ring
  set n : ℕ := ⌈6 / c⌉₊ + 1 with hn
  have hmc : ((6 : ℕ) : ℝ) < (n : ℝ) * c := by
    have h1 : 6 / c ≤ (⌈6 / c⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (6 / c) * c = 6 := div_mul_cancel₀ _ hc.ne'
    rw [hn]; push_cast
    nlinarith
  set g := gaussianAbsMoment (2 * n) with hg
  have hg0 : 0 ≤ g := gaussianAbsMoment_nonneg _
  have hK3 : 0 ≤ K * 3 ^ c := by positivity
  obtain ⟨Y, hY, hYZ, -⟩ := KolmN.exists_continuous_modification_N (d := 6)
    (Z := fun q ω => X ω (flowMu W (ptQ m q) (rhQ q))) (P := P)
    (fun q => (hX.measurable_coord _).aemeasurable) (p := 2 * n) (by omega) hmc
    (fun R => ⟨(K * 3 ^ c) ^ n * g, by positivity, fun q _ q' _ => by
      obtain ⟨hA1, hmA⟩ := hA W hW hW0 _ (flowBox_subset_flowPar m (ptQ_mem m q)) _
        (rhQ_mem q)
      obtain ⟨hB1, hmB⟩ := hA W hW hW0 _ (flowBox_subset_flowPar m (ptQ_mem m q')) _
        (rhQ_mem q')
      refine (lintegral_pow_diff_le hX hA1 hB1 (hmA.trans hmB.symm) n (hEq q q')).trans ?_
      refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
      rw [mul_pow, ← Real.rpow_natCast (‖q - q'‖ ^ c), ← Real.rpow_mul (norm_nonneg _), hg,
        mul_comm c]
      ring⟩)
  exact ⟨Y, hY, hYZ⟩

/-- **The fixed-driver `Γ⁰` node from the energy, admissibility, identity and deterministic
nodes.** -/
theorem xFlowFixedUCQAllStmt_of (hE : FlowEnergyStmt) (hA : FlowAdmStmt) (hID : FlowIdentStmt)
    (hD : FlowDetStmt) : XFlowFixedUCQAllStmt := by
  intro κ hκ hκ4 Ω _ P _ X hX m W a CH hWH
  have hWH' := hWH
  obtain ⟨hW, hW0, -, -, -, -⟩ := hWH'
  obtain ⟨K, c, hK, hc, hEn⟩ := hE m W a CH hWH
  obtain ⟨Y, hYc, hYZ⟩ := exists_contMod_flow hX hA hW hW0 hK hc hEn
  have hgood : ∀ᵐ ω ∂P, ∀ x : (ℚ × ℚ × ℚ × ℚ × ℚ) × ℕ, flowQ x.1 ∈ flowBox m →
      flowPhiY κ (X ω) W x.2 (flowQ x.1) =
          X ω (flowMu W (flowQ x.1) (radius x.2)) + flowDetJ κ W (flowQ x.1) x.2 ∧
        Y (embQ (flowQ x.1) (radius x.2)) ω = X ω (flowMu W (flowQ x.1) (radius x.2)) := by
    refine ae_all_iff.2 fun x => ?_
    by_cases hx : flowQ x.1 ∈ flowBox m
    · have h2 := hYZ (embQ (flowQ x.1) (radius x.2))
      rw [ptQ_embQ hx, rhQ_embQ _ (radius_mem_Icc x.2)] at h2
      filter_upwards [hID κ hκ hκ4 P X hX W hW hW0 _ (flowBox_subset_flowPar m hx) x.2, h2]
        with ω h1 h2 _
      exact ⟨h1, h2⟩
    · exact ae_of_all _ fun ω h => absurd h hx
  have hdet := Metric.tendstoUniformlyOn_iff.1 (hD κ hκ hκ4 W hW hW0 m)
  filter_upwards [hgood] with ω hω n
  set ε : ℝ := 1 / ((n : ℝ) + 1) with hε
  have hε0 : 0 < ε := by positivity
  set Kc : Set (Fin 6 → ℝ) :=
    Set.pi univ (fun _ : Fin 6 => Icc (-((m : ℝ) + 3)) ((m : ℝ) + 3)) with hKc
  have hKcc : IsCompact Kc := isCompact_univ_pi fun _ => isCompact_Icc
  obtain ⟨η, hη, hU⟩ := Metric.uniformContinuousOn_iff.1
    (hKcc.uniformContinuousOn_of_continuous (hYc ω).continuousOn) (ε / 2) (by positivity)
  have hrad : Tendsto radius atTop (𝓝 0) := by
    unfold radius
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  obtain ⟨N1, hN1⟩ := eventually_atTop.1 (hrad.eventually (gt_mem_nhds hη))
  obtain ⟨N2, hN2⟩ := eventually_atTop.1 (hdet (ε / 4) (by positivity))
  refine ⟨max N1 N2, fun j hj j' hj' q hq => ?_⟩
  have e1 : flowPhiY κ (X ω) W j (flowQ q) =
      X ω (flowMu W (flowQ q) (radius j)) + flowDetJ κ W (flowQ q) j := (hω (q, j) hq).1
  have e2 : flowPhiY κ (X ω) W j' (flowQ q) =
      X ω (flowMu W (flowQ q) (radius j')) + flowDetJ κ W (flowQ q) j' := (hω (q, j') hq).1
  have e3 : Y (embQ (flowQ q) (radius j)) ω = X ω (flowMu W (flowQ q) (radius j)) :=
    (hω (q, j) hq).2
  have e4 : Y (embQ (flowQ q) (radius j')) ω = X ω (flowMu W (flowQ q) (radius j')) :=
    (hω (q, j') hq).2
  have r1 := hN1 j (le_of_max_le_left hj)
  have r2 := hN1 j' (le_of_max_le_left hj')
  have hj0 := radius_pos j
  have hj0' := radius_pos j'
  have hd : dist (embQ (flowQ q) (radius j)) (embQ (flowQ q) (radius j')) < η := by
    refine (dist_embQ_le _ _ _).trans_lt ?_
    rw [abs_lt]; constructor <;> linarith
  have hY := hU _ (embQ_mem_cube hq (radius_mem_Icc j)) _
    (embQ_mem_cube hq (radius_mem_Icc j')) hd
  rw [Real.dist_eq, e3, e4] at hY
  have d1 := hN2 j (le_of_max_le_right hj) _ hq
  have d2 := hN2 j' (le_of_max_le_right hj') _ hq
  rw [Real.dist_eq] at d1 d2
  rw [e1, e2]
  have hdd : |flowDetJ κ W (flowQ q) j - flowDetJ κ W (flowQ q) j'| < ε / 2 := by
    rw [abs_lt] at d1 d2 ⊢; constructor <;> linarith
  rw [abs_lt] at hY hdd
  rw [abs_le]; constructor <;> linarith

/-- **`XFlowUCStmt` from the four fixed-driver nodes and the log node.** -/
theorem xFlowUCStmt_of_nodes (hE : FlowEnergyStmt) (hA : FlowAdmStmt) (hID : FlowIdentStmt)
    (hD : FlowDetStmt) (hL : XFlowLogUCStmt) : XFlowUCStmt :=
  xFlowUCStmt_of_gamQ_log (xFlowGamUCQStmt_of_fixed (xFlowFixedUCQAllStmt_of hE hA hID hD)) hL

end F1
end QuantumZipper
