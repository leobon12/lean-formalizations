import QuantumZipper.Proofs.Zipper.XFlowUCDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# XFLOW-UC: `XFlowUCStmt` from the `Γ⁰` node and the deterministic log node

**Main result** `xFlowUCStmt_of_gamQ_log : XFlowGamUCQStmt → XFlowLogUCStmt → XFlowUCStmt`.

Proof (own elementary bookkeeping, as `UnifRC3UC.unifRC3Stmt_of_uc` and `UnifUCFix`):

* `flowPhi_eq_split`: at every time `u` where the `Γ⁰` field `y = 𝔥₀ + x` is regular after
  unzipping (witness `F`) and has `RegShift` along the unzipped dyadic circles,
  `Φ_j(p) = Φ^y_j(p) − √κ L_j(p)` (`avgReg_unzX_eq` pointwise on `ℍ̄`; both integrands are
  bounded on the compact set `R_{u,s}(supp fc(d, r)) ⊆ closedBall 0 Rb ∩ ℍ̄`). On one full event
  (JointMod witnesses `RegUnif.ae_exists_joint_witness`, `RegUnif.gaugeRegDyStmt_holds`) this
  holds for all `j` and all `p ∈ flowPar`.
* On that event, `Φ_j` is uniformly Cauchy at the rational points of each box `flowBox m`
  (the two nodes), every `Φ_j` is continuous on `flowPar` (`xFlowPhiContStmt_holds`), and the
  rational points are dense in the box (`flowBox_subset_closure`), so `Φ_j` is uniformly Cauchy
  on the whole box (`ContinuousWithinAt.closure_le`).
* Every point of `flowPar` has a `flowPar`-neighbourhood inside some box
  (`flowBox_mem_nhdsWithin`), hence locally uniform convergence to the pointwise limit.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace F1

open RegCont TwoPoint RegUnif

/-! ## The boxes -/

theorem exists_rat_mem_Icc_near {a b x : ℝ} (hab : a < b) (hx : x ∈ Icc a b) {ε : ℝ}
    (hε : 0 < ε) : ∃ q : ℚ, (q : ℝ) ∈ Icc a b ∧ |x - q| < ε := by
  obtain ⟨q, h1, h2⟩ := exists_rat_btwn (show max a (x - ε) < min b (x + ε) by
    rw [max_lt_iff, lt_min_iff, lt_min_iff]
    exact ⟨⟨hab, by linarith [hx.1]⟩, by linarith [hx.2], by linarith⟩)
  refine ⟨q, ⟨(le_max_left _ _).trans h1.le, h2.le.trans (min_le_left _ _)⟩, ?_⟩
  rw [abs_lt]
  constructor <;> linarith [le_max_right a (x - ε), min_le_right b (x + ε)]

/-- The rational points of a box are dense in it. -/
theorem flowBox_subset_closure (m : ℕ) :
    flowBox m ⊆ closure {p | ∃ q, flowQ q = p ∧ p ∈ flowBox m} := by
  intro p hp
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have h2 : 1 / ((m : ℝ) + 2) < (m : ℝ) + 2 := by
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  have he := half_pos hε
  obtain ⟨q1, hq1, e1⟩ := exists_rat_mem_Icc_near hm1 hp.1 he
  obtain ⟨q2, hq2, e2⟩ := exists_rat_mem_Icc_near hm1 hp.2.1 he
  obtain ⟨q3, hq3, e3⟩ := exists_rat_mem_Icc_near (by linarith) hp.2.2.1 he
  obtain ⟨q4, hq4, e4⟩ := exists_rat_mem_Icc_near hm1 hp.2.2.2.1 he
  obtain ⟨q5, hq5, e5⟩ := exists_rat_mem_Icc_near h2 hp.2.2.2.2 he
  refine ⟨flowQ (q1, q2, q3, q4, q5), ⟨_, rfl, hq1, hq2, hq3, hq4, hq5⟩, ?_⟩
  have hd : dist p.2.2.1 (⟨(q3 : ℝ), (q4 : ℝ)⟩ : ℂ) < ε := by
    rw [Complex.dist_eq]
    refine (Complex.norm_le_abs_re_add_abs_im _).trans_lt ?_
    rw [Complex.sub_re, Complex.sub_im]
    change |p.2.2.1.re - q3| + |p.2.2.1.im - q4| < ε
    linarith
  rw [Prod.dist_eq, Prod.dist_eq, Prod.dist_eq, max_lt_iff, max_lt_iff, max_lt_iff]
  refine ⟨?_, ?_, hd, ?_⟩
  · rw [Real.dist_eq]; change |p.1 - q1| < ε; linarith
  · rw [Real.dist_eq]; change |p.2.1 - q2| < ε; linarith
  · rw [Real.dist_eq]; change |p.2.2.2 - q5| < ε; linarith

theorem flowBox_subset_flowPar (m : ℕ) : flowBox m ⊆ flowPar := fun p hp =>
  ⟨hp.1.1, hp.2.1.1, hp.2.2.2.1.1, lt_of_lt_of_le (by positivity) hp.2.2.2.2.1⟩

/-- Every point of `flowPar` has a `flowPar`-neighbourhood inside some box. -/
theorem flowBox_mem_nhdsWithin {p : ℝ × ℝ × ℂ × ℝ} (hp : p ∈ flowPar) :
    ∃ m : ℕ, flowBox m ∈ 𝓝[flowPar] p := by
  have hr : 0 < p.2.2.2 := hp.2.2.2
  set A : ℝ := |p.1| + |p.2.1| + |p.2.2.1.re| + |p.2.2.1.im| + p.2.2.2 + 1 / p.2.2.2 with hA
  refine ⟨⌈A⌉₊, ?_⟩
  set a : ℝ := ((⌈A⌉₊ : ℕ) : ℝ) with ha
  have hAa : A ≤ a := Nat.le_ceil A
  have h1 := le_abs_self p.1
  have h2 := le_abs_self p.2.1
  have h3 := neg_abs_le p.2.2.1.re
  have h3' := le_abs_self p.2.2.1.re
  have h4 := le_abs_self p.2.2.1.im
  have hir : 0 < 1 / p.2.2.2 := by positivity
  have hq : 1 / (a + 2) < p.2.2.2 := by
    rw [div_lt_iff₀ (by positivity)]
    have n1 := abs_nonneg p.1
    have n2 := abs_nonneg p.2.1
    have n3 := abs_nonneg p.2.2.1.re
    have n4 := abs_nonneg p.2.2.1.im
    have : 1 / p.2.2.2 ≤ a := by linarith
    rw [div_le_iff₀ hr] at this
    nlinarith
  rw [mem_nhdsWithin]
  refine ⟨{q | q.1 < a + 1} ∩ ({q | q.2.1 < a + 1} ∩ ({q | -(a + 1) < q.2.2.1.re} ∩
    ({q | q.2.2.1.re < a + 1} ∩ ({q | q.2.2.1.im < a + 1} ∩ ({q | 1 / (a + 2) < q.2.2.2} ∩
      {q | q.2.2.2 < a + 2}))))), ?_, ?_, ?_⟩
  · refine (isOpen_lt (by fun_prop) (by fun_prop)).inter ((isOpen_lt (by fun_prop)
      (by fun_prop)).inter ((isOpen_lt (by fun_prop) (by fun_prop)).inter ((isOpen_lt
      (by fun_prop) (by fun_prop)).inter ((isOpen_lt (by fun_prop) (by fun_prop)).inter
      ((isOpen_lt (by fun_prop) (by fun_prop)).inter (isOpen_lt (by fun_prop)
      (by fun_prop)))))))
  · have hn := abs_nonneg p.1
    have hn2 := abs_nonneg p.2.1
    have hn3 := abs_nonneg p.2.2.1.re
    have hn4 := abs_nonneg p.2.2.1.im
    refine ⟨by show p.1 < a + 1; linarith, by show p.2.1 < a + 1; linarith,
      by show -(a + 1) < p.2.2.1.re; linarith, by show p.2.2.1.re < a + 1; linarith,
      by show p.2.2.1.im < a + 1; linarith, hq, by show p.2.2.2 < a + 2; linarith⟩
  · rintro q ⟨⟨k1, k2, k3, k4, k5, k6, k7⟩, hqP⟩
    exact ⟨⟨hqP.1, k1.le⟩, ⟨hqP.2.1, k2.le⟩, ⟨k3.le, k4.le⟩, ⟨hqP.2.2.1, k5.le⟩, ⟨k6.le, k7.le⟩⟩

/-! ## The pathwise split -/

/-- **`Φ_j = Φ^y_j − √κ L_j`** at a time `u` where `y` is regular after unzipping. -/
theorem flowPhi_eq_split (κ : ℝ) {x : FieldSample} {W : ℝ → ℝ} (hW : Continuous W)
    (hW0 : W 0 = 0) {u s : ℝ} (d : ℂ) {r : ℝ} (hu : 0 ≤ u) (hs : 0 ≤ s) (hr : 0 < r)
    (hR : ∀ k : ℕ, ∀ d ∈ Dy, E1.RegShift (ofFun (h0rev κ) + x)
      ((foldedCircle d (radius k)).map (fwdMapInv W u)))
    {F : ℂ × ℝ → ℝ} (hF : IsRegularWith (unzippedField (Real.sqrt κ) (ofFun (h0rev κ) + x, W) u) F)
    (j : ℕ) :
    flowPhi κ x W j (u, s, d, r) =
      flowPhiY κ x W j (u, s, d, r) + -Real.sqrt κ * flowLogJ W j (u, s, d, r) := by
  have hV := B2.continuous_vrev hW (u + s)
  have hRm : Measurable (revMap (B2.vrev W (u + s)) s) := measurable_revMap hV hs
  have hfym : Measurable fun w =>
      avgReg (unzippedField (Real.sqrt κ) (ofFun (h0rev κ) + x, W) u) j w :=
    CoordRegComp.measurable_avgReg_right _ j
  have hfJc : Continuous fun w : ℂ =>
      ∫ v, Real.log ‖fwdMapInv W u v‖ ∂foldedCircle w (radius j) :=
    continuous_integral_log_fwdMapInv hW hW0 hu (radius_pos j)
  have hH : ∀ᵐ w ∂(foldedCircle d r).map (revMap (B2.vrev W (u + s)) s), w ∈ H :=
    (ae_map_iff hRm.aemeasurable isOpen_H.measurableSet).2
      ((foldedCircle_ae_mem_H d hr).mono fun z hz => im_revMap_pos hV hz hs)
  have hae : ∀ᵐ w ∂(foldedCircle d r).map (revMap (B2.vrev W (u + s)) s),
      avgReg (F2.unzX κ x W u) j w =
        avgReg (unzippedField (Real.sqrt κ) (ofFun (h0rev κ) + x, W) u) j w +
          -Real.sqrt κ * ∫ v, Real.log ‖fwdMapInv W u v‖ ∂foldedCircle w (radius j) := by
    filter_upwards [hH] with w hw
    have hwb : w ∈ Hbar := show (0 : ℝ) ≤ w.im from le_of_lt hw
    rw [avgReg_unzX_eq κ hW hW0 hu hR hF j hwb, hF.avgReg_eq j hwb]
  obtain ⟨M, hM⟩ := exists_abs_le_on_Icc hW (u + s)
  have hbd : ∀ᵐ z ∂foldedCircle d r, revMap (B2.vrev W (u + s)) s z ∈
      Metric.closedBall (0 : ℂ) (revBound (2 * M) s (‖d‖ + r)) ∩ Hbar := by
    filter_upwards [foldedCircle_ae_mem_H d hr, foldedCircle_ae_norm_le d hr.le] with z hz hzn
    refine ⟨mem_closedBall_zero_iff.2 (norm_revMap_le_revBound hV hs
      (fun t _ => abs_vrev_le hM ⟨by linarith, le_rfl⟩ t) _ hzn),
      (im_revMap_pos hV hz hs).le⟩
  have hKc : IsCompact (Metric.closedBall (0 : ℂ) (revBound (2 * M) s (‖d‖ + r)) ∩ Hbar) :=
    (isCompact_closedBall _ _).inter_right isClosed_Hbar
  obtain ⟨C1, hC1⟩ := (hKc.prod (isCompact_singleton (x := radius j))).exists_bound_of_continuousOn
    (hF.1.mono fun q hq => ⟨hq.1.2, by rw [Set.mem_singleton_iff.1 hq.2]; exact radius_pos j⟩)
  obtain ⟨C2, hC2⟩ := hKc.exists_bound_of_continuousOn hfJc.continuousOn
  have hIy : Integrable (fun w =>
      avgReg (unzippedField (Real.sqrt κ) (ofFun (h0rev κ) + x, W) u) j w)
      ((foldedCircle d r).map (revMap (B2.vrev W (u + s)) s)) := by
    rw [integrable_map_measure hfym.aestronglyMeasurable hRm.aemeasurable]
    refine Integrable.of_bound (hfym.comp hRm).aestronglyMeasurable C1 ?_
    filter_upwards [hbd] with z hz
    rw [Function.comp_apply, hF.avgReg_eq j hz.2]
    exact hC1 _ ⟨hz, Set.mem_singleton _⟩
  have hIJ : Integrable (fun w : ℂ =>
      ∫ v, Real.log ‖fwdMapInv W u v‖ ∂foldedCircle w (radius j))
      ((foldedCircle d r).map (revMap (B2.vrev W (u + s)) s)) := by
    rw [integrable_map_measure hfJc.aestronglyMeasurable hRm.aemeasurable]
    refine Integrable.of_bound (hfJc.measurable.comp hRm).aestronglyMeasurable C2 ?_
    filter_upwards [hbd] with z hz
    exact hC2 _ hz
  show ∫ w, avgReg (F2.unzX κ x W u) j w ∂(foldedCircle d r).map
      (revMap (B2.vrev W (u + s)) s) =
    ∫ w, avgReg (unzippedField (Real.sqrt κ) (ofFun (h0rev κ) + x, W) u) j w
      ∂(foldedCircle d r).map (revMap (B2.vrev W (u + s)) s) +
    -Real.sqrt κ * ∫ w, (∫ v, Real.log ‖fwdMapInv W u v‖ ∂foldedCircle w (radius j))
      ∂(foldedCircle d r).map (revMap (B2.vrev W (u + s)) s)
  rw [integral_congr_ae hae, integral_add hIy (hIJ.const_mul _), integral_const_mul]

/-! ## The main reduction -/

/-- **`XFlowUCStmt` from the `Γ⁰` node at rational points and the deterministic log node.** -/
theorem xFlowUCStmt_of_gamQ_log (hG : XFlowGamUCQStmt) (hL : XFlowLogUCStmt) : XFlowUCStmt := by
  intro κ hκ hκ4 Ω _ P _ B X hB hX hind
  have hwit : ∀ᵐ ω ∂P, ∀ n : ℕ, ∃ Z : ℝ × (ℂ × ℝ) → ℝ, ContinuousOn Z (parSet ((n : ℝ) + 1)) ∧
      ∀ t ∈ Icc 0 ((n : ℝ) + 1), IsRegularWith
        (unzippedField (Real.sqrt κ) (ofFun (h0rev κ) + X ω, drive κ B ω) t) (fun p => Z (t, p)) :=
    ae_all_iff.2 fun n => ae_exists_joint_witness (κ := κ) (γ := Real.sqrt κ) hB hX hind
      (by positivity)
  have hreg : ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ s ∈ Icc (0 : ℝ) ((n : ℝ) + 1),
      (∀ k : ℕ, ∀ d ∈ Dy, E1.RegShift (B2.cfg κ B X ω).1
        ((foldedCircle d (radius k)).map (fwdMapInv (drive κ B ω) s))) ∧
        Cor15Group.BdryConvAE (B2.h0f κ s B X ω) :=
    ae_all_iff.2 fun n => gaugeRegDyStmt_holds hB hX hind (by positivity)
  filter_upwards [hwit, hreg, hB.cont, hB.eval_zero_ae_eq_zero,
    ae_all_iff.2 (hG κ hκ hκ4 P B X hB hX hind),
    xFlowPhiContStmt_holds κ hκ hκ4 P B X hB hX hind] with ω hZ hRg hc h0 hGω hCω
  set W := drive κ B ω with hWdef
  have hW : Continuous W := by
    rw [hWdef]; unfold drive
    exact continuous_const.mul (hc.comp continuous_real_toNNReal)
  have hW0 : W 0 = 0 := by simp [hWdef, drive, h0]
  have hsplit : ∀ j : ℕ, ∀ p ∈ flowPar, flowPhi κ (X ω) W j p =
      flowPhiY κ (X ω) W j p + -Real.sqrt κ * flowLogJ W j p := by
    rintro j ⟨u, s, d, r⟩ ⟨hu, hs, -, hr⟩
    obtain ⟨Z, -, hZr⟩ := hZ ⌈u⌉₊
    have huT : u ∈ Icc (0 : ℝ) ((⌈u⌉₊ : ℝ) + 1) := ⟨hu, by linarith [Nat.le_ceil u]⟩
    exact flowPhi_eq_split κ hW hW0 d hu hs hr (hRg _ u huT).1 (hZr u huT) j
  have hUC : ∀ m : ℕ, UniformCauchySeqOn (fun j => flowPhi κ (X ω) W j) atTop (flowBox m) := by
    intro m
    have hLm := (hL W hW hW0 m).uniformCauchySeqOn
    rw [Metric.uniformCauchySeqOn_iff] at hLm ⊢
    intro ε hε
    set c := Real.sqrt κ with hc
    have hc0 : 0 ≤ c := Real.sqrt_nonneg κ
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show 0 < ε / 4 by positivity)
    obtain ⟨N1, hN1⟩ := hGω m n
    set δ := ε / (4 * (c + 1)) with hδ
    have hδ0 : 0 < δ := by positivity
    have hcδ : (c + 1) * δ = ε / 4 := by rw [hδ]; field_simp
    obtain ⟨N2, hN2⟩ := hLm δ hδ0
    refine ⟨max N1 N2, fun j hj j' hj' => ?_⟩
    set D : Set (ℝ × ℝ × ℂ × ℝ) := {p | ∃ q, flowQ q = p ∧ p ∈ flowBox m} with hD
    have hDP : D ⊆ flowPar := by
      rintro p ⟨-, -, h⟩
      exact flowBox_subset_flowPar m h
    have hDq : ∀ p ∈ D, |flowPhi κ (X ω) W j p - flowPhi κ (X ω) W j' p| ≤ ε / 2 := by
      rintro p ⟨q, rfl, hq⟩
      have hpP := flowBox_subset_flowPar m hq
      rw [hsplit j _ hpP, hsplit j' _ hpP]
      have h1 := hN1 j (le_of_max_le_left hj) j' (le_of_max_le_left hj') q hq
      have h2 := hN2 j (le_of_max_le_right hj) j' (le_of_max_le_right hj') _ hq
      rw [Real.dist_eq] at h2
      have e : flowPhiY κ (X ω) W j (flowQ q) + -c * flowLogJ W j (flowQ q) -
          (flowPhiY κ (X ω) W j' (flowQ q) + -c * flowLogJ W j' (flowQ q)) =
          (flowPhiY κ (X ω) W j (flowQ q) - flowPhiY κ (X ω) W j' (flowQ q)) +
            -c * (flowLogJ W j (flowQ q) - flowLogJ W j' (flowQ q)) := by ring
      rw [e]
      have h3 : |-c * (flowLogJ W j (flowQ q) - flowLogJ W j' (flowQ q))| ≤ ε / 4 := by
        rw [abs_mul, abs_neg, abs_of_nonneg hc0]
        have := mul_le_mul (show c ≤ c + 1 by linarith) h2.le (abs_nonneg _) (by linarith)
        linarith
      have h4 := abs_add_le (flowPhiY κ (X ω) W j (flowQ q) - flowPhiY κ (X ω) W j' (flowQ q))
        (-c * (flowLogJ W j (flowQ q) - flowLogJ W j' (flowQ q)))
      linarith
    intro p hp
    have hpP := flowBox_subset_flowPar m hp
    have hcont : ContinuousWithinAt
        (fun p => |flowPhi κ (X ω) W j p - flowPhi κ (X ω) W j' p|) D p :=
      ((((hCω j).sub (hCω j')).abs) p hpP).mono hDP
    have hle := ContinuousWithinAt.closure_le (g := fun _ => ε / 2)
      (flowBox_subset_closure m hp) hcont continuousWithinAt_const hDq
    rw [Real.dist_eq]
    have : |flowPhi κ (X ω) W j p - flowPhi κ (X ω) W j' p| ≤ ε / 2 := hle
    linarith
  refine ⟨fun p => limUnder atTop (fun j => flowPhi κ (X ω) W j p), ?_⟩
  refine tendstoLocallyUniformlyOn_of_forall_exists_nhds fun p hp => ?_
  obtain ⟨m, hm⟩ := flowBox_mem_nhdsWithin hp
  exact ⟨flowBox m, hm, (hUC m).tendstoUniformlyOn_of_tendsto fun y hy =>
    ((hUC m).cauchySeq hy).tendsto_limUnder⟩

end F1
end QuantumZipper
