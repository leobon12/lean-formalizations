import QuantumZipper.Proofs.Zipper.UnifRC3UC
import QuantumZipper.Proofs.Zipper.F1PStarShiftReg
import QuantumZipper.Proofs.Zipper.Cor15RezipRegGood
import QuantumZipper.Proofs.Zipper.Cor15GroupZero
import QuantumZipper.Proofs.Thm18.G1PkgTrace

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# REGSHIFT-UNIF, deterministic part: `RegShift` along pushed circles from a regular witness

Deterministic lemmas behind `RegShiftUnif.lean` (the uniform-in-time `E1.RegShift` inputs
`RegUnif.GaugeRegStmt` and its dyadic-radius form):

* `isRegularWith_of_raw_eq`: a regular witness passes to any field with the same raw values at
  the circles read by `avgReg`;
* `raw_unzip_zero_eq`: at time `0` the unzipped field `coordChange y (f_0) Q` has the raw values
  of `y` at every dyadic folded circle, as soon as `evalReg y` is the raw value there
  (`f_0 = id` on `ℍ`, `Thm18Asm.G1Pkg.fwdMapInv_zero_time`);
* `exists_tendsto_of_uc_tri`: steps 1–2 of `RegUnif.unifRC3Stmt_of_uc` (uniform Cauchy on the
  rational points of the time triangle plus continuity in `(u, s)` gives convergence at every
  point of the triangle), for an arbitrary folded circle `fc(w, r)`;
* `regShift_fc_map_of_witness`: a regular sample `y` with witness `F` satisfies `E1.RegShift`
  along `(f_s)_* fc(w, r)` as soon as `∫ F(R_s z, 2^{-j}) dfc(w, r)(z)` converges
  (`R_s = revMap (vrev W s) s = f_s` on `ℍ`).

Sources: Duplantier–Sheffield, *Liouville quantum gravity and KPZ*, Invent. Math. 185 (2011),
Prop. 3.1 (regularized coordinate change), through `CoordRegComp`/JointMod; Sheffield,
arXiv:1012.4797, §5.1 rule (5.1). The bookkeeping (density/continuity, integrability by
compactness) is an **own elementary argument**, as in `UnifRC3UC.lean`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal

namespace QuantumZipper
namespace RegUnif

open B2 RegCont TwoPoint

/-- A regular witness passes to a field with the same raw values at the dyadic circles. -/
theorem isRegularWith_of_raw_eq {y y' : FieldSample} {F : ℂ × ℝ → ℝ}
    (h : ∀ n k : ℕ, ∀ z : ℂ, y (foldedCircle (dyadicRoundC n z) (radius k)) =
      y' (foldedCircle (dyadicRoundC n z) (radius k)))
    (hF : IsRegularWith y' F) : IsRegularWith y F :=
  ⟨hF.1, fun k z hz => (hF.2.1 k z hz).congr fun n => (h n k z).symm, hF.2.2⟩

/-- The circles read by `avgReg` are enumerated circles. -/
theorem exists_fullIndex_radius (n k : ℕ) (z : ℂ) :
    ∃ i, CoordsFull.fullIndex i = (dyadicRoundC n z, radius k) := by
  obtain ⟨i, hi⟩ := CoordsFull.fullIndex_surj n z 1 one_pos k
  refine ⟨i, ?_⟩
  rw [hi]
  simp [radius, inv_pow]

/-- **Time `0`: raw values of the unzipped field.** -/
theorem raw_unzip_zero_eq (γ : ℝ) {y : FieldSample} {W : ℝ → ℝ} (hW : Continuous W)
    (hW0 : W 0 = 0)
    (hy : ∀ i : ℕ, evalReg y (foldedCircle (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2) =
      y (foldedCircle (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2)) (n k : ℕ) (z : ℂ) :
    y (foldedCircle (dyadicRoundC n z) (radius k)) =
      unzippedField γ (y, W) 0 (foldedCircle (dyadicRoundC n z) (radius k)) := by
  have hid : EqOn (fwdMapInv W 0) id H := fun w hw => by
    rw [Thm18Asm.G1Pkg.fwdMapInv_zero_time hW (show 0 < w.im from hw), hW0]
    simp
  obtain ⟨i, hi⟩ := exists_fullIndex_radius n k z
  have h1 := hy i
  rw [hi] at h1
  show _ = coordChange y (fwdMapInv W 0) (Qc γ) _
  rw [Cor15Group.coordChange_congr_H y hid (Qc γ)
    (TwoPoint.foldedCircle_ae_mem_H _ (radius_pos k)), Cor15Partial.coordChange_id_apply]
  exact h1.symm

/-- **Steps 1–2 of `unifRC3Stmt_of_uc`, at an arbitrary folded circle**: uniform Cauchy on the
rational points of the triangle and continuity in `(u, s)` give convergence at every point. -/
theorem exists_tendsto_of_uc_tri {W : ℝ → ℝ} (hW : Continuous W) {T : ℝ} (hT : 0 < T)
    {G : ℝ × (ℂ × ℝ) → ℝ} (hG : ContinuousOn G (parSet T)) (w : ℂ) {r : ℝ} (hr : 0 < r)
    (hUC : ∀ n : ℕ, ∃ N : ℕ, ∀ j, N ≤ j → ∀ j', N ≤ j' → ∀ p ∈ triQ T,
      |(∫ z, G (p.1, (revMap (vrev W (p.1 + p.2)) p.2 z, radius j)) ∂foldedCircle w r) -
        ∫ z, G (p.1, (revMap (vrev W (p.1 + p.2)) p.2 z, radius j')) ∂foldedCircle w r| ≤
          1 / ((n : ℝ) + 1))
    {p : ℝ × ℝ} (hp : p ∈ tri T) :
    ∃ L, Tendsto (fun j => ∫ z, G (p.1, (revMap (vrev W (p.1 + p.2)) p.2 z, radius j))
      ∂foldedCircle w r) atTop (𝓝 L) := by
  obtain ⟨Φ, hΦdef⟩ : ∃ Φ : ℕ → ℝ × ℝ → ℝ, Φ = fun j p =>
      ∫ z, G (p.1, (revMap (vrev W (p.1 + p.2)) p.2 z, radius j)) ∂foldedCircle w r := ⟨_, rfl⟩
  have hΦc : ∀ j, ContinuousOn (Φ j) (tri T) := fun j => by
    rw [hΦdef]; exact continuousOn_integral_comp_R hW hG w hr (radius_pos j)
  have hC : CauchySeq fun j => Φ j p := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    obtain ⟨N, hN⟩ := hUC n
    refine ⟨N, fun j hj => ?_⟩
    have hcont : ContinuousOn (fun q => |Φ j q - Φ N q|) (tri T) := ((hΦc j).sub (hΦc N)).abs
    have hle : |Φ j p - Φ N p| ≤ 1 / ((n : ℝ) + 1) :=
      ContinuousWithinAt.closure_le (tri_subset_closure_triQ hT hp)
        ((hcont p hp).mono (triQ_subset_tri T)) continuousWithinAt_const fun q hq => by
          rw [hΦdef]; exact hN j hj N le_rfl q hq
    rw [Real.dist_eq]
    exact hle.trans_lt hn
  have := hC.tendsto_limUnder
  subst hΦdef
  exact ⟨_, this⟩

/-- **`RegShift` along a pushed circle from a regular witness** (deterministic). -/
theorem regShift_fc_map_of_witness {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {s : ℝ}
    (hs : 0 ≤ s) {y : FieldSample} {F : ℂ × ℝ → ℝ} (hF : IsRegularWith y F) (w : ℂ) {r : ℝ}
    (hr : 0 < r)
    (hL : ∃ L, Tendsto (fun j => ∫ z, F (revMap (vrev W s) s z, radius j) ∂foldedCircle w r)
      atTop (𝓝 L)) :
    E1.RegShift y ((foldedCircle w r).map (fwdMapInv W s)) := by
  have hV : Continuous (vrev W s) := continuous_vrev hW s
  have hRm : Measurable (revMap (vrev W s) s) := measurable_revMap hV hs
  have hmap : (foldedCircle w r).map (fwdMapInv W s) =
      (foldedCircle w r).map (revMap (vrev W s) s) :=
    Measure.map_congr ((foldedCircle_ae_mem_H w hr).mono fun z hz =>
      fwdMapInv_eq_revMap_vrev hW hW0 hs hz)
  rw [hmap]
  have hav : ∀ k : ℕ, ∀ᵐ z ∂foldedCircle w r,
      avgReg y k (revMap (vrev W s) s z) = F (revMap (vrev W s) s z, radius k) := fun k =>
    (foldedCircle_ae_mem_H w hr).mono fun z hz => hF.avgReg_eq k (im_revMap_pos hV hz hs).le
  have hm : ∀ k, Measurable fun v => avgReg y k v := fun k =>
    CoordRegComp.measurable_avgReg_right y k
  obtain ⟨M, hM⟩ := exists_abs_le_on_Icc hV s
  set K := Metric.closedBall (0 : ℂ) (revBound M s (‖w‖ + r)) ∩ Hbar with hK
  have hKc : IsCompact K := (isCompact_closedBall _ _).inter_right isClosed_Hbar
  have hint : ∀ k : ℕ, Integrable (fun v => avgReg y k v)
      ((foldedCircle w r).map (revMap (vrev W s) s)) := by
    intro k
    obtain ⟨C, hC⟩ := (hKc.prod (isCompact_singleton (x := radius k))).exists_bound_of_continuousOn
      (hF.1.mono fun q hq => ⟨hq.1.2, by
        rw [show q.2 = radius k from hq.2]; exact radius_pos k⟩)
    rw [integrable_map_measure (hm k).aestronglyMeasurable hRm.aemeasurable]
    refine Integrable.mono' (integrable_const C) ((hm k).comp hRm).aestronglyMeasurable ?_
    filter_upwards [hav k, foldedCircle_ae_mem_H w hr, foldedCircle_ae_norm_le w hr.le]
      with z h1 hz hzn
    rw [Function.comp_apply, h1]
    exact hC _ ⟨⟨Metric.mem_closedBall.2 (by
      rw [dist_zero_right]; exact norm_revMap_le_revBound hV hs hM _ hzn),
      (im_revMap_pos hV hz hs).le⟩, rfl⟩
  obtain ⟨L, hL⟩ := hL
  refine ⟨Eventually.of_forall fun z k => ⟨_, F1.tendsto_raw_of_isRegularWith hF k z⟩, hint,
    L, ?_⟩
  refine hL.congr fun k => ?_
  rw [integral_map hRm.aemeasurable (hm k).aestronglyMeasurable]
  exact (integral_congr_ae (hav k)).symm

end RegUnif
end QuantumZipper
