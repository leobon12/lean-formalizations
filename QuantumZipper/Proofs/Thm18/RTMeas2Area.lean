import QuantumZipper.Proofs.Thm18.RTMeas2AreaW
import QuantumZipper.Proofs.Section5.Prop16AssemblyBasic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# RT-MEAS2, part 7: `AreaRegStmt` holds

The countable area certificate of the data (`AreaCertD`): on every rational window
`B̄(c_n, 2r_n) ⊆ ℍ` at distance `> 2r_n` from the curve (a Borel condition on the driver,
`WinOKD`), eventual finiteness and convergence of the weighted approximations against the dense
family (`WinCertC`), and finiteness of the read areas of the exhaustion `hExh N` (`readO`). It is
Borel, it implies `AreaGood` (`areaGood_of_cert`: the window certificate gives the local limit on
`ℍ ∖ curve`, `exists_lim_of_winCertC`, and `readO_eq` identifies the read areas), and it holds a.s.
for the pieces of the wedge: the local limit is the wedge area off the curve
(`isVagueLimitOn_offData`, `areaOfData_offData`, Sheffield arXiv:1012.4797 §4.1 p. 48: the curve
carries no area), and the approximations of the pieces are bounded on bounded sets by the log
growth of the circle averages (`circAvgLogGrowthStmt_holds`, Hu–Miller–Peres 2010 Prop 2.1).

Own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace R18
namespace RTMeas

open Thm18Asm

/-- Distance of a point to the curve of the data. -/
def curveInf (c : ℂ) (p : PX) : ℝ := infDist c (D74.curveSel p.2)

theorem measurable_curveInf (c : ℂ) : Measurable (curveInf c) := by
  have hne : ∀ p : PX, (range fun q : ℚ≥0 => G1Pkg.traceSel 1 p.2 (q : ℝ)).Nonempty :=
    fun p => range_nonempty _
  refine measurable_of_Iio fun r => ?_
  have e : curveInf c ⁻¹' Iio r =
      ⋃ q : ℚ≥0, {p : PX | dist c (G1Pkg.traceSel 1 p.2 (q : ℝ)) < r} := by
    ext p
    simp only [mem_preimage, mem_Iio, curveInf, D74.curveSel, infDist_closure,
      infDist_lt_iff (hne p), mem_range, mem_iUnion, mem_setOf_eq]
    constructor
    · rintro ⟨y, ⟨q, rfl⟩, h⟩; exact ⟨q, h⟩
    · rintro ⟨q, h⟩; exact ⟨_, ⟨q, rfl⟩, h⟩
  rw [e]
  exact MeasurableSet.iUnion fun q => measurableSet_lt (measurable_const.dist
    ((D74.measurable_traceSel_apply _).comp measurable_snd)) measurable_const

/-- The window condition read from the data. -/
def WinOKD (p : PX) (n : ℕ) : Prop :=
  0 < rC n ∧ closedBall (cC n) (2 * rC n) ⊆ H ∧ 2 * rC n < curveInf (cC n) p

theorem winOKD_iff (p : PX) (n : ℕ) : WinOKD p n ↔ WinOKC (offSet (dfull p)) n := by
  constructor
  · rintro ⟨hr, hH, hd⟩
    refine ⟨hr, fun y hy => ⟨hH hy, fun hyc => ?_⟩⟩
    have := infDist_le_dist_of_mem hyc (x := cC n)
    rw [dist_comm] at this
    exact absurd ((this.trans (mem_closedBall.1 hy))) (not_le.2 hd)
  · rintro ⟨hr, hsub⟩
    refine ⟨hr, fun y hy => (hsub hy).1, ?_⟩
    have hne : (D74.curveSel p.2).Nonempty := (range_nonempty _).mono subset_closure
    obtain ⟨y, hy, hyd⟩ := isClosed_closure.exists_infDist_eq_dist hne (cC n)
    have hyd' : curveInf (cC n) p = dist (cC n) y := hyd
    rw [hyd']
    by_contra hle
    push Not at hle
    exact (hsub (mem_closedBall.2 (by rw [dist_comm]; exact hle))).2 hy

/-- **The countable area certificate of the data.** -/
def AreaCertD (γ : ℝ) (p : PX) : Prop :=
  (∀ n, WinOKD p n →
    (∃ K : ℕ, ∀ k, K ≤ k →
      areaApprox γ (readOffField (dfull p)) k (closedBall (cC n) (2 * rC n)) < ⊤) ∧
    ∀ f ∈ GoodMeas.denseFam, ∃ l,
      Tendsto (fun k => ∫ z, f z * wt n z ∂areaApprox γ (readOffField (dfull p)) k) atTop (𝓝 l)) ∧
  ∀ N : ℕ, readO γ (LQGMeas.hExh N) N (dfull p) < ⊤

theorem measurableSet_areaCertD (γ : ℝ) : MeasurableSet {p : PX | AreaCertD γ p} := by
  have hx : Measurable fun p : PX => readOffField (dfull p) :=
    measurable_readOffField.comp measurable_dfull
  have hok : ∀ n, Measurable fun p : PX => WinOKD p n := fun n =>
    measurable_const.and (measurable_const.and
      (measurableSet_setOfPred.1 (measurableSet_lt measurable_const (measurable_curveInf _))))
  refine measurableSet_setOfPred.2 (Measurable.and (Measurable.forall fun n => (hok n).imp ?_) ?_)
  · refine Measurable.and (Measurable.exists fun K => Measurable.forall fun k =>
      measurable_const.imp (measurableSet_setOfPred.1 (measurableSet_lt
        ((Measure.measurable_coe measurableSet_closedBall).comp
          ((measurable_areaApprox γ k).comp hx)) measurable_const))) ?_
    have hset : {p : PX | ∀ f ∈ GoodMeas.denseFam, ∃ l, Tendsto (fun k => ∫ z, f z * wt n z
        ∂areaApprox γ (readOffField (dfull p)) k) atTop (𝓝 l)} =
        ⋂ f ∈ GoodMeas.denseFam, {p : PX | ∃ l, Tendsto (fun k => ∫ z, f z * wt n z
          ∂areaApprox γ (readOffField (dfull p)) k) atTop (𝓝 l)} := by
      ext p; simp
    refine measurableSet_setOfPred.1 ?_
    rw [hset]
    refine MeasurableSet.biInter GoodMeas.denseFam_countable fun f hf => ?_
    have hfc : Continuous f := (GoodMeas.denseFam_dense.1 f hf).1
    exact StronglyMeasurable.measurableSet_exists_tendsto fun k =>
      (Prop16Area.Meas.measurable_integral_areaApprox_param γ k hx
        (g := fun _ z => f z * wt n z)
        ((hfc.mul (continuous_wt n)).measurable.comp measurable_snd)).stronglyMeasurable
  · exact Measurable.forall fun N => measurableSet_setOfPred.1 (measurableSet_lt
      ((measurable_readO γ (LQGMeas.isOpen_hExh N) _).comp measurable_dfull) measurable_const)

theorem hExh_subset_ball (N : ℕ) : LQGMeas.hExh N ⊆ ball (0 : ℂ) N := fun z hz => by
  simpa [mem_ball, dist_zero_right] using hz.1

theorem areaGood_of_cert {γ : ℝ} {p : PX} (h : AreaCertD γ p) : AreaGood γ (dfull p) := by
  have hU := isOpen_offSet (dfull p)
  have hUH : offSet (dfull p) ⊆ H := diff_subset
  obtain ⟨m, hm⟩ := exists_lim_of_winCertC hU hUH fun n hok => h.1 n ((winOKD_iff p n).2 hok)
  refine ⟨⟨m, hm⟩, fun K hK hKH => ?_⟩
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover LQGMeas.hExh LQGMeas.isOpen_hExh
    (hKH.trans LQGMeas.H_subset_iUnion_hExh)
  have hKN : K ⊆ LQGMeas.hExh (s.sup id) := fun z hz => by
    obtain ⟨n, hn, hzn⟩ := mem_iUnion₂.1 (hs hz)
    exact LQGMeas.hExh_mono (Finset.le_sup (f := id) hn) hzn
  have hr := readO_eq (LQGMeas.isOpen_hExh _) (hExh_subset_ball (s.sup id)) hm
  rw [inter_eq_left.2 (fun z hz => LQGMeas.hExhK_subset_H _
    (LQGMeas.hExh_subset_compact _ hz))] at hr
  exact (measure_mono hKN).trans_lt (hr ▸ h.2 _)

/-! ## The certificate for the pieces of the wedge -/

theorem areaApprox_closedBall_lt_top {γ : ℝ} {x : FieldSample × (ℝ → ℝ)}
    (hg : ∀ Rr : ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (k n : ℕ) (w : ℂ), ‖w‖ ≤ Rr →
      |x.1 (foldedCircle (dyadicRoundC n w) (radius k))| ≤ C * (k + 1))
    (c : ℂ) (ρ : ℝ) (k : ℕ) :
    areaApprox γ (readOffField (offData x)) k (closedBall c ρ) < ⊤ := by
  obtain ⟨C, -, hC⟩ := hg (‖c‖ + |ρ|)
  set M : ℝ := max (C * (k + 1)) |junkRT|
  set Bd : ℝ := radius k ^ (γ ^ 2 / 2) * Real.exp (|γ| * M)
  have hbd : ∀ z ∈ closedBall c ρ, ENNReal.ofReal (radius k ^ (γ ^ 2 / 2) *
      Real.exp (γ * avgReg (readOffField (offData x)) k z)) ≤ ENNReal.ofReal Bd := by
    intro z hz
    have hz' : ‖z‖ ≤ ‖c‖ + |ρ| := by
      have := mem_closedBall.1 hz
      rw [dist_eq_norm] at this
      calc ‖z‖ ≤ ‖z - c‖ + ‖c‖ := norm_le_norm_sub_add z c
        _ ≤ ‖c‖ + |ρ| := by linarith [le_abs_self ρ]
    have ha : |avgReg (readOffField (offData x)) k z| ≤ M :=
      abs_limUnder_le_RT fun n => (abs_readOffField_offData_le x _).trans (hC k n z hz')
    refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_)
      (Real.rpow_nonneg (radius_pos k).le _))
    calc γ * avgReg (readOffField (offData x)) k z ≤ |γ * avgReg (readOffField (offData x)) k z| :=
          le_abs_self _
      _ = |γ| * |avgReg (readOffField (offData x)) k z| := abs_mul _ _
      _ ≤ |γ| * M := mul_le_mul_of_nonneg_left ha (abs_nonneg _)
  unfold areaApprox
  rw [withDensity_apply _ measurableSet_closedBall]
  calc ∫⁻ z in closedBall c ρ, ENNReal.ofReal (radius k ^ (γ ^ 2 / 2) *
        Real.exp (γ * avgReg (readOffField (offData x)) k z)) ∂volume.restrict H
      ≤ ∫⁻ _z in closedBall c ρ, ENNReal.ofReal Bd ∂volume.restrict H :=
        setLIntegral_mono measurable_const hbd
    _ = ENNReal.ofReal Bd * (volume.restrict H) (closedBall c ρ) := setLIntegral_const _ _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        ((Measure.restrict_apply_le _ _).trans_lt measure_closedBall_lt_top)

theorem areaGood_of_dfull {γ : ℝ} {d : E6.FullData} (h : AreaGood γ (dfull (πd d))) :
    AreaGood γ d := by
  have e1 : readOffField (dfull (πd d)) = readOffField d := rfl
  have e2 : offSet (dfull (πd d)) = offSet d := rfl
  have e3 : areaOfData γ (dfull (πd d)) = areaOfData γ d := rfl
  unfold AreaGood at h ⊢
  rw [e1, e2, e3] at h
  exact h

/-- The certificate for the pieces of a configuration with a continuous driver starting at `0`,
a global area limit and log-growing circle averages. -/
theorem areaCertD_offData {γ : ℝ} {x : FieldSample × (ℝ → ℝ)} (hc : Continuous x.2)
    (h0 : x.2 0 = 0) {μ : Measure ℂ} (hμ : IsVagueLimitOn H (areaApprox γ x.1) μ)
    (hlog : ∀ Rr : ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (k n : ℕ) (w : ℂ), ‖w‖ ≤ Rr →
      |x.1 (foldedCircle (dyadicRoundC n w) (radius k))| ≤ C * (k + 1)) :
    AreaCertD γ (πd (offData x)) := by
  have e1 : readOffField (dfull (πd (offData x))) = readOffField (offData x) := rfl
  have e2 : offSet (dfull (πd (offData x))) = offSet (offData x) := rfl
  have e3 : areaOfData γ (dfull (πd (offData x))) = areaOfData γ (offData x) := rfl
  obtain ⟨m, hm⟩ := isVagueLimitOn_offData hc h0 hμ
  have hA := areaOfData_offData hc h0 hμ
  have hm' : IsVagueLimitOn (offSet (dfull (πd (offData x))))
      (areaApprox γ (readOffField (dfull (πd (offData x))))) m := by rw [e1, e2]; exact hm
  refine ⟨fun n hok => ⟨⟨0, fun k _ => ?_⟩, fun f hf => ?_⟩, fun N => ?_⟩
  · rw [e1]; exact areaApprox_closedBall_lt_top hlog _ _ k
  · have hok' := (winOKD_iff _ n).1 hok
    have hfT := GoodMeas.denseFam_dense.1 f hf
    have hts : tsupport (fun z => f z * wt n z) ⊆ closedBall (cC n) (2 * rC n) :=
      (tsupport_mul_subset_right).trans (closure_minimal (fun z hz => by
        by_contra h; exact hz (wt_eq_zero hok'.1 h)) isClosed_closedBall)
    exact ⟨_, hm'.2.2 _ (hfT.1.mul (continuous_wt n)) hfT.2.1.mul_right (hts.trans hok'.2)⟩
  · rw [readO_eq (LQGMeas.isOpen_hExh N) (hExh_subset_ball N) hm', e3, hA]
    refine (Measure.restrict_apply_le _ _).trans_lt ?_
    exact (measure_mono (inter_subset_left.trans (LQGMeas.hExh_subset_compact N))).trans_lt
      (hμ.2.1 _ (LQGMeas.isCompact_hExhK N) (LQGMeas.hExhK_subset_H N))

/-- **`AreaRegStmt` holds.** -/
theorem areaRegStmt_holds : AreaRegStmt := by
  intro γ Ω _ P _ B Y hS hIn
  have hC : ∀ᵐ ω ∂P, AreaCertD γ (πd (offData (wedgeAConfig γ B Y ω).toPair)) := by
    filter_upwards [hIn.1, circAvgLogGrowthStmt_holds γ P B Y hS hIn,
      D74.ae_wedgeConfig_snd_good hS] with ω hgood hlog hW
    obtain ⟨μ, hμ⟩ := Prop16Asm.exists_isVagueLimitOn_of_isLQGGood hgood.1
    exact areaCertD_offData (x := (wedgeAConfig γ B Y ω).toPair) hW.1 hW.2 hμ hlog
  exact ⟨{p | AreaCertD γ p}, measurableSet_areaCertD γ,
    fun d hd => areaGood_of_dfull (areaGood_of_cert hd), hC⟩

end RTMeas
end R18
end QuantumZipper
