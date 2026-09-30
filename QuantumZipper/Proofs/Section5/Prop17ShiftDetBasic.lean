import QuantumZipper.Proofs.Section5.Prop17StatLocal
import QuantumZipper.Proofs.Zipper.D3PlusLocal
import QuantumZipper.Proofs.LQG.PalmNormLocal
import QuantumZipper.Proofs.Section5.Prop16LocalRule

/-!
# Proposition 1.7, SHIFT-DET (part 1): deterministic locality lemmas

Sheffield, arXiv:1012.4797, proof of Proposition 1.7 (p. 26): "the shift-by-`L` map is local"
(blueprint D5: the shifted surface restricted to a ball is determined by the original surface
restricted to a larger ball, on the event that the length-`L` point and the new scale are
bounded). The paper states this without proof; the formal argument below is our own elementary
one (AGENT_GUIDE cost rule), built from the locality of the Gaussian multiplicative chaos
approximations (Duplantier–Sheffield, *Liouville quantum gravity and KPZ*, Invent. Math. 185
(2011), §6, formalized in `Prop16LocalRule.lean`, `D3PlusLocal.lean`, `PalmNormLocal.lean`).

* `sInf_eq_of_agree_below`: two sets of nonnegative reals agreeing below `M`, the first having
  infimum `< M`, have the same infimum;
* `norm_add_le_of_foldedCircle_eq`: a folded circle determines `‖centre‖ + radius`;
* `agreeNear_reconstruct`, `agreeNear_of_locFull`: coordinates agreeing on the circles inside a
  ball give reconstructions agreeing near `0`;
* `lenG_eq_of_agreeNear`: locality of the length point;
* `coords_translate_eq_of_agreeNear`: locality of translation;
* `scaleParam_eq_of_agreeNear`: locality of the scale parameter on `{0 < scaleParam < r}`.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal Real

namespace QuantumZipper
namespace S5
namespace FieldLaw
namespace Raw

open WedgeMeas Factorization CoordsFull

/-! ## 1. Infima of sets agreeing below a level -/

/-- Own elementary lemma. -/
theorem sInf_eq_of_agree_below {S S' : Set ℝ} {M : ℝ} (hS0 : ∀ a ∈ S, 0 ≤ a)
    (hS0' : ∀ a ∈ S', 0 ≤ a) (hagr : ∀ a < M, a ∈ S ↔ a ∈ S') (hne : S.Nonempty)
    (hlt : sInf S < M) : sInf S' = sInf S := by
  have hb : BddBelow S := ⟨0, hS0⟩
  have hb' : BddBelow S' := ⟨0, hS0'⟩
  obtain ⟨a₀, ha₀, ha₀M⟩ := exists_lt_of_csInf_lt hne hlt
  have ha₀' : a₀ ∈ S' := (hagr a₀ ha₀M).1 ha₀
  apply le_antisymm
  · refine le_csInf hne fun b hbS => ?_
    by_cases hbM : b < M
    · exact csInf_le hb' ((hagr b hbM).1 hbS)
    · exact (csInf_le hb' ha₀').trans (ha₀M.le.trans (not_lt.1 hbM))
  · refine le_csInf ⟨a₀, ha₀'⟩ fun b hbS => ?_
    by_cases hbM : b < M
    · exact csInf_le hb ((hagr b hbM).2 hbS)
    · exact hlt.le.trans (not_lt.1 hbM)

/-! ## 2. A folded circle determines `‖centre‖ + radius` -/

theorem norm_foldH_shiftDet (u : ℂ) : ‖foldH u‖ = ‖u‖ := by
  unfold foldH
  split_ifs
  · rfl
  · exact Complex.norm_conj u

theorem norm_circleMap_arg_shiftDet (z : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    ‖circleMap z r z.arg‖ = ‖z‖ + r := by
  have e : circleMap z r z.arg = ((‖z‖ + r : ℝ) : ℂ) * Complex.exp (z.arg * Complex.I) := by
    simp only [circleMap]
    push_cast
    rw [add_mul, Complex.norm_mul_exp_arg_mul_I]
  rw [e, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]

theorem foldedCircle_norm_gt_pos {z : ℂ} {r ρ : ℝ} (hr : 0 < r) (hρ : ρ < ‖z‖ + r) :
    0 < foldedCircle z r {u | ρ < ‖u‖} := by
  have hV : IsOpen {u : ℂ | ρ < ‖u‖} := isOpen_lt continuous_const continuous_norm
  have hVm := hV.measurableSet
  rw [foldedCircle, Measure.map_apply measurable_foldH hVm]
  have hpre : foldH ⁻¹' {u | ρ < ‖u‖} = {u | ρ < ‖u‖} := by
    ext u; simp only [mem_preimage, mem_ofPred_eq, norm_foldH_shiftDet]
  rw [hpre, circleUnif, Measure.smul_apply, Measure.map_apply (measurable_circleMap z r) hVm,
    smul_eq_mul]
  refine ENNReal.mul_pos (ENNReal.inv_ne_zero.2 ENNReal.ofReal_ne_top) (ne_of_gt ?_)
  set U := circleMap z r ⁻¹' {u | ρ < ‖u‖} with hUdef
  have hU : IsOpen U := hV.preimage (continuous_circleMap z r)
  set θ₁ := toIcoMod Real.two_pi_pos 0 z.arg with hθ₁
  have hθI : θ₁ ∈ Ico 0 (0 + 2 * π) := toIcoMod_mem_Ico _ _ _
  rw [zero_add] at hθI
  have hθU : θ₁ ∈ U := by
    have : circleMap z r θ₁ = circleMap z r z.arg := by
      rw [hθ₁, toIcoMod]
      exact (periodic_circleMap z r).sub_zsmul_eq _
    simp only [hUdef, mem_preimage, mem_ofPred_eq, this, norm_circleMap_arg_shiftDet z hr.le]
    exact hρ
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU θ₁ hθU
  have hsub : Ioo θ₁ (min (θ₁ + ε) (2 * π)) ⊆ U ∩ Ico 0 (2 * π) := by
    intro θ hθ
    refine ⟨hball ?_, hθI.1.trans hθ.1.le, hθ.2.trans_le (min_le_right _ _)⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor
    · linarith [hθ.1]
    · linarith [hθ.2.trans_le (min_le_left _ _)]
  rw [Measure.restrict_apply hU.measurableSet]
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  rw [Real.volume_Ioo, ENNReal.ofReal_pos]
  have := hθI.2
  exact sub_pos.2 (lt_min (by linarith) this)

/-- Own elementary lemma: equal folded circles (positive radii) have equal `‖centre‖ + radius`
(one inequality suffices here). -/
theorem norm_add_le_of_foldedCircle_eq {z₁ z₂ : ℂ} {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₂ : 0 ≤ r₂)
    (h : foldedCircle z₁ r₁ = foldedCircle z₂ r₂) : ‖z₁‖ + r₁ ≤ ‖z₂‖ + r₂ := by
  by_contra hlt
  push Not at hlt
  have h1 := foldedCircle_norm_gt_pos hr₁ hlt
  have h2 : foldedCircle z₂ r₂ {u | ‖z₂‖ + r₂ < ‖u‖} = 0 := by
    refine measure_mono_null (fun u hu => ?_) (CircleFubini.foldedCircle_support hr₂ le_rfl)
    simp only [CircleFubini.ballH, mem_compl_iff, mem_inter_iff, Metric.mem_closedBall,
      dist_zero_right, not_and_or, not_le]
    exact Or.inl hu
  rw [h, h2] at h1
  exact lt_irrefl _ h1

/-! ## 3. Reconstructions from locally agreeing coordinates -/

theorem agreeNear_mono_shiftDet {y y' : FieldSample} {r r' : ℝ} (h : D3Plus.AgreeNear y y' r)
    (hr : r' ≤ r) : D3Plus.AgreeNear y y' r' := fun n k z hz => h n k z (hz.trans_le hr)

theorem agreeNear_reconstruct {a b : ℕ → ℝ} {ρ : ℝ}
    (h : ∀ j, ‖(dyadicIndex j).1‖ + radius (dyadicIndex j).2 < ρ → a j = b j) :
    D3Plus.AgreeNear (reconstruct a) (reconstruct b) ρ := by
  classical
  intro n k z hz
  unfold reconstruct
  by_cases hex : ∃ i, foldedCircle (dyadicIndex i).1 (radius (dyadicIndex i).2) =
      foldedCircle (dyadicRoundC n z) (radius k)
  · rw [dif_pos hex, dif_pos hex]
    exact h _ ((norm_add_le_of_foldedCircle_eq (radius_pos _) (radius_pos k).le
      (Nat.find_spec hex)).trans_lt hz)
  · rw [dif_neg hex, dif_neg hex]

theorem proj_eq_of_locFull {R : ℕ} {c c' : ℕ → ℝ} (h : locFull R c = locFull R c') {j : ℕ}
    (hj : ‖(dyadicIndex j).1‖ + radius (dyadicIndex j).2 ≤ R) : proj c j = proj c' j := by
  have hs := Classical.choose_spec (WedgeGood.exists_fullIndex j)
  have hin : inBallFull R (Classical.choose (WedgeGood.exists_fullIndex j)) := by
    unfold inBallFull; rw [hs]; exact hj
  have := congrFun h (Classical.choose (WedgeGood.exists_fullIndex j))
  simp only [locFull, if_pos hin] at this
  exact this

theorem agreeNear_of_locFull {R : ℕ} {c c' : ℕ → ℝ} (h : locFull R c = locFull R c') :
    D3Plus.AgreeNear (reconstruct (proj c)) (reconstruct (proj c')) R :=
  agreeNear_reconstruct fun _ hj => proj_eq_of_locFull h hj.le

/-! ## 4. Locality of the length point -/

theorem exists_mem_lenSet {ν : Measure ℝ} (h : ν (Ici 0) = ⊤) (L : ℝ) :
    ∃ y, 0 < y ∧ ENNReal.ofReal L ≤ ν (Icc 0 y) := by
  by_contra hne
  push Not at hne
  have hU : Ici (0 : ℝ) = ⋃ m : ℕ, Icc 0 ((m : ℝ) + 1) := by
    ext t
    simp only [mem_Ici, mem_iUnion, mem_Icc]
    constructor
    · intro ht
      obtain ⟨m, hm⟩ := exists_nat_ge t
      exact ⟨m, ht, by linarith⟩
    · rintro ⟨m, h1, -⟩; exact h1
  have hmono : Monotone fun m : ℕ => Icc (0 : ℝ) ((m : ℝ) + 1) := fun a b hab =>
    Icc_subset_Icc_right (by have : (a : ℝ) ≤ b := by exact_mod_cast hab
                             linarith)
  rw [hU, hmono.measure_iUnion] at h
  have hle : ⨆ m : ℕ, ν (Icc 0 ((m : ℝ) + 1)) ≤ ENNReal.ofReal L :=
    iSup_le fun m => (hne _ (by positivity)).le
  rw [h] at hle
  exact ENNReal.ofReal_ne_top (top_le_iff.1 hle)

theorem lenG_nonneg (γ L : ℝ) (x : FieldSample) : 0 ≤ lenG γ L x :=
  Real.sInf_nonneg fun _ hy => hy.1.le

theorem lenG_eq_of_agreeNear {γ L : ℝ} {x x' : FieldSample} (hx : IsLQGGood γ x)
    (hx' : IsLQGGood γ x') {R n : ℝ} (hag : D3Plus.AgreeNear x x' R) (hnR : n + 2 ≤ R)
    (htop : qBoundaryMeasure γ x (Ici 0) = ⊤) (hn : lenG γ L x ≤ n) :
    lenG γ L x' = lenG γ L x := by
  have hres : (qBoundaryMeasure γ x).restrict (Ioo (-(n + 1)) (n + 1)) =
      (qBoundaryMeasure γ x').restrict (Ioo (-(n + 1)) (n + 1)) := by
    refine PalmNorm.qBoundaryMeasure_restrict_eq_of_avgReg isOpen_Ioo
      ⟨_, Prop16Area.G.isVagueLimitR_of_good hx⟩ ⟨_, Prop16Area.G.isVagueLimitR_of_good hx'⟩
      (Eventually.of_forall fun k t ht => D3Plus.avgReg_congr hag ?_)
    rw [Complex.norm_real, Real.norm_eq_abs]
    have := abs_lt.2 ⟨ht.1, ht.2⟩
    linarith [BdryExist.radius_le_one k]
  have hb : bdryG γ x = qBoundaryMeasure γ x := if_pos hx
  have hb' : bdryG γ x' = qBoundaryMeasure γ x' := if_pos hx'
  unfold lenG at hn ⊢
  rw [hb] at hn ⊢
  rw [hb']
  refine sInf_eq_of_agree_below (M := n + 1) (fun _ h => h.1.le) (fun _ h => h.1.le)
    (fun a ha => ?_) (exists_mem_lenSet htop L) (by linarith)
  simp only [mem_ofPred_eq]
  constructor
  · rintro ⟨h0, hL⟩
    refine ⟨h0, ?_⟩
    have hsub : Icc 0 a ⊆ Ioo (-(n + 1)) (n + 1) := fun t ht =>
      ⟨by linarith [ht.1, lenG_nonneg γ L x], by linarith [ht.2]⟩
    rwa [← Measure.restrict_eq_self _ hsub, ← hres, Measure.restrict_eq_self _ hsub]
  · rintro ⟨h0, hL⟩
    refine ⟨h0, ?_⟩
    have hsub : Icc 0 a ⊆ Ioo (-(n + 1)) (n + 1) := fun t ht =>
      ⟨by linarith [ht.1, lenG_nonneg γ L x], by linarith [ht.2]⟩
    rwa [← Measure.restrict_eq_self _ hsub, hres, Measure.restrict_eq_self _ hsub]

/-! ## 5. Locality of translation -/

theorem coords_translate_eq_of_agreeNear {x x' : FieldSample} {R y : ℝ}
    (hag : D3Plus.AgreeNear x x' R) {j : ℕ}
    (hj : ‖(dyadicIndex j).1‖ + radius (dyadicIndex j).2 + |y| < R) :
    coords (translate x (y : ℂ)) j = coords (translate x' (y : ℂ)) j := by
  simp only [coords, translate]
  refine D3Plus.evalReg_congr hag
    (ρ := ‖(dyadicIndex j).1‖ + radius (dyadicIndex j).2 + |y|) ?_ hj
  rw [Measure.map_apply (measurable_add_const _) Metric.isClosed_closedBall.measurableSet.compl]
  refine measure_mono_null (fun u hu => ?_)
    (CircleFubini.foldedCircle_support (radius_pos _).le le_rfl)
  simp only [mem_preimage, mem_compl_iff, Metric.mem_closedBall, dist_zero_right] at hu
  simp only [CircleFubini.ballH, mem_compl_iff, mem_inter_iff, Metric.mem_closedBall,
    dist_zero_right, not_and_or]
  left
  intro hu'
  apply hu
  calc ‖u + (y : ℂ)‖ ≤ ‖u‖ + ‖(y : ℂ)‖ := norm_add_le _ _
    _ ≤ _ := by rw [Complex.norm_real, Real.norm_eq_abs]; linarith

/-! ## 6. Locality of the scale parameter -/

theorem scaleParam_eq_of_agreeNear {γ : ℝ} {y y' : FieldSample} (hy : IsLQGGood γ y)
    (hy' : IsLQGGood γ y') {r : ℝ} (hag : D3Plus.AgreeNear y y' r) (hpos : 0 < scaleParam γ y)
    (hlt : scaleParam γ y < r) : scaleParam γ y' = scaleParam γ y := by
  have h1 := D3Plus.qAreaMeasureOn_eq_restrict_of_agree hag
    (Prop16Area.G.isVagueLimitOn_H_of_good hy)
  have h2 := D3Plus.qAreaMeasureOn_eq_restrict_of_agree
    (fun _ _ _ _ => rfl : D3Plus.AgreeNear y' y' r) (Prop16Area.G.isVagueLimitOn_H_of_good hy')
  have hres : (qAreaMeasure γ y).restrict (D3Plus.halfDisc r) =
      (qAreaMeasure γ y').restrict (D3Plus.halfDisc r) := h1.symm.trans h2
  unfold scaleParam at hpos hlt ⊢
  refine sInf_eq_of_agree_below (M := r) (fun _ h => h.1.le) (fun _ h => h.1.le)
    (fun a ha => ?_) ?_ hlt
  · have hsub : Metric.ball (0 : ℂ) a ∩ H ⊆ D3Plus.halfDisc r :=
      inter_subset_inter_left _ (Metric.ball_subset_ball ha.le)
    simp only [mem_ofPred_eq]
    rw [← Measure.restrict_eq_self (qAreaMeasure γ y) hsub,
      ← Measure.restrict_eq_self (qAreaMeasure γ y') hsub, hres]
  · by_contra hne
    rw [not_nonempty_iff_eq_empty] at hne
    rw [hne, Real.sInf_empty] at hpos
    exact lt_irrefl _ hpos

end Raw
end FieldLaw
end S5
end QuantumZipper
