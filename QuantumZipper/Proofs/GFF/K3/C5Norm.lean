import QuantumZipper.Proofs.GFF.K3.C5Assembly
import QuantumZipper.Proofs.GFF.K3.DisjointUnion

/-!
# GFF-K3, node C5 (via C5′): the dual norm on `ℍ \ η[0,T]` as a `V_T`-energy

Blueprint `blueprint/EXT_PP_BLUEPRINT.md` §B (C5′) and `blueprint/GFF_K3_BLUEPRINT.md` §3.C
node C5.  C3 (`dualNormSq_iUnion_of_pairwise_disjoint`) splits the dual norm over the pieces
`c5Piece`; C2 (`dualNormSq_eq_kerInt` with `f_T`) evaluates the `D_T` piece; C5′
(`dualNormSq_bubble_eq_lintegral`, with BUB-4) evaluates each bubble along `t_n ↑ τ`; item 5
(`VTe_eq_zero_of_mem_c5Piece`) kills the cross terms; zero area of the trace (AD-2) removes
`η[0,T]` itself:

`‖g dz‖²_{U_T} = ∬ g(a) g(b) V_T(a,b) da db` (`dualNormSq_compl_image_eq`).

Source: Sheffield, arXiv:1012.4797, Theorem 1.1 addendum (p. 12), route of the blueprint C5′.
-/

noncomputable section

open Set Filter Topology MeasureTheory Function
open scoped ENNReal

namespace QuantumZipper.K3

variable {W : ℝ → ℝ} {η : ℝ → ℂ} {T : ℝ}

theorem dualNormSq_empty_eq_zero (μ : Measure ℂ) : dualNormSq ∅ (zeroSpace ∅) μ = 0 := by
  refine le_antisymm (iSup₂_le fun f hf => ?_) bot_le
  exfalso
  have h := hf.2
  simp [dirichletEnergyOn] at h

/-- The approximating times `t_n = τ (1 - 1/(n+1)) ↑ τ`. -/
def c5Time (τ : ℝ) (n : ℕ) : ℝ := τ - τ * (1 / ((n : ℝ) + 1))

theorem c5Time_props {τ : ℝ} (hτ : 0 < τ) :
    Monotone (c5Time τ) ∧ (∀ n, 0 ≤ c5Time τ n) ∧ (∀ n, c5Time τ n < τ) ∧
      Tendsto (c5Time τ) atTop (𝓝 τ) := by
  refine ⟨fun n m hnm => ?_, fun n => ?_, fun n => ?_, ?_⟩
  · have hc : (n : ℝ) + 1 ≤ (m : ℝ) + 1 := by
      have := (Nat.cast_le (α := ℝ)).2 hnm; linarith
    have : 1 / ((m : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) := one_div_le_one_div_of_le (by positivity) hc
    unfold c5Time; nlinarith
  · have : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
    unfold c5Time; nlinarith
  · have : 0 < 1 / ((n : ℝ) + 1) := by positivity
    unfold c5Time; nlinarith
  · have h := (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul τ).const_sub τ
    rw [mul_zero, sub_zero] at h
    exact h

/-- **Each piece.** The dual norm on a piece is the `V_T`-energy of the density restricted to
it: C2 with `f_T` on `D_T`, C5′ (BUB-4) on a bubble, `0` on `∅`. -/
theorem dualNormSq_c5Piece (hBUB4 : BUB4Stmt) (hg : GenTrace W η) (hT : 0 ≤ T)
    (hS : (bubbleIdx W η T).Countable) {g : ℂ → ℝ≥0∞} {M : ℝ≥0∞} {R : ℝ}
    (hu : BddDens g M R) (n : ℕ) :
    dualNormSq (c5Piece W η T hS n) (zeroSpace (c5Piece W η T hS n)) (volume.withDensity g) =
      ∫⁻ p, (c5Piece W η T hS n).indicator g p.1 *
        ((c5Piece W η T hS n).indicator g p.2 * VTe W T p.1 p.2)
          ∂((volume : Measure ℂ).prod volume) := by
  cases n with
  | zero =>
    have hφ := isConformalOnto_fwdMap hg.contW hg.zeroW hT
    rw [show c5Piece W η T hS 0 = H \ fwdHull W T from rfl]
    rw [dualNormSq_eq_kerInt hφ diff_subset hu, kerInt]
    refine lintegral_congr fun p => ?_
    unfold kerDens confKer
    by_cases h1 : p.1 ∈ H \ fwdHull W T
    · by_cases h2 : p.2 ∈ H \ fwdHull W T
      · rw [confMod_eqOn h1, confMod_eqOn h2, VTe_eq_vtKer_of_lt hg.contW h1.1 h2.1 hT
          (not_le.1 fun h => h1.2 ⟨h1.1, h⟩) (not_le.1 fun h => h2.2 ⟨h2.1, h⟩)]
        rfl
      · simp [indicator_of_notMem h2]
    · simp [indicator_of_notMem h1]
  | succ m =>
    rcases c5Piece_succ hS m with h | ⟨τ, -, h⟩
    · rw [h, dualNormSq_empty_eq_zero]; simp
    rw [h]
    have hτT : τ.1 ≤ T := τ.2.1.2
    obtain ⟨z0, hz0⟩ := τ.2.2
    have hτ0 : 0 < τ.1 := by
      have := swallowTime_pos hg.contW hz0.1.1
      rw [hz0.2] at this; exact ENNReal.ofReal_pos.1 this
    have hΩo : IsOpen (bubbleSet W η T τ.1) := hg.isOpen_bubbleSet hτT
    haveI := isFiniteMeasure_withDensity_bdd hu.lt_top hu.le hu.zero
    rw [dualNormSq_zeroSpace_restrict hΩo, restrict_withDensity hΩo.measurableSet,
      ← withDensity_indicator hΩo.measurableSet]
    obtain ⟨hmono, ht0, hlt, hlim⟩ := c5Time_props hτ0
    obtain ⟨r, hr0, hr, hrb⟩ := hg.exists_gate_radius hτ0.le ht0 (fun n => (hlt n).le) hlim
    obtain ⟨d, hd, hfat⟩ :=
      hg.exists_fat ht0 hr0 (fun n => hrb n (c5Time τ.1 n) ⟨le_rfl, (hlt n).le⟩)
    refine dualNormSq_bubble_eq_lintegral hBUB4 (D := fun n => H \ fwdHull W (c5Time τ.1 n))
      (φ := fun n => fwdMap W (c5Time τ.1 n))
      (fun n => isConformalOnto_fwdMap hg.contW hg.zeroW (ht0 n))
      (fun n => diff_subset) hΩo (fun n => bubbleSet_subset_compl_fwdHull (ht0 n) (hlt n)) hr0 hr
      (fun n z hz => ?_) hd hfat (hu.meas.indicator hΩo.measurableSet)
      ⟨M, hu.lt_top, fun z => (indicator_le_self _ _ z).trans (hu.le z)⟩
      (fun z hz => indicator_of_notMem hz _) ?_ (V := fun q => VTe W T q.1 q.2)
      (fun q hq => ?_) (fun q hq => ?_)
    · obtain ⟨s, hs, rfl⟩ := hg.frontier_bubbleSet_inter_subset hτT (ht0 n) (hlt n) hz
      rw [Metric.mem_closedBall, dist_eq_norm]
      exact hrb n s ⟨hs.1.le, hs.2⟩
    · refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := R)).subset fun z hz => ?_
      by_contra hzR
      refine hz ?_
      rcases em (z ∈ bubbleSet W η T τ.1) with hzΩ | hzΩ
      · rw [indicator_of_mem hzΩ, hu.zero z hzR]
      · rw [indicator_of_notMem hzΩ]
    · exact (tendsto_vtKer_bubble hg.contW hq.1.1.1 hq.2.1.1 hq.1.2 hq.2.2 hτT hmono ht0 hlt
        hlim).1
    · exact (tendsto_vtKer_bubble hg.contW hq.1.1.1 hq.2.1.1 hq.1.2 hq.2.2 hτT hmono ht0 hlt
        hlim).2

/-- **C5′, dual-norm form.** For a curve-generated chain whose trace `η[0,T]` has zero area in
`ℍ`, and a bounded density `g` with bounded support in `ℍ`,
`‖g dz‖²_{ℍ \ η[0,T]} = ∬ g(a) g(b) V_T(a,b)`. -/
theorem dualNormSq_compl_image_eq (hBUB4 : BUB4Stmt) (hg : GenTrace W η) (hT : 0 ≤ T)
    (harea : volume (η '' Icc 0 T ∩ H) = 0) {g : ℂ → ℝ≥0∞} {M : ℝ≥0∞} {R : ℝ}
    (hu : BddDens g M R) (hgH : ∀ z ∉ H, g z = 0) :
    dualNormSq (H \ η '' Icc 0 T) (zeroSpace (H \ η '' Icc 0 T)) (volume.withDensity g) =
      ∫⁻ p, g p.1 * (g p.2 * VTe W T p.1 p.2) ∂((volume : Measure ℂ).prod volume) := by
  have hS := hg.countable_bubbleIdx T
  set P := c5Piece W η T hS with hP
  set U := H \ η '' Icc 0 T with hU
  have hPU : ⋃ n, P n = U := iUnion_c5Piece hg hT hS
  have hPsub : ∀ n, P n ⊆ U := c5Piece_subset hg hT hS
  set F : ℕ → ℂ × ℂ → ℝ≥0∞ := fun n p =>
    (P n).indicator g p.1 * ((P n).indicator g p.2 * VTe W T p.1 p.2) with hF
  have hVm := measurable_indicator_VTe hg.contW hg.zeroW T
  have hFm : ∀ n, Measurable (F n) := by
    intro n
    have hPm := (isOpen_c5Piece hg hT hS n).measurableSet
    have : F n = fun p => (P n).indicator g p.1 * ((P n).indicator g p.2 *
        (H ×ˢ H).indicator (fun p : ℂ × ℂ => VTe W T p.1 p.2) p) := by
      funext p
      simp only [F]
      by_cases h1 : p.1 ∈ P n
      · by_cases h2 : p.2 ∈ P n
        · rw [indicator_of_mem (show p ∈ H ×ˢ H from ⟨(hPsub n h1).1, (hPsub n h2).1⟩)]
        · simp [F, indicator_of_notMem h2]
      · simp [F, indicator_of_notMem h1]
    rw [this]
    exact ((hu.meas.indicator hPm).comp measurable_fst).mul
      (((hu.meas.indicator hPm).comp measurable_snd).mul hVm)
  -- pointwise: the sum over pieces is the `U × U` restriction (item 5 for cross terms)
  have hpt : ∀ p : ℂ × ℂ, ∑' n, F n p = U.indicator g p.1 * (U.indicator g p.2 * VTe W T p.1 p.2) := by
    intro p
    by_cases ha : p.1 ∈ U
    · obtain ⟨n0, hn0⟩ := mem_iUnion.1 (hPU ▸ ha : p.1 ∈ ⋃ n, P n)
      rw [tsum_eq_single n0 fun n hn => by
        simp only [F]
        rw [indicator_of_notMem (fun h => hn (c5Piece_eq_of_swallowTime_eq hS h hn0 rfl)),
          zero_mul]]
      simp only [F]
      rw [indicator_of_mem hn0, indicator_of_mem ha]
      by_cases hb : p.2 ∈ P n0
      · rw [indicator_of_mem hb, indicator_of_mem (hPsub n0 hb)]
      · rw [indicator_of_notMem hb, zero_mul, mul_zero]
        by_cases hbU : p.2 ∈ U
        · obtain ⟨m, hm⟩ := mem_iUnion.1 (hPU ▸ hbU : p.2 ∈ ⋃ n, P n)
          rw [VTe_eq_zero_of_mem_c5Piece hg hS (fun h => hb (by rw [h]; exact hm)) hn0 hm, mul_zero,
            mul_zero]
        · rw [indicator_of_notMem hbU, zero_mul, mul_zero]
    · have h0 : ∀ n, F n p = 0 := fun n => by
        simp [F, indicator_of_notMem (fun h => ha (hPsub n h))]
      rw [tsum_congr h0, tsum_zero, indicator_of_notMem ha, zero_mul]
  -- the trace has zero area
  have hae : ∀ᵐ z ∂(volume : Measure ℂ), U.indicator g z = g z := by
    refine measure_mono_null (fun z hz => ?_) harea
    have hz' : ¬ U.indicator g z = g z := hz
    by_cases hzU : z ∈ U
    · exact absurd (indicator_of_mem hzU g) hz'
    · by_cases hzH : z ∈ H
      · exact ⟨by_contra fun h => hzU ⟨hzH, h⟩, hzH⟩
      · exact absurd (by rw [indicator_of_notMem hzU, hgH z hzH]) hz'
  have hae2 := (Measure.quasiMeasurePreserving_fst.ae hae).and
    (Measure.quasiMeasurePreserving_snd.ae hae)
  rw [← hPU, dualNormSq_iUnion_of_pairwise_disjoint P (isOpen_c5Piece hg hT hS)
    (pairwise_disjoint_c5Piece hS)]
  calc ∑' n, dualNormSq (P n) (zeroSpace (P n)) (volume.withDensity g)
      = ∑' n, ∫⁻ p, F n p ∂((volume : Measure ℂ).prod volume) :=
        tsum_congr fun n => dualNormSq_c5Piece hBUB4 hg hT hS hu n
    _ = ∫⁻ p, ∑' n, F n p ∂((volume : Measure ℂ).prod volume) :=
        (lintegral_tsum fun n => (hFm n).aemeasurable).symm
    _ = ∫⁻ p, U.indicator g p.1 * (U.indicator g p.2 * VTe W T p.1 p.2)
          ∂((volume : Measure ℂ).prod volume) := lintegral_congr hpt
    _ = _ := lintegral_congr_ae (hae2.mono fun p hp => by beta_reduce; rw [hp.1, hp.2])

end QuantumZipper.K3
