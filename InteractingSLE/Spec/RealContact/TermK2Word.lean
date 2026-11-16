/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.RealContact.TermK2Stop
import InteractingSLE.Spec.Sec5.CrossCondStagedFinalWord
import InteractingSLE.Spec.Supplement.GW2RdHitSet
import InteractingSLE.Spec.Supplement.GW3Word

/-!
# The chart word of the completed second path at untouched points

Packet PROVE-RC-TERM, second run (ruling R124).

* **`stopWord_fn_fwd`**: at the image `Re f_T(x)` of an alive real point `x ≠ 0` off the jumps of the word `c`, the
  stop word `stopWord κ (c, θ, r)` has no jump and the value `c.fn x` (the marks keep their order under the real
  Loewner flow: `GW1W.markPos_le_iff`, `GW1W.le_markPosL_iff`).

* `rightLim_stopWord_markPos`, `leftLim_stopWord_fwd`: the one-sided limits of the stop word at the image of a mark;
* `IsKSample.untouched_real`: an untouched real chart point is the image of an alive real point of the second path's
  flow, at capacity distance `y + τ`;
* **`IsKSample.isUntouchedWord`**: `RLC.IsUntouchedWord` for the seed-centred chart word
  `shiftW τ (stopWord κ (c₂, θ₂, r))` and the boundary inverse `v ↦ kInv v + x₁`;
* **`IsKSample.isAdmissibleSeed`**: the one-sided limits of the chart word at the seed are admissible for the angle
  `θ₁ < θ₂` (distinct seeds: the original limits at `x₁`; common seed: `λ − θ₂χ` on the left).

Deterministic; R48-neutral.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped NNReal ENNReal
open QuantumZipper (H Hbar chiC fwdMap IsForwardSol)

namespace InteractingSLE.RealContact

namespace Term

open LP (reflectC)
open Restart Exist.Staged Exist.StagedLaw PiecewiseConstantBoundaryData

/-- An alive real point has alive real points on both sides, arbitrarily close. -/
theorem exists_alive_real_near {W : ℝ → ℝ} (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T) {x : ℝ}
    (hx : ∃ u, IsForwardSol W (x : ℂ) T u) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, δ < ε ∧ (∃ u, IsForwardSol W ((x + δ : ℝ) : ℂ) T u) ∧ ∃ u, IsForwardSol W ((x - δ : ℝ) : ℂ) T u := by
  obtain ⟨r, hr, hall⟩ := exists_alive_near hW hT hx
  have hm0 : 0 < min (r / 2) (ε / 2) := lt_min (by positivity) (by positivity)
  refine ⟨min (r / 2) (ε / 2), hm0, by linarith [min_le_right (r / 2) (ε / 2)], hall _ ?_, hall _ ?_⟩
  · rw [mem_ball, Complex.dist_eq, ← ofReal_sub, Complex.norm_real, Real.norm_eq_abs, add_sub_cancel_left,
      abs_of_pos hm0]
    linarith [min_le_left (r / 2) (ε / 2)]
  · rw [mem_ball, Complex.dist_eq, ← ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sub_sub_cancel_left,
      abs_neg, abs_of_pos hm0]
    linarith [min_le_left (r / 2) (ε / 2)]

/-- **The stop word at the image of an alive real point** (see the module docstring). -/
theorem stopWord_fn_fwd {κ : ℝ} (hκ : 0 < κ) (c : BoundaryWord) (θ : ℝ) (r : RecData) {x : ℝ} (hx0 : x ≠ 0)
    (hxJ : x ∉ c.jumps) (hal : ∃ u, IsForwardSol (rdrv r) (x : ℂ) (rtime r) u) :
    (fwdMap (rdrv r) (rtime r) (x : ℂ)).re ∉ (stopWord κ (c, θ, r)).jumps ∧
      (fwdMap (rdrv r) (rtime r) (x : ℂ)).re ≠ 0 ∧
      (stopWord κ (c, θ, r)).fn (fwdMap (rdrv r) (rtime r) (x : ℂ)).re = c.fn x := by
  classical
  have hU := continuous_rdrv r
  have hU0 := rdrv_zero r
  have hT := rtime_nonneg r
  have hb := c.isPiecewiseConstantBoundaryData
  set z := (fwdMap (rdrv r) (rtime r) (x : ℂ)).re with hz
  have hflow := Exist.StagedLaw.isRealFlow_fwd hU hU0 hT
  have hxL0 : ∀ i, flowLineXL c.fn c.jumps 0 i ≤ 0 := fun i => Theorem14.GW3Word.flowLineXL_nonpos _ _ i
  have hxR0 : ∀ j, 0 ≤ flowLineXR c.fn c.jumps 0 j := fun j => Theorem14.GW3Word.flowLineXR_nonneg _ _ j
  have hxLne : ∀ i, flowLineXL c.fn c.jumps 0 i ≠ x := fun i he => by
    rcases Theorem14.GW2Rd.flowLineXL_eq_zero_or_mem c.fn c.jumps i with h0 | hJ
    · exact hx0 (he ▸ h0)
    · exact hxJ (he ▸ hJ)
  have hxRne : ∀ j, flowLineXR c.fn c.jumps 0 j ≠ x := fun j he => by
    rcases Theorem14.GW2Rd.flowLineXR_eq_zero_or_mem c.fn c.jumps j with h0 | hJ
    · exact hx0 (he ▸ h0)
    · exact hxJ (he ▸ hJ)
  have hseedv := Exist.forceBoundaryData_flowLine_seed hκ hb 0 θ hx0 (by simpa using hxJ)
  rw [add_zero] at hseedv
  rcases lt_or_gt_of_ne hx0 with hneg | hpos
  · -- left of the seed
    have hzneg : z < 0 := by
      have h1 := hflow.2.2.2.2.1 (-x) (by linarith) (by simpa only [neg_neg] using hal)
      simp only [neg_neg] at h1
      linarith
    have hiff : ∀ i, z < markPosL (rdrv r) (rtime r) (flowLineXL c.fn c.jumps 0 i) ↔
        x < flowLineXL c.fn c.jumps 0 i := by
      intro i
      have hle := Theorem14.GW1W.le_markPosL_iff hU hU0 hT (hxL0 i) hneg hal
      constructor
      · intro hlt
        exact lt_of_le_of_ne (hle.1 hlt.le) (Ne.symm (hxLne i))
      · intro hlt
        obtain ⟨δ, hδ, hδε, hal₁, -⟩ := exists_alive_real_near hU hT hal
          (ε := flowLineXL c.fn c.jumps 0 i - x) (by linarith)
        have h1 := re_fwdMap_lt_of_alive hU hT (a := x) (b := x + δ) (by linarith) hal hal₁
        have h2 := (Theorem14.GW1W.le_markPosL_iff hU hU0 hT (hxL0 i)
          (by linarith [hxL0 i] : x + δ < 0) hal₁).2 (by linarith)
        linarith
    have hzJ : z ∉ (stopWord κ (c, θ, r)).jumps := by
      intro hmem
      rcases Sec5.CrossCond.StagedFinal.mem_jumps_stopWord hmem with ⟨i, hi⟩ | h0 | ⟨j, hj⟩
      · have hle := (Theorem14.GW1W.le_markPosL_iff hU hU0 hT (hxL0 i) hneg hal).1 hi.le
        have hlt : x < flowLineXL c.fn c.jumps 0 i := lt_of_le_of_ne hle (Ne.symm (hxLne i))
        have := (hiff i).2 hlt
        linarith
      · linarith
      · have := Theorem14.GW1W.markPos_nonneg hU hU0 hT (hxR0 j)
        linarith
    refine ⟨hzJ, hzneg.ne, ?_⟩
    rw [Sec5.CrossCond.StagedFinal.fn_stopWord c θ r hzJ hzneg.ne, Sec4.forceBoundaryData_of_neg _ _ _ _ hzneg,
      Finset.filter_congr fun i _ => hiff i]
    rw [Sec4.forceBoundaryData_of_neg _ _ _ _ hneg] at hseedv
    linarith
  · -- right of the seed
    have hzpos : 0 < z := hflow.1.2.2.2.1 x hpos hal
    have hiff : ∀ j, markPos (rdrv r) (rtime r) (flowLineXR c.fn c.jumps 0 j) ≤ z ↔
        flowLineXR c.fn c.jumps 0 j ≤ x := fun j =>
      Theorem14.GW1W.markPos_le_iff hU hU0 hT (hxR0 j) hpos hal
    have hzJ : z ∉ (stopWord κ (c, θ, r)).jumps := by
      intro hmem
      rcases Sec5.CrossCond.StagedFinal.mem_jumps_stopWord hmem with ⟨i, hi⟩ | h0 | ⟨j, hj⟩
      · have := Theorem14.GW1W.markPosL_nonpos hU hU0 hT (hxL0 i)
        linarith
      · linarith
      · have hle := (hiff j).1 hj.ge
        have hlt : flowLineXR c.fn c.jumps 0 j < x := lt_of_le_of_ne hle (hxRne j)
        obtain ⟨δ, hδ, hδε, -, hal₁⟩ := exists_alive_real_near hU hT hal
          (ε := x - flowLineXR c.fn c.jumps 0 j) (by linarith)
        have h1 := re_fwdMap_lt_of_alive hU hT (a := x - δ) (b := x) (by linarith) hal₁ hal
        have h2 := (Theorem14.GW1W.markPos_le_iff hU hU0 hT (hxR0 j)
          (by linarith [hxR0 j] : 0 < x - δ) hal₁).2 (by linarith)
        linarith
    refine ⟨hzJ, hzpos.ne', ?_⟩
    rw [Sec5.CrossCond.StagedFinal.fn_stopWord c θ r hzJ hzpos.ne',
      Sec4.forceBoundaryData_of_nonneg _ _ _ _ hzpos.le, Finset.filter_congr fun j _ => hiff j]
    rw [Sec4.forceBoundaryData_of_nonneg _ _ _ _ hpos.le] at hseedv
    linarith

/-! ### One-sided limits of piecewise constant data -/

theorem exists_jumpfree_right (J : Finset ℝ) (a : ℝ) : ∃ u, a < u ∧ ∀ s ∈ Ioo a u, s ∉ J := by
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 (Sec4.eventually_notMem_nhdsGT J a)
  exact ⟨u, hu, fun s hs => hsub hs⟩

theorem exists_jumpfree_left (J : Finset ℝ) (a : ℝ) : ∃ l, l < a ∧ ∀ s ∈ Ioo l a, s ∉ J := by
  obtain ⟨l, hl, hsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1 (Sec4.eventually_notMem_nhdsLT J a)
  exact ⟨l, hl, fun s hs => hsub hs⟩

theorem rightLim_eq_of_jumpfree {b : ℝ → ℝ} {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J) {a u t : ℝ}
    (hJ : ∀ s ∈ Ioo a u, s ∉ J) (ht : t ∈ Ioo a u) : rightLim b a = b t := by
  refine Sec4.rightLim_eq_of_forall_notMem J (lt_trans ht.1 ht.2) fun s hs _ => ?_
  rcases le_total s t with hst | hts
  · exact (Sec4.eq_of_forall_notMem_of_isPiecewiseConstant hb hst fun z hz =>
      hJ z ⟨lt_of_lt_of_le hs.1 hz.1, lt_of_le_of_lt hz.2 ht.2⟩).symm
  · exact Sec4.eq_of_forall_notMem_of_isPiecewiseConstant hb hts fun z hz =>
      hJ z ⟨lt_of_lt_of_le ht.1 hz.1, lt_of_le_of_lt hz.2 hs.2⟩

theorem leftLim_eq_of_jumpfree {b : ℝ → ℝ} {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J) {l a t : ℝ}
    (hJ : ∀ s ∈ Ioo l a, s ∉ J) (ht : t ∈ Ioo l a) : leftLim b a = b t := by
  refine Sec4.leftLim_eq_of_forall_notMem J (lt_trans ht.1 ht.2) fun s hs _ => ?_
  rcases le_total s t with hst | hts
  · exact (Sec4.eq_of_forall_notMem_of_isPiecewiseConstant hb hst fun z hz =>
      hJ z ⟨lt_of_lt_of_le hs.1 hz.1, lt_of_le_of_lt hz.2 ht.2⟩).symm
  · exact Sec4.eq_of_forall_notMem_of_isPiecewiseConstant hb hts fun z hz =>
      hJ z ⟨lt_of_lt_of_le ht.1 hz.1, lt_of_le_of_lt hz.2 hs.2⟩

/-- **The right limit of the stop word at the position of a mark whose right neighbours are alive** is the right
limit of the original word at the mark. -/
theorem rightLim_stopWord_markPos {κ : ℝ} (hκ : 0 < κ) (c : BoundaryWord) (θ : ℝ) (r : RecData) {a : ℝ}
    (ha : 0 ≤ a) (hal : ∀ y : ℝ, a < y → ∃ u, IsForwardSol (rdrv r) (y : ℂ) (rtime r) u) :
    rightLim (stopWord κ (c, θ, r)).fn (markPos (rdrv r) (rtime r) a) = rightLim c.fn a := by
  have hU := continuous_rdrv r
  have hU0 := rdrv_zero r
  have hT := rtime_nonneg r
  obtain ⟨u₁, hu₁, hJ₁⟩ := exists_jumpfree_right (stopWord κ (c, θ, r)).jumps (markPos (rdrv r) (rtime r) a)
  obtain ⟨u₂, hu₂, hJ₂⟩ := exists_jumpfree_right c.jumps a
  have htend := tendsto_re_fwdMap_markPos hU hU0 hT ha hal
  have hev : ∀ᶠ y : ℝ in 𝓝[>] a, (fwdMap (rdrv r) (rtime r) (y : ℂ)).re < u₁ :=
    htend (Iio_mem_nhds hu₁)
  obtain ⟨y, hy3, hy⟩ := (hev.and (Ioo_mem_nhdsGT hu₂)).exists
  have hy0 : 0 < y := lt_of_le_of_lt ha hy.1
  have hmid : a < (a + y) / 2 ∧ (a + y) / 2 < y := ⟨by linarith [hy.1], by linarith [hy.1]⟩
  have h1 := (Theorem14.GW1W.markPos_le_iff hU hU0 hT ha (lt_of_le_of_lt ha hmid.1) (hal _ hmid.1)).2 hmid.1.le
  have h2 := re_fwdMap_lt_of_alive hU hT hmid.2 (hal _ hmid.1) (hal _ hy.1)
  obtain ⟨-, -, hfn⟩ := stopWord_fn_fwd hκ c θ r hy0.ne' (hJ₂ y hy) (hal y hy.1)
  rw [rightLim_eq_of_jumpfree (stopWord κ (c, θ, r)).isPiecewiseConstantBoundaryData hJ₁
      ⟨lt_of_le_of_lt h1 h2, hy3⟩, hfn,
    rightLim_eq_of_jumpfree c.isPiecewiseConstantBoundaryData hJ₂ hy]

/-- **The left limit of the stop word at the image of an alive point right of the seed** is the left limit of the
original word at the point. -/
theorem leftLim_stopWord_fwd {κ : ℝ} (hκ : 0 < κ) (c : BoundaryWord) (θ : ℝ) (r : RecData) {a : ℝ}
    (ha : 0 < a) (hal : ∃ u, IsForwardSol (rdrv r) (a : ℂ) (rtime r) u) :
    leftLim (stopWord κ (c, θ, r)).fn (fwdMap (rdrv r) (rtime r) (a : ℂ)).re = leftLim c.fn a := by
  have hU := continuous_rdrv r
  have hT := rtime_nonneg r
  obtain ⟨l₁, hl₁, hJ₁⟩ := exists_jumpfree_left (stopWord κ (c, θ, r)).jumps
    (fwdMap (rdrv r) (rtime r) (a : ℂ)).re
  obtain ⟨l₂, hl₂, hJ₂⟩ := exists_jumpfree_left c.jumps a
  obtain ⟨u, hu⟩ := hal
  obtain ⟨r₀, hr₀, hall⟩ := exists_alive_near hU hT ⟨u, hu⟩
  have hcont : ContinuousAt (fun y : ℝ => (fwdMap (rdrv r) (rtime r) (y : ℂ)).re) a :=
    Complex.continuous_re.continuousAt.comp
      ((continuousAt_fwdMap_of_alive hU hT hu).comp Complex.continuous_ofReal.continuousAt)
  have hev : ∀ᶠ y : ℝ in 𝓝[<] a, l₁ < (fwdMap (rdrv r) (rtime r) (y : ℂ)).re :=
    (hcont.tendsto.mono_left nhdsWithin_le_nhds) (Ioi_mem_nhds hl₁)
  have hlow : max (max l₂ (a - r₀)) 0 < a := max_lt (max_lt hl₂ (by linarith)) ha
  obtain ⟨y, hy3, hy⟩ := (hev.and (Ioo_mem_nhdsLT hlow)).exists
  have hy0 : 0 < y := lt_of_le_of_lt (le_max_right _ _) hy.1
  have hyl₂ : l₂ < y := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_left _ _)) hy.1
  have hyr : a - r₀ < y := lt_of_le_of_lt ((le_max_right _ _).trans (le_max_left _ _)) hy.1
  have haly : ∃ v, IsForwardSol (rdrv r) (y : ℂ) (rtime r) v := by
    refine hall _ ?_
    rw [mem_ball, Complex.dist_eq, ← ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_lt]
    constructor <;> linarith [hy.2]
  have h2 := re_fwdMap_lt_of_alive hU hT hy.2 haly ⟨u, hu⟩
  obtain ⟨-, -, hfn⟩ := stopWord_fn_fwd hκ c θ r hy0.ne' (hJ₂ y ⟨hyl₂, hy.2⟩) haly
  rw [leftLim_eq_of_jumpfree (stopWord κ (c, θ, r)).isPiecewiseConstantBoundaryData hJ₁ ⟨hy3, h2⟩, hfn,
    leftLim_eq_of_jumpfree c.isPiecewiseConstantBoundaryData hJ₂ ⟨hyl₂, hy.2⟩]

/-- The position of an alive mark right of the seed is its image under the real flow. -/
theorem markPos_eq_fwd {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ} (hT : 0 ≤ T) {a : ℝ} (ha : 0 < a)
    (hal : ∃ u, IsForwardSol W (a : ℂ) T u) : markPos W T a = (fwdMap W T (a : ℂ)).re := by
  obtain ⟨u, hu⟩ := hal
  rw [markPos_eq hW hW0 hT (isMark_of_isForwardSol hW hW0 ha hT hu),
    QuantumZipper.F1.fwdMap_eq_of_isForwardSol hu ⟨hT, le_rfl⟩]

/-! ### The chart word in the original orientation -/

namespace IsKSample

variable {U : ℝ → ℝ} {T : ℝ≥0} {ρ₂ : ℝ → ℂ} {q d : ℝ} {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {ρ₁ : ℝ≥0 → ℂ}
  (h : IsKSample U T ρ₂ q d w ζ ρ₁)
include h

/-- Real points right of the first seed are alive for the second path. -/
theorem alive_of_gt {y : ℝ} (hy : d < y) : ∃ u, IsForwardSol U (y : ℂ) (T : ℝ) u := by
  have hE := IsPathSample.entry h
  have h1 := hE.alive_of_lt (x := -y) (by linarith)
  have h2 := (Exist.StagedLaw.alive_neg_iff U (T : ℝ) (-y)).1 h1
  rwa [neg_neg] at h2

/-- For distinct seeds the first seed is alive for the second path. -/
theorem alive_seed (hd : 0 < d) : ∃ u, IsForwardSol U (d : ℂ) (T : ℝ) u := by
  have hE := IsPathSample.entry h
  have hf := (IsPathSample.isRetPath h).isFreeAt_zero hd
  have hf' : HalfPlaneSep.IsFreeAt (entryPath (fun s => reflectC (ρ₂ s)) (T : ℝ) d '' Icc 0 1) (0 : ℂ) := by
    rw [← retSet_eq (IsPathSample.tpos h)]
    exact hf
  have h1 := hE.alive_of_isFreeAt (z := 0) (by simp) (fun h0 => hd.ne' (by exact_mod_cast h0.symm)) hf'
  have h1' : ∃ u, IsForwardSol (-U) ((-d : ℝ) : ℂ) (T : ℝ) u := by
    rwa [zero_sub, ← ofReal_neg] at h1
  have h2 := (Exist.StagedLaw.alive_neg_iff U (T : ℝ) (-d)).1 h1'
  rwa [neg_neg] at h2

/-- **An untouched real chart point is the image of an alive real point of the second path's flow.** -/
theorem untouched_real {y : ℝ}
    (hK : reflectC (kInv U (T : ℝ) d (y : ℂ)) ∉ retSet (fun s => reflectC (ρ₂ s)) T d) :
    ∃ x' : ℝ, kInv U (T : ℝ) d (y : ℂ) + (d : ℂ) = (x' : ℂ) ∧ x' ≠ 0 ∧
      (∃ u, IsForwardSol U (x' : ℂ) (T : ℝ) u) ∧
      (fwdMap U (T : ℝ) (x' : ℂ)).re = y + markPos U (T : ℝ) d := by
  have hE := IsPathSample.entry h
  have hret := retSet_eq (IsPathSample.tpos h) (fun s => reflectC (ρ₂ s)) d
  have e2 : reflectC (kInv U (T : ℝ) d (y : ℂ)) = entryInv (-U) (T : ℝ) d ((-y : ℝ) : ℂ) := by
    unfold kInv
    rw [LP.reflectC_reflectC, reflectC_ofReal']
  rw [e2, hret] at hK
  obtain ⟨xb, hxb, hxbd, hf, he⟩ := hE.entryInv_untouched hK
  obtain ⟨hal, hF⟩ := hE.entryExt_ofReal hxbd hf
  refine ⟨d - xb, ?_, sub_ne_zero.2 (Ne.symm hxbd), ?_, ?_⟩
  · have h1 := congrArg reflectC e2
    rw [LP.reflectC_reflectC, hxb, reflectC_ofReal'] at h1
    rw [h1]
    push_cast
    ring
  · have h2 := (Exist.StagedLaw.alive_neg_iff U (T : ℝ) (xb - d)).1 hal
    rwa [neg_sub] at h2
  · have e : -y = (fwdMap (-U) (T : ℝ) ((xb - d : ℝ) : ℂ)).re - markPosL (-U) (T : ℝ) (-d) := by
      have := he.symm.trans hF
      exact_mod_cast this
    have hfun : (fun s => -(-U) s) = U := funext fun s => by simp
    have hmL : markPosL (-U) (T : ℝ) (-d) = -markPos U (T : ℝ) d := by
      unfold markPosL
      rw [hfun, neg_neg]
    have hr : (fwdMap (-U) (T : ℝ) ((xb - d : ℝ) : ℂ)).re = -(fwdMap U (T : ℝ) ((d - xb : ℝ) : ℂ)).re := by
      have h2 := QuantumZipper.F1.fwdMap_reflect_ofReal U T.coe_nonneg (d - xb)
      rw [neg_sub] at h2
      rw [h2, Complex.neg_re]
    rw [hr, hmL] at e
    linarith

/-- **The chart word is the original datum at the untouched real chart points.** -/
theorem isUntouchedWord {κ : ℝ} (hκ : 0 < κ) {r : RecData} (hU : rdrv r = U) (hT : rtime r = (T : ℝ))
    {b : ℝ → ℝ} {jumps : Finset ℝ} {x₁ x₂ θ₂ : ℝ} (hd : d = x₁ - x₂) {c₂ : BoundaryWord}
    (hcJ : c₂.jumps = jumps.image (· - x₂)) (hcb : ∀ y ∉ jumps.image (· - x₂), c₂.fn y = b (y + x₂))
    {Kp : Set ℂ} (hK : ∀ z : ℂ, z ∈ Kp ↔
      reflectC (z - (x₁ : ℂ)) ∈ retSet (fun s => reflectC (ρ₂ s)) T d ∨ z = (x₁ : ℂ)) :
    RLC.IsUntouchedWord b jumps Kp (fun v => kInv U (T : ℝ) d v + (x₁ : ℂ))
      (BoundaryWord.shiftW (markPos U (T : ℝ) d) (stopWord κ (c₂, θ₂, r))) := by
  intro y _ hyK hyJ
  have hK' : reflectC (kInv U (T : ℝ) d (y : ℂ)) ∉ retSet (fun s => reflectC (ρ₂ s)) T d := fun hmem =>
    hyK ((hK _).2 (Or.inl (by rwa [add_sub_cancel_right])))
  obtain ⟨x', hx', hx'0, hal, hval⟩ := h.untouched_real hK'
  have hψ : kInv U (T : ℝ) d (y : ℂ) + (x₁ : ℂ) = ((x' + x₂ : ℝ) : ℂ) := by
    have h1 : kInv U (T : ℝ) d (y : ℂ) = (x' : ℂ) - (d : ℂ) := eq_sub_of_add_eq hx'
    rw [h1, hd]
    push_cast
    ring
  have hyJ' : x' + x₂ ∉ jumps := by
    have := hyJ
    simp only [hψ, ofReal_re] at this
    exact this
  have hx'J : x' ∉ jumps.image (· - x₂) := by
    intro hm
    obtain ⟨j, hj, hje⟩ := Finset.mem_image.1 hm
    refine hyJ' ?_
    have : x' + x₂ = j := by linarith
    rw [this]
    exact hj
  have hsw := stopWord_fn_fwd hκ c₂ θ₂ r hx'0 (by rw [hcJ]; exact hx'J) (by rw [hU, hT]; exact hal)
  rw [hU, hT, hval] at hsw
  obtain ⟨hzJ, -, hfn⟩ := hsw
  constructor
  · rw [BoundaryWord.jumps_shiftW]
    intro hm
    obtain ⟨j, hj, hje⟩ := Finset.mem_image.1 hm
    refine hzJ ?_
    have : y + markPos U (T : ℝ) d = j := by
      have hje' : j - markPos U (T : ℝ) d = y := hje
      linarith
    rw [this]
    exact hj
  · show (BoundaryWord.shiftW (markPos U (T : ℝ) d) (stopWord κ (c₂, θ₂, r))).fn y =
      b (kInv U (T : ℝ) d (y : ℂ) + (x₁ : ℂ)).re
    rw [BoundaryWord.fn_shiftW, hfn, hcb x' hx'J, hψ, ofReal_re]

/-- **The seed of the chart word is admissible.** -/
theorem isAdmissibleSeed {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hq : q < 0) {r : RecData} (hU : rdrv r = U)
    (hT : rtime r = (T : ℝ)) {b : ℝ → ℝ} {jumps : Finset ℝ} {x₁ x₂ θ₁ θ₂ : ℝ} (hd : d = x₁ - x₂)
    (hθ : θ₁ < θ₂) {c₂ : BoundaryWord} (hcb : ∀ y ∉ jumps.image (· - x₂), c₂.fn y = b (y + x₂))
    (hv0 : leftLim b x₁ + θ₁ * chiC κ < sleLambda κ ∧ -sleLambda κ < rightLim b x₁ + θ₁ * chiC κ) :
    ExplState.IsAdmissibleSeed κ
      (leftLim (BoundaryWord.shiftW (markPos U (T : ℝ) d) (stopWord κ (c₂, θ₂, r))).fn 0)
      (rightLim (BoundaryWord.shiftW (markPos U (T : ℝ) d) (stopWord κ (c₂, θ₂, r))).fn 0) θ₁ := by
  have hE := IsPathSample.entry h
  have hd0 : 0 ≤ d := hE.seed
  have hfn : (BoundaryWord.shiftW (markPos U (T : ℝ) d) (stopWord κ (c₂, θ₂, r))).fn =
      fun y => (stopWord κ (c₂, θ₂, r)).fn (y + markPos U (T : ℝ) d) :=
    funext fun y => BoundaryWord.fn_shiftW _ _ y
  have hx : d + x₂ = x₁ := by rw [hd]; ring
  have hRb : rightLim c₂.fn d = rightLim b x₁ := by
    rw [show rightLim c₂.fn = rightLim fun y => b (y + x₂) from Restart.rightLim_congr hcb,
      Exist.rightLim_comp_add, hx]
  have hLb : leftLim c₂.fn d = leftLim b x₁ := by
    rw [show leftLim c₂.fn = leftLim fun y => b (y + x₂) from Restart.leftLim_congr hcb,
      Exist.leftLim_comp_add, hx]
  have hR : rightLim (stopWord κ (c₂, θ₂, r)).fn (markPos U (T : ℝ) d) = rightLim b x₁ := by
    have h1 := rightLim_stopWord_markPos hκ c₂ θ₂ r hd0 (fun y hy => by rw [hU, hT]; exact h.alive_of_gt hy)
    rw [hU, hT] at h1
    rw [h1, hRb]
  rw [hfn, Exist.leftLim_comp_add, Exist.rightLim_comp_add, zero_add, hR]
  refine ⟨?_, hv0.2⟩
  rcases hd0.lt_or_eq with hpos | hzero
  · have hal := h.alive_seed hpos
    have h1 := leftLim_stopWord_fwd hκ c₂ θ₂ r hpos (by rw [hU, hT]; exact hal)
    rw [hU, hT, ← markPos_eq_fwd (by rw [← hU]; exact continuous_rdrv r) (by rw [← hU]; exact rdrv_zero r)
      T.coe_nonneg hpos hal] at h1
    rw [h1, hLb]
    exact hv0.1
  · have hpos0 : 0 < markPos U (T : ℝ) 0 := h.markPos_zero_pos hq
    have hL : leftLim (stopWord κ (c₂, θ₂, r)).fn (markPos U (T : ℝ) d) = sleLambda κ - θ₂ * chiC κ := by
      rw [← hzero]
      refine Sec4.leftLim_eq_of_forall_notMem (stopWord κ (c₂, θ₂, r)).jumps hpos0 fun t ht htJ => ?_
      have h2 := (Theorem14.GW2Sdp.fn_stopWord_right hκ c₂ θ₂ r (le_refl 0) ht.1 htJ).1
        (by rw [hU, hT]; exact ht.2)
      rcases h2 with h3 | ⟨y, hy1, hy2, -⟩
      · exact h3
      · exact absurd (hy1.trans hy2) (lt_irrefl 0)
    rw [hL]
    have hχ := Sec4.chiC_pos hκ hκ4
    nlinarith

end IsKSample

end Term

end InteractingSLE.RealContact
