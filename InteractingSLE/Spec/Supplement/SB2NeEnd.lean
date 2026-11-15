/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2NeRel
import InteractingSLE.Spec.Supplement.SB2JvEnd

/-!
# The end of F2b′'s relative curve

Packet PROVE-AUX61-NOJUMP (round 22, component F).

* `offset_eq`: two driven canonical curves of the same piece have the same offset;
* **`capLife_top_of_good`**: at an infinite B-stage the relative curve has infinite capacity lifetime (LIFTSET's
  `Lk.canon_old_top`, its density input from `mem_closure_goodU`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar chiC)

namespace InteractingSLE.Theorem14.SB.Ne

open Sec7.PocketTraversal Sec7.Lemma71C Lk LuM GW1Bookkeep Exist Exist.Staged Exist.StagedLaw GW1Conn Dv Mz Nc

/-- **Two driven canonical curves of the same piece have the same offset.** -/
theorem offset_eq {X : Set ℂ} (hA : IsHPHull (fillH X)) {p : ℝ≥0 → ℂ} {L : ℝ≥0∞} (hL : L ≠ 0)
    (hpc : ContinuousOn p {t | (t : ℝ≥0∞) ≤ L}) {x₀ x₁ : ℝ} (hdr : IsDrivenCurve (canonCurve X x₀ p L))
    (hdr' : IsDrivenCurve (canonCurve X x₁ p L)) : x₀ = x₁ := by
  set G : Set ℝ := {v' : ℝ | 0 ≤ v' ∧ Nc.cTime L v' ∈ canonGood X p L} with hG
  have hcl := mem_closure_goodU (x₀ := x₀) hA.2.2.1 hL hpc hdr (le_refl (0 : ℝ))
  have : (𝓝[G] (0 : ℝ)).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hcl
  have hGs : G ⊆ Ici 0 := fun v' hv' => hv'.1
  have h0 : Tendsto (canonCurve X x₀ p L) (𝓝[G] 0) (𝓝 0) := by
    have := (hdr.continuousOn 0 (le_refl (0 : ℝ))).tendsto.mono_left (nhdsWithin_mono _ hGs)
    rwa [hdr.zero] at this
  have h1 : Tendsto (canonCurve X x₁ p L) (𝓝[G] 0) (𝓝 0) := by
    have := (hdr'.continuousOn 0 (le_refl (0 : ℝ))).tendsto.mono_left (nhdsWithin_mono _ hGs)
    rwa [hdr'.zero] at this
  have he : ∀ v ∈ G, canonCurve X x₁ p L v = canonCurve X x₀ p L v + ((x₀ - x₁ : ℝ) : ℂ) := by
    intro v hv
    rw [canonCurve_eq_fwd hL hv.1 hv.2.2, canonCurve_eq_fwd hL hv.1 hv.2.2, Mo.hullChart_fwd, Mo.hullChart_fwd]
    push_cast; ring
  have h2 : Tendsto (canonCurve X x₁ p L) (𝓝[G] 0) (𝓝 (0 + ((x₀ - x₁ : ℝ) : ℂ))) :=
    (h0.add_const _).congr' (eventually_nhdsWithin_of_forall fun v hv => (he v hv).symm)
  have h3 := tendsto_nhds_unique h1 h2
  rw [zero_add] at h3
  have : (x₀ - x₁ : ℝ) = 0 := by exact_mod_cast h3.symm
  linarith

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type*} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {u : ℝ}
  {l : List (ℝ × ℝ≥0)} {k ℓ : ℕ} {K : Ω → Set ℂ} {x₀ : Ω → ℝ} {Ê : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {ω : Ω}

/-- The relative stage curve, read on the retained union. -/
theorem bRel_eq_retX (hg : StageGoodAt κ b jumps E u l k ℓ K x₀ Ê ω) :
    bRel κ b jumps E ℓ K x₀ ω =
      canonCurve (retX κ b jumps E u l k ℓ ω) (x₀ ω) (bPc κ b jumps E ℓ ω) (bLife b jumps E ℓ ω) := by
  unfold bRel canonCurve canonVal canonGood
  rw [hg.fill]

/-- **At an infinite B-stage the relative curve has infinite capacity lifetime.** -/
theorem capLife_top_of_good (hg : StageGoodAt κ b jumps E u l k ℓ K x₀ Ê ω) (htop : bLife b jumps E ℓ ω = ⊤) :
    capLife (bRel κ b jumps E ℓ K x₀ ω) = ⊤ := by
  classical
  have hl := hg.stage.2
  have hev := even_of_launch hl
  have hre := relOff_even κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
    (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω)
  obtain ⟨hro, e', he', hent⟩ := relOffEvent_of_walkGood hg.walk
  have hge : e' + 1 ≤ ℓ := by have := hg.off; omega
  set θ : ℝ := -(Real.pi / 2) with hθ
  set w := boundaryWalkSpec b jumps θ true with hw
  set D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞ := fun i => E w i ω with hDdef
  have hR : ((realMax (upperPrefix κ b jumps E u l k ω) : ℝ) : ℂ) ∈
      statePhysicalSet 0 (ExplState.run κ b jumps w D ℓ) :=
    statePhysicalSet_mono (κ := κ) (θ := θ) (b := b) (jumps := jumps) (D := D) hge hent
  obtain ⟨pA, hpc, hp0, hpH, hpv, hpA⟩ := hg.walk.upath
  obtain ⟨β, hβ, hβ0, hβr, hS1, hS3⟩ := hg.walk.proper
  obtain ⟨⟨c₀, θ₀⟩, hl'⟩ := Option.ne_none_iff_exists'.1 hl
  have hnd := WalkIntRunChron.not_done_of_launch _ _ hl'
  have hdr : IsDrivenCurve (canonCurve (retX κ b jumps E u l k ℓ ω) (x₀ ω) (bPc κ b jumps E ℓ ω)
      (bLife b jumps E ℓ ω)) := by rw [← bRel_eq_retX hg]; exact hg.driven
  have hbpc := continuousOn_bPc hg
  have hden : ∀ t : ℝ≥0, t ∈ closure {t' : ℝ≥0 |
      pcPt (ExplState.run κ b jumps w D ℓ) (D ℓ) t' ∈ H \ fillH (pA '' Icc 0 1)} := by
    intro t
    have hcl := mem_closure_goodU hg.hull.2.2.1 hg.pos hbpc hdr (NNReal.coe_nonneg t)
    have hsub : (fun v : ℝ => Nc.cTime (bLife b jumps E ℓ ω) v) ''
        {v' : ℝ | 0 ≤ v' ∧ Nc.cTime (bLife b jumps E ℓ ω) v' ∈
          canonGood (retX κ b jumps E u l k ℓ ω) (bPc κ b jumps E ℓ ω) (bLife b jumps E ℓ ω)} ⊆
        {t' : ℝ≥0 | pcPt (ExplState.run κ b jumps w D ℓ) (D ℓ) t' ∈ H \ fillH (pA '' Icc 0 1)} := by
      rintro _ ⟨v, hv, rfl⟩
      refine ⟨hv.2.2.1, fun hF => hv.2.2.2 ?_⟩
      exact fillH_mono (by rw [hpA]; exact subset_union_left) hF
    have hct : ContinuousWithinAt (fun v : ℝ => Nc.cTime (bLife b jumps E ℓ ω) v)
        {v' : ℝ | 0 ≤ v' ∧ Nc.cTime (bLife b jumps E ℓ ω) v' ∈
          canonGood (retX κ b jumps E u l k ℓ ω) (bPc κ b jumps E ℓ ω) (bLife b jumps E ℓ ω)} (t : ℝ) :=
      (Nc.continuousOn_cTime (t : ℝ) (NNReal.coe_nonneg t)).mono fun v hv => hv.1
    have h1 := hct.mem_closure_image hcl
    have heq : Nc.cTime (bLife b jumps E ℓ ω) (t : ℝ) = t := by
      unfold Nc.cTime Nc.rTime
      rw [htop]
      simp
    rw [heq] at h1
    exact closure_mono hsub h1
  have hcap := canon_old_top hg.walk.reg hg.walk.chain hg.walk.noLeftMove hg.walk.noLeftHit hl hg.pos htop
    (hg.walk.pinv ℓ hnd).1 hpc hp0 hpH hpv hβ hβ0 hβr (by rw [hpA]; exact hS1) (by rw [hpA]; exact hR)
    (by rw [hpA]; exact hS3) hden
  obtain ⟨x₁, ζ, hdr₁, -, -, -, hcapT⟩ := hcap
  have hX : pA '' Icc 0 1 ∪ SB.prefixPhysSet κ b jumps w D ℓ = retX κ b jumps E u l k ℓ ω := by
    rw [hpA]; rfl
  rw [hX] at hdr₁ hcapT
  have hdr' := hdr
  have hbpc' := hbpc
  rw [htop] at hdr' hbpc'
  have hx : x₀ ω = x₁ := offset_eq hg.hull ENNReal.top_ne_zero hbpc' hdr' hdr₁
  rw [bRel_eq_retX hg, htop, hx]
  exact hcapT


/-! ### A bad physical endpoint is a bad relative point -/

section Conv

open PiecewiseConstantBoundaryData (rightLim)

variable {g : ℂ → ℂ} {R x₀' : ℝ} {β : Restart.BoundaryWord} {Fy : Finset ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ}
  {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

/-- **An original right-bad point read back from a relative point right of the seed makes it a bad relative point**
(D34's clause, right side: the relative heights just right of it are the original heights just right of the point). -/
theorem rel_bad_of_phys (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hmono : StrictMonoOn (fun y : ℝ => (g (y : ℂ)).re) (Ici x₀'))
    (hFy : ∀ y : ℝ, x₀' < y → y ∉ Fy → (g (y : ℂ)).re ∉ jumps → β.fn y = b (g (y : ℂ)).re)
    (hft : Restart.FCDet.IsFlowType κ (-(Real.pi / 2)) (BoundaryWord.shiftW x₀' β) xL xR ρL ρR) {y x : ℝ}
    (hy : 0 < y) (hx : g ((y + x₀' : ℝ) : ℂ) = x) (hbad : x ∈ origBadR κ b R) :
    Vq.IsBadPoint xL xR ρL ρR (y : ℂ) := by
  classical
  refine ⟨by simp, Or.inl ⟨by simpa using hy.le, ?_⟩⟩
  simp only [Complex.ofReal_re]
  obtain ⟨y₁, hy₁, hwr⟩ := Vt.wR_eq_of_isFlowType hκ hft hy.le
  obtain ⟨δb, hδb, hb'⟩ := exists_eq_rightLim_data hb x
  set f : ℝ → ℝ := fun y'' => (g ((y'' + x₀' : ℝ) : ℂ)).re with hfdef
  have hfx : f y = x := by simp only [hfdef, hx, Complex.ofReal_re]
  have hfc : ContinuousAt f y := by
    have h1 : ContinuousAt (fun y'' : ℝ => ((y'' + x₀' : ℝ) : ℂ)) y :=
      (Complex.continuous_ofReal.comp (continuous_id.add continuous_const)).continuousAt
    have h2 := (hgc ((y + x₀' : ℝ) : ℂ) (by simp)).tendsto
    have h3 : Tendsto (fun y'' : ℝ => ((y'' + x₀' : ℝ) : ℂ)) (𝓝 y) (𝓝[{z | 0 ≤ z.im}] ((y + x₀' : ℝ) : ℂ)) :=
      tendsto_nhdsWithin_iff.2 ⟨h1, Eventually.of_forall fun y'' => by simp⟩
    exact Complex.continuous_re.continuousAt.comp (h2.comp h3)
  obtain ⟨η, hη, hηf⟩ := Metric.continuousAt_iff.1 hfc δb hδb
  have hinj : InjOn f (Ioi 0) := fun a ha a' ha' he => by
    have h1 := hmono.injOn (show a + x₀' ∈ Ici x₀' by simp only [mem_Ici]; linarith [mem_Ioi.1 ha])
      (show a' + x₀' ∈ Ici x₀' by simp only [mem_Ici]; linarith [mem_Ioi.1 ha']) he
    linarith
  have hT : (Ioi (0 : ℝ) ∩ f ⁻¹' (jumps : Set ℝ)).Finite :=
    Set.Finite.of_finite_image ((jumps.finite_toSet).subset (image_subset_iff.2 fun _ h => h.2))
      (hinj.mono inter_subset_left)
  set ε : ℝ := min (y₁ - y) η with hε
  have hε0 : 0 < ε := lt_min (by linarith) hη
  obtain ⟨y'', hy'', hn⟩ := (Set.Ioo_infinite (show y < y + ε by linarith)).exists_notMem_finset
    ((BoundaryWord.shiftW x₀' β).jumps ∪ Fy.image (· - x₀') ∪ hT.toFinset)
  have h1 : y < y'' := hy''.1
  have h2 : y'' < y₁ := by have := min_le_left (y₁ - y) η; linarith [hy''.2]
  have hcw : y'' ∉ (BoundaryWord.shiftW x₀' β).jumps := fun h =>
    hn (Finset.mem_union_left _ (Finset.mem_union_left _ h))
  have hFy' : y'' + x₀' ∉ Fy := fun h => hn (Finset.mem_union_left _ (Finset.mem_union_right _
    (Finset.mem_image.2 ⟨y'' + x₀', h, by ring⟩)))
  have hJ : f y'' ∉ jumps := fun h => hn (Finset.mem_union_right _ ((Set.Finite.mem_toFinset _).2
    ⟨lt_trans hy h1, h⟩))
  have hgt : x₀' < y'' + x₀' := by linarith
  have hfn : β.fn (y'' + x₀') = b (f y'') := hFy _ hgt hFy' hJ
  have hmon : x < f y'' := by
    rw [← hfx]
    exact hmono (show y + x₀' ∈ Ici x₀' by simp only [mem_Ici]; linarith) (show y'' + x₀' ∈ Ici x₀' by
      simp only [mem_Ici]; linarith) (by linarith)
  have hdist : dist (f y'') (f y) < δb := hηf (by
    rw [Real.dist_eq, abs_lt]; constructor <;> linarith [min_le_right (y₁ - y) η, hy''.2])
  rw [Real.dist_eq, abs_lt, hfx] at hdist
  have hbr : b (f y'') = rightLim b x := hb' (f y'') ⟨hmon, by linarith [hdist.2]⟩ hJ
  rw [hwr y'' h1 h2 hcw, BoundaryWord.fn_shiftW, hfn, hbr]
  exact hbad.2

end Conv

/-! ### The relative curve converges at a finite lifetime -/

section Lim

variable {X : Set ℂ} {x₀' : ℝ} {p : ℝ≥0 → ℂ} {L : ℝ≥0∞}

theorem tendsto_cTime_atTop (hL : L ≠ ⊤) (hL0 : L ≠ 0) :
    Tendsto (fun v : ℝ => Nc.cTime L v) atTop (𝓝 L.toNNReal) := by
  have h1 : Tendsto (fun v : ℝ => 1 / (1 + v)) atTop (𝓝 0) := by
    have := tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left atTop (1 : ℝ) tendsto_id)
    simpa [Function.comp_def, one_div] using this
  have h2 : Tendsto (fun v : ℝ => v / (1 + v)) atTop (𝓝 1) := by
    have := (tendsto_const_nhds (x := (1 : ℝ))).sub h1
    rw [sub_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with v hv
    field_simp
    ring
  have h3 : Tendsto (fun v : ℝ => (Nc.cTime L v : ℝ)) atTop (𝓝 L.toReal) := by
    have := (tendsto_const_nhds (x := L.toReal)).mul h2
    rw [mul_one] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with v hv
    rw [Nc.coe_cTime hL0 hv]
    unfold Nc.rTime clockOf
    simp only [hL, ↓reduceIte]
  rw [← NNReal.tendsto_coe, ENNReal.coe_toNNReal_eq_toReal]
  exact h3

/-- **At a finite lifetime the relative curve converges**, to the unique preimage of the piece's end point. -/
theorem tendsto_canonCurve_atTop (hA : IsHPHull (fillH X)) (hL0 : L ≠ 0) (hL : L ≠ ⊤)
    (hpc : ContinuousOn p {t | (t : ℝ≥0∞) ≤ L}) (hdr : IsDrivenCurve (canonCurve X x₀' p L)) {g : ℂ → ℂ}
    (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g (Mo.hullChart (fillH X) 0).2.1 H) {C : ℝ}
    (hC : ∀ q : ℂ, 0 ≤ q.im → ‖g q - q‖ ≤ C) {w : ℂ}
    (huniq : ∀ z : ℂ, 0 ≤ z.im → g z = p L.toNNReal → z = w) :
    Tendsto (canonCurve X x₀' p L) atTop (𝓝 (w - x₀')) := by
  set f : ℝ → ℂ := fun v => canonCurve X x₀' p L v + x₀' with hf
  have hfH : ∀ v, 0 ≤ v → 0 ≤ (f v).im := fun v hv => by
    simpa [hf] using canonCurve_mem_Hbar hA hL0 hpc hdr hv
  have hgf : ∀ v, 0 ≤ v → g (f v) = p (Nc.cTime L v) := fun v hv => g_canonCurve_eq hA hL0 hpc hdr hgc hgi hv
  have hLle : ((L.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ L := ENNReal.coe_toNNReal_le_self
  have hpL : Tendsto (fun v => p (Nc.cTime L v)) atTop (𝓝 (p L.toNNReal)) :=
    (hpc _ hLle).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨tendsto_cTime_atTop hL hL0,
      eventually_ge_atTop (0 : ℝ) |>.mono fun v hv => Nc.cTime_le hL0 hv⟩)
  have hgfl : Tendsto (fun v => g (f v)) atTop (𝓝 (p L.toNNReal)) :=
    hpL.congr' (eventually_ge_atTop (0 : ℝ) |>.mono fun v hv => (hgf v hv).symm)
  -- a bound for the piece
  have hKp : IsCompact (p '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ L}) := by
    have hset : {t : ℝ≥0 | (t : ℝ≥0∞) ≤ L} = Icc 0 L.toNNReal := by
      ext t
      simp only [mem_ofPred_eq, mem_Icc, zero_le, true_and]
      rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal hL]
    rw [hset] at hpc ⊢
    exact isCompact_Icc.image_of_continuousOn hpc
  obtain ⟨M, hM⟩ := hKp.isBounded.subset_closedBall 0
  set K : Set ℂ := closedBall 0 (M + C) ∩ {z | 0 ≤ z.im} with hK
  have hKc : IsCompact K := (isCompact_closedBall _ _).inter_right (isClosed_le continuous_const Complex.continuous_im)
  have hmem : ∀ᶠ v in atTop, f v ∈ K := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with v hv
    refine ⟨?_, hfH v hv⟩
    rw [mem_closedBall_zero_iff]
    have h1 := hC (f v) (hfH v hv)
    have h2 := hM ⟨Nc.cTime L v, Nc.cTime_le hL0 hv, rfl⟩
    rw [mem_closedBall_zero_iff] at h2
    rw [hgf v hv] at h1
    have := norm_sub_norm_le (p (Nc.cTime L v)) (f v)
    calc ‖f v‖ ≤ ‖p (Nc.cTime L v)‖ + ‖p (Nc.cTime L v) - f v‖ := by
          have := norm_sub_le (p (Nc.cTime L v)) (p (Nc.cTime L v) - f v)
          rw [sub_sub_cancel] at this
          exact this
      _ ≤ M + C := add_le_add h2 h1
  have hlim : Tendsto f atTop (𝓝 w) := by
    refine hKc.tendsto_nhds_of_unique_mapClusterPt hmem fun y hy hcl => huniq y hy.2 ?_
    set F := 𝓝 y ⊓ map f atTop with hF
    have hFne : F.NeBot := hcl
    have hFH : F ≤ 𝓝[{z | 0 ≤ z.im}] y := by
      refine le_inf inf_le_left (inf_le_right.trans ?_)
      rw [le_principal_iff]
      exact mem_map.2 (hmem.mono fun v hv => hv.2)
    have h1 : Tendsto g F (𝓝 (g y)) := (hgc y hy.2).tendsto.mono_left hFH
    have h2 : Tendsto g F (𝓝 (p L.toNNReal)) := (tendsto_map'_iff.2 hgfl).mono_left inf_le_right
    exact tendsto_nhds_unique h1 h2
  have := hlim.sub_const (x₀' : ℂ)
  simpa [hf] using this

end Lim

end InteractingSLE.Theorem14.SB.Ne
