/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2NvMeas

/-!
# The death of a zero-lifetime candidate: the seed threshold in the stage chart

Packet PROVE-GW2-NOTHR (round 4, D46). A candidate of zero lifetime dies at its start: its launch word has a seed
threshold (`SB.Retain.ae_lifetime_eq_zero_iff_seed`). Its death clock is the stage start, so BUF's
`DeathThrXStatement` asks for the stage word's threshold at stage time `0`. The seed weight moves forward through
the relative chart at `0` (`relBdry 0 = 0`, `0` off the retained hull) and through the dilation:

* **`sumR_le_of_boundary_chart₀`**, **`sumL_le_of_boundary_chart₀`**: `GW2Nu.sumR_le_of_boundary_chart` (and its
  mirror) also at the point `0`;
* **`joint_seed_of_launch_seed`** (one sample): a seed threshold of the launch word gives a seed weight `≤ −2` of the
  joint word of the counterflow record;
* **`stage_threshold_zero_of_joint`**: a seed weight of the joint word gives the stage word's threshold at `0` along
  every stage path from `0`;
* **`ae_stage_seed_at_death`**: SAFE's configuration under any probability measure, almost surely, at every own time
  of the counterflow with an interior tip, a zero lifetime gives the stage threshold at `0` for every identification.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Finset MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H chiC fwdHull fwdMapInv)
open LQGMetric (DistOn)

namespace InteractingSLE.Theorem14.GW2Nv

open Restart Exist.StagedLaw Sec7.PocketTraversal Supp8 Supp8.GB6 Supp8.GB6.RelDrv Supp8.GB6.CoordB Supp8.Q3Rel
  GW2Rd GW2TipSystem GW2Sf GW2JointKernel MartChar.RealFlow GW2Nu Sec5.CrossCond.StagedRepLater

section Chart

variable {κ θ : ℝ} {b bR : ℝ → ℝ} {J JR : Finset ℝ}

/-- **Right bad weights move forward through a real boundary chart, also at `0`.** -/
theorem sumR_le_of_boundary_chart₀ (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b J)
    (hbR : IsPiecewiseConstantBoundaryData bR JR) {φ : ℂ → ℂ} {x r : ℝ} (hr : 0 < r)
    (hφ : R16.IsRealBoundaryConformal φ x r) (hx : 0 ≤ x) (hφx : 0 ≤ (φ x).re)
    (hmono : ∀ u ∈ Ioo (x - r) (x + r), u ≤ x → (φ u).re ≤ (φ x).re)
    {E : Set ℝ} (hE : E.Finite) (hEJ : (J : Set ℝ) ⊆ E)
    (hheight : ∀ u ∈ Ioo (x - r) (x + r), u ∉ E → (φ u).re ∉ JR → bR (φ u).re = b u + θ * chiC κ)
    (hbad : ∑ i ∈ univ.filter (fun i => flowLineXR b J 0 i ≤ x), flowLineRhoR κ b J 0 θ i ≤ -2) :
    ∑ j ∈ univ.filter (fun j => flowLineXR bR JR 0 j ≤ (φ x).re), flowLineRhoR κ bR JR 0 0 j ≤ -2 := by
  classical
  set q := (φ x).re with hqdef
  obtain ⟨δ, hδ, hδJ⟩ := exists_gap_above J x
  obtain ⟨δR, hδR, hδRJ⟩ := exists_gap_above JR q
  set r₁ := min r δ with hr₁def
  have hr₁ : 0 < r₁ := lt_min hr hδ
  have hφ₁ := isRealBoundaryConformal_mono hφ (min_le_left r δ)
  obtain ⟨ε, hε, himg⟩ := Sec7.Aux37Side.exists_ball_image hφ₁ (y := x) (mem_ball_self hr₁)
  have hφxr : φ x = (q : ℂ) := Complex.ext (by simp [hqdef]) (by
    simpa using hφ.2.2.1 x (mem_ball_self hr) (by simp))
  set F : Set ℝ := (JR : Set ℝ) ∪ (fun e : ℝ => (φ (e : ℂ)).re) '' E with hFdef
  have hF : F.Finite := JR.finite_toSet.union (hE.image _)
  obtain ⟨q', hq', hq'F⟩ := exists_mem_Ioo_notMem (show q < q + min ε δR by
    have := lt_min hε hδR; linarith) hF
  obtain ⟨u, hub, -, hu, -, hu0⟩ := himg (q' : ℂ) (by
    rw [mem_ball, hφxr, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith [hq'.1])]
    linarith [hq'.2, min_le_left ε δR]) (by simp)
  have huim : u.im = 0 := hu0 (by simp)
  have hue : u = (u.re : ℂ) := Complex.ext rfl (by simpa using huim)
  have huI : u.re ∈ Ioo (x - r₁) (x + r₁) := Sec7.Aux37Side.ofReal_mem_ball_iff.1 (hue ▸ hub)
  have huI' : u.re ∈ Ioo (x - r) (x + r) :=
    ⟨by linarith [huI.1, min_le_left r δ], by linarith [huI.2, min_le_left r δ]⟩
  have hφu : (φ (u.re : ℂ)).re = q' := by rw [← hue, hu, Complex.ofReal_re]
  have huE : u.re ∉ E := fun h => hq'F (Or.inr ⟨u.re, h, hφu⟩)
  have hq'JR : q' ∉ JR := fun h => hq'F (Or.inl h)
  have hxu : x < u.re := by
    by_contra hle
    have := hmono u.re huI' (not_lt.1 hle)
    rw [hφu] at this
    linarith [hq'.1]
  have hupos : 0 < u.re := lt_of_le_of_lt hx hxu
  have huJ : u.re ∉ J := fun h => huE (hEJ h)
  have hL : ∑ i ∈ univ.filter (fun i => flowLineXR b J 0 i ≤ u.re), flowLineRhoR κ b J 0 θ i =
      ∑ i ∈ univ.filter (fun i => flowLineXR b J 0 i ≤ x), flowLineRhoR κ b J 0 θ i := by
    refine Finset.sum_congr (Finset.filter_congr fun i _ => ⟨fun h => ?_, fun h => h.trans hxu.le⟩) fun _ _ => rfl
    by_contra hgt
    rcases flowLineXR_eq_zero_or_mem b J i with h0 | hJ
    · rw [h0] at hgt; linarith
    · have := hδJ _ hJ (not_le.1 hgt)
      linarith [huI.2, min_le_right r δ]
  have hR : ∑ j ∈ univ.filter (fun j => flowLineXR bR JR 0 j ≤ q'), flowLineRhoR κ bR JR 0 0 j =
      ∑ j ∈ univ.filter (fun j => flowLineXR bR JR 0 j ≤ q), flowLineRhoR κ bR JR 0 0 j := by
    refine Finset.sum_congr (Finset.filter_congr fun j _ => ⟨fun h => ?_, fun h => h.trans hq'.1.le⟩)
      fun _ _ => rfl
    by_contra hgt
    rcases flowLineXR_eq_zero_or_mem bR JR j with h0 | hJ
    · rw [h0] at hgt; linarith
    · have := hδRJ _ hJ (not_le.1 hgt)
      linarith [hq'.2, min_le_right ε δR]
  have h1 := sum_filter_flowLineXR_le_theta (θ := θ) hκ hb hupos huJ
  have h2 := sum_filter_flowLineXR_le_theta (θ := 0) hκ hbR (lt_of_le_of_lt hφx hq'.1) hq'JR
  have hh := hheight u.re huI' huE (by rw [hφu]; exact hq'JR)
  rw [hφu] at hh
  rw [← hR, h2, zero_mul, add_zero, hh, ← h1, hL]
  exact hbad

/-- **Left bad weights move forward through a real boundary chart, also at `0`** (mirror form). -/
theorem sumL_le_of_boundary_chart₀ (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b J)
    (hbR : IsPiecewiseConstantBoundaryData bR JR) {φ : ℂ → ℂ} {x r : ℝ} (hr : 0 < r)
    (hφ : R16.IsRealBoundaryConformal φ x r) (hx : x ≤ 0) (hφx : (φ x).re ≤ 0)
    (hmono : ∀ u ∈ Ioo (x - r) (x + r), x ≤ u → (φ x).re ≤ (φ u).re)
    {E : Set ℝ} (hE : E.Finite) (hEJ : (J : Set ℝ) ⊆ E)
    (hheight : ∀ u ∈ Ioo (x - r) (x + r), u ∉ E → (φ u).re ∉ JR → bR (φ u).re = b u + θ * chiC κ)
    (hbad : ∑ i ∈ univ.filter (fun i => x ≤ flowLineXL b J 0 i), flowLineRhoL κ b J 0 θ i ≤ -2) :
    ∑ j ∈ univ.filter (fun j => (φ x).re ≤ flowLineXL bR JR 0 j), flowLineRhoL κ bR JR 0 0 j ≤ -2 := by
  classical
  set q := (φ x).re with hqdef
  obtain ⟨δ, hδ, hδJ⟩ := exists_gap_below J x
  obtain ⟨δR, hδR, hδRJ⟩ := exists_gap_below JR q
  set r₁ := min r δ with hr₁def
  have hr₁ : 0 < r₁ := lt_min hr hδ
  have hφ₁ := isRealBoundaryConformal_mono hφ (min_le_left r δ)
  obtain ⟨ε, hε, himg⟩ := Sec7.Aux37Side.exists_ball_image hφ₁ (y := x) (mem_ball_self hr₁)
  have hφxr : φ x = (q : ℂ) := Complex.ext (by simp [hqdef]) (by
    simpa using hφ.2.2.1 x (mem_ball_self hr) (by simp))
  set F : Set ℝ := (JR : Set ℝ) ∪ (fun e : ℝ => (φ (e : ℂ)).re) '' E with hFdef
  have hF : F.Finite := JR.finite_toSet.union (hE.image _)
  obtain ⟨q', hq', hq'F⟩ := exists_mem_Ioo_notMem (show q - min ε δR < q by
    have := lt_min hε hδR; linarith) hF
  obtain ⟨u, hub, -, hu, -, hu0⟩ := himg (q' : ℂ) (by
    rw [mem_ball, hφxr, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_neg (by linarith [hq'.2])]
    linarith [hq'.1, min_le_left ε δR]) (by simp)
  have huim : u.im = 0 := hu0 (by simp)
  have hue : u = (u.re : ℂ) := Complex.ext rfl (by simpa using huim)
  have huI : u.re ∈ Ioo (x - r₁) (x + r₁) := Sec7.Aux37Side.ofReal_mem_ball_iff.1 (hue ▸ hub)
  have huI' : u.re ∈ Ioo (x - r) (x + r) :=
    ⟨by linarith [huI.1, min_le_left r δ], by linarith [huI.2, min_le_left r δ]⟩
  have hφu : (φ (u.re : ℂ)).re = q' := by rw [← hue, hu, Complex.ofReal_re]
  have huE : u.re ∉ E := fun h => hq'F (Or.inr ⟨u.re, h, hφu⟩)
  have hq'JR : q' ∉ JR := fun h => hq'F (Or.inl h)
  have hux : u.re < x := by
    by_contra hle
    have := hmono u.re huI' (not_lt.1 hle)
    rw [hφu] at this
    linarith [hq'.2]
  have huneg : u.re < 0 := lt_of_lt_of_le hux hx
  have huJ : u.re ∉ J := fun h => huE (hEJ h)
  have hL : ∑ i ∈ univ.filter (fun i => u.re ≤ flowLineXL b J 0 i), flowLineRhoL κ b J 0 θ i =
      ∑ i ∈ univ.filter (fun i => x ≤ flowLineXL b J 0 i), flowLineRhoL κ b J 0 θ i := by
    refine Finset.sum_congr (Finset.filter_congr fun i _ => ⟨fun h => ?_, fun h => hux.le.trans h⟩) fun _ _ => rfl
    by_contra hlt
    rcases flowLineXL_eq_zero_or_mem b J i with h0 | hJ
    · rw [h0] at hlt; linarith
    · have := hδJ _ hJ (not_le.1 hlt)
      linarith [huI.1, min_le_right r δ]
  have hR : ∑ j ∈ univ.filter (fun j => q' ≤ flowLineXL bR JR 0 j), flowLineRhoL κ bR JR 0 0 j =
      ∑ j ∈ univ.filter (fun j => q ≤ flowLineXL bR JR 0 j), flowLineRhoL κ bR JR 0 0 j := by
    refine Finset.sum_congr (Finset.filter_congr fun j _ => ⟨fun h => ?_, fun h => hq'.2.le.trans h⟩)
      fun _ _ => rfl
    by_contra hlt
    rcases flowLineXL_eq_zero_or_mem bR JR j with h0 | hJ
    · rw [h0] at hlt; linarith
    · have := hδRJ _ hJ (not_le.1 hlt)
      linarith [hq'.1, min_le_right ε δR]
  have h1 := sum_filter_le_flowLineXL_theta (θ := θ) hκ hb huneg huJ
  have h2 := sum_filter_le_flowLineXL_theta (θ := 0) hκ hbR (lt_of_lt_of_le hq'.2 hφx) hq'JR
  have hh := hheight u.re huI' huE (by rw [hφu]; exact hq'JR)
  rw [hφu] at hh
  rw [← hR, h2, zero_mul, add_zero, hh, ← h1, hL]
  exact hbad

end Chart

section Joint

variable {Ω : Type*} {κ θ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {γ : Ω → ℝ≥0 → ℂ}

/-- **A launch seed threshold gives a seed weight `≤ −2` of the joint word** (one sample, at an own time `S` of the
complete counterflow with an interior tip). -/
theorem joint_seed_of_launch_seed {ω : Ω} (S : ℝ≥0) (hW0 : W 0 ω = 0)
    (hWc : ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω}) (hζ : ζ ω = ⊤)
    (hγ : IsGeneratingTrace (fun t => W t ω) (ζ ω) (γ ω)) (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b J)
    (c' : BoundaryWord)
    (hdata : ∀ x : ℝ, x ∉ J → x ≠ 0 → -x⁻¹ ∉ c'.jumps →
      b x = Sec7.StripSysField.returnData (Real.pi * chiC (16 / κ)) (chiC (16 / κ)) c'.fn x)
    (hseed : ∑ i ∈ univ.filter (fun i => 0 ≤ flowLineXL b J 0 i), flowLineRhoL κ b J 0 θ i ≤ -2 ∨
      ∑ j ∈ univ.filter (fun j => flowLineXR b J 0 j ≤ 0), flowLineRhoR κ b J 0 θ j ≤ -2) :
    ∑ i ∈ univ.filter (fun i => 0 ≤ flowLineXL (gw2Word κ θ c' (gb6Rec S W ζ ω)).fn
        (gw2Word κ θ c' (gb6Rec S W ζ ω)).jumps 0 i),
        flowLineRhoL κ (gw2Word κ θ c' (gb6Rec S W ζ ω)).fn (gw2Word κ θ c' (gb6Rec S W ζ ω)).jumps 0 0 i ≤ -2 ∨
      ∑ j ∈ univ.filter (fun j => flowLineXR (gw2Word κ θ c' (gb6Rec S W ζ ω)).fn
        (gw2Word κ θ c' (gb6Rec S W ζ ω)).jumps 0 j ≤ 0),
        flowLineRhoR κ (gw2Word κ θ c' (gb6Rec S W ζ ω)).fn (gw2Word κ θ c' (gb6Rec S W ζ ω)).jumps 0 0 j ≤ -2 := by
  classical
  obtain ⟨hgood, -⟩ := recGood_tip_of_sample hW0 hWc hζ hγ S
  have hrtime : rtime (gb6Rec S W ζ ω) = S := hgood.2.2
  set rec := gb6Rec S W ζ ω with hrecdef
  set U : ℝ → ℝ := rdrv rec with hUdef
  have hU : Continuous U := continuous_rdrv rec
  have hU0 : U 0 = 0 := rdrv_zero rec
  have hs : (0 : ℝ) ≤ S := S.coe_nonneg
  set K := gw2Word κ θ c' rec with hKdef
  have hKeq : K = upW (θ * chiC κ) (gb6WordOfRec (16 / κ) 0 c' rec) := by
    rw [hKdef, gw2Word, GW2Fb.jointWordOfRec_specOffset hκ]
  have hKpc : IsPiecewiseConstantBoundaryData K.fn K.jumps := K.isPiecewiseConstantBoundaryData
  set E : Set ℝ := ({0} ∪ (J : Set ℝ)) ∪ (fun y : ℝ => -y⁻¹) '' (c'.jumps : Set ℝ) with hEdef
  have hE : E.Finite := ((finite_singleton 0).union J.finite_toSet).union (c'.jumps.finite_toSet.image _)
  have hEJ : (J : Set ℝ) ⊆ E := fun _ hy => Or.inl (Or.inr hy)
  have hEInv {u : ℝ} (hu : u ∉ E) : -u⁻¹ ∉ c'.jumps := fun h => hu (Or.inr ⟨-u⁻¹, h, neg_inv_neg_inv_real u⟩)
  have hheight : ∀ u : ℝ, (u : ℂ) ∉ closure (invHull U S) → u ∉ E → (relBdry U S u).re ∉ K.jumps →
      K.fn (relBdry U S u).re = b u + θ * chiC κ := by
    intro u huA huE huJR
    have hu0 : u ≠ 0 := fun h => huE (Or.inl (Or.inl h))
    rw [hKeq, upW_fn]
    rw [hKeq, upW_jumps] at huJR
    have h := gb6WordOfRec_fn_relBdry (by positivity : (0 : ℝ) < 16 / κ) c' rec hu0
      (by rw [hrtime]; exact huA) (hEInv huE) (by rw [hrtime]; exact huJR)
    rw [hrtime] at h
    show (gb6WordOfRec (16 / κ) 0 c' rec).fn (relBdry U S u).re + θ * chiC κ = _
    rw [h, ← hdata u (fun h => huE (hEJ h)) hu0 (hEInv huE)]
  have h0A : ((0 : ℝ) : ℂ) ∉ closure (invHull U S) := by
    rw [Complex.ofReal_zero]; exact zero_notMem_closure_invHull hU hs
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 isClosed_closure.isOpen_compl _ h0A
  have hφ := isRealBoundaryConformal_relBdry hU hU0 hs hball
  have hφ0 : relBdry U S ((0 : ℝ) : ℂ) = 0 := by rw [Complex.ofReal_zero]; exact relBdry_zero hU hU0 hs
  have hreal : ∀ u ∈ Ioo ((0 : ℝ) - r) (0 + r), (u : ℂ) ∉ closure (invHull U S) := fun u hu =>
    hball (Sec7.Aux37Side.ofReal_mem_ball_iff.2 hu)
  rcases hseed with hL | hR
  · left
    have h := sumL_le_of_boundary_chart₀ (θ := θ) (x := 0) hκ hb hKpc hr hφ le_rfl (by rw [hφ0]; simp)
      (fun u hu h0u => by
        rw [hφ0, Complex.zero_re]
        rcases h0u.eq_or_lt with rfl | hpos
        · rw [Complex.ofReal_zero, relBdry_zero hU hU0 hs, Complex.zero_re]
        · exact (((relBdry_real_sign hU hU0 hs hpos.ne' (hreal u hu)).1).1 hpos).le)
      hE hEJ (fun u hu huE huJR => hheight u (hreal u hu) huE huJR) hL
    rwa [hφ0, Complex.zero_re] at h
  · right
    have h := sumR_le_of_boundary_chart₀ (θ := θ) (x := 0) hκ hb hKpc hr hφ le_rfl (by rw [hφ0]; simp)
      (fun u hu hu0 => by
        rw [hφ0, Complex.zero_re]
        rcases hu0.eq_or_lt with rfl | hneg
        · rw [Complex.ofReal_zero, relBdry_zero hU hU0 hs, Complex.zero_re]
        · exact (((relBdry_real_sign hU hU0 hs hneg.ne (hreal u hu)).2).1 hneg).le)
      hE hEJ (fun u hu huE huJR => hheight u (hreal u hu) huE huJR) hR
    rwa [hφ0, Complex.zero_re] at h

end Joint

/-- **A seed weight of the joint word gives the stage word's threshold at `0`** along every stage path from `0`
(the data-level transfer at time `0`). -/
theorem stage_threshold_zero_of_joint {κ : ℝ} (hκ : 0 < κ) {β K : BoundaryWord} {lam : ℝ} (hlam : 0 < lam)
    {F : Set ℝ} (hF : F.Finite) (hdata : ∀ y, y ∉ F → β.fn y = K.fn (lam * y)) {D : ℝ≥0 → ℝ}
    (hD : Continuous D) (hD0 : D 0 = 0)
    (hseed : ∑ i ∈ univ.filter (fun i => 0 ≤ flowLineXL K.fn K.jumps 0 i), flowLineRhoL κ K.fn K.jumps 0 0 i ≤ -2 ∨
      ∑ j ∈ univ.filter (fun j => flowLineXR K.fn K.jumps 0 j ≤ 0), flowLineRhoR κ K.fn K.jumps 0 0 j ≤ -2) :
    ForceWord.ThresholdCondition (flowLineRhoL κ β.fn β.jumps 0 0) (flowLineRhoR κ β.fn β.jumps 0 0) (D 0)
      (fun i => -rightImg (fun v : ℝ => -D v.toNNReal) (-flowLineXL β.fn β.jumps 0 i) ((0 : ℝ≥0) : ℝ))
      (fun j => rightImg (fun v : ℝ => D v.toNNReal) (flowLineXR β.fn β.jumps 0 j) ((0 : ℝ≥0) : ℝ)) := by
  classical
  set D' : ℝ → ℝ := fun q => D q.toNNReal with hD'def
  have hD'c : Continuous D' := hD.comp continuous_real_toNNReal
  have hD'0 : D' 0 = 0 := by simp [hD'def, hD0]
  set WL : ℝ → ℝ := scD lam D' with hWLdef
  have hWLc : Continuous WL := continuous_scD hD'c
  have hWL0 : WL 0 = 0 := by simp [hWLdef, scD, hD'0]
  have h := (GW2Nt.thresholdCondition_iff_of_dil (θ₁ := 0) (θ₂ := 0) hκ K.isPiecewiseConstantBoundaryData
    β.isPiecewiseConstantBoundaryData hlam hF (fun y hy => by simp only [zero_mul, add_zero]; exact hdata y hy)
    hD'c le_rfl (WL := WL) fun v _ => rfl).2 ?_
  · simpa only [NNReal.coe_zero, hD'def, Real.toNNReal_zero] using h
  · rw [mul_zero]
    have hR : ∀ j, rightImg WL (flowLineXR K.fn K.jumps 0 j) 0 = flowLineXR K.fn K.jumps 0 j := fun j =>
      rightImg_zero hWLc hWL0 (Restart.FlowStopIdentCMI.flowLineXR_nonneg' _ _ 0 j)
    have hL : ∀ i, -rightImg (fun v => -WL v) (-flowLineXL K.fn K.jumps 0 i) 0 = flowLineXL K.fn K.jumps 0 i :=
      fun i => by
        have h := rightImg_zero (w := fun v => -WL v) hWLc.neg (by simp [hWL0])
          (neg_nonneg.2 (Restart.FlowStopIdentCMI.flowLineXL_nonpos' K.fn K.jumps 0 i))
        rw [h, neg_neg]
    unfold ForceWord.ThresholdCondition
    simp only [hR, hL, hWL0]
    rcases hseed with hs | hs
    · left
      refine le_trans (le_of_eq ?_) hs
      refine Finset.sum_congr (Finset.filter_congr fun i _ => ?_) fun _ _ => rfl
      have := Restart.FlowStopIdentCMI.flowLineXL_nonpos' K.fn K.jumps 0 i
      constructor <;> intro h <;> linarith
    · right
      refine le_trans (le_of_eq ?_) hs
      refine Finset.sum_congr (Finset.filter_congr fun j _ => ?_) fun _ _ => rfl
      have := Restart.FlowStopIdentCMI.flowLineXR_nonneg' K.fn K.jumps 0 j
      constructor <;> intro h <;> linarith

/-- **The stage threshold at `0` of a zero-lifetime candidate, almost surely** (SAFE's configuration under any
probability measure): almost surely, at every own time `S` of the counterflow, if the candidate's lifetime is `0`,
then for every identification (the stage word is the dilated joint word off a finite set) the stage word has a
continuation threshold at stage time `0` along every stage path from `0`. -/
theorem ae_stage_seed_at_death {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {κ θ : ℝ} {b b' : ℝ → ℝ} {J J' : Finset ℝ} {h h' : Ω → DistOn upperHalfPlaneOpens}
    {Wα W : ℝ≥0 → Ω → ℝ} {ζα ζ : Ω → ℝ≥0∞} {γ : Ω → ℝ≥0 → ℂ} (hκ : 0 < κ)
    (hb : IsPiecewiseConstantBoundaryData b J) (hG : IsGFFWithBoundaryData P h b J)
    (hb' : IsPiecewiseConstantBoundaryData b' J')
    (hT : ∀ ω, IsChartTransport infinitySourceChart (-1) (-(Real.pi * chiC κ)) (chiC (16 / κ)) (h ω) (h' ω))
    (hfl : IsFlowLineDriver κ b J θ P h Wα ζα) (hcf : IsFlowLineDriver (16 / κ) b' J' 0 P h' W ζ)
    (hγ : ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω))
    (c' : BoundaryWord) (hc'J : c'.jumps = J') (hc'b : ∀ y ∉ J', c'.fn y = b' y) :
    ∀ᵐ ω ∂P, ∀ S : ℝ≥0, ζα ω = 0 → ∀ (β : BoundaryWord) (lam : ℝ) (F : Set ℝ) (D : ℝ≥0 → ℝ), 0 < lam →
      F.Finite → (∀ y, y ∉ F → β.fn y = (gw2Word κ θ c' (gb6Rec S W ζ ω)).fn (lam * y)) → Continuous D →
      D 0 = 0 →
      ForceWord.ThresholdCondition (flowLineRhoL κ β.fn β.jumps 0 0) (flowLineRhoR κ β.fn β.jumps 0 0) (D 0)
        (fun i => -rightImg (fun v : ℝ => -D v.toNNReal) (-flowLineXL β.fn β.jumps 0 i) ((0 : ℝ≥0) : ℝ))
        (fun j => rightImg (fun v : ℝ => D v.toNNReal) (flowLineXR β.fn β.jumps 0 j) ((0 : ℝ≥0) : ℝ)) := by
  have hG' := GW2aPiece.isGFFWithBoundaryData_of_isFlowLineDriver (by positivity : 0 < 16 / κ) hb' hcf
  have hdata := fun x hxJ hx0 hxJ' => data_eq_returnData_gw2 hκ hb hG hb' hG' hT c' hc'J hc'b
    (x := x) hxJ hx0 hxJ'
  filter_upwards [SB.Retain.ae_lifetime_eq_zero_iff_seed hfl, ae_driver_zero_continuousOn hcf, hγ]
    with ω hseedω hd hγω S hz β lam F D hlam hF hdat hDc hD0
  have hthr := hseedω.1 hz
  have hseed : ∑ i ∈ univ.filter (fun i => 0 ≤ flowLineXL b J 0 i), flowLineRhoL κ b J 0 θ i ≤ -2 ∨
      ∑ j ∈ univ.filter (fun j => flowLineXR b J 0 j ≤ 0), flowLineRhoR κ b J 0 θ j ≤ -2 := by
    rcases hthr with hL | hR
    · left
      refine le_trans (le_of_eq ?_) hL
      refine Finset.sum_congr (Finset.filter_congr fun i _ => ?_) fun _ _ => rfl
      have := Restart.FlowStopIdentCMI.flowLineXL_nonpos' b J 0 i
      constructor <;> intro h <;> linarith
    · right
      refine le_trans (le_of_eq ?_) hR
      refine Finset.sum_congr (Finset.filter_congr fun j _ => ?_) fun _ _ => rfl
      have := Restart.FlowStopIdentCMI.flowLineXR_nonneg' b J 0 j
      constructor <;> intro h <;> linarith
  have hγt : IsGeneratingTrace (fun t => W t ω) (ζ ω) (γ ω) := by rw [hγω.1]; exact hγω.2
  have hj := joint_seed_of_launch_seed S hd.1 hd.2 hγω.1 hγt hκ hb c' hdata hseed
  exact stage_threshold_zero_of_joint hκ hlam hF hdat hDc hD0 hj

end InteractingSLE.Theorem14.GW2Nv
