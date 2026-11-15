/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2WfNoThr
import InteractingSLE.Spec.Supplement.SB2VrBad
import InteractingSLE.Spec.Supplement.SBLwLink
import InteractingSLE.Spec.Supplement.G12Statement
import InteractingSLE.Spec.Sec4.Prob41Flow

/-!
# E7, second direction: a bad physical point read back from the relative tip is a bad relative point

Packet PROVE-T14-SB2WORD (round 3, decision D18). The converse of `SB2WfNoThr`'s correspondence, deterministic.

* `rel_bad_right`: if `g (y + m)` is a bad physical point (`p ∈ badSet`) for some `y > 0` and the relative heights
  just right of `y + m` are not the old lower-side height `−λ + (π/2)χ`, then by the second clause they are original
  heights at free original-real points `x ↓ p` (strict monotonicity of the profile), so `rightLim b p` is the relative
  height and the relative right weight at `y` is `≤ −2`;
* `rel_bad_left`: the same on the left (`y < 0`), where every relative point is original;
* `thr_le_of_bad_right`, `thr_le_of_bad_left`: a relative tip at a bad relative point forces the continuation
  threshold at or before that time (`Vo.exists_first_threshold_right`, reflected on the left);
* `readback`: the link reads the relative trace back to the physical flow at every relative time up to the relative
  lifetime, the lifetime included when finite (density of interior times, continuity);
* `badSet` against NOJUMP's `Vr.badSet` of the flow-line word.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric Finset
open scoped NNReal ENNReal
open QuantumZipper (H Hbar chiC fwdMapInv)

namespace InteractingSLE.Theorem14.SB.Wf

open Exist Exist.StagedLaw Exist.Staged Restart GW1W Lv Sec7.PocketTraversal MartChar.RealFlow
open PiecewiseConstantBoundaryData (rightLim leftLim)

/-! ### One-sided limits from one point beyond -/

theorem rightLim_eq_of_gap {b : ℝ → ℝ} {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J) {p δ x : ℝ}
    (hδ : ∀ z ∈ J, z ∉ Ioo p (p + δ)) (hx : x ∈ Ioo p (p + δ)) : rightLim b p = b x :=
  Sec4.rightLim_eq_of_forall (lt_trans hx.1 hx.2) fun _ ht =>
    Sec4.eq_of_mem_Ioo_of_isPiecewiseConstant hb hδ hx ht

theorem leftLim_eq_of_gap {b : ℝ → ℝ} {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J) {p δ x : ℝ}
    (hδ : ∀ z ∈ J, z ∉ Ioo (p - δ) p) (hx : x ∈ Ioo (p - δ) p) : leftLim b p = b x :=
  Sec4.leftLim_eq_of_forall (lt_trans hx.1 hx.2) fun _ ht =>
    Sec4.eq_of_mem_Ioo_of_isPiecewiseConstant hb hδ hx ht

/-! ### The bad set of the original data against the flow-line word -/

section BadSet

variable {κ ψ u : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

theorem flowBad_of_mem_badSet (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps) {x : ℝ}
    (hx : x ∈ badSet κ ψ u b) :
    (((x - u : ℝ) : ℂ)) ∈ Vr.badSet (flowLineXL b jumps u) (flowLineXR b jumps u) (flowLineRhoL κ b jumps u ψ)
      (flowLineRhoR κ b jumps u ψ) := by
  refine ⟨by simp, ?_⟩
  rcases hx with ⟨hux, hbad⟩ | ⟨hxu, hbad⟩
  · refine Or.inl ⟨by simp; linarith, ?_⟩
    have e := Vr.cumWeightRight_rightLim_flowLine hκ hb u ψ (show 0 < x - u by linarith)
    rw [sub_add_cancel] at e
    simp only [Complex.ofReal_re]
    rw [← e]
    exact hbad
  · refine Or.inr ⟨by simp; linarith, ?_⟩
    have e := Vr.cumWeightLeft_leftLim_flowLine hκ hb u ψ (show x - u < 0 by linarith)
    rw [sub_add_cancel] at e
    simp only [Complex.ofReal_re]
    rw [← e]
    exact hbad

theorem flowBad_of_mem_closure_badSet (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps) {x : ℝ}
    (hx : x ∈ closure (badSet κ ψ u b)) :
    (((x - u : ℝ) : ℂ)) ∈ closure (Vr.badSet (flowLineXL b jumps u) (flowLineXR b jumps u)
      (flowLineRhoL κ b jumps u ψ) (flowLineRhoR κ b jumps u ψ)) := by
  have hf : Continuous fun y : ℝ => (((y - u : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_id.sub continuous_const)
  have h1 := image_closure_subset_closure_image hf ⟨x, hx, rfl⟩
  refine closure_mono ?_ h1
  rintro _ ⟨y, hy, rfl⟩
  exact flowBad_of_mem_badSet hκ hb hy

theorem mem_badSet_of_flowBad (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps) {p : ℝ} (hpu : p ≠ u)
    (hp : Vq.IsBadPoint (flowLineXL b jumps u) (flowLineXR b jumps u) (flowLineRhoL κ b jumps u ψ)
      (flowLineRhoR κ b jumps u ψ) (((p - u : ℝ) : ℂ))) : p ∈ badSet κ ψ u b := by
  obtain ⟨-, hR | hL⟩ := hp
  · simp only [Complex.ofReal_re] at hR
    have hup : u < p := lt_of_le_of_ne (by linarith [hR.1]) (Ne.symm hpu)
    refine Or.inl ⟨hup, ?_⟩
    have e := Vr.cumWeightRight_rightLim_flowLine hκ hb u ψ (show 0 < p - u by linarith)
    rw [sub_add_cancel] at e
    rw [e]
    exact hR.2
  · simp only [Complex.ofReal_re] at hL
    have hpu' : p < u := lt_of_le_of_ne (by linarith [hL.1]) hpu
    refine Or.inr ⟨hpu', ?_⟩
    have e := Vr.cumWeightLeft_leftLim_flowLine hκ hb u ψ (show p - u < 0 by linarith)
    rw [sub_add_cancel] at e
    rw [e]
    exact hL.2

end BadSet

/-! ### A bad physical point is a bad relative point -/

section Corr

variable {κ ψ u m : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {c : Chart} {g : ℂ → ℂ} {β cw : BoundaryWord}
  {Fw : Finset ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

/-- **Right side**: a bad physical point read back at a relative point `y > 0` whose right neighbourhood is not an old
lower side is a bad relative point. -/
theorem rel_bad_right (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps) (hcc : c.IsConformal)
    (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g c.2.1 H) (hSC : SecondClause κ b jumps c u m β.fn β.jumps)
    (hcw : ∀ y ∉ Fw, cw.fn y = β.fn (y + m)) (hft : FCDet.IsFlowType κ ψ cw xL xR ρL ρR) {y : ℝ} (hy : 0 < y)
    {p : ℝ} (hp : g ((y + m : ℝ) : ℂ) = p) (hpb : p ∈ badSet κ ψ u b)
    (hlow : ¬ ∃ ε > 0, ∀ y'' ∈ Ioo (y + m) (y + m + ε), y'' ∉ β.jumps →
      β.fn y'' = -sleLambda κ - -(Real.pi / 2) * chiC κ) :
    Vq.wR xR ρR y ≤ -2 := by
  classical
  obtain ⟨hc, S, Fx, Fy, hSm, hSc, hSo, hSy, hSr, -⟩ := hSC
  obtain ⟨y₁, hy₁, hw⟩ := wR_eq_of_isFlowType hκ hft hy.le
  have hl := Sec4.sleLambda_pos hκ
  set E : Finset ℝ := cw.jumps ∪ Fw ∪ β.jumps.image (· - m) ∪ Fy.image (· - m) ∪
    (jumps ∪ Fx).image (fun x => rProf c x - m) with hE
  set G : ℝ → Prop := fun y'' => y < y'' ∧ y'' < y₁ ∧ y'' ∉ E with hG
  have hGcw : ∀ y'', G y'' → y'' ∉ cw.jumps := fun y'' hG h => hG.2.2 (Finset.mem_union_left _
    (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ h))))
  have hGFw : ∀ y'', G y'' → y'' ∉ Fw := fun y'' hG h => hG.2.2 (Finset.mem_union_left _
    (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ h))))
  have hev : ∀ᶠ y'' in 𝓝[>] y, G y'' := by
    have h1 : ∀ᶠ y'' in 𝓝[>] y, y'' < y₁ := (gt_mem_nhds hy₁).filter_mono nhdsWithin_le_nhds
    have h2 : ∀ᶠ y'' in 𝓝[>] y, y'' ∉ (E : Set ℝ) :=
      (eventually_notMem_of_finite E.finite_toSet y).filter_mono (nhdsWithin_mono _ fun z hz => ne_of_gt hz)
    filter_upwards [self_mem_nhdsWithin, h1, h2] with y'' hy'' hy''₁ hy''E using ⟨hy'', hy''₁, hy''E⟩
  -- an original point at every good point whose height is not the lower-side height
  have horig : ∀ y'', G y'' → β.fn (y'' + m) ≠ -sleLambda κ - -(Real.pi / 2) * chiC κ →
      ∃ x ∈ S, rProf c x = y'' + m ∧ x ∉ jumps ∧ b x = β.fn (y'' + m) ∧ u ≤ x ∧
        g ((y'' + m : ℝ) : ℂ) = (x : ℂ) := by
    intro y'' hG' hne
    have hE'' := hG'.2.2
    have hβJ : y'' + m ∉ β.jumps := fun h => hE'' (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_right _ (Finset.mem_image.2 ⟨y'' + m, h, by ring⟩))))
    have hFy : y'' + m ∉ Fy := fun h => hE'' (Finset.mem_union_left _
      (Finset.mem_union_right _ (Finset.mem_image.2 ⟨y'' + m, h, by ring⟩)))
    rcases hSy (y'' + m) hβJ hFy with ⟨hβ, -⟩ | ⟨x, hxS, hxy⟩
    · exact absurd hβ hne
    · have hxJ : x ∉ jumps := fun h => hE'' (Finset.mem_union_right _ (Finset.mem_image.2
        ⟨x, Finset.mem_union_left _ h, by rw [hxy]; ring⟩))
      have hxF : x ∉ Fx := fun h => hE'' (Finset.mem_union_right _ (Finset.mem_image.2
        ⟨x, Finset.mem_union_right _ h, by rw [hxy]; ring⟩))
      have hzJ : rProf c x ∉ β.jumps := by rw [hxy]; exact hβJ
      have hbx : β.fn (rProf c x) = b x := hSo x hxS hxJ hxF hzJ
      have h1 := bdry_eq_of_chartFree hcc hgc hgi (hSc x hxS).1 (hSc x hxS).2 (hc x)
      rw [hc.eq_ofReal x, hxy] at h1
      refine ⟨x, hxS, hxy, hxJ, by rw [← hbx, hxy], hSr x hxS (by rw [hxy]; linarith [hG'.1]), h1⟩
  -- a good point with a height other than the lower-side height
  obtain ⟨y₀, hy₀G, hy₀ne⟩ : ∃ y₀, G y₀ ∧ β.fn (y₀ + m) ≠ -sleLambda κ - -(Real.pi / 2) * chiC κ := by
    obtain ⟨ε, hε, hεG⟩ : ∃ ε > 0, Ioo y (y + ε) ⊆ {y'' | G y''} := by
      obtain ⟨u', hu', hsub⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).1 hev
      exact ⟨u' - y, by simpa using hu', by rw [add_sub_cancel]; exact hsub⟩
    by_contra hall
    push Not at hall
    refine hlow ⟨ε, hε, fun y'' hy'' _ => ?_⟩
    have := hall (y'' - m) (hεG ⟨by linarith [hy''.1], by linarith [hy''.2]⟩)
    rwa [sub_add_cancel] at this
  -- every good point carries that height
  have hconst : ∀ y'', G y'' → β.fn (y'' + m) = β.fn (y₀ + m) := by
    intro y'' hG'
    have e1 := hw y'' hG'.1 hG'.2.1 (hGcw y'' hG')
    have e2 := hw y₀ hy₀G.1 hy₀G.2.1 (hGcw y₀ hy₀G)
    rw [hcw y'' (hGFw y'' hG')] at e1
    rw [hcw y₀ (hGFw y₀ hy₀G)] at e2
    have e3 := e1.symm.trans e2
    unfold Sec4.cumWeightRight at e3
    have e4 : (β.fn (y'' + m) + ψ * chiC κ) / sleLambda κ = (β.fn (y₀ + m) + ψ * chiC κ) / sleLambda κ := by
      linarith
    rw [div_left_inj' hl.ne'] at e4
    linarith
  set v := β.fn (y₀ + m) with hv
  have horig' : ∀ y'', G y'' → ∃ x ∈ S, rProf c x = y'' + m ∧ x ∉ jumps ∧ b x = v ∧ u ≤ x ∧
      g ((y'' + m : ℝ) : ℂ) = (x : ℂ) := by
    intro y'' hG'
    obtain ⟨x, hxS, hxy, hxJ, hbx, hux, hgx⟩ := horig y'' hG' (by rw [hconst y'' hG']; exact hy₀ne)
    exact ⟨x, hxS, hxy, hxJ, by rw [hbx, hconst y'' hG'], hux, hgx⟩
  -- the read-back converges to `p`
  have hlim : Tendsto (fun y'' : ℝ => (g ((y'' + m : ℝ) : ℂ)).re) (𝓝[>] y) (𝓝 p) := by
    have h := (Complex.continuous_re.tendsto _).comp (tendsto_g_real (m := m) hgc (𝓝[>] y) nhdsWithin_le_nhds)
    rw [hp, Complex.ofReal_re] at h
    exact h
  have hgre : ∀ y'', G y'' → ∀ x : ℝ, g ((y'' + m : ℝ) : ℂ) = (x : ℂ) → (g ((y'' + m : ℝ) : ℂ)).re = x :=
    fun _ _ x hx => by rw [hx, Complex.ofReal_re]
  have hpu : u ≤ p := ge_of_tendsto hlim (hev.mono fun y'' hG' => by
    obtain ⟨x, -, -, -, -, hux, hgx⟩ := horig' y'' hG'
    rw [hgre y'' hG' x hgx]
    exact hux)
  -- the original points lie strictly right of `p`
  have hgt : ∀ y'', G y'' → ∀ x ∈ S, rProf c x = y'' + m → p < x := by
    intro y'' hG' x hxS hxy
    by_contra hle
    push Not at hle
    obtain ⟨y₃, hy₃G, hy₃⟩ : ∃ y₃, G y₃ ∧ y₃ < y'' := by
      obtain ⟨z, hz1, hz2⟩ := (hev.and (Ioo_mem_nhdsGT hG'.1)).exists
      exact ⟨z, hz1, hz2.2⟩
    obtain ⟨x₃, hx₃S, hx₃y, -, -, -, hg₃⟩ := horig' y₃ hy₃G
    have hx₃x : x₃ < x := (hSm.lt_iff_lt hx₃S hxS).1 (by rw [hx₃y, hxy]; linarith)
    have hev₃ : ∀ᶠ y₄ in 𝓝[>] y, (g ((y₄ + m : ℝ) : ℂ)).re ≤ x₃ := by
      filter_upwards [hev, Ioo_mem_nhdsGT hy₃G.1] with y₄ hG₄ hy₄
      obtain ⟨x₄, hx₄S, hx₄y, -, -, -, hg₄⟩ := horig' y₄ hG₄
      have h4 : x₄ < x₃ := (hSm.lt_iff_lt hx₄S hx₃S).1 (by rw [hx₄y, hx₃y]; linarith [hy₄.2])
      rw [hgre y₄ hG₄ x₄ hg₄]
      exact h4.le
    have := le_of_tendsto hlim hev₃
    linarith
  -- the right limit at `p` is `v`
  obtain ⟨δ, hδ, hδJ⟩ := Supp7.exists_pos_forall_notMem jumps p
  have hrl : rightLim b p = v := by
    have hev' : ∀ᶠ y'' in 𝓝[>] y, (g ((y'' + m : ℝ) : ℂ)).re < p + δ := hlim (gt_mem_nhds (by linarith))
    obtain ⟨y'', hG', hlt⟩ := (hev.and hev').exists
    obtain ⟨x, hxS, hxy, -, hbx, -, hgx⟩ := horig' y'' hG'
    have hxp := hgt y'' hG' x hxS hxy
    rw [hgre y'' hG' x hgx] at hlt
    rw [rightLim_eq_of_gap hb (fun z hz => (hδJ z hz).1) ⟨hxp, hlt⟩, hbx]
  have hbadp : Sec4.cumWeightRight κ (rightLim b p + ψ * chiC κ) ≤ -2 := by
    rcases hpb with ⟨-, h2⟩ | ⟨h1, -⟩
    · exact h2
    · exact absurd h1 (not_lt.2 hpu)
  rw [hrl] at hbadp
  rw [hw y₀ hy₀G.1 hy₀G.2.1 (hGcw y₀ hy₀G), hcw y₀ (hGFw y₀ hy₀G)]
  exact hbadp

/-- **Left side**: a bad physical point read back at a relative point `y < 0` is a bad relative point (left of the
entry every relative point is original). -/
theorem rel_bad_left (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps) (hcc : c.IsConformal)
    (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g c.2.1 H) (hSC : SecondClause κ b jumps c u m β.fn β.jumps)
    (hcw : ∀ y ∉ Fw, cw.fn y = β.fn (y + m)) (hft : FCDet.IsFlowType κ ψ cw xL xR ρL ρR) {y : ℝ} (hy : y < 0)
    {p : ℝ} (hp : g ((y + m : ℝ) : ℂ) = p) (hpb : p ∈ badSet κ ψ u b) :
    Vq.wL xL ρL y ≤ -2 := by
  classical
  obtain ⟨hc, S, Fx, Fy, hSm, hSc, hSo, hSy, -, hSl⟩ := hSC
  obtain ⟨y₁, hy₁, hw⟩ := wL_eq_of_isFlowType hκ hft hy.le
  set E : Finset ℝ := cw.jumps ∪ Fw ∪ β.jumps.image (· - m) ∪ Fy.image (· - m) ∪
    (jumps ∪ Fx).image (fun x => rProf c x - m) with hE
  set G : ℝ → Prop := fun y'' => y₁ < y'' ∧ y'' < y ∧ y'' ∉ E with hG
  have hGcw : ∀ y'', G y'' → y'' ∉ cw.jumps := fun y'' hG h => hG.2.2 (Finset.mem_union_left _
    (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ h))))
  have hGFw : ∀ y'', G y'' → y'' ∉ Fw := fun y'' hG h => hG.2.2 (Finset.mem_union_left _
    (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ h))))
  have hev : ∀ᶠ y'' in 𝓝[<] y, G y'' := by
    have h1 : ∀ᶠ y'' in 𝓝[<] y, y₁ < y'' := (lt_mem_nhds hy₁).filter_mono nhdsWithin_le_nhds
    have h2 : ∀ᶠ y'' in 𝓝[<] y, y'' ∉ (E : Set ℝ) :=
      (eventually_notMem_of_finite E.finite_toSet y).filter_mono (nhdsWithin_mono _ fun z hz => ne_of_lt hz)
    filter_upwards [self_mem_nhdsWithin, h1, h2] with y'' hy'' hy''₁ hy''E using ⟨hy''₁, hy'', hy''E⟩
  have horig : ∀ y'', G y'' → ∃ x ∈ S, rProf c x = y'' + m ∧ x ∉ jumps ∧ b x = β.fn (y'' + m) ∧ x < u ∧
      g ((y'' + m : ℝ) : ℂ) = (x : ℂ) := by
    intro y'' hG'
    have hE'' := hG'.2.2
    have hβJ : y'' + m ∉ β.jumps := fun h => hE'' (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_right _ (Finset.mem_image.2 ⟨y'' + m, h, by ring⟩))))
    have hFy : y'' + m ∉ Fy := fun h => hE'' (Finset.mem_union_left _
      (Finset.mem_union_right _ (Finset.mem_image.2 ⟨y'' + m, h, by ring⟩)))
    rcases hSy (y'' + m) hβJ hFy with ⟨-, hmy⟩ | ⟨x, hxS, hxy⟩
    · exfalso
      linarith [hG'.2.1]
    · have hxJ : x ∉ jumps := fun h => hE'' (Finset.mem_union_right _ (Finset.mem_image.2
        ⟨x, Finset.mem_union_left _ h, by rw [hxy]; ring⟩))
      have hxF : x ∉ Fx := fun h => hE'' (Finset.mem_union_right _ (Finset.mem_image.2
        ⟨x, Finset.mem_union_right _ h, by rw [hxy]; ring⟩))
      have hzJ : rProf c x ∉ β.jumps := by rw [hxy]; exact hβJ
      have hbx : β.fn (rProf c x) = b x := hSo x hxS hxJ hxF hzJ
      have h1 := bdry_eq_of_chartFree hcc hgc hgi (hSc x hxS).1 (hSc x hxS).2 (hc x)
      rw [hc.eq_ofReal x, hxy] at h1
      refine ⟨x, hxS, hxy, hxJ, by rw [← hbx, hxy], hSl x hxS (by rw [hxy]; linarith [hG'.2.1]), h1⟩
  have hlim : Tendsto (fun y'' : ℝ => (g ((y'' + m : ℝ) : ℂ)).re) (𝓝[<] y) (𝓝 p) := by
    have h := (Complex.continuous_re.tendsto _).comp (tendsto_g_real (m := m) hgc (𝓝[<] y) nhdsWithin_le_nhds)
    rw [hp, Complex.ofReal_re] at h
    exact h
  have hgre : ∀ y'', ∀ x : ℝ, g ((y'' + m : ℝ) : ℂ) = (x : ℂ) → (g ((y'' + m : ℝ) : ℂ)).re = x :=
    fun _ x hx => by rw [hx, Complex.ofReal_re]
  have hpu : p ≤ u := le_of_tendsto hlim (hev.mono fun y'' hG' => by
    obtain ⟨x, -, -, -, -, hxu, hgx⟩ := horig y'' hG'
    rw [hgre y'' x hgx]
    exact hxu.le)
  have hlt : ∀ y'', G y'' → ∀ x ∈ S, rProf c x = y'' + m → x < p := by
    intro y'' hG' x hxS hxy
    by_contra hle
    push Not at hle
    obtain ⟨y₃, hy₃G, hy₃⟩ : ∃ y₃, G y₃ ∧ y'' < y₃ := by
      obtain ⟨z, hz1, hz2⟩ := (hev.and (Ioo_mem_nhdsLT hG'.2.1)).exists
      exact ⟨z, hz1, hz2.1⟩
    obtain ⟨x₃, hx₃S, hx₃y, -, -, -, hg₃⟩ := horig y₃ hy₃G
    have hx₃x : x < x₃ := (hSm.lt_iff_lt hxS hx₃S).1 (by rw [hx₃y, hxy]; linarith)
    have hev₃ : ∀ᶠ y₄ in 𝓝[<] y, x₃ ≤ (g ((y₄ + m : ℝ) : ℂ)).re := by
      filter_upwards [hev, Ioo_mem_nhdsLT hy₃G.2.1] with y₄ hG₄ hy₄
      obtain ⟨x₄, hx₄S, hx₄y, -, -, -, hg₄⟩ := horig y₄ hG₄
      have h4 : x₃ < x₄ := (hSm.lt_iff_lt hx₃S hx₄S).1 (by rw [hx₄y, hx₃y]; linarith [hy₄.1])
      rw [hgre y₄ x₄ hg₄]
      exact h4.le
    have := ge_of_tendsto hlim hev₃
    linarith
  obtain ⟨δ, hδ, hδJ⟩ := Supp7.exists_pos_forall_notMem jumps p
  have hev' : ∀ᶠ y'' in 𝓝[<] y, p - δ < (g ((y'' + m : ℝ) : ℂ)).re := hlim (lt_mem_nhds (by linarith))
  obtain ⟨y'', hG', hgt⟩ := (hev.and hev').exists
  obtain ⟨x, hxS, hxy, -, hbx, -, hgx⟩ := horig y'' hG'
  have hxp := hlt y'' hG' x hxS hxy
  rw [hgre y'' x hgx] at hgt
  have hll : leftLim b p = β.fn (y'' + m) := by
    rw [leftLim_eq_of_gap hb (fun z hz => (hδJ z hz).2) ⟨hgt, hxp⟩, hbx]
  have hbadp : Sec4.cumWeightLeft κ (leftLim b p + ψ * chiC κ) ≤ -2 := by
    rcases hpb with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact absurd h1 (not_lt.2 hpu)
    · exact h2
  rw [hll] at hbadp
  rw [hw y'' hG'.1 hG'.2.1 (hGcw y'' hG'), hcw y'' (hGFw y'' hG')]
  exact hbadp

end Corr

/-! ### A bad relative tip forces the threshold -/

section Thr

variable {Ω : Type*} {W : ℝ≥0 → Ω → ℝ} {ω : Ω} {V : ℝ≥0∞} {Γ : ℝ≥0 → ℂ} {nL nR : ℕ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ} {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ}

theorem thr_le_of_mem {τ : ℝ≥0} (hTC : ForceWord.ThresholdCondition ρL ρR (W τ ω) (fun i => geomLW W xL i τ ω)
    (fun j => geomRW W xR j τ ω)) : FCDet.thr ρL ρR W xL xR ω ≤ τ := by
  have hmem : τ ∈ MartChar.thresholdSet ρL ρR (fun t => W t ω) (fun i t => geomLW W xL i t ω)
      (fun j t => geomRW W xR j t ω) := hTC
  unfold FCDet.thr MartChar.thresholdTime
  split_ifs with hne
  · exact ENNReal.coe_le_coe.2 (csInf_le (OrderBot.bddBelow _) hmem)
  · exact absurd ⟨τ, hmem⟩ hne

/-- **A relative tip at a bad right point forces the threshold by then.** -/
theorem thr_le_of_bad_right (hWc : Continuous fun t => W t ω) (hW0 : W 0 ω = 0)
    (hΓ : IsGeneratingTrace (fun t => W t ω) V Γ) {T : ℝ≥0} (hT0 : 0 < T) (hT : (T : ℝ≥0∞) ≤ V)
    (him : (Γ T).im = 0) (hpos : 0 < (Γ T).re) (hbad : Vq.wR (xR ω) ρR (Γ T).re ≤ -2) :
    FCDet.thr ρL ρR W xL xR ω ≤ T := by
  obtain ⟨hL, hc, -, -⟩ := trace_facts hWc hW0 hΓ hT0 hT
  have hU : Continuous (Bessel.realPath W ω) := hWc.comp continuous_real_toNNReal
  have hU0 : Bessel.realPath W ω 0 = 0 := by simp [Bessel.realPath, hW0]
  have hT0' : (0 : ℝ) < T := NNReal.coe_pos.2 hT0
  have hΓT : Γ (T : ℝ).toNNReal = Γ T := by simp
  obtain ⟨τ₀, hτ0, hτT, -, hsum⟩ := Vo.exists_first_threshold_right hU hU0 hT0' hL hc
    (by rw [hΓT]; exact him) (by rw [hΓT]; exact hpos) (xR ω) ρR (by rw [hΓT]; exact hbad)
  set τ : ℝ≥0 := τ₀.toNNReal with hτdef
  have hτ : (τ : ℝ) = τ₀ := Real.coe_toNNReal _ hτ0.le
  have hTC : ForceWord.ThresholdCondition ρL ρR (W τ ω) (fun i => geomLW W xL i τ ω)
      (fun j => geomRW W xR j τ ω) := by
    right
    have hf : univ.filter (fun j => geomRW W xR j τ ω = W τ ω) =
        univ.filter (fun j => rightImg (Bessel.realPath W ω) (xR ω j) τ₀ = Bessel.realPath W ω τ₀) :=
      Finset.filter_congr fun j _ => by
        simp only [geomRW, Bessel.realPath]
        rw [hτ]
    rw [hf]
    exact hsum
  refine (thr_le_of_mem hTC).trans (ENNReal.coe_le_coe.2 ?_)
  rw [← NNReal.coe_le_coe, hτ]
  exact hτT

/-- **A relative tip at a bad left point forces the threshold by then** (reflection). -/
theorem thr_le_of_bad_left (hWc : Continuous fun t => W t ω) (hW0 : W 0 ω = 0)
    (hΓ : IsGeneratingTrace (fun t => W t ω) V Γ) {T : ℝ≥0} (hT0 : 0 < T) (hT : (T : ℝ≥0∞) ≤ V)
    (him : (Γ T).im = 0) (hneg : (Γ T).re < 0) (hbad : Vq.wL (xL ω) ρL (Γ T).re ≤ -2) :
    FCDet.thr ρL ρR W xL xR ω ≤ T := by
  obtain ⟨hL, hc, -, -⟩ := trace_facts hWc hW0 hΓ hT0 hT
  set U := Bessel.realPath W ω with hUdef
  have hU : Continuous U := hWc.comp continuous_real_toNNReal
  have hU0 : U 0 = 0 := by simp [hUdef, Bessel.realPath, hW0]
  have hT0' : (0 : ℝ) < T := NNReal.coe_pos.2 hT0
  have hLr := Vo.isLoewnerTraceLT_reflect hL
  have hcr : ContinuousOn (fun s : ℝ => LP.reflectC (Γ s.toNNReal)) (Icc 0 T) :=
    LP.continuous_reflectC.comp_continuousOn hc
  have hre' : (LP.reflectC (Γ T)).re = -(Γ T).re := by simp [LP.reflectC]
  have him' : (LP.reflectC (Γ T)).im = (Γ T).im := by simp [LP.reflectC]
  have hwL : ∀ y : ℝ, Vq.wR (fun i => -xL ω i) ρL (-y) = Vq.wL (xL ω) ρL y := fun y => by
    unfold Vq.wR Vq.wL
    exact Finset.sum_congr (Finset.filter_congr fun i _ => by constructor <;> intro h <;> linarith) fun _ _ => rfl
  have hΓT : LP.reflectC (Γ (T : ℝ).toNNReal) = LP.reflectC (Γ T) := by simp
  have hnU : Continuous (-U) := hU.neg
  have hnU0 : (-U) 0 = 0 := by simp [hU0]
  obtain ⟨τ₀, hτ0, hτT, -, hsum⟩ := Vo.exists_first_threshold_right hnU hnU0 hT0' hLr hcr
    (by rw [hΓT, him']; exact him) (by rw [hΓT, hre']; linarith) (fun i => -xL ω i) ρL
    (by rw [hΓT, hre', hwL]; exact hbad)
  set τ : ℝ≥0 := τ₀.toNNReal with hτdef
  have hτ : (τ : ℝ) = τ₀ := Real.coe_toNNReal _ hτ0.le
  have hU' : Bessel.realPath (fun t ω => -W t ω) ω = -U := by
    funext r; simp [hUdef, Bessel.realPath]
  have hTC : ForceWord.ThresholdCondition ρL ρR (W τ ω) (fun i => geomLW W xL i τ ω)
      (fun j => geomRW W xR j τ ω) := by
    left
    have hf : univ.filter (fun i => geomLW W xL i τ ω = W τ ω) =
        univ.filter (fun i => rightImg (-U) (-xL ω i) τ₀ = (-U) τ₀) :=
      Finset.filter_congr fun i _ => by
        simp only [geomLW, hU', Pi.neg_apply, hUdef, Bessel.realPath]
        rw [hτ]
        constructor <;> intro h <;> linarith
    rw [hf]
    exact hsum
  refine (thr_le_of_mem hTC).trans (ENNReal.coe_le_coe.2 ?_)
  rw [← NNReal.coe_le_coe, hτ]
  exact hτT

end Thr

/-! ### Reading the relative trace back through the link -/

/-- **The link reads the relative trace back at every relative time up to the lifetime** (the lifetime included when
it is finite), and a finite relative lifetime is the physical one. -/
theorem readback {Ω : Type*} {W : ℝ≥0 → Ω → ℝ} {ω : Ω} {V : ℝ≥0∞} {Γ : ℝ≥0 → ℂ}
    (hWc : Continuous fun t => W t ω) (hW0 : W 0 ω = 0) (hΓ : IsGeneratingTrace (fun t => W t ω) V Γ)
    {c : Chart} {g : ℂ → ℂ} (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g c.2.1 H)
    {η : ℝ≥0 → ℂ} {ζ : ℝ≥0∞} (hηc : ContinuousOn η {t | (t : ℝ≥0∞) ≤ ζ}) {L m : ℝ}
    (hlink : IsRemainderLink c η ζ L (fun t => Γ t + (m : ℂ)) V) (hv : firstVisit η ζ L < ζ) :
    ∃ σ : ℝ≥0 → ℝ≥0, σ 0 = 0 ∧ Continuous σ ∧ 0 < V ∧
      (∀ s : ℝ≥0, (s : ℝ≥0∞) < V ↔ (((firstVisit η ζ L).toNNReal + σ s : ℝ≥0) : ℝ≥0∞) < ζ) ∧
      (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ V → 0 ≤ (Γ s).im ∧
        g (Γ s + (m : ℂ)) = η ((firstVisit η ζ L).toNNReal + σ s)) ∧
      (∀ T : ℝ≥0, V = T → ζ = (((firstVisit η ζ L).toNNReal + σ T : ℝ≥0) : ℝ≥0∞)) := by
  set tL := (firstVisit η ζ L).toNNReal with htL
  obtain ⟨σ, hσ0, -, hσc, hσ⟩ := hlink hv
  have hiff : ∀ s : ℝ≥0, (s : ℝ≥0∞) < V ↔ ((tL + σ s : ℝ≥0) : ℝ≥0∞) < ζ := fun s => (hσ s).1
  have htLζ : (tL : ℝ≥0∞) < ζ := by
    rw [htL, ENNReal.coe_toNNReal (hv.trans_le le_top).ne]; exact hv
  have hV0 : 0 < V := by
    have h0 := (hiff 0).2 (by rw [hσ0, add_zero]; exact htLζ)
    simpa using h0
  have hle : ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ V → ((tL + σ s : ℝ≥0) : ℝ≥0∞) ≤ ζ := fun s hs =>
    Lw.add_clock_le hσc hiff hV0 hs
  set D : Set ℝ≥0 := {t | (t : ℝ≥0∞) ≤ V} with hD
  set Gs : Set ℝ≥0 := {t | (t : ℝ≥0∞) < V ∧ Γ t ∈ H} with hGs
  have hGD : Gs ⊆ D := fun t ht => ht.1.le
  -- every time up to the lifetime is a limit of interior times
  have hWcon : ContinuousOn (fun t => W t ω) {s | (s : ℝ≥0∞) < V} := hWc.continuousOn
  have hDcl : D ⊆ closure Gs := by
    intro t ht
    rw [Metric.mem_closure_iff]
    intro ε hε
    rcases (show (t : ℝ≥0∞) ≤ V from ht).lt_or_eq with hlt | heq
    · obtain ⟨b, htb, hbV⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hlt
      have htb' : t < b := ENNReal.coe_lt_coe.1 htb
      set εn : ℝ≥0 := ⟨ε / 2, by positivity⟩ with hεndef
      have hεn : (εn : ℝ) = ε / 2 := rfl
      have hεn0 : 0 < εn := by rw [← NNReal.coe_pos, hεn]; linarith
      set b' : ℝ≥0 := min b (t + εn) with hb'
      have htb'' : t < b' := lt_min htb' (lt_add_of_pos_right t hεn0)
      have hb'V : (b' : ℝ≥0∞) ≤ V := (ENNReal.coe_le_coe.2 (min_le_left _ _)).trans hbV.le
      obtain ⟨s, hs, hsH⟩ := Restart.IsGeneratingTrace.exists_mem_H hΓ hWcon hW0 htb'' hb'V
      refine ⟨s, ⟨(ENNReal.coe_lt_coe.2 hs.2).trans_le hb'V, hsH⟩, ?_⟩
      have h1 : (s : ℝ) < t + ε / 2 := by
        have h3 : s < t + εn := lt_of_lt_of_le hs.2 (min_le_right _ _)
        have h4 := NNReal.coe_lt_coe.2 h3
        rw [NNReal.coe_add, hεn] at h4
        exact h4
      have h2 : (t : ℝ) < s := hs.1
      rw [NNReal.dist_eq, abs_sub_comm, abs_of_pos (by linarith)]
      linarith
    · have ht0 : 0 < t := by
        have : (0 : ℝ≥0∞) < t := heq ▸ hV0
        exact ENNReal.coe_pos.1 this
      have htpos : (0 : ℝ) < t := NNReal.coe_pos.2 ht0
      set δn : ℝ≥0 := ⟨min (ε / 2) ((t : ℝ) / 2), le_min (by positivity) (by positivity)⟩ with hδndef
      have hδn : (δn : ℝ) = min (ε / 2) ((t : ℝ) / 2) := rfl
      have hδn0 : 0 < δn := by
        rw [← NNReal.coe_pos, hδn]; exact lt_min (by linarith) (by linarith)
      have hδnt : δn ≤ t := by
        rw [← NNReal.coe_le_coe, hδn]
        have := min_le_right (ε / 2) ((t : ℝ) / 2)
        linarith
      set a : ℝ≥0 := t - δn with ha
      have hat : a < t := tsub_lt_self ht0 hδn0
      obtain ⟨s, hs, hsH⟩ := Restart.IsGeneratingTrace.exists_mem_H hΓ hWcon hW0 hat (le_of_eq heq)
      refine ⟨s, ⟨heq ▸ ENNReal.coe_lt_coe.2 hs.2, hsH⟩, ?_⟩
      have h1 : (a : ℝ) = t - min (ε / 2) ((t : ℝ) / 2) := by
        rw [ha, NNReal.coe_sub hδnt, hδn]
      have h2 : (a : ℝ) < s := hs.1
      have h3 : (s : ℝ) < t := hs.2
      rw [NNReal.dist_eq, abs_of_pos (by linarith)]
      have := min_le_left (ε / 2) ((t : ℝ) / 2)
      linarith
  -- both sides are continuous on the closed range and agree at interior times
  have hΓc : ContinuousOn Γ D := hΓ.2.1
  have hHbar : ∀ t ∈ D, 0 ≤ (Γ t).im := by
    intro t ht
    have hmem : Γ t ∈ closure (Γ '' Gs) := ((hΓc t ht).mono hGD).mem_closure_image (hDcl ht)
    have hsub : Γ '' Gs ⊆ {z : ℂ | 0 ≤ z.im} := by
      rintro _ ⟨s, hs, rfl⟩
      exact (show (0 : ℝ) < (Γ s).im from hs.2).le
    exact closure_minimal hsub (isClosed_le continuous_const Complex.continuous_im) hmem
  have hF1 : ContinuousOn (fun t => g (Γ t + (m : ℂ))) D :=
    hgc.comp (hΓc.add continuousOn_const) fun t ht => by
      show 0 ≤ (Γ t + (m : ℂ)).im
      simpa using hHbar t ht
  have hF2 : ContinuousOn (fun t => η (tL + σ t)) D :=
    hηc.comp ((continuous_const.add hσc).continuousOn) fun t ht => hle t ht
  have hEq : EqOn (fun t => g (Γ t + (m : ℂ))) (fun t => η (tL + σ t)) Gs := by
    intro t ht
    have hH : Γ t + (m : ℂ) ∈ H := by
      show 0 < (Γ t + (m : ℂ)).im
      have h2 : (0 : ℝ) < (Γ t).im := ht.2
      simpa using h2
    show g (Γ t + (m : ℂ)) = η (tL + σ t)
    rw [hgi hH]
    exact (hσ t).2 ht.1 hH
  have hEqD := hEq.of_subset_closure hF1 hF2 hGD hDcl
  refine ⟨σ, hσ0, hσc, hV0, hiff, fun s hs => ⟨hHbar s hs, hEqD hs⟩, fun T hT => ?_⟩
  refine le_antisymm ?_ (hle T (le_of_eq hT.symm))
  have h1 : ¬ ((tL + σ T : ℝ≥0) : ℝ≥0∞) < ζ := fun h => by
    have := (hiff T).2 h
    rw [hT] at this
    exact lt_irrefl _ this
  exact not_lt.1 h1

end InteractingSLE.Theorem14.SB.Wf
