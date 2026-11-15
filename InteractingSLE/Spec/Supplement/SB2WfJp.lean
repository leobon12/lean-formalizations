/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2WfJr
import InteractingSLE.Spec.Supplement.SB2WfRel

/-!
# The physical points of a piece's real trace points

Packet PROVE-T14-SB2WORD (round 3, the junction fact of E7). The three hypotheses `hB`, `hR`, `hL` of `jw_launch`, from
facts about the piece in its launch chart (word `β`, angle `θ < ψ`):

* `rightLim_word_rightRay`: right of the tip the word's right limits are the original data's at the read-back point;
* `jw_base`: if the seed is admissible on the right (`cumWeightRight (β⁺(0) + θχ) > −2`), the base is not upper-bad;
* `jw_rightTouch`: a right touch whose right weight for the piece is `> −2` is not upper-bad;
* `jw_leftTouch`: a left touch inside an open interval where the word is constant with left weight `< κ/2 − 2` (the
  touch criterion GB7a) reads back to a point right of the new left record which is not upper-bad: the word there is
  not the lower-side height, so the points are original (`OW`), their read-backs decrease to `p`, and
  `cumWeightRight (v + ψχ) = (ψ − θ)χ/λ − 2 − cumWeightLeft (v + θχ) > −2`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar chiC fwdMap fwdMapInv fwdHull IsForwardSol)

namespace InteractingSLE.Theorem14.SB.Wf

open Exist Exist.StagedLaw Exist.Staged Restart GW1W
open PiecewiseConstantBoundaryData (rightLim leftLim)

variable {κ θ ψ u : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- The upper right weight exceeds the lower one when the upper angle is larger. -/
theorem cumWeightRight_lt_of_angle (hκ : 0 < κ) (hκ4 : κ < 4) (hθψ : θ < ψ) (h : ℝ) :
    Sec4.cumWeightRight κ (h + θ * chiC κ) < Sec4.cumWeightRight κ (h + ψ * chiC κ) := by
  have hl := Sec4.sleLambda_pos hκ
  have hχ := Sec4.chiC_pos hκ hκ4
  unfold Sec4.cumWeightRight
  have : (h + θ * chiC κ) / sleLambda κ < (h + ψ * chiC κ) / sleLambda κ :=
    div_lt_div_of_pos_right (by nlinarith) hl
  linarith

/-- A low left weight for the lower angle gives an upper right weight `> −2`. -/
theorem cumWeightRight_gt_of_lowLeft (hκ : 0 < κ) (hκ4 : κ < 4) (hθψ : θ < ψ) {v : ℝ}
    (hv : Sec4.cumWeightLeft κ (v + θ * chiC κ) < κ / 2 - 2) :
    -2 < Sec4.cumWeightRight κ (v + ψ * chiC κ) := by
  have hl := Sec4.sleLambda_pos hκ
  have hχ := Sec4.chiC_pos hκ hκ4
  unfold Sec4.cumWeightLeft at hv
  unfold Sec4.cumWeightRight
  have h1 : (v + θ * chiC κ) / sleLambda κ > 1 - κ / 2 := by
    have : -(v + θ * chiC κ) / sleLambda κ = -((v + θ * chiC κ) / sleLambda κ) := neg_div _ _
    linarith
  have h2 : (v + ψ * chiC κ) / sleLambda κ = (v + θ * chiC κ) / sleLambda κ + (ψ - θ) * chiC κ / sleLambda κ := by
    field_simp; ring
  have h3 : 0 < (ψ - θ) * chiC κ / sleLambda κ := div_pos (mul_pos (by linarith) hχ) hl
  linarith

/-- **Right limits of the word right of the tip are those of the original data** at the read-back point. -/
theorem rightLim_word_rightRay {β : BoundaryWord} {s : ExplState} (hc : IsRealChart (stChart s))
    (hcc : (stChart s).IsConformal) (hR : RProf s) (hO : ROrig b jumps β s)
    (hfree : ∀ x, stRecR s < x → ContinuousAt (stChart s).1 (x : ℂ) ∧ ChartFree (stChart s) x)
    {g : ℂ → ℂ} (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g (stChart s).2.1 H) {z : ℝ} (hz : 0 ≤ z) :
    ∃ x₀ : ℝ, stRecR s ≤ x₀ ∧ g (z : ℂ) = x₀ ∧ rightLim β.fn z = rightLim b x₀ := by
  classical
  obtain ⟨hrb, hg0⟩ := rightRay_readback hc hcc hR hfree hgc hgi
  set c := stChart s with hcdef
  set R := stRecR s with hRdef
  -- the word right of `z`
  obtain ⟨δ, hδ, hδJ⟩ := Supp7.exists_pos_forall_notMem β.jumps z
  set v := rightLim β.fn z with hv
  have hvz : ∀ y ∈ Ioo z (z + δ), β.fn y = v := fun y hy =>
    (rightLim_eq_of_gap β.isPiecewiseConstantBoundaryData (fun w hw => (hδJ w hw).1) hy).symm
  -- the physical point and a right neighbourhood of it mapping into `(z, z + δ)`
  obtain ⟨x₀, hx₀R, hgx₀, x₁, hx₀₁, hx₁⟩ : ∃ x₀, R ≤ x₀ ∧ g (z : ℂ) = x₀ ∧ ∃ x₁, x₀ < x₁ ∧
      ∀ x ∈ Ioo x₀ x₁, R < x ∧ rProf c x ∈ Ioo z (z + δ) := by
    rcases hz.lt_or_eq with hzpos | hz0
    · obtain ⟨x₀, hx₀, hx₀e⟩ := RProf.exists_eq hR hzpos
      have hcont : ContinuousAt (rProf c) x₀ := hR.2.1.2.1.continuousAt (Ioi_mem_nhds hx₀)
      obtain ⟨ε, hε, hεc⟩ := Metric.continuousAt_iff.1 hcont δ hδ
      have hm : 0 < min ε (x₀ - R) := lt_min hε (by linarith)
      refine ⟨x₀, hx₀.le, by rw [← hx₀e]; exact hrb x₀ hx₀, x₀ + min ε (x₀ - R) / 2, by linarith,
        fun x hx => ?_⟩
      have hxR : R < x := lt_trans hx₀ hx.1
      refine ⟨hxR, ?_, ?_⟩
      · rw [← hx₀e]; exact hR.2.1.1 hx₀ hxR hx.1
      · have h1 : dist x x₀ < ε := by
          rw [Real.dist_eq, abs_of_pos (by linarith [hx.1])]
          linarith [hx.2, min_le_left ε (x₀ - R)]
        have h2 := hεc h1
        rw [Real.dist_eq, hx₀e] at h2
        linarith [(abs_lt.1 h2).2]
    · subst hz0
      obtain ⟨x₁, hx₁, hx₁ε⟩ := hR.2.2.2 δ hδ
      refine ⟨R, le_rfl, by rw [Complex.ofReal_zero, hg0], x₁, hx₁, fun x hx => ⟨hx.1, hR.2.2.1 x hx.1, ?_⟩⟩
      have := hR.2.1.1 hx.1 hx₁ hx.2
      simp only [zero_add]
      linarith
  refine ⟨x₀, hx₀R, hgx₀, ?_⟩
  set Ex : Set ℝ := {x | R < x ∧ rProf c x ∈ (β.jumps : Set ℝ)} with hEx
  have hExf : Ex.Finite :=
    Set.Finite.of_finite_image (f := rProf c) (β.jumps.finite_toSet.subset (by rintro _ ⟨x, hx, rfl⟩; exact hx.2))
      (hR.2.1.1.injOn.mono fun x hx => hx.1)
  refine (Sec4.rightLim_eq_of_forall_notMem (jumps ∪ hExf.toFinset) (a := x₁) hx₀₁ fun t ht htJ => ?_).symm
  have htj : t ∉ jumps := fun h => htJ (Finset.mem_union_left _ h)
  obtain ⟨htR, hty⟩ := hx₁ t ht
  have htβ : rProf c t ∉ β.jumps := fun h =>
    htJ (Finset.mem_union_right _ (hExf.mem_toFinset.2 ⟨htR, h⟩))
  rw [← hO t htR htj htβ]
  exact hvz _ hty

/-- **The base is not upper-bad** when the seed is admissible on the right. -/
theorem jw_base (hκ : 0 < κ) (hκ4 : κ < 4) (hθψ : θ < ψ) {β : BoundaryWord} {s : ExplState}
    (hc : IsRealChart (stChart s)) (hcc : (stChart s).IsConformal) (hR : RProf s) (hO : ROrig b jumps β s)
    (hfree : ∀ x, stRecR s < x → ContinuousAt (stChart s).1 (x : ℂ) ∧ ChartFree (stChart s) x)
    {g : ℂ → ℂ} (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g (stChart s).2.1 H) {L₁ : ℝ}
    (hL₁ : L₁ ≤ stRecR s) (hseed : -2 < Sec4.cumWeightRight κ (rightLim β.fn 0 + θ * chiC κ)) (p : ℝ)
    (hp : g 0 = p) : L₁ ≤ p ∧ (u < p → -2 < Sec4.cumWeightRight κ (rightLim b p + ψ * chiC κ)) := by
  obtain ⟨x₀, hx₀R, hgx₀, hrl⟩ := rightLim_word_rightRay hc hcc hR hO hfree hgc hgi (le_refl (0 : ℝ))
  rw [Complex.ofReal_zero, hp] at hgx₀
  have hpx : p = x₀ := by exact_mod_cast hgx₀
  subst hpx
  refine ⟨hL₁.trans hx₀R, fun _ => ?_⟩
  rw [← hrl]
  exact hseed.trans (cumWeightRight_lt_of_angle hκ hκ4 hθψ _)

/-- **A right touch that is not bad for the piece is not upper-bad.** -/
theorem jw_rightTouch (hκ : 0 < κ) (hκ4 : κ < 4) (hθψ : θ < ψ) {β : BoundaryWord} {s : ExplState}
    (hc : IsRealChart (stChart s)) (hcc : (stChart s).IsConformal) (hR : RProf s) (hO : ROrig b jumps β s)
    (hfree : ∀ x, stRecR s < x → ContinuousAt (stChart s).1 (x : ℂ) ∧ ChartFree (stChart s) x)
    {g : ℂ → ℂ} (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g (stChart s).2.1 H) {L₁ : ℝ}
    (hL₁ : L₁ ≤ stRecR s) {z : ℝ} (hz : 0 < z) (hw : -2 < Sec4.cumWeightRight κ (rightLim β.fn z + θ * chiC κ))
    (p : ℝ) (hp : g (z : ℂ) = p) :
    L₁ ≤ p ∧ (u < p → -2 < Sec4.cumWeightRight κ (rightLim b p + ψ * chiC κ)) := by
  obtain ⟨x₀, hx₀R, hgx₀, hrl⟩ := rightLim_word_rightRay hc hcc hR hO hfree hgc hgi hz.le
  rw [hp] at hgx₀
  have hpx : p = x₀ := by exact_mod_cast hgx₀
  subst hpx
  refine ⟨hL₁.trans hx₀R, fun _ => ?_⟩
  rw [← hrl]
  exact hw.trans (cumWeightRight_lt_of_angle hκ hκ4 hθψ _)

/-- **A left touch inside a low-weight constancy interval** reads back right of `L₁` (any bound below every original
point right of the touch) to a point that is not upper-bad. -/
theorem jw_leftTouch (hκ : 0 < κ) (hκ4 : κ < 4) (hθψ : θ < ψ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    {β : BoundaryWord} {s : ExplState} (hcc : (stChart s).IsConformal) (hOW : OW κ θ b jumps β s)
    (hc : IsRealChart (stChart s)) {g : ℂ → ℂ} (hgc : ContinuousOn g {z | 0 ≤ z.im})
    (hgi : EqOn g (stChart s).2.1 H) {z : ℝ} {a a' v : ℝ} (haz : a < z) (hza : z < a')
    (hcon : ∀ y ∈ Ioo a a', y ∉ β.jumps → β.fn y = v) (hlowv : Sec4.cumWeightLeft κ (v + θ * chiC κ) < κ / 2 - 2)
    {L₁ : ℝ} (hloc : ∃ δ > 0, ∀ x, (z < rProf (stChart s) x ∧ rProf (stChart s) x < z + δ) → L₁ ≤ x)
    (p : ℝ) (hp : g (z : ℂ) = p) :
    L₁ ≤ p ∧ (u < p → -2 < Sec4.cumWeightRight κ (rightLim b p + ψ * chiC κ)) := by
  classical
  obtain ⟨S, Fx, Fy, -, -, hSm, hSc, hSo, hSy, -⟩ := hOW
  set c := stChart s with hcdef
  have hl := Sec4.sleLambda_pos hκ
  -- `v` is not the lower-side height
  have hvne : v ≠ -sleLambda κ - θ * chiC κ := by
    intro hv
    rw [hv] at hlowv
    have h0 : Sec4.cumWeightLeft κ (-sleLambda κ - θ * chiC κ + θ * chiC κ) = 0 := by
      unfold Sec4.cumWeightLeft
      field_simp
      ring
    rw [h0] at hlowv
    linarith
  obtain ⟨δ₀, hδ₀, hloc'⟩ := hloc
  set E : Finset ℝ := β.jumps ∪ Fy ∪ (jumps ∪ Fx).image (fun x => rProf c x) with hE
  set G : ℝ → Prop := fun y => z < y ∧ y < min a' (z + δ₀) ∧ y ∉ E with hG
  have hev : ∀ᶠ y in 𝓝[>] z, G y := by
    have h1 : ∀ᶠ y in 𝓝[>] z, y < min a' (z + δ₀) :=
      (gt_mem_nhds (lt_min hza (by linarith))).filter_mono nhdsWithin_le_nhds
    have h2 : ∀ᶠ y in 𝓝[>] z, y ∉ (E : Set ℝ) :=
      (eventually_notMem_of_finite E.finite_toSet z).filter_mono (nhdsWithin_mono _ fun w hw => ne_of_gt hw)
    filter_upwards [self_mem_nhdsWithin, h1, h2] with y hy hy₁ hyE using ⟨hy, hy₁, hyE⟩
  -- every good point right of `z` is the image of an original point with data `v`
  have horig : ∀ y, G y → ∃ x ∈ S, rProf c x = y ∧ x ∉ jumps ∧ b x = v ∧ L₁ ≤ x ∧ g (y : ℂ) = (x : ℂ) := by
    intro y hGy
    have hyE := hGy.2.2
    have hyJ : y ∉ β.jumps := fun h => hyE (Finset.mem_union_left _ (Finset.mem_union_left _ h))
    have hyF : y ∉ Fy := fun h => hyE (Finset.mem_union_left _ (Finset.mem_union_right _ h))
    have hya : y ∈ Ioo a a' := ⟨lt_trans haz hGy.1, lt_of_lt_of_le hGy.2.1 (min_le_left _ _)⟩
    have hβy := hcon y hya hyJ
    rcases hSy y hyJ hyF with ⟨hlow', -⟩ | ⟨x, hxS, hxy⟩
    · exact absurd (hβy.symm.trans hlow') hvne
    · have hxJ : x ∉ jumps := fun h => hyE (Finset.mem_union_right _ (Finset.mem_image.2
        ⟨x, Finset.mem_union_left _ h, hxy⟩))
      have hxF : x ∉ Fx := fun h => hyE (Finset.mem_union_right _ (Finset.mem_image.2
        ⟨x, Finset.mem_union_right _ h, hxy⟩))
      have hzJ : rProf c x ∉ β.jumps := by rw [hxy]; exact hyJ
      have hbx : β.fn (rProf c x) = b x := hSo x hxS hxJ hxF hzJ
      have h1 := bdry_eq_of_chartFree hcc hgc hgi (hSc x hxS).1 (hSc x hxS).2 (hc x)
      rw [hc.eq_ofReal x, hxy] at h1
      refine ⟨x, hxS, hxy, hxJ, by rw [← hbx, hxy, hβy], hloc' x ⟨by rw [hxy]; exact hGy.1, ?_⟩, h1⟩
      rw [hxy]; exact lt_of_lt_of_le hGy.2.1 (min_le_right _ _)
  have hlim : Tendsto (fun y : ℝ => (g ((y + 0 : ℝ) : ℂ)).re) (𝓝[>] z) (𝓝 p) := by
    have h := (Complex.continuous_re.tendsto _).comp (tendsto_g_real (m := 0) hgc (𝓝[>] z) nhdsWithin_le_nhds)
    rw [add_zero, hp, Complex.ofReal_re] at h
    exact h
  have hgre : ∀ y x : ℝ, g (y : ℂ) = (x : ℂ) → (g ((y + 0 : ℝ) : ℂ)).re = x := fun y x hx => by
    rw [add_zero, hx, Complex.ofReal_re]
  have hLp : L₁ ≤ p := ge_of_tendsto hlim (hev.mono fun y hGy => by
    obtain ⟨x, -, -, -, -, hLx, hgx⟩ := horig y hGy
    rw [hgre y x hgx]
    exact hLx)
  refine ⟨hLp, fun _ => ?_⟩
  -- the originals lie strictly right of `p`
  have hgt : ∀ y, G y → ∀ x ∈ S, rProf c x = y → p < x := by
    intro y hGy x hxS hxy
    by_contra hle
    push Not at hle
    obtain ⟨y₃, hy₃G, hy₃⟩ : ∃ y₃, G y₃ ∧ y₃ < y := by
      obtain ⟨w, hw1, hw2⟩ := (hev.and (Ioo_mem_nhdsGT hGy.1)).exists
      exact ⟨w, hw1, hw2.2⟩
    obtain ⟨x₃, hx₃S, hx₃y, -, -, -, hg₃⟩ := horig y₃ hy₃G
    have hx₃x : x₃ < x := (hSm.lt_iff_lt hx₃S hxS).1 (by rw [hx₃y, hxy]; exact hy₃)
    have hev₃ : ∀ᶠ y₄ in 𝓝[>] z, (g ((y₄ + 0 : ℝ) : ℂ)).re ≤ x₃ := by
      filter_upwards [hev, Ioo_mem_nhdsGT hy₃G.1] with y₄ hG₄ hy₄
      obtain ⟨x₄, hx₄S, hx₄y, -, -, -, hg₄⟩ := horig y₄ hG₄
      have h4 : x₄ < x₃ := (hSm.lt_iff_lt hx₄S hx₃S).1 (by rw [hx₄y, hx₃y]; exact hy₄.2)
      rw [hgre y₄ x₄ hg₄]
      exact h4.le
    have := le_of_tendsto hlim hev₃
    linarith
  obtain ⟨δ, hδ, hδJ⟩ := Supp7.exists_pos_forall_notMem jumps p
  have hev' : ∀ᶠ y in 𝓝[>] z, (g ((y + 0 : ℝ) : ℂ)).re < p + δ := hlim (gt_mem_nhds (by linarith))
  obtain ⟨y, hGy, hlt⟩ := (hev.and hev').exists
  obtain ⟨x, hxS, hxy, -, hbx, -, hgx⟩ := horig y hGy
  have hxp := hgt y hGy x hxS hxy
  rw [hgre y x hgx] at hlt
  rw [rightLim_eq_of_gap hb (fun w hw => (hδJ w hw).1) ⟨hxp, hlt⟩, hbx]
  exact cumWeightRight_gt_of_lowLeft hκ hκ4 hθψ hlowv

end InteractingSLE.Theorem14.SB.Wf
