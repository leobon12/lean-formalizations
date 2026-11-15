/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma71PSide

/-!
# Lemma 7.1's (CS), geometric half: the middle curve's integer is `0` (the junction with the left wall)

Packet PROVE-LEMMA71P (supplement §2.3, the corner argument of the deterministic normalization lemma, at the junction
of the left wall and the middle curve). In the setting `IsTSetting` at capacity time `t`, at the image `x₀ = L_t − W_t`
of `0⁻` the boundary of the active component switches from the left wall `β` (alive chart points `< x₀`) to the left
side of the stopped middle curve (`x₀ < x < x₁`). With `Γ = β([0, q₁]) ∪ γ([0, T])` (`q₁` past the junction point):

* the transition `g_Γ ∘ ψ_t⁻¹` has real limits at every real point near `x₀` other than `x₀`
  (`exists_real_tendsto_mapOut_path`: the landing points lie on `Γ`), and a real limit at `x₀` (removable corner,
  `exists_tendsto_of_realLimits_at`), so `Im (log g_Γ′ − log ψ_t′) ∘ ψ_t⁻¹ → 2πn_c` near `x₀`
  (`Lemma71O.exists_int_tendsto_of_realLimits`);
* at a wall point left of `x₀`: `Im log g_Γ′ − Im log g^β′ → 0` (Aux. 57 along the chart), and
  `Im log ψ_t′ − Im log g^β′ → 0` (the inherited branch `IsPocketBranch` at the alive point, and `arg f_t′ → 0` there),
  so `n_c = 0`;
* at a point `z₂ ∈ (x₀, x₁)` landing inside the pocket (`exists_mem_H_of_lt`, so off the left wall):
  `Im log g_Γ′ − Im log g^γ_T′ → 0` (Aux. 57), so the middle-curve integer at `z₂` is `0`
  (**`IsTSetting.exists_wallInt_zero_junction`**).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.Lemma71P

open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull logDerivFwd)
open QuantumZipper.CA (cayley cayleyInv)
open Lemma71K (IsMarkedPocket wallPt segPt)
open Lemma71N (IsPocketFrame IsPocketBranch)
open Lemma71O (land WallInt)
open Lemma71C (IsSegCurve capLife capInv segDriver)
open MartChar.RealFlow

theorem simpleProper_mem_Hbar {η : ℝ≥0 → ℂ} (h : Lemma71I.IsSimpleProper η) (s : ℝ≥0) : η s ∈ Hbar := by
  rcases eq_zero_or_pos s with rfl | hs
  · rw [h.2.2.1]; exact mem_Hbar_of_im_eq_zero (by simp)
  · exact H_subset_Hbar (h.2.2.2.1 s hs)

namespace IsTSetting

variable {β α γ : ℝ≥0 → ℂ} {C : Set ℂ} {c : Chart} {Ψ : ℂ → ℂ} {a b : ℝ} {γ' : ℝ → ℂ} {κ : ℝ → ℝ} {n : ℤ}
  {W : ℝ → ℝ} {η : ℝ → ℂ} {t : ℝ≥0}

/-- The landing map along the real chart axis is continuous. -/
theorem continuous_land (hS : IsTSetting β α γ C c Ψ a b γ' κ n W η t) :
    Continuous fun z : ℝ => land c (extendFrom H (fwdMapInv W t) z) := by
  have hmem : ∀ z : ℝ, extendFrom H (fwdMapInv W t) z ∈ Hbar := fun z =>
    extendFrom_mem_Hbar hS.hη hS.hW hS.hW0 t.coe_nonneg (mem_Hbar_of_im_eq_zero (by simp))
  have h1 : Continuous fun z : ℝ => extendFrom H (fwdMapInv W t) z :=
    continuousOn_univ.1 (hS.hB.continuousOn.comp Complex.continuous_ofReal.continuousOn
      fun z _ => mem_Hbar_of_im_eq_zero (by simp))
  exact continuousOn_univ.1 ((Lemma71O.PocketFrame.continuousOn_land hS.seg.frame).comp h1.continuousOn
    fun z _ => hmem z)

/-- **The left wall points of the active component**: a real chart point left of `L_t − W_t` is the image of an alive
real point `ξ < 0`, and the chart lands there at a point `β s` (`s > 0`, off the right wall). -/
theorem exists_wall_left (hS : IsTSetting β α γ C c Ψ a b γ' κ n W η t) {z : ℝ} (hz : z < midL W t) :
    ∃ ξ : ℝ, ξ < 0 ∧ (∃ u : ℝ → ℂ, QuantumZipper.IsForwardSol W (ξ : ℂ) t u) ∧
      extendFrom H (fwdMapInv W t) z = ξ ∧ Tendsto (fwdMapInv W t) (𝓝[H] (z : ℂ)) (𝓝[H] (ξ : ℂ)) ∧
      ∃ s : ℝ≥0, 0 < s ∧ β s ∉ range α ∧ land c ξ = β s := by
  have ht0 := hS.ht0
  obtain ⟨y, hy0, hya, hyx⟩ := Lemma71N.exists_alive_neg_cflow_eq hS.hW ht0 (x := z) hz
  have hu := WangWu.isForwardSol_neg_of_alive hS.hW hya
  have hu' : QuantumZipper.IsForwardSol W ((-y : ℝ) : ℂ) t (fun s => -(cflow (fun s => -W s) y s : ℂ)) := by
    rwa [ofReal_neg]
  have hFz : extendFrom H (fwdMapInv W t) z = ((-y : ℝ) : ℂ) := by
    have h := SideHeight.extendFrom_eq_of_isForwardSol' hS.hB hS.hW hS.hW0 ht0
      (mem_Hbar_of_im_eq_zero (by simp)) hu'
    have e : -(cflow (fun s => -W s) y t : ℂ) = ((z : ℝ) : ℂ) := by rw [← hyx]; push_cast; ring
    rwa [e] at h
  obtain ⟨s, hs0, hsα, hls⟩ := Lemma71O.PocketFrame.land_ofReal_neg hS.seg.frame (show -y < 0 by linarith)
  refine ⟨-y, by linarith, ⟨_, hu'⟩, hFz, ?_, s, hs0, hsα, hls⟩
  have hzH : ((z : ℝ) : ℂ) ∈ Hbar := mem_Hbar_of_im_eq_zero (by simp)
  refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun w hw =>
    QuantumZipper.RS.fwdMapInv_mem_H hS.hW hS.hW0 ht0 hw⟩
  have := hS.hB.tendsto hzH
  rwa [hFz] at this

/-- **The inherited branch, transported to the time-`t` chart at a left wall point**: at a real chart point `z` left
of `L_t − W_t` landing at `β s`, `s < q`, `Im L_t − Im log g^β_q′ → 0` along `ψ_t⁻¹` (`IsPocketBranch` at the alive
point `ξ = F̄_t(z)`, and `arg f_t′ → 0` there, `Sec6.tendsto_im_logDerivFwd_of_isForwardSol_real`). -/
theorem tendsto_wall_branch (hS : IsTSetting β α γ C c Ψ a b γ' κ n W η t) {Wβ Wα : ℝ≥0 → ℝ}
    (htrβ : IsGeneratingTrace Wβ ⊤ β) (htrα : IsGeneratingTrace Wα ⊤ α) {Lt : ℂ → ℂ}
    (hLte : ∀ z ∈ ((tChart c n W t).dom : Set ℂ), (tChart c n W t).2.2 z = (Lt z).im) {z : ℝ}
    (hz : z < midL W t) {s q : ℝ≥0} (hsq : s < q) (hls : land c (extendFrom H (fwdMapInv W t) z) = β s) :
    Tendsto (fun y => (Lt ((tChart c n W t).2.1 y)).im -
      (logDerivFwd (fun r : ℝ => Wβ r.toNNReal) q ((tChart c n W t).2.1 y)).im) (𝓝[H] (z : ℂ)) (𝓝 0) := by
  have ht0 := hS.ht0
  have hF := hS.seg.frame
  obtain ⟨ξ, hξ0, ⟨u, hu⟩, hFz, hFt, -⟩ := hS.exists_wall_left hz
  have hξH : ((ξ : ℝ) : ℂ) ∈ Hbar := mem_Hbar_of_im_eq_zero (by simp)
  have hlandξ : Tendsto c.2.1 (𝓝[H] (ξ : ℂ)) (𝓝 (β s)) := by
    have h := Lemma71O.PocketFrame.tendsto_land hF hξH
    rwa [← hFz, hls, hFz] at h
  have hbr := ((hS.branch Wβ Wα htrβ htrα ξ s q hsq).1 hξ0 hlandξ).comp hFt
  have hca := (Sec6.tendsto_im_logDerivFwd_of_isForwardSol_real hS.hW ht0 hu).comp hFt
  have hsum := hca.add hbr
  rw [add_zero] at hsum
  refine hsum.congr' (eventually_nhdsWithin_of_forall fun y hy => ?_)
  have hyH := QuantumZipper.RS.fwdMapInv_mem_H hS.hW hS.hW0 ht0 hy
  simp only [Function.comp_apply]
  rw [← hLte _ (hS.inv_mem_dom hy)]
  show _ = (logDerivFwd W t (c.1 (c.2.1 (fwdMapInv W t y)))).im + (c.2.2 (c.2.1 (fwdMapInv W t y)) + 2 * π * n) -
      (logDerivFwd (fun r : ℝ => Wβ r.toNNReal) q (c.2.1 (fwdMapInv W t y))).im
  rw [hF.hc.2.2 _ hyH]
  ring

/-- **The junction with the left wall** (supplement §2.3, the corner argument): if every chart point of
`(L_t − W_t, x₁)` is a middle point `≠ 0`, some point `z` of that interval has middle-curve integer `0` for the stopped
prefix `γ([0, T])`. -/
theorem exists_wallInt_zero_junction (hS : IsTSetting β α γ C c Ψ a b γ' κ n W η t) {Wβ Wα Wγ : ℝ≥0 → ℝ}
    (htrβ : IsGeneratingTrace Wβ ⊤ β) (htrα : IsGeneratingTrace Wα ⊤ α) (htrγ : IsGeneratingTrace Wγ ⊤ γ)
    {Lt : ℂ → ℂ} (hLt : IsDerivLog (tChart c n W t).1 Lt (tChart c n W t).dom)
    (hLte : ∀ z ∈ ((tChart c n W t).dom : Set ℂ), (tChart c n W t).2.2 z = (Lt z).im)
    {x₁ : ℝ} (hx₁ : midL W t < x₁) (hmid : ∀ z ∈ Ioo (midL W t) x₁, z < midR W t ∧ z ≠ 0) :
    ∃ z ∈ Ioo (midL W t) x₁, WallInt (tChart c n W t) Lt Wγ hS.capT z 0 := by
  have hF := hS.seg.frame
  have ht0 := hS.ht0
  set x₀ := midL W t with hx₀
  set ct := tChart c n W t with hct
  set D : Set ℂ := (ct.dom : Set ℂ) with hD
  set ℓ : ℝ → ℂ := fun z => land c (extendFrom H (fwdMapInv W t) z) with hℓ
  have hℓc : Continuous ℓ := hS.continuous_land
  have hℓT : ∀ z : ℝ, Tendsto ct.2.1 (𝓝[H] (z : ℂ)) (𝓝 (ℓ z)) := fun z =>
    tendsto_tChart_inv (t := t) hF hS.hη hS.hW hS.hW0 n (mem_Hbar_of_im_eq_zero (by simp))
  have hWβ := Lemma71O.continuous_of_isGeneratingTrace_top htrβ
  have hWβ0 : Wβ 0 = 0 := SideHeight.w_zero_of_isGeneratingTrace htrβ (by simp)
  have hWγ := Lemma71O.continuous_of_isGeneratingTrace_top htrγ
  have hWγ0 : Wγ 0 = 0 := SideHeight.w_zero_of_isGeneratingTrace htrγ (by simp)
  -- the junction point is on the left wall
  obtain ⟨sP, hsP⟩ : ∃ sP : ℝ≥0, ℓ x₀ = β sP := by
    have hcl := Lemma71Pin.IsSimpleProper.isClosed_range hF.hβ
    have ht : Tendsto ℓ (𝓝[<] x₀) (𝓝 (ℓ x₀)) := (hℓc.tendsto x₀).mono_left nhdsWithin_le_nhds
    obtain ⟨s, hs⟩ := hcl.mem_of_tendsto ht (eventually_nhdsWithin_of_forall fun z hz => by
      obtain ⟨ξ, -, -, hFz, -, s, -, -, hls⟩ := hS.exists_wall_left (show z < midL W t from hz)
      refine ⟨s, ?_⟩
      show β s = land c (extendFrom H (fwdMapInv W t) z)
      rw [hFz]; exact hls.symm)
    exact ⟨s, hs.symm⟩
  set q₁ : ℝ≥0 := sP + 1 with hq₁
  have hsPq₁ : sP < q₁ := by rw [hq₁]; exact lt_add_one sP
  have hq₁0 : 0 < q₁ := lt_of_le_of_lt (zero_le (a := sP)) hsPq₁
  obtain ⟨ρ₁, hρ₁, hball₁⟩ := Lemma71N.exists_ball_tail hF.hβ hsPq₁
  obtain ⟨δ₁, hδ₁, hℓδ⟩ := Metric.continuous_iff.1 hℓc x₀ ρ₁ hρ₁
  -- the wall side near the junction
  have hwall : ∀ z : ℝ, z < x₀ → x₀ - δ₁ < z → ∃ s : ℝ≥0, s < q₁ ∧ ℓ z = β s ∧ β s ∉ γ '' Icc 0 hS.capT := by
    intro z hz hzδ
    obtain ⟨ξ, hξ0, ⟨u, hu⟩, hFz, -, s, -, -, hls⟩ := hS.exists_wall_left hz
    have hℓz : ℓ z = β s := by
      show land c (extendFrom H (fwdMapInv W t) z) = β s
      rw [hFz]; exact hls
    refine ⟨s, ?_, hℓz, ?_⟩
    · by_contra hle
      refine hball₁ s (not_lt.1 hle) ?_
      rw [← hℓz, ← hsP, mem_ball]
      exact hℓδ z (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
    · rw [← hls]; exact hS.notMem_prefix_of_alive hξ0.ne hu
  -- the union hull `Γ = β([0, q₁]) ∪ γ([0, T])`
  set T' := hS.capT with hT'
  set Γ := Restart.prefixSet β q₁ γ T' with hΓ
  have hβγ0 : β 0 = γ 0 := by rw [hF.hβ.2.2.1, hS.seg.hγ.2.2.1]
  have hΓe : outBack β γ q₁ '' Icc 0 (2 * q₁ + T') = Γ := image_outBack hβγ0 q₁ T'
  have hζc : Continuous (outBack β γ q₁) := continuous_outBack hF.hβ.1 hS.seg.hγ.1 hβγ0 q₁
  have hζH : MapsTo (outBack β γ q₁) (Icc 0 (2 * q₁ + T')) Hbar := fun r _ => by
    unfold outBack
    split_ifs
    · exact simpleProper_mem_Hbar hF.hβ _
    · exact simpleProper_mem_Hbar hS.seg.hγ _
  have hζ0 : (outBack β γ q₁ 0).im = 0 := by rw [outBack_zero q₁.coe_nonneg, hF.hβ.2.2.1]; simp
  have hS0 : (0 : ℝ) ≤ 2 * q₁ + T' := by positivity
  have hΓc : IsCompact Γ := Restart.isCompact_prefixSet hF.hβ.1.continuousOn hS.seg.hγ.1.continuousOn
  have hKΓ : IsHPHull (fillH Γ) := Restart.isHPHull_fillH_prefixSet hF.hβ.1.continuousOn
    hS.seg.hγ.1.continuousOn (by rw [hF.hβ.2.2.1]; simp) (by rw [hS.seg.hγ.2.2.1]; simp)
  set gK := ConformalImage.mapOut (fillH Γ) with hgKdef
  have hgK : IsMapOut (fillH Γ) gK := ConformalImage.isMapOut_mapOut hKΓ
  obtain ⟨LK, hLK⟩ := Restart.exists_isCanonicalDerivLog hKΓ hgK
  have hDΓ : D ⊆ H \ fillH Γ := hS.subset_H_diff_fillH hΓc.isClosed fun z hz => by
    rcases hz with ⟨u, -, rfl⟩ | h
    · exact Or.inl ⟨u, rfl⟩
    · exact Or.inr h
  have hpΓ : ∀ p ∈ Γ, p ∉ H \ fillH Γ := fun p hp hp' => hp'.2 ⟨hp'.1, Or.inl (subset_closure hp)⟩
  -- the landing points near the junction lie on `Γ`
  set r₀ := min δ₁ (x₁ - x₀) with hr₀
  have hr₀0 : 0 < r₀ := lt_min hδ₁ (by linarith)
  have hgam : ∀ z : ℝ, x₀ < z → z < x₁ →
      ∃ σ : ℝ≥0, σ < T' ∧ Tendsto ct.2.1 (𝓝[H] (z : ℂ)) (𝓝 (γ σ)) ∧ ℓ z = γ σ := by
    intro z hz hz₁
    obtain ⟨hzR, hz0⟩ := hmid z ⟨hz, hz₁⟩
    obtain ⟨σ, hσ, hT, -⟩ := hS.exists_land hz hzR hz0
    have := Lemma71O.nhdsWithin_H_ofReal_neBot z
    exact ⟨σ, hσ, hT, tendsto_nhds_unique (hℓT z) hT⟩
  have hlandΓ : ∀ z : ℝ, |z - x₀| < r₀ → z ≠ x₀ → ℓ z ∈ Γ := by
    intro z hz hzne
    rw [abs_lt] at hz
    rcases lt_or_gt_of_ne hzne with hlt | hgt
    · obtain ⟨s, hs, hℓz, -⟩ := hwall z hlt (by linarith [min_le_left δ₁ (x₁ - x₀)])
      rw [hℓz]; exact Or.inl ⟨s, ⟨zero_le, hs.le⟩, rfl⟩
    · obtain ⟨σ, hσ, -, hℓz⟩ := hgam z hgt (by linarith [min_le_right δ₁ (x₁ - x₀)])
      rw [hℓz]; exact Or.inr ⟨σ, ⟨zero_le, hσ.le⟩, rfl⟩
  have hlimK : ∀ z : ℝ, |z - x₀| < r₀ → z ≠ x₀ → ∃ v : ℂ, v.im = 0 ∧
      Tendsto (fun y => gK (ct.2.1 y)) (𝓝[H] (z : ℂ)) (𝓝 v) := by
    intro z hz hzne
    have h := exists_real_tendsto_mapOut_path hS0 hζc.continuousOn hζH hζ0 hS.hc' (by rw [hΓe]; exact hDΓ)
      (mem_Hbar_of_im_eq_zero (z := ((z : ℝ) : ℂ)) (by simp)) (hℓT z)
      (by rw [hΓe]; exact hpΓ _ (hlandΓ z hz hzne))
    rwa [hΓe] at h
  -- the corner at the junction
  obtain ⟨δ₂, hδ₂, hδ₂p⟩ := Metric.tendsto_nhdsWithin_nhds.1 (hℓT x₀) 1 one_pos
  obtain ⟨M, hM⟩ := hgK.exists_norm_sub_le hKΓ
  set r := min r₀ δ₂ with hr
  have hr0 : 0 < r := lt_min hr₀0 hδ₂
  have hbd : ∀ y ∈ ball (x₀ : ℂ) r ∩ H, ‖gK (ct.2.1 y)‖ ≤ ‖ℓ x₀‖ + 1 + M := by
    rintro y ⟨hyb, hy⟩
    have h1 := hδ₂p hy (lt_of_lt_of_le (mem_ball.1 hyb) (min_le_right _ _))
    have h2 := hM _ (hDΓ (hS.inv_mem_dom hy))
    have h3 : ‖ct.2.1 y‖ ≤ ‖ℓ x₀‖ + 1 := by
      have := norm_le_norm_add_norm_sub' (ct.2.1 y) (ℓ x₀)
      rw [← dist_eq_norm] at this; linarith
    have := norm_le_norm_add_norm_sub' (gK (ct.2.1 y)) (ct.2.1 y)
    linarith
  have hlim' : ∀ z ∈ ball (x₀ : ℂ) r, z.im = 0 → z ≠ x₀ → ∃ v : ℂ, v.im = 0 ∧
      Tendsto (fun y => gK (ct.2.1 y)) (𝓝[H] z) (𝓝 v) := by
    intro z hz hz0 hzne
    have hzx : z = ((z.re : ℝ) : ℂ) := eq_ofReal_re_of_im_eq_zero hz0
    have hzr : |z.re - x₀| < r := by
      rw [hzx, mem_ball, Lemma71O.dist_ofReal_ofReal, Real.dist_eq] at hz; exact hz
    rw [hzx]
    exact hlimK z.re (lt_of_lt_of_le hzr (min_le_left _ _)) (fun h => hzne (by rw [hzx, h]))
  obtain ⟨v₀, hv₀, hT₀⟩ := exists_tendsto_of_realLimits_at hS.hc' rfl hDΓ hgK.1.1 hgK.1.2.injOn hgK.1.2.mapsTo
    hr0 hbd hlim'
  obtain ⟨nc, ε, hε, hεr, hint⟩ := Lemma71O.exists_int_tendsto_of_realLimits hS.hc' rfl hLt hKΓ.2.2.1 hDΓ
    hgK.1.1 hgK.1.2.injOn hgK.1.2.mapsTo hLK.1 hr0 fun z hz hz0 => by
      by_cases hzx₀ : z = x₀
      · rw [hzx₀]; exact ⟨v₀, hv₀, hT₀⟩
      · exact hlim' z hz hz0 hzx₀
  have hball' : ∀ z : ℝ, |z - x₀| < ε → ((z : ℝ) : ℂ) ∈ ball (x₀ : ℂ) ε := fun z hz => by
    rw [mem_ball, Lemma71O.dist_ofReal_ofReal, Real.dist_eq]; exact hz
  have hεr' : ε ≤ r := hεr
  -- the wall side fixes the corner integer to `0`
  have hnc : nc = 0 := by
    set z₁ := x₀ - ε / 2 with hz₁
    have hz₁x : z₁ < x₀ := by linarith
    have hz₁δ : x₀ - δ₁ < z₁ := by
      linarith [min_le_left r₀ δ₂, min_le_left δ₁ (x₁ - x₀)]
    obtain ⟨s, hsq, hℓs, hsγ⟩ := hwall z₁ hz₁x hz₁δ
    have hland : Tendsto ct.2.1 (𝓝[H] (z₁ : ℂ)) (𝓝 (β s)) := by rw [← hℓs]; exact hℓT z₁
    obtain ⟨ρ, hρ, hρK⟩ := Lemma613.exists_ball_notMem (isCompact_Icc.image hS.seg.hγ.1) hsγ
    have hloc : Γ ∩ ball (β s) ρ ⊆ β '' Icc 0 q₁ := by
      rintro z ⟨hzΓ | hzΓ, hzb⟩
      · exact hzΓ
      · exact absurd hzb (hρK z hzΓ)
    have hCq₁ : D ⊆ H \ fwdHull (fun r : ℝ => Wβ r.toNNReal) q₁ := fun z hz =>
      Lemma71O.subset_H_diff_fwdHull_left hF htrβ q₁ (hS.mem_of_mem_dom hz).1
    obtain ⟨vβ, hvβ, hTβ⟩ := Lemma71O.exists_real_tendsto_wall htrβ hWβ hWβ0 hS.hc' hCq₁
      (mem_Hbar_of_im_eq_zero (by simp)) hsq.le hland
    have hA := Lemma71O.tendsto_lift_sub_of_agree_chart hΓc hKΓ hgK hLK hS.hc' hDΓ hland hρ htrβ hWβ hWβ0
      hF.hβ.2.1 hq₁0 subset_union_left hloc hvβ hTβ
    have hB := hS.tendsto_wall_branch htrβ htrα hLte hz₁x hsq hℓs
    have hC := hint (z₁ : ℂ) (hball' z₁ (by rw [hz₁, abs_lt]; constructor <;> linarith)) (by simp)
    have hD' := hA.sub hB
    rw [sub_zero] at hD'
    have := Lemma71O.nhdsWithin_H_ofReal_neBot z₁
    have heq : 2 * π * (nc : ℝ) = 0 :=
      tendsto_nhds_unique hC (hD'.congr fun y => by simp only [Complex.sub_im]; ring)
    have hpi : (2 * π : ℝ) ≠ 0 := by positivity
    exact_mod_cast (mul_eq_zero.1 heq).resolve_left hpi
  -- a middle point near the junction landing inside the pocket
  set ε'' := min ε (x₁ - x₀) with hε''
  have hε''0 : 0 < ε'' := lt_min hε (by linarith)
  have hηi : InjOn η (Icc 0 (t : ℝ)) := fun s hs s' hs' h => by
    rw [hS.hηe s hs.1 hs.2, hS.hηe s' hs'.1 hs'.2] at h
    exact injOn_capInv hS.seg.seg hS.ht hs hs' h
  have hηint : ∀ a b : ℝ, a < b → Ioo a b ⊆ Icc 0 (t : ℝ) → ∃ u ∈ Ioo a b, (η u).im ≠ 0 := fun a b hab hI => by
    obtain ⟨u, hu, hne⟩ := exists_im_ne_zero hS.seg.seg hS.ht hab hI
    exact ⟨u, hu, by rw [hS.hηe u (hI hu).1 (hI hu).2]; exact hne⟩
  obtain ⟨z₂, hz₂, hz₂H⟩ := exists_mem_H_of_lt hS.hη hS.hW hS.hW0 ht0 hηi hηint
    (show x₀ < x₀ + ε'' by linarith) fun z hz =>
      mem_image_of_mid hS.hη hS.hW hS.hW0 ht0 hz.1
        (hmid z ⟨hz.1, by linarith [hz.2, min_le_right ε (x₁ - x₀)]⟩).1
  have hz₂₁ : z₂ < x₁ := by linarith [hz₂.2, min_le_right ε (x₁ - x₀)]
  obtain ⟨σ, hσ, hTσ, hℓσ⟩ := hgam z₂ hz₂.1 hz₂₁
  have hσC : γ σ ∈ C := by
    rw [← hℓσ]
    show land c (extendFrom H (fwdMapInv W t) z₂) ∈ C
    rw [show land c (extendFrom H (fwdMapInv W t) z₂) = c.2.1 (extendFrom H (fwdMapInv W t) z₂) from
      extendFrom_extends hF.hc.1.continuousOn _ hz₂H, ← hF.hdom]
    exact hF.hc.inv_mem_dom hz₂H
  have hσβ : γ σ ∉ β '' Icc 0 q₁ := by
    rintro ⟨u, -, hu⟩
    exact (hF.subset_sides hσC).2.1.2 ⟨u, hu⟩
  obtain ⟨ρ, hρ, hρK⟩ := Lemma613.exists_ball_notMem (isCompact_Icc.image hF.hβ.1) hσβ
  have hloc : Γ ∩ ball (γ σ) ρ ⊆ γ '' Icc 0 T' := by
    rintro z ⟨hzΓ | hzΓ, hzb⟩
    · exact absurd hzb (hρK z hzΓ)
    · exact hzΓ
  have hCT := hS.subset_H_diff_fwdHull htrγ le_rfl
  obtain ⟨vγ, hvγ, hTγ⟩ := Lemma71O.exists_real_tendsto_wall htrγ hWγ hWγ0 hS.hc' hCT
    (mem_Hbar_of_im_eq_zero (by simp)) hσ.le hTσ
  have hT'0 : 0 < T' := lt_of_le_of_lt (zero_le (a := σ)) hσ
  have hA := Lemma71O.tendsto_lift_sub_of_agree_chart hΓc hKΓ hgK hLK hS.hc' hDΓ hTσ hρ htrγ hWγ hWγ0
    hS.seg.hγ.2.1 hT'0 subset_union_right hloc hvγ hTγ
  have hC := hint (z₂ : ℂ) (hball' z₂ (by
    rw [abs_lt]; constructor <;> linarith [hz₂.1, hz₂.2, min_le_left ε (x₁ - x₀)])) (by simp)
  rw [hnc, Int.cast_zero, mul_zero] at hC
  refine ⟨z₂, ⟨hz₂.1, hz₂₁⟩, ?_⟩
  have h := hC.sub hA
  rw [sub_zero] at h
  show Tendsto (fun y => (logDerivFwd (fun r : ℝ => Wγ r.toNNReal) T' (ct.2.1 y) - Lt (ct.2.1 y)).im)
    (𝓝[H] (z₂ : ℂ)) (𝓝 (2 * π * ((0 : ℤ) : ℝ)))
  rw [Int.cast_zero, mul_zero]
  refine h.congr fun y => ?_
  simp only [Complex.sub_im]
  ring

end IsTSetting

end InteractingSLE.Sec7.Lemma71P
