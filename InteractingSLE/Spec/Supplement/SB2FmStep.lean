/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2FmComp
import InteractingSLE.Spec.Supplement.SB2LwStop
import InteractingSLE.Spec.Supplement.SB2WeOrig
import InteractingSLE.Spec.Supplement.GW1ActiveWord
import InteractingSLE.Spec.Supplement.SB2QwStep
import InteractingSLE.Spec.Supplement.SB2FmWord

/-!
# D34's clause, step (L): the left heights through one step of F3's induction (one sample)

Worker PROVE-SB2-F3LAW (round 2, target 3, handoff §R2.7). At stage `ℓ` the word `β` (chart `Mo.hullChart K 0`, `K`
free right of the seed `p`) is admissible left of the entry `entry K p` and original right of it; the relative piece
(record `r`, driver `W`, lifetime `T`) is launched at the offset `x₀ ≤ entry K p`. The step word is the stop word
recentred by `x₀ + W_T` (`Qw.stepWord`'s form). If the piece's right side is swallowed (`markPos W T 0 = 0`) and the
free points of the stepped hull between the two seeds have admissible original heights, the step word is admissible
left of the entry of the stepped hull at the next seed `p'`:

* left of the tip: `leftAdm_stopWord`, `leftAdm_shiftW`;
* right of the tip: the stop word's heights are the old word's at alive points (`Lh.exists_alive_eq_of_markPos_lt`,
  `GW1W.stopWord_fn_fwdMap`); left of the old entry they are admissible, right of it they are original heights at
  free points `x > p` whose boundary value in the stepped hull is the point itself (`bdryVal_stepHull`,
  `bdryVal_fwdHull_of_alive`), hence `x < p'`;
* finitely many exceptional points are avoided by the local constancy of words.

Helpers: `bddBelow_bdryVal`, `entry_le_bdryVal`, `entry_le_bdryVal_self`, `exists_bdryVal_eq`, `free_stepHull`,
`endV_eq_rdrv`. Main: **`leftAdm_entry_step`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H fwdMap fwdHull IsForwardSol chiC)

namespace InteractingSLE.Theorem14.SB.Fm

open Restart Sec7 Exist Exist.StagedLaw Exist.Staged

theorem bddBelow_bdryVal {A : Set ℂ} (hA : IsHPHull A) {p : ℝ} (hp : FreeRight A p) :
    BddBelow (bdryVal A '' Ioi p) := by
  obtain ⟨M, hM⟩ := (ConformalImage.isMapOut_mapOut hA).exists_norm_sub_le hA
  refine ⟨p - M, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨r, hr, hd⟩ := hp x hx
  have h1 := abs_bdryVal_sub_le hA hM hr hd
  have h2 := neg_abs_le (bdryVal A x - x)
  have hx' : p < x := hx
  linarith

theorem entry_le_bdryVal {A : Set ℂ} (hA : IsHPHull A) {p : ℝ} (hp : FreeRight A p) {x : ℝ} (hx : p < x) :
    entry A p ≤ bdryVal A x :=
  csInf_le (bddBelow_bdryVal hA hp) ⟨x, hx, rfl⟩

/-- At a free point `p` itself, the entry is at most the boundary value. -/
theorem entry_le_bdryVal_self {A : Set ℂ} (hA : IsHPHull A) {p : ℝ} (hp : FreeRight A p) {r : ℝ} (hr : 0 < r)
    (hd : Disjoint (ball (p : ℂ) r) A) : entry A p ≤ bdryVal A p := by
  obtain ⟨d, -, hD⟩ := hasDerivAt_bdryVal hA hr hd
  have hT : Tendsto (bdryVal A) (𝓝[>] p) (𝓝 (bdryVal A p)) :=
    hD.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto hT (Eventually.mono self_mem_nhdsWithin fun x hx => entry_le_bdryVal hA hp hx)

/-- **Every value past the entry is a boundary value of the free ray.** -/
theorem exists_bdryVal_eq {A : Set ℂ} (hA : IsHPHull A) {p : ℝ} (hp : FreeRight A p) {y : ℝ} (hy : entry A p < y) :
    ∃ x, p < x ∧ bdryVal A x = y := by
  obtain ⟨M, hM⟩ := (ConformalImage.isMapOut_mapOut hA).exists_norm_sub_le hA
  have hcont := continuousOn_bdryVal hA hp
  have hne : (bdryVal A '' Ioi p).Nonempty := ⟨bdryVal A (p + 1), p + 1, by simp, rfl⟩
  obtain ⟨_, ⟨x₁, hx₁, rfl⟩, hx₁y⟩ := exists_lt_of_csInf_lt hne hy
  set x₂ := max x₁ (y + M + 1) with hx₂
  have hx₁₂ : x₁ ≤ x₂ := le_max_left _ _
  have hx₂p : x₂ ∈ Ioi p := lt_of_lt_of_le hx₁ hx₁₂
  have hFx₂ : y ≤ bdryVal A x₂ := by
    obtain ⟨r, hr, hd⟩ := hp x₂ hx₂p
    have h1 := abs_bdryVal_sub_le hA hM hr hd
    have h2 := neg_abs_le (bdryVal A x₂ - x₂)
    have : y + M + 1 ≤ x₂ := le_max_right _ _
    linarith
  have hsub : Icc x₁ x₂ ⊆ Ioi p := fun t ht => lt_of_lt_of_le hx₁ ht.1
  obtain ⟨x, hx, hFx⟩ := intermediate_value_Icc hx₁₂ (hcont.mono hsub) ⟨hx₁y.le, hFx₂⟩
  exact ⟨x, hsub hx, hFx⟩

/-- **A free point whose image is alive stays free after the step.** -/
theorem free_stepHull {K : Set ℂ} (hK : IsHPHull K) (x₀ : ℝ) {W : ℝ → ℝ} (hW : Continuous W) {T : ℝ}
    (hT : 0 ≤ T) {x r : ℝ} (hr : 0 < r) (hd : Disjoint (ball (x : ℂ) r) K)
    (hal : ∃ u, IsForwardSol W ((bdryVal K x - x₀ : ℝ) : ℂ) T u) :
    ∃ ρ > 0, Disjoint (ball (x : ℂ) ρ) (Qw.stepHull K x₀ W T) := by
  obtain ⟨u, hu⟩ := hal
  have hcl := Supp8.RelTrans.notMem_closure_fwdHull_of_isForwardSol hW hT hu
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isClosed_closure.isOpen_compl _ hcl
  have hc := Mo.isConformal_hullChart hK x₀
  have hT1 : Tendsto (fun z => ConformalImage.mapOut K z - (x₀ : ℂ)) (𝓝[H] (x : ℂ))
      (𝓝 ((bdryVal K x - x₀ : ℝ) : ℂ)) := by
    have h := (tendsto_mapOut_bdryVal hK hr hd).sub_const (x₀ : ℂ)
    convert h using 2; push_cast; ring
  obtain ⟨δ, hδ, hδc⟩ := Metric.tendsto_nhdsWithin_nhds.1 hT1 ε hε
  refine ⟨min δ r, lt_min hδ hr, Set.disjoint_left.2 fun z hz hzA => ?_⟩
  have hzr : z ∈ ball (x : ℂ) r := ball_subset_ball (min_le_right _ _) hz
  rcases hzA with hzK | ⟨w, hwJ, rfl⟩
  · exact Set.disjoint_left.1 hd hzr hzK
  · have hwH : w ∈ H := (isHPHull_fwdHull hW hT).1 hwJ
    have hzH : (Mo.hullChart K x₀).2.1 w ∈ H := hc.dom_subset (hc.inv_mem_dom hwH)
    have h1 := hδc hzH (lt_of_lt_of_le hz (min_le_left _ _))
    have h2 : (Mo.hullChart K x₀).1 ((Mo.hullChart K x₀).2.1 w) = w := hc.2.2 w hwH
    rw [Mo.hullChart_fwd] at h2
    rw [h2] at h1
    exact hball h1 (subset_closure hwJ)

theorem endV_eq_rdrv (r : RecData) : Qw.endV r = rdrv r (rtime r) := by
  unfold Qw.endV rdrv
  rw [← histTime_recHist, Real.toNNReal_coe]

/-- **The left heights pass through a step of F3's induction (one sample).** Stage `ℓ`: hull `K` free right of the
seed `p`, word `β` admissible left of the entry and original right of it, chart offset `x₀ ≤ entry`. Step: record `r`
of the relative piece whose right side is swallowed (`markPos 0 = 0`), stepped hull `K' = Qw.stepHull K x₀ W T` free
right of the next seed `p'`, and admissible original heights at the free points of `K'` between the two seeds. Then
the step word (the stop word recentred by `x₀ + W_T`, as `Qw.stepWord`) is admissible left of the entry of `K'` at
`p'`. -/
theorem leftAdm_entry_step {κ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ} {jumps : Finset ℝ} {K : Set ℂ} (hK : IsHPHull K)
    {p : ℝ} (hp : FreeRight K p) {x₀ : ℝ} (hx₀ : x₀ ≤ entry K p) {β : BoundaryWord}
    (hL : LeftAdm κ β (entry K p))
    (hread : ∀ x, p < x → x ∉ jumps → bdryVal K x ∉ β.jumps → β.fn (bdryVal K x) = b x)
    (r : RecData) (h0 : markPos (rdrv r) (rtime r) 0 = 0)
    {p' : ℝ} (hp' : FreeRight (Qw.stepHull K x₀ (rdrv r) (rtime r)) p')
    (hlow : ∀ x, p < x → x < p' → (∃ ρ > 0, Disjoint (ball (x : ℂ) ρ) (Qw.stepHull K x₀ (rdrv r) (rtime r))) →
      x ∉ jumps → b x + -(Real.pi / 2) * chiC κ < sleLambda κ) :
    LeftAdm κ (BoundaryWord.shiftW (-(x₀ + Qw.endV r)) (stopWord κ (BoundaryWord.shiftW x₀ β, -(Real.pi / 2), r)))
      (entry (Qw.stepHull K x₀ (rdrv r) (rtime r)) p') := by
  classical
  set W := rdrv r with hWdef
  set T := rtime r with hTdef
  have hW : Continuous W := continuous_rdrv r
  have hW0 : W 0 = 0 := rdrv_zero r
  have hT : 0 ≤ T := rtime_nonneg r
  set A' := Qw.stepHull K x₀ W T with hA'def
  have hA' : IsHPHull A' := Qw.isHPHull_stepHull hK x₀ hW hW0 hT
  set c := BoundaryWord.shiftW x₀ β with hc
  set γ := stopWord κ (c, -(Real.pi / 2), r) with hγ
  have hend : Qw.endV r = W T := endV_eq_rdrv r
  set tip := x₀ + W T with htip
  set β' := BoundaryWord.shiftW (-(x₀ + Qw.endV r)) γ with hβ'
  have hfn' : ∀ y, β'.fn y = γ.fn (y - tip) := fun y => by
    rw [hβ', BoundaryWord.fn_shiftW, hend]; congr 1
  have hjump' : ∀ y, y - tip ∈ γ.jumps → y ∈ β'.jumps := fun y h => by
    rw [hβ', BoundaryWord.jumps_shiftW, hend]
    exact Finset.mem_image.2 ⟨y - tip, h, by ring⟩
  have hfnc : ∀ y, c.fn y = β.fn (y + x₀) := fun y => BoundaryWord.fn_shiftW _ _ _
  have hjc : ∀ y, y + x₀ ∈ β.jumps → y ∈ c.jumps := fun y h => by
    rw [hc, BoundaryWord.jumps_shiftW]
    exact Finset.mem_image.2 ⟨y + x₀, h, by ring⟩
  -- left of the tip
  have hLtip : LeftAdm κ β' tip := by
    have h1 : LeftAdm κ β x₀ := fun y hy hyJ => hL y (lt_of_lt_of_le hy hx₀) hyJ
    have h2 : LeftAdm κ c 0 := by have := leftAdm_shiftW h1 x₀; rwa [sub_self] at this
    have h3 : LeftAdm κ β' (0 - -(x₀ + Qw.endV r)) := leftAdm_shiftW (leftAdm_stopWord hκ h2 r) (-(x₀ + Qw.endV r))
    have e : (0 : ℝ) - -(x₀ + Qw.endV r) = tip := by rw [hend]; ring
    rw [e] at h3
    exact h3
  -- the bad finite set
  set φ : ℝ → ℝ := fun t => (fwdMap W T (t : ℂ)).re + tip with hφ
  set F : Finset ℝ := β'.jumps ∪ c.jumps.image φ ∪ {φ (entry K p - x₀), tip} ∪ jumps.image (bdryVal A') with hF
  have hmono := GW1W.strictMonoOn_re_fwdMap_alive hW hW0 hT
  -- generic points
  have hgen : ∀ y, y < entry A' p' → y ∉ F → β'.fn y + -(Real.pi / 2) * chiC κ < sleLambda κ := by
    intro y hy hyF
    have hyJ : y ∉ β'.jumps := fun h => hyF (by simp [hF, h])
    rcases lt_or_ge y tip with hlt | hge
    · exact hLtip y hlt hyJ
    rcases eq_or_lt_of_le hge with heq | hgt
    · exact absurd (by rw [hF]; simp [heq]) hyF
    obtain ⟨y₀, hy₀, hal, hφy⟩ := Lh.exists_alive_eq_of_markPos_lt hW hW0 hT (y := y - tip) (by rw [h0]; linarith)
    have hyφ : y = φ y₀ := by simp only [hφ]; linarith
    have hy₀c : y₀ ∉ c.jumps := fun h => hyF (by
      rw [hF, hyφ]
      exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_right _ (Finset.mem_image_of_mem φ h))))
    have hγJ : (fwdMap W T (y₀ : ℂ)).re ∉ γ.jumps := fun h => hyJ (hjump' y (by rw [← hφy]; exact h))
    have hfn := GW1W.stopWord_fn_fwdMap hκ c (-(Real.pi / 2)) r hy₀ hal hy₀c hγJ
    rw [hfn' y, show y - tip = (fwdMap W T (y₀ : ℂ)).re by linarith, hfn, hfnc y₀]
    have hzJ : y₀ + x₀ ∉ β.jumps := fun h => hy₀c (hjc y₀ h)
    rcases lt_trichotomy (y₀ + x₀) (entry K p) with hlt | heq | hgt'
    · exact hL _ hlt hzJ
    · exfalso
      have : y = φ (entry K p - x₀) := by rw [hyφ, ← heq, add_sub_cancel_right]
      exact hyF (by rw [hF, this]; simp)
    obtain ⟨x, hpx, hbx⟩ := exists_bdryVal_eq hK hp hgt'
    have hy₀eq : bdryVal K x - x₀ = y₀ := by linarith
    have halx : ∃ u, IsForwardSol W ((bdryVal K x - x₀ : ℝ) : ℂ) T u := by rw [hy₀eq]; exact hal
    obtain ⟨rx, hrx, hdx⟩ := hp x hpx
    obtain ⟨ρ, hρ, hdρ⟩ := free_stepHull hK x₀ hW hT hrx hdx halx
    obtain ⟨-, hbv⟩ := bdryVal_stepHull hK x₀ hW hW0 hT hρ hdρ
    obtain ⟨-, hJv⟩ := bdryVal_fwdHull_of_alive hW hW0 hT hal
    have hyx : bdryVal A' x = y := by
      rw [hA'def, hbv, hy₀eq, hJv]
      have : (fwdMap W T (y₀ : ℂ)).re = y - tip := by linarith
      rw [this, htip]; ring
    have hxp' : x < p' := by
      by_contra hge'
      rcases eq_or_lt_of_le (not_lt.1 hge') with h | h
      · have := entry_le_bdryVal_self hA' hp' hρ (by rw [h]; exact hdρ)
        rw [show bdryVal A' p' = y by rw [h]; exact hyx] at this
        linarith
      · have := entry_le_bdryVal hA' hp' h
        rw [hyx] at this
        linarith
    have hxJ : x ∉ jumps := fun h => hyF (by
      rw [hF, ← hyx]
      exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ h))
    rw [← hbx, hread x hpx hxJ (by rw [hbx]; exact hzJ)]
    exact hlow x hpx hxp' ⟨ρ, hρ, hdρ⟩ hxJ
  -- every point: move to a nearby generic point with the same height
  intro y hy hyJ
  obtain ⟨δ, hδ, hδb⟩ := Metric.eventually_nhds_iff.1 (β'.isPiecewiseConstantBoundaryData y hyJ)
  obtain ⟨y'', ⟨hy1, hy2⟩, hyF⟩ := ((Set.Ioo_infinite (show y - δ < y by linarith)).sdiff
    F.finite_toSet).nonempty
  have he : β'.fn y'' = β'.fn y := hδb (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
  rw [← he]
  exact hgen y'' (by linarith) hyF

end InteractingSLE.Theorem14.SB.Fm
