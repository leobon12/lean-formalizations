/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SdsCw
import InteractingSLE.Spec.Supplement.GW2WmPos
import InteractingSLE.Spec.Supplement.GW2CvCover
import InteractingSLE.Spec.Sec4.Prob41Flow

/-!
# The near structure (N3), step G: the root word's side forms at a lower-arc root (GW2.1)

Packet PROVE-GW2-SDE (round 18). At a root `x > 0` untouched by the counterflow at time `s`, the root word
`GW2Wm.rootWordX κ c′ x s r` is the joint word re-centred at the root's image `baseRead = −1/markPosL(−1/x)`. Its
heights just left of the tip, on `(−baseRead, 0)`, are returned heights of the counterflow word left of `−1/x`; for the
source counterflow word `c′ = counterflowData κ b` they return to the source heights `b(y₀)`, `y₀ ∈ (0, x)`
(`returnData ∘ inverseData = id` with `retA + specOffset = cfOffset = −πχ`):

* **`rootWordX_fn_seed`** (deterministic);
* **`rootForms_lowerArc`**: at a lower-arc root (no jump in `(0, x]`, `b(0⁺) − πχ/2 ≤ −λ`, ROOT2's `RootSeedOK`) the
  root word's left heights are left forms (the seed height `b(0⁺) < πχ + λ′`, and the joint word's left heights) and its
  right heights are right forms (the joint word's right heights).

A height is a left form `−λ′(1 + S) + πχ` with `S > −2` iff it is `< πχ + λ′` (`isLeftForm_of_lt`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Finset MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (chiC fwdMap)

universe u

namespace InteractingSLE.Theorem14.GW2Sds

open Restart Exist.Staged Exist.StagedLaw GW2TipSystem.RootC24 GW2TipSystem.RootH10 Sec7.StripSysField
  GW2JointKernel

/-- **A height below `πχ + λ′` is a left form** `−λ′(1 + S) + πχ` with `S > −2`. -/
theorem isLeftForm_of_lt {κ : ℝ} (hκ : 0 < κ) {h : ℝ} (hh : h < Real.pi * chiC κ + sleLambda (16 / κ)) :
    ∃ S : ℝ, -2 < S ∧ h = -sleLambda (16 / κ) * (1 + S) + Real.pi * chiC κ := by
  have hl : 0 < sleLambda (16 / κ) := by unfold sleLambda; positivity
  refine ⟨(Real.pi * chiC κ - h) / sleLambda (16 / κ) - 1, ?_, ?_⟩
  · have : -1 < (Real.pi * chiC κ - h) / sleLambda (16 / κ) := by
      rw [lt_div_iff₀ hl]; linarith
    linarith
  · field_simp
    ring

/-- The counterflow data left of `0` returns the source data: `counterflowData κ b y = −b(−1/y) + cfOffset κ`. -/
theorem counterflowData_of_neg (κ : ℝ) (b : ℝ → ℝ) {y : ℝ} (hy : y < 0) :
    counterflowData κ b y = -b (-y⁻¹) + cfOffset κ := by
  simp only [counterflowData, inverseData, returnData, liftBoundary, hy, ↓reduceIte]
  ring

/-- **The root word's heights just left of the tip at an untouched positive root** are source heights `b(y₀)`,
`y₀ ∈ (0, x)`, for a counterflow word of the explicit counterflow data. -/
theorem rootWordX_fn_seed {κ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ} {J : Finset ℝ} {c' : BoundaryWord}
    (hc'J : c'.jumps = counterflowJumps J) (hc' : ∀ y ∉ counterflowJumps J, c'.fn y = counterflowData κ b y)
    {x : ℝ} (hx : 0 < x) {s : ℝ≥0} {r : RecData} (hr : rtime r = s)
    (hxA : (x : ℂ) ∉ closure (Supp8.Q3Rel.invHull (rdrv r) s))
    {y : ℝ} (hy0 : y < 0) (hyJ : y ∉ (GW2Wm.rootWordX κ c' x s r).jumps) (hyb : -GW2Rz.baseRead x s r < y) :
    ∃ y₀, 0 < y₀ ∧ y₀ < x ∧ (GW2Wm.rootWordX κ c' x s r).fn y = b y₀ := by
  classical
  set U := rdrv r with hU
  have hUc : Continuous U := continuous_rdrv r
  have hU0 : U 0 = 0 := rdrv_zero r
  have hT : 0 ≤ rtime r := rtime_nonneg r
  have hxA' : (x : ℂ) ∉ closure (Supp8.Q3Rel.invHull U (rtime r)) := by rw [hr]; exact hxA
  set m := markPosL U (rtime r) (-x⁻¹) with hm
  -- the root's image is `−1/m`
  have hbase : GW2Rz.baseRead x s r = -m⁻¹ := by
    rw [GW2Wm.baseRead_eq_rootOff x s r hr hxA, GW2Wm.rootOff_eq_relBdry x r hxA',
      ← GW2Wm.labelL_eq_relBdry hUc hU0 hT hx hxA']
    rfl
  have hm0 : m ≤ 0 := Sec7.StripDet.markPosL_nonpos hUc hU0 hT (by have := inv_pos.2 hx; linarith)
  have hmlt : m < 0 := by
    rcases hm0.lt_or_eq with h | h
    · exact h
    · exfalso
      rw [hbase, h, inv_zero, neg_zero, neg_zero] at hyb
      exact absurd hyb (not_lt.2 hy0.le)
  rw [hbase] at hyb
  set y' := y + -m⁻¹ with hy'
  have hy'0 : 0 < y' := by rw [hy']; linarith
  have hy'm : y' < -m⁻¹ := by rw [hy']; linarith
  -- the point read in the counterflow chart lies left of the image of `−1/x`
  set z := -y'⁻¹ with hz
  have hz0 : z < 0 := neg_neg_of_pos (inv_pos.2 hy'0)
  have hzm : z < m := by
    have h1 : -m < y'⁻¹ := by
      have hpos : 0 < -m⁻¹ := neg_pos.2 (inv_lt_zero.2 hmlt)
      have := (inv_lt_inv₀ hpos hy'0).2 hy'm
      rwa [inv_neg, inv_inv] at this
    rw [hz]; linarith
  -- the root word is the joint word re-centred
  set g := stopWord (16 / κ) (c', 0, r) with hg
  have hgs : g.IsSorted := isSorted_stopWord _ _
  have hy'J : y' ∉ (jointWordOfRec (specOffset κ) κ c' r).jumps := by
    intro hmem
    apply hyJ
    unfold GW2Wm.rootWordX
    rw [Exist.StagedLaw.BoundaryWord.jumps_shiftW, hbase]
    exact Finset.mem_image.2 ⟨y', hmem, by rw [hy']; ring⟩
  have hfn : (GW2Wm.rootWordX κ c' x s r).fn y = (jointWordOfRec (specOffset κ) κ c' r).fn y' := by
    unfold GW2Wm.rootWordX
    rw [Exist.StagedLaw.BoundaryWord.fn_shiftW, hbase]
  have hret : (jointWordOfRec (specOffset κ) κ c' r).fn y' =
      returnData (retA κ + specOffset κ) (retL κ) g.fn y' := by
    unfold jointWordOfRec at hy'J ⊢
    exact fn_retWord hgs _ _ hy'J
  have hzJ : z ∉ g.jumps := by
    intro hmem
    apply hy'J
    unfold jointWordOfRec
    rw [jumps_retWord hgs]
    refine Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨z, hmem, ?_⟩)
    rw [hz, inv_neg, inv_inv, neg_neg]
  -- the counterflow word's height there
  have hk : 0 < 16 / κ := by positivity
  obtain ⟨y₁, hy₁, hy₁J, hgy⟩ := (GW2Sdp.fn_stopWord_left hk c' 0 r
    (by have := inv_pos.2 hx; linarith : -x⁻¹ ≤ 0) hz0 hzJ).2 hzm
  have hy₁0 : y₁ < 0 := hy₁.trans (by have := inv_pos.2 hx; linarith)
  have hc'y : c'.fn y₁ = -b (-y₁⁻¹) + cfOffset κ := by
    rw [hc' y₁ (by rw [← hc'J]; exact hy₁J), counterflowData_of_neg κ b hy₁0]
  refine ⟨-y₁⁻¹, neg_pos.2 (inv_lt_zero.2 hy₁0), ?_, ?_⟩
  · have h1 : x⁻¹ < -y₁ := by linarith
    have h2 := (inv_lt_inv₀ (by linarith) (inv_pos.2 hx)).2 h1
    rw [inv_inv] at h2
    simpa only [inv_neg] using h2
  · rw [hfn, hret]
    simp only [returnData, liftBoundary, not_lt.2 hy'0.le, ↓reduceIte, mul_zero, add_zero]
    rw [← hz, hgy, hc'y, retA_add_specOffset hκ]
    simp only [cfOffset]
    ring

/-- **The root's image at an untouched positive root**: `baseRead x s r = −1/markPosL(−1/x) ≥ 0`. -/
theorem baseRead_nonneg_of_pos {x : ℝ} (hx : 0 < x) {s : ℝ≥0} {r : RecData} (hr : rtime r = s)
    (hxA : (x : ℂ) ∉ closure (Supp8.Q3Rel.invHull (rdrv r) s)) : 0 ≤ GW2Rz.baseRead x s r := by
  have hUc : Continuous (rdrv r) := continuous_rdrv r
  have hU0 : rdrv r 0 = 0 := rdrv_zero r
  have hT : 0 ≤ rtime r := rtime_nonneg r
  have hxA' : (x : ℂ) ∉ closure (Supp8.Q3Rel.invHull (rdrv r) (rtime r)) := by rw [hr]; exact hxA
  have hbase : GW2Rz.baseRead x s r = -(markPosL (rdrv r) (rtime r) (-x⁻¹))⁻¹ := by
    rw [GW2Wm.baseRead_eq_rootOff x s r hr hxA, GW2Wm.rootOff_eq_relBdry x r hxA',
      ← GW2Wm.labelL_eq_relBdry hUc hU0 hT hx hxA']
    rfl
  have hm0 : markPosL (rdrv r) (rtime r) (-x⁻¹) ≤ 0 :=
    Sec7.StripDet.markPosL_nonpos hUc hU0 hT (by have := inv_pos.2 hx; linarith)
  rw [hbase]
  exact neg_nonneg.2 (inv_nonpos.2 hm0)

variable {Ω : Type u} [MeasurableSpace Ω]

/-- **The side forms of the root word at a lower-arc root** (Lemma GW2.1's seed): for the source counterflow word, at
an untouched root `x > 0` with no jump of `b` in `(0, x]` and `b(0⁺) − πχ/2 ≤ −λ`, the root word's left heights are
left forms and its right heights are right forms. -/
theorem rootForms_lowerArc (c : SourceData Ω) {x : ℝ} (hx : 0 < x) (hJ : ∀ y ∈ c.jumps, y ∉ Ioc 0 x)
    (hseed : PiecewiseConstantBoundaryData.rightLim c.b 0 + -(Real.pi / 2) * chiC c.κ ≤ -sleLambda c.κ)
    (r : RecData) (hr : rtime r = c.s) (hxA : (x : ℂ) ∉ closure (Supp8.Q3Rel.invHull (rdrv r) c.s)) :
    (∀ h ∈ GW2Sdp.rootHeightsL (GW2Wm.rootWordX c.κ (cfWordSrc c) x c.s r), h ∈ oldLeftHeights c.κ ∨
      ∃ S : ℝ, -2 < S ∧ h = -sleLambda (16 / c.κ) * (1 + S) + Real.pi * chiC c.κ) ∧
    (∀ h ∈ GW2Sdp.rootHeightsR (GW2Wm.rootWordX c.κ (cfWordSrc c) x c.s r), h ∈ oldRightHeights c.κ ∨
      ∃ S : ℝ, -2 < S ∧ h = sleLambda (16 / c.κ) * (1 + S) - Real.pi * chiC c.κ) := by
  classical
  obtain ⟨hadmL, hadmR⟩ := cfWordSrc_admissible c
  set base := GW2Rz.baseRead x c.s r with hbase
  have hb0 : 0 ≤ base := baseRead_nonneg_of_pos hx hr hxA
  have hfn : ∀ y, (GW2Wm.rootWordX c.κ (cfWordSrc c) x c.s r).fn y =
      (jointWordOfRec (specOffset c.κ) c.κ (cfWordSrc c) r).fn (y + base) := fun y => by
    unfold GW2Wm.rootWordX
    rw [Exist.StagedLaw.BoundaryWord.fn_shiftW]
  have hjJ : ∀ y, y ∉ (GW2Wm.rootWordX c.κ (cfWordSrc c) x c.s r).jumps →
      y + base ∉ (jointWordOfRec (specOffset c.κ) c.κ (cfWordSrc c) r).jumps := fun y hyJ hmem => by
    apply hyJ
    unfold GW2Wm.rootWordX
    rw [Exist.StagedLaw.BoundaryWord.jumps_shiftW]
    exact Finset.mem_image.2 ⟨y + base, hmem, by ring⟩
  refine ⟨?_, ?_⟩
  · rintro _ ⟨y, hy, hyJ, rfl⟩
    rcases lt_trichotomy (y + base) 0 with hlt | heq | hgt
    · rw [hfn]
      exact Or.inr (GW2Sdp.jointWord_left_form c.hκ (cfWordSrc c) hadmR r hlt (hjJ y hyJ))
    · exfalso
      apply hjJ y hyJ
      rw [heq]
      unfold jointWordOfRec
      rw [jumps_retWord (isSorted_stopWord _ _)]
      exact Finset.mem_insert_self _ _
    · obtain ⟨y₀, hy₀, hy₀x, hval⟩ := rootWordX_fn_seed c.hκ (cfWordSrc_jumps c) (cfWordSrc_fn c) hx hr hxA hy hyJ
        (by linarith)
      rw [hval]
      have hJ' : ∀ z ∈ c.jumps, z ∉ Ioo 0 x := fun z hz hzI => hJ z hz ⟨hzI.1, hzI.2.le⟩
      have hlim : PiecewiseConstantBoundaryData.rightLim c.b 0 = c.b y₀ :=
        Sec4.rightLim_eq_of_forall hx fun t ht =>
          Sec4.eq_of_mem_Ioo_of_isPiecewiseConstant c.hb hJ' ⟨hy₀, hy₀x⟩ ht
      have hχ := Sec4.chiC_pos c.hκ c.hκ4
      have hl := Sec4.sleLambda_pos c.hκ
      have hl' := Sec4.sleLambda_pos (show (0 : ℝ) < 16 / c.κ by have := c.hκ; positivity)
      refine Or.inr (isLeftForm_of_lt c.hκ ?_)
      have hpi := Real.pi_pos
      nlinarith
  · rintro _ ⟨y, hy, hyJ, rfl⟩
    rw [hfn]
    exact Or.inr (GW2Sdp.jointWord_right_form c.hκ (cfWordSrc c) hadmL r (by linarith) (hjJ y hyJ))

end InteractingSLE.Theorem14.GW2Sds
