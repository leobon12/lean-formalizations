/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.GlueCondUnionImgLim
import InteractingSLE.Spec.Restart.RetAux79Zone
import InteractingSLE.Spec.Sec5.CrossCondWord

/-!
# G3 (ii), Proposition 4.9 direction: the union mean at the real points of the image chart off the image hull

Packet PROVE-GLUECOND8, item 1 (PROVE-GLUECOND6's "What remains" 1). Notation: the counterflow chart
`Ψ = revChart w s` of `ℍ ∖ G` (`G = R(K′_s)`), an image chain `W′` with a simple proper trace `η′` (the image of the
flow prefix under `Ψ`), image time `T`, `F′_T = fwdMapInv W′ T` and `Φ = Ψ⁻¹ ∘ F′_T`. At a real point `x` of the image
chart whose boundary value `r = F̄′_T(x)` is a real point `≠ 0` of the chart `Ψ` (the counterflow side, the physical
real line, and physical `∞`), the union mean read through `Φ` has the boundary value of the image word:

* **`tendsto_imgChart_of_real`** (deterministic): from PROVE-GLUECOND6's chart limit
  (`tendsto_add_argPsi_sub_of_real`), the boundary value of the bounded harmonic function `V` (the counterflow mean in
  the chart `Ψ`, `retMean`), Aux. 57 for `W′` at `r`, and a **data match** `d_I(x) = d_V(r) + c`:
  `M ∘ Φ + c − (u − χ (Im L′_T ∘ F′_T + arg_Ψ ∘ Φ)) → 0` at `x`;
* **the data transport** of the image word from time `T` to time `0` (`forceBoundaryData_imgChart_eq`): the force data
  of the flowed marks at `x` equal the force data of the initial marks at `r`;
* **the data match at time `0`** (`imgData0_eq_left`, `imgData0_eq_right`, `imgData0_eq_mid_neg`,
  `imgData0_eq_mid_pos`): the image word's data at a real chart point `r` equal the return data of the counterflow word
  at time `s` plus `πχ/2`, with the junction weights `κ − 4 − Σρ_L`, `κ/2 − 2 − Σρ_R` (PROVE-GLUECOND6's finding);
  on the physical real line it is the original data (no junction weight enters).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped NNReal Real

open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv logDerivFwd chiC)

namespace InteractingSLE.Sec5.GlueImg

open WangWu hiding ratPt exists_ratPt_dist_lt

/-! ### Real points of the image chart -/

section ImgReal

variable {W' : ℝ → ℝ} {η' : ℝ → ℂ} {T : ℝ}

/-- At a real point `x` of the image chart with real boundary value `r`, `F′_T → r` within `ℍ`. -/
theorem tendsto_fwdMapInv_nhdsWithin_of_real (hη' : IsLoewnerTrace W' η') (hW' : Continuous W') (hW'0 : W' 0 = 0)
    (hT : 0 ≤ T) {x r : ℝ} (hF : extendFrom H (fwdMapInv W' T) x = r) :
    Tendsto (fwdMapInv W' T) (𝓝[H] (x : ℂ)) (𝓝[H] (r : ℂ)) := by
  have hxH : (x : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (x : ℂ).im by simp
  refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun y hy =>
    QuantumZipper.RS.fwdMapInv_mem_H hW' hW'0 hT hy⟩
  have := (hη'.hasBdryLimits hW' hW'0 hT).tendsto hxH
  rwa [hF] at this

/-- A real point `r ≠ 0` has a ball disjoint from the hull of a simple proper trace. -/
theorem exists_ball_disjoint_fwdHull_of_isProperArc (hη' : IsLoewnerTrace W' η') (hη'p : IsProperArc η')
    (hT : 0 ≤ T) {r : ℝ} (hr : r ≠ 0) : ∃ ρ > 0, Disjoint (ball (r : ℂ) ρ) (fwdHull W' T) := by
  have hK : fwdHull W' T ⊆ η' '' Icc 0 T := by
    rw [fwdHull_eq_image_Ioc hη' hη'p hT]
    exact image_mono Ioc_subset_Icc_self
  have hc : IsCompact (η' '' Icc 0 T) := isCompact_Icc.image_of_continuousOn (hη'p.cont.mono Icc_subset_Ici_self)
  have hr' : (r : ℂ) ∉ η' '' Icc 0 T := by
    rintro ⟨u, hu, he⟩
    rcases hu.1.eq_or_lt with h0 | hpos
    · rw [← h0, hη'p.zero] at he
      exact hr (by exact_mod_cast he.symm)
    · have := hη'p.mem_H u hpos
      rw [he] at this
      exact lt_irrefl _ (show (0 : ℝ) < (r : ℂ).im from this |>.trans_eq (by simp))
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hc.isClosed.isOpen_compl (r : ℂ) hr'
  exact ⟨ρ, hρ, Set.disjoint_left.2 fun z hz hzK => hball hz (hK hzK)⟩

end ImgReal

/-! ### The union mean at the real points of the image chart -/

section Limit

variable {w : ℝ → ℝ} {s : ℝ} {W' : ℝ → ℝ} {η' : ℝ → ℂ} {T : ℝ}

/-- **The union mean at a real point of the image chart with a real boundary value** (deterministic). In the setting
of `tendsto_add_argPsi_sub_of_real` (counterflow chart `Ψ = revChart w s`, `M − m_G → 0` at `G ∪ ℝ` away from `A` and at
`∞`, `m_G + χ arg_Ψ = V ∘ Ψ`), let `V` be a bounded harmonic extension of `d_V`, `W′` an image chain with a simple
proper trace, `u` a bounded harmonic extension of `d_I`, and `x` a real point of the image chart whose boundary value
`r = F̄′_T(x)` is real and `≠ 0`. If `r` is not exceptional for `V`, `x` not exceptional for `u`, and
`d_I(x) = d_V(r) + c`, then `M ∘ Φ + c − (u − χ (Im L′_T ∘ F′_T + arg_Ψ ∘ Φ)) → 0` at `x` (`Φ = Ψ⁻¹ ∘ F′_T`). -/
theorem tendsto_imgChart_of_real (hw : Continuous w) (hw0 : w 0 = 0) (hs : 0 ≤ s)
    (hB : HasBdryLimits (fwdMapInv w s)) {A : Set ℂ} (hAb : Bornology.IsBounded A)
    (hAcl : ∀ z ∈ closure A, z ∈ A ∨ z = 0) (hAG : Disjoint A (negInv '' fwdHull w s)) (hAH : A ⊆ H)
    {M mG V : ℂ → ℝ} {χ : ℝ}
    (hG : ∀ z₀ ∈ negInv '' fwdHull w s ∪ {z : ℂ | z.im = 0}, (∃ r > 0, A ∩ ball z₀ r ⊆ negInv '' fwdHull w s) →
      Tendsto (fun z => M z - mG z) (𝓝[H \ (A ∪ negInv '' fwdHull w s)] z₀) (𝓝 0))
    (hInf : Tendsto (fun z => M z - mG z) (Bornology.cobounded ℂ ⊓ 𝓟 (H \ (A ∪ negInv '' fwdHull w s))) (𝓝 0))
    (hId : ∀ z ∈ H \ negInv '' fwdHull w s, mG z + χ * (logDerivPsi w s z).im = V (revChart w s z))
    {dV : ℝ → ℝ} {SV : Set ℝ} (hV : IsBoundedHarmonicExtension dV SV V)
    (hW' : Continuous W') (hW'0 : W' 0 = 0) (hη' : IsLoewnerTrace W' η') (hη'p : IsProperArc η') (hT : 0 ≤ T)
    {dI : ℝ → ℝ} {SI : Set ℝ} {u : ℂ → ℝ} (hu : IsBoundedHarmonicExtension dI SI u)
    {x r c : ℝ} (hr : r ≠ 0) (hF : extendFrom H (fwdMapInv W' T) x = r) (hrV : r ∉ SV) (hxI : x ∉ SI)
    (hmatch : dI x = dV r + c) :
    Tendsto (fun y => M (revChartInv w s (fwdMapInv W' T y)) + c -
        (u y - χ * ((logDerivFwd W' T (fwdMapInv W' T y)).im +
          (logDerivPsi w s (revChartInv w s (fwdMapInv W' T y))).im))) (𝓝[H] (x : ℂ)) (𝓝 0) := by
  have h1 := tendsto_fwdMapInv_nhdsWithin_of_real hη' hW' hW'0 hT hF
  have h3 := (tendsto_add_argPsi_sub_of_real hw hw0 hs hB hAb hAcl hAG hAH hG hInf hId hr).comp h1
  have h4 := (hV.2.2 r hrV).comp h1
  obtain ⟨ρ, hρ, hd⟩ := exists_ball_disjoint_fwdHull_of_isProperArc hη' hη'p hT hr
  have h5 := (Restart.IsCanonicalDerivLog.tendsto_im_nhdsWithin_zero (isHPHull_fwdHull hW' hT)
    (Sec7.SideHeight.isCanonicalDerivLog_fwdMap hW' hW'0 hT) (isMapOut_fwdMap hW' hW'0 hT) hρ hd).comp h1
  have h6 := hu.2.2 x hxI
  have h := ((h3.add h4).add_const c).sub (h6.sub (h5.const_mul χ))
  have hval : (0 : ℝ) + dV r + c - (dI x - χ * 0) = 0 := by rw [hmatch]; ring
  rw [hval] at h
  refine h.congr fun y => ?_
  simp only [Function.comp_apply]
  ring

end Limit

/-! ### The data transport of the image word -/

section Transport

open MartChar.RealFlow Restart.RetAux79

variable {W' : ℝ → ℝ} {η' : ℝ → ℂ} {T : ℝ}

/-- For a driver all of whose positive points are alive, the image of `z ≥ 0` lies strictly left of the image of
any `x > z`. -/
theorem rightImg_lt_gImg_of_lt {w : ℝ → ℝ} (hw : Continuous w) {t : ℝ} (ht : 0 ≤ t)
    (hal : ∀ y, 0 < y → Alive w y t) {z x : ℝ} (hz : 0 ≤ z) (hzx : z < x) : rightImg w z t < gImg w x t := by
  have hm : 0 < (z + x) / 2 := by linarith
  have h1 := rightImg_le_gImg hw ht (show z < (z + x) / 2 by linarith) (hal _ hm)
  have h2 := gImg_lt_gImg hw ht (hal _ hm) (show (z + x) / 2 < x by linarith)
  linarith

/-- For a driver with a simple proper trace every positive point is alive. -/
theorem alive_of_isProperArc (hη' : IsLoewnerTrace W' η') (hη'p : IsProperArc η') (hW' : Continuous W')
    (hW'0 : W' 0 = 0) (hT : 0 ≤ T) : ∀ y, 0 < y → Alive W' y T := by
  intro y hy
  obtain ⟨v, hv⟩ := exists_isForwardSol_of_isProperArc hη' hη'p hW' hW'0 hy.ne' hT
  rcases isForwardSol_real_cases hW' hW'0 hT hv with ⟨_, h, _⟩ | ⟨h, _, _⟩
  · exact h
  · exact absurd h (not_lt.2 hy.le)

/-- For a driver with a simple proper trace every positive point is alive for the reflected driver. -/
theorem alive_neg_of_isProperArc (hη' : IsLoewnerTrace W' η') (hη'p : IsProperArc η') (hW' : Continuous W')
    (hW'0 : W' 0 = 0) (hT : 0 ≤ T) : ∀ y, 0 < y → Alive (fun s => -W' s) y T := by
  intro y hy
  obtain ⟨v, hv⟩ := exists_isForwardSol_of_isProperArc hη' hη'p hW' hW'0 (x := -y) (by linarith) hT
  rcases isForwardSol_real_cases hW' hW'0 hT hv with ⟨h, _, _⟩ | ⟨_, h, _⟩
  · exact absurd h (by linarith)
  · rwa [neg_neg] at h

/-- **The image-chart point of a positive real boundary value** is its real flow: `x = g′_T(r) − W′_T`. -/
theorem eq_gImg_of_extendFrom_pos (hη' : IsLoewnerTrace W' η') (hη'p : IsProperArc η') (hW' : Continuous W')
    (hW'0 : W' 0 = 0) (hT : 0 ≤ T) {x r : ℝ} (hr : 0 < r) (hF : extendFrom H (fwdMapInv W' T) x = r) :
    x = gImg W' r T - W' T := by
  obtain ⟨v, hv⟩ := exists_isForwardSol_of_isProperArc hη' hη'p hW' hW'0 hr.ne' hT
  have hxH : (x : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (x : ℂ).im by simp
  have h := eq_of_extendFrom_eq_of_isForwardSol hW' hW'0 hT hv hη' hxH hF
  rcases isForwardSol_real_cases hW' hW'0 hT hv with ⟨_, _, hvT⟩ | ⟨hneg, _, _⟩
  · rw [hvT] at h
    exact_mod_cast h
  · exact absurd hneg (not_lt.2 hr.le)

/-- **The image-chart point of a negative real boundary value**: `x = −g̃′_T(−r) − W′_T` (reflected driver). -/
theorem eq_neg_gImg_of_extendFrom_neg (hη' : IsLoewnerTrace W' η') (hη'p : IsProperArc η') (hW' : Continuous W')
    (hW'0 : W' 0 = 0) (hT : 0 ≤ T) {x r : ℝ} (hr : r < 0) (hF : extendFrom H (fwdMapInv W' T) x = r) :
    x = -gImg (fun s => -W' s) (-r) T - W' T := by
  obtain ⟨v, hv⟩ := exists_isForwardSol_of_isProperArc hη' hη'p hW' hW'0 hr.ne hT
  have hxH : (x : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (x : ℂ).im by simp
  have h := eq_of_extendFrom_eq_of_isForwardSol hW' hW'0 hT hv hη' hxH hF
  rcases isForwardSol_real_cases hW' hW'0 hT hv with ⟨hpos, _, _⟩ | ⟨_, _, hvT⟩
  · exact absurd hpos (not_lt.2 hr.le)
  · rw [hvT] at h
    exact_mod_cast h

variable {κ : ℝ} {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}

/-- **The data transport of a word through an image chain with a simple proper trace**: at a real point `x` of the
image chart whose boundary value `r ≠ 0` is real and not a mark, the force data of the flowed marks at `x` are the force
data of the initial marks at `r`. -/
theorem forceBoundaryData_imgChart_eq (hη' : IsLoewnerTrace W' η') (hη'p : IsProperArc η') (hW' : Continuous W')
    (hW'0 : W' 0 = 0) (hT : 0 ≤ T) (hxL : ∀ i, xL i ≤ 0) {x r : ℝ} (hr : r ≠ 0)
    (hF : extendFrom H (fwdMapInv W' T) x = r) (hrL : ∀ i, xL i ≠ r) (hrR : ∀ j, xR j ≠ r) :
    forceBoundaryData κ ρL ρR (fun i => -rightImg (fun s => -W' s) (-xL i) T - W' T)
        (fun j => rightImg W' (xR j) T - W' T) x = forceBoundaryData κ ρL ρR xL xR r := by
  rcases lt_or_gt_of_ne hr with hneg | hpos
  · rw [eq_neg_gImg_of_extendFrom_neg hη' hη'p hW' hW'0 hT hneg hF]
    have hal := alive_neg_of_isProperArc hη' hη'p hW' hW'0 hT
    have h := forceBoundaryData_flow_left (κ := κ) ρL ρR (xR := xR) hW' hT (neg_pos.2 hneg)
      (hal _ (neg_pos.2 hneg)) (xL := xL) (fun i h => hrL i (by linarith)) (fun i => ?_)
    · rwa [neg_neg] at h
    · intro he
      have he' : gImg (fun s => -W' s) (-r) T = rightImg (fun s => -W' s) (-xL i) T := by linarith
      rcases lt_or_gt_of_ne (show -xL i ≠ -r from fun h' => hrL i (by linarith)) with hlt | hgt
      · have := rightImg_lt_gImg_of_lt (show Continuous fun s => -W' s from hW'.neg) hT hal (neg_nonneg.2 (hxL i)) hlt
        linarith
      · have := (rightImg_le_gImg_iff (show Continuous fun s => -W' s from hW'.neg) hT (hal _ (neg_pos.2 hneg))
          (show -xL i ≠ -r from fun h' => hrL i (by linarith))).1 he'.ge
        linarith
  · rw [eq_gImg_of_extendFrom_pos hη' hη'p hW' hW'0 hT hpos hF]
    exact forceBoundaryData_flow_right ρL ρR hW' hT hpos (alive_of_isProperArc hη' hη'p hW' hW'0 hT _ hpos) hrR

/-- **A real image-chart point with a real boundary value `r ≠ 0` off the marks is not a jump of the flowed data.** -/
theorem notMem_forceJumpSet_imgChart (hη' : IsLoewnerTrace W' η') (hη'p : IsProperArc η') (hW' : Continuous W')
    (hW'0 : W' 0 = 0) (hT : 0 ≤ T) (hxL : ∀ i, xL i ≤ 0) (hxR : ∀ j, 0 ≤ xR j) {x r : ℝ} (hr : r ≠ 0)
    (hF : extendFrom H (fwdMapInv W' T) x = r) (hrL : ∀ i, xL i ≠ r) (hrR : ∀ j, xR j ≠ r) :
    x ∉ forceJumpSet (fun i => -rightImg (fun s => -W' s) (-xL i) T - W' T)
      (fun j => rightImg W' (xR j) T - W' T) := by
  have hR0 : ∀ z, 0 ≤ z → W' T ≤ rightImg W' z T := fun z hz =>
    (show W' T ≤ rightImg W' 0 T by have h0 := chartAR_nonneg hW' hT (W' := W'); unfold chartAR at h0; linarith).trans
      (rightImg_mono_index hW' hT hz)
  have hL0 : ∀ z, 0 ≤ z → -W' T ≤ rightImg (fun s => -W' s) z T := fun z hz =>
    (show -W' T ≤ rightImg (fun s => -W' s) 0 T by
      have h0 := chartAL_nonpos hW' hT (W' := W'); unfold chartAL at h0; linarith).trans
      (rightImg_mono_index (show Continuous fun s => -W' s from hW'.neg) hT hz)
  simp only [forceJumpSet, mem_insert_iff, mem_union, mem_range, not_or]
  rcases lt_or_gt_of_ne hr with hneg | hpos
  · have hx := eq_neg_gImg_of_extendFrom_neg hη' hη'p hW' hW'0 hT hneg hF
    have hal := alive_neg_of_isProperArc hη' hη'p hW' hW'0 hT
    have hg := (hal _ (neg_pos.2 hneg)).lt_gImg (show Continuous fun s => -W' s from hW'.neg) ⟨hT, le_rfl⟩
    refine ⟨by linarith, ?_, ?_⟩
    · rintro ⟨i, he⟩
      rcases lt_or_gt_of_ne (show -xL i ≠ -r from fun h' => hrL i (by linarith)) with hlt | hgt
      · have := rightImg_lt_gImg_of_lt (show Continuous fun s => -W' s from hW'.neg) hT hal (neg_nonneg.2 (hxL i)) hlt
        linarith
      · have := (rightImg_le_gImg_iff (show Continuous fun s => -W' s from hW'.neg) hT (hal _ (neg_pos.2 hneg))
          (show -xL i ≠ -r from fun h' => hrL i (by linarith))).not.2 (not_lt.2 hgt.le)
        linarith
    · rintro ⟨j, he⟩
      have := hR0 _ (hxR j)
      linarith
  · have hx := eq_gImg_of_extendFrom_pos hη' hη'p hW' hW'0 hT hpos hF
    have hal := alive_of_isProperArc hη' hη'p hW' hW'0 hT
    have hg := (hal _ hpos).lt_gImg hW' ⟨hT, le_rfl⟩
    refine ⟨by linarith, ?_, ?_⟩
    · rintro ⟨i, he⟩
      have := hL0 _ (neg_nonneg.2 (hxL i))
      linarith
    · rintro ⟨j, he⟩
      rcases lt_or_gt_of_ne (hrR j) with hlt | hgt
      · have := rightImg_lt_gImg_of_lt hW' hT hal (hxR j) hlt
        linarith
      · have := (rightImg_le_gImg_iff hW' hT (hal _ hpos) (hrR j)).not.2 (not_lt.2 hgt.le)
        linarith

end Transport

/-! ### The data match at time `0` -/

section Match

open MartChar.RealFlow Restart.RetAux79 GlueCond Sec7.StripSysField Cond44Ref
open CrossCond.Word49 (psiL psiR junL junR)

variable {κ : ℝ} {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ)

/-- **The image word's data at time `0`** in the counterflow chart `Ψ = revChart ω s`: marks `Ψ(x_{i,L})`, `Ψ(x_{j,R})`
and the junctions `Ψ(∞⁻)`, `Ψ(∞⁺)`, with the junction weights `κ − 4 − Σρ_L`, `κ/2 − 2 − Σρ_R` of the chart `Ψ`
(PROVE-GLUECOND6's finding; GLUECOND7's `jwL cL6`, `jwR cR6`). -/
def imgData0 (κ : ℝ) (ω : ℝ → ℝ) (s : ℝ) : ℝ → ℝ :=
  forceBoundaryData κ (Fin.snoc ρL (κ - 4 - ∑ i, ρL i)) (Fin.snoc ρR (κ / 2 - 2 - ∑ j, ρR j))
    (Fin.snoc (fun i => psiL ω s (xL i)) (junL ω s)) (Fin.snoc (fun j => psiR ω s (xR j)) (junR ω s))

/-- **The counterflow word's data at time `s`** (chart `R`, parameter `16/κ`, centred), with the marks flowed by the
driver `ω` (the data of `cfU` when `ω` is the history's regularized driver). -/
def cfDataAt (κ : ℝ) (b : ℝ → ℝ) (J : Finset ℝ) (ω : ℝ → ℝ) (s : ℝ) : ℝ → ℝ :=
  forceBoundaryData (16 / κ) (cfRhoL κ b J) (cfRhoR κ b J)
    (fun i => -rightImg (fun r => -ω r) (-flowLineXL (counterflowData κ b) (counterflowJumps J) 0 i) s - ω s)
    (fun j => rightImg ω (flowLineXR (counterflowData κ b) (counterflowJumps J) 0 j) s - ω s)

theorem sum_filter_lt_snoc {n : ℕ} (f g : Fin n → ℝ) (a c r : ℝ) :
    ∑ i ∈ Finset.univ.filter (fun i => r < (Fin.snoc f a : Fin (n + 1) → ℝ) i),
        (Fin.snoc g c : Fin (n + 1) → ℝ) i =
      (∑ i ∈ Finset.univ.filter (fun i => r < f i), g i) + if r < a then c else 0 := by
  rw [Finset.sum_filter, Finset.sum_filter, Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]

theorem sum_filter_snoc_le {n : ℕ} (f g : Fin n → ℝ) (a c r : ℝ) :
    ∑ i ∈ Finset.univ.filter (fun i => (Fin.snoc f a : Fin (n + 1) → ℝ) i ≤ r),
        (Fin.snoc g c : Fin (n + 1) → ℝ) i =
      (∑ i ∈ Finset.univ.filter (fun i => f i ≤ r), g i) + if a ≤ r then c else 0 := by
  rw [Finset.sum_filter, Finset.sum_filter, Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]

/-- The right marks of the counterflow word are nonnegative. -/
theorem flowLineXR_zero_nonneg (b : ℝ → ℝ) (J : Finset ℝ) (j : Fin (flowLineNR b J 0)) : 0 ≤ flowLineXR b J 0 j := by
  rcases Supp8.flowLineXR_cases 0 j with h | ⟨z, -, hz, h⟩
  · rw [h]
  · rw [h]; linarith

/-- The left marks of the counterflow word are nonpositive. -/
theorem flowLineXL_zero_nonpos (b : ℝ → ℝ) (J : Finset ℝ) (i : Fin (flowLineNL b J 0)) : flowLineXL b J 0 i ≤ 0 := by
  rcases Supp8.flowLineXL_cases 0 i with h | ⟨z, -, hz, h⟩
  · rw [h]
  · rw [h]; linarith

variable {ω : ℝ → ℝ} {s : ℝ}

/-- **The exposed left side** (`r` left of the left junction): the image word's datum is the return datum of the
counterflow word plus `πχ/2`. -/
theorem imgData0_eq_left (hκ : 0 < κ) (hω : Continuous ω) (hs : 0 ≤ s) (hj : 0 < rightImg ω 0 s - ω s)
    (hxL : ∀ i, xL i ≤ 0) (b : ℝ → ℝ) (J : Finset ℝ) {r : ℝ} (hr : r < junL ω s) :
    imgData0 ρL ρR xL xR κ ω s r =
      returnData (cfOffset κ) (cfCoeff κ) (cfDataAt κ b J ω s) r + π / 2 * chiC κ := by
  have hjL : junL ω s < 0 := by
    rw [junL, neg_div]; exact neg_neg_of_pos (div_pos one_pos hj)
  have hr0 : r < 0 := hr.trans hjL
  have hR : ∀ j, -r⁻¹ < rightImg ω (flowLineXR (counterflowData κ b) (counterflowJumps J) 0 j) s - ω s := by
    intro j
    have h1 := rightImg_mono_index hω hs (flowLineXR_zero_nonneg _ _ j) (x := 0)
    have h2 : -r⁻¹ < rightImg ω 0 s - ω s := by
      have h3 : r < -1 / (rightImg ω 0 s - ω s) := hr
      rw [lt_div_iff₀ hj] at h3
      have h4 : -r⁻¹ = -1 / r := by rw [neg_div, one_div]
      rw [h4, div_lt_iff_of_neg hr0]
      linarith [mul_comm (rightImg ω 0 s - ω s) r]
    linarith
  rw [cfDataAt, returnData_forceBoundaryData_left hκ _ _ _ _ hr0 hR, ← junction_height_left hκ (∑ i, ρL i)]
  unfold imgData0 forceBoundaryData
  simp only [hr0, ↓reduceIte]
  rw [sum_filter_lt_snoc, Finset.filter_true_of_mem fun i _ =>
    hr.trans_le (CrossCond.Word49.junL_le_psiL hω hs hj (hxL i))]
  simp only [hr, ↓reduceIte]
  ring

/-- **The exposed right side** (`r` right of the right junction). -/
theorem imgData0_eq_right (hκ : 0 < κ) (hω : Continuous ω) (hs : 0 ≤ s)
    (hj : -rightImg (fun r => -ω r) 0 s - ω s < 0) (hxR : ∀ j, 0 ≤ xR j) (b : ℝ → ℝ) (J : Finset ℝ) {r : ℝ}
    (hr : junR ω s < r) :
    imgData0 ρL ρR xL xR κ ω s r =
      returnData (cfOffset κ) (cfCoeff κ) (cfDataAt κ b J ω s) r + π / 2 * chiC κ := by
  have hjR : 0 < junR ω s := by
    rw [junR, neg_div]; exact neg_pos.2 (div_neg_of_pos_of_neg one_pos hj)
  have hr0 : 0 < r := hjR.trans hr
  have hL : ∀ i, -rightImg (fun r => -ω r) (-flowLineXL (counterflowData κ b) (counterflowJumps J) 0 i) s - ω s <
      -r⁻¹ := by
    intro i
    have h1 := rightImg_mono_index (w := fun r => -ω r) (show Continuous fun r => -ω r from hω.neg) hs
      (neg_nonneg.2 (flowLineXL_zero_nonpos _ _ i)) (x := 0)
    have h2 : -rightImg (fun r => -ω r) 0 s - ω s < -r⁻¹ := by
      have h3 : -1 / (-rightImg (fun r => -ω r) 0 s - ω s) < r := hr
      rw [div_lt_iff_of_neg hj] at h3
      have h4 : -r⁻¹ = -1 / r := by rw [neg_div, one_div]
      rw [h4, lt_div_iff₀ hr0]
      linarith [mul_comm (-rightImg (fun r => -ω r) 0 s - ω s) r]
    linarith
  rw [cfDataAt, returnData_forceBoundaryData_right hκ _ _ _ _ hr0 hL, ← junction_height_right hκ (∑ j, ρR j)]
  unfold imgData0 forceBoundaryData
  simp only [not_lt.2 hr0.le, ↓reduceIte]
  rw [sum_filter_snoc_le, Finset.filter_true_of_mem fun j _ =>
    (CrossCond.Word49.psiR_le_junR hω hs hj (hxR j)).trans hr.le]
  simp only [hr.le, ↓reduceIte]
  ring

/-- `−r⁻¹ < G ↔ r < −1/G` for `r < 0 < G`. -/
theorem neg_inv_lt_iff_lt_neg_one_div {r G : ℝ} (hr : r < 0) (hG : 0 < G) : -r⁻¹ < G ↔ r < -1 / G := by
  have h4 : -r⁻¹ = -1 / r := by rw [neg_div, one_div]
  rw [h4, div_lt_iff_of_neg hr, lt_div_iff₀ hG, mul_comm]

/-- `−1/H < r ↔ −r⁻¹ < H`... in the form needed on the right: `−1/H < −1/m ↔ H < m` for negative `H`, `m`. -/
theorem neg_one_div_lt_neg_one_div_iff {H m : ℝ} (hH : H < 0) (hm : m < 0) : -1 / H < -1 / m ↔ H < m := by
  rw [neg_div, neg_div, neg_lt_neg_iff]
  exact one_div_lt_one_div_of_neg hm hH

/-- **The physical real line, left of `0`** (`Ψ(∞⁻) < r < 0`): the image word's datum is the original datum at the
physical point `Ψ⁻¹(r)`, which is the return datum of the counterflow word plus `πχ/2`. -/
theorem imgData0_eq_mid_neg (hκ : 0 < κ) (hω : Continuous ω) (hs : 0 ≤ s) (hj : 0 < rightImg ω 0 s - ω s)
    (hxL : ∀ i, xL i ≤ 0) {r : ℝ} (hr0 : r < 0) (hrj : junL ω s < r)
    (hrJ : ∀ x ∈ forceJumpFinset xL xR, x < 0 → psiL ω s x ≠ r) :
    imgData0 ρL ρR xL xR κ ω s r = returnData (cfOffset κ) (cfCoeff κ)
      (cfDataAt κ (fun x => forceBoundaryData κ ρL ρR xL xR x + -(π / 2 * chiC κ)) (forceJumpFinset xL xR) ω s) r +
        π / 2 * chiC κ := by
  set b : ℝ → ℝ := fun x => forceBoundaryData κ ρL ρR xL xR x + -(π / 2 * chiC κ) with hbdef
  set J := forceJumpFinset xL xR with hJdef
  have hM : rightImg ω 0 s < -r⁻¹ + ω s := by
    have h3 : -1 / (rightImg ω 0 s - ω s) < r := hrj
    rw [div_lt_iff₀ hj] at h3
    have h4 : -r⁻¹ = -1 / r := by rw [neg_div, one_div]
    have h5 : rightImg ω 0 s - ω s < -r⁻¹ := by
      rw [h4, lt_div_iff_of_neg hr0]; linarith [mul_comm (rightImg ω 0 s - ω s) r]
    linarith
  obtain ⟨y, hy0, hyA, hyg⟩ := exists_alive_gImg_eq hω hs hM
  set x' : ℝ := -y⁻¹ with hx'
  have hx'0 : x' < 0 := neg_neg_of_pos (inv_pos.2 hy0)
  have hyx' : -1 / x' = y := by rw [hx']; field_simp
  have hrg : rightImg ω y s - ω s = -r⁻¹ := by rw [rightImg_eq_gImg hω hs hyA, hyg]; ring
  have hpsi : psiL ω s x' = r := by
    unfold psiL
    simp only [hx'0.ne, ↓reduceIte]
    rw [hyx', hrg]
    field_simp
  have hx'J : x' ∉ J := fun h => hrJ x' h hx'0 hpsi
  have hyJ : y ∉ counterflowJumps J := by
    simp only [counterflowJumps, returnExcept, Finset.mem_insert, Finset.mem_image, not_or, not_exists, not_and]
    refine ⟨hy0.ne', fun w hw he => hx'J ?_⟩
    have : w = x' := by rw [hx', ← he, inv_neg, inv_inv, neg_neg]
    rwa [← this]
  have hXR : ∀ j, flowLineXR (counterflowData κ b) (counterflowJumps J) 0 j ≠ y := by
    intro j he
    rcases Supp8.flowLineXR_cases 0 j with h | ⟨z, hz, -, h⟩
    · rw [h] at he; exact hy0.ne' he.symm
    · rw [h, sub_zero] at he
      exact hyJ (he ▸ Finset.filter_subset _ _ hz)
  have hb : IsPiecewiseConstantBoundaryData b J := isPiecewiseConstant_forceData κ ρL ρR xL xR _
  have e1 : cfDataAt κ b J ω s (-r⁻¹) = counterflowData κ b y := by
    rw [cfDataAt, show -r⁻¹ = gImg ω y s - ω s by linarith, forceBoundaryData_flow_right _ _ hω hs hy0 hyA hXR]
    exact Sec4.forceBoundaryData_flowLine (by positivity) (isPiecewiseConstant_counterflowData κ hb) hy0.ne' hyJ
  have hlift : liftBoundary x' = liftBoundary r := by simp [liftBoundary, hr0, hx'0]
  have e2 : b x' = -counterflowData κ b y + cfOffset κ + cfCoeff κ * liftBoundary r := by
    rw [← returnData_inverseData (cfOffset κ) (cfCoeff κ) b hx'0.ne, returnData, ← hlift]
    have : -x'⁻¹ = y := by rw [hx', inv_neg, inv_inv, neg_neg]
    rw [this]
    rfl
  have hRHS : returnData (cfOffset κ) (cfCoeff κ) (cfDataAt κ b J ω s) r = b x' := by
    rw [returnData, e1, e2]
  have hiff : ∀ i, r < psiL ω s (xL i) ↔ x' < xL i := by
    intro i
    have hxi : xL i ∈ J := Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image_of_mem _
      (Finset.mem_univ i)))
    have hne : xL i ≠ x' := fun h => hx'J (h ▸ hxi)
    rcases (hxL i).lt_or_eq with hneg | h0
    · have hG : 0 < rightImg ω (-1 / xL i) s - ω s := by
        have := rightImg_mono_index hω hs (x := 0) (x' := -1 / xL i)
          (div_nonneg_of_nonpos (by norm_num) (hxL i))
        linarith
      have hya : -1 / xL i ≠ y := fun h => hne (by
        have e : -1 / xL i = -1 / x' := h.trans hyx'.symm
        rw [div_eq_div_iff hneg.ne hx'0.ne] at e
        linarith)
      have hpsi' : psiL ω s (xL i) = -1 / (rightImg ω (-1 / xL i) s - ω s) := by
        unfold psiL; simp only [hneg.ne, ↓reduceIte]
      rw [hpsi', ← neg_inv_lt_iff_lt_neg_one_div hr0 hG, ← hrg, sub_lt_sub_iff_right,
        rightImg_eq_gImg hω hs hyA, ← not_le, rightImg_le_gImg_iff hω hs hyA hya]
      have h1 := neg_inv_lt_iff_of_neg_of_pos hneg hy0
      have h2 : -1 / xL i = -(xL i)⁻¹ := by rw [neg_div, one_div]
      rw [h2, h1, not_lt]
      exact ⟨fun h => lt_of_le_of_ne h hne.symm, le_of_lt⟩
    · rw [h0]
      have : psiL ω s 0 = 0 := by simp [psiL]
      rw [this]
      exact iff_of_true hr0 hx'0
  have hLHS : imgData0 ρL ρR xL xR κ ω s r = forceBoundaryData κ ρL ρR xL xR x' := by
    unfold imgData0 forceBoundaryData
    simp only [hr0, hx'0, ↓reduceIte]
    rw [sum_filter_lt_snoc]
    simp only [show ¬ (r < junL ω s) from not_lt.2 hrj.le, ↓reduceIte, add_zero]
    rw [Finset.filter_congr fun i _ => hiff i]
  rw [hLHS, hRHS, hbdef]
  ring

/-- **The physical real line, right of `0`** (`0 < r < Ψ(∞⁺)`): the mirror of `imgData0_eq_mid_neg` (through the
reflected driver); `−r⁻¹` must not be a left mark of the counterflow word at time `s`. -/
theorem imgData0_eq_mid_pos (hκ : 0 < κ) (hω : Continuous ω) (hs : 0 ≤ s)
    (hj : -rightImg (fun r => -ω r) 0 s - ω s < 0) (hxR : ∀ j, 0 ≤ xR j) {r : ℝ} (hr0 : 0 < r)
    (hrj : r < junR ω s) (hrJ : ∀ x ∈ forceJumpFinset xL xR, 0 < x → psiR ω s x ≠ r)
    (hrV : ∀ i, -rightImg (fun r => -ω r)
      (-flowLineXL (counterflowData κ (fun x => forceBoundaryData κ ρL ρR xL xR x + -(π / 2 * chiC κ)))
        (counterflowJumps (forceJumpFinset xL xR)) 0 i) s - ω s ≠ -r⁻¹) :
    imgData0 ρL ρR xL xR κ ω s r = returnData (cfOffset κ) (cfCoeff κ)
      (cfDataAt κ (fun x => forceBoundaryData κ ρL ρR xL xR x + -(π / 2 * chiC κ)) (forceJumpFinset xL xR) ω s) r +
        π / 2 * chiC κ := by
  set b : ℝ → ℝ := fun x => forceBoundaryData κ ρL ρR xL xR x + -(π / 2 * chiC κ) with hbdef
  set J := forceJumpFinset xL xR with hJdef
  have hωn : Continuous fun r => -ω r := hω.neg
  have hM : rightImg (fun r => -ω r) 0 s < r⁻¹ - ω s := by
    have h3 : r < -1 / (-rightImg (fun r => -ω r) 0 s - ω s) := hrj
    rw [lt_div_iff_of_neg hj] at h3
    have h4 : -r⁻¹ = -1 / r := by rw [neg_div, one_div]
    have h5 : -r⁻¹ < -rightImg (fun r => -ω r) 0 s - ω s := by
      rw [h4, div_lt_iff₀ hr0]; linarith [mul_comm (-rightImg (fun r => -ω r) 0 s - ω s) r]
    linarith
  obtain ⟨y, hy0, hyA, hyg⟩ := exists_alive_gImg_eq hωn hs hM
  set x' : ℝ := y⁻¹ with hx'
  have hx'0 : 0 < x' := inv_pos.2 hy0
  have hyx' : 1 / x' = y := by rw [hx', one_div, inv_inv]
  have hrg : -rightImg (fun r => -ω r) y s - ω s = -r⁻¹ := by rw [rightImg_eq_gImg hωn hs hyA, hyg]; ring
  have hpsi : psiR ω s x' = r := by
    unfold psiR
    simp only [hx'0.ne', ↓reduceIte]
    rw [hyx', hrg]
    field_simp
  have hx'J : x' ∉ J := fun h => hrJ x' h hx'0 hpsi
  have hyJ : -y ∉ counterflowJumps J := by
    simp only [counterflowJumps, returnExcept, Finset.mem_insert, Finset.mem_image, not_or, not_exists, not_and]
    refine ⟨neg_ne_zero.2 hy0.ne', fun w hw he => hx'J ?_⟩
    have hw' : w⁻¹ = y := by linarith
    have : w = x' := by rw [hx', ← hw', inv_inv]
    rwa [← this]
  have hXL : ∀ i, -flowLineXL (counterflowData κ b) (counterflowJumps J) 0 i ≠ y := by
    intro i he
    rcases Supp8.flowLineXL_cases 0 i with h | ⟨z, hz, -, h⟩
    · rw [h, neg_zero] at he; exact hy0.ne' he.symm
    · rw [h, sub_zero] at he
      exact hyJ (by rw [← he, neg_neg]; exact Finset.filter_subset _ _ hz)
  have hb : IsPiecewiseConstantBoundaryData b J := isPiecewiseConstant_forceData κ ρL ρR xL xR _
  have e1 : cfDataAt κ b J ω s (-r⁻¹) = counterflowData κ b (-y) := by
    rw [cfDataAt, show -r⁻¹ = -gImg (fun r => -ω r) y s - ω s by rw [← rightImg_eq_gImg hωn hs hyA]; linarith,
      forceBoundaryData_flow_left _ _ hω hs hy0 hyA hXL fun i h => hrV i (by
        rw [← rightImg_eq_gImg hωn hs hyA] at h; linarith)]
    exact Sec4.forceBoundaryData_flowLine (by positivity) (isPiecewiseConstant_counterflowData κ hb)
      (neg_ne_zero.2 hy0.ne') hyJ
  have hlift : liftBoundary x' = liftBoundary r := by simp [liftBoundary, not_lt.2 hr0.le, not_lt.2 hx'0.le]
  have e2 : b x' = -counterflowData κ b (-y) + cfOffset κ + cfCoeff κ * liftBoundary r := by
    rw [← returnData_inverseData (cfOffset κ) (cfCoeff κ) b hx'0.ne', returnData, ← hlift]
    have : -x'⁻¹ = -y := by rw [hx', inv_inv]
    rw [this]
    rfl
  have hRHS : returnData (cfOffset κ) (cfCoeff κ) (cfDataAt κ b J ω s) r = b x' := by
    rw [returnData, e1, e2]
  have hm : -r⁻¹ < 0 := neg_neg_of_pos (inv_pos.2 hr0)
  have hiff : ∀ j, psiR ω s (xR j) ≤ r ↔ xR j ≤ x' := by
    intro j
    have hxj : xR j ∈ J := Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image_of_mem _
      (Finset.mem_univ j)))
    have hne : xR j ≠ x' := fun h => hx'J (h ▸ hxj)
    rcases (hxR j).lt_or_eq with hpos | h0
    · have hH : -rightImg (fun r => -ω r) (1 / xR j) s - ω s < 0 := by
        have := rightImg_mono_index hωn hs (x := 0) (x' := 1 / xR j) (one_div_pos.2 hpos).le
        linarith
      have hya : 1 / xR j ≠ y := fun h => hne (by
        have e : 1 / xR j = 1 / x' := h.trans hyx'.symm
        rw [div_eq_div_iff hpos.ne' hx'0.ne'] at e
        linarith)
      have hpsi' : psiR ω s (xR j) = -1 / (-rightImg (fun r => -ω r) (1 / xR j) s - ω s) := by
        unfold psiR; simp only [hpos.ne', ↓reduceIte]
      have hne' : psiR ω s (xR j) ≠ r := hrJ (xR j) hxj hpos
      have hr_eq : r = -1 / -r⁻¹ := by field_simp
      rw [le_iff_lt_or_eq, or_iff_left hne', hpsi']
      conv_lhs => rw [hr_eq]
      rw [neg_one_div_lt_neg_one_div_iff hH hm, ← hrg, sub_lt_sub_iff_right, neg_lt_neg_iff,
        rightImg_eq_gImg hωn hs hyA, ← not_le, rightImg_le_gImg_iff hωn hs hyA hya, not_lt,
        le_one_div hy0 hpos, ← hyx', one_div_one_div]
    · rw [← h0]
      have : psiR ω s 0 = 0 := by simp [psiR]
      rw [this]
      exact iff_of_true hr0.le hx'0.le
  have hLHS : imgData0 ρL ρR xL xR κ ω s r = forceBoundaryData κ ρL ρR xL xR x' := by
    unfold imgData0 forceBoundaryData
    simp only [not_lt.2 hr0.le, not_lt.2 hx'0.le, ↓reduceIte]
    rw [sum_filter_snoc_le]
    simp only [show ¬ (junR ω s ≤ r) from not_le.2 hrj, ↓reduceIte, add_zero]
    rw [Finset.filter_congr fun j _ => hiff j]
  rw [hLHS, hRHS, hbdef]
  ring

/-- **The data match at every real chart point off a finite set**: the image word's datum is the return datum of the
counterflow word at time `s` plus `πχ/2` (junction weights `κ − 4 − Σρ_L`, `κ/2 − 2 − Σρ_R`). -/
theorem imgData0_eq_returnData (hκ : 0 < κ) (hω : Continuous ω) (hs : 0 ≤ s) (hjL : 0 < rightImg ω 0 s - ω s)
    (hjR : -rightImg (fun r => -ω r) 0 s - ω s < 0) (hxL : ∀ i, xL i ≤ 0) (hxR : ∀ j, 0 ≤ xR j) {r : ℝ}
    (hr0 : r ≠ 0) (hrL : r ≠ junL ω s) (hrR : r ≠ junR ω s) (hrJ : ∀ x ∈ forceJumpFinset xL xR, psiL ω s x ≠ r)
    (hrJ' : ∀ x ∈ forceJumpFinset xL xR, psiR ω s x ≠ r)
    (hrV : ∀ i, -rightImg (fun r => -ω r)
      (-flowLineXL (counterflowData κ (fun x => forceBoundaryData κ ρL ρR xL xR x + -(π / 2 * chiC κ)))
        (counterflowJumps (forceJumpFinset xL xR)) 0 i) s - ω s ≠ -r⁻¹) :
    imgData0 ρL ρR xL xR κ ω s r = returnData (cfOffset κ) (cfCoeff κ)
      (cfDataAt κ (fun x => forceBoundaryData κ ρL ρR xL xR x + -(π / 2 * chiC κ)) (forceJumpFinset xL xR) ω s) r +
        π / 2 * chiC κ := by
  rcases lt_or_gt_of_ne hr0 with hneg | hpos
  · rcases lt_or_gt_of_ne hrL with h1 | h1
    · exact imgData0_eq_left ρL ρR xL xR hκ hω hs hjL hxL _ _ h1
    · exact imgData0_eq_mid_neg ρL ρR xL xR hκ hω hs hjL hxL hneg h1 fun x hx _ => hrJ x hx
  · rcases lt_or_gt_of_ne hrR with h1 | h1
    · exact imgData0_eq_mid_pos ρL ρR xL xR hκ hω hs hjR hxR hpos h1 (fun x hx _ => hrJ' x hx) hrV
    · exact imgData0_eq_right ρL ρR xL xR hκ hω hs hjR hxR _ _ h1

end Match

/-! ### Item 1: the union mean at the real points of the image chart, for the image word -/

section Word

open MartChar.RealFlow Restart.RetAux79 GlueCond Sec7.StripSysField Cond44Ref
open CrossCond.Word49 (psiL psiR junL junR)

variable {κ : ℝ} {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ)

/-- The left weights of the image word in the chart `Ψ` (GLUECOND7's `jwL cL6`). -/
abbrev imgRhoL (κ : ℝ) : Fin (nL + 1) → ℝ := Fin.snoc ρL (κ - 4 - ∑ i, ρL i)

/-- The right weights of the image word in the chart `Ψ` (GLUECOND7's `jwR cR6`). -/
abbrev imgRhoR (κ : ℝ) : Fin (nR + 1) → ℝ := Fin.snoc ρR (κ / 2 - 2 - ∑ j, ρR j)

/-- The left marks of the image word at time `0` (GLUECOND5's `gXL` on good samples). -/
abbrev imgMarkL (ω : ℝ → ℝ) (s : ℝ) : Fin (nL + 1) → ℝ := Fin.snoc (fun i => psiL ω s (xL i)) (junL ω s)

/-- The right marks of the image word at time `0` (GLUECOND5's `gXR` on good samples). -/
abbrev imgMarkR (ω : ℝ → ℝ) (s : ℝ) : Fin (nR + 1) → ℝ := Fin.snoc (fun j => psiR ω s (xR j)) (junR ω s)

/-- The counterflow word's flowed left marks at time `s`. -/
abbrev cfMarkL (κ : ℝ) (b : ℝ → ℝ) (J : Finset ℝ) (ω : ℝ → ℝ) (s : ℝ)
    (i : Fin (flowLineNL (counterflowData κ b) (counterflowJumps J) 0)) : ℝ :=
  -rightImg (fun r => -ω r) (-flowLineXL (counterflowData κ b) (counterflowJumps J) 0 i) s - ω s

/-- The counterflow word's flowed right marks at time `s`. -/
abbrev cfMarkR (κ : ℝ) (b : ℝ → ℝ) (J : Finset ℝ) (ω : ℝ → ℝ) (s : ℝ)
    (j : Fin (flowLineNR (counterflowData κ b) (counterflowJumps J) 0)) : ℝ :=
  rightImg ω (flowLineXR (counterflowData κ b) (counterflowJumps J) 0 j) s - ω s

/-- The data of the original flow word shifted to the counterflow field `h − πχ/2`. -/
abbrev bData (κ : ℝ) : ℝ → ℝ := fun x => forceBoundaryData κ ρL ρR xL xR x + -(π / 2 * chiC κ)

/-- **The exceptional real chart points** (time `0`): `0`, the junctions, the images of the jump candidates, and the
exceptional set of the counterflow mean `retMean`. -/
def badPts (κ : ℝ) (ω : ℝ → ℝ) (s : ℝ) : Set ℝ :=
  {0, junL ω s, junR ω s} ∪ psiL ω s '' ↑(forceJumpFinset xL xR) ∪ psiR ω s '' ↑(forceJumpFinset xL xR) ∪
    ↑(returnExcept (forceJumpFinset (cfMarkL κ (bData ρL ρR xL xR κ) (forceJumpFinset xL xR) ω s)
      (cfMarkR κ (bData ρL ρR xL xR κ) (forceJumpFinset xL xR) ω s)))

theorem badPts_finite (κ : ℝ) (ω : ℝ → ℝ) (s : ℝ) : (badPts ρL ρR xL xR κ ω s).Finite := by
  unfold badPts
  refine (((Set.toFinite _).union ?_).union ?_).union (Finset.finite_toSet _)
  · exact (Finset.finite_toSet _).image _
  · exact (Finset.finite_toSet _).image _

variable {ω : ℝ → ℝ} {s : ℝ} {W' : ℝ → ℝ} {η' : ℝ → ℂ} {T : ℝ}

/-- **Item 1 (deterministic, for the image word).** Counterflow chart `Ψ = revChart ω s` with strict junction gaps,
flow hull `A` (bounded, `closure A ⊆ A ∪ {0}`, disjoint from `G = R(K′_s)`), `M`, `m_G` with GLUECOND6's limits `hG`,
`hInf` and identity `m_G + χ arg_Ψ = retMean κ v ∘ Ψ` (`v` the bounded harmonic extension of the counterflow word's
data at time `s`), an image chain `W′` with a simple proper trace, image time `T > 0`, and `u` the bounded harmonic
extension of the image word's data at `T` (marks flowed from `imgMarkL`, `imgMarkR`; weights `imgRhoL`, `imgRhoR`).
Then off a finite set, at every real image-chart point `x` whose boundary value `F̄′_T(x)` is real,
`M ∘ Φ + πχ/2 − (u − χ (Im L′_T ∘ F′_T + arg_Ψ ∘ Φ)) → 0`. -/
theorem exists_finite_tendsto_imgChart_real (hκ : 0 < κ) (hω : Continuous ω) (hω0 : ω 0 = 0) (hs : 0 ≤ s)
    (hB : HasBdryLimits (fwdMapInv ω s)) (hjL : 0 < rightImg ω 0 s - ω s)
    (hjR : -rightImg (fun r => -ω r) 0 s - ω s < 0) (hxL : ∀ i, xL i ≤ 0) (hxR : ∀ j, 0 ≤ xR j)
    {A : Set ℂ} (hAb : Bornology.IsBounded A) (hAcl : ∀ z ∈ closure A, z ∈ A ∨ z = 0)
    (hAG : Disjoint A (negInv '' fwdHull ω s)) (hAH : A ⊆ H) {M mG v : ℂ → ℝ}
    (hv : IsBoundedHarmonicExtension (cfDataAt κ (bData ρL ρR xL xR κ) (forceJumpFinset xL xR) ω s)
      (forceJumpSet (cfMarkL κ (bData ρL ρR xL xR κ) (forceJumpFinset xL xR) ω s)
        (cfMarkR κ (bData ρL ρR xL xR κ) (forceJumpFinset xL xR) ω s)) v)
    (hG : ∀ z₀ ∈ negInv '' fwdHull ω s ∪ {z : ℂ | z.im = 0}, (∃ r > 0, A ∩ ball z₀ r ⊆ negInv '' fwdHull ω s) →
      Tendsto (fun z => M z - mG z) (𝓝[H \ (A ∪ negInv '' fwdHull ω s)] z₀) (𝓝 0))
    (hInf : Tendsto (fun z => M z - mG z) (Bornology.cobounded ℂ ⊓ 𝓟 (H \ (A ∪ negInv '' fwdHull ω s))) (𝓝 0))
    (hId : ∀ z ∈ H \ negInv '' fwdHull ω s, mG z + chiC κ * (logDerivPsi ω s z).im = retMean κ v (revChart ω s z))
    (hW' : Continuous W') (hW'0 : W' 0 = 0) (hη' : IsLoewnerTrace W' η') (hη'p : IsProperArc η') (hT : 0 < T)
    {u : ℂ → ℝ}
    (hu : IsBoundedHarmonicExtension (forceBoundaryData κ (imgRhoL ρL κ) (imgRhoR ρR κ)
        (fun i => -rightImg (fun r => -W' r) (-imgMarkL xL ω s i) T - W' T)
        (fun j => rightImg W' (imgMarkR xR ω s j) T - W' T))
      (forceJumpSet (fun i => -rightImg (fun r => -W' r) (-imgMarkL xL ω s i) T - W' T)
        (fun j => rightImg W' (imgMarkR xR ω s j) T - W' T)) u) :
    ∃ E : Set ℝ, E.Finite ∧ ∀ x : ℝ, x ∉ E → (extendFrom H (fwdMapInv W' T) x).im = 0 →
      Tendsto (fun y => M (revChartInv ω s (fwdMapInv W' T y)) + π / 2 * chiC κ -
        (u y - chiC κ * ((logDerivFwd W' T (fwdMapInv W' T y)).im +
          (logDerivPsi ω s (revChartInv ω s (fwdMapInv W' T y))).im))) (𝓝[H] (x : ℂ)) (𝓝 0) := by
  set Eb := badPts ρL ρR xL xR κ ω s with hEb
  refine ⟨(fun r : ℝ => (fwdMap W' T r).re) '' Eb ∪ {chartAL W' T, chartAR W' T},
    ((badPts_finite ρL ρR xL xR κ ω s).image _).union (by simp), fun x hx hFim => ?_⟩
  simp only [mem_union, mem_image, mem_insert_iff, mem_singleton_iff, not_or, not_exists, not_and] at hx
  obtain ⟨hxE, hxAL, hxAR⟩ := hx
  set r := extendFrom H (fwdMapInv W' T) x with hrdef
  have hreq : r = ((r.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hFim])
  have hF : extendFrom H (fwdMapInv W' T) x = (r.re : ℂ) := by rw [← hrdef]; exact hreq
  have hr0 : r.re ≠ 0 := by
    intro h0
    have hF0 : extendFrom H (fwdMapInv W' T) x = 0 := by rw [hF, h0, Complex.ofReal_zero]
    rcases extendFrom_eq_zero_imp hη' hη'p hW' hW'0 hT hF0 with h | h
    · exact hxAR (by rw [chartAR]; linarith)
    · exact hxAL (by rw [chartAL]; linarith)
  have hxr := (eq_re_fwdMap_of_extendFrom_eq hη' hη'p hW' hW'0 hT.le hr0 hF).1
  have hrE : r.re ∉ Eb := fun h => hxE r.re h hxr.symm
  simp only [hEb, badPts, mem_union, mem_insert_iff, mem_singleton_iff, mem_image, Finset.mem_coe, not_or,
    not_exists, not_and] at hrE
  obtain ⟨⟨⟨⟨-, hrjL, hrjR⟩, hrJ⟩, hrJ'⟩, hrV⟩ := hrE
  -- the counterflow mean's boundary data
  have hV := isBoundedHarmonicExtension_retMean (κ := κ) (S := forceJumpFinset
    (cfMarkL κ (bData ρL ρR xL xR κ) (forceJumpFinset xL xR) ω s)
    (cfMarkR κ (bData ρL ρR xL xR κ) (forceJumpFinset xL xR) ω s)) (by rwa [coe_forceJumpFinset])
  have hrV' : r.re ∉ (returnExcept (forceJumpFinset
      (cfMarkL κ (bData ρL ρR xL xR κ) (forceJumpFinset xL xR) ω s)
      (cfMarkR κ (bData ρL ρR xL xR κ) (forceJumpFinset xL xR) ω s)) : Set ℝ) := hrV
  -- the image marks are not at `r`
  have hmL : ∀ i, imgMarkL xL ω s i ≠ r.re := by
    intro i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp only [imgMarkL, Fin.snoc_last]; exact fun h => hrjL h.symm
    · simp only [imgMarkL, Fin.snoc_castSucc]
      exact hrJ (xL i) (Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image_of_mem _
        (Finset.mem_univ i))))
  have hmR : ∀ j, imgMarkR xR ω s j ≠ r.re := by
    intro j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [imgMarkR, Fin.snoc_last]; exact fun h => hrjR h.symm
    · simp only [imgMarkR, Fin.snoc_castSucc]
      exact hrJ' (xR j) (Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image_of_mem _
        (Finset.mem_univ j))))
  have hmL0 : ∀ i, imgMarkL xL ω s i ≤ 0 := by
    intro i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp only [imgMarkL, Fin.snoc_last, junL, neg_div]; exact (neg_neg_of_pos (div_pos one_pos hjL)).le
    · simp only [imgMarkL, Fin.snoc_castSucc]; exact CrossCond.Word49.psiL_nonpos hω hs hjL (hxL i)
  -- the data match
  have hmatch : forceBoundaryData κ (imgRhoL ρL κ) (imgRhoR ρR κ)
      (fun i => -rightImg (fun r => -W' r) (-imgMarkL xL ω s i) T - W' T)
      (fun j => rightImg W' (imgMarkR xR ω s j) T - W' T) x =
      returnData (cfOffset κ) (cfCoeff κ) (cfDataAt κ (bData ρL ρR xL xR κ) (forceJumpFinset xL xR) ω s) r.re +
        π / 2 * chiC κ := by
    rw [forceBoundaryData_imgChart_eq _ _ hη' hη'p hW' hW'0 hT.le hmL0 hr0 hF hmL hmR]
    refine imgData0_eq_returnData ρL ρR xL xR hκ hω hs hjL hjR hxL hxR hr0 hrjL hrjR (fun c hc => hrJ c hc)
      (fun c hc => hrJ' c hc) fun i h => hrV' ?_
    simp only [returnExcept, Finset.coe_insert, Finset.coe_image, mem_insert_iff, mem_image, Finset.mem_coe]
    refine Or.inr ⟨_, Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image_of_mem _
      (Finset.mem_univ i))), ?_⟩
    have h' : cfMarkL κ (bData ρL ρR xL xR κ) (forceJumpFinset xL xR) ω s i = -r.re⁻¹ := h
    rw [h', inv_neg, inv_inv, neg_neg]
  have hxI := notMem_forceJumpSet_imgChart hη' hη'p hW' hW'0 hT.le hmL0 (fun j => ?_) hr0 hF hmL hmR
  · exact tendsto_imgChart_of_real hω hω0 hs hB hAb hAcl hAG hAH hG hInf hId hV hW' hW'0 hη' hη'p hT.le hu hr0
      hF hrV' hxI hmatch
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [imgMarkR, Fin.snoc_last, junR, neg_div]
      exact (neg_pos.2 (div_neg_of_pos_of_neg one_pos hjR)).le
    · simp only [imgMarkR, Fin.snoc_castSucc]; exact CrossCond.Word49.psiR_nonneg hω hs hjR (hxR j)

end Word

end InteractingSLE.Sec5.GlueImg