/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossRestartKernelSlit

/-!
# Finite exceptional sets for the nonsimple restart image

The general-angle data match is reused unchanged; only the real boundary steps need
interior-trace adapters. The finite set includes the base points and the flowed marks.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Complex Metric
open scoped Real
open QuantumZipper (H fwdHull fwdMap fwdMapInv logDerivFwd chiC)

namespace InteractingSLE.Sec5.CrossRestart

open WangWu hiding ratPt exists_ratPt_dist_lt
open MartChar.RealFlow Restart.RetAux79 GlueCond Sec7.StripSysField Cond44Ref GlueImg
open CrossCond.Theta
open CrossCond.Word49 (psiL psiR junL junR)

variable {κ : ℝ} {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
  (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (θ : ℝ)
  {ω : ℝ → ℝ} {s : ℝ} {W' : ℝ → ℝ} {η' : ℝ → ℂ} {T : ℝ}

/-- The real-boundary comparison outside a finite set, without image simplicity. -/
theorem exists_finite_tendsto_imgChart_realT_of_mem_H (hκ : 0 < κ) (hω : Continuous ω) (hω0 : ω 0 = 0) (hs : 0 ≤ s)
    (hB : HasBdryLimits (fwdMapInv ω s)) (hjL : 0 < rightImg ω 0 s - ω s)
    (hjR : -rightImg (fun r => -ω r) 0 s - ω s < 0) (hxL : ∀ i, xL i ≤ 0) (hxR : ∀ j, 0 ≤ xR j)
    {A : Set ℂ} (hAb : Bornology.IsBounded A) (hAcl : ∀ z ∈ closure A, z ∈ A ∨ z = 0)
    (hAG : Disjoint A (negInv '' fwdHull ω s)) (hAH : A ⊆ H) {M mG v : ℂ → ℝ}
    (hv : IsBoundedHarmonicExtension (cfDataAt κ (bDataT ρL ρR xL xR θ κ) (forceJumpFinset xL xR) ω s)
      (forceJumpSet (cfMarkL κ (bDataT ρL ρR xL xR θ κ) (forceJumpFinset xL xR) ω s)
        (cfMarkR κ (bDataT ρL ρR xL xR θ κ) (forceJumpFinset xL xR) ω s)) v)
    (hG : ∀ z₀ ∈ negInv '' fwdHull ω s ∪ {z : ℂ | z.im = 0}, (∃ r > 0, A ∩ ball z₀ r ⊆ negInv '' fwdHull ω s) →
      Tendsto (fun z => M z - mG z) (𝓝[H \ (A ∪ negInv '' fwdHull ω s)] z₀) (𝓝 0))
    (hInf : Tendsto (fun z => M z - mG z) (Bornology.cobounded ℂ ⊓ 𝓟 (H \ (A ∪ negInv '' fwdHull ω s))) (𝓝 0))
    (hId : ∀ z ∈ H \ negInv '' fwdHull ω s, mG z + chiC κ * (logDerivPsi ω s z).im = retMean κ v (revChart ω s z))
    (hW' : Continuous W') (hW'0 : W' 0 = 0) (hη' : IsLoewnerTrace W' η')
    (hη'H : ∀ r ∈ Ioc (0 : ℝ) T, η' r ∈ H) (hT : 0 < T)
    {u : ℂ → ℝ}
    (hu : IsBoundedHarmonicExtension (forceBoundaryData κ (imgRhoLT ρL θ κ) (imgRhoRT ρR θ κ)
        (fun i => -rightImg (fun r => -W' r) (-imgMarkL xL ω s i) T - W' T)
        (fun j => rightImg W' (imgMarkR xR ω s j) T - W' T))
      (forceJumpSet (fun i => -rightImg (fun r => -W' r) (-imgMarkL xL ω s i) T - W' T)
        (fun j => rightImg W' (imgMarkR xR ω s j) T - W' T)) u) :
    ∃ E : Set ℝ, E.Finite ∧ ∀ x : ℝ, x ∉ E → (extendFrom H (fwdMapInv W' T) x).im = 0 →
      Tendsto (fun y => M (revChartInv ω s (fwdMapInv W' T y)) + θ * chiC κ -
        (u y - chiC κ * ((logDerivFwd W' T (fwdMapInv W' T y)).im +
          (logDerivPsi ω s (revChartInv ω s (fwdMapInv W' T y))).im))) (𝓝[H] (x : ℂ)) (𝓝 0) := by
  set Eb := badPtsT ρL ρR xL xR θ κ ω s with hEb
  refine ⟨(fun r : ℝ => (fwdMap W' T r).re) '' Eb ∪
      ({chartAL W' T, chartAR W' T} ∪ ↑(forceJumpFinset
        (fun i => -rightImg (fun r => -W' r) (-imgMarkL xL ω s i) T - W' T)
        (fun j => rightImg W' (imgMarkR xR ω s j) T - W' T))),
    ((badPts_finiteT ρL ρR xL xR θ κ ω s).image _).union
      ((Set.toFinite _).union (Finset.finite_toSet _)), fun x hx hFim => ?_⟩
  simp only [mem_union, mem_image, mem_insert_iff, mem_singleton_iff, not_or, not_exists, not_and] at hx
  obtain ⟨hxE, ⟨⟨hxAL, hxAR⟩, hxJ⟩⟩ := hx
  set r := extendFrom H (fwdMapInv W' T) x with hrdef
  have hreq : r = ((r.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hFim])
  have hF : extendFrom H (fwdMapInv W' T) x = (r.re : ℂ) := by rw [← hrdef]; exact hreq
  have hr0 : r.re ≠ 0 := by
    intro h0
    have hF0 : extendFrom H (fwdMapInv W' T) x = 0 := by rw [hF, h0, Complex.ofReal_zero]
    rcases extendFrom_eq_zero_imp_of_mem_H hη' hη'H hW' hW'0 hT hF0 with h | h
    · exact hxAL h
    · exact hxAR h
  have hxr := eq_re_fwdMap_of_extendFrom_eq_of_mem_H hη' hη'H hW' hW'0 hT.le hr0 hF
  have hrE : r.re ∉ Eb := fun h => hxE r.re h hxr.symm
  simp only [hEb, badPtsT, mem_union, mem_insert_iff, mem_singleton_iff, mem_image, Finset.mem_coe, not_or,
    not_exists, not_and] at hrE
  obtain ⟨⟨⟨⟨-, hrjL, hrjR⟩, hrJ⟩, hrJ'⟩, hrV⟩ := hrE
  -- the counterflow mean's boundary data
  have hV := isBoundedHarmonicExtension_retMean (κ := κ) (S := forceJumpFinset
    (cfMarkL κ (bDataT ρL ρR xL xR θ κ) (forceJumpFinset xL xR) ω s)
    (cfMarkR κ (bDataT ρL ρR xL xR θ κ) (forceJumpFinset xL xR) ω s)) (by rwa [coe_forceJumpFinset])
  have hrV' : r.re ∉ (returnExcept (forceJumpFinset
      (cfMarkL κ (bDataT ρL ρR xL xR θ κ) (forceJumpFinset xL xR) ω s)
      (cfMarkR κ (bDataT ρL ρR xL xR θ κ) (forceJumpFinset xL xR) ω s)) : Set ℝ) := hrV
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
  have hmatch : forceBoundaryData κ (imgRhoLT ρL θ κ) (imgRhoRT ρR θ κ)
      (imgMarkL xL ω s) (imgMarkR xR ω s) r.re =
      returnData (cfOffset κ) (cfCoeff κ)
        (cfDataAt κ (bDataT ρL ρR xL xR θ κ) (forceJumpFinset xL xR) ω s) r.re +
        θ * chiC κ := by
    refine imgData0_eq_returnDataT ρL ρR xL xR θ hκ hω hs hjL hjR hxL hxR
      hr0 hrjL hrjR (fun c hc => hrJ c hc) (fun c hc => hrJ' c hc) fun i h => hrV' ?_
    simp only [returnExcept, Finset.coe_insert, Finset.coe_image, mem_insert_iff,
      mem_image, Finset.mem_coe]
    refine Or.inr ⟨_, Finset.mem_insert_of_mem (Finset.mem_union_left _
      (Finset.mem_image_of_mem _ (Finset.mem_univ i))), ?_⟩
    have h' : cfMarkL κ (bDataT ρL ρR xL xR θ κ) (forceJumpFinset xL xR) ω s i =
        -r.re⁻¹ := h
    rw [h', inv_neg, inv_inv, neg_neg]
  have hxI : x ∉ forceJumpSet
      (fun i => -rightImg (fun r => -W' r) (-imgMarkL xL ω s i) T - W' T)
      (fun j => rightImg W' (imgMarkR xR ω s j) T - W' T) := by
    rwa [coe_forceJumpFinset] at hxJ
  exact realSlitSideStatement ω s hω hω0 hs hB A hAb hAcl hAG hAH M mG
    (retMean κ v) (chiC κ) hG hInf hId _ _ hV W' η' T hW' hW'0 hη' hη'H hT.le
    (ofReal_notMem_closure_fwdHull_of_mem_H hη' hη'H hW' hT.le)
    κ (nL + 1) (nR + 1) (imgRhoLT ρL θ κ) (imgRhoRT ρR θ κ)
    (imgMarkL xL ω s) (imgMarkR xR ω s) hmL0 u hu x r.re (θ * chiC κ)
    hr0 hF hrV' hxI hmL hmR hmatch


/-- Image weights on the left of the restart chart, including the new junction. -/
abbrev slitRhoL {nL : ℕ} (ρL : Fin nL → ℝ) (κ θ : ℝ) : Fin (nL + 1) → ℝ :=
  Fin.snoc ρL (slitJunctionL κ θ (∑ i, ρL i))

/-- Image weights on the right of the restart chart, including the new junction. -/
abbrev slitRhoR {nR : ℕ} (ρR : Fin nR → ℝ) (κ θ : ℝ) : Fin (nR + 1) → ℝ :=
  Fin.snoc ρR (slitJunctionR κ θ (∑ j, ρR j))

/-- Dualizing and reversing the relative angle gives exactly the restart left weights. -/
theorem imgRhoLT_dual_neg {nL : ℕ} (ρL : Fin nL → ℝ) (κ θ : ℝ) :
    imgRhoLT ρL (-θ) (16 / κ) = slitRhoL ρL κ θ := by
  unfold imgRhoLT slitRhoL
  congr 1
  unfold cLT slitJunctionL cRT
  ring

/-- The corresponding equality for the restart right weights. -/
theorem imgRhoRT_dual_neg {nR : ℕ} (ρR : Fin nR → ℝ) (κ θ : ℝ) :
    imgRhoRT ρR (-θ) (16 / κ) = slitRhoR ρR κ θ := by
  unfold imgRhoRT slitRhoR
  congr 1
  unfold cRT slitJunctionR cLT
  ring

/-- The flow-slit side needed by Lemma 4.7's restart mean identification.

The obstacle's word and mean are the general-angle return word at parameter `16/κ`
and angle `−θ`. The constant `c` allows the centering of the union mean to be chosen
by the caller; `hId` records that same centering. The new and image traces need only
stay in the open half-plane, while the obstacle is a simple flow slit. -/
def SlitSideStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ θ : ℝ,
  ∀ {Wα : ℝ → ℝ} {α : ℝ → ℂ} {t : ℝ},
    Continuous Wα → Wα 0 = 0 → 0 < t → IsLoewnerTrace Wα α →
    (∀ r ∈ Ioc (0 : ℝ) t, α r ∈ H) →
  ∀ {ω : ℝ → ℝ} {β : ℝ → ℂ} {s : ℝ},
    Continuous ω → ω 0 = 0 → 0 < s → IsLoewnerTrace ω β → IsProperArc β →
    Disjoint (fwdHull Wα t) (negInv '' fwdHull ω s) →
  ∀ {W' : ℝ → ℝ} {η' : ℝ → ℂ} {T : ℝ},
    Continuous W' → W' 0 = 0 → 0 < T → IsLoewnerTrace W' η' →
    (∀ r ∈ Ioc (0 : ℝ) T, η' r ∈ H) →
    fwdHull W' T = revChart ω s '' fwdHull Wα t →
  ∀ {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    (xL : Fin nL → ℝ) (xR : Fin nR → ℝ),
    (∀ i, xL i ≤ 0) → (∀ j, 0 ≤ xR j) →
  ∀ (M mG v : ℂ → ℝ) (c : ℝ),
    IsBoundedHarmonicExtension
      (cfDataAt (16 / κ) (bDataT ρL ρR xL xR (-θ) (16 / κ))
        (forceJumpFinset xL xR) ω s)
      (forceJumpSet
        (cfMarkL (16 / κ) (bDataT ρL ρR xL xR (-θ) (16 / κ))
          (forceJumpFinset xL xR) ω s)
        (cfMarkR (16 / κ) (bDataT ρL ρR xL xR (-θ) (16 / κ))
          (forceJumpFinset xL xR) ω s)) v →
    (∀ z₀ ∈ negInv '' fwdHull ω s ∪ {z : ℂ | z.im = 0},
      (∃ r > 0, fwdHull Wα t ∩ ball z₀ r ⊆ negInv '' fwdHull ω s) →
      Tendsto (fun z => M z - mG z)
        (𝓝[H \ (fwdHull Wα t ∪ negInv '' fwdHull ω s)] z₀) (𝓝 0)) →
    Tendsto (fun z => M z - mG z)
      (Bornology.cobounded ℂ ⊓ 𝓟 (H \ (fwdHull Wα t ∪ negInv '' fwdHull ω s))) (𝓝 0) →
    (∀ z ∈ H \ negInv '' fwdHull ω s,
      mG z + chiC (16 / κ) * (logDerivPsi ω s z).im + c =
        retMean (16 / κ) v (revChart ω s z) + (-θ) * chiC (16 / κ)) →
  ∀ {u : ℂ → ℝ}, IsBoundedHarmonicExtension
      (forceBoundaryData (16 / κ) (slitRhoL ρL κ θ) (slitRhoR ρR κ θ)
        (fun i => -rightImg (fun r => -W' r) (-imgMarkL xL ω s i) T - W' T)
        (fun j => rightImg W' (imgMarkR xR ω s j) T - W' T))
      (forceJumpSet
        (fun i => -rightImg (fun r => -W' r) (-imgMarkL xL ω s i) T - W' T)
        (fun j => rightImg W' (imgMarkR xR ω s j) T - W' T)) u →
    ∃ E : Set ℝ, E.Finite ∧ ∀ x : ℝ, x ∉ E →
      (extendFrom H (fwdMapInv W' T) x).im = 0 →
      Tendsto (fun y => M (revChartInv ω s (fwdMapInv W' T y)) + c -
        (u y - chiC (16 / κ) * ((logDerivFwd W' T (fwdMapInv W' T y)).im +
          (logDerivPsi ω s (revChartInv ω s (fwdMapInv W' T y))).im)))
        (𝓝[H] (x : ℂ)) (𝓝 0)

/-- The required finite-exception statement, with no simplicity of either counterflow trace. -/
theorem slitSideStatement : SlitSideStatement := by
  intro κ hκ _hκ4 θ Wα α t hWα _hWα0 ht hα hαH ω β s hω hω0 hs hβ hβp
    hdisj W' η' T hW' hW'0 hT hη' hη'H _hK' nL nR ρL ρR xL xR hxL hxR
    M mG v c hv hG hInf hId u hu
  have hκ' : 0 < 16 / κ := div_pos (by norm_num) hκ
  let a : ℝ := (-θ) * chiC (16 / κ)
  let M' : ℂ → ℝ := fun z => M z + c - a
  let mG' : ℂ → ℝ := fun z => mG z + c - a
  have hdiff : (fun z => M' z - mG' z) = fun z => M z - mG z := by
    funext z
    dsimp only [M', mG']
    ring
  have hId' : ∀ z ∈ H \ negInv '' fwdHull ω s,
      mG' z + chiC (16 / κ) * (logDerivPsi ω s z).im =
        retMean (16 / κ) v (revChart ω s z) := by
    intro z hz
    have hh := hId z hz
    dsimp only [mG', a]
    linarith only [hh]
  have hu' := hu
  rw [← imgRhoLT_dual_neg, ← imgRhoRT_dual_neg] at hu'
  obtain ⟨E, hE, hlim⟩ := exists_finite_tendsto_imgChart_realT_of_mem_H
    (M := M') (mG := mG') (v := v)
    ρL ρR xL xR (-θ) hκ' hω hω0 hs.le (hβ.hasBdryLimits hω hω0 hs.le)
    (chartAR_pos hβ hβp hω hω0 hs) (chartAL_neg hβ hβp hω hω0 hs)
    hxL hxR (InteractingSLE.isBounded_fwdHull hWα t)
    (closure_fwdHull_subset_of_mem_H hα hαH hWα ht.le) hdisj
    (fun _ hz => hz.1) hv (by simpa only [hdiff] using hG)
    (by simpa only [hdiff] using hInf) hId' hW' hW'0 hη' hη'H hT hu'
  refine ⟨E, hE, fun x hx hreal => ?_⟩
  refine (hlim x hx hreal).congr fun y => ?_
  dsimp only [M', a]
  ring

end InteractingSLE.Sec5.CrossRestart
