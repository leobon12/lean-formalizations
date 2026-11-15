/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.GlueCondUnionImgBase
import InteractingSLE.Spec.Sec6.Prop61BGlobal
import InteractingSLE.Spec.Sec6.DiskCaratheodory
import InteractingSLE.Foundations.Loewner.Capacity
import InteractingSLE.Foundations.Complex.RiemannMap
import InteractingSLE.Spec.Sec7.Lemma78MeanAssembly
import InteractingSLE.Spec.Sec5.CrossCondMartFwd

/-!
# G3 (ii), Proposition 4.9 direction: the boundary values of the union mean in the image chart, assembled, and the
chart data of the uniqueness step

Packet PROVE-GLUECOND10 (PROVE-GLUECOND8's "What remains" 3, deterministic part). Notation as in
`GlueCondUnionImgBase`.

* **`exists_finite_tendsto_imgChart`**: off a finite set of real image-chart points, the candidate
  `M ∘ Φ + πχ/2 − (u − χ (Im L′_T ∘ F′_T + arg_Ψ ∘ Φ))` tends to `0` — at the real points with a real boundary value
  (PROVE-GLUECOND8's item 1) and at the slit points (`tendsto_imgChart_slit_left_of_flow`, `…_right_of_flow`);
* **`tendsto_disk_of_imgChart`**: the same limits read on the unit circle through `Φ ∘ cayleyInv`;
* the chart data of `Sec6.ae_eqOn_component_of_tendsto_global` on `C = ℍ ∖ (A ∪ G)`: `Φ` is a conformal bijection
  `ℍ → C` (`isConformalBijection_imgPhiChart`), `φ_c = f′_T ∘ Ψ` its inverse (`isConformalBijection_imgFwdChart`),
  `L = Im L′_T ∘ Ψ + arg_Ψ` a continuous branch of `arg φ_c′` (`deriv_imgFwdChart_eq`), and `C` is connected.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped NNReal Real

open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv logDerivFwd chiC)
open QuantumZipper.CA (cayley cayleyInv)
open SupercriticalConformalCovariance (IsConformalBijection)

namespace InteractingSLE.Sec5.GlueImg

open WangWu hiding ratPt exists_ratPt_dist_lt
open MartChar.RealFlow Restart.RetAux79

/-! ### The boundary limits on the whole real line of the image chart -/

section Combine

open GlueCond Sec7.StripSysField Cond44Ref
open CrossCond.Word49 (psiL psiR junL junR)

variable {Wα ω W' : ℝ → ℝ} {t s T : ℝ}

/-- The closure of the hull of a trace that avoids `ℝ ∖ {0}` adds only the base point. -/
theorem mem_or_eq_zero_of_mem_closure_fwdHull (hWα : Continuous Wα) (ht : 0 ≤ t)
    (hKt : ∀ x : ℝ, x ≠ 0 → (x : ℂ) ∉ closure (fwdHull Wα t)) :
    ∀ z ∈ closure (fwdHull Wα t), z ∈ fwdHull Wα t ∨ z = 0 := by
  intro z hz
  have hA := isHPHull_fwdHull hWα ht
  have hzb : z ∈ Hbar := by
    have := closure_mono hA.1 hz
    rwa [closure_H] at this
  by_cases hzH : z ∈ H
  · left
    by_contra hzA
    obtain ⟨a, ⟨-, haA⟩, haA'⟩ := (_root_.mem_closure_iff.1 hz) (H \ fwdHull Wα t) hA.2.2.1 ⟨hzH, hzA⟩
    exact haA haA'
  · right
    have him : z.im = 0 := le_antisymm (not_lt.1 hzH) hzb
    by_contra hz0
    have hre : z.re ≠ 0 := fun h => hz0 (Complex.ext h him)
    have e : ((z.re : ℝ) : ℂ) = z := Complex.ext (by simp) (by simp [him])
    exact hKt z.re hre (e ▸ hz)

variable {κ : ℝ} {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}

theorem imgMarkL_nonpos (hω : Continuous ω) (hs : 0 ≤ s) (hjL : 0 < rightImg ω 0 s - ω s) (hxL : ∀ i, xL i ≤ 0) :
    ∀ i, imgMarkL xL ω s i ≤ 0 := by
  intro i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simp only [imgMarkL, Fin.snoc_last, junL, neg_div]; exact (neg_neg_of_pos (div_pos one_pos hjL)).le
  · simp only [imgMarkL, Fin.snoc_castSucc]; exact CrossCond.Word49.psiL_nonpos hω hs hjL (hxL i)

theorem imgMarkR_nonneg (hω : Continuous ω) (hs : 0 ≤ s) (hjR : -rightImg (fun r => -ω r) 0 s - ω s < 0)
    (hxR : ∀ j, 0 ≤ xR j) : ∀ j, 0 ≤ imgMarkR xR ω s j := by
  intro j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simp only [imgMarkR, Fin.snoc_last, junR, neg_div]
    exact (neg_pos.2 (div_neg_of_pos_of_neg one_pos hjR)).le
  · simp only [imgMarkR, Fin.snoc_castSucc]; exact CrossCond.Word49.psiR_nonneg hω hs hjR (hxR j)

/-- **The boundary values of the union mean in the image chart, everywhere but finitely many points** (G3 (ii),
deterministic). Flow: simple proper trace `α` avoiding `ℝ ∖ {0}`, flow time `t > 0`. Counterflow chart
`Ψ = revChart ω s` with boundary limits, `closure K′_s ∩ ℝ ⊆ {0}`, strict junction gaps, `G = R(K′_s)` closed,
`A = K_t` disjoint from `G`, `closure K′_s` disjoint from `closure R(A)`. Image chain `W′` with a simple proper trace,
`K^{W′}_T = Ψ(A)`, tip `Ψ(α(t))`. `M` has GLUECOND6's counterflow-side limits (`hG`, `hInf`, `hId`) and the flow-side
limit `hFl` at the non-tip slit points. Then off a finite set of real image-chart points,
`M ∘ Φ + πχ/2 − (u − χ (Im L′_T ∘ F′_T + arg_Ψ ∘ Φ)) → 0` (`u` the bounded harmonic extension of the image word's
data at `T`, junction weights `κ − 4 − Σρ_L`, `κ/2 − 2 − Σρ_R`). -/
theorem exists_finite_tendsto_imgChart {α : ℝ → ℂ} (hα : IsLoewnerTrace Wα α) (hαp : IsProperArc α)
    (hWα : Continuous Wα) (hWα0 : Wα 0 = 0) (ht : 0 < t)
    (hKt : ∀ x : ℝ, x ≠ 0 → (x : ℂ) ∉ closure (fwdHull Wα t)) (hκ : 0 < κ)
    (hω : Continuous ω) (hω0 : ω 0 = 0) (hs : 0 ≤ s) (hB : HasBdryLimits (fwdMapInv ω s))
    (hKs : ∀ z ∈ closure (fwdHull ω s), z.im = 0 → z = 0) (hjL : 0 < rightImg ω 0 s - ω s)
    (hjR : -rightImg (fun r => -ω r) 0 s - ω s < 0) (hGc : IsClosed (negInv '' fwdHull ω s))
    (hdisj : Disjoint (fwdHull Wα t) (negInv '' fwdHull ω s))
    (hdis : Disjoint (closure (fwdHull ω s)) (closure (negInv '' fwdHull Wα t)))
    (hxL : ∀ i, xL i ≤ 0) (hxR : ∀ j, 0 ≤ xR j) {M mG v : ℂ → ℝ}
    (hv : IsBoundedHarmonicExtension (cfDataAt κ (bData ρL ρR xL xR κ) (forceJumpFinset xL xR) ω s)
      (forceJumpSet (cfMarkL κ (bData ρL ρR xL xR κ) (forceJumpFinset xL xR) ω s)
        (cfMarkR κ (bData ρL ρR xL xR κ) (forceJumpFinset xL xR) ω s)) v)
    (hG : ∀ z₀ ∈ negInv '' fwdHull ω s ∪ {z : ℂ | z.im = 0},
      (∃ r > 0, fwdHull Wα t ∩ ball z₀ r ⊆ negInv '' fwdHull ω s) →
      Tendsto (fun z => M z - mG z) (𝓝[H \ (fwdHull Wα t ∪ negInv '' fwdHull ω s)] z₀) (𝓝 0))
    (hInf : Tendsto (fun z => M z - mG z)
      (Bornology.cobounded ℂ ⊓ 𝓟 (H \ (fwdHull Wα t ∪ negInv '' fwdHull ω s))) (𝓝 0))
    (hId : ∀ z ∈ H \ negInv '' fwdHull ω s, mG z + chiC κ * (logDerivPsi ω s z).im = retMean κ v (revChart ω s z))
    (hW' : Continuous W') (hW'0 : W' 0 = 0) {η' : ℝ → ℂ} (hη' : IsLoewnerTrace W' η') (hη'p : IsProperArc η')
    (hT : 0 < T) (hK' : fwdHull W' T = revChart ω s '' fwdHull Wα t) (htip : η' T = revChart ω s (α t))
    {u uA : ℂ → ℝ}
    (hu : IsBoundedHarmonicExtension (forceBoundaryData κ (imgRhoL ρL κ) (imgRhoR ρR κ)
        (fun i => -rightImg (fun r => -W' r) (-imgMarkL xL ω s i) T - W' T)
        (fun j => rightImg W' (imgMarkR xR ω s j) T - W' T))
      (forceJumpSet (fun i => -rightImg (fun r => -W' r) (-imgMarkL xL ω s i) T - W' T)
        (fun j => rightImg W' (imgMarkR xR ω s j) T - W' T)) u)
    (huA : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR
        (fun i => -rightImg (fun r => -Wα r) (-xL i) t - Wα t) (fun j => rightImg Wα (xR j) t - Wα t))
      (forceJumpSet (fun i => -rightImg (fun r => -Wα r) (-xL i) t - Wα t)
        (fun j => rightImg Wα (xR j) t - Wα t)) uA)
    (hFl : ∀ v : ℝ, 0 < v → v < t → Tendsto (fun z => M z + π / 2 * chiC κ -
        (uA (fwdMap Wα t z) - chiC κ * (logDerivFwd Wα t z).im))
      (𝓝[H \ (fwdHull Wα t ∪ negInv '' fwdHull ω s)] (α v)) (𝓝 0)) :
    ∃ E : Set ℝ, E.Finite ∧ ∀ x : ℝ, x ∉ E →
      Tendsto (fun y => M (revChartInv ω s (fwdMapInv W' T y)) + π / 2 * chiC κ -
        (u y - chiC κ * ((logDerivFwd W' T (fwdMapInv W' T y)).im +
          (logDerivPsi ω s (revChartInv ω s (fwdMapInv W' T y))).im))) (𝓝[H] (x : ℂ)) (𝓝 0) := by
  have hA := isHPHull_fwdHull hWα ht.le
  obtain ⟨E₁, hE₁, h1⟩ := exists_finite_tendsto_imgChart_real ρL ρR xL xR hκ hω hω0 hs hB hjL hjR hxL hxR hA.2.1
    (mem_or_eq_zero_of_mem_closure_fwdHull hWα ht.le hKt) hdisj hA.1 hv hG hInf hId hW' hW'0 hη' hη'p hT hu
  refine ⟨E₁ ∪ {0}, hE₁.union (finite_singleton 0), fun x hx => ?_⟩
  rcases (extendFrom_im_nonneg hη' hW' hW'0 hT.le x).lt_or_eq with hpos | h0
  · have hxx := chartAL_lt_of_extendFrom_mem_H hη' hW' hW'0 hT.le hpos
    have hx0 : x ≠ 0 := fun h => hx (Or.inr h)
    have hmL := imgMarkL_nonpos hω hs hjL hxL
    have hmR := imgMarkR_nonneg hω hs hjR hxR
    rcases lt_or_gt_of_ne hx0 with hneg | hpos'
    · exact tendsto_imgChart_slit_left_of_flow hα hαp hWα hWα0 ht hKt hω hω0 hs hB hKs hjL hW' hW'0 hT hη' hη'p hGc
        hdisj hdis hK' htip hxL hxR hmL hmR huA hu hFl hxx.1 hneg
    · exact tendsto_imgChart_slit_right_of_flow hα hαp hWα hWα0 ht hKt hω hω0 hs hB hKs hjR hW' hW'0 hT hη' hη'p hGc
        hdisj hdis hK' htip hxL hxR hmL hmR huA hu hFl hxx.2 hpos'
  · exact h1 x (fun h => hx (Or.inl h)) h0.symm

end Combine

/-! ### The chart data of the uniqueness step -/

section Chart

variable {Wα ω W' : ℝ → ℝ} {t s T : ℝ}

/-- `C = ℍ ∖ (A ∪ G)` is open. -/
theorem isOpen_H_diff_union (hWα : Continuous Wα) (ht : 0 ≤ t) (hGc : IsClosed (negInv '' fwdHull ω s)) :
    IsOpen (H \ (fwdHull Wα t ∪ negInv '' fwdHull ω s)) := by
  rw [← sdiff_sdiff]
  exact (QuantumZipper.FwdHolo.isOpen_compl_fwdHull hWα ht).sdiff hGc

/-- **`Φ = Ψ⁻¹ ∘ F′_T` is a conformal bijection `ℍ → ℍ ∖ (A ∪ G)`.** -/
theorem isConformalBijection_imgPhiChart (hω : Continuous ω) (hω0 : ω 0 = 0) (hs : 0 ≤ s)
    (hW' : Continuous W') (hW'0 : W' 0 = 0) (hT : 0 ≤ T) (hAG : fwdHull Wα t ⊆ H \ negInv '' fwdHull ω s)
    (hK' : fwdHull W' T = revChart ω s '' fwdHull Wα t) :
    IsConformalBijection (fun y => revChartInv ω s (fwdMapInv W' T y)) H
      (H \ (fwdHull Wα t ∪ negInv '' fwdHull ω s)) := by
  have h1 := isConformalBijection_fwdMapInv hW' hW'0 hT
  have h2 := isConformalBijection_revChartInv hω hω0 hs
  have h2' : IsConformalBijection (revChartInv ω s) (H \ fwdHull W' T)
      (H \ (fwdHull Wα t ∪ negInv '' fwdHull ω s)) := by
    refine ⟨h2.1.mono sdiff_subset, ?_⟩
    have hb := (h2.2.injOn.mono (sdiff_subset : H \ fwdHull W' T ⊆ H)).bijOn_image
    rw [hK', CrossCond.Word49.revChartInv_image_H_diff_union hω hω0 hs hAG] at hb
    rw [hK']
    exact hb
  have h3 := isConformalBijection_comp h2' h1
  exact h3

/-- `Ψ` maps `ℍ ∖ (A ∪ G)` into `ℍ ∖ Ψ(A)`. -/
theorem revChart_mapsTo_H_diff (hω : Continuous ω) (hω0 : ω 0 = 0) (hs : 0 ≤ s)
    (hAG : fwdHull Wα t ⊆ H \ negInv '' fwdHull ω s) :
    MapsTo (revChart ω s) (H \ (fwdHull Wα t ∪ negInv '' fwdHull ω s)) (H \ revChart ω s '' fwdHull Wα t) := by
  intro z hz
  have hzG : z ∈ H \ negInv '' fwdHull ω s := ⟨hz.1, fun h => hz.2 (Or.inr h)⟩
  refine ⟨revChart_mem_H hω hs hzG, ?_⟩
  rintro ⟨a, ha, e⟩
  exact hz.2 (Or.inl (injOn_revChart hω hω0 hs (hAG ha) hzG e ▸ ha))

/-- **`φ_c = f′_T ∘ Ψ` is a conformal bijection `ℍ ∖ (A ∪ G) → ℍ`**, the inverse of `Φ`. -/
theorem isConformalBijection_imgFwdChart (hω : Continuous ω) (hω0 : ω 0 = 0) (hs : 0 ≤ s)
    (hW' : Continuous W') (hW'0 : W' 0 = 0) (hT : 0 ≤ T) (hAG : fwdHull Wα t ⊆ H \ negInv '' fwdHull ω s)
    (hK' : fwdHull W' T = revChart ω s '' fwdHull Wα t) :
    IsConformalBijection (fun z => fwdMap W' T (revChart ω s z)) (H \ (fwdHull Wα t ∪ negInv '' fwdHull ω s)) H := by
  have hmaps := revChart_mapsTo_H_diff hω hω0 hs hAG
  rw [← hK'] at hmaps
  have hΦ := isConformalBijection_imgPhiChart hω hω0 hs hW' hW'0 hT hAG hK'
  refine ⟨fun z hz => ?_, ?_⟩
  · have hzG : z ∈ H \ negInv '' fwdHull ω s := ⟨hz.1, fun h => hz.2 (Or.inr h)⟩
    have h1 := differentiableAt_revChart hω hs hzG
    have h2 := (QuantumZipper.FwdHolo.differentiableOn_fwdMap hW' hT _ (hmaps hz)).differentiableAt
      ((QuantumZipper.FwdHolo.isOpen_compl_fwdHull hW' hT).mem_nhds (hmaps hz))
    exact (h2.comp z h1).differentiableWithinAt
  · refine Set.InvOn.bijOn (f' := fun y => revChartInv ω s (fwdMapInv W' T y)) ⟨fun z hz => ?_, fun y hy => ?_⟩
      (fun z hz => QuantumZipper.FwdHolo.mapsTo_fwdMap hW' hT (hmaps hz)) hΦ.2.mapsTo
    · have hzG : z ∈ H \ negInv '' fwdHull ω s := ⟨hz.1, fun h => hz.2 (Or.inr h)⟩
      show revChartInv ω s (fwdMapInv W' T (fwdMap W' T (revChart ω s z))) = z
      rw [QuantumZipper.RS.fwdMapInv_fwdMap hW' hW'0 hT (hmaps hz), revChartInv_revChart hω hω0 hs hzG]
    · show fwdMap W' T (revChart ω s (revChartInv ω s (fwdMapInv W' T y))) = y
      rw [revChart_revChartInv hω hω0 hs (QuantumZipper.RS.fwdMapInv_mem_H hW' hW'0 hT hy),
        QuantumZipper.RS.fwdMap_fwdMapInv hW' hW'0 hT hy]

/-- `exp w = ‖exp w‖ · exp(i Im w)`. -/
theorem exp_eq_norm_mul_exp_im (w : ℂ) : exp w = ‖exp w‖ * exp (w.im * I) := by
  calc exp w = exp ((w.re : ℂ) + (w.im : ℂ) * I) := by rw [Complex.re_add_im]
    _ = exp (w.re : ℂ) * exp (w.im * I) := exp_add _ _
    _ = ‖exp w‖ * exp (w.im * I) := by rw [Complex.norm_exp, Complex.ofReal_exp]

/-- **The continuous branch of `arg φ_c′`** on `C = ℍ ∖ (A ∪ G)`: `L = Im L′_T ∘ Ψ + arg_Ψ` (chain rule of the lifts
`logDerivFwd W′ T` of `f′_T` and `logDerivPsi` of `Ψ`). -/
theorem deriv_imgFwdChart_eq (hWα : Continuous Wα) (ht : 0 ≤ t) (hω : Continuous ω) (hω0 : ω 0 = 0) (hs : 0 ≤ s)
    (hGc : IsClosed (negInv '' fwdHull ω s)) (hW' : Continuous W') (hT : 0 ≤ T)
    (hAG : fwdHull Wα t ⊆ H \ negInv '' fwdHull ω s) (hK' : fwdHull W' T = revChart ω s '' fwdHull Wα t) :
    ContinuousOn (fun z => (logDerivFwd W' T (revChart ω s z)).im + (logDerivPsi ω s z).im)
        (H \ (fwdHull Wα t ∪ negInv '' fwdHull ω s)) ∧
      ∀ z ∈ H \ (fwdHull Wα t ∪ negInv '' fwdHull ω s),
        deriv (fun z => fwdMap W' T (revChart ω s z)) z =
          ‖deriv (fun z => fwdMap W' T (revChart ω s z)) z‖ *
            exp ((((logDerivFwd W' T (revChart ω s z)).im + (logDerivPsi ω s z).im : ℝ) : ℂ) * I) := by
  have hmaps := revChart_mapsTo_H_diff hω hω0 hs hAG
  rw [← hK'] at hmaps
  have hCo := isOpen_H_diff_union hWα ht hGc (ω := ω) (s := s)
  have hCsub : H \ (fwdHull Wα t ∪ negInv '' fwdHull ω s) ⊆ H \ negInv '' fwdHull ω s :=
    fun z hz => ⟨hz.1, fun h => hz.2 (Or.inr h)⟩
  have hdR : DifferentiableOn ℂ (revChart ω s) (H \ (fwdHull Wα t ∪ negInv '' fwdHull ω s)) :=
    fun z hz => (differentiableAt_revChart hω hs (hCsub hz)).differentiableWithinAt
  have hL := IsDerivLog.comp hCo (QuantumZipper.FwdHolo.isOpen_compl_fwdHull hW' hT)
    (QuantumZipper.FwdHolo.differentiableOn_fwdMap hW' hT) hdR hmaps (isDerivLog_fwdMap hW' hT)
    ((isDerivLog_revChart hω hs).mono hCsub)
  refine ⟨?_, fun z hz => ?_⟩
  · have := Complex.continuous_im.comp_continuousOn hL.1.continuousOn
    refine this.congr fun z _ => ?_
    simp only [Function.comp_apply, add_im]
  · have e : exp (logDerivFwd W' T (revChart ω s z) + logDerivPsi ω s z) =
        deriv (fun z => fwdMap W' T (revChart ω s z)) z := hL.2 z hz
    rw [← e]
    conv_lhs => rw [exp_eq_norm_mul_exp_im]
    simp only [add_im, Complex.ofReal_add]

/-- `C = ℍ ∖ (A ∪ G)` is connected (the image of `ℍ` under `Φ`), so it is its own component. -/
theorem connectedComponentIn_H_diff_union (hω : Continuous ω) (hω0 : ω 0 = 0) (hs : 0 ≤ s)
    (hW' : Continuous W') (hW'0 : W' 0 = 0) (hT : 0 ≤ T) (hAG : fwdHull Wα t ⊆ H \ negInv '' fwdHull ω s)
    (hK' : fwdHull W' T = revChart ω s '' fwdHull Wα t) {z₀ : ℂ}
    (hz₀ : z₀ ∈ H \ (fwdHull Wα t ∪ negInv '' fwdHull ω s)) :
    connectedComponentIn (H \ (fwdHull Wα t ∪ negInv '' fwdHull ω s)) z₀ =
      H \ (fwdHull Wα t ∪ negInv '' fwdHull ω s) := by
  have hΦ := isConformalBijection_imgPhiChart hω hω0 hs hW' hW'0 hT hAG hK'
  have hpre : IsPreconnected (H \ (fwdHull Wα t ∪ negInv '' fwdHull ω s)) := by
    rw [← hΦ.2.image_eq]
    exact (convex_halfSpace_im_gt 0).isPreconnected.image _ hΦ.1.continuousOn
  exact hpre.connectedComponentIn hz₀

/-- **The boundary limits read on the unit circle** (through `f = Φ ∘ cayleyInv`; the point `1` is `∞`). -/
theorem tendsto_disk_of_imgChart {Φ φc : ℂ → ℂ} {M v F G L Lb : ℂ → ℝ} {c χ : ℝ} {E : Set ℝ}
    (hlim : ∀ x : ℝ, x ∉ E → Tendsto (fun y => M (Φ y) + c - (G y - χ * Lb y)) (𝓝[H] (x : ℂ)) (𝓝 0))
    (hMv : ∀ y ∈ H, v (Φ y) + F (Φ y) = M (Φ y) + c) (hφ : ∀ y ∈ H, φc (Φ y) = y)
    (hL : ∀ y ∈ H, L (Φ y) = Lb y) :
    ∀ q ∈ sphere (0 : ℂ) 1, q ∉ insert (1 : ℂ) ((fun w : ℝ => cayley (w : ℂ)) '' E) →
      Tendsto (fun ζ => (v ((Φ ∘ cayleyInv) ζ) + F ((Φ ∘ cayleyInv) ζ)) -
          (G (φc ((Φ ∘ cayleyInv) ζ)) - χ * L ((Φ ∘ cayleyInv) ζ))) (𝓝[ball 0 1] q) (𝓝 0) := by
  intro q hq hqE
  have hq1 : q ≠ 1 := fun h1 => hqE (Set.mem_insert_iff.2 (Or.inl h1))
  set w : ℝ := (cayleyInv q).re with hw
  have hqw : cayleyInv q = (w : ℂ) := Restart.cayleyInv_eq_ofReal_re hq
  have hwE : w ∉ E := by
    intro hmem
    refine hqE (mem_insert_of_mem _ ⟨w, hmem, ?_⟩)
    show cayley (w : ℂ) = q
    rw [← hqw]
    exact QuantumZipper.CA.cayley_cayleyInv hq1
  have hT : Tendsto cayleyInv (𝓝[ball 0 1] q) (𝓝[H] (w : ℂ)) := by
    rw [← hqw]; exact Sec6.tendsto_cayleyInv_nhdsWithin_ball hq1
  refine ((hlim w hwE).comp hT).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ζ hζ
  have hζH : cayleyInv ζ ∈ H := QuantumZipper.CA.cayleyInv_mem_H hζ
  simp only [Function.comp_apply, hMv _ hζH, hφ _ hζH, hL _ hζH]

end Chart

/-! ### The identification on `C`, deterministic -/

section Ident

open GlueCond Sec7.StripSysField Cond44Ref
open CrossCond.Word49 (psiL psiR junL junR)

variable {Wα ω W' : ℝ → ℝ} {t s T : ℝ} {κ : ℝ} {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
  {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}

/-- **G3 (ii): the union mean in the image chart** (deterministic form of the glued assembly). In the setting of
`exists_finite_tendsto_imgChart`, let `w` be a function on `C = ℍ ∖ (A ∪ G)` with `M + πχ/2 = w + u₀`, for which the
uniqueness statement of Aux. 28 on `C` holds (`huniq`, the per-sample conclusion of
`Sec6.ae_eqOn_component_of_tendsto_global` with `v = w`, `F = u₀`). Then on `C`,
`w + u₀ = u ∘ f′_T ∘ Ψ − χ (Im L′_T ∘ Ψ + arg_Ψ)`. -/
theorem eqOn_imgChart {α : ℝ → ℂ} (hα : IsLoewnerTrace Wα α) (hαp : IsProperArc α)
    (hWα : Continuous Wα) (hWα0 : Wα 0 = 0) (ht : 0 < t)
    (hKt : ∀ x : ℝ, x ≠ 0 → (x : ℂ) ∉ closure (fwdHull Wα t)) (hκ : 0 < κ)
    (hω : Continuous ω) (hω0 : ω 0 = 0) (hs : 0 ≤ s) (hB : HasBdryLimits (fwdMapInv ω s))
    (hKs : ∀ z ∈ closure (fwdHull ω s), z.im = 0 → z = 0) (hjL : 0 < rightImg ω 0 s - ω s)
    (hjR : -rightImg (fun r => -ω r) 0 s - ω s < 0) (hGc : IsClosed (negInv '' fwdHull ω s))
    (hdisj : Disjoint (fwdHull Wα t) (negInv '' fwdHull ω s))
    (hdis : Disjoint (closure (fwdHull ω s)) (closure (negInv '' fwdHull Wα t)))
    (hxL : ∀ i, xL i ≤ 0) (hxR : ∀ j, 0 ≤ xR j) {M mG v : ℂ → ℝ}
    (hv : IsBoundedHarmonicExtension (cfDataAt κ (bData ρL ρR xL xR κ) (forceJumpFinset xL xR) ω s)
      (forceJumpSet (cfMarkL κ (bData ρL ρR xL xR κ) (forceJumpFinset xL xR) ω s)
        (cfMarkR κ (bData ρL ρR xL xR κ) (forceJumpFinset xL xR) ω s)) v)
    (hG : ∀ z₀ ∈ negInv '' fwdHull ω s ∪ {z : ℂ | z.im = 0},
      (∃ r > 0, fwdHull Wα t ∩ ball z₀ r ⊆ negInv '' fwdHull ω s) →
      Tendsto (fun z => M z - mG z) (𝓝[H \ (fwdHull Wα t ∪ negInv '' fwdHull ω s)] z₀) (𝓝 0))
    (hInf : Tendsto (fun z => M z - mG z)
      (Bornology.cobounded ℂ ⊓ 𝓟 (H \ (fwdHull Wα t ∪ negInv '' fwdHull ω s))) (𝓝 0))
    (hId : ∀ z ∈ H \ negInv '' fwdHull ω s, mG z + chiC κ * (logDerivPsi ω s z).im = retMean κ v (revChart ω s z))
    (hW' : Continuous W') (hW'0 : W' 0 = 0) {η' : ℝ → ℂ} (hη' : IsLoewnerTrace W' η') (hη'p : IsProperArc η')
    (hT : 0 < T) (hK' : fwdHull W' T = revChart ω s '' fwdHull Wα t) (htip : η' T = revChart ω s (α t))
    {u uA : ℂ → ℝ}
    (hu : IsBoundedHarmonicExtension (forceBoundaryData κ (imgRhoL ρL κ) (imgRhoR ρR κ)
        (fun i => -rightImg (fun r => -W' r) (-imgMarkL xL ω s i) T - W' T)
        (fun j => rightImg W' (imgMarkR xR ω s j) T - W' T))
      (forceJumpSet (fun i => -rightImg (fun r => -W' r) (-imgMarkL xL ω s i) T - W' T)
        (fun j => rightImg W' (imgMarkR xR ω s j) T - W' T)) u)
    (huA : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR
        (fun i => -rightImg (fun r => -Wα r) (-xL i) t - Wα t) (fun j => rightImg Wα (xR j) t - Wα t))
      (forceJumpSet (fun i => -rightImg (fun r => -Wα r) (-xL i) t - Wα t)
        (fun j => rightImg Wα (xR j) t - Wα t)) uA)
    (hFl : ∀ v : ℝ, 0 < v → v < t → Tendsto (fun z => M z + π / 2 * chiC κ -
        (uA (fwdMap Wα t z) - chiC κ * (logDerivFwd Wα t z).im))
      (𝓝[H \ (fwdHull Wα t ∪ negInv '' fwdHull ω s)] (α v)) (𝓝 0))
    {w u₀ : ℂ → ℝ} (hMw : ∀ z, M z + π / 2 * chiC κ = w z + u₀ z)
    (huniq : ∀ z₀ ∈ H \ (fwdHull Wα t ∪ negInv '' fwdHull ω s), ∀ (f φc : ℂ → ℂ) (G L : ℂ → ℝ) (E : Set ℂ),
      IsConformalBijection f (ball 0 1) (connectedComponentIn (H \ (fwdHull Wα t ∪ negInv '' fwdHull ω s)) z₀) →
      IsConformalBijection φc (connectedComponentIn (H \ (fwdHull Wα t ∪ negInv '' fwdHull ω s)) z₀)
        {w : ℂ | 0 < w.im} →
      InnerProductSpace.HarmonicOnNhd G {w : ℂ | 0 < w.im} →
      (∃ M, ∀ w : ℂ, 0 < w.im → |G w| ≤ M) →
      ContinuousOn L (connectedComponentIn (H \ (fwdHull Wα t ∪ negInv '' fwdHull ω s)) z₀) →
      (∀ z ∈ connectedComponentIn (H \ (fwdHull Wα t ∪ negInv '' fwdHull ω s)) z₀,
        deriv φc z = ‖deriv φc z‖ * exp (L z * I)) →
      E.Finite →
      (∀ q ∈ sphere (0 : ℂ) 1, q ∉ E →
        Tendsto (fun ζ => (w (f ζ) + u₀ (f ζ)) - (G (φc (f ζ)) - chiC κ * L (f ζ))) (𝓝[ball 0 1] q) (𝓝 0)) →
      ∀ z ∈ connectedComponentIn (H \ (fwdHull Wα t ∪ negInv '' fwdHull ω s)) z₀,
        w z + u₀ z = G (φc z) - chiC κ * L z) :
    ∀ z ∈ H \ (fwdHull Wα t ∪ negInv '' fwdHull ω s), w z + u₀ z =
      u (fwdMap W' T (revChart ω s z)) -
        chiC κ * ((logDerivFwd W' T (revChart ω s z)).im + (logDerivPsi ω s z).im) := by
  obtain ⟨E, hE, hlim⟩ := exists_finite_tendsto_imgChart ρL ρR hα hαp hWα hWα0 ht hKt hκ hω hω0 hs hB hKs hjL hjR
    hGc hdisj hdis hxL hxR hv hG hInf hId hW' hW'0 hη' hη'p hT hK' htip hu huA hFl
  have hAG : fwdHull Wα t ⊆ H \ negInv '' fwdHull ω s := fun z hz =>
    ⟨(isHPHull_fwdHull hWα ht.le).1 hz, fun h => disjoint_left.1 hdisj hz h⟩
  have hΦ := isConformalBijection_imgPhiChart hω hω0 hs hW' hW'0 hT.le hAG hK'
  have hφc := isConformalBijection_imgFwdChart hω hω0 hs hW' hW'0 hT.le hAG hK'
  obtain ⟨hLc, hder⟩ := deriv_imgFwdChart_eq hWα ht.le hω hω0 hs hGc hW' hT.le hAG hK'
  have hIH : I ∈ H := show (0 : ℝ) < I.im by simp
  have hz₀ := hΦ.2.mapsTo hIH
  have hcc := connectedComponentIn_H_diff_union hω hω0 hs hW' hW'0 hT.le hAG hK' hz₀
  have hf := isConformalBijection_comp hΦ isConformalBijection_cayleyInv
  have hφ : ∀ y ∈ H, fwdMap W' T (revChart ω s (revChartInv ω s (fwdMapInv W' T y))) = y := fun y hy => by
    rw [revChart_revChartInv hω hω0 hs (QuantumZipper.RS.fwdMapInv_mem_H hW' hW'0 hT.le hy),
      QuantumZipper.RS.fwdMap_fwdMapInv hW' hW'0 hT.le hy]
  have hdisk := tendsto_disk_of_imgChart (v := w) (F := u₀) (G := u) (χ := chiC κ)
    (φc := fun z => fwdMap W' T (revChart ω s z))
    (L := fun z => (logDerivFwd W' T (revChart ω s z)).im + (logDerivPsi ω s z).im) hlim
    (fun y _ => (hMw _).symm) hφ (fun y hy => by
      simp only [revChart_revChartInv hω hω0 hs (QuantumZipper.RS.fwdMapInv_mem_H hW' hW'0 hT.le hy)])
  have hEd : (insert (1 : ℂ) ((fun w : ℝ => cayley (w : ℂ)) '' E)).Finite := (hE.image _).insert 1
  have key := huniq _ hz₀
  rw [hcc] at key
  exact key _ _ u (fun z => (logDerivFwd W' T (revChart ω s z)).im + (logDerivPsi ω s z).im) _
    hf hφc hu.1 hu.2.1 hLc hder hEd hdisk

end Ident

end InteractingSLE.Sec5.GlueImg
