/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossCondStagedLawSlit
import InteractingSLE.Spec.Sec5.CrossCondThetaImg

/-!
# The staged cross-conditioning law: the mean identification for a prefix with born marks

Packet PROVE-CROSSCOND-STAGED3 (S2). The root identification of CROSSCOND-THETA (`Theta.eqOn_imgChartT`) reads the
union mean of `A_t ∪ G_s` in the joint chart `f′_T ∘ Ψ` as the bounded harmonic extension of the image word, for a
flow word without marks on its sides. A staged prefix (one simple trace whose pieces start at switch times) carries the
marks created at its switches on its sides (born marks). Here the flow word `u_A` and the image word `u` are any force
words with the same weights whose side marks are paired (`IsBornPairL`, `IsBornPairR`: born at the same switch, or
outer), and the image word agrees with the root image word off the closed image slit (`hphysL`, `hphysR`):

* `exists_finite_tendsto_imgChart_bornWord`: off a finite set of image-chart real points the union-mean expression
  has the candidate's boundary limit (slit points: `tendsto_slit_left/right_of_bornWord` plus the flow side's limit
  `hFl`; physical and counterflow points: the root real-point lemma transferred through the equal data);
* **`eqOn_imgChart_bornWord`**: with Aux. 28's uniqueness (`huniq`), the union mean is the candidate of the born-mark
  image word: `w + 𝔥₀ = u ∘ f′_T ∘ Ψ − χ (arg f′_T′ ∘ Ψ + arg Ψ′)` on `ℍ ∖ (A ∪ G)`.

Deterministic; every probabilistic input (`hFl`, `hG`, `hInf`, `hId`, `huniq`) has the form the landed root chain
supplies (`Theta.meanIdentThetaStatement`'s proof).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv logDerivFwd chiC)
open QuantumZipper.RS (shiftDrive)
open QuantumZipper.CA (cayley cayleyInv)
open SupercriticalConformalCovariance (IsConformalBijection)
open scoped Real

namespace InteractingSLE.Sec5.CrossCond.StagedLaw

open WangWu hiding ratPt exists_ratPt_dist_lt
open GlueImg Theta Cond44Ref Word49 Sec7.StripSysField
open MartChar.RealFlow Restart.RetAux79

section Ident

variable {Wα ω W' : ℝ → ℝ} {t s T : ℝ} {κ : ℝ} {nL nR mL mR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (θ : ℝ)
  {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}

/-- **The per-point limits of the candidate with a born-mark image word** (staged version of
`Theta.exists_finite_tendsto_imgChartT`). The flow side is a born-mark word `u_A` (marks `vL`, `vR`, paired with the
image word's marks `vL'`, `vR'` by `IsBornPairL/R`), and the image word `u` agrees with the root image word of
CROSSCOND-THETA off the closed image slit (`hphysL`, `hphysR`). Off a finite set of image-chart real points, the
union-mean expression has the candidate's boundary limit. -/
theorem exists_finite_tendsto_imgChart_bornWord {α : ℝ → ℂ} (hα : IsLoewnerTrace Wα α) (hαp : IsProperArc α)
    (hWα : Continuous Wα) (hWα0 : Wα 0 = 0) (ht : 0 < t)
    (hKt : ∀ x : ℝ, x ≠ 0 → (x : ℂ) ∉ closure (fwdHull Wα t)) (hκ : 0 < κ)
    (hω : Continuous ω) (hω0 : ω 0 = 0) (hs : 0 ≤ s) (hB : HasBdryLimits (fwdMapInv ω s))
    (hKs : ∀ z ∈ closure (fwdHull ω s), z.im = 0 → z = 0) (hjL : 0 < rightImg ω 0 s - ω s)
    (hjR : -rightImg (fun r => -ω r) 0 s - ω s < 0) (hGc : IsClosed (negInv '' fwdHull ω s))
    (hdisj : Disjoint (fwdHull Wα t) (negInv '' fwdHull ω s))
    (hdis : Disjoint (closure (fwdHull ω s)) (closure (negInv '' fwdHull Wα t)))
    (hxL : ∀ i, xL i ≤ 0) (hxR : ∀ j, 0 ≤ xR j) {M mG v : ℂ → ℝ}
    (hv : IsBoundedHarmonicExtension (cfDataAt κ (bDataT ρL ρR xL xR θ κ) (forceJumpFinset xL xR) ω s)
      (forceJumpSet (cfMarkL κ (bDataT ρL ρR xL xR θ κ) (forceJumpFinset xL xR) ω s)
        (cfMarkR κ (bDataT ρL ρR xL xR θ κ) (forceJumpFinset xL xR) ω s)) v)
    (hG : ∀ z₀ ∈ negInv '' fwdHull ω s ∪ {z : ℂ | z.im = 0},
      (∃ r > 0, fwdHull Wα t ∩ ball z₀ r ⊆ negInv '' fwdHull ω s) →
      Tendsto (fun z => M z - mG z) (𝓝[H \ (fwdHull Wα t ∪ negInv '' fwdHull ω s)] z₀) (𝓝 0))
    (hInf : Tendsto (fun z => M z - mG z)
      (Bornology.cobounded ℂ ⊓ 𝓟 (H \ (fwdHull Wα t ∪ negInv '' fwdHull ω s))) (𝓝 0))
    (hId : ∀ z ∈ H \ negInv '' fwdHull ω s, mG z + chiC κ * (logDerivPsi ω s z).im = retMean κ v (revChart ω s z))
    (hW' : Continuous W') (hW'0 : W' 0 = 0) {η' : ℝ → ℂ} (hη' : IsLoewnerTrace W' η') (hη'p : IsProperArc η')
    (hT : 0 < T) (hK' : fwdHull W' T = revChart ω s '' fwdHull Wα t) (htip : η' T = revChart ω s (α t))
    {ρL₁ : Fin mL → ℝ} {ρR₁ : Fin mR → ℝ} {vL vL' : Fin mL → ℝ} {vR vR' : Fin mR → ℝ}
    (hvL : ∀ i, vL i ≤ 0) (hvR : ∀ j, 0 ≤ vR j) (hvL' : ∀ i, vL' i ≤ 0) (hvR' : ∀ j, 0 ≤ vR' j)
    (hpL : ∀ i, IsBornPairL Wα α t ω s W' η' T (vL i) (vL' i))
    (hpR : ∀ j, IsBornPairR Wα α t ω s W' η' T (vR j) (vR' j)) {uA u : ℂ → ℝ}
    (huA : IsBoundedHarmonicExtension (forceBoundaryData κ ρL₁ ρR₁ vL vR) (forceJumpSet vL vR) uA)
    (hu : IsBoundedHarmonicExtension (forceBoundaryData κ ρL₁ ρR₁ vL' vR') (forceJumpSet vL' vR') u)
    (hphysL : ∀ x : ℝ, x < chartAL W' T → forceBoundaryData κ ρL₁ ρR₁ vL' vR' x =
      forceBoundaryData κ (imgRhoLT ρL θ κ) (imgRhoRT ρR θ κ)
        (fun i => -rightImg (fun r => -W' r) (-imgMarkL xL ω s i) T - W' T)
        (fun j => rightImg W' (imgMarkR xR ω s j) T - W' T) x)
    (hphysR : ∀ x : ℝ, chartAR W' T < x → forceBoundaryData κ ρL₁ ρR₁ vL' vR' x =
      forceBoundaryData κ (imgRhoLT ρL θ κ) (imgRhoRT ρR θ κ)
        (fun i => -rightImg (fun r => -W' r) (-imgMarkL xL ω s i) T - W' T)
        (fun j => rightImg W' (imgMarkR xR ω s j) T - W' T) x)
    (hFl : ∀ v : ℝ, 0 < v → v < t → Tendsto (fun z => M z + θ * chiC κ -
        (uA (fwdMap Wα t z) - chiC κ * (logDerivFwd Wα t z).im))
      (𝓝[H \ (fwdHull Wα t ∪ negInv '' fwdHull ω s)] (α v)) (𝓝 0)) :
    ∃ E : Set ℝ, E.Finite ∧ ∀ x : ℝ, x ∉ E →
      Tendsto (fun y => M (revChartInv ω s (fwdMapInv W' T y)) + θ * chiC κ -
        (u y - chiC κ * ((logDerivFwd W' T (fwdMapInv W' T y)).im +
          (logDerivPsi ω s (revChartInv ω s (fwdMapInv W' T y))).im))) (𝓝[H] (x : ℂ)) (𝓝 0) := by
  have hA := isHPHull_fwdHull hWα ht.le
  obtain ⟨u₁, hu₁⟩ := exists_isBoundedHarmonicExtension_forceBoundaryData κ (imgRhoLT ρL θ κ) (imgRhoRT ρR θ κ)
    (fun i => -rightImg (fun r => -W' r) (-imgMarkL xL ω s i) T - W' T)
    (fun j => rightImg W' (imgMarkR xR ω s j) T - W' T)
  obtain ⟨E₁, hE₁, h1⟩ := exists_finite_tendsto_imgChart_realT ρL ρR xL xR θ hκ hω hω0 hs hB hjL hjR hxL hxR hA.2.1
    (mem_or_eq_zero_of_mem_closure_fwdHull hWα ht.le hKt) hdisj hA.1 hv hG hInf hId hW' hW'0 hη' hη'p hT hu₁
  set J₁ := forceJumpSet (fun i => -rightImg (fun r => -W' r) (-imgMarkL xL ω s i) T - W' T)
    (fun j => rightImg W' (imgMarkR xR ω s j) T - W' T) with hJ₁
  have hJ₁f : J₁.Finite := by
    simp only [hJ₁, forceJumpSet]
    exact ((Set.finite_range _).union (Set.finite_range _)).insert 0
  have hJf : (forceJumpSet vL' vR').Finite := by
    simp only [forceJumpSet]
    exact ((Set.finite_range _).union (Set.finite_range _)).insert 0
  refine ⟨E₁ ∪ J₁ ∪ forceJumpSet vL' vR' ∪ {chartAL W' T, chartAR W' T},
    ((hE₁.union hJ₁f).union hJf).union (by simp), fun x hx => ?_⟩
  simp only [mem_union, mem_insert_iff, mem_singleton_iff, not_or] at hx
  obtain ⟨⟨⟨hxE, hxJ₁⟩, hxJ⟩, hxAL, hxAR⟩ := hx
  have hx0 : x ≠ 0 := fun h => hxJ (by rw [h]; exact mem_insert _ _)
  have hxmL : ∀ i, x ≠ vL' i := fun i h => hxJ (Or.inr (Or.inl ⟨i, h.symm⟩))
  have hxmR : ∀ j, x ≠ vR' j := fun j h => hxJ (Or.inr (Or.inr ⟨j, h.symm⟩))
  rcases (extendFrom_im_nonneg hη' hW' hW'0 hT.le x).lt_or_eq with hpos | h0
  · -- a slit point: the prefix side
    have hxx := chartAL_lt_of_extendFrom_mem_H hη' hW' hW'0 hT.le hpos
    have hΘH : ∀ y ∈ H, imgTheta Wα t ω s W' T y ∈ H := fun y hy => by
      have hp := revChartInv_fwdMapInv_mem hω hω0 hs hW' hW'0 hT.le hK' hy
      exact QuantumZipper.FwdHolo.mapsTo_fwdMap hWα ht.le ⟨hp.1, fun h => hp.2 (Or.inl h)⟩
    obtain ⟨v₀, hv₀, hv₀t, hΦ, -⟩ := imgTheta_limits_of_slit hα hαp hWα hWα0 ht hKt hω hω0 hs hW' hW'0 hT hη' hη'p
      hGc hdisj hdis hK' htip hxx.1 hxx.2 hx0
    have hA' := (hFl v₀ hv₀ hv₀t).comp hΦ
    have hS : Tendsto (fun y => (uA (imgTheta Wα t ω s W' T y) -
          chiC κ * (logDerivFwd Wα t (revChartInv ω s (fwdMapInv W' T y))).im) -
        (u y - chiC κ * ((logDerivFwd W' T (fwdMapInv W' T y)).im +
          (logDerivPsi ω s (revChartInv ω s (fwdMapInv W' T y))).im))) (𝓝[H] (x : ℂ)) (𝓝 0) := by
      rcases lt_or_gt_of_ne hx0 with hneg | hpos'
      · exact tendsto_slit_left_of_bornWord hα hαp hWα hWα0 ht hKt hω hω0 hs hB hKs hjL hW' hW'0 hT hη' hη'p hGc
          hdisj hdis hK' htip hvR hvR' hpL huA hu (chiC κ) hxx.1 hneg hxmL
      · exact tendsto_slit_right_of_bornWord hα hαp hWα hWα0 ht hKt hω hω0 hs hB hKs hjR hW' hW'0 hT hη' hη'p hGc
          hdisj hdis hK' htip hvL hvL' hpR huA hu (chiC κ) hxx.2 hpos' hxmR
    have h := hA'.add hS
    rw [add_zero] at h
    refine h.congr fun y => ?_
    simp only [Function.comp_apply, imgTheta]
    ring
  · -- a physical real point: the root image word has the same data
    have hreal := h1 x hxE h0.symm
    have hdata : forceBoundaryData κ ρL₁ ρR₁ vL' vR' x =
        forceBoundaryData κ (imgRhoLT ρL θ κ) (imgRhoRT ρR θ κ)
          (fun i => -rightImg (fun r => -W' r) (-imgMarkL xL ω s i) T - W' T)
          (fun j => rightImg W' (imgMarkR xR ω s j) T - W' T) x := by
      rcases extendFrom_real_cases hη' hη'p hW' hW'0 hT h0.symm with ⟨-, h | h⟩ | ⟨-, h⟩ | ⟨-, h⟩
      · exact absurd h hxAL
      · exact absurd h hxAR
      · exact hphysR x h
      · exact hphysL x h
    have hu' := hu.2.2 x hxJ
    have hu₁' := hu₁.2.2 x hxJ₁
    rw [hdata] at hu'
    have h := hreal.add (hu₁'.sub hu')
    rw [sub_self, add_zero] at h
    refine h.congr fun y => ?_
    ring

/-- **The mean identification with a born-mark image word** (staged version of `Theta.eqOn_imgChartT`): under the
hypotheses of `exists_finite_tendsto_imgChart_bornWord`, a harmonic representative `w` of the union mean with
`M + θχ = w + 𝔥₀` satisfying Aux. 28's uniqueness on the component (`huniq`) is the candidate of the born-mark image
word in the joint chart: `w + 𝔥₀ = u ∘ f′_T ∘ Ψ − χ (arg f′_T′ ∘ Ψ + arg Ψ′)` on `ℍ ∖ (A ∪ G)`. -/
theorem eqOn_imgChart_bornWord {α : ℝ → ℂ} (hα : IsLoewnerTrace Wα α) (hαp : IsProperArc α)
    (hWα : Continuous Wα) (hWα0 : Wα 0 = 0) (ht : 0 < t)
    (hKt : ∀ x : ℝ, x ≠ 0 → (x : ℂ) ∉ closure (fwdHull Wα t)) (hκ : 0 < κ)
    (hω : Continuous ω) (hω0 : ω 0 = 0) (hs : 0 ≤ s) (hB : HasBdryLimits (fwdMapInv ω s))
    (hKs : ∀ z ∈ closure (fwdHull ω s), z.im = 0 → z = 0) (hjL : 0 < rightImg ω 0 s - ω s)
    (hjR : -rightImg (fun r => -ω r) 0 s - ω s < 0) (hGc : IsClosed (negInv '' fwdHull ω s))
    (hdisj : Disjoint (fwdHull Wα t) (negInv '' fwdHull ω s))
    (hdis : Disjoint (closure (fwdHull ω s)) (closure (negInv '' fwdHull Wα t)))
    (hxL : ∀ i, xL i ≤ 0) (hxR : ∀ j, 0 ≤ xR j) {M mG v : ℂ → ℝ}
    (hv : IsBoundedHarmonicExtension (cfDataAt κ (bDataT ρL ρR xL xR θ κ) (forceJumpFinset xL xR) ω s)
      (forceJumpSet (cfMarkL κ (bDataT ρL ρR xL xR θ κ) (forceJumpFinset xL xR) ω s)
        (cfMarkR κ (bDataT ρL ρR xL xR θ κ) (forceJumpFinset xL xR) ω s)) v)
    (hG : ∀ z₀ ∈ negInv '' fwdHull ω s ∪ {z : ℂ | z.im = 0},
      (∃ r > 0, fwdHull Wα t ∩ ball z₀ r ⊆ negInv '' fwdHull ω s) →
      Tendsto (fun z => M z - mG z) (𝓝[H \ (fwdHull Wα t ∪ negInv '' fwdHull ω s)] z₀) (𝓝 0))
    (hInf : Tendsto (fun z => M z - mG z)
      (Bornology.cobounded ℂ ⊓ 𝓟 (H \ (fwdHull Wα t ∪ negInv '' fwdHull ω s))) (𝓝 0))
    (hId : ∀ z ∈ H \ negInv '' fwdHull ω s, mG z + chiC κ * (logDerivPsi ω s z).im = retMean κ v (revChart ω s z))
    (hW' : Continuous W') (hW'0 : W' 0 = 0) {η' : ℝ → ℂ} (hη' : IsLoewnerTrace W' η') (hη'p : IsProperArc η')
    (hT : 0 < T) (hK' : fwdHull W' T = revChart ω s '' fwdHull Wα t) (htip : η' T = revChart ω s (α t))
    {ρL₁ : Fin mL → ℝ} {ρR₁ : Fin mR → ℝ} {vL vL' : Fin mL → ℝ} {vR vR' : Fin mR → ℝ}
    (hvL : ∀ i, vL i ≤ 0) (hvR : ∀ j, 0 ≤ vR j) (hvL' : ∀ i, vL' i ≤ 0) (hvR' : ∀ j, 0 ≤ vR' j)
    (hpL : ∀ i, IsBornPairL Wα α t ω s W' η' T (vL i) (vL' i))
    (hpR : ∀ j, IsBornPairR Wα α t ω s W' η' T (vR j) (vR' j)) {uA u : ℂ → ℝ}
    (huA : IsBoundedHarmonicExtension (forceBoundaryData κ ρL₁ ρR₁ vL vR) (forceJumpSet vL vR) uA)
    (hu : IsBoundedHarmonicExtension (forceBoundaryData κ ρL₁ ρR₁ vL' vR') (forceJumpSet vL' vR') u)
    (hphysL : ∀ x : ℝ, x < chartAL W' T → forceBoundaryData κ ρL₁ ρR₁ vL' vR' x =
      forceBoundaryData κ (imgRhoLT ρL θ κ) (imgRhoRT ρR θ κ)
        (fun i => -rightImg (fun r => -W' r) (-imgMarkL xL ω s i) T - W' T)
        (fun j => rightImg W' (imgMarkR xR ω s j) T - W' T) x)
    (hphysR : ∀ x : ℝ, chartAR W' T < x → forceBoundaryData κ ρL₁ ρR₁ vL' vR' x =
      forceBoundaryData κ (imgRhoLT ρL θ κ) (imgRhoRT ρR θ κ)
        (fun i => -rightImg (fun r => -W' r) (-imgMarkL xL ω s i) T - W' T)
        (fun j => rightImg W' (imgMarkR xR ω s j) T - W' T) x)
    (hFl : ∀ v : ℝ, 0 < v → v < t → Tendsto (fun z => M z + θ * chiC κ -
        (uA (fwdMap Wα t z) - chiC κ * (logDerivFwd Wα t z).im))
      (𝓝[H \ (fwdHull Wα t ∪ negInv '' fwdHull ω s)] (α v)) (𝓝 0))
    {w u₀ : ℂ → ℝ} (hMw : ∀ z, M z + θ * chiC κ = w z + u₀ z)
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
  obtain ⟨E, hE, hlim⟩ := exists_finite_tendsto_imgChart_bornWord ρL ρR θ hα hαp hWα hWα0 ht hKt hκ hω hω0 hs hB hKs
    hjL hjR hGc hdisj hdis hxL hxR hv hG hInf hId hW' hW'0 hη' hη'p hT hK' htip hvL hvR hvL' hvR' hpL hpR huA hu
    hphysL hphysR hFl
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

end InteractingSLE.Sec5.CrossCond.StagedLaw
