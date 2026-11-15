/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossCondStagedLawIdent

/-!
# The staged cross-conditioning law: the mean identification with slit data

Packet PROVE-CROSSCOND-STAGED4 (S2). PROVE-CROSSCOND-STAGED3's `StagedLaw.eqOn_imgChart_bornWord` reads the union mean
of `A_t ∪ G_s` in the joint chart as the bounded harmonic extension of an image word for a flow word and an image word
**with the same weights** whose side marks are paired. A staged prefix's flow word (the stop word in the prefix chart)
and its image word (the stage word in the joint chart) do not have the same marks off the slit: the image word also
carries the junction mark and the images of the root marks, which the flow word does not. Only the data **on the
slit** have to match. Here both sides are arbitrary piecewise boundary data:

* `tendsto_slit_of_slitData`: at an image slit point `x` (not an image jump), if the flow data at the `Θ`-limit `x₁`
  of `x` equal the image data at `x` (`hslit`), the candidate has the flow side's limit;
* `exists_finite_tendsto_imgChart_slitData`: off a finite set of image-chart real points the union-mean expression has
  the candidate's boundary limit (`hslit` on the slit, `hphys` — the image data are the root image word's data — off
  the closed slit);
* **`eqOn_imgChart_slitData`**: with Aux. 28's uniqueness, the union mean is the candidate of the image data:
  `w + 𝔥₀ = u ∘ f′_T ∘ Ψ − χ (arg f′_T′ ∘ Ψ + arg Ψ′)` on `ℍ ∖ (A ∪ G)`.

Deterministic. The proofs are STAGED3's with the force-word comparison (`forceBoundaryData_eq_of_neg`) replaced by the
hypothesis `hslit`. Conditional helpers with distinct names; R48: no Theorem 1.2/1.3 input.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv logDerivFwd chiC)
open QuantumZipper.RS (shiftDrive)
open QuantumZipper.CA (cayley cayleyInv)
open SupercriticalConformalCovariance (IsConformalBijection)
open scoped Real

namespace InteractingSLE.Sec5.CrossCond.StagedFinal

open WangWu hiding ratPt exists_ratPt_dist_lt
open GlueImg Theta Cond44Ref Word49 Sec7.StripSysField StagedLaw
open MartChar.RealFlow Restart.RetAux79

section Slit

variable {Wα Wβ W' : ℝ → ℝ} {t s T : ℝ}

/-- **The candidate at an image slit point with matching slit data.** If the flow data `b_A` at the `Θ`-limit `x₁` of an
image slit point `x` equal the image data `b′` at `x` and `x₁` is not a flow jump (`hslit`), then
`u_A ∘ Θ − χ arg f_t′ ∘ Φ − (u − χ (arg f′_T′ + arg Ψ′ ∘ Φ)) → 0` at `x`. -/
theorem tendsto_slit_of_slitData {α : ℝ → ℂ} (hα : IsLoewnerTrace Wα α) (hαp : IsProperArc α)
    (hWα : Continuous Wα) (hWα0 : Wα 0 = 0) (ht : 0 < t) (hKt : ∀ x : ℝ, x ≠ 0 → (x : ℂ) ∉ closure (fwdHull Wα t))
    (hWβ : Continuous Wβ) (hWβ0 : Wβ 0 = 0) (hs : 0 ≤ s) (hB : HasBdryLimits (fwdMapInv Wβ s))
    (hKs : ∀ z ∈ closure (fwdHull Wβ s), z.im = 0 → z = 0) (hjL : 0 < rightImg Wβ 0 s - Wβ s)
    (hjR : -rightImg (fun r => -Wβ r) 0 s - Wβ s < 0)
    (hW' : Continuous W') (hW'0 : W' 0 = 0) (hT : 0 < T) {η' : ℝ → ℂ} (hη' : IsLoewnerTrace W' η')
    (hη'p : IsProperArc η') (hGc : IsClosed (negInv '' fwdHull Wβ s))
    (hdisj : Disjoint (fwdHull Wα t) (negInv '' fwdHull Wβ s))
    (hdis : Disjoint (closure (fwdHull Wβ s)) (closure (negInv '' fwdHull Wα t)))
    (hK' : fwdHull W' T = revChart Wβ s '' fwdHull Wα t) (htip : η' T = revChart Wβ s (α t))
    {bA b' : ℝ → ℝ} {JA J' : Set ℝ} {uA u : ℂ → ℝ} (huA : IsBoundedHarmonicExtension bA JA uA)
    (hu : IsBoundedHarmonicExtension b' J' u) (χ : ℝ)
    (hslit : ∀ x x₁ : ℝ, x ∉ J' → chartAL W' T < x → x < chartAR W' T → x ≠ 0 →
      Tendsto (imgTheta Wα t Wβ s W' T) (𝓝[H] (x : ℂ)) (𝓝 (x₁ : ℂ)) → x₁ ∉ JA ∧ bA x₁ = b' x)
    {x : ℝ} (hxJ : x ∉ J') (hxL : chartAL W' T < x) (hxR : x < chartAR W' T) (hx0 : x ≠ 0) :
    Tendsto (fun y => (uA (imgTheta Wα t Wβ s W' T y) -
        χ * (logDerivFwd Wα t (revChartInv Wβ s (fwdMapInv W' T y))).im) -
      (u y - χ * ((logDerivFwd W' T (fwdMapInv W' T y)).im +
        (logDerivPsi Wβ s (revChartInv Wβ s (fwdMapInv W' T y))).im))) (𝓝[H] (x : ℂ)) (𝓝 0) := by
  have hlim : ∃ x₁ : ℝ, Tendsto (imgTheta Wα t Wβ s W' T) (𝓝[H] (x : ℂ)) (𝓝 (x₁ : ℂ)) ∧
      Tendsto (imgBranch Wα t Wβ s W' T) (𝓝[H] (x : ℂ)) (𝓝 0) := by
    rcases lt_or_gt_of_ne hx0 with hneg | hpos
    · obtain ⟨x₁, -, -, hΘ, hbr⟩ := slit_left_limits hα hαp hWα hWα0 ht hKt hWβ hWβ0 hs hB hKs hjL hW' hW'0 hT
        hη' hη'p hGc hdisj hdis hK' htip hxL hneg
      exact ⟨x₁, hΘ, hbr⟩
    · obtain ⟨x₁, -, -, hΘ, hbr⟩ := slit_right_limits hα hαp hWα hWα0 ht hKt hWβ hWβ0 hs hB hKs hjR hW' hW'0 hT
        hη' hη'p hGc hdisj hdis hK' htip hxR hpos
      exact ⟨x₁, hΘ, hbr⟩
  obtain ⟨x₁, hΘ, hbr⟩ := hlim
  obtain ⟨hx₁J, hd⟩ := hslit x x₁ hxJ hxL hxR hx0 hΘ
  have hΘH : ∀ y ∈ H, imgTheta Wα t Wβ s W' T y ∈ H := fun y hy => by
    have hp := revChartInv_fwdMapInv_mem hWβ hWβ0 hs hW' hW'0 hT.le hK' hy
    exact QuantumZipper.FwdHolo.mapsTo_fwdMap hWα ht.le ⟨hp.1, fun h => hp.2 (Or.inl h)⟩
  have hΘ' : Tendsto (imgTheta Wα t Wβ s W' T) (𝓝[H] (x : ℂ)) (𝓝[H] (x₁ : ℂ)) :=
    tendsto_nhdsWithin_iff.2 ⟨hΘ, eventually_nhdsWithin_of_forall hΘH⟩
  have h1 := (huA.2.2 x₁ hx₁J).comp hΘ'
  have h2 := hu.2.2 x hxJ
  have h := (h1.sub h2).sub (hbr.const_mul χ)
  rw [hd, sub_self, mul_zero, sub_zero] at h
  refine h.congr fun y => ?_
  simp only [Function.comp_apply, imgBranch]
  ring

end Slit
section Ident

variable {Wα ω W' : ℝ → ℝ} {t s T : ℝ} {κ : ℝ} {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (θ : ℝ)
  {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}

/-- **The per-point limits of the candidate with slit data** (slit-data version of
`StagedLaw.exists_finite_tendsto_imgChart_bornWord`). The flow side is any bounded harmonic extension `u_A` of data
`b_A`; the image side is any bounded harmonic extension `u` of data `b′` with a finite jump set `J′`, agreeing with the
flow data on the slit (`hslit`) and with the root image word of CROSSCOND-THETA off the closed slit (`hphys`). Off a
finite set of image-chart real points, the union-mean expression has the candidate's boundary limit. -/
theorem exists_finite_tendsto_imgChart_slitData {α : ℝ → ℂ} (hα : IsLoewnerTrace Wα α) (hαp : IsProperArc α)
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
    {bA b' : ℝ → ℝ} {JA J' : Set ℝ} (hJ' : J'.Finite) {uA u : ℂ → ℝ}
    (huA : IsBoundedHarmonicExtension bA JA uA) (hu : IsBoundedHarmonicExtension b' J' u)
    (hslit : ∀ x x₁ : ℝ, x ∉ J' → chartAL W' T < x → x < chartAR W' T → x ≠ 0 →
      Tendsto (imgTheta Wα t ω s W' T) (𝓝[H] (x : ℂ)) (𝓝 (x₁ : ℂ)) → x₁ ∉ JA ∧ bA x₁ = b' x)
    (hphys : ∀ x : ℝ, x ∉ J' → (x < chartAL W' T ∨ chartAR W' T < x) → b' x =
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
  refine ⟨E₁ ∪ J₁ ∪ J' ∪ {0, chartAL W' T, chartAR W' T},
    ((hE₁.union hJ₁f).union hJ').union (by simp), fun x hx => ?_⟩
  simp only [mem_union, mem_insert_iff, mem_singleton_iff, not_or] at hx
  obtain ⟨⟨⟨hxE, hxJ₁⟩, hxJ⟩, hx0, hxAL, hxAR⟩ := hx
  rcases (extendFrom_im_nonneg hη' hW' hW'0 hT.le x).lt_or_eq with hpos | h0
  · -- a slit point: the prefix side
    have hxx := chartAL_lt_of_extendFrom_mem_H hη' hW' hW'0 hT.le hpos
    obtain ⟨v₀, hv₀, hv₀t, hΦ, -⟩ := imgTheta_limits_of_slit hα hαp hWα hWα0 ht hKt hω hω0 hs hW' hW'0 hT hη' hη'p
      hGc hdisj hdis hK' htip hxx.1 hxx.2 hx0
    have hA' := (hFl v₀ hv₀ hv₀t).comp hΦ
    have hS := tendsto_slit_of_slitData hα hαp hWα hWα0 ht hKt hω hω0 hs hB hKs hjL hjR hW' hW'0 hT hη' hη'p hGc
      hdisj hdis hK' htip huA hu (chiC κ) hslit hxJ hxx.1 hxx.2 hx0
    have h := hA'.add hS
    rw [add_zero] at h
    refine h.congr fun y => ?_
    simp only [Function.comp_apply, imgTheta]
    ring
  · -- a physical real point: the root image word has the same data
    have hreal := h1 x hxE h0.symm
    have hdata : b' x =
        forceBoundaryData κ (imgRhoLT ρL θ κ) (imgRhoRT ρR θ κ)
          (fun i => -rightImg (fun r => -W' r) (-imgMarkL xL ω s i) T - W' T)
          (fun j => rightImg W' (imgMarkR xR ω s j) T - W' T) x := by
      rcases extendFrom_real_cases hη' hη'p hW' hW'0 hT h0.symm with ⟨-, h | h⟩ | ⟨-, h⟩ | ⟨-, h⟩
      · exact absurd h hxAL
      · exact absurd h hxAR
      · exact hphys x hxJ (Or.inr h)
      · exact hphys x hxJ (Or.inl h)
    have hu' := hu.2.2 x hxJ
    have hu₁' := hu₁.2.2 x hxJ₁
    rw [hdata] at hu'
    have h := hreal.add (hu₁'.sub hu')
    rw [sub_self, add_zero] at h
    refine h.congr fun y => ?_
    ring

/-- **The mean identification with slit data** (slit-data version of `StagedLaw.eqOn_imgChart_bornWord`): under the
hypotheses of `exists_finite_tendsto_imgChart_slitData`, a harmonic representative `w` of the union mean with
`M + θχ = w + 𝔥₀` satisfying Aux. 28's uniqueness on the component (`huniq`) is the candidate of the image data in the
joint chart: `w + 𝔥₀ = u ∘ f′_T ∘ Ψ − χ (arg f′_T′ ∘ Ψ + arg Ψ′)` on `ℍ ∖ (A ∪ G)`. -/
theorem eqOn_imgChart_slitData {α : ℝ → ℂ} (hα : IsLoewnerTrace Wα α) (hαp : IsProperArc α)
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
    {bA b' : ℝ → ℝ} {JA J' : Set ℝ} (hJ' : J'.Finite) {uA u : ℂ → ℝ}
    (huA : IsBoundedHarmonicExtension bA JA uA) (hu : IsBoundedHarmonicExtension b' J' u)
    (hslit : ∀ x x₁ : ℝ, x ∉ J' → chartAL W' T < x → x < chartAR W' T → x ≠ 0 →
      Tendsto (imgTheta Wα t ω s W' T) (𝓝[H] (x : ℂ)) (𝓝 (x₁ : ℂ)) → x₁ ∉ JA ∧ bA x₁ = b' x)
    (hphys : ∀ x : ℝ, x ∉ J' → (x < chartAL W' T ∨ chartAR W' T < x) → b' x =
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
  obtain ⟨E, hE, hlim⟩ := exists_finite_tendsto_imgChart_slitData ρL ρR θ hα hαp hWα hWα0 ht hKt hκ hω hω0 hs hB hKs
    hjL hjR hGc hdisj hdis hxL hxR hv hG hInf hId hW' hW'0 hη' hη'p hT hK' htip hJ' huA hu hslit hphys hFl
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

end InteractingSLE.Sec5.CrossCond.StagedFinal
