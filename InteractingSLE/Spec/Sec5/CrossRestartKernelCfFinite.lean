/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossRestartKernelCfBase
import InteractingSLE.Spec.Sec5.CrossRestartKernelSlitFinite
import InteractingSLE.Spec.Sec5.GlueCondUnionImgAssembly

/-!
# Lemma 4.7's direction, items (B)–(C) combined: the union mean's boundary values in the image chart, off a finite set

Packet PROVE-CFRESTART2. In the setting `IsCfImgSetup` (new curve: the non-simple counterflow, driver `Wα`; obstacle:
the simple flow slit `R(K^{Wβ}_s)`; image chain `W′`), the image word at parameter `16/κ` is the counterflow word
`(ρL, ρR; xL, xR)` mapped by `Ψ` with the two junction marks (`imgMarkL`, `imgMarkR`, weights `slitRhoL`, `slitRhoR` —
the word fixed by PROVE-CFRESTART-C's `SlitSideStatement`). **`exists_finite_tendsto_imgChart_restart`**: if the
union-mean expression `M + c` is asymptotic

* near the flow slit and the physical real line away from the counterflow hull to the obstacle mean `mG` (with the
  chart identity `hId`, the hypotheses of `SlitSideStatement`), and
* at every point of the counterflow hull to the counterflow's coupling mean `𝔥_t = uA ∘ f_t − χ′ arg f_t′`,

then off a finite set of real image-chart points `M ∘ Φ + c − (u − χ′ (Im L′_T ∘ F′_T + arg_Ψ ∘ Φ)) → 0`, `u` the
bounded harmonic extension of the image word's data at `T`. Points with a real inverse boundary value are
`slitSideStatement`'s; the others lie over the open base interval of the image hull, where
`IsCfImgSetup.tendsto_imgChart_of_mem_base` applies (the exceptional points added are the two base points and the
image tip).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped NNReal Real

open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv logDerivFwd chiC)

namespace InteractingSLE.Sec5.CrossRestart

open WangWu hiding ratPt exists_ratPt_dist_lt
open MartChar.RealFlow Restart.RetAux79 GlueCond Sec7.StripSysField Cond44Ref GlueImg
open CrossCond.Theta
open QuantumZipper.CA (cayley cayleyInv)
open SupercriticalConformalCovariance (IsConformalBijection)

namespace IsCfImgSetup

variable {Wα Wβ W' : ℝ → ℝ} {α β η' : ℝ → ℂ} {t s T : ℝ}

/-- **The union mean's boundary values in the image chart, off a finite set** (Lemma 4.7's direction; both sides). -/
theorem exists_finite_tendsto_imgChart_restart (hd : IsCfImgSetup Wα α t Wβ s W' η' T) {κ : ℝ} (hκ : 0 < κ)
    (hκ4 : κ < 4) (θ : ℝ) (hs : 0 < s) (hβ : IsLoewnerTrace Wβ β) (hβp : IsProperArc β)
    {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ)
    (hxL : ∀ i, xL i ≤ 0) (hxR : ∀ j, 0 ≤ xR j) {M mG v uA u : ℂ → ℝ} {c : ℝ}
    -- the flow-slit side (the hypotheses of `SlitSideStatement`)
    (hv : IsBoundedHarmonicExtension
      (cfDataAt (16 / κ) (bDataT ρL ρR xL xR (-θ) (16 / κ)) (forceJumpFinset xL xR) Wβ s)
      (forceJumpSet
        (cfMarkL (16 / κ) (bDataT ρL ρR xL xR (-θ) (16 / κ)) (forceJumpFinset xL xR) Wβ s)
        (cfMarkR (16 / κ) (bDataT ρL ρR xL xR (-θ) (16 / κ)) (forceJumpFinset xL xR) Wβ s)) v)
    (hG : ∀ z₀ ∈ negInv '' fwdHull Wβ s ∪ {z : ℂ | z.im = 0},
      (∃ r > 0, fwdHull Wα t ∩ ball z₀ r ⊆ negInv '' fwdHull Wβ s) →
      Tendsto (fun z => M z - mG z) (𝓝[H \ (fwdHull Wα t ∪ negInv '' fwdHull Wβ s)] z₀) (𝓝 0))
    (hInf : Tendsto (fun z => M z - mG z)
      (Bornology.cobounded ℂ ⊓ 𝓟 (H \ (fwdHull Wα t ∪ negInv '' fwdHull Wβ s))) (𝓝 0))
    (hId : ∀ z ∈ H \ negInv '' fwdHull Wβ s,
      mG z + chiC (16 / κ) * (logDerivPsi Wβ s z).im + c =
        retMean (16 / κ) v (revChart Wβ s z) + (-θ) * chiC (16 / κ))
    -- the counterflow side
    (huA : IsBoundedHarmonicExtension
      (forceBoundaryData (16 / κ) ρL ρR (fun i => -rightImg (fun r => -Wα r) (-xL i) t - Wα t)
        (fun j => rightImg Wα (xR j) t - Wα t))
      (forceJumpSet (fun i => -rightImg (fun r => -Wα r) (-xL i) t - Wα t)
        (fun j => rightImg Wα (xR j) t - Wα t)) uA)
    (hA : ∀ z₀ ∈ fwdHull Wα t, Tendsto (fun z => M z + c - couplingMean (16 / κ) Wα t uA z)
      (𝓝[H \ (fwdHull Wα t ∪ negInv '' fwdHull Wβ s)] z₀) (𝓝 0))
    -- the image word
    (hu : IsBoundedHarmonicExtension
      (forceBoundaryData (16 / κ) (slitRhoL ρL κ θ) (slitRhoR ρR κ θ)
        (fun i => -rightImg (fun r => -W' r) (-imgMarkL xL Wβ s i) T - W' T)
        (fun j => rightImg W' (imgMarkR xR Wβ s j) T - W' T))
      (forceJumpSet (fun i => -rightImg (fun r => -W' r) (-imgMarkL xL Wβ s i) T - W' T)
        (fun j => rightImg W' (imgMarkR xR Wβ s j) T - W' T)) u) :
    ∃ E : Set ℝ, E.Finite ∧ ∀ x : ℝ, x ∉ E →
      Tendsto (fun y => M (revChartInv Wβ s (fwdMapInv W' T y)) + c -
        (u y - chiC (16 / κ) * ((logDerivFwd W' T (fwdMapInv W' T y)).im +
          (logDerivPsi Wβ s (revChartInv Wβ s (fwdMapInv W' T y))).im))) (𝓝[H] (x : ℂ)) (𝓝 0) := by
  obtain ⟨E₁, hE₁, hslit⟩ := slitSideStatement κ hκ hκ4 θ hd.hWα hd.hWα0 hd.ht hd.hα hd.hαH hd.hWβ hd.hWβ0 hs hβ
    hβp hd.hdisj hd.hW' hd.hW'0 hd.hT hd.hη' hd.hη'H hd.hK' ρL ρR xL xR hxL hxR M mG v c hv hG hInf hId hu
  refine ⟨E₁ ∪ {chartAL W' T, 0, chartAR W' T}, hE₁.union (by simp), fun x hx => ?_⟩
  have hx₁ : x ∉ E₁ := fun h => hx (Or.inl h)
  have hxL' : x ≠ chartAL W' T := fun h => hx (Or.inr (by simp [h]))
  have hx0 : x ≠ 0 := fun h => hx (Or.inr (by simp [h]))
  have hxR' : x ≠ chartAR W' T := fun h => hx (Or.inr (by simp [h]))
  by_cases him : (extendFrom H (fwdMapInv W' T) x).im = 0
  · exact hslit x hx₁ him
  · have hxI : x ∈ Ioo (chartAL W' T) (chartAR W' T) := by
      refine ⟨lt_of_le_of_ne (not_lt.1 fun h => him ?_) hxL'.symm,
        lt_of_le_of_ne (not_lt.1 fun h => him ?_) hxR'⟩
      · exact (re_extendFrom_neg_of_lt_chartAL_of_mem_H hd.hη' hd.hη'H hd.hW' hd.hW'0 hd.hT.le h).1
      · exact (re_extendFrom_pos_of_chartAR_lt_of_mem_H hd.hη' hd.hη'H hd.hW' hd.hW'0 hd.hT.le h).1
    exact hd.tendsto_imgChart_of_mem_base hxL hxR (imgMarkL_nonpos hd.hWβ hd.hs hd.hjL hxL)
      (imgMarkR_nonneg hd.hWβ hd.hs hd.hjR hxR) huA hu hA hxI hx0

/-- **The union mean in the image chart** (Lemma 4.7's direction; deterministic form of the identification). In the
setting of `exists_finite_tendsto_imgChart_restart`, let `w` be a function on `C = ℍ ∖ (A ∪ G)` with
`M + c = w + u₀`, for which the uniqueness statement of Aux. 28 on `C` holds (`huniq`, the per-sample conclusion of
`Sec6.ae_eqOn_component_of_tendsto_global` with `v = w`, `F = u₀`). Then on `C`,
`w + u₀ = u ∘ f′_T ∘ Ψ − χ′ (Im L′_T ∘ Ψ + arg_Ψ)`. (GLUECOND10's `GlueImg.eqOn_imgChart` with the roles of the two
curves exchanged; no simple curve except the obstacle.) -/
theorem eqOn_imgChart_restart (hd : IsCfImgSetup Wα α t Wβ s W' η' T) {κ : ℝ} (hκ : 0 < κ)
    (hκ4 : κ < 4) (θ : ℝ) (hs : 0 < s) (hβ : IsLoewnerTrace Wβ β) (hβp : IsProperArc β)
    {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ)
    (hxL : ∀ i, xL i ≤ 0) (hxR : ∀ j, 0 ≤ xR j) {M mG v uA u : ℂ → ℝ} {c : ℝ}
    -- the flow-slit side (the hypotheses of `SlitSideStatement`)
    (hv : IsBoundedHarmonicExtension
      (cfDataAt (16 / κ) (bDataT ρL ρR xL xR (-θ) (16 / κ)) (forceJumpFinset xL xR) Wβ s)
      (forceJumpSet
        (cfMarkL (16 / κ) (bDataT ρL ρR xL xR (-θ) (16 / κ)) (forceJumpFinset xL xR) Wβ s)
        (cfMarkR (16 / κ) (bDataT ρL ρR xL xR (-θ) (16 / κ)) (forceJumpFinset xL xR) Wβ s)) v)
    (hG : ∀ z₀ ∈ negInv '' fwdHull Wβ s ∪ {z : ℂ | z.im = 0},
      (∃ r > 0, fwdHull Wα t ∩ ball z₀ r ⊆ negInv '' fwdHull Wβ s) →
      Tendsto (fun z => M z - mG z) (𝓝[H \ (fwdHull Wα t ∪ negInv '' fwdHull Wβ s)] z₀) (𝓝 0))
    (hInf : Tendsto (fun z => M z - mG z)
      (Bornology.cobounded ℂ ⊓ 𝓟 (H \ (fwdHull Wα t ∪ negInv '' fwdHull Wβ s))) (𝓝 0))
    (hId : ∀ z ∈ H \ negInv '' fwdHull Wβ s,
      mG z + chiC (16 / κ) * (logDerivPsi Wβ s z).im + c =
        retMean (16 / κ) v (revChart Wβ s z) + (-θ) * chiC (16 / κ))
    -- the counterflow side
    (huA : IsBoundedHarmonicExtension
      (forceBoundaryData (16 / κ) ρL ρR (fun i => -rightImg (fun r => -Wα r) (-xL i) t - Wα t)
        (fun j => rightImg Wα (xR j) t - Wα t))
      (forceJumpSet (fun i => -rightImg (fun r => -Wα r) (-xL i) t - Wα t)
        (fun j => rightImg Wα (xR j) t - Wα t)) uA)
    (hA : ∀ z₀ ∈ fwdHull Wα t, Tendsto (fun z => M z + c - couplingMean (16 / κ) Wα t uA z)
      (𝓝[H \ (fwdHull Wα t ∪ negInv '' fwdHull Wβ s)] z₀) (𝓝 0))
    -- the image word
    (hu : IsBoundedHarmonicExtension
      (forceBoundaryData (16 / κ) (slitRhoL ρL κ θ) (slitRhoR ρR κ θ)
        (fun i => -rightImg (fun r => -W' r) (-imgMarkL xL Wβ s i) T - W' T)
        (fun j => rightImg W' (imgMarkR xR Wβ s j) T - W' T))
      (forceJumpSet (fun i => -rightImg (fun r => -W' r) (-imgMarkL xL Wβ s i) T - W' T)
        (fun j => rightImg W' (imgMarkR xR Wβ s j) T - W' T)) u) 
    {w u₀ : ℂ → ℝ} (hMw : ∀ z, M z + c = w z + u₀ z)
    (huniq : ∀ z₀ ∈ H \ (fwdHull Wα t ∪ negInv '' fwdHull Wβ s), ∀ (f φc : ℂ → ℂ) (G L : ℂ → ℝ) (E : Set ℂ),
      IsConformalBijection f (ball 0 1) (connectedComponentIn (H \ (fwdHull Wα t ∪ negInv '' fwdHull Wβ s)) z₀) →
      IsConformalBijection φc (connectedComponentIn (H \ (fwdHull Wα t ∪ negInv '' fwdHull Wβ s)) z₀)
        {w : ℂ | 0 < w.im} →
      InnerProductSpace.HarmonicOnNhd G {w : ℂ | 0 < w.im} →
      (∃ M, ∀ w : ℂ, 0 < w.im → |G w| ≤ M) →
      ContinuousOn L (connectedComponentIn (H \ (fwdHull Wα t ∪ negInv '' fwdHull Wβ s)) z₀) →
      (∀ z ∈ connectedComponentIn (H \ (fwdHull Wα t ∪ negInv '' fwdHull Wβ s)) z₀,
        deriv φc z = ‖deriv φc z‖ * exp (L z * I)) →
      E.Finite →
      (∀ q ∈ sphere (0 : ℂ) 1, q ∉ E →
        Tendsto (fun ζ => (w (f ζ) + u₀ (f ζ)) - (G (φc (f ζ)) - chiC (16 / κ) * L (f ζ))) (𝓝[ball 0 1] q)
          (𝓝 0)) →
      ∀ z ∈ connectedComponentIn (H \ (fwdHull Wα t ∪ negInv '' fwdHull Wβ s)) z₀,
        w z + u₀ z = G (φc z) - chiC (16 / κ) * L z) :
    ∀ z ∈ H \ (fwdHull Wα t ∪ negInv '' fwdHull Wβ s), w z + u₀ z =
      u (fwdMap W' T (revChart Wβ s z)) -
        chiC (16 / κ) * ((logDerivFwd W' T (revChart Wβ s z)).im + (logDerivPsi Wβ s z).im) := by
  obtain ⟨E, hE, hlim⟩ := hd.exists_finite_tendsto_imgChart_restart hκ hκ4 θ hs hβ hβp ρL ρR xL xR hxL hxR hv hG
    hInf hId huA hA hu
  have hAG : fwdHull Wα t ⊆ H \ negInv '' fwdHull Wβ s := fun z hz =>
    ⟨(QuantumZipper.fwdHull_mono (W := Wα)).2 t hz, fun h => disjoint_left.1 hd.hdisj hz h⟩
  have hΦ := isConformalBijection_imgPhiChart hd.hWβ hd.hWβ0 hd.hs hd.hW' hd.hW'0 hd.hT.le hAG hd.hK'
  have hφc := isConformalBijection_imgFwdChart hd.hWβ hd.hWβ0 hd.hs hd.hW' hd.hW'0 hd.hT.le hAG hd.hK'
  obtain ⟨hLc, hder⟩ := deriv_imgFwdChart_eq hd.hWα hd.ht.le hd.hWβ hd.hWβ0 hd.hs hd.hGc hd.hW' hd.hT.le hAG hd.hK'
  have hIH : I ∈ H := show (0 : ℝ) < I.im by simp
  have hz₀ := hΦ.2.mapsTo hIH
  have hcc := connectedComponentIn_H_diff_union hd.hWβ hd.hWβ0 hd.hs hd.hW' hd.hW'0 hd.hT.le hAG hd.hK' hz₀
  have hf := isConformalBijection_comp hΦ isConformalBijection_cayleyInv
  have hφ : ∀ y ∈ H, fwdMap W' T (revChart Wβ s (revChartInv Wβ s (fwdMapInv W' T y))) = y := fun y hy => by
    rw [revChart_revChartInv hd.hWβ hd.hWβ0 hd.hs (QuantumZipper.RS.fwdMapInv_mem_H hd.hW' hd.hW'0 hd.hT.le hy),
      QuantumZipper.RS.fwdMap_fwdMapInv hd.hW' hd.hW'0 hd.hT.le hy]
  have hdisk := tendsto_disk_of_imgChart (v := w) (F := u₀) (G := u) (χ := chiC (16 / κ))
    (φc := fun z => fwdMap W' T (revChart Wβ s z))
    (L := fun z => (logDerivFwd W' T (revChart Wβ s z)).im + (logDerivPsi Wβ s z).im) hlim
    (fun y _ => (hMw _).symm) hφ (fun y hy => by
      simp only [revChart_revChartInv hd.hWβ hd.hWβ0 hd.hs
        (QuantumZipper.RS.fwdMapInv_mem_H hd.hW' hd.hW'0 hd.hT.le hy)])
  have hEd : (insert (1 : ℂ) ((fun w : ℝ => cayley (w : ℂ)) '' E)).Finite := (hE.image _).insert 1
  have key := huniq _ hz₀
  rw [hcc] at key
  exact key _ _ u (fun z => (logDerivFwd W' T (revChart Wβ s z)).im + (logDerivPsi Wβ s z).im) _
    hf hφc hu.1 hu.2.1 hLc hder hEd hdisk

end IsCfImgSetup

end InteractingSLE.Sec5.CrossRestart
