/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossCondStagedFinalPast

/-!
# Proposition 5.9 at depth `ℓ`: the staged image-chart identification on one glued sample

Packet PROVE-STAGED-DEPTH (S2, per sample). On the glued space of PROVE-GLUECOND / CROSSCOND-THETA, take for the flow
side an arbitrary driver process `W` on `Ω` (for Prop 5.9: the concatenated driver of a fixed extreme-angle schedule)
and read its trace `α = seedLine ζ W p.1` through the counterflow chart `Ψ = revChart (cfDrv0 s p.2) s`. The image
curve `γ = gCurve s ζ W E p` is a killed arc (`isKilledArc_gCurve`); its capacity clock gives the image times.

* `eq_of_image_Ioc_eq`: two injective arcs whose initial images `η((0, r])` agree for every `r ≤ A` agree at `A`;
* **`exists_imgChain_capClock`**: on a good glued sample, at every pre-contact own time `t > 0` there is an image
  chain `(W', η', T)` of the prefix `α((0, t])` with `T = capClock γ t`, `W' = chainDrv γ P` on `[0, T]`, and at every
  earlier own time `S ∈ (0, t)` the image trace passes through `Ψ(α(S))` at the image time `capClock γ S`;
* **`stage_imgChart_sample`**: the per-sample staged identification of PROVE-CROSSCOND-STAGED4
  (`StagedFinal.eqOn_imgChart_pastWord`) instantiated on a good glued sample: the union mean `w + u₀` equals the image
  stage word's candidate in the chart `Ψ`, the image chain being the canonical one of the killed arc `γ` and the switch
  image times being `capClock γ (startT m)`;
* `stage_integral_sample`: the same identity integrated against a test function supported off the union.

Deterministic helpers with distinct names; they replace no source theorem. R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology Complex
open scoped NNReal ENNReal Real
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv logDerivFwd chiC)
open QuantumZipper.RS (shiftDrive)
open SupercriticalConformalCovariance (IsConformalBijection)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Sec5.CrossCond.StagedDepth

open WangWu hiding ratPt exists_ratPt_dist_lt
open WangWu.ImgWord LawUnique GlueCond Cond44Ref CfRegQ Prop411Q WholeField LocalSets
open ImgDrv MartChar MartChar.RealFlow Restart.RetAux79 Sec7.StripSysField GlueImg Word49 Theta StagedFinal
open Restart Exist.StagedLaw Exist.Staged Staged Theorem14.GW2Schedule
open Sec7.Lemma71C (capClock)

/-! ### Two injective arcs with the same initial images -/

/-- **Two injective arcs with the same initial images agree at the end**: if `η((0, r]) = η'((0, r])` for every
`r ∈ (0, A]`, then `η(A) = η'(A)`. (The point `η'(A)` is some `η(u)`, `u ≤ A`; if `u < A`, then `η(u) = η'(v)` with
`v ≤ u < A`, against the injectivity of `η'`.) -/
theorem eq_of_image_Ioc_eq {η η' : ℝ → ℂ} (hinj' : InjOn η' (Ici 0)) {A : ℝ} (hA : 0 < A)
    (h : ∀ r ∈ Ioc (0 : ℝ) A, η '' Ioc 0 r = η' '' Ioc 0 r) : η A = η' A := by
  have h1 : η' A ∈ η '' Ioc 0 A := by
    rw [h A ⟨hA, le_rfl⟩]
    exact ⟨A, ⟨hA, le_rfl⟩, rfl⟩
  obtain ⟨u, hu, hu'⟩ := h1
  rcases hu.2.lt_or_eq with hlt | heq
  · exfalso
    have h2 : η u ∈ η' '' Ioc 0 u := by
      rw [← h u ⟨hu.1, hu.2⟩]
      exact ⟨u, ⟨hu.1, le_rfl⟩, rfl⟩
    obtain ⟨v, hv, hv'⟩ := h2
    have hvA : v = A := hinj' (mem_Ici.2 hv.1.le) (mem_Ici.2 hA.le) (hv'.trans hu')
    linarith [hv.2]
  · rw [heq] at hu'
    exact hu'

/-! ### A boundary word shifted by a constant -/

section VShift

/-- **A boundary word shifted by a constant `a`**: same jump positions, every height `+ a`. -/
def vshift (c : BoundaryWord) (a : ℝ) : BoundaryWord := (c.1, c.2.1, fun j => c.2.2 j + a)

theorem vshift_fn (c : BoundaryWord) (a y : ℝ) : (vshift c a).fn y = c.fn y + a := rfl

theorem vshift_jumps (c : BoundaryWord) (a : ℝ) : (vshift c a).jumps = c.jumps := rfl

theorem isSorted_vshift {c : BoundaryWord} (hc : c.IsSorted) (a : ℝ) : (vshift c a).IsSorted := hc

/-- The mean of a shifted word is the shifted mean. -/
theorem mean_vshift (c : BoundaryWord) (a : ℝ) (z : ℂ) : (vshift c a).mean z = c.mean z + a := by
  simp only [BoundaryWord.mean, vshift, add_sub_add_right_eq_sub]
  ring

theorem IsLeftLevels.vshift {c : BoundaryWord} {k : ℕ} {p ht : ℕ → ℝ} (h : IsLeftLevels c k p ht) (a : ℝ) :
    IsLeftLevels (vshift c a) k p (fun j => ht j + a) :=
  ⟨h.1, h.2.1, h.2.2.1, fun j hj y h1 h2 h3 => by rw [vshift_fn, h.2.2.2 j hj y h1 h2 h3]⟩

theorem IsRightLevels.vshift {c : BoundaryWord} {k : ℕ} {q ht : ℕ → ℝ} (h : IsRightLevels c k q ht) (a : ℝ) :
    IsRightLevels (vshift c a) k q (fun j => ht j + a) :=
  ⟨h.1, h.2.1, h.2.2.1, fun j hj y h1 h2 h3 => by rw [vshift_fn, h.2.2.2 j hj y h1 h2 h3]⟩

end VShift

/-! ### The canonical image chain of a good glued sample -/

section Chain

variable {Ω : Type*} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {s : ℝ≥0} {E : Set (Ω × HistorySpace 0 0)}

/-- **The canonical image chain of the prefix on a good glued sample.** At a pre-contact own time `t > 0` of the flow
trace `α = seedLine ζ W p.1` (a Loewner trace of `Wα`), the image `Ψ(α((0, t]))` in the counterflow chart is the hull at
the image time `capClock γ t > 0` of a continuous driver `W'` equal to the killed arc's chain driver on
`[0, capClock γ t]`,
whose trace `η'` is a proper arc ending at `Ψ(α(t))`; at every earlier own time `S ∈ (0, t)` the image trace passes
through `Ψ(α(S))` at the image time `capClock γ S ∈ (0, capClock γ t)`. -/
theorem exists_imgChain_capClock (hEg : ∀ p ∈ E, IsGood49 s ζ W p) {p : Ω × HistorySpace 0 0} (hp : p ∈ E)
    {t : ℝ} (ht : 0 < t) (htP : t ∈ gPre s ζ W E p) {Wα : ℝ → ℝ} (hα : IsLoewnerTrace Wα (seedLine ζ W p.1)) :
    ∃ W' : ℝ → ℝ, Continuous W' ∧ W' 0 = 0 ∧ ∃ η' : ℝ → ℂ, IsLoewnerTrace W' η' ∧ IsProperArc η' ∧
      0 < capClock (gCurve s ζ W E p) t ∧
      fwdHull W' (capClock (gCurve s ζ W E p) t) = revChart (cfDrv0 s p.2) s '' fwdHull Wα t ∧
      η' (capClock (gCurve s ζ W E p) t) = revChart (cfDrv0 s p.2) s (seedLine ζ W p.1 t) ∧
      EqOn W' (chainDrv (gCurve s ζ W E p) (gPre s ζ W E p)) (Icc 0 (capClock (gCurve s ζ W E p) t)) ∧
      ∀ S : ℝ, 0 < S → S < t → 0 < capClock (gCurve s ζ W E p) S ∧
        capClock (gCurve s ζ W E p) S < capClock (gCurve s ζ W E p) t ∧
        η' (capClock (gCurve s ζ W E p) S) = revChart (cfDrv0 s p.2) s (seedLine ζ W p.1 S) := by
  set γ := gCurve s ζ W E p with hγdef
  set P := gPre s ζ W E p with hPdef
  set ω := cfDrv0 s p.2 with hωdef
  have hγ : IsKilledArc γ P := isKilledArc_gCurve hEg p
  obtain ⟨hαp, hGc, -, -, hGeq⟩ := hEg p hp
  have hω : Continuous ω := continuous_cfDrv0 s p.2
  have hω0 : ω 0 = 0 := cfDrv0_zero s p.2
  have hpre : t ∈ preContact (seedLine ζ W p.1) (cfHullQ s p.2) := gPre_of_mem hp ▸ htP
  have hdisjS : ∀ S, 0 ≤ S → S ≤ t → Disjoint (fwdHull Wα S) (negInv '' fwdHull ω s) := by
    intro S hS0 hSt
    rw [fwdHull_eq_image_Ioc hα hαp hS0, ← hGeq]
    refine disjoint_left.2 ?_
    rintro _ ⟨v, hv, rfl⟩ hG
    exact hpre.2 v ⟨hv.1.le, hv.2.trans hSt⟩ hG
  have hγimg : ∀ S, 0 ≤ S → γ '' Ioc 0 S = revChart ω s '' fwdHull Wα S := by
    intro S hS0
    rw [hγdef, gCurve_of_mem hp, fwdHull_eq_image_Ioc hα hαp hS0, image_image]
    exact image_congr fun v hv => imgCurve_of_pos hv.1
  have hSP : ∀ S, 0 ≤ S → S ≤ t → S ∈ P := fun S h0 h1 => hγ.icc t htP ⟨h0, h1⟩
  have hchain : ∀ S, 0 < S → S ≤ t → ∃ W' : ℝ → ℝ, Continuous W' ∧ W' 0 = 0 ∧ ∃ η' : ℝ → ℂ,
      IsLoewnerTrace W' η' ∧ IsProperArc η' ∧ fwdHull W' (capClock γ S) = revChart ω s '' fwdHull Wα S ∧
      η' (capClock γ S) = revChart ω s (seedLine ζ W p.1 S) ∧ EqOn W' (chainDrv γ P) (Icc 0 (capClock γ S)) := by
    intro S hS hSt
    obtain ⟨W', hW', hW'0, T, hT, η', h1, h2, h3, h4⟩ :=
      exists_imageTrace hα hαp hω hω0 s.coe_nonneg hGc hS (hdisjS S hS.le hSt)
    obtain ⟨hTc, hEq⟩ := hγ.eqOn_chainDrv_of_fwdHull_eq (hSP S hS.le hSt) hS hW' hW'0 h1 h2 hT
      (h3.trans (hγimg S hS.le).symm)
    subst hTc
    exact ⟨W', hW', hW'0, η', h1, h2, h3, h4, hEq⟩
  have hcappos : ∀ S, 0 < S → S ≤ t → 0 < capClock γ S := fun S hS hSt => by
    have h := hγ.strictMonoOn_capClock hγ.zero_mem (hSP S hS.le hSt) hS
    rwa [hγ.capClock_zero] at h
  obtain ⟨W', hW', hW'0, η', h1, h2, h3, h4, hEq⟩ := hchain t ht le_rfl
  refine ⟨W', hW', hW'0, η', h1, h2, hcappos t ht le_rfl, h3, h4, hEq, fun S hS hSt => ?_⟩
  have hlt : capClock γ S < capClock γ t := hγ.strictMonoOn_capClock (hSP S hS.le hSt.le) htP hSt
  refine ⟨hcappos S hS hSt.le, hlt, ?_⟩
  obtain ⟨W'', hW'', hW''0, η'', g1, g2, -, g4, gEq⟩ := hchain S hS hSt.le
  have hag : ∀ r ∈ Icc (0 : ℝ) (capClock γ S), W' r = W'' r := fun r hr =>
    (hEq ⟨hr.1, hr.2.trans hlt.le⟩).trans (gEq hr).symm
  rw [← g4]
  refine eq_of_image_Ioc_eq (g2.inj) (hcappos S hS hSt.le) fun r hr => ?_
  rw [← fwdHull_eq_image_Ioc h1 h2 hr.1.le, ← fwdHull_eq_image_Ioc g1 g2 hr.1.le]
  exact YuanCorollary13.fwdHull_eq_of_eqOn_Icc hW' hW'' hr.1.le fun x hx => hag x ⟨hx.1, hx.2.trans hr.2⟩

end Chain

/-! ### The staged identification on one good glued sample -/

section Sample

variable {κ θ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type*} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {s : ℝ≥0} {E : Set (Ω × HistorySpace 0 0)}

/-- **The staged image-chart identification on one good glued sample** (S2 per sample). On a good glued sample `p`
(the flow trace `α = seedLine ζ W p.1` a proper arc, the counterflow history in `goodHitSet`), at a pre-contact own
time `t > 0`, let `u` be records of pieces `0, …, ℓ` (positive own times summing to `t`) whose drivers are the pieces of
`α`'s driver `Wα`, with angles `ang j` relative to the staged field `h_s`, and let `w` be a harmonic function off the
union `α((0, t]) ∪ G_s` with the flow-side limit `w + u₀ − (𝔪 + θ₀ χ) → 0` at the trace points, where
`𝔪 = mean of pastWord (stopWord κ) c₀ x₀ ang (ℓ + 1) u` is the conditional mean of `h_s` and `θ₀ = ang 0` (the
coupling field is `h = h_s + θ₀ χ`, so that the first piece is its angle-`0` line), the counterflow-side and cobounded
limits of the counterflow mean, and Aux. 28's uniqueness. Then, with the canonical image chain `W'` of the killed arc
`γ = gCurve s ζ W E p` up to `T = capClock γ t` and the switch image times `A m = capClock γ (startT m)`, `w + u₀` is
the image stage word (angles `ang j − θ₀`) candidate in the chart `Ψ` minus `(ang ℓ − θ₀) χ`. -/
theorem stage_imgChart_sample (hκ : 0 < κ) (hxL : ∀ i, xL i ≤ 0) (hxR : ∀ j, 0 ≤ xR j)
    (hEg : ∀ p ∈ E, IsGood49 s ζ W p) {p : Ω × HistorySpace 0 0} (hp : p ∈ E) {t : ℝ} (ht : 0 < t)
    (htP : t ∈ gPre s ζ W E p) {Wα : ℝ → ℝ} (hα : IsLoewnerTrace Wα (seedLine ζ W p.1))
    (hWα : Continuous Wα) (hWα0 : Wα 0 = 0) (hy : p.2 ∈ goodHitSet)
    (c₀ : BoundaryWord) (x₀ : ℝ) {ang : ℕ → ℝ} {ℓ : ℕ} (u : PastData (ℓ + 1))
    (hpos : ∀ i ≤ ℓ, 0 < recSeqT u i) (htS : startT (recSeqT u) (ℓ + 1) = t)
    (hw : ∀ i, EqOn (recSeqW u i) (shiftDrive Wα (startT (recSeqT u) i)) (Icc 0 (recSeqT u i)))
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    {u' : ℂ → ℝ}
    (hu' : IsBoundedHarmonicExtension (cfWordData κ (bDataT ρL ρR xL xR θ κ) (forceJumpFinset xL xR))
      (cfWordJumps κ (bDataT ρL ρR xL xR θ κ) (forceJumpFinset xL xR)) u')
    {w : ℂ → ℝ}
    (hwFl : ∀ v : ℝ, 0 < v → v < t → Tendsto (fun z => w z + u₀ z -
        ((pastWord (stopWord κ) c₀ x₀ ang (ℓ + 1) u).mean (fwdMap Wα t z) + ang 0 * chiC κ -
          chiC κ * (logDerivFwd Wα t z).im))
      (𝓝[H \ (fwdHull Wα t ∪ cfHullQ s p.2)] (seedLine ζ W p.1 v)) (𝓝 0))
    (hwG : ∀ z₀ ∈ cfHullQ s p.2 ∪ {z : ℂ | z.im = 0},
      (∃ r > 0, fwdHull Wα t ∩ ball z₀ r ⊆ cfHullQ s p.2) →
      Tendsto (fun z => w z - cfMeanQ κ (bDataT ρL ρR xL xR θ κ) (forceJumpFinset xL xR) u' s p.2 z)
        (𝓝[H \ (fwdHull Wα t ∪ cfHullQ s p.2)] z₀) (𝓝 0))
    (hwInf : Tendsto (fun z => w z - cfMeanQ κ (bDataT ρL ρR xL xR θ κ) (forceJumpFinset xL xR) u' s p.2 z)
      (Bornology.cobounded ℂ ⊓ 𝓟 (H \ (fwdHull Wα t ∪ cfHullQ s p.2))) (𝓝 0))
    (huniq : ∀ z₀ ∈ H \ (fwdHull Wα t ∪ cfHullQ s p.2), ∀ (f φc : ℂ → ℂ) (G L : ℂ → ℝ) (E' : Set ℂ),
      IsConformalBijection f (ball 0 1) (connectedComponentIn (H \ (fwdHull Wα t ∪ cfHullQ s p.2)) z₀) →
      IsConformalBijection φc (connectedComponentIn (H \ (fwdHull Wα t ∪ cfHullQ s p.2)) z₀)
        {w : ℂ | 0 < w.im} →
      InnerProductSpace.HarmonicOnNhd G {w : ℂ | 0 < w.im} →
      (∃ M, ∀ w : ℂ, 0 < w.im → |G w| ≤ M) →
      ContinuousOn L (connectedComponentIn (H \ (fwdHull Wα t ∪ cfHullQ s p.2)) z₀) →
      (∀ z ∈ connectedComponentIn (H \ (fwdHull Wα t ∪ cfHullQ s p.2)) z₀,
        deriv φc z = ‖deriv φc z‖ * exp (L z * I)) →
      E'.Finite →
      (∀ q ∈ sphere (0 : ℂ) 1, q ∉ E' →
        Tendsto (fun ζ => (w (f ζ) + u₀ (f ζ)) - (G (φc (f ζ)) - chiC κ * L (f ζ))) (𝓝[ball 0 1] q) (𝓝 0)) →
      ∀ z ∈ connectedComponentIn (H \ (fwdHull Wα t ∪ cfHullQ s p.2)) z₀,
        w z + u₀ z = G (φc z) - chiC κ * L z) :
    ∃ W' : ℝ → ℝ, Continuous W' ∧ W' 0 = 0 ∧
      EqOn W' (chainDrv (gCurve s ζ W E p) (gPre s ζ W E p)) (Icc 0 (capClock (gCurve s ζ W E p) t)) ∧
      ∀ uI : ℂ → ℝ, IsBoundedHarmonicExtension (forceBoundaryData κ (imgStageRhoL κ θ ρL (fun j => ang j - ang 0) ℓ)
          (imgStageRhoR κ θ ρR (fun j => ang j - ang 0) ℓ)
          (imgStageVL xL (cfDrv0 s p.2) s W' (capClock (gCurve s ζ W E p) t)
            (fun m => capClock (gCurve s ζ W E p) (startT (recSeqT u) m)) ℓ)
          (imgStageVR xR (cfDrv0 s p.2) s W' (capClock (gCurve s ζ W E p) t)
            (fun m => capClock (gCurve s ζ W E p) (startT (recSeqT u) m)) ℓ))
        (forceJumpSet (imgStageVL xL (cfDrv0 s p.2) s W' (capClock (gCurve s ζ W E p) t)
            (fun m => capClock (gCurve s ζ W E p) (startT (recSeqT u) m)) ℓ)
          (imgStageVR xR (cfDrv0 s p.2) s W' (capClock (gCurve s ζ W E p) t)
            (fun m => capClock (gCurve s ζ W E p) (startT (recSeqT u) m)) ℓ)) uI →
      ∀ z ∈ H \ (fwdHull Wα t ∪ cfHullQ s p.2), w z + u₀ z =
        (uI (fwdMap W' (capClock (gCurve s ζ W E p) t) (revChart (cfDrv0 s p.2) s z)) - (ang ℓ - ang 0) * chiC κ) -
          chiC κ * ((logDerivFwd W' (capClock (gCurve s ζ W E p) t) (revChart (cfDrv0 s p.2) s z)).im +
            (logDerivPsi (cfDrv0 s p.2) s z).im) := by
  set ω := cfDrv0 s p.2 with hωdef
  have hω : Continuous ω := continuous_cfDrv0 s p.2
  have hω0 : ω 0 = 0 := cfDrv0_zero s p.2
  obtain ⟨hαp, hGc, hjL, hjR, hGeq⟩ := hEg p hp
  have hpre : t ∈ preContact (seedLine ζ W p.1) (cfHullQ s p.2) := gPre_of_mem hp ▸ htP
  have hdisj : Disjoint (fwdHull Wα t) (negInv '' fwdHull ω s) := by
    rw [fwdHull_eq_image_Ioc hα hαp ht.le, ← hGeq]
    refine disjoint_left.2 ?_
    rintro _ ⟨v, hv, rfl⟩ hG
    exact hpre.2 v ⟨hv.1.le, hv.2⟩ hG
  have hKt := ofReal_notMem_closure_of_isProperArc hα hαp ht.le
  have hdis := disjoint_closure_fwdHull_negInv hWα ht.le hKt hω s.coe_nonneg hdisj
  have hB := hasBdryLimits_cfDrv0 hy.1 s
  have hKs := eq_zero_of_mem_closure_cfDrv0 hy s
  obtain ⟨W', hW', hW'0, η', hη', hη'p, hT, hK', htip, hEq, hS⟩ := exists_imgChain_capClock hEg hp ht htP hα
  -- the counterflow mean in the chart `Ψ`
  set bd : ℝ → ℝ := bDataT ρL ρR xL xR θ κ with hbd
  set v := cfU κ bd (forceJumpFinset xL xR) s (cfStop s p.2) with hvdef
  have hv : IsBoundedHarmonicExtension (cfDataAt κ bd (forceJumpFinset xL xR) ω s)
      (forceJumpSet (cfMarkL κ bd (forceJumpFinset xL xR) ω s) (cfMarkR κ bd (forceJumpFinset xL xR) ω s)) v := by
    have h1 := isBoundedHarmonicExtension_cfU κ bd (forceJumpFinset xL xR) s (cfStop s p.2)
    have e := rpath_regPath_cfStop_eq hy.1 s
    have hL : cfPosL κ bd (forceJumpFinset xL xR) (Sec4.regPath (cfStop s p.2)) s =
        cfMarkL κ bd (forceJumpFinset xL xR) ω s := by
      funext i; rw [hωdef, ← e]; simp [cfPosL, cfMarkL, Ito.rpath]
    have hR : cfPosR κ bd (forceJumpFinset xL xR) (Sec4.regPath (cfStop s p.2)) s =
        cfMarkR κ bd (forceJumpFinset xL xR) ω s := by
      funext i; rw [hωdef, ← e]; simp [cfPosR, cfMarkR, Ito.rpath]
    rw [hL, hR] at h1
    exact h1
  set mG : ℂ → ℝ := fun z => cfMeanQ κ bd (forceJumpFinset xL xR) u' s p.2 z + u₀ z - θ * chiC κ with hmG
  set M : ℂ → ℝ := fun z => w z + u₀ z - θ * chiC κ with hM
  have hId : ∀ z ∈ H \ negInv '' fwdHull ω s, mG z + chiC κ * (GlueImg.logDerivPsi ω s z).im =
      GlueImg.retMean κ v (revChart ω s z) := by
    intro z hz
    have h1 := cfMeanQ_add_eq_retMean_addT hκ θ ρL ρR xL xR hu₀ hu' s p.2 (z := z) (hGeq ▸ hz)
    rw [rpath_regPath_cfStop_eq hy.1 s] at h1
    simp only [hmG]
    linarith
  rw [hGeq] at hwFl hwG hwInf huniq
  have hG : ∀ z₀ ∈ negInv '' fwdHull ω s ∪ {z : ℂ | z.im = 0},
      (∃ r > 0, fwdHull Wα t ∩ ball z₀ r ⊆ negInv '' fwdHull ω s) →
      Tendsto (fun z => M z - mG z) (𝓝[H \ (fwdHull Wα t ∪ negInv '' fwdHull ω s)] z₀) (𝓝 0) := by
    intro z₀ hz₀ hr
    refine (hwG z₀ hz₀ hr).congr fun z => ?_
    simp only [hM, hmG]; ring
  have hInf : Tendsto (fun z => M z - mG z)
      (Bornology.cobounded ℂ ⊓ 𝓟 (H \ (fwdHull Wα t ∪ negInv '' fwdHull ω s))) (𝓝 0) := by
    refine hwInf.congr fun z => ?_
    simp only [hM, hmG]; ring
  have hFl : ∀ v : ℝ, 0 < v → v < t → Tendsto (fun z => M z + θ * chiC κ -
      ((vshift (pastWord (stopWord κ) c₀ x₀ ang (ℓ + 1) u) (ang 0 * chiC κ)).mean (fwdMap Wα t z) -
        chiC κ * (logDerivFwd Wα t z).im))
      (𝓝[H \ (fwdHull Wα t ∪ negInv '' fwdHull ω s)] (seedLine ζ W p.1 v)) (𝓝 0) := by
    intro v hv0 hvt
    refine (hwFl v hv0 hvt).congr fun z => ?_
    simp only [hM, mean_vshift]; ring
  have hA : ∀ m, 1 ≤ m → m ≤ ℓ → 0 < capClock (gCurve s ζ W E p) (startT (recSeqT u) m) ∧
      capClock (gCurve s ζ W E p) (startT (recSeqT u) m) < capClock (gCurve s ζ W E p) t ∧
      η' (capClock (gCurve s ζ W E p) (startT (recSeqT u) m)) =
        revChart ω s (seedLine ζ W p.1 (startT (recSeqT u) m)) := by
    intro m h1 h2
    obtain ⟨hpos', hlt'⟩ := startT_pos_lt u hpos m h1 h2
    rw [htS] at hlt'
    exact hS _ hpos' hlt'
  have hS' : ∀ m, 1 ≤ m → m ≤ ℓ → 0 < startT (recSeqT u) m ∧ startT (recSeqT u) m < t := fun m h1 h2 => by
    rw [← htS]; exact startT_pos_lt u hpos m h1 h2
  have hgapI : ∀ r ∈ Ioc 0 (capClock (gCurve s ζ W E p) t), chartAL W' r < 0 ∧ 0 < chartAR W' r := fun r hr =>
    ⟨chartAL_neg_of_isProperArc hη' hη'p hW' hW'0 hr.1, chartAR_pos_of_isProperArc hη' hη'p hW' hW'0 hr.1⟩
  have hLc := isLeftLevels_pastWord_chartAL c₀ x₀ ang hκ u hα hαp hWα hWα0 hw
  have hRc := isRightLevels_pastWord_chartAR c₀ x₀ ang hκ u hα hαp hWα hWα0 hw
  rw [htS] at hLc hRc
  have hLc' := StagedFinal.IsLeftLevels.congr_ht (IsLeftLevels.vshift hLc (ang 0 * chiC κ))
    (ht' := fun j => -sleLambda κ - (fun j => ang j - ang 0) j * chiC κ) fun j _ => by ring
  have hRc' := StagedFinal.IsRightLevels.congr_ht (IsRightLevels.vshift hRc (ang 0 * chiC κ))
    (ht' := fun j => sleLambda κ - (fun j => ang j - ang 0) j * chiC κ) fun j _ => by ring
  refine ⟨W', hW', hW'0, hEq, fun uI hu z hz => ?_⟩
  rw [hGeq] at hz
  exact eqOn_imgChart_stage ρL ρR θ hα hαp hWα hWα0 ht hKt hκ hω hω0 s.coe_nonneg hB hKs hjL hjR hGc hdisj hdis
    hxL hxR hv hG hInf hId hW' hW'0 hη' hη'p hT hK' htip (startT_zero _) hS' hA hgapI (sub_self _)
    (isSorted_vshift (isSorted_stopWord κ _) _) hLc' hRc' hu hFl (fun z => by simp only [hM]; ring) huniq z hz

end Sample

end InteractingSLE.Sec5.CrossCond.StagedDepth
