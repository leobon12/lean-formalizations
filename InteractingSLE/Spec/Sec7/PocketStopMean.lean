/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketStopActive
import InteractingSLE.Spec.Sec7.Aux2728Pocket
import InteractingSLE.Spec.Coupling.WholeField8Flow
import InteractingSLE.Spec.Dimension.TraceBridge
import InteractingSLE.Spec.Ito.Loewner

/-!
# The central pocket mean at `T(q)` from its boundary values in the relative coordinate

Packet PROVE-STRIPSYS33. Specification §7.4: Aux. lemma 36 (`source/spec/p193-240.md` L60–L78, pp. 194–197: "In any
uniformizing coordinate of `E_T`, flatten these boundary germs with those lifts. The resulting finitely many constant
values have their usual bounded Poisson extension; its pullback with the derivative correction is the full marked
conditional mean in `E_T`" and "*Uniqueness at the exceptional physical points* … The cited uniqueness lemma makes the
difference zero"), Aux. lemma 122 (the phase `d = 0`), Aux. lemma 125's proof (p. 396: the relative active domain at
`q` is the target component of `C ∖ R_{T(q)}`).

PROVE-STRIPSYS32's `PocketUnionPt.PocketStopMeanAt` asks, for every version `g` of the local-set mean of `K_q`, for a
continuous representative `v` of `g + 𝔥` on the active domain `S` with `v + a + k ℓ_c = couplingMean(q) ∘ c.fwd`. With
`K_q = ℍ ∖ activeDom` (`PocketStopActive.lean`) the active domain is `ℍ ∖ K_q`, and it is the domain of the **relative
chart** `c' = c.loewner w q` (the pocket chart `c` followed by the relative Loewner map `f_q` of the traversal's driver
`w`, with the lift `arg f_q′ ∘ c.fwd + ℓ_c`). This file proves `PocketStopMeanAt` from the **boundary values** of the
mean in that coordinate (`PocketStopSideLimit`, the named field-level input): at every real point `ξ` off the word's
force points, the coordinate mean `v + u + χ ℓ_{c'}` of `c'⁻¹` tends to the word's boundary height at `q` minus the
constant `a`. The step "boundary values ⇒ the mean is the bounded Poisson extension, pulled back" is Aux. lemmas 27–28
(`Aux2728Pocket.ae_eqOn_of_sideLimit`), applied in the relative chart; the extension is the canonical `bheProc` of the
word at `q`, and `couplingMean` is its pullback by `f_q` with the hydrodynamic lift.

## Main results

* `relChart`, `relChart_eq_loewner`: the relative chart, and its agreement with the chart of any continuous driver that
  agrees with the traversal's driver beyond `q`;
* `PocketStopSideLimit` (named input: Aux. lemma 36's boundary data at `T(q)` read in the relative coordinate, with
  Aux. lemma 120's word heights and Aux. lemma 122's phase `d = 0`);
* **`pocketStopMeanAt_of_sideLimit`**: `PocketStopMeanAt` with `k = χ(κ)` from the side limits.

Conditional helpers; no source theorem is replaced. Ruling R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any result taking them as hypotheses.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H fwdHull fwdMap fwdMapInv logDerivFwd chiC)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.PocketStop

open PocketTraversal PocketAdapt Lemma71C LocalSets WholeField PocketCoupling PocketUnionPt

/-! ### The relative chart -/

section Chart

variable {Ω : Type*}

/-- **The relative chart at capacity time `q`**: the pocket chart `c ω` followed by the relative Loewner map at `q` of
the traversal's capacity driver. -/
def relChart (c : Ω → Chart) (γ : Ω → ℝ → ℂ) (q : ℝ≥0) (ω : Ω) : Chart :=
  (c ω).loewner (fun s : ℝ => segDriver (γ ω) s.toNNReal) q

/-- A Loewner chart only depends on the driver on `[0, q']` for any `q' > q`. -/
theorem loewner_congr (c : Chart) {w W : ℝ → ℝ} {q q' : ℝ} (hq : 0 ≤ q) (hqq' : q < q')
    (h : ∀ r ∈ Icc (0 : ℝ) q', w r = W r) : c.loewner w q = c.loewner W q := by
  have h1 : (fun z => fwdMap w q (c.1 z)) = fun z => fwdMap W q (c.1 z) :=
    funext fun z => fwdMap_eq_of_eqOn hq fun r hr => h r ⟨hr.1, hr.2.trans hqq'.le⟩
  have h2 : fwdMapInv w q = fwdMapInv W q := fwdMapInv_eq_of_eqOn hq hqq' h
  have h3 : (fun z => (logDerivFwd w q (c.1 z)).im + c.2.2 z) = fun z => (logDerivFwd W q (c.1 z)).im + c.2.2 z :=
    funext fun z => by
      rw [Ito.logDerivFwd_congr_of_eqOn (T := q) (fun r hr => h r ⟨hr.1, hr.2.trans hqq'.le⟩) hq le_rfl]
  simp only [Chart.loewner, h1, h2, h3]

/-- **The relative chart is the Loewner chart of a continuous local driver**: below the terminal capacity time the
traversal's driver agrees, beyond `q`, with a continuous driver `W` vanishing at `0` (`IsDrivenCurve.localDriver`). -/
theorem exists_relChart_eq_loewner {c : Ω → Chart} {γ : Ω → ℝ → ℂ} {q : ℝ≥0} {ω : Ω} (hγ : IsDrivenCurve (γ ω))
    (hq : (q : ℝ≥0∞) < capLife (γ ω)) :
    ∃ W : ℝ → ℝ, Continuous W ∧ W 0 = 0 ∧ ∃ q' : ℝ, (q : ℝ) < q' ∧
      (∀ r ∈ Icc (0 : ℝ) q', segDriver (γ ω) r.toNNReal = W r) ∧ relChart c γ q ω = (c ω).loewner W q := by
  have hq' : ENNReal.ofReal (q : ℝ) < capLife (γ ω) := by rwa [ENNReal.ofReal_coe_nnreal]
  obtain ⟨n, hn0, hn⟩ := hγ.exists_pos_lt_capClock q.coe_nonneg hq'
  obtain ⟨W, hW, hW0, -, -, -, hK⟩ := hγ.localDriver n hn0
  have heq : ∀ r ∈ Icc (0 : ℝ) (capClock (γ ω) n), segDriver (γ ω) r.toNNReal = W r := fun r hr => by
    show segDrv (γ ω) (r.toNNReal : ℝ) = W r
    rw [Real.coe_toNNReal _ hr.1]
    exact hγ.segDrv_eq hn0 hW hW0 (fun t ht => (hK t ht).2) hr.1 hr.2
  exact ⟨W, hW, hW0, capClock (γ ω) n, hn, heq, loewner_congr (c ω) q.coe_nonneg hn heq⟩

end Chart

/-! ### The named input: the boundary values in the relative coordinate -/

section SideLimit

variable {Ω : Type*}

/-- **The boundary values of the central pocket mean at `T(q)` in the relative coordinate** (named field-level input;
Aux. lemma 36's boundary data — the prescribed flow heights on the open incoming sides, the old counterflow heights on
the exposed counterflow boundary (Aux. lemma 35 (i)–(ii)), transported to the coordinate by (JC2) with the inherited
analytic lifts — read in the relative chart `c' = c.loewner w q`, where they are the word's force heights at `q`
(Aux. lemma 120) with no `2π` shift of the phase (Aux. lemma 122, `d = 0`)): for every version `g` of the local-set
mean of `K`, almost surely on the live event, for every harmonic representative `v` of `g` on `ℍ ∖ K`, at every real
point `ξ` off the word's centred force points, the coordinate mean `v + u + χ(κ) ℓ_{c'}` read through `c'⁻¹` tends to
the word's boundary height at `ξ` minus `a`. -/
def PocketStopSideLimit (κ : ℝ) {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (A : Set Ω) (γ : Ω → ℝ → ℂ) (xL : Ω → Fin nL → ℝ) (xR : Ω → Fin nR → ℝ) (c : Ω → Chart)
    (a : ℝ) (h₀ : Ω → DistOn upperHalfPlaneOpens) (u : ℂ → ℝ) (K : Ω → Set ℂ) (q : ℝ≥0) : Prop :=
  ∀ g : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean K h₀ P g →
    ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (γ ω) →
      ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ K ω) →
        (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ K ω → g ω φ = ∫ z, v z * φ z) →
        ∀ ξ : ℝ, ξ ∉ forceJumpSet
            (fun i => geomLW (fun t ω => segDriver (γ ω) t) xL i q ω - segDriver (γ ω) q)
            (fun j => geomRW (fun t ω => segDriver (γ ω) t) xR j q ω - segDriver (γ ω) q) →
          Tendsto (fun y => v ((relChart c γ q ω).2.1 y) + u ((relChart c γ q ω).2.1 y) +
              chiC κ * (relChart c γ q ω).2.2 ((relChart c γ q ω).2.1 y)) (𝓝[H] (ξ : ℂ))
            (𝓝 (forceBoundaryData κ ρL ρR
              (fun i => geomLW (fun t ω => segDriver (γ ω) t) xL i q ω - segDriver (γ ω) q)
              (fun j => geomRW (fun t ω => segDriver (γ ω) t) xR j q ω - segDriver (γ ω) q) ξ - a))

end SideLimit

/-! ### The central pocket mean from the side limits -/

section Mean

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **The central pocket mean at `T(q)` from its boundary values** (Aux. lemma 36's final step, Aux. lemmas 27–28 in
the relative chart). Let `K` be a hitting-measurable local set of the zero-boundary GFF `h₀` whose complement in `ℍ` is,
on the live event, the active domain `inv(ℍ ∖ K^{rel}_q)` (e.g. `activeCompl`), `S` the ambient pocket domain (equal to
the active domain on the live event), `c` a conformal pocket chart with a derivative logarithm `ℓ` whose imaginary part
is its lift, `γ` driven curves on `A`, and `𝔥` the bounded harmonic function `u`. If the coordinate mean has the word's
boundary heights at `q` minus `a` in the relative chart (`PocketStopSideLimit`), then `PocketStopMeanAt` holds with
`k = χ(κ)`: `v + a + χ ℓ_c = couplingMean(q) ∘ c.fwd` on `S`, `v` the density of `g + 𝔥`. -/
theorem pocketStopMeanAt_of_sideLimit [IsProbabilityMeasure P] {κ : ℝ} {nL nR : ℕ} {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} {h₀ : Ω → DistOn upperHalfPlaneOpens} (hh₀ : IsZeroBoundaryGFF upperHalfPlaneOpens h₀ P)
    {A : Set Ω} {γ : Ω → ℝ → ℂ} {c : Ω → Chart} {q : ℝ≥0} {K : Ω → Set ℂ}
    (hKm : Measurable[mΩ, hittingSigma] K) (hloc : IsLocalSet K h₀ P)
    (hK : ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) → H \ K ω = activeDom A γ c q ω)
    {S : Ω → Set ℂ} (hS : ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) → S ω = activeDom A γ c q ω)
    (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω)) {ℓ : Ω → ℂ → ℂ}
    (hc : ∀ ω ∈ A, (c ω).IsConformal ∧ IsDerivLog (c ω).1 (ℓ ω) (c ω).dom ∧
      ∀ z ∈ (c ω).dom, (c ω).2.2 z = (ℓ ω z).im)
    {u : ℂ → ℝ} (hu : InnerProductSpace.HarmonicOnNhd u H) (hub : ∃ M : ℝ, ∀ z ∈ H, |u z| ≤ M)
    {𝔥 : DistOn upperHalfPlaneOpens} (h𝔥 : ∀ φ : TestOn upperHalfPlaneOpens, 𝔥 φ = ∫ z, u z * φ z)
    {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ} {a : ℝ}
    (hside : PocketStopSideLimit κ ρL ρR P A γ xL xR c a h₀ u K q) :
    PocketStopMeanAt κ ρL ρR P A γ xL xR c a (chiC κ) h₀ 𝔥 K S q := by
  intro g hg
  filter_upwards [Aux2728Pocket.ae_eqOn_of_sideLimit hh₀ hKm hloc hg hu hub (chiC κ), hside g hg, hg.2.1]
    with ω hω hsω hharm hωA hq
  obtain ⟨v, hvh, hvrep⟩ := hharm
  obtain ⟨hcc, hℓ, hlift⟩ := hc ω hωA
  obtain ⟨W, hW, hW0, q', hqq', hWeq, hrel⟩ := exists_relChart_eq_loewner (c := c) (hγ ω hωA) hq
  set w : ℝ → ℝ := fun s => segDriver (γ ω) s.toNNReal with hw
  set c' : Chart := (c ω).loewner W q with hc'
  have hq0 : (0 : ℝ) ≤ q := q.coe_nonneg
  have hc'conf : c'.IsConformal := hcc.loewner hW hW0 hq0
  have hhull : fwdHull w q = fwdHull W q := fwdHull_eq_of_eqOn hq0 hqq' hWeq
  -- the active domain is the domain of the relative chart
  have himg : c'.2.1 '' H = (c ω).2.1 '' (H \ fwdHull W q) := by
    rw [show c'.2.1 = (c ω).2.1 ∘ fwdMapInv W q from rfl, image_comp,
      QuantumZipper.RS.image_fwdMapInv_H hW hW0 hq0]
  have hdomK : H \ K ω = (c'.dom : Set ℂ) := by
    rw [hK ω hωA hq, activeDom_eq hωA hq, hc'conf.coe_dom, himg, ← hhull]
  have hdomS : S ω = (c'.dom : Set ℂ) := by
    rw [hS ω hωA hq, ← hdomK, hK ω hωA hq]
  have hsub : (c'.dom : Set ℂ) ⊆ (c ω).dom := by
    rw [hc'conf.coe_dom, himg, hcc.coe_dom]
    exact image_mono sdiff_subset
  -- the chart data of Aux. lemmas 27–28
  have hpre : IsPreconnected (c'.dom : Set ℂ) := by
    rw [hc'conf.coe_dom]
    exact (convex_halfSpace_gt Complex.imLm.isLinear 0).isPreconnected.image _ hc'conf.1.continuousOn
  have hI : c'.2.1 Complex.I ∈ (c'.dom : Set ℂ) := by
    rw [hc'conf.coe_dom]
    exact mem_image_of_mem _ (show (0 : ℝ) < Complex.I.im by simp)
  have hcomp : ∃ z₀ ∈ H \ K ω, (c'.dom : Set ℂ) = connectedComponentIn (H \ K ω) z₀ :=
    ⟨c'.2.1 Complex.I, hdomK ▸ hI, by rw [hdomK, hpre.connectedComponentIn hI]⟩
  have hmaps : MapsTo (c ω).1 c'.dom (H \ fwdHull W q) := by
    intro z hz
    rw [hc'conf.coe_dom, himg] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    rw [hcc.2.2 y hy.1]
    exact hy
  have hψd : DifferentiableOn ℂ (fwdMap W q) (H \ fwdHull W q) := fun z hz =>
    (QuantumZipper.FwdHolo.hasDerivAt_fwdMap hW hq0 hz).differentiableAt.differentiableWithinAt
  have hℓ'0 := IsDerivLog.comp (ψ := fwdMap W q) (φ := (c ω).1) (Lψ := logDerivFwd W q) (Lφ := ℓ ω)
    (D := (c'.dom : Set ℂ)) (E := H \ fwdHull W q) c'.dom.isOpen
    (QuantumZipper.FwdHolo.isOpen_compl_fwdHull hW hq0) hψd (hcc.differentiableOn_fwd.mono hsub) hmaps
    (isDerivLog_fwdMap hW hq0) (hℓ.mono hsub)
  have hℓ' : IsDerivLog c'.1 (fun z => logDerivFwd W q ((c ω).1 z) + ℓ ω z) c'.dom := hℓ'0
  have hlift' : ∀ z ∈ (c'.dom : Set ℂ), c'.2.2 z = ((fun z => logDerivFwd W q ((c ω).1 z) + ℓ ω z) z).im :=
    fun z hz => by
      show (logDerivFwd W q ((c ω).1 z)).im + (c ω).2.2 z = _
      rw [Complex.add_im, hlift z (hsub hz)]
  -- the word's boundary data at `q` and its bounded harmonic extension, shifted by `a`
  set vL : Fin nL → ℝ := fun i => geomLW (fun t ω => segDriver (γ ω) t) xL i q ω - segDriver (γ ω) q
  set vR : Fin nR → ℝ := fun j => geomRW (fun t ω => segDriver (γ ω) t) xR j q ω - segDriver (γ ω) q
  set G₀ : ℂ → ℝ := Restart.DomainMarkov.bheProc κ ρL ρR (fun t ω => segDriver (γ ω) t)
    (geomLW (fun t ω => segDriver (γ ω) t) xL) (geomRW (fun t ω => segDriver (γ ω) t) xR) ω q
  have hG₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR vL vR) (forceJumpSet vL vR) G₀ :=
    Restart.DomainMarkov.isBoundedHarmonicExtension_bheProc ω q
  have hG : IsBoundedHarmonicExtension (fun ξ => forceBoundaryData κ ρL ρR vL vR ξ - a) (forceJumpSet vL vR)
      fun z => G₀ z - a := by
    obtain ⟨hGh, ⟨M, hM⟩, hGt⟩ := hG₀
    refine ⟨fun z hz => ?_, ⟨M + |a|, fun z hz => ?_⟩, fun ξ hξ => (hGt ξ hξ).sub_const a⟩
    · exact (hGh z hz).sub (InnerProductSpace.harmonicAt_const a)
    · calc |G₀ z - a| ≤ |G₀ z| + |a| := abs_sub _ _
        _ ≤ M + |a| := by linarith [hM z hz]
  have hJ : (forceJumpSet vL vR).Finite := ((finite_range vL).union (finite_range vR)).insert 0
  have hsideω : ∀ ξ : ℝ, ξ ∉ forceJumpSet vL vR →
      Tendsto (fun y => v (c'.2.1 y) + u (c'.2.1 y) + chiC κ * (c'.2.2 (c'.2.1 y) + 2 * π * ((0 : ℤ) : ℝ)))
        (𝓝[H] (ξ : ℂ)) (𝓝 (forceBoundaryData κ ρL ρR vL vR ξ - a)) := by
    intro ξ hξ
    have h1 := hsω hωA hq v hvh hvrep ξ hξ
    rw [hrel] at h1
    simpa only [Int.cast_zero, mul_zero, add_zero] using h1
  have key := hω v hvh hvrep c' (fun z => logDerivFwd W q ((c ω).1 z) + ℓ ω z) 0 _ _ _ hc'conf hcomp hℓ'
    hlift' hJ hG hsideω
  -- the conclusion
  have hvc : ContinuousOn v (H \ K ω) := fun z hz => (hvh z hz).1.continuousAt.continuousWithinAt
  have huc : ContinuousOn u H := fun z hz => (hu z hz).1.continuousAt.continuousWithinAt
  have hSK : S ω = H \ K ω := by rw [hdomS, hdomK]
  refine ⟨fun z => v z + u z, ?_, fun φ hφ => ?_, fun z hz => ?_⟩
  · rw [hSK]
    exact hvc.add (huc.mono sdiff_subset)
  · have hφK : tsupport φ ⊆ H \ K ω := hSK ▸ hφ
    have hi₁ : Integrable fun z => v z * φ z := integrable_mul_testOn hvc φ hφK
    have hi₂ : Integrable fun z => u z * φ z := integrable_mul_testOn huc φ (hφK.trans sdiff_subset)
    rw [add_apply, hvrep φ hφK, h𝔥 φ, ← integral_add hi₁ hi₂]
    exact integral_congr_ae (Eventually.of_forall fun z => by simp only [add_mul])
  · have hz' : z ∈ (c'.dom : Set ℂ) := hdomS ▸ hz
    have hk := key z hz'
    have e1 : fwdMap w q ((c ω).1 z) = fwdMap W q ((c ω).1 z) :=
      fwdMap_eq_of_eqOn hq0 fun r hr => hWeq r ⟨hr.1, hr.2.trans hqq'.le⟩
    have e2 : logDerivFwd w q ((c ω).1 z) = logDerivFwd W q ((c ω).1 z) :=
      Ito.logDerivFwd_congr_of_eqOn (T := q) (fun r hr => hWeq r ⟨hr.1, hr.2.trans hqq'.le⟩) hq0 le_rfl
    show v z + u z + a + chiC κ * (c ω).2.2 z = couplingMean κ w q G₀ ((c ω).1 z)
    rw [couplingMean, e1, e2]
    have hc'1 : c'.1 z = fwdMap W q ((c ω).1 z) := rfl
    have hc'2 : c'.2.2 z = (logDerivFwd W q ((c ω).1 z)).im + (c ω).2.2 z := rfl
    rw [hc'1, hc'2] at hk
    simp only [Int.cast_zero, mul_zero, add_zero] at hk
    linarith

end Mean

end InteractingSLE.Sec7.PocketStop
