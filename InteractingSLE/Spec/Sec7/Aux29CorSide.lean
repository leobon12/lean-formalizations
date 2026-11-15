/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Aux29CorMob
import InteractingSLE.Spec.Sec7.SideLCGerm
import InteractingSLE.Spec.Sec7.PocketStopSideInputsGeometry
import InteractingSLE.Spec.Sec6.Prop61BGlobal
import QuantumZipper.Proofs.Loewner.CoreArc3b
import QuantumZipper.Proofs.Zipper.PStarAreaCoord

/-!
# Theorem 1.2's R.7 side limit with the collar required only off the exceptional fibres

PROVE-AUX29-CORNER. `PocketStopSide.pocketStopPhaseSideLimit_of_raw_reference_germs` derives the
phase side limit at a relative capacity `q` from R.5's collar (`hCollar`) at **every** real current
coordinate off the jump set. R.5 (specification p. 474–475) gives no comparison at the prime ends
whose physical landing is the current tip or the bounded pocket's outgoing corner; the source covers
them by Aux. 29 in the corollary "the full stopped Gaussian kernel" (p. 475). This file proves the
side limit at every coordinate from the collar **off a finite exceptional physical set** `X ω`:

* `exists_isDerivLog_relChart`: the current chart inherits the base chart's analytic lift;
* `tendsto_fwdMapInv_cobounded`, `relChart_extension_and_limit`: the current inverse extends
  continuously to `ℍ̄` and has the base chart's landing at `∞`;
* **`pocketStopPhaseSideLimit_of_collar_offExc`**: the conclusion `PocketStopPhaseSideLimit` of
  `pocketStopPhaseSideLimit_of_raw_reference_germs`, with the collar required only where the physical
  landing `extendFrom H inv ξ` avoids `X ω`. The local set's logarithmic growth is Wang–Wu's global
  Lemma 4.6 (`Sec6.ae_abs_le_log_global_of_isLocalSetMean`); Aux. 29 is applied through
  `Aux29Cor.eqOn_phaseWordExt_of_landing_germs`.

Conditional helper with a distinct name; it replaces no source theorem. Nothing here uses
Theorem 1.2/1.3 (R43, R48).
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology Metric Complex
open QuantumZipper (H Hbar chiC fwdMapInv)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.Aux29Cor

open LocalSets PocketTraversal PocketAdapt Lemma71C PocketStop PocketUnionPt PocketCoupling
  Aux119Heights PocketStopSide PhaseSel

/-! ### The current chart: analytic lift, boundary extension and the landing at `∞` -/

/-- The Loewner inverse tends to `∞` within `ℍ` at `∞`. -/
theorem tendsto_fwdMapInv_cobounded {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) (q : ℝ≥0) :
    Tendsto (fwdMapInv W q) (Bornology.cobounded ℂ ⊓ 𝓟 H) (Bornology.cobounded ℂ ⊓ 𝓟 H) := by
  have hq0 : (0 : ℝ) ≤ q := q.coe_nonneg
  refine tendsto_inf.2 ⟨?_, tendsto_principal.2 (eventually_inf_principal.2
    (Eventually.of_forall fun w hw => QuantumZipper.RS.fwdMapInv_mem_H hW hW0 hq0 hw))⟩
  rcases eq_or_lt_of_le hq0 with h0 | hpos
  · have hid : ∀ w ∈ H, fwdMapInv W q w = w := fun w hw => by
      rw [← h0]
      exact QuantumZipper.E6.fwdMapInv_zero_eq_self hW hW0 hw
    exact (tendsto_id.mono_left inf_le_left).congr'
      (eventually_inf_principal.2 (Eventually.of_forall fun w hw => (hid w hw).symm))
  · obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (hW.continuousOn (s := Icc 0 (q : ℝ)))
    have hM' : ∀ t ∈ Icc (0 : ℝ) q, |W t| ≤ M := fun t ht => by
      simpa [Real.norm_eq_abs] using hM t ht
    set C := 24 * M + 8 * Real.sqrt q
    rw [← tendsto_norm_atTop_iff_cobounded]
    have hle : ∀ w ∈ H, ‖w‖ + -C ≤ ‖fwdMapInv W q w‖ := fun w hw => by
      have hz := QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hW hW0 hq0 hw
      have h1 := QuantumZipper.CoreArc.norm_fwdMap_sub_le_uniform hW hW0 hpos hM' hz
      rw [QuantumZipper.RS.fwdMap_fwdMapInv hW hW0 hq0 hw] at h1
      have h2 := norm_sub_norm_le w (fwdMapInv W q w)
      linarith
    have hn : Tendsto (fun w : ℂ => ‖w‖ + -C) (Bornology.cobounded ℂ ⊓ 𝓟 H) atTop :=
      tendsto_atTop_add_const_right _ _ (tendsto_norm_cobounded_atTop.mono_left inf_le_left)
    exact tendsto_atTop_mono' _ (eventually_inf_principal.2 (Eventually.of_forall hle)) hn

variable {Ω : Type*} {c : Ω → Chart} {γ : Ω → ℝ → ℂ} {q : ℝ≥0} {ω : Ω}

/-- The current chart inherits the base chart's analytic derivative logarithm. -/
theorem exists_isDerivLog_relChart (hγ : IsDrivenCurve (γ ω)) (hq : (q : ℝ≥0∞) < capLife (γ ω))
    {ℓ : ℂ → ℂ} (hcc : (c ω).IsConformal) (hℓ : IsDerivLog (c ω).1 ℓ (c ω).dom)
    (hlift : ∀ z ∈ (c ω).dom, (c ω).2.2 z = (ℓ z).im) :
    ∃ L : ℂ → ℂ, IsDerivLog (relChart c γ q ω).1 L (relChart c γ q ω).dom ∧
      ∀ z ∈ (relChart c γ q ω).dom, (relChart c γ q ω).2.2 z = (L z).im := by
  obtain ⟨W, hW, hW0, q', hqq', hWeq, hrel⟩ := exists_relChart_eq_loewner (c := c) hγ hq
  rw [hrel]
  set c' : Chart := (c ω).loewner W q with hc'
  have hq0 : (0 : ℝ) ≤ q := q.coe_nonneg
  have hc'conf : c'.IsConformal := hcc.loewner hW hW0 hq0
  have himg : c'.2.1 '' H = (c ω).2.1 '' (H \ QuantumZipper.fwdHull W q) := by
    rw [show c'.2.1 = (c ω).2.1 ∘ fwdMapInv W q from rfl, image_comp,
      QuantumZipper.RS.image_fwdMapInv_H hW hW0 hq0]
  have hsub : (c'.dom : Set ℂ) ⊆ (c ω).dom := by
    rw [hc'conf.coe_dom, himg, hcc.coe_dom]
    exact image_mono sdiff_subset
  have hmaps : MapsTo (c ω).1 c'.dom (H \ QuantumZipper.fwdHull W q) := by
    intro z hz
    rw [hc'conf.coe_dom, himg] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    rw [hcc.2.2 y hy.1]
    exact hy
  have hψd : DifferentiableOn ℂ (QuantumZipper.fwdMap W q) (H \ QuantumZipper.fwdHull W q) := fun z hz =>
    (QuantumZipper.FwdHolo.hasDerivAt_fwdMap hW hq0 hz).differentiableAt.differentiableWithinAt
  have hℓ'0 := IsDerivLog.comp (ψ := QuantumZipper.fwdMap W q) (φ := (c ω).1)
    (Lψ := QuantumZipper.logDerivFwd W q) (Lφ := ℓ) (D := (c'.dom : Set ℂ))
    (E := H \ QuantumZipper.fwdHull W q) c'.dom.isOpen
    (QuantumZipper.FwdHolo.isOpen_compl_fwdHull hW hq0) hψd (hcc.differentiableOn_fwd.mono hsub) hmaps
    (isDerivLog_fwdMap hW hq0) (hℓ.mono hsub)
  refine ⟨fun z => QuantumZipper.logDerivFwd W q ((c ω).1 z) + ℓ z, hℓ'0, fun z hz => ?_⟩
  show (QuantumZipper.logDerivFwd W q ((c ω).1 z)).im + (c ω).2.2 z = _
  rw [Complex.add_im, hlift z (hsub hz)]

/-- The current chart's inverse extends continuously to `ℍ̄`, and its landing at `∞` (after `mob`)
is the base chart's. -/
theorem relChart_extension_and_limit (hγ : IsDrivenCurve (γ ω)) (hq : (q : ℝ≥0∞) < capLife (γ ω))
    {E : ℂ → ℂ} (hE : EqOn E (c ω).2.1 H) (hEc : ContinuousOn E Hbar) {p : ℂ}
    (hp : Tendsto (fun w => mob ((c ω).2.1 w)) (Bornology.cobounded ℂ ⊓ 𝓟 H) (𝓝 p)) :
    (∃ F : ℂ → ℂ, EqOn F (relChart c γ q ω).2.1 H ∧ ContinuousOn F Hbar) ∧
      Tendsto (fun w => mob ((relChart c γ q ω).2.1 w)) (Bornology.cobounded ℂ ⊓ 𝓟 H) (𝓝 p) := by
  obtain ⟨F, hF, hFc, -⟩ := exists_relative_inverse_extension hγ hq hE hEc
  refine ⟨⟨F, hF, hFc⟩, ?_⟩
  obtain ⟨W, hW, hW0, -, -, -, hrel⟩ := exists_relChart_eq_loewner (c := c) hγ hq
  rw [hrel]
  exact hp.comp (tendsto_fwdMapInv_cobounded hW hW0 q)


/-! ### The side limit at every coordinate from the collar off the exceptional fibres -/

/-- **Theorem 1.2's R.7 side limit at a fixed relative capacity, with the collar required only off a
finite exceptional physical set** (Lemma R.5 and its corollary, specification pp. 474–475; Aux. 29).
This is `pocketStopPhaseSideLimit_of_raw_reference_germs` with the R.5 collar hypothesis `hCollar`
weakened: the comparison is required only at real current coordinates `ξ` whose physical landing
`extendFrom H inv ξ` avoids the finite set `X ω` (for R.7: the current tip and the bounded pocket's
outgoing corner, where R.5 gives no comparison). The excluded prime ends are covered by Aux. 29,
with Wang–Wu's logarithmic local-set growth and the analytic lift of the current chart. The new
inputs are the base chart's analytic lift (`hc`), its continuous boundary extension (`hcExt`) and
landing at `∞` (`hcInf`), hitting measurability of the active complement (`hKm`), and boundedness
of the deterministic mean `u`. -/
theorem pocketStopPhaseSideLimit_of_collar_offExc {Ω ι : Type*}
    {ℳ : ι → MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {κ : ℝ} (hκ : 0 < κ) {nL nR : ℕ}
    {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ}
    {A : Set Ω} {γ : Ω → ℝ → ℂ} {xL : Ω → Fin (nL + 1) → ℝ}
    {xR : Ω → Fin (nR + 1) → ℝ} {c : Ω → Chart} {a : ℝ}
    {h₀ : Ω → DistOn upperHalfPlaneOpens} {u : ℂ → ℝ}
    {C : Ω → Set ℂ} {F : ι → Ω → Set ℂ} {q q₀ : ℝ≥0} {δ : Ω → ℝ}
    (hh₀ : IsZeroBoundaryGFF upperHalfPlaneOpens h₀ P)
    (hpre : ∀ i, locPrefixSigma (ℳ i) A γ q₀ ≤ mΩ)
    (hCo : ∀ ω ∈ A, IsOpen (C ω))
    (hFo : ∀ i ω, ω ∈ A → IsOpen (H \ F i ω))
    (hRawReference : ∀ i, PocketStopUnionLaw (ℳ i) P A γ C (F i) h₀ q₀)
    {liftB : ι → Ω → ℂ → ℝ}
    (hLattice : ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (γ ω) →
      ∃ m : ℤ, δ ω = m * phaseStep κ)
    (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω)) {ℓ : Ω → ℂ → ℂ}
    (hc : ∀ ω ∈ A, (c ω).IsConformal ∧ IsDerivLog (c ω).1 (ℓ ω) (c ω).dom ∧
      ∀ z ∈ (c ω).dom, (c ω).2.2 z = (ℓ ω z).im)
    (hcExt : ∀ ω ∈ A, ∃ E : ℂ → ℂ, EqOn E (c ω).2.1 H ∧ ContinuousOn E Hbar)
    (hcInf : ∀ ω ∈ A, ∃ p : ℂ,
      Tendsto (fun w => mob ((c ω).2.1 w)) (Bornology.cobounded ℂ ⊓ 𝓟 H) (𝓝 p))
    (hKm : Measurable[mΩ, hittingSigma] (activeCompl A γ c q))
    (hu : InnerProductSpace.HarmonicOnNhd u H) (hub : ∃ M : ℝ, ∀ z ∈ H, |u z| ≤ M)
    {X : Ω → Set ℂ} (hX : ∀ ω, (X ω).Finite)
    (hCollar : ∀ gB : ι → Ω → DistOn upperHalfPlaneOpens,
      (∀ i, IsLocalSetMean (liveExt A γ C (F i) q₀) h₀ P (gB i)) →
      ∀ g : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean (activeCompl A γ c q) h₀ P g →
      ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (γ ω) →
        ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ activeCompl A γ c q ω) →
          (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ activeCompl A γ c q ω →
            g ω φ = ∫ z, v z * φ z) →
          ∀ ξ : ℝ, ξ ∉ forceJumpSet
            (fun i => geomLW (fun t ω => segDriver (γ ω) t) xL i q ω - segDriver (γ ω) q)
            (fun j => geomRW (fun t ω => segDriver (γ ω) t) xR j q ω - segDriver (γ ω) q) →
            extendFrom H (relChart c γ q ω).2.1 ξ ∉ X ω →
            ∃ (i : ι) (b d : ℝ),
              let inv := (relChart c γ q ω).2.1;
              let vB := harmRep (gB i ω) (H \ liveExt A γ C (F i) q₀ ω);
              Tendsto (fun y => v (inv y) - vB (inv y)) (𝓝[H] (ξ : ℂ)) (𝓝 0) ∧
              Tendsto (fun y => vB (inv y) + u (inv y) + chiC κ * liftB i ω (inv y))
                (𝓝[H] (ξ : ℂ)) (𝓝 b) ∧
              Tendsto (fun y => (relChart c γ q ω).2.2 (inv y) - liftB i ω (inv y))
                (𝓝[H] (ξ : ℂ)) (𝓝 d) ∧
              b + chiC κ * d = phaseData κ ρL ρR
                (fun i => geomLW (fun t ω => segDriver (γ ω) t) xL i q ω - segDriver (γ ω) q)
                (fun j => geomRW (fun t ω => segDriver (γ ω) t) xR j q ω - segDriver (γ ω) q)
                (δ ω) ξ - a) :
    PocketStopPhaseSideLimit κ ρL ρR P A γ xL xR c a h₀ u (activeCompl A γ c q) δ q := by
  classical
  have hMeans : ∀ i, ∃ g : Ω → DistOn upperHalfPlaneOpens,
      IsLocalSetMean (liveExt A γ C (F i) q₀) h₀ P g := fun i =>
    (referenceFacts_of_unionLaw hh₀ (hpre i) hCo (hFo i) (hRawReference i)).2.2
  choose gB hgB using hMeans
  refine ⟨hLattice, fun g hg => ?_⟩
  -- the active complement is a local set (its mean exists by hypothesis)
  have hKopen : ∀ ω, activeCompl A γ c q ω ⊆ H ∧ IsOpen (H \ activeCompl A γ c q ω) := by
    intro ω
    refine ⟨fun z hz => hz.1, ?_⟩
    by_cases hl : ω ∈ A ∧ (q : ℝ≥0∞) < capLife (γ ω)
    · rw [H_diff_activeCompl_eq_relChart_dom hl.1 hl.2 (hγ ω hl.1) (hc ω hl.1).1]
      exact (relChart c γ q ω).dom.isOpen
    · have he : H \ activeCompl A γ c q ω = ∅ := eq_empty_of_forall_notMem fun z hz => by
        have hzd : z ∈ activeDom A γ c q ω := by
          by_contra h
          exact hz.2 ⟨hz.1, h⟩
        exact hl ⟨hzd.1, hzd.2.1⟩
      rw [he]
      exact isOpen_empty
  have hloc : IsLocalSet (activeCompl A γ c q) h₀ P :=
    ((isLocalSet_tfae hh₀ hKm (Eventually.of_forall hKopen)).out 3 4).1 (isGermConditionalLaw_iff.2 ⟨g, hg⟩)
  obtain ⟨M, hM⟩ := hub
  filter_upwards [Sec6.ae_abs_le_log_global_of_isLocalSetMean hh₀ hKm hloc hg,
    hCollar gB hgB g hg] with ω ⟨Kc, hKc⟩ hcol hωA hq v hv hvr ξ hξ
  have hγω := hγ ω hωA
  obtain ⟨hcc, hℓ, hlift⟩ := hc ω hωA
  set cur : Chart := relChart c γ q ω with hcur
  have hcurc : cur.IsConformal := isConformal_relChart_of_driven hγω hq hcc
  have hdom : H \ activeCompl A γ c q ω = (cur.dom : Set ℂ) :=
    H_diff_activeCompl_eq_relChart_dom hωA hq hγω hcc
  obtain ⟨L, hL, hLlift⟩ := exists_isDerivLog_relChart hγω hq hcc hℓ hlift
  have hA : ∀ z ∈ cur.dom, deriv cur.1 z = ‖deriv cur.1 z‖ * exp ((cur.2.2 z : ℂ) * I) := by
    intro z hz
    have := Aux2728Pocket.deriv_fwd_eq hL hLlift 0 z hz
    simpa only [Int.cast_zero, mul_zero, add_zero] using this
  have hAc : ContinuousOn cur.2.2 (cur.dom : Set ℂ) := by
    have := Aux2728Pocket.continuousOn_shift hL hLlift 0
    simpa only [Int.cast_zero, mul_zero, add_zero] using this
  obtain ⟨E, hE, hEc⟩ := hcExt ω hωA
  obtain ⟨p0, hp0⟩ := hcInf ω hωA
  obtain ⟨⟨Fx, hFx, hFxc⟩, hp⟩ := relChart_extension_and_limit hγω hq hE hEc hp0
  -- the corrected physical mean and its logarithmic growth
  set V : ℂ → ℝ := fun z => v z + u z + a with hVdef
  have hV : InnerProductSpace.HarmonicOnNhd V cur.dom := by
    intro z hz
    have hz' : z ∈ H \ activeCompl A γ c q ω := hdom ▸ hz
    exact ((hv z hz').add (hu z hz'.1)).add (InnerProductSpace.harmonicAt_const a)
  set K' : ℝ := max Kc 0 + max M 0 + |a| with hK'
  have hlog : ∀ z ∈ (cur.dom : Set ℂ),
      |V z| ≤ K' * (1 + Real.log (1 + ‖z‖) + Real.log (1 + 1 / infDist z (cur.dom : Set ℂ)ᶜ)) := by
    intro z hz
    have hz' : z ∈ H \ activeCompl A γ c q ω := hdom ▸ hz
    have h1 := hKc v hv hvr z hz'
    rw [hdom] at h1
    set B := 1 + Real.log (1 + ‖z‖) + Real.log (1 + 1 / infDist z (cur.dom : Set ℂ)ᶜ) with hB
    have hB1 : 1 ≤ B := by
      have e1 : 0 ≤ Real.log (1 + ‖z‖) := Real.log_nonneg (by linarith [norm_nonneg z])
      have e2 : 0 ≤ Real.log (1 + 1 / infDist z (cur.dom : Set ℂ)ᶜ) :=
        Real.log_nonneg (by linarith [one_div_nonneg.2 (infDist_nonneg (x := z) (s := (cur.dom : Set ℂ)ᶜ))])
      linarith
    have hu' : |u z| ≤ max M 0 := (hM z hz'.1).trans (le_max_left _ _)
    have hKc' : |v z| ≤ max Kc 0 * B :=
      h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith))
    have hM0 : 0 ≤ max M 0 := le_max_right _ _
    have ha : 0 ≤ |a| := abs_nonneg a
    calc |V z| ≤ |v z| + |u z| + |a| := by
          simp only [hVdef]
          exact (abs_add_le _ _).trans (add_le_add_left (abs_add_le _ _) _) |>.trans_eq (by ring)
      _ ≤ max Kc 0 * B + max M 0 * B + |a| * B := by nlinarith
      _ = K' * B := by rw [hK']; ring
  -- the seed coordinates bracket the driver
  have hwc : ContinuousOn (fun t => segDriver (γ ω) t) {t : ℝ≥0 | (t : WithTop ℝ≥0) < capLife (γ ω)} :=
    hγω.segDriver_spec.2.1
  have hL0 : geomLW (fun t ω => segDriver (γ ω) t) xL 0 q ω - segDriver (γ ω) q ≤ 0 :=
    sub_nonpos.2 (PocketMartLife.geomLW_le_of_lt (W := fun t ω => segDriver (γ ω) t) (ω := ω) hwc hq xL 0)
  have hR0 : 0 ≤ geomRW (fun t ω => segDriver (γ ω) t) xR 0 q ω - segDriver (γ ω) q :=
    sub_nonneg.2 (PocketMartLife.le_geomRW_of_lt (W := fun t ω => segDriver (γ ω) t) (ω := ω) hwc hq xR 0)
  -- the incident germs off the exceptional physical points
  have hInc : ∀ x : ℝ, x ∉ forceJumpSet
      (fun i => geomLW (fun t ω => segDriver (γ ω) t) xL i q ω - segDriver (γ ω) q)
      (fun j => geomRW (fun t ω => segDriver (γ ω) t) xR j q ω - segDriver (γ ω) q) → Fx x ∉ X ω →
      (∀ y ∈ forceJumpSet
        (fun i => geomLW (fun t ω => segDriver (γ ω) t) xL i q ω - segDriver (γ ω) q)
        (fun j => geomRW (fun t ω => segDriver (γ ω) t) xR j q ω - segDriver (γ ω) q), Fx x ≠ Fx y) →
      mob (Fx x) ≠ p0 →
      Tendsto (fun y => V (cur.2.1 y) + chiC κ * cur.2.2 (cur.2.1 y)) (𝓝[H] (x : ℂ))
        (𝓝 (phaseData κ ρL ρR
          (fun i => geomLW (fun t ω => segDriver (γ ω) t) xL i q ω - segDriver (γ ω) q)
          (fun j => geomRW (fun t ω => segDriver (γ ω) t) xR j q ω - segDriver (γ ω) q) (δ ω) x)) := by
    intro x hx hxX _ _
    have hland : extendFrom H cur.2.1 x = Fx x := by
      have hxcl : ((x : ℝ) : ℂ) ∈ closure H := by
        rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]
        exact real_mem_Hbar x
      exact extendFrom_eq hxcl (tendsto_inv_of_extension hFx hFxc (real_mem_Hbar x))
    obtain ⟨i, b, d', h1, h2, h3, h4⟩ := hcol hωA hq v hv hvr x hx (by rw [hland]; exact hxX)
    have hsum := (h1.add (h2.add (h3.const_mul (chiC κ)))).add_const a
    rw [zero_add, h4, sub_add_cancel] at hsum
    refine hsum.congr' (eventually_nhdsWithin_of_forall fun y _ => ?_)
    simp only [hVdef]
    ring
  have key := eqOn_phaseWordExt_of_landing_germs hκ ρL ρR hL0 hR0 (δ ω) hcurc hFx hFxc hp hV hlog hAc hA
    (hX ω) hInc
  have hext := (isBoundedHarmonicExtension_phaseWordExt hκ ρL ρR hL0 hR0 (δ ω)).2.2 ξ hξ
  refine (hext.sub_const a).congr' (eventually_nhdsWithin_of_forall fun y hy => ?_)
  have hk := key (cur.2.1 y) (hcurc.inv_mem_dom hy)
  rw [hcurc.2.2 y hy] at hk
  simp only [hVdef] at hk
  linarith

end InteractingSLE.Sec7.Aux29Cor
