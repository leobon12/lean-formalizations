/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6GaugeETerminal

/-!
# The physical endpoint alternatives at a finite relative lifetime

An exact inverse of the increasing relative clock eventually exceeds every
strictly pre-contact physical time. Thus it converges to finite first contact,
or tends to infinity. Trace continuity and source transience give precisely
the physical terminal alternatives used by the separation readout.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Complex
open scoped NNReal ENNReal

namespace InteractingSLE.Supp8.GB6.GaugeE

open Exist.StagedLaw ReadD RelDrv

/-- The inverse clock eventually passes every strictly preterminal physical
time as relative time approaches its finite lifetime from below. -/
theorem eventually_lt_clockInverse {a : ℝ≥0 → ℝ} {c : ℝ≥0 → ℝ≥0} {Tc : ℝ≥0∞} {T : ℝ≥0}
    (hm : StrictMonoOn a {t | (t : ℝ≥0∞) < Tc})
    (hb : ∀ t : ℝ≥0, (t : ℝ≥0∞) < Tc → 0 ≤ a t ∧ a t < T)
    (hc : ∀ u : ℝ≥0, u < T → (c u : ℝ≥0∞) < Tc ∧ a (c u) = u)
    {v : ℝ≥0} (hv : (v : ℝ≥0∞) < Tc) : ∀ᶠ u : ℝ≥0 in 𝓝[<] T, v < c u := by
  have hav := hb v hv
  have havT : (a v).toNNReal < T := by
    rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hav.1]
    exact hav.2
  have hnear : ∀ᶠ u : ℝ≥0 in 𝓝[<] T, (a v).toNNReal < u :=
    mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds havT)
  have hu : ∀ᶠ u : ℝ≥0 in 𝓝[<] T, u < T := self_mem_nhdsWithin
  filter_upwards [hnear, hu] with u hlu hu
  by_contra hle
  have hcu := hc u hu
  have hmono := hm.monotoneOn hcu.1 hv (le_of_not_gt hle)
  rw [hcu.2] at hmono
  have hlt : a v < (u : ℝ) := by
    simpa only [Real.coe_toNNReal _ hav.1] using NNReal.coe_lt_coe.2 hlu
  exact (not_lt_of_ge hmono) hlt

/-- At infinite physical contact time the inverse clock tends to infinity. -/
theorem tendsto_clockInverse_top {a : ℝ≥0 → ℝ} {c : ℝ≥0 → ℝ≥0} {T : ℝ≥0}
    (hm : StrictMonoOn a {t | (t : ℝ≥0∞) < ⊤})
    (hb : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ⊤ → 0 ≤ a t ∧ a t < T)
    (hc : ∀ u : ℝ≥0, u < T → (c u : ℝ≥0∞) < ⊤ ∧ a (c u) = u) :
    Tendsto c (𝓝[<] T) atTop := by
  apply tendsto_atTop.2
  intro v
  exact (eventually_lt_clockInverse hm hb hc (v := v) ENNReal.coe_lt_top).mono fun _ h => h.le

/-- At finite physical contact time the inverse clock converges to it. -/
theorem tendsto_clockInverse_finite {a : ℝ≥0 → ℝ} {c : ℝ≥0 → ℝ≥0} {C T : ℝ≥0}
    (hm : StrictMonoOn a {t | (t : ℝ≥0∞) < (C : ℝ≥0∞)})
    (hb : ∀ t : ℝ≥0, (t : ℝ≥0∞) < (C : ℝ≥0∞) → 0 ≤ a t ∧ a t < T)
    (hc : ∀ u : ℝ≥0, u < T → (c u : ℝ≥0∞) < (C : ℝ≥0∞) ∧ a (c u) = u) :
    Tendsto c (𝓝[<] T) (𝓝 C) := by
  apply tendsto_order.2
  constructor
  · intro v hv
    exact eventually_lt_clockInverse hm hb hc (ENNReal.coe_lt_coe.2 hv)
  · intro v hv
    have hu : ∀ᶠ u : ℝ≥0 in 𝓝[<] T, u < T := self_mem_nhdsWithin
    exact hu.mono fun u hu => (ENNReal.coe_lt_coe.1 (hc u hu).1).trans hv

/-- The source hypotheses prove the terminal contact-or-escape alternatives
for every relative driver satisfying the full source coordinates. -/
theorem hasPhysicalTerminalLimits {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ θ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {J : Finset ℝ}
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {W Wα D : ℝ≥0 → Ω → ℝ}
    {ζα L : Ω → ℝ≥0∞} {γ α : Ω → ℝ≥0 → ℂ}
    (hF : IsFlowLineDriver κ b J θ P h Wα ζα)
    (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (Wα · ω) (ζα ω) (α ω))
    (hW : ∀ᵐ ω ∂P, Continuous (W · ω) ∧ W 0 ω = 0 ∧ IsGeneratingTrace (W · ω) ⊤ (γ ω) ∧
      Tendsto (fun t => ‖γ ω t‖) atTop atTop)
    (s : ℝ≥0) (hs : 0 < s) (hC : SourceC.RelativeDriverCoordinates s P W Wα ζα γ α D L) :
    HasPhysicalTerminalLimits s P (gb6Rec s Wα ζα) D L := by
  classical
  have hW' : ∀ᵐ ω ∂P, Continuous (W · ω) ∧ W 0 ω = 0 ∧ IsGeneratingTrace (W · ω) ⊤ (γ ω) :=
    hW.mono (fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩)
  filter_upwards [ae_physicalReadback hκ hκ4 hF hα hW' s hs hC, hC.relative,
    ae_gb6RecGood hF hα s, hW, hα, ae_driver_zero_continuousOn hF]
    with ω hread hcoords hgood hcounter hflow hreg hrec T hTL
  obtain ⟨hsζ, hsH⟩ := (mem_gb6TS_iff hgood).2 hrec
  obtain ⟨_, ham, _, _, hcapacity⟩ := hread hsζ hsH
  obtain ⟨_, hhulls⟩ := hcoords hsζ hsH
  let a := gb6Clock s W Wα ω
  let Tc := gb6Tc s γ α ω
  change StrictMonoOn a {t | (t : ℝ≥0∞) < Tc} at ham
  have hbound : ∀ t : ℝ≥0, (t : ℝ≥0∞) < Tc → 0 ≤ a t ∧ a t < T := by
    intro t ht
    obtain ⟨hn, hl, _⟩ := hhulls t ht
    refine ⟨hn, ?_⟩
    rw [← hTL] at hl
    simpa only [ENNReal.coe_toReal] using (ENNReal.ofReal_lt_iff_lt_toReal hn ENNReal.coe_ne_top).1 hl
  have hex : ∀ u : ℝ≥0, u < T → ∃ t : ℝ≥0, (t : ℝ≥0∞) < Tc ∧ a t = u ∧
      physicalTrace s u (gb6Rec s Wα ζα ω, (fun v => D v ω)) = γ ω t := by
    intro u hu
    apply hcapacity u
    rw [← hTL]
    exact ENNReal.coe_lt_coe.2 hu
  let c : ℝ≥0 → ℝ≥0 := fun u => if hu : u < T then (hex u hu).choose else 0
  have hcspec : ∀ u : ℝ≥0, u < T → (c u : ℝ≥0∞) < Tc ∧ a (c u) = u ∧
      physicalTrace s u (gb6Rec s Wα ζα ω, (fun v => D v ω)) = γ ω (c u) := by
    intro u hu
    simpa only [c, hu, ↓reduceDIte] using (hex u hu).choose_spec
  have hc : ∀ u : ℝ≥0, u < T → (c u : ℝ≥0∞) < Tc ∧ a (c u) = u :=
    fun u hu => ⟨(hcspec u hu).1, (hcspec u hu).2.1⟩
  have hu : ∀ᶠ u : ℝ≥0 in 𝓝[<] T, u < T := self_mem_nhdsWithin
  have he : (fun u => γ ω (c u)) =ᶠ[𝓝[<] T]
      (fun u => physicalTrace s u (gb6Rec s Wα ζα ω, (fun v => D v ω))) :=
    hu.mono (fun u hu => (hcspec u hu).2.2.symm)
  have hγc : Continuous (γ ω) := by
    have hh := hcounter.2.2.1.2.1
    simp only [le_top, ofPred_true] at hh
    exact continuousOn_univ.1 hh
  rcases eq_top_or_lt_top Tc with htop | hfin
  · right
    have hm : StrictMonoOn a {t | (t : ℝ≥0∞) < ⊤} := by simpa only [htop] using ham
    have hb : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ⊤ → 0 ≤ a t ∧ a t < T := by simpa only [htop] using hbound
    have hc' : ∀ u : ℝ≥0, u < T → (c u : ℝ≥0∞) < ⊤ ∧ a (c u) = u := by simpa only [htop] using hc
    have hinf := hcounter.2.2.2.comp (tendsto_clockInverse_top hm hb hc')
    exact hinf.congr' (he.mono (fun _ h => congrArg norm h))
  · let C := Tc.toNNReal
    have hTc : Tc = (C : ℝ≥0∞) := (ENNReal.coe_toNNReal hfin.ne).symm
    have hm : StrictMonoOn a {t | (t : ℝ≥0∞) < (C : ℝ≥0∞)} := by simpa only [hTc] using ham
    have hb : ∀ t : ℝ≥0, (t : ℝ≥0∞) < (C : ℝ≥0∞) → 0 ≤ a t ∧ a t < T := by simpa only [hTc] using hbound
    have hc' : ∀ u : ℝ≥0, u < T → (c u : ℝ≥0∞) < (C : ℝ≥0∞) ∧ a (c u) = u := by simpa only [hTc] using hc
    have hlim := ((hγc.tendsto C).comp (tendsto_clockInverse_finite hm hb hc')).congr' he
    have hA : IsCompact ((fun v => (α ω v : OnePoint ℂ)) '' Icc 0 s) := by
      have hcompact : IsCompact (α ω '' Icc 0 s) := isCompact_Icc.image_of_continuousOn
        (hflow.2.1.mono fun v hv => (ENNReal.coe_le_coe.2 hv.2).trans hsζ.le)
      simpa only [image_image] using hcompact.image OnePoint.continuous_coe
    obtain ⟨v, hv, hcontact⟩ := firstContactTime_mem
      (continuous_sphereInv.comp (OnePoint.continuous_coe.comp hγc)) hA.isClosed hTc
    left
    refine ⟨γ ω C, v, hv.2, ?_, hlim⟩
    rw [recordTrace_eq s hreg.1 hreg.2 hflow hsζ hv.2]
    exact (SourceC.sphereInv_eq_iff _ _).1 hcontact.symm

end InteractingSLE.Supp8.GB6.GaugeE
