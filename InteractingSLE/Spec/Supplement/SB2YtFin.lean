/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2FzFin
import InteractingSLE.Spec.Supplement.SB2YtAe

/-!
# SB2(1)'s late (S) line mean and driver link without the tip condition

Packet PROVE-T14-SB2DRV (round 13). **`sb2JxFinStatement_proved`**: `SB2JxFinStatement` from Theorems 1.2–1.3 alone
(R48). It is round 12's assembly (`sb2JxFinStatement_of_tip`, `SB2FzFin`) with the configuration data from
`ae_exists_isFinCfg_noTip`, which needs only the fixed-time interior of the flow (`RLC.OrdLate.ae_mem_H_at`) instead
of the named hypothesis `SB2JxTipStatement`. Hence

* **`sb2LineSMeanLateStatement_proved`**: the late regime of the (S) line mean;
* **`sb2DriverLinkAmbStatement_of_versionR_proved`**: SB2(1)'s driver link from Theorems 1.2–1.3 and
  PROVE-AUX61-NOJUMP's `SB2LineVersionRStatement`;
* **`sb2LineSMeanStatement_proved`**, **`sb2LineUnionStatement_proved`**, **`sb2LineKernelRStatement_proved`**: the
  (S) line mean, the line union input and this packet's kernel half `SB2LineKernelRStatement` (R108).

`SB2JxTipStatement` is no longer an input of anything.

**R48.** Theorems 1.2–1.3 appear only as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal ENNReal
open QuantumZipper (chiC H fwdMap fwdHull logDerivFwd)
open LQGMetric (DistOn TestOn)
open SupercriticalConformalCovariance.GM24 (smoothDist)

universe u

namespace InteractingSLE.Theorem14.SB.Lv

open Restart Exist Exist.Staged Exist.StagedLaw GW1W GW1Conn WalkInf Restart.DomainMarkov Restart.DomainMarkov.K2
  Supp8.Q3Stop Sec7.PocketTraversal LocalSets Sec6
open Supp8.Q3Chain (flowedData flowedJumps initJumps)

/-- **`SB2JxFinStatement` holds** (Theorems 1.2–1.3 as hypotheses, R48; no other input). -/
theorem sb2JxFinStatement_proved (h12p : Theorem12ParamStatement.{u}) (h13 : Exist.Theorem13Statement.{u}) :
    SB2JxFinStatement.{u} := by
  intro κ b jumps Ω mΩ _ P _ h E k u ψ η ζ HP I u₀ hu₀ D Vd wt hwt A' hA'H hA'm hA'ae t h' 𝓕 W VL VR B htrans hC
    htr hX τ hτ hτζ hτt K hKm hKe gU hgU φ
  classical
  have hκ := HP.kappa_pos
  /- the coupling's coordinates -/
  obtain ⟨u₀', hu₀'⟩ := Sec4.exists_isBoundedHarmonicExtension_forceBoundaryData κ (flowLineRhoL κ b jumps u ψ)
    (flowLineRhoR κ b jumps u ψ) (flowLineXL b jumps u) (flowLineXR b jumps u)
  obtain ⟨hrel, e1, e2⟩ := centredField_coupling HP hu₀ htrans hu₀'
  have hh0' := WholeField.isZeroBoundaryGFF_centredField hC hu₀'
  obtain ⟨hAm, hAc, hdA, hlA, gW, hgW, hg₁⟩ := walkFill_coupling h12p h13 HP hu₀ hA'H hA'm hA'ae e1 e2
  obtain ⟨hKc, hlKK⟩ := hull_coupling hκ hC hu₀' hX hτ hτζ hKm hKe
  obtain ⟨hgAK, hlAK, hAKc⟩ := union_coupling hh0' e1 hAm hAc hKm hKc hgU
  obtain ⟨g₂K, hg₂K⟩ := isGermConditionalLaw_iff.1 (((isLocalSet_tfae hh0' hKm hKc).out 4 3).1 hlKK)
  have hind₂K := GW2Fb.ae_eqOn_explMean_stop hκ hC hu₀' hh0' hX hτ hτζ hKe hKm hg₂K
  /- the measurable co-null set where the hull version is the coupling hull -/
  have hGae : ∀ᵐ ω ∂P, K ω = fwdHull (fun r : ℝ => W r.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0) ∧
      ((((τ ω).untopD 0 : ℝ≥0) : ℝ≥0∞) < ζ ω ∧ ContinuousOn (fun s => W s ω) {s | (s : ℝ≥0∞) < ζ ω}) ∧
      W 0 ω = 0 ∧ IsGeneratingTrace (fun s => W s ω) (ζ ω) (fun s => η ω s - u) := by
    filter_upwards [hKe, hτζ, LawUnique.IsIntegratedSLEEvolution.ae_continuousOn_driving hC.1, hC.1.2.2.2.2, htr]
      with ω h1 h2 h3 h4 h5
    have hsτ := coe_untopD_of_le (hτt ω)
    have hsζ : ((((τ ω).untopD 0 : ℝ≥0) : WithTop ℝ≥0) : ℝ≥0∞) < ζ ω := by rw [hsτ]; exact h2
    exact ⟨h1, ⟨hsζ, h3.1⟩, h4.1, h5⟩
  obtain ⟨G, hGm, hGc, hGsp⟩ := exists_measurableSet_subset_of_ae hGae
  have hGae' : ∀ᵐ ω ∂P, ω ∈ G := ae_iff.2 hGc
  /- the configuration event -/
  obtain ⟨Cfg, hCfg⟩ : ∃ Cfg : Ω → Prop, ∀ ω, Cfg ω ↔ (ω ∈ G ∧ ω ∈ lineLive Vd wt t ∧
      firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω)) < (t : ℝ≥0∞) ∧
      (t : WithTop ℝ≥0) ≤ τ ω ∧ (t : ℝ≥0∞) < ζ ω ∧
      ((I.chart ω).dom : Set ℂ) = H \ walkFill κ b jumps E k A' ω ∧
      IsFinCfg Vd wt t A' ω (finCfg Vd wt t A' ω)) := ⟨_, fun ω => Iff.rfl⟩
  have hCτ : ∀ ω, Cfg ω → ((τ ω).untopD 0 : ℝ≥0) = t := fun ω hD => by
    have he : τ ω = (t : WithTop ℝ≥0) := le_antisymm (hτt ω) ((hCfg ω).1 hD).2.2.2.1
    rw [he]
    rfl
  /- FIN's literal driver, time and hull -/
  obtain ⟨wF, hwC, hwG, hw0⟩ := exists_finDriver Cfg (fun ω => (finCfg Vd wt t A' ω).w) (G := G) (W := W)
    (ζ := ζ) (τ' := fun ω => ((τ ω).untopD 0 : ℝ≥0)) fun ω hω => (hGsp ω hω).2.1
  obtain ⟨tF, htG, htG'⟩ : ∃ tF : Ω → ℝ, (∀ ω ∈ G, tF ω = (((τ ω).untopD 0 : ℝ≥0) : ℝ)) ∧ (∀ ω ∉ G, tF ω = 0) :=
    ⟨fun ω => if ω ∈ G then (((τ ω).untopD 0 : ℝ≥0) : ℝ) else 0, fun ω hω => ite_eq_left hω,
      fun ω hω => ite_eq_right hω⟩
  obtain ⟨LΨF, hLC, hLC'⟩ : ∃ L : Ω → ℂ → ℂ, (∀ ω, Cfg ω → L ω = (finCfg Vd wt t A' ω).LΨ) ∧
      (∀ ω, ¬ Cfg ω → L ω = fun z => ((Lw.shiftChart (I.chart ω) u 0).2.2 z : ℂ) * Complex.I) :=
    ⟨fun ω => if Cfg ω then (finCfg Vd wt t A' ω).LΨ else
      fun z => ((Lw.shiftChart (I.chart ω) u 0).2.2 z : ℂ) * Complex.I,
      fun ω hω => ite_eq_left hω, fun ω hω => ite_eq_right hω⟩
  have hCfgHull : ∀ ω, Cfg ω → fwdHull (wF ω) (tF ω) = K ω ∧ ∃ t₂ : ℝ, (t : ℝ) < t₂ ∧
      EqOn (finCfg Vd wt t A' ω).w (fun r : ℝ => W r.toNNReal ω) (Icc 0 t₂) := fun ω hD => by
    obtain ⟨hGω, -, -, -, htζ, -, hFin⟩ := (hCfg ω).1 hD
    have hcf := hFin.2.2.2.2
    obtain ⟨hK, ⟨-, hWc⟩, hW0, htrω⟩ := hGsp ω hGω
    obtain ⟨t₂, htt₂, hEq⟩ := exists_eqOn_cfgDriver hcf.hw hcf.hw0 hcf.hη hWc hW0 htrω htζ hFin.2.1
    refine ⟨?_, t₂, htt₂, hEq⟩
    rw [hwC ω hD, htG ω hGω, hK, hCτ ω hD]
    exact LocalExt.fwdHull_congr_of_eqOn_of_lt t.coe_nonneg htt₂ hEq
  have hon : ∀ ω ∈ G, fwdHull (wF ω) (tF ω) = K ω := fun ω hω => by
    by_cases hD : Cfg ω
    · exact (hCfgHull ω hD).1
    · rw [htG ω hω, (hwG ω hω hD).2.2, (hGsp ω hω).1]
  have hoff : ∀ ω ∉ G, fwdHull (wF ω) (tF ω) = ∅ := fun ω hω => by
    have hD : ¬ Cfg ω := fun hD => hω ((hCfg ω).1 hD).1
    rw [hw0 ω hω hD, htG' ω hω]
    exact QuantumZipper.RS.fwdHull_zero_eq_empty continuous_zero
  have hwcont : ∀ ω, Continuous (wF ω) := fun ω => by
    by_cases hD : Cfg ω
    · rw [hwC ω hD]
      exact ((hCfg ω).1 hD).2.2.2.2.2.2.2.2.2.2.hw
    · by_cases hω : ω ∈ G
      · exact (hwG ω hω hD).1
      · rw [hw0 ω hω hD]
        exact continuous_zero
  have htF0 : ∀ ω, 0 ≤ tF ω := fun ω => by
    by_cases hω : ω ∈ G
    · rw [htG ω hω]
      exact NNReal.coe_nonneg _
    · rw [htG' ω hω]
  /- FIN's hull and union inputs -/
  have hLm : Measurable[mΩ, hittingSigma] fun ω => fwdHull (wF ω) (tF ω) := measurable_fwdHull_switch hGm hKm hon hoff
  have hlitK : ∀ᵐ ω ∂P, fwdHull (wF ω) (tF ω) = K ω := by
    filter_upwards [hGae'] with ω hω
    exact hon ω hω
  have hlK := Exist.Staged.IsLocalSet.congr_ae hlKK hlitK
  have hLc : ∀ᵐ ω ∂P, fwdHull (wF ω) (tF ω) ⊆ H ∧ IsOpen (H \ fwdHull (wF ω) (tF ω)) := by
    filter_upwards [hlitK, hKc] with ω h1 h2
    rw [h1]
    exact h2
  have hUeq : ∀ᵐ ω ∂P, (fun z : ℂ => z + (-u : ℝ)) '' walkFill κ b jumps E k A' ω ∪ fwdHull (wF ω) (tF ω) =
      (fun z : ℂ => z + (-u : ℝ)) '' walkFill κ b jumps E k A' ω ∪ K ω := by
    filter_upwards [hlitK] with ω h1
    rw [h1]
  have hlU := Exist.Staged.IsLocalSet.congr_ae hlAK hUeq
  have hULm := LocalSets.measurable_union_hitting hAm hLm
  have hULc : ∀ᵐ ω ∂P, (fun z : ℂ => z + (-u : ℝ)) '' walkFill κ b jumps E k A' ω ∪ fwdHull (wF ω) (tF ω) ⊆ H ∧
      IsOpen (H \ ((fun z : ℂ => z + (-u : ℝ)) '' walkFill κ b jumps E k A' ω ∪ fwdHull (wF ω) (tF ω))) := by
    filter_upwards [hUeq, hAKc] with ω h1 h2
    rw [h1]
    exact h2
  obtain ⟨gF, hgF⟩ := isGermConditionalLaw_iff.1 (((isLocalSet_tfae hh0' hULm hULc).out 4 3).1 hlU)
  obtain ⟨g₂F, hg₂F⟩ := isGermConditionalLaw_iff.1 (((isLocalSet_tfae hh0' hLm hLc).out 4 3).1 hlK)
  have hgg := IsLocalSetMean.ae_eq_of_ae_eq_set hh0' hULm (LocalSets.measurable_union_hitting hAm hKm) hULc hAKc
    hlU hlAK hUeq hgF hgAK
  have hg₂g := IsLocalSetMean.ae_eq_of_ae_eq_set hh0' hLm hKm hLc hKc hlK hlKK hlitK hg₂F hg₂K
  have hunbA := ae_unb_walkFill_translate HP hA'ae (-u)
  have hunbK : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (fwdHull (wF ω) (tF ω)),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (fwdHull (wF ω) (tF ω))) z) :=
    ae_of_all _ fun ω => unb_fwdHull (hwcont ω) (htF0 ω)
  /- FIN's chart -/
  have hcF : ∀ ω, (Lw.shiftChart (I.chart ω) u 0).IsConformal := fun ω =>
    isConformal_lw_shiftChart (isConformal_chart I ω) u 0
  have hℓ : ∀ ω, ContinuousOn (Lw.shiftChart (I.chart ω) u 0).2.2 (Lw.shiftChart (I.chart ω) u 0).dom := fun ω => by
    rw [Shift.dom_shiftChart]
    have hc : ContinuousOn (I.chart ω).2.2 ((I.chart ω).dom : Set ℂ) := I.chart_measurable.2.1 ω
    show ContinuousOn (fun z => (I.chart ω).2.2 (z + (u : ℂ))) _
    refine hc.comp (continuousOn_id.add continuousOn_const) ?_
    rintro _ ⟨y, hy, rfl⟩
    show y - (u : ℂ) + u ∈ ((I.chart ω).dom : Set ℂ)
    rw [sub_add_cancel]
    exact hy
  have hlift : ∀ ω, ∀ y ∈ H, (Lw.shiftChart (I.chart ω) u 0).2.2 ((Lw.shiftChart (I.chart ω) u 0).2.1 y) =
      (LΨF ω ((Lw.shiftChart (I.chart ω) u 0).2.1 y)).im + 0 := fun ω y hy => by
    rw [add_zero]
    by_cases hD : Cfg ω
    · obtain ⟨-, -, -, -, -, hdomω, hFin⟩ := (hCfg ω).1 hD
      rw [hLC ω hD]
      exact hFin.2.2.2.1 (shift_inv_mem_sdiff (isConformal_chart I ω) hdomω u hy)
    · rw [hLC' ω hD]
      simp only [Complex.mul_I_im, Complex.ofReal_re]
  /- FIN's union mean -/
  have hfin := FinRel.ae_chartTransport_eq_couplingMean_of_relConfigJK (κ := κ) (h := h') (u₀ := u₀') (P := P)
    (A := fun ω => (fun z : ℂ => z + (-u : ℝ)) '' walkFill κ b jumps E k A' ω)
    (Ψ := fun ω => (Lw.shiftChart (I.chart ω) u 0).1) (Ψi := fun ω => (Lw.shiftChart (I.chart ω) u 0).2.1)
    (LΨ := LΨF) (Sb := fun _ => ∅) (w := wF) (Wr := fun ω => (finCfg Vd wt t A' ω).Wr)
    (η := fun ω => (finCfg Vd wt t A' ω).ηw) (ηr := fun ω => (finCfg Vd wt t A' ω).ηr) (t := tF)
    (u := fun ω => ((Vd.a t ω).toNNReal : ℝ)) (lam := Real.pi / Real.sqrt κ)
    (β₀ := fun ω => forceBoundaryData κ (typedRhoL wt) (typedRhoR wt) (cellXL κ ψ I.word wt ω)
      (cellXR κ ψ I.word wt ω))
    (βE := fun ω => flowedData κ (flowLineRhoL κ b jumps u ψ) (flowLineRhoR κ b jumps u ψ) (flowLineXL b jumps u)
      (flowLineXR b jumps u) (wF ω) (tF ω))
    (βu := fun ω => flowedData κ (typedRhoL wt) (typedRhoR wt) (cellXL κ ψ I.word wt ω) (cellXR κ ψ I.word wt ω)
      (finCfg Vd wt t A' ω).Wr ((Vd.a t ω).toNNReal : ℝ))
    (S₀ := fun ω => initJumps (cellXL κ ψ I.word wt ω) (cellXR κ ψ I.word wt ω))
    (SE := fun ω => flowedJumps (flowLineXL b jumps u) (flowLineXR b jumps u) (wF ω) (tF ω))
    (Su := fun ω => flowedJumps (cellXL κ ψ I.word wt ω) (cellXR κ ψ I.word wt ω) (finCfg Vd wt t A' ω).Wr
      ((Vd.a t ω).toNNReal : ℝ))
    (G₀ := fun ω => (finCfg Vd wt t A' ω).G₀) (GE := fun ω => (finCfg Vd wt t A' ω).GE)
    (G := fun ω => (finCfg Vd wt t A' ω).G)
    (v := fun ω z => (finCfg Vd wt t A' ω).G (fwdMap (finCfg Vd wt t A' ω).Wr ((Vd.a t ω).toNNReal : ℝ)
        ((Lw.shiftChart (I.chart ω) u 0).1 z)) -
      chiC κ * ((logDerivFwd (finCfg Vd wt t A' ω).Wr ((Vd.a t ω).toNNReal : ℝ)
        ((Lw.shiftChart (I.chart ω) u 0).1 z)).im + (LΨF ω z).im))
    (D := {ω | Cfg ω}) (c := fun ω => Lw.shiftChart (I.chart ω) u 0) (ℓ₀ := 0)
    hh0' hu₀'.1 hu₀'.2.1 hAm hLm hdA hlA hlK hlU hunbA hunbK hgF hg₁ hg₂F ?hcfg ?hind₁ ?hind₂ hcF hℓ
    (fun _ _ _ => rfl) hlift 0
  case hcfg =>
    refine ae_of_all _ fun ω hD => ?_
    obtain ⟨hGω, -, -, -, -, -, hFin⟩ := (hCfg ω).1 hD
    rw [hwC ω hD, htG ω hGω, hCτ ω hD, hLC ω hD]
    exact hFin.2.2.2.2
  case hind₁ =>
    filter_upwards [ae_hind₁_line h12p h13 HP I hu₀ hA'H hA'm hA'ae hrel hgW D.event wt] with ω hω hD
    obtain ⟨-, hlive, -, -, -, -, hFin⟩ := (hCfg ω).1 hD
    rw [hLC ω hD]
    exact hω (D.event_subset hlive.1.1.1) hlive.1.1 _ _ hFin.2.2.2.1 hFin.2.2.2.2.bhe₀
  case hind₂ =>
    filter_upwards [hind₂K, hg₂g] with ω hω hgω hD w₂ hw₂ hrep
    obtain ⟨hGω, -, -, -, -, -, hFin⟩ := (hCfg ω).1 hD
    obtain ⟨hhull, t₂, htt₂, hEq⟩ := hCfgHull ω hD
    have hcf := hFin.2.2.2.2
    have hτ' := hCτ ω hD
    rw [hhull] at hw₂ hrep ⊢
    rw [hwC ω hD, htG ω hGω, hτ']
    have hrep' : ∀ φ' : TestOn upperHalfPlaneOpens, tsupport φ' ⊆ H \ K ω →
        g₂K ω φ' = ∫ z, w₂ z * φ' z := fun φ' hφ' => by
      rw [← hgω]
      exact hrep φ' hφ'
    have key := hω (finCfg Vd wt t A' ω).w t₂ hcf.hw hcf.hw0 (by rw [hτ']; exact htt₂) (fun r hr => hEq hr)
      (finCfg Vd wt t A' ω).GE (by rw [hτ']; exact hcf.bheE) w₂ hw₂ hrep'
    rw [hτ'] at key
    exact key
  /- reading FIN's conclusion in the launch chart -/
  filter_upwards [hfin, hgg, hGae', ae_exists_isFinCfg_noTip Vd hwt t hA'ae, Vd.alive wt hwt t,
    ae_dom_eq_H_sdiff_walkFill HP I hA'ae] with ω hfω hggω hGω hexω halω hdomω hcell hlt hdisj hlate htτ
  have hl : ω ∈ launchSet κ b jumps E (k + 1) := D.event_subset hcell.1.1
  have hlive : ω ∈ lineLive Vd wt t := ⟨hcell, hlt⟩
  have hFin := isFinCfg_finCfg Vd wt t A' (hexω hlive hlate)
  have hD : Cfg ω := (hCfg ω).2 ⟨hGω, hlive, hlate, htτ, halω hcell hlt, hdomω hl, hFin⟩
  have hcf := hFin.2.2.2.2
  have hxL : ∀ i, cellXL κ ψ I.word wt ω i ≤ 0 := (FCDet.isOrderedForceWord_typeXL (I.word ω)).2.1
  have hxR : ∀ j, 0 ≤ cellXR κ ψ I.word wt ω j := (FCDet.isOrderedForceWord_typeXL (I.word ω)).2.2.2
  have hsV : (((Vd.a t ω).toNNReal : ℝ≥0) : ℝ≥0∞) <
      FCDet.thr (typedRhoL wt) (typedRhoR wt) Vd.W (cellXL κ ψ I.word wt) (cellXR κ ψ I.word wt) ω := by
    rw [ENNReal.coe_toNNReal hFin.2.2.1]
    exact hlt
  obtain ⟨hdisj', hint⟩ := integral_couplingMean_fin (typedRhoL wt) (typedRhoR wt) Vd.W_cont Vd.W_zero hxL hxR
    hcf.hWr hcf.hWr0 hFin.1 hsV hcf.bheu (c := 0 + chiC κ * 0) (by ring) φ hdisj
  have hF := hfω hD φ hdisj'
  beta_reduce at hF
  rw [hint] at hF
  have hh' := Lemma75Bridge.eq_flowField_of_isTranslateAddConst (htrans ω)
  have e4 : WholeField.centredField h' u₀' ω = Exist.flowField u 0 (WholeField.centredField h u₀ ω) := by
    rw [e1, neg_neg]
  have e5 : h' ω - WholeField.centredField h' u₀' ω = smoothDist upperHalfPlaneOpens u₀' := by
    simp only [WholeField.centredField, sub_sub_cancel]
  have e3 : gF ω + smoothDist upperHalfPlaneOpens u₀' =
      Exist.flowField u 0 (gU ω) + (h' ω - Exist.flowField u 0 (WholeField.centredField h u₀ ω)) := by
    rw [hggω, neg_neg, ← e4, e5]
  rw [e3, chartTransport_fin_back (isConformal_chart I ω) (hcF ω) (ψ * chiC κ) (chiC κ) hh' φ] at hF
  exact hF

/-- **The late regime of the (S) line mean holds** (Theorems 1.2–1.3 as hypotheses). -/
theorem sb2LineSMeanLateStatement_proved (h12p : Theorem12ParamStatement.{u}) (h13 : Exist.Theorem13Statement.{u}) :
    SB2LineSMeanLateStatement.{u} :=
  sb2LineSMeanLateStatement_of_fin h12p h13 (sb2JxFinStatement_proved h12p h13)

/-- **SB2(1)'s driver link from Theorems 1.2–1.3 and the version half (PROVE-AUX61-NOJUMP) alone.** -/
theorem sb2DriverLinkAmbStatement_of_versionR_proved (h12p : Theorem12ParamStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (hV : SB2LineVersionRStatement.{u}) : SB2DriverLinkAmbStatement.{u} :=
  sb2DriverLinkAmbStatement_of_versionR_fin h12p h13 hV (sb2JxFinStatement_proved h12p h13)

/-- **The (S) line mean holds** (both regimes; Theorems 1.2–1.3 as hypotheses). -/
theorem sb2LineSMeanStatement_proved (h12p : Theorem12ParamStatement.{u}) (h13 : Exist.Theorem13Statement.{u}) :
    SB2LineSMeanStatement.{u} :=
  sb2LineSMeanStatement_of_late h12p h13 (sb2LineSMeanLateStatement_proved h12p h13)

/-- **The line union input holds** (Theorems 1.2–1.3 as hypotheses). -/
theorem sb2LineUnionStatement_proved (h12p : Theorem12ParamStatement.{u}) (h13 : Exist.Theorem13Statement.{u}) :
    SB2LineUnionStatement.{u} :=
  sb2LineUnionStatement_of_sMean h12p h13 (sb2LineSMeanStatement_proved h12p h13)

/-- **The kernel half (R108) holds**: K2's (S) and (L) for the chart field on every type cell of the entrance event,
from every repaired line version (Theorems 1.2–1.3 as hypotheses). -/
theorem sb2LineKernelRStatement_proved (h12p : Theorem12ParamStatement.{u}) (h13 : Exist.Theorem13Statement.{u}) :
    SB2LineKernelRStatement.{u} :=
  sb2LineKernelStatement_of_union h12p h13 (sb2LineUnionStatement_proved h12p h13)

/-- **K2's line data in the entrance σ-algebra from the version half (PROVE-AUX61-NOJUMP) alone** (Theorems 1.2–1.3
as hypotheses). -/
theorem sb2EntranceLinesStatement_of_versionR_proved (h12p : Theorem12ParamStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (hV : SB2LineVersionRStatement.{u}) : SB2EntranceLinesStatement.{u} :=
  sb2EntranceLinesStatement_of_halvesR hV (sb2LineKernelRStatement_proved h12p h13)

end InteractingSLE.Theorem14.SB.Lv
