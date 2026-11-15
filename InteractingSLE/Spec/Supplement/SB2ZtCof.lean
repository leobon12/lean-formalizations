/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2VtSeed
import InteractingSLE.Spec.Supplement.SB2VsVer

/-!
# SB2(1)'s final gluing, part 1: the stops exhaust the relative lifetime

Packet PROVE-T14-SB2DRV (round 16, D4/D10/D19: SB2(1)'s driver link from the successor version half). The stops of
PROVE-AUX61-NOJUMP's version (`Vs.SB2StopData`, `Vs.stopRule`: the first time a gauge read from (record, relative
path) falls below a level, capped) are cofinal in the relative lifetime: almost surely on the entrance event, every
relative time before the lifetime is passed by some stop. The gauge is the minimum of three parts (distance of the
physical read-back to the physical bad set, decay at infinity, distance of the relative tip to the closed relative bad
set of the launch word); along the trace before the lifetime all three are positive:

* the physical read-back is the flow before `ζ`, off NOJUMP's closed bad set (`GoodAt.avoid`);
* **`readback_mem_sb2BadClosure`** (deterministic, the general-time form of `Vt.not_seed_of_good`): a point of the
  closure of the relative bad set is read back into the closed physical bad set (the second clause, through
  `Vt.phys_bad_right`, `Vt.phys_bad_left`, and continuity of the read-back), so the relative tip avoids it too.

* `sample_cofinal` (deterministic): positivity of the gauge before the lifetime gives cofinal stops
  (`exists_lt_localStop`, `Vs.sample_rules`);
* `sb2_cofinal`: the same at one good sample (the setup of `Vs.sb2_sample`);
* **`SB2StopData.ae_cofinal`**.

**R48.** Theorems 1.2–1.3 are not used here beyond the committed inputs. No source theorem is replaced.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Zt

open Exist Exist.StagedLaw Exist.Staged Restart GW1W Lv Sec7.PocketTraversal Supp8.Q3Stop Vs Vr
open Supp8.GB6 Supp8.GB6.HullId Supp8.GB6.RelDrv.Version

/-! ### The read-back of the closed relative bad set -/

section Corr

variable {κ ψ u m : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {c : Chart} {g : ℂ → ℂ} {β cw : BoundaryWord}
  {Fw : Finset ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

/-- **The closure of the relative bad set is read back into the closed physical bad set** (deterministic). Let `g`
extend the inverse of the shifted launch chart continuously to the closed half-plane and let the launch word `cw` be
the witness word `β` shifted by the entry `m`, with the second clause. Then `g` maps the closure of the relative bad
set of the word's flow type into NOJUMP's closed bad set of the flow from `u`. -/
theorem readback_mem_sb2BadClosure (hκ : 0 < κ) (hκ4 : κ < 4) (hψ : -(Real.pi / 2) < ψ)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hcc : c.IsConformal) (hgc : ContinuousOn g {z | 0 ≤ z.im})
    (hgi : EqOn g (Lw.shiftChart c u m).2.1 H) (hSC : SecondClause κ b jumps c u m β.fn β.jumps)
    (hcw : ∀ y ∉ Fw, cw.fn y = β.fn (y + m)) (hft : FCDet.IsFlowType κ ψ cw xL xR ρL ρR) {z : ℂ}
    (hz : z ∈ closure (badSet xL xR ρL ρR)) : g z ∈ sb2BadClosure κ b jumps u ψ := by
  set gc : ℂ → ℂ := fun w => g (w - m) + u with hgcdef
  have hgcc : ContinuousOn gc {w | 0 ≤ w.im} := by
    refine (hgc.comp (continuous_id.sub continuous_const).continuousOn fun w hw => ?_).add continuousOn_const
    show 0 ≤ (w - (m : ℂ)).im
    simpa using hw
  have hgci : EqOn gc c.2.1 H := by
    intro w hw
    have hw' : w - (m : ℂ) ∈ H := by
      show 0 < (w - (m : ℂ)).im
      simpa using (show 0 < w.im from hw)
    simp only [hgcdef, hgi hw', Lw.shiftChart_inv, sub_add_cancel]
  have hgy : ∀ y : ℝ, gc ((y + m : ℝ) : ℂ) = g (y : ℂ) + u := fun y => by
    simp only [hgcdef]; push_cast; ring_nf
  -- the bad points themselves
  have hbad : ∀ z' ∈ badSet xL xR ρL ρR, g z' ∈ sb2BadClosure κ b jumps u ψ := by
    rintro z' ⟨him, hz'⟩
    have hz'e : z' = ((z'.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
    have key : ∀ x₀ : ℝ, gc ((z'.re + m : ℝ) : ℂ) = x₀ → x₀ ∈ closure (Vt.origBad κ ψ u b) →
        g z' ∈ sb2BadClosure κ b jumps u ψ := fun x₀ hx₀ hcl => by
      have hmem := Vt.mem_sb2BadClosure_of_mem_closure_origBad hκ hb hcl
      have e : g z' = ((x₀ - u : ℝ) : ℂ) := by
        rw [hgy, ← hz'e] at hx₀
        push_cast
        rw [← hx₀]; ring
      rw [e]; exact hmem
    rcases hz' with ⟨hy, hw⟩ | ⟨hy, hw⟩
    · obtain ⟨x₀, hx₀, hcl⟩ := Vt.phys_bad_right hκ hκ4 hψ hb hcc hgcc hgci hSC hcw hft hy hw
      exact key x₀ hx₀ hcl
    · obtain ⟨x₀, hx₀, hcl⟩ := Vt.phys_bad_left hκ hb hcc hgcc hgci hSC hcw hft hy hw
      exact key x₀ hx₀ hcl
  -- the closure, by continuity of the read-back on the real line
  have hreal : closure (badSet xL xR ρL ρR) ⊆ {w : ℂ | 0 ≤ w.im} :=
    closure_minimal (fun w hw => le_of_eq (badSet_subset_real hw).symm)
      (isClosed_le continuous_const Complex.continuous_im)
  have himg := (hgc.mono hreal).image_closure (s := badSet xL xR ρL ρR)
  have hsub : g '' badSet xL xR ρL ρR ⊆ sb2BadClosure κ b jumps u ψ := by
    rintro _ ⟨z', hz', rfl⟩; exact hbad z' hz'
  have hcl : closure (g '' badSet xL xR ρL ρR) ⊆ sb2BadClosure κ b jumps u ψ :=
    closure_minimal hsub isClosed_closure
  exact hcl (himg ⟨z, hz, rfl⟩)

end Corr

/-! ### Cofinal stops from a positive gauge -/

section Det

variable {G : ℂ → ℝ≥0∞} {g : ℂ → ℂ} {F : Set ℂ} {ρ : ℝ → ℂ} {Wr : ℝ≥0 → ℝ} {a : ℝ≥0 → ℝ≥0∞} {tL : ℝ≥0}
  {Z : ℝ≥0∞} {η' : ℝ≥0 → ℂ} {r : RecData}

/-- **The stops are cofinal when the gauge is positive along the trace before the lifetime** (deterministic). -/
theorem sample_cofinal (hGc : ContinuousOn G {z | 0 ≤ z.im}) (hG1 : ∀ z, G z ≤ 1)
    (hGA : ∀ z, G z ≤ Aph F (g z)) (hGB : ∀ z, G z ≤ Bph (g z)) (hG0 : 0 < G 0)
    (hd : IsDrivenCurve ρ)
    (hgen : ∀ T : ℝ≥0∞, T < Sec7.Lemma71C.capLife ρ → IsGeneratingTrace Wr T (capTrace ρ))
    (hWrc : ContinuousOn Wr {t | (t : ℝ≥0∞) < Sec7.Lemma71C.capLife ρ}) (hWr0 : Wr 0 = 0)
    (ham : Monotone a) (htZ : (tL : ℝ≥0∞) < Z)
    (hread : ∀ t : ℝ≥0, tL ≤ t → (t : ℝ≥0∞) < Z → a t < Sec7.Lemma71C.capLife ρ ∧
      0 ≤ (capTrace ρ (a t).toNNReal).im ∧ g (capTrace ρ (a t).toNNReal) = η' t)
    (hsurj : ∀ s : ℝ≥0, (s : ℝ≥0∞) < Sec7.Lemma71C.capLife ρ → ∃ t : ℝ≥0, tL ≤ t ∧ (t : ℝ≥0∞) < Z ∧ a t = s)
    (hη' : ContinuousOn η' {t | (t : ℝ≥0∞) ≤ Z}) (hend : ∀ T : ℝ≥0, (T : ℝ≥0∞) = Z → η' T ∈ F)
    (htr : Z = ⊤ → Tendsto (fun t => ‖η' t‖) atTop atTop)
    (hdec : ∀ z, 0 ≤ z.im → decode r z = (G z).toReal)
    (hpos : ∀ s : ℝ≥0, (s : ℝ≥0∞) < Sec7.Lemma71C.capLife ρ → 0 < G (capTrace ρ s)) :
    ∀ s : ℝ≥0, (s : ℝ≥0∞) < Sec7.Lemma71C.capLife ρ → ∃ m : ℕ, (s : ℝ≥0∞) < stopRule m (r, Wr) := by
  set U := Sec7.Lemma71C.capLife ρ with hUdef
  set Γ := capTrace ρ with hΓdef
  have hΓH : ∀ s : ℝ≥0, (s : ℝ≥0∞) < U → 0 ≤ (Γ s).im := fun s hs => by
    obtain ⟨t, htL, htZ', hts⟩ := hsurj s hs
    have := (hread t htL htZ').2.1
    rwa [hts, ENNReal.toNNReal_coe] at this
  have hΓc : ContinuousOn Γ {s | (s : ℝ≥0∞) < U} := Vk.continuousOn_of_forall_lt hgen
  have hread' : ∀ t : ℝ≥0, tL ≤ t → (t : ℝ≥0∞) < Z → a t < U ∧ g (Γ (a t).toNNReal) = η' t :=
    fun t h1 h2 => ⟨(hread t h1 h2).1, (hread t h1 h2).2.2⟩
  have hgc : Continuous (gco G Γ U) :=
    continuous_gco hGc hG1 hGA hGB hΓc hΓH ham htZ hread' hsurj hη' hend htr
  have hfin : ∀ z, G z ≠ ⊤ := fun z => ne_top_of_le_ne_top ENNReal.one_ne_top (hG1 z)
  intro s hs
  have hp : ∀ v ≤ s, 0 < gco G Γ U v := fun v hv => by
    have hvU : (v : ℝ≥0∞) < U := lt_of_le_of_lt (ENNReal.coe_le_coe.2 hv) hs
    rw [gco_of_lt hvU]
    exact ENNReal.toReal_pos (hpos v hvU).ne' (hfin _)
  obtain ⟨m, hm⟩ := exists_lt_localStop hgc hp
  refine ⟨m, ?_⟩
  rw [(sample_rules hGc hG1 hGA hGB hG0 hd hgen hWrc hWr0 ham htZ hread hsurj hη' hend htr hdec m).2.1]
  exact ENNReal.coe_lt_coe.2 hm

end Det

/-! ### Cofinal stops at a good sample -/

section Sample

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u ψ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}

/-- **SB2(1)'s stops are cofinal at one good sample** (the setup of `Vs.sb2_sample`, with the second clause at the
sample for the relative part of the gauge). -/
theorem sb2_cofinal (hκ : 0 < κ) (hκ4 : κ < 4) (hψ : -(Real.pi / 2) < ψ)
    (hb : IsPiecewiseConstantBoundaryData b jumps)
    (I : K2LaunchInputs κ b jumps P h E k u ψ) {ω : Ω} {ρω : ℝ → ℂ} {Wr : ℝ≥0 → ℝ}
    {a : ℝ≥0 → ℝ≥0∞}
    (hT : Ve.entT κ b jumps E k u η ζ ω < ζ ω)
    (h1 : ζ ω = ⊤ → EqOn ρω (Vd.liftR (Ve.flowLift κ b jumps E k u η ζ ω)) (Ici 0))
    (h2 : ζ ω ≠ ⊤ → EqOn ρω (relCurve (Vd.liftR (Ve.flowLift κ b jumps E k u η ζ ω))
      ((ζ ω).toReal - (Ve.entT κ b jumps E k u η ζ ω).toReal)) (Ici 0))
    (hd : IsDrivenCurve ρω) (hcl : Sec7.Lemma71C.capLife ρω = Vk.relLife κ b jumps E k u η ζ ω)
    (hgen : ∀ T : ℝ≥0∞, T < Sec7.Lemma71C.capLife ρω → IsGeneratingTrace Wr T (capTrace ρω))
    (hWrc : ContinuousOn Wr {t | (t : ℝ≥0∞) < Sec7.Lemma71C.capLife ρω}) (hWr0 : Wr 0 = 0)
    (hac : Continuous a) (ham : Monotone a)
    (hclock : ∀ t, a t = Vc.clockOf (Ve.flowLift κ b jumps E k u η ζ ω) (Ve.entT κ b jumps E k u η ζ ω).toNNReal
      (ζ ω) t)
    (hc0 : Sec7.Lemma71C.capClock (fun r : ℝ => Ve.flowLift κ b jumps E k u η ζ ω r.toNNReal) 0 = 0)
    (hmono : ∀ T₁ : ℝ≥0, (Ve.entT κ b jumps E k u η ζ ω).toNNReal ≤ T₁ → (T₁ : ℝ≥0∞) < ζ ω →
      MonotoneOn (Sec7.Lemma71C.capClock fun r : ℝ => Ve.flowLift κ b jumps E k u η ζ ω r.toNNReal)
        (Icc 0 ((T₁ : ℝ) - (Ve.entT κ b jumps E k u η ζ ω).toNNReal)))
    (hinv : ∃ g : ℂ → ℂ, ContinuousOn g {z | 0 ≤ z.im} ∧
      EqOn g (Lw.shiftChart (Lv.launchChart κ b jumps E (k + 1) ω) u (launchEntry κ b jumps E (k + 1) u ω)).2.1 H ∧
      ∀ r : ℝ≥0, (((Ve.entT κ b jumps E k u η ζ ω).toNNReal + r : ℝ≥0) : ℝ≥0∞) < ζ ω →
        0 ≤ (Ve.flowLift κ b jumps E k u η ζ ω r).im ∧
        g (Ve.flowLift κ b jumps E k u η ζ ω r) = η ω ((Ve.entT κ b jumps E k u η ζ ω).toNNReal + r) - u)
    (hchart : iChart I ω = (Lv.launchChart κ b jumps E (k + 1) ω).recenter (launchEntry κ b jumps E (k + 1) u ω))
    (hηc : ContinuousOn (η ω) {t | (t : ℝ≥0∞) ≤ ζ ω})
    (htr : ζ ω = ⊤ → Tendsto (fun t => ‖η ω t‖) atTop atTop)
    (htip : 0 < ζ ω → ζ ω ≠ ⊤ → Vq.IsBadPoint (flowLineXL b jumps u) (flowLineXR b jumps u)
      (flowLineRhoL κ b jumps u ψ) (flowLineRhoR κ b jumps u ψ) (η ω (ζ ω).toNNReal - u))
    (hnv : 0 < ζ ω → ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → η ω t - u ∉ sb2BadClosure κ b jumps u ψ)
    {w : WordType} (hw : w ∈ I.types) (hcell : angleWordType κ ψ (I.word ω) = w)
    (hseed : ¬ ForceWord.ThresholdCondition (typedRhoL w) (typedRhoR w) 0 (cellXL κ ψ I.word w ω)
      (cellXR κ ψ I.word w ω))
    (hcc : (Lv.launchChart κ b jumps E (k + 1) ω).IsConformal) {β : BoundaryWord} {Fw : Finset ℝ}
    (hSC : SecondClause κ b jumps (Lv.launchChart κ b jumps E (k + 1) ω) u (launchEntry κ b jumps E (k + 1) u ω)
      β.fn β.jumps)
    (hcw : ∀ y ∉ Fw, (I.word ω).fn y = β.fn (y + launchEntry κ b jumps E (k + 1) u ω))
    (hft : FCDet.IsFlowType κ ψ (I.word ω) (cellXL κ ψ I.word w ω) (cellXR κ ψ I.word w ω) (typedRhoL w)
      (typedRhoR w)) :
    ∀ s : ℝ≥0, (s : ℝ≥0∞) < Sec7.Lemma71C.capLife ρω → ∃ m : ℕ, (s : ℝ≥0∞) < stopRule m (sb2Rec I ω, Wr) := by
  obtain ⟨g, hgc, hgi, hgr⟩ := hinv
  set tL := (Ve.entT κ b jumps E k u η ζ ω).toNNReal with htLdef
  set γ := Ve.flowLift κ b jumps E k u η ζ ω with hγdef
  set F := sb2BadClosure κ b jumps u ψ with hFdef
  have hTLtop : Ve.entT κ b jumps E k u η ζ ω ≠ ⊤ := ne_top_of_lt hT
  have htZ : (tL : ℝ≥0∞) < ζ ω := by rw [htLdef, ENNReal.coe_toNNReal hTLtop]; exact hT
  have hζ0 : 0 < ζ ω := lt_of_le_of_lt zero_le hT
  set G := gaugeExt F κ ψ I.word I.types g ω with hGdef
  have hread0 : ∀ t : ℝ≥0, tL ≤ t → (t : ℝ≥0∞) < ζ ω →
      a t = ENNReal.ofReal (Sec7.Lemma71C.capClock (Vd.liftR γ) ((t - tL : ℝ≥0) : ℝ)) ∧
      capTrace ρω (Sec7.Lemma71C.capClock (Vd.liftR γ) ((t - tL : ℝ≥0) : ℝ)).toNNReal = γ (t - tL) ∧
      ENNReal.ofReal (Sec7.Lemma71C.capClock (Vd.liftR γ) ((t - tL : ℝ≥0) : ℝ)) < Sec7.Lemma71C.capLife ρω := by
    intro t htL htζ
    have hsub : (((t - tL : ℝ≥0) : ℝ)) = (t : ℝ) - tL := NNReal.coe_sub htL
    have hs : ((((Ve.entT κ b jumps E k u η ζ ω).toNNReal + (t - tL) : ℝ≥0) : ℝ≥0∞)) < ζ ω := by
      rw [← htLdef, add_tsub_cancel_of_le htL]; exact htζ
    obtain ⟨hc1, hc2⟩ := Vk.capTrace_capClock hd hT h1 h2 hs
    refine ⟨?_, ?_, hc2⟩
    · rw [hclock, Vc.clockOf_eq htL htζ (hmono t htL htζ), hsub]; rfl
    · rw [hc1]; show γ (((t - tL : ℝ≥0) : ℝ)).toNNReal = _; rw [Real.toNNReal_coe]
  have hread : ∀ t : ℝ≥0, tL ≤ t → (t : ℝ≥0∞) < ζ ω → a t < Sec7.Lemma71C.capLife ρω ∧
      0 ≤ (capTrace ρω (a t).toNNReal).im ∧ g (capTrace ρω (a t).toNNReal) = η ω t - u := by
    intro t htL htζ
    obtain ⟨ha, hc1, hc2⟩ := hread0 t htL htζ
    have hat : (a t).toNNReal = (Sec7.Lemma71C.capClock (Vd.liftR γ) ((t - tL : ℝ≥0) : ℝ)).toNNReal := by
      rw [ha]; exact ENNReal.toNNReal_coe _
    have hs : ((tL + (t - tL) : ℝ≥0) : ℝ≥0∞) < ζ ω := by rw [add_tsub_cancel_of_le htL]; exact htζ
    obtain ⟨him, hg⟩ := hgr (t - tL) hs
    refine ⟨ha ▸ hc2, ?_, ?_⟩
    · rw [hat, hc1]; exact him
    · rw [hat, hc1, hg, add_tsub_cancel_of_le htL]
  have hatL : a tL = 0 := by
    rw [(hread0 tL le_rfl htZ).1, tsub_self, NNReal.coe_zero]
    show ENNReal.ofReal (Sec7.Lemma71C.capClock (fun r : ℝ => γ r.toNNReal) 0) = 0
    rw [hc0, ENNReal.ofReal_zero]
  have hsurj : ∀ s : ℝ≥0, (s : ℝ≥0∞) < Sec7.Lemma71C.capLife ρω →
      ∃ t : ℝ≥0, tL ≤ t ∧ (t : ℝ≥0∞) < ζ ω ∧ a t = s := by
    intro s hs
    rw [hcl] at hs
    obtain ⟨s', hs'⟩ := lt_iSup_iff.1 hs
    obtain ⟨hs'ζ, hs's⟩ := lt_iSup_iff.1 hs'
    set t₁ := tL + s' with ht₁
    have ht₁ζ : (t₁ : ℝ≥0∞) < ζ ω := hs'ζ
    have hat₁ : a t₁ = ENNReal.ofReal (Sec7.Lemma71C.capClock (Vd.liftR γ) (s' : ℝ)) := by
      rw [(hread0 t₁ le_self_add ht₁ζ).1, ht₁, add_tsub_cancel_left]
    have hmem : (s : ℝ≥0∞) ∈ Icc (a tL) (a t₁) := ⟨by rw [hatL]; exact zero_le, by rw [hat₁]; exact hs's.le⟩
    obtain ⟨t, ht, hts⟩ := intermediate_value_Icc (le_self_add : tL ≤ t₁) hac.continuousOn hmem
    exact ⟨t, ht.1, lt_of_le_of_lt (ENNReal.coe_le_coe.2 ht.2) ht₁ζ, hts⟩
  have hGc : ContinuousOn G {z | 0 ≤ z.im} := continuousOn_gaugeExt F κ ψ I.word I.types hgc ω
  have hG1 : ∀ z, G z ≤ 1 := gaugeExt_le_one F κ ψ I.word I.types g ω
  have hGA : ∀ z, G z ≤ Aph F (g z) := fun z => (min_le_left _ _).trans (min_le_left _ _)
  have hGB : ∀ z, G z ≤ Bph (g z) := fun z => (min_le_left _ _).trans (min_le_right _ _)
  have hg0 : g 0 = η ω tL - u := by
    have := (hread tL le_rfl htZ).2.2
    rwa [hatL, ENNReal.toNNReal_zero, capTrace_zero hd] at this
  have hBpos : ∀ x : ℂ, 0 < Bph x := fun x => by unfold Bph; rw [ENNReal.ofReal_pos]; positivity
  have hG0 : 0 < G 0 := by
    refine lt_min (lt_min ?_ (hBpos _)) (pos_relGauge_zero hw hcell hseed)
    refine lt_min ?_ one_pos
    rw [hg0, infEDist_pos_iff_notMem_closure, hFdef, sb2BadClosure, closure_closure]
    exact hnv hζ0 tL htZ
  have hη' : ContinuousOn (fun t => η ω t - u) {t | (t : ℝ≥0∞) ≤ ζ ω} := hηc.sub continuousOn_const
  have hend : ∀ T : ℝ≥0, (T : ℝ≥0∞) = ζ ω → η ω T - u ∈ F := by
    intro T hTe
    have hb' := htip hζ0 (by rw [← hTe]; exact ENNReal.coe_ne_top)
    rw [← hTe, ENNReal.toNNReal_coe] at hb'
    exact subset_closure hb'
  have htr' : ζ ω = ⊤ → Tendsto (fun t => ‖η ω t - u‖) atTop atTop := fun hζ => by
    refine tendsto_atTop_mono (fun t => ?_) (tendsto_atTop_add_const_right _ (-‖(u : ℂ)‖) (htr hζ))
    have := norm_sub_norm_le (η ω t) (u : ℂ)
    linarith
  have hgH : ∀ z ∈ H, g z = (iChart I ω).2.1 z - u := fun z hz => by
    rw [hgi hz, hchart]; rfl
  have hdec : ∀ z, 0 ≤ z.im → decode (sb2Rec I ω) z = (G z).toReal := fun z hz =>
    decode_sb2Record (iChart I) u F κ ψ I.word I.types hgc hgH hz
  -- the gauge is positive along the trace before the lifetime
  have hpos : ∀ s : ℝ≥0, (s : ℝ≥0∞) < Sec7.Lemma71C.capLife ρω → 0 < G (capTrace ρω s) := by
    intro s hs
    obtain ⟨t, htL, htζ, hts⟩ := hsurj s hs
    obtain ⟨-, -, hgt⟩ := hread t htL htζ
    rw [hts, ENNReal.toNNReal_coe] at hgt
    have hnF : g (capTrace ρω s) ∉ F := by rw [hgt]; exact hnv hζ0 t htζ
    refine lt_min (lt_min (lt_min ?_ one_pos) (hBpos _)) ?_
    · rw [infEDist_pos_iff_notMem_closure, hFdef, sb2BadClosure, closure_closure]
      exact hnF
    · rw [relGauge_eq κ ψ I.word I.types hw hcell]
      refine lt_min ?_ one_pos
      rw [infEDist_pos_iff_notMem_closure, closure_closure]
      exact fun hmem => hnF (readback_mem_sb2BadClosure hκ hκ4 hψ hb hcc hgc hgi hSC hcw hft hmem)
  exact sample_cofinal hGc hG1 hGA hGB hG0 hd hgen hWrc hWr0 ham htZ hread hsurj hη' hend htr' hdec hpos

end Sample

/-! ### Almost surely on the entrance event -/

section AE

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u ψ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
  {u₀ : ℂ → ℝ}

/-- **The stops of NOJUMP's stop data are cofinal in the relative lifetime**, almost surely on the entrance event. -/
theorem ae_cofinal (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ) {I : K2LaunchInputs κ b jumps P h E k u ψ}
    {D : EntranceUnion κ b jumps P h E k u η ζ u₀} (S : SB2StopData HP I D) :
    ∀ᵐ ω ∂P, ω ∈ D.event → ω ∈ S.Gs ∧ ∀ s : ℝ≥0, (s : ℝ≥0∞) < Sec7.Lemma71C.capLife (S.ρ ω) →
      ∃ m : ℕ, (s : ℝ≥0∞) < S.Vstop m ω := by
  obtain ⟨β, Y, hW, hβ⟩ := sb2StageActiveWord2Statement κ HP.kappa_pos HP.kappa_lt_four b jumps HP.boundary P h
    HP.field HP.admissible E HP.staged HP.pieces_regular HP.drivers_regular k
  filter_upwards [S.ae_mem_Gs, hβ u HP.seed_nonpos, Vt.ae_word_eq_shift HP I hW, hW.2.2.1]
    with ω hG hβω heqω hTω hD
  have hGs := hG hD
  have hg := S.good hGs
  have hF := hg.launch
  obtain ⟨⟨c₀, θ₀⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hF
  have hc₀ : Lv.launchChart κ b jumps E (k + 1) ω =
      stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (k + 1)) := by
    rw [launchChart_eq hcθ, (eq_launch_of_launches _ _ hcθ).2.2]
  have hcc : (Lv.launchChart κ b jumps E (k + 1) ω).IsConformal := by rw [hc₀]; exact (hTω hF).1
  have hcell : ω ∈ wordTypeCell κ ψ I.word D.event (angleWordType κ ψ (I.word ω)) := ⟨hD, rfl⟩
  have hft := FCDet.isFlowType_of_mem_typeSet (mem_typeSet_of_mem_wordTypeCell hcell)
  have hρω := S.ρ'_eq hGs
  have hgen : ∀ T : ℝ≥0∞, T < Sec7.Lemma71C.capLife (S.ρ ω) →
      IsGeneratingTrace (S.Wr · ω) T (capTrace (S.ρ ω)) := fun T hT => by
    have := S.isGeneratingTrace_Wr ω (T := T) (by rw [hρω]; exact hT)
    rwa [hρω] at this
  have hWrc : ContinuousOn (S.Wr · ω) {t | (t : ℝ≥0∞) < Sec7.Lemma71C.capLife (S.ρ ω)} := by
    have := S.continuousOn_Wr ω
    rwa [hρω] at this
  exact ⟨hGs, sb2_cofinal HP.kappa_pos HP.kappa_lt_four HP.angle HP.boundary I hg.ent hg.fam1 hg.fam2 hg.driven
    hg.life hgen hWrc (S.Wr_zero ω) (S.hac ω) (S.ham ω) hg.clock hg.c0 hg.mono hg.inv hg.chart hg.cont hg.trans
    hg.tip hg.avoid hg.cover rfl hg.seed hcc (hβω hF).2 (heqω hF) hft⟩

end AE

end InteractingSLE.Theorem14.SB.Zt
