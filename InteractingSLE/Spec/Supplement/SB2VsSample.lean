/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2VsCoord

/-!
# The stops along one sample (D19, step 4)

Packet PROVE-AUX61-NOJUMP (decision D19). **`sample_rules`** (deterministic): along one sample with
* a driven relative curve `ρ` (relative lifetime `U = capLife ρ`, relative trace `Γ = capTrace ρ`) and a driver `Wr`
  generating `Γ` before `U`;
* a clock `a` reading `Γ` at the physical times `t ∈ [t_L, Z)`, onto `[0, U)`, with `g (Γ (a t)) = η' t`;
* a record `r` decoding, on the closed half-plane, to a continuous gauge function `G ≤ 1` bounded by the physical
  parts `Aph F ∘ g`, `Bph ∘ g`, positive at `0`;
* a physical flow `η'` continuous on `[0, Z]`, ending on `F` at a finite `Z`, transient at an infinite `Z`,
the `m`-th stop rule along `Wr` is the gauge stop `localStop (gco G Γ U) m`, strictly below `U`, announced by Q3's
rules, and the gauge is positive at the relative trace before it.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.SB.Vs

open Exist.StagedLaw Supp8.GB6 Supp8.GB6.HullId Supp8.GB6.RelDrv.Version Supp8.Q3Stop Sec7.PocketTraversal

section Det

variable {G : ℂ → ℝ≥0∞} {g : ℂ → ℂ} {F : Set ℂ} {ρ : ℝ → ℂ} {Wr : ℝ≥0 → ℝ} {a : ℝ≥0 → ℝ≥0∞} {tL : ℝ≥0}
  {Z : ℝ≥0∞} {η' : ℝ≥0 → ℂ} {r : RecData}

/-- The relative trace of a driven curve starts at `0`. -/
theorem capTrace_zero (hd : IsDrivenCurve ρ) : capTrace ρ 0 = 0 := by
  unfold capTrace
  have h := hd.capInv_eq (u := 0) le_rfl
  rw [hd.capClock_zero] at h
  simp only [NNReal.coe_zero]
  rw [h]; exact hd.zero

/-- **The stops along one sample.** -/
theorem sample_rules (hGc : ContinuousOn G {z | 0 ≤ z.im}) (hG1 : ∀ z, G z ≤ 1)
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
    (hdec : ∀ z, 0 ≤ z.im → decode r z = (G z).toReal) (m : ℕ) :
    (localStop (gco G (capTrace ρ) (Sec7.Lemma71C.capLife ρ)) m : ℝ≥0∞) < Sec7.Lemma71C.capLife ρ ∧
      stopRule m (r, Wr) = localStop (gco G (capTrace ρ) (Sec7.Lemma71C.capLife ρ)) m ∧
      (∀ n, annRules gaugeRead m n (r, Wr) < localStop (gco G (capTrace ρ) (Sec7.Lemma71C.capLife ρ)) m) ∧
      ⨆ n, annRules gaugeRead m n (r, Wr) = localStop (gco G (capTrace ρ) (Sec7.Lemma71C.capLife ρ)) m ∧
      ∀ t : ℝ≥0, t < localStop (gco G (capTrace ρ) (Sec7.Lemma71C.capLife ρ)) m → 0 < G (capTrace ρ t) := by
  set U := Sec7.Lemma71C.capLife ρ with hUdef
  have hΓ0 : capTrace ρ 0 = 0 := capTrace_zero hd
  set Γ := capTrace ρ with hΓdef
  have hU0 : 0 < U := Vk.capLife_pos hd
  -- the relative trace lies in the closed half-plane and is continuous before `U`
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
  have hg0 : 0 < gco G Γ U 0 := by
    rw [gco_of_lt (by exact_mod_cast hU0), hΓ0]
    exact ENNReal.toReal_pos hG0.ne' (hfin 0)
  have hterm : ∀ T : ℝ≥0, (T : ℝ≥0∞) = U → gco G Γ U T = 0 := fun T hT => gco_of_le hT.ge
  have hlt : (localStop (gco G Γ U) m : ℝ≥0∞) < U := localStop_lt hgc hg0 hterm m
  -- the readback of the gauge along the driver through the stop
  have hrd : ∀ v ≤ localStop (gco G Γ U) m, gaugeRead v (r, Wr) = gco G Γ U v := fun v hv => by
    have hvU : (v : ℝ≥0∞) < U := lt_of_le_of_lt (ENNReal.coe_le_coe.2 hv) hlt
    obtain ⟨T, hvT, hTU⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hvU
    have htr' : LP.traceAt v Wr = Γ v :=
      LP.traceAt_eq_of_isGeneratingTrace (hgen T hTU) (hWrc.mono fun s hs => lt_trans hs hTU) hWr0 hvT
    simp only [gaugeRead]
    rw [htr', hdec _ (hΓH v hvU), gco_of_lt hvU]
  have h0 : gaugeRead 0 (r, fun _ => 0) = gco G Γ U 0 := by
    rw [gaugeRead_zero_zero, hdec 0 le_rfl, gco_of_lt (by exact_mod_cast hU0), hΓ0]
  obtain ⟨h1, h2, h3⟩ := rules_of_readback hgc hg0 m h0 hrd
  refine ⟨hlt, h1, h2, h3, fun t ht => ?_⟩
  -- before the stop the gauge exceeds the positive level
  have htU : (t : ℝ≥0∞) < U := lt_trans (ENNReal.coe_lt_coe.2 ht) hlt
  have hlev : gaugeLevel (gco G Γ U 0) m < gco G Γ U t := by
    by_contra hle
    rw [not_lt] at hle
    have := gaugeStop_le_of_le (ht.le.trans (gaugeStop_le _ _ _)) hle
    exact absurd this (not_le.2 ht)
  have hpos : 0 < gco G Γ U t := lt_trans (gaugeLevel_pos hg0 m) hlev
  rw [gco_of_lt htU] at hpos
  exact ENNReal.toReal_pos_iff.1 hpos |>.1

end Det

end InteractingSLE.Theorem14.SB.Vs
