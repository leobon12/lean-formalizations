/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2TlGauge

/-!
# N4 item 1 in launch coordinates, part 4: the launch gauge along every relative coordinate

Packet PROVE-GW2-RELDET (decision D20). The cap-gauge hypothesis of RELDET's version families
(`exists_versionsA_of_capGauge_strict`, `exists_schedVersionsA_strict_gauge`) for the launch gauge `launchGauge`:

* **`launchGauge_sample`** (one sample): given GB6's read-back facts (clock `a` strictly increasing and continuous
  before the first contact, reading back the explored trace; every relative time before the life is a clock value),
  BUF's time rule, and a launch word read off the driver up to `T`, the gauge is continuous before the life `L`,
  positive before `launchLife` and zero at it, and `0 < launchLife`;
* **`ae_launchGauge_coord`**: the same along EVERY `SourceC.RelativeDriverCoordinates`, almost surely on the record
  event (GB6's `ae_physicalReadback_nr`, `ae_separationRead_regular_nr`; BUF's `ae_timeCapRule_coord`,
  `ae_min_timeCapRule_coord`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.GW2Rd

open Exist.StagedLaw Supp8 Supp8.GB6 Supp8.GB6.RelDrv Supp8.GB6.RelDrv.Version Supp8.GB6.HullId
open Restart (BoundaryWord)

variable {κ θ : ℝ} {B : (ℝ≥0 → ℝ) → BoundaryWord} {T cap : ℝ≥0}

section Sample

variable {s : ℝ≥0} {p : RecData × (ℝ≥0 → ℝ)} {a : ℝ≥0 → ℝ} {Tc L : ℝ≥0∞} {γ : ℝ≥0 → ℂ} {W : ℝ≥0 → ℝ}

/-- **The launch gauge along one sample of relative coordinates.** -/
theorem launchGauge_sample (hBc : ∀ w : ℝ≥0 → ℝ, (∀ u ≤ T, w u = W u) → B w = B W)
    (hγ : IsGeneratingTrace W ⊤ γ) (hW : Continuous W) (hW0 : W 0 = 0) (ha0 : a 0 = 0)
    (ham : StrictMonoOn a {t | (t : ℝ≥0∞) < Tc})
    (haL : ∀ t : ℝ≥0, (t : ℝ≥0∞) < Tc → 0 ≤ a t ∧ ENNReal.ofReal (a t) < L)
    (hback : ∀ u : ℝ≥0, (u : ℝ≥0∞) < L → ∃ t : ℝ≥0, (t : ℝ≥0∞) < Tc ∧ a t = u)
    (hread : ∀ t : ℝ≥0, (t : ℝ≥0∞) < Tc → ReadD.physicalTrace s (a t).toNNReal p = γ t)
    (hXc : ContinuousOn (fun u => ReadD.physicalTrace s u p) {u | (u : ℝ≥0∞) < L})
    (hrule : ∀ Δ : ℝ≥0, (Δ : ℝ≥0∞) < Tc → timeCapRule s Δ p = ENNReal.ofReal (a Δ))
    (hruleL : ∀ Δ : ℝ≥0, ¬ (Δ : ℝ≥0∞) < Tc → L ≤ timeCapRule s Δ p) :
    0 < launchLife κ θ B T cap W a Tc ∧
      ContinuousOn (fun t => launchGauge κ θ B T cap s t p) {t | (t : ℝ≥0∞) < L} ∧
      (∀ t : ℝ≥0, (t : ℝ≥0∞) < L → (t : ℝ≥0∞) < launchLife κ θ B T cap W a Tc →
        0 < launchGauge κ θ B T cap s t p) ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < L → (t : ℝ≥0∞) = launchLife κ θ B T cap W a Tc →
        launchGauge κ θ B T cap s t p = 0 := by
  classical
  set f := launchDist κ θ B T W with hfdef
  set d0 := launchStart κ θ B W with hd0def
  have hfc : Continuous f := continuous_launchDist hγ hW hW0
  have hf0 : f 0 = d0 := launchDist_zero W
  have hfnn : ∀ σ, 0 ≤ f σ := fun σ => badDist_nonneg _ _
  set ψ : ℝ≥0 → ℝ≥0 := fun t => (physTimeR s t p).toNNReal with hψdef
  have hψ : ∀ t : ℝ≥0, (t : ℝ≥0∞) < L → (ψ t : ℝ≥0∞) < Tc ∧ a (ψ t) = t := by
    intro t ht
    obtain ⟨t', ht', hat⟩ := hback t ht
    have he : ψ t = t' := by
      simp only [hψdef, physTimeR_eq ham hrule hruleL ht ht' hat, ENNReal.toNNReal_coe]
    rw [he]
    exact ⟨ht', hat⟩
  set g : ℝ≥0 → ℝ := fun σ => if d0 = 0 then 1 else min 1 (f σ / d0) with hgdef
  have hrep : ∀ t : ℝ≥0, (t : ℝ≥0∞) < L → launchGauge κ θ B T cap s t p = g (min cap (ψ t - T)) := fun t ht =>
    launchGauge_eq (fun w hw => hBc w hw) hγ hW hW0 ham haL hread hXc hrule hruleL ht (hψ t ht).1 (hψ t ht).2
  set Z : Set ℝ≥0 := {σ | σ ≤ cap ∧ f σ = 0} with hZdef
  have hZc : IsClosed Z := (isClosed_le continuous_id continuous_const).inter (isClosed_eq hfc continuous_const)
  -- the life, unfolded
  have hlife : launchLife κ θ B T cap W a Tc =
      if d0 ≠ 0 ∧ ∃ σ : ℝ≥0, σ ≤ cap ∧ f σ = 0 ∧ ((T + σ : ℝ≥0) : ℝ≥0∞) < Tc then
        ENNReal.ofReal (a (T + sInf Z)) else ⊤ := rfl
  -- the gauge where the launch distance vanishes at the own time of `t`
  refine ⟨?_, ?_, fun t ht hlt => ?_, fun t ht heq => ?_⟩
  · -- the life is positive
    rw [hlife]
    split_ifs with hc
    · obtain ⟨hd, σ₀, hσ₀, hf₀, hT₀⟩ := hc
      have hmem : sInf Z ∈ Z := hZc.csInf_mem ⟨σ₀, hσ₀, hf₀⟩ (OrderBot.bddBelow Z)
      have hle : sInf Z ≤ σ₀ := csInf_le (OrderBot.bddBelow Z) ⟨hσ₀, hf₀⟩
      have hTc : ((T + sInf Z : ℝ≥0) : ℝ≥0∞) < Tc :=
        (ENNReal.coe_le_coe.2 (add_le_add_right hle T)).trans_lt hT₀
      have hpos : 0 < T + sInf Z := by
        refine lt_of_le_of_ne zero_le fun h0 => ?_
        have hz : sInf Z = 0 := le_zero_iff.1 (le_of_le_of_eq le_add_self h0.symm)
        have := hmem.2
        rw [hz, hf0] at this
        exact hd this
      have h0Tc : ((0 : ℝ≥0) : ℝ≥0∞) < Tc := (ENNReal.coe_le_coe.2 zero_le).trans_lt hTc
      have := ham h0Tc hTc hpos
      rw [ha0] at this
      exact ENNReal.ofReal_pos.2 this
    · exact ENNReal.zero_lt_top
  · -- continuity
    have hψc := continuousOn_invClock ham haL hψ
    have hg : Continuous g := by
      by_cases hd : d0 = 0
      · simp only [hgdef, hd, ↓reduceIte]
        exact continuous_const
      · simp only [hgdef, hd, ↓reduceIte]
        exact continuous_const.min (hfc.div_const d0)
    have hσc : ContinuousOn (fun t => min cap (ψ t - T)) {t | (t : ℝ≥0∞) < L} :=
      (continuous_const.min (continuous_id.sub continuous_const)).comp_continuousOn hψc
    exact (hg.comp_continuousOn hσc).congr fun t ht => hrep t ht
  · -- positivity before the life
    rw [hrep t ht]
    by_cases hd : d0 = 0
    · simp only [hgdef, hd, ↓reduceIte, zero_lt_one]
    have hd0 : 0 < d0 := lt_of_le_of_ne (launchStart_nonneg W) (Ne.symm hd)
    simp only [hgdef, hd, ↓reduceIte]
    refine lt_min one_pos (div_pos (lt_of_le_of_ne (hfnn _) fun hf => ?_) hd0)
    set σt := min cap (ψ t - T) with hσt
    by_cases hT : T ≤ ψ t
    · have hσle : T + σt ≤ ψ t := by
        calc T + σt ≤ T + (ψ t - T) := add_le_add_right (min_le_right _ _) T
          _ = ψ t := add_tsub_cancel_of_le hT
      have hTc : ((T + σt : ℝ≥0) : ℝ≥0∞) < Tc := (ENNReal.coe_le_coe.2 hσle).trans_lt (hψ t ht).1
      have hc : d0 ≠ 0 ∧ ∃ σ : ℝ≥0, σ ≤ cap ∧ f σ = 0 ∧ ((T + σ : ℝ≥0) : ℝ≥0∞) < Tc :=
        ⟨hd, σt, min_le_left _ _, hf.symm, hTc⟩
      rw [hlife, ite_eq_left_of_eq_true _ _ (eq_true hc)] at hlt
      have hle : sInf Z ≤ σt := csInf_le (OrderBot.bddBelow Z) ⟨min_le_left _ _, hf.symm⟩
      have hT1 : T + sInf Z ≤ ψ t := (add_le_add_right hle T).trans hσle
      have h1 : a (T + sInf Z) ≤ a (ψ t) :=
        ham.monotoneOn ((ENNReal.coe_le_coe.2 hT1).trans_lt (hψ t ht).1) (hψ t ht).1 hT1
      rw [(hψ t ht).2] at h1
      have h2 : ENNReal.ofReal (a (T + sInf Z)) ≤ (t : ℝ≥0∞) := by
        rw [← ENNReal.ofReal_coe_nnreal]
        exact ENNReal.ofReal_le_ofReal h1
      exact absurd hlt (not_lt.2 h2)
    · have h0 : σt = 0 := by
        rw [hσt, tsub_eq_zero_of_le (le_of_lt (not_le.1 hT)), min_eq_right (zero_le (a := cap))]
      rw [h0, hf0] at hf
      exact hd hf.symm
  · -- zero at the life
    have hne : launchLife κ θ B T cap W a Tc ≠ ⊤ := heq ▸ ENNReal.coe_ne_top
    have hc : d0 ≠ 0 ∧ ∃ σ : ℝ≥0, σ ≤ cap ∧ f σ = 0 ∧ ((T + σ : ℝ≥0) : ℝ≥0∞) < Tc := by
      by_contra hc
      rw [hlife, ite_eq_right_of_eq_false _ _ (eq_false hc)] at hne
      exact hne rfl
    rw [hlife, ite_eq_left_of_eq_true _ _ (eq_true hc)] at heq
    obtain ⟨hd, σ₀, hσ₀, hf₀, hT₀⟩ := hc
    set τ := sInf Z with hτ
    have hmem : τ ∈ Z := hZc.csInf_mem ⟨σ₀, hσ₀, hf₀⟩ (OrderBot.bddBelow Z)
    have hle : τ ≤ σ₀ := csInf_le (OrderBot.bddBelow Z) ⟨hσ₀, hf₀⟩
    have hTc : ((T + τ : ℝ≥0) : ℝ≥0∞) < Tc := (ENNReal.coe_le_coe.2 (add_le_add_right hle T)).trans_lt hT₀
    have hat : a (T + τ) = t := by
      have h0 := (haL _ hTc).1
      have h1 : ENNReal.ofReal (a (T + τ)) = ENNReal.ofReal (t : ℝ) := by
        rw [ENNReal.ofReal_coe_nnreal]; exact heq.symm
      exact (ENNReal.ofReal_eq_ofReal_iff h0 t.coe_nonneg).1 h1
    have hψt : ψ t = T + τ := by
      refine ham.injOn (hψ t ht).1 hTc ?_
      rw [(hψ t ht).2, hat]
    rw [hrep t ht, hψt, add_tsub_cancel_left, min_eq_right hmem.1]
    simp only [hgdef, hd, ↓reduceIte, hmem.2, zero_div, min_eq_right zero_le_one]

end Sample

/-! ### Along every relative coordinate process -/

section Coord

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κc θc : ℝ} {bc : ℝ → ℝ} {Jc : Finset ℝ} {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {W Wα D : ℝ≥0 → Ω → ℝ}
  {ζα L : Ω → ℝ≥0∞} {γ α : Ω → ℝ≥0 → ℂ}

/-- **The launch gauge along every relative coordinate process**: almost surely on the record event it is continuous
before the coordinates' life, positive before `launchLife` and zero at it, and `0 < launchLife`. These are the
cap-gauge hypotheses of RELDET's capped version families. -/
theorem ae_launchGauge_coord (hF : IsFlowLineDriver κc bc Jc θc P h Wα ζα)
    (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (Wα · ω) (ζα ω) (α ω))
    (hNR : ∀ᵐ ω ∂P, ∀ α' : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) α' →
      ∀ v : ℝ≥0, 0 < v → (v : ℝ≥0∞) < ζα ω → α' v ≠ 0)
    (hW : ∀ᵐ ω ∂P, Continuous (W · ω) ∧ W 0 ω = 0 ∧ IsGeneratingTrace (W · ω) ⊤ (γ ω))
    (s : ℝ≥0) (hs0 : 0 < s) (hC : SourceC.RelativeDriverCoordinates s P W Wα ζα γ α D L)
    (hBc : ∀ w w' : ℝ≥0 → ℝ, (∀ u ≤ T, w u = w' u) → B w = B w') :
    ∀ᵐ ω ∂P, gb6Rec s Wα ζα ω ∈ gb6TS s →
      0 < launchLife κ θ B T cap (W · ω) (gb6Clock s W Wα ω) (gb6Tc s γ α ω) ∧
      ContinuousOn (fun t => launchGauge κ θ B T cap s t (gb6Rec s Wα ζα ω, fun u => D u ω))
        {t | (t : ℝ≥0∞) < L ω} ∧
      (∀ t : ℝ≥0, (t : ℝ≥0∞) < L ω →
        (t : ℝ≥0∞) < launchLife κ θ B T cap (W · ω) (gb6Clock s W Wα ω) (gb6Tc s γ α ω) →
        0 < launchGauge κ θ B T cap s t (gb6Rec s Wα ζα ω, fun u => D u ω)) ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < L ω →
        (t : ℝ≥0∞) = launchLife κ θ B T cap (W · ω) (gb6Clock s W Wα ω) (gb6Tc s γ α ω) →
        launchGauge κ θ B T cap s t (gb6Rec s Wα ζα ω, fun u => D u ω) = 0 := by
  filter_upwards [ae_physicalReadback_nr hF hα hNR hW s hs0 hC, ae_separationRead_regular_nr hF hα hNR hW s hs0 hC,
    GW2Bh.ae_timeCapRule_coord hF hα hW hC, GW2Bh.ae_min_timeCapRule_coord hF hα hW hC, ae_gb6RecGood hF hα s,
    hC.relative, hW] with ω hread hreg hcapR hminR hgood hrel hWω hrec
  obtain ⟨hs, hsH⟩ := (mem_gb6TS_iff hgood).2 hrec
  obtain ⟨ha0, ham, -, hat, hcapacity⟩ := hread hs hsH
  have hXc := (hreg hrec).2.2.2.2
  obtain ⟨-, hhull⟩ := hrel hs hsH
  have hruleL : ∀ Δ : ℝ≥0, ¬ (Δ : ℝ≥0∞) < gb6Tc s γ α ω →
      L ω ≤ timeCapRule s Δ (gb6Rec s Wα ζα ω, fun u => D u ω) := by
    intro Δ hΔ
    have hm := hminR hrec Δ
    simp only [capClock, hΔ, ↓reduceIte, min_top_right] at hm
    exact min_eq_left_iff.1 hm
  exact launchGauge_sample (fun w hw => hBc w _ hw) hWω.2.2 hWω.1 hWω.2.1 ha0 ham
    (fun t ht => ⟨(hhull t ht).1, (hhull t ht).2.1⟩)
    (fun u hu => by obtain ⟨t, ht, hclk, -⟩ := hcapacity u hu; exact ⟨t, ht, hclk⟩)
    hat hXc (fun Δ hΔ => hcapR hrec Δ hΔ) hruleL

end Coord

end InteractingSLE.Theorem14.GW2Rd
