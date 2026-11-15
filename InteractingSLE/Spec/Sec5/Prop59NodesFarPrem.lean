/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop59NodesFar

/-!
# The killed comparison premises of Proposition 5.9's experiment

Packet PROVE-PROP59-NODES. The two estimates of PROVE-PROP59T2's experiment, for evolutions killed at their first far
contact (`CompPremiseFar`, `Prop59NodesFar`):

* **`compPremiseFar_crossL`**, **`compPremiseFar_crossR`**: every integrated evolution of a stage word from an
  admissible start crosses `∓(2 + 1/8)` strictly before its first far contact almost surely (p. 144). The crossing of
  PROVE-PROP59T's `ae_stage_cross_left` happens before the first contact with the far mark of the heading side, and the
  far mark of the other side is never met before the lifetime (Astra's follow-up 5 §2.4: far total `κ/2 − 2`), so the
  crossing time is before the killed lifetime (`lt_farLife_of`);
* **`exists_compPremiseFar_unit`**: Lemma 5.10's unit estimate (PROVE-PROP59T2's `exists_compPremise_unit`) for the
  killed evolutions: the unit event only constrains the samples before the lifetime, so killing enlarges it.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Prop59Nodes

open Prop59Stage Supp8.GB8 Prop59Tips

variable {κ : ℝ} {nL nR : ℕ}

theorem continuousOn_lt_mono {f : ℝ≥0 → ℝ} {ζ ζ' : ℝ≥0∞} (hf : ContinuousOn f {s | (s : ℝ≥0∞) < ζ})
    (h : ζ' ≤ ζ) : ContinuousOn f {s | (s : ℝ≥0∞) < ζ'} :=
  hf.mono fun _ hs => lt_of_lt_of_le hs h

/-- **The killed leftward crossing premise**: every integrated evolution of a stage word from an admissible start
(`startsL`), with an almost surely existing trace, killed at its first far contact, crosses the absolute level
`−(2 + 1/8)` almost surely. -/
theorem compPremiseFar_crossL (hκ : 0 < κ) (hκ4 : κ < 4) (hnL : 0 < nL) (hnR : 0 < nR) {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} (hw : IsStageWordN κ ρL ρR) :
    CompPremiseFar κ ρL ρR (farL hnL) (farR hnR) (startsL hnL hnR) (crossL (-(2 + 1 / 8)) (farL hnL)) 1 := by
  intro y₀ hy Ω' mΩ' P' _ 𝓕' W' VL' VR' B' ζ' hE htr
  obtain ⟨m, hm, hw'⟩ := hw
  subst hm
  have hw'' : IsStageWord κ ρL ρR := by
    have e : (fun i : Fin (m + 1) => ρL (Fin.cast rfl i)) = ρL := funext fun i => rfl
    rw [e] at hw'; exact hw'
  obtain ⟨hF, hxL, hxR, hfar, hxm, hxp⟩ := hy
  have hlast : farL hnL = Fin.last m := last_eq_mk m hnL
  rw [hlast] at hfar hxm
  have h8 := ae_stage_cross_left hκ hκ4 hnR hE hF hxL hxR hxm hxp hw'' htr
  refine one_le_measure_of_ae ?_
  filter_upwards [h8, hE.2.2.2.2] with ω hω hp
  obtain ⟨⟨τ, hτ, -⟩, hright, -⟩ := hω
  have hfp := hp.isForcePath
  obtain ⟨t, htζ, hwt, hgap⟩ := exists_crossing_of_contact_level (ℓ := -(2 + 1 / 8) - y₀.1)
    hfp.continuousOn_w (fun s t hst ht => hfp.vL_le_of_le hst ht (Fin.last m)) (hfp.vL_zero (Fin.last m))
    (by linarith) hτ
  show (y₀, samp (W' · ω) (fun i t => VL' i t ω) (fun k t => VR' k t ω)
    (farLife (farL hnL) (farR hnR) (W' · ω) (fun i t => VL' i t ω) (fun k t => VR' k t ω) (ζ' ω))) ∈ _
  rw [hlast]
  have hlt := lt_farLife_of (iL := Fin.last m) (iR := farR hnR) (w := fun t => W' t ω)
    (vL := fun i t => VL' i t ω) (vR := fun k t => VR' k t ω) hfp.continuousOn_w (hfp.continuousOn_vL _)
    (hfp.continuousOn_vR _) htζ fun u hu => ⟨hgap u hu,
      (hright u (lt_of_le_of_lt (by exact_mod_cast hu) htζ) : W' u ω < VR' (farR hnR) u ω)⟩
  exact crossL_of_path (x := y₀.2) (continuousOn_lt_mono hfp.continuousOn_w farLife_le)
    (continuousOn_lt_mono (hfp.continuousOn_vL (Fin.last m)) farLife_le) hlt (by linarith) hgap

/-- **The killed rightward crossing premise** (by reflection). -/
theorem compPremiseFar_crossR (hκ : 0 < κ) (hκ4 : κ < 4) (hnL : 0 < nL) (hnR : 0 < nR) {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} (hw : IsStageWordN κ ρR ρL) :
    CompPremiseFar κ ρL ρR (farL hnL) (farR hnR) (startsR hnL hnR) (crossR (2 + 1 / 8) (farR hnR)) 1 := by
  intro y₀ hy Ω' mΩ' P' _ 𝓕' W' VL' VR' B' ζ' hE htr
  obtain ⟨m, hm, hw'⟩ := hw
  subst hm
  have hw'' : IsStageWord κ ρR ρL := by
    have e : (fun i : Fin (m + 1) => ρR (Fin.cast rfl i)) = ρR := funext fun i => rfl
    rw [e] at hw'; exact hw'
  obtain ⟨hF, hxL, hxR, hfar, hxm, hxp⟩ := hy
  have hlast : farR hnR = Fin.last m := last_eq_mk m hnR
  rw [hlast] at hfar hxp
  have hEr := IsIntegratedSLEEvolution.reflect hE
  have htr' : ∀ᵐ ω ∂P', ∃ γ : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => (-W') t ω) (ζ' ω) γ := by
    filter_upwards [htr] with ω ⟨γ, hγ⟩
    exact ⟨fun t => LP.reflectC (γ t), LP.isGeneratingTrace_reflect hγ⟩
  have hxm' : (-y₀.2.2) (Fin.last m) < 0 := by simp only [Pi.neg_apply]; linarith
  have hxp' : 0 < (-y₀.2.1) (farL hnL) := by simp only [Pi.neg_apply]; linarith
  have h8 := ae_stage_cross_left hκ hκ4 hnL hEr (Theorem14.CS3Cross.isOrderedForceWord_reflect hF)
    (fun a b hab => neg_lt_neg (hxR hab)) (fun a b hab => neg_lt_neg (hxL hab)) hxm' hxp' hw'' htr'
  refine one_le_measure_of_ae ?_
  filter_upwards [h8, hEr.2.2.2.2, hE.2.2.2.2] with ω hω hpr hp
  obtain ⟨⟨τ, hτ, -⟩, hleft, -⟩ := hω
  have hfr := hpr.isForcePath
  obtain ⟨t, htζ, hwt, hgap⟩ := exists_crossing_of_contact_level (ℓ := y₀.1 - (2 + 1 / 8))
    hfr.continuousOn_w (fun s t hst ht => hfr.vL_le_of_le hst ht (Fin.last m)) (hfr.vL_zero (Fin.last m))
    (by simp only [Pi.neg_apply]; linarith) hτ
  have hfp := hp.isForcePath
  show (y₀, samp (W' · ω) (fun i t => VL' i t ω) (fun k t => VR' k t ω)
    (farLife (farL hnL) (farR hnR) (W' · ω) (fun i t => VL' i t ω) (fun k t => VR' k t ω) (ζ' ω))) ∈ _
  rw [hlast]
  have hgap' : ∀ u ≤ t, W' u ω < VR' (Fin.last m) u ω := fun u hu => by
    have := hgap u hu; simp only [Pi.neg_apply] at this; linarith
  have hlt := lt_farLife_of (iL := farL hnL) (iR := Fin.last m) (w := fun t => W' t ω)
    (vL := fun i t => VL' i t ω) (vR := fun k t => VR' k t ω) hfp.continuousOn_w (hfp.continuousOn_vL _)
    (hfp.continuousOn_vR _) htζ fun u hu => ⟨by
      have h := hleft u (lt_of_le_of_lt (by exact_mod_cast hu) htζ)
      have h' : -W' u ω < -VL' (farL hnL) u ω := h
      linarith, hgap' u hu⟩
  refine crossR_of_path (x := y₀.2) (continuousOn_lt_mono hfp.continuousOn_w farLife_le)
    (continuousOn_lt_mono (hfp.continuousOn_vR (Fin.last m)) farLife_le) hlt ?_ hgap'
  simp only [Pi.neg_apply] at hwt; linarith

/-- **The killed unit premise** (Lemma 5.10 at the first passage through `0`, for evolutions killed at their first
far contact): PROVE-PROP59T2's `p₀` works for every pair of far marks. -/
theorem exists_compPremiseFar_unit {nL₀ nR₀ : ℕ} (hκ : 0 < κ) (hκ4 : κ < 4) (ρL₀ : Fin nL₀ → ℝ)
    (ρR₀ : Fin nR₀ → ℝ) :
    ∃ p₀ : ℝ≥0∞, 0 < p₀ ∧ p₀ ≤ 1 ∧ ∀ (j : ℕ) (iL : Fin (nL₀ + (j + 1))) (iR : Fin (nR₀ + (j + 1))),
      CompPremiseFar κ (stageρL κ ρL₀ (j + 1)) (stageρR κ ρR₀ (j + 1)) iL iR startsU unitSet p₀ := by
  obtain ⟨p₀, hp₀, hp₀1, hprem⟩ := exists_compPremise_unit hκ hκ4 ρL₀ ρR₀
  refine ⟨p₀, hp₀, hp₀1, fun j iL iR y₀ hy Ω' mΩ' P' _ 𝓕' W' VL' VR' B' ζ' hE htr => ?_⟩
  refine (hprem j y₀ hy Ω' mΩ' P' 𝓕' W' VL' VR' B' ζ' hE htr).trans (measure_mono fun ω hω => ?_)
  intro q hq1 hqζ
  have hqζ' : ((q : ℝ≥0) : ℝ≥0∞) < ζ' ω := lt_of_lt_of_le hqζ farLife_le
  have h := hω q hq1 hqζ'
  change y₀.1 + ((samp (W' · ω) (fun i t => VL' i t ω) (fun k t => VR' k t ω) (ζ' ω)).2 q).1 < 7 / 4 at h
  change y₀.1 + ((samp (W' · ω) (fun i t => VL' i t ω) (fun k t => VR' k t ω)
    (farLife iL iR (W' · ω) (fun i t => VL' i t ω) (fun k t => VR' k t ω) (ζ' ω))).2 q).1 < 7 / 4
  rw [samp_snd_of_lt_farLife hqζ]
  exact h

end InteractingSLE.Sec5.Prop59Nodes
