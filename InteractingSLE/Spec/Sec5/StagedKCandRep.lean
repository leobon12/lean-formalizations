/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.StoppedCont
import InteractingSLE.Spec.Sec5.CrossCondStagedKillLaw
import InteractingSLE.Spec.Sec7.ContinuityProb2Restart

/-!
# Prop 5.9's killed law: a stopped evolution represents its killed law (the continuation step)

Packet PROVE-STAGEDK-CAND (ruling R78). PROVE-STAGED8's §5.2 asks, for the per-candidate law `IsStageLawFarK`, for a
representation `HasKilledRep false` of the conditional law of a piece: an integrated evolution whose samples killed at
its first far contact have that law and which is traced up to that contact. This file proves that every **local
evolution stopped at its first far contact** gives one:

* `IsKilledAtFar`: a path killed at its first far contact, continuously (continuous through a finite kill time, no far
  contact before it, a far contact at it);
* `farLife_eq_of_agree`: an integrated path that agrees with such a path before its kill time and lives at least as
  long has that kill time as its killed lifetime `farLife`;
* `samp_congr`: the killed samples only see the path before the lifetime;
* **`hasKilledRep_of_isSLEEvolutionUpTo`**: a local integrated evolution (`Sec2.IsSLEEvolutionUpTo`) before its kill
  time, killed at its first far contact and traced up to it, represents the law of its killed samples — through the
  landed continuation (CONT) `Restart.StoppedCont.stoppedContinuationStatement` (every `κ > 0`).

No finiteness of the kill time is needed: on `{τ = ∞}` the continuation is the local evolution itself.

Conditional helpers with distinct names; they replace no source theorem. R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`; the continuation uses only Theorem 2.2's existence
(`exists_isIntegratedSLEEvolution_assembled`, inside (CONT)).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CrossCond.StagedKCand

open Prop59Stage Prop59Nodes StagedKill

/-! ### Paths killed at their first far contact -/

section Path

variable {nL nR : ℕ} {iL : Fin nL} {iR : Fin nR}

/-- **A path killed at its first far contact, continuously**: continuous on `[0, τ]` when `τ` is finite, no contact of
the driver with the far marks `iL`, `iR` before `τ`, and a far contact at a finite `τ`. -/
structure IsKilledAtFar (iL : Fin nL) (iR : Fin nR) (w : ℝ≥0 → ℝ) (vL : Fin nL → ℝ≥0 → ℝ)
    (vR : Fin nR → ℝ≥0 → ℝ) (τ : ℝ≥0∞) : Prop where
  cont : ∀ T : ℝ≥0, (T : ℝ≥0∞) = τ → ContinuousOn (fun t => (w t, fun i => vL i t, fun j => vR j t)) (Iic T)
  noContact : ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ → w t ≠ vL iL t ∧ w t ≠ vR iR t
  contact : ∀ T : ℝ≥0, (T : ℝ≥0∞) = τ → w T = vL iL T ∨ w T = vR iR T

/-- Two paths agreeing before `τ`. -/
def AgreeBefore (w w' : ℝ≥0 → ℝ) (vL vL' : Fin nL → ℝ≥0 → ℝ) (vR vR' : Fin nR → ℝ≥0 → ℝ) (τ : ℝ≥0∞) : Prop :=
  ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ → w' t = w t ∧ (∀ i, vL' i t = vL i t) ∧ ∀ j, vR' j t = vR j t

/-- **The killed samples only see the path before the lifetime.** -/
theorem samp_congr {w w' : ℝ≥0 → ℝ} {vL vL' : Fin nL → ℝ≥0 → ℝ} {vR vR' : Fin nR → ℝ≥0 → ℝ} {τ : ℝ≥0∞}
    (hag : AgreeBefore w w' vL vL' vR vR' τ) : samp w' vL' vR' τ = samp w vL vR τ := by
  unfold samp
  refine Prod.ext rfl (funext fun q => ?_)
  by_cases hq : ((q : ℝ≥0) : ℝ≥0∞) < τ
  · obtain ⟨e1, e2, e3⟩ := hag q hq
    simp only [hq, ↓reduceIte, e1, e2, e3]
  · simp only [hq, ↓reduceIte]

/-- **The killed lifetime of a continuation.** A path `(w', v')` living until `ζ' ≥ τ`, continuous before `ζ'`, that
agrees before `τ` with a path killed at its first far contact `τ` (and at time `0`), has killed lifetime
`farLife = τ`. -/
theorem farLife_eq_of_agree {w w' : ℝ≥0 → ℝ} {vL vL' : Fin nL → ℝ≥0 → ℝ} {vR vR' : Fin nR → ℝ≥0 → ℝ}
    {τ ζ' : ℝ≥0∞} (hτζ : τ ≤ ζ') (hag : AgreeBefore w w' vL vL' vR vR' τ)
    (hc' : ContinuousOn (fun t => (w' t, fun i => vL' i t, fun j => vR' j t)) {t | (t : ℝ≥0∞) < ζ'})
    (hK : IsKilledAtFar iL iR w vL vR τ)
    (h0 : w' 0 = w 0 ∧ (∀ i, vL' i 0 = vL i 0) ∧ ∀ j, vR' j 0 = vR j 0) :
    farLife iL iR w' vL' vR' ζ' = τ := by
  have hge : τ ≤ farHit iL iR w' vL' vR' := by
    refine le_farHit fun t ht => ?_
    by_contra hlt
    push Not at hlt
    obtain ⟨e1, e2, e3⟩ := hag t hlt
    rcases ht with h | h
    · exact (hK.noContact t hlt).1 (by rw [← e1, ← e2 iL]; exact h)
    · exact (hK.noContact t hlt).2 (by rw [← e1, ← e3 iR]; exact h)
  induction τ using ENNReal.recTopCoe with
  | top =>
    exact le_antisymm le_top (le_min hτζ hge)
  | coe T =>
    by_cases hTζ : (T : ℝ≥0∞) = ζ'
    · rw [farLife, ← hTζ]
      exact min_eq_left hge
    have hlt : (T : ℝ≥0∞) < ζ' := lt_of_le_of_ne hτζ hTζ
    -- the continuation meets a far mark at `T`
    have hval : w' T = w T ∧ vL' iL T = vL iL T ∧ vR' iR T = vR iR T := by
      rcases eq_or_ne T 0 with rfl | hT0
      · exact ⟨h0.1, h0.2.1 iL, h0.2.2 iR⟩
      have hT0' : 0 < T := pos_iff_ne_zero.2 hT0
      have hsub : Iic T ⊆ {t : ℝ≥0 | (t : ℝ≥0∞) < ζ'} := fun t ht =>
        lt_of_le_of_lt (by exact_mod_cast ht) hlt
      have heq : EqOn (fun t => (w' t, fun i => vL' i t, fun j => vR' j t))
          (fun t => (w t, fun i => vL i t, fun j => vR j t)) (Iio T) := by
        intro t ht
        obtain ⟨e1, e2, e3⟩ := hag t (by exact_mod_cast ht)
        simp only [e1, e2, e3]
      have hcl : Iic T ⊆ closure (Iio T) := by
        rw [closure_Iio' (a := T) ⟨0, hT0'⟩]
      have h := heq.of_subset_closure (hc'.mono hsub) (hK.cont T rfl) Iio_subset_Iic_self hcl
        (Set.mem_Iic.2 le_rfl)
      simp only [Prod.mk.injEq] at h
      exact ⟨h.1, congrFun h.2.1 iL, congrFun h.2.2 iR⟩
    have hle : farHit iL iR w' vL' vR' ≤ T := by
      refine iInf₂_le T ?_
      rcases hK.contact T rfl with h | h
      · exact Or.inl (by rw [hval.1, hval.2.1]; exact h)
      · exact Or.inr (by rw [hval.1, hval.2.2]; exact h)
    rw [farLife, le_antisymm hle hge]
    exact min_eq_right hτζ

end Path

/-! ### The representation through the continuation -/

section Rep

variable {nL nR : ℕ} {iL : Fin nL} {iR : Fin nR}

/-- **A stopped evolution represents its killed law** (PROVE-STAGED8 §5.2, the continuation step). Let
`(W, V_L, V_R, B)` be a local integrated `SLE_κ(ρ)` evolution from the start `y₀` before the random time `ζ`, almost
surely killed at its first far contact `ζ` (`IsKilledAtFar`) and traced up to it. Then the law of its killed samples is
represented by an integrated evolution traced up to its killed lifetime: `HasKilledRep κ false`. The evolution is the
continuation (CONT) of the local one (`stoppedContinuationStatement`); its killed lifetime is `ζ`
(`farLife_eq_of_agree`), so its killed samples are the local ones (`samp_congr`). -/
theorem hasKilledRep_of_isSLEEvolutionUpTo {κ : ℝ} (hκ : 0 < κ) {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {y₀ : Start nL nR} (hF : IsOrderedForceWord y₀.2.1 y₀.2.2)
    {Ω : Type} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ] {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} (hE : Sec2.IsSLEEvolutionUpTo κ y₀.2.1 y₀.2.2 ρL ρR μ 𝓕 W VL VR B ζ)
    (hK : ∀ᵐ ω ∂μ, IsKilledAtFar iL iR (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) (ζ ω))
    (htr : ∀ᵐ ω ∂μ, ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (W · ω) (ζ ω) η) :
    HasKilledRep κ false ρL ρR iL iR y₀ (μ.map (pieceSamp W VL VR ζ)) := by
  have hc : ∀ᵐ ω ∂μ, ∀ T : ℝ≥0, (T : ℝ≥0∞) = ζ ω →
      ContinuousOn (fun t => (W t ω, fun i => VL i t ω, fun j => VR j t ω)) (Iic T) := by
    filter_upwards [hK] with ω hω using hω.cont
  obtain ⟨Ω', mΩ', P', hP', π, hπ, 𝓕', W', VL', VR', B', ζ', hmap, hE', hag⟩ :=
    Restart.StoppedCont.stoppedContinuationStatement hκ y₀.2.1 y₀.2.2 ρL ρR hF μ 𝓕 W VL VR B ζ hE hc
  have hobs : Measurable (pieceSamp W VL VR ζ) :=
    measurable_samp_of_adaptedBefore hE.adapted_W hE.adapted_VL hE.adapted_VR
  have hpull : ∀ {p : Ω → Prop}, (∀ᵐ ω ∂μ, p ω) → ∀ᵐ ω' ∂P', p (π ω') := fun h =>
    ae_of_ae_map hπ.aemeasurable (by rw [hmap]; exact h)
  have hkey : ∀ᵐ ω' ∂P',
      farLife iL iR (W' · ω') (fun i t => VL' i t ω') (fun j t => VR' j t ω') (ζ' ω') = ζ (π ω') ∧
      AgreeBefore (W · (π ω')) (W' · ω') (fun i t => VL i t (π ω')) (fun i t => VL' i t ω')
        (fun j t => VR j t (π ω')) (fun j t => VR' j t ω') (ζ (π ω')) := by
    filter_upwards [hag, hpull hK, hpull hE.ae_path, hE'.2.2.2.2] with ω' hag' hK' hp hp'
    have hagb : AgreeBefore (W · (π ω')) (W' · ω') (fun i t => VL i t (π ω')) (fun i t => VL' i t ω')
        (fun j t => VR j t (π ω')) (fun j t => VR' j t ω') (ζ (π ω')) := fun t ht => hag'.2 t ht
    refine ⟨farLife_eq_of_agree hag'.1 hagb ?_ hK' ?_, hagb⟩
    · exact hp'.2.2.2.1.prodMk ((continuousOn_pi.2 hp'.2.2.2.2.1).prodMk (continuousOn_pi.2 hp'.2.2.2.2.2.1))
    · exact ⟨hp'.1.trans hp.w_zero.symm, fun i => (hp'.2.1 i).trans (hp.vL_zero i).symm,
        fun j => (hp'.2.2.1 j).trans (hp.vR_zero j).symm⟩
  have hsamp : farSamp iL iR W' VL' VR' ζ' =ᵐ[P'] (pieceSamp W VL VR ζ) ∘ π := by
    filter_upwards [hkey] with ω' h
    change samp _ _ _ (farLife iL iR (W' · ω') (fun i t => VL' i t ω') (fun j t => VR' j t ω') (ζ' ω')) =
      samp (W · (π ω')) (fun i t => VL i t (π ω')) (fun j t => VR j t (π ω')) (ζ (π ω'))
    rw [h.1]
    exact samp_congr h.2
  refine ⟨Ω', mΩ', P', hP', 𝓕', W', VL', VR', B', ζ', hE', ?_, (hobs.comp hπ).aemeasurable.congr hsamp.symm, ?_⟩
  · filter_upwards [hkey, hpull htr] with ω' h hη
    obtain ⟨η, hη⟩ := hη
    refine ⟨η, ?_⟩
    change IsGeneratingTrace (W' · ω')
      (farLife iL iR (W' · ω') (fun i t => VL' i t ω') (fun j t => VR' j t ω') (ζ' ω')) η
    rw [h.1]
    exact Sec7.IsGeneratingTrace.congr_lt hη fun t ht => (h.2 t ht).1
  · rw [Measure.map_congr hsamp, ← Measure.map_map hobs hπ, hmap]

end Rep

end InteractingSLE.Sec5.CrossCond.StagedKCand
