/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WholeFieldStoppedRef
import InteractingSLE.Spec.Restart.StoppedExtendProofDet

/-!
# Aux. lemma 54 for general words from the joint law of the field and the stopped history

Packet PROVE-DOMAINMARKOV10. Specification Aux. lemma 54 (p. 246: "Then the stopped coupling extends to a full coupling
with the original optional hull specification. The extension preserves the whole initial field and uses only the
stopped history and its active field when sampling the future"), by the whole-field route of ruling R38, Part C:
(WF2) at every own-filtration stop makes the joint law of the field and the stopped driving history the same in every
coupling, and then the future is sampled from a full reference **given the whole field and the stopped history**, so
the extension's field is the given field and the clauses of the frozen optional hull specification are inherited from
the reference (no locality analysis on the extension).

The stop is a **Galmarino path functional** (PROVE-DOMAINMARKOV9 §4.2, ruling R37): `V = R(history killed at V)` for
a measurable rule `R` on `LawUnique.HistorySpace` that only reads the samples before its value (`IsHistGalmarino`).

* `IsHistGalmarino R`: two histories whose lifetimes are both `≥ R γ` and whose samples agree at the dyadic times
  `< R γ` have the same value of `R`;
* `StoppedJointLawStatement κ` (**named input**: the stopped whole-field identification, R38 Part C at the stop): for
  every coupling through a Galmarino stop `V = R(…)` and every full coupling of the word, the joint law of the field and
  the history killed at `V` equals that of the full coupling's field and its history killed at `R(its history) ∧ ζ`;
* `StoppedHullExtendGKStatement κ`: Aux. lemma 54 in kernel form (PROVE-DOMAINMARKOV9's `StoppedHullExtendKStatement`)
  for Galmarino stops; `StoppedHullExtendGStatement κ`: the same with an enlargement measure (PROVE-DOMAINMARKOV7's
  form) for Galmarino stops;
* **`exists_extension_of_jointLaw`** (proved): given a coupling through `V`, a family reference on a standard Borel
  space (`WholeFieldStopped.IsFamilyRef`), a measurable stop `V₀ ≤ ζ₀` of the reference and equal joint laws of
  (history killed at the stop, field), the kernel `K = κ₀(history, field)` (`Sec7.aux54_exists_extension`) gives on
  `Ω × Ω₀` an optional hull coupling with the field `h ∘ fst` whose coordinates agree with the stopped ones through `V`;
* **`stoppedHullExtendGKStatement_of_jointLaw`**, `stoppedHullExtendGStatement_of_jointLaw`: Aux. lemma 54 (both forms,
  Galmarino stops) from `StoppedJointLawStatement κ`, every `κ > 0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open LQGMetric (DistOn)
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Restart

namespace StoppedExtendWF

open LawUnique WholeFieldStopped Coupling StoppedExtend

variable {nL nR : ℕ}

/-! ### Galmarino rules and the statements -/

/-- **A history recorded from a state that is continuous before its lifetime**: the samples at the dyadic times before
the lifetime are those of a path continuous on `{t < γ.1}`. -/
def IsKilledContHist (γ : HistorySpace nL nR) : Prop :=
  ∃ f : ℝ≥0 → DrivingValue nL nR, ContinuousOn f {t | (t : ℝ≥0∞) < γ.1} ∧
    ∀ p : ℕ × ℕ, (dyadicTime p : ℝ≥0∞) < γ.1 → γ.2 p = f (dyadicTime p)

/-- **A Galmarino rule on killed histories**: if two histories recorded from states continuous before their lifetimes
both live at least until `R γ` and their samples agree at every dyadic time before `R γ`, then `R` takes the same value
on them. (For a continuous path, the first exit time of an open set capped at the lifetime, or a first contact time,
read from the samples before it, is such a rule.) -/
def IsHistGalmarino (R : HistorySpace nL nR → ℝ≥0∞) : Prop :=
  ∀ γ γ' : HistorySpace nL nR, IsKilledContHist γ → IsKilledContHist γ' → R γ ≤ γ.1 → R γ ≤ γ'.1 →
    (∀ p : ℕ × ℕ, (dyadicTime p : ℝ≥0∞) < R γ → γ.2 p = γ'.2 p) → R γ' = R γ

/-- The killed history of a state continuous before the lifetime is recorded from a continuous state. -/
theorem isKilledContHist_killedHistory {Ω : Type*} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {ω : Ω}
    (hc : ContinuousOn (fun t => (W t ω, fun i => VL i t ω, fun j => VR j t ω)) {t | (t : ℝ≥0∞) < ζ ω}) :
    IsKilledContHist (killedHistory W VL VR ζ ω) :=
  ⟨fun t => (W t ω, fun i => VL i t ω, fun j => VR j t ω), hc, fun p hp => by
    have hp' : (dyadicTime p : ℝ≥0∞) < ζ ω := hp
    simp only [killedHistory, hp', ↓reduceIte]⟩

/-- The state of a local path is continuous before its time. -/
theorem continuousOn_state_of_isSLEPathUpTo {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {τ : ℝ≥0∞}
    (hp : Sec2.IsSLEPathUpTo κ xL xR ρL ρR w vL vR b τ) :
    ContinuousOn (fun t => (w t, fun i => vL i t, fun j => vR j t)) {t | (t : ℝ≥0∞) < τ} :=
  hp.continuousOn_w.prodMk ((continuousOn_pi.2 fun i => hp.continuousOn_vL i).prodMk
    (continuousOn_pi.2 fun j => hp.continuousOn_vR j))

/-- **Named input: the stopped whole-field identification** (ruling R38, Part C, (WF2) at an own-filtration stop and
its consequence "any two couplings satisfying the original statement have the same joint law of the field and the
stopped driving history", specialized to a coupling known only through its stop). For an ordered word, a measurable
Galmarino rule `R`, a coupling through `V` with `V = R(history killed at V)` almost surely, and a full optional hull
coupling of the word: the field and the history killed at `V` have the same joint law as the full coupling's field and
its history killed at `R(its killed history) ∧ ζ₀`. -/
def StoppedJointLawStatement (κ : ℝ) : Prop :=
  ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ),
    IsOrderedForceWord xL xR → ∀ R : HistorySpace nL nR → ℝ≥0∞, Measurable R → IsHistGalmarino R →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P] (𝓕 : Filtration ℝ≥0 mΩ)
      (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ)
      (V : Ω → ℝ≥0∞) (h : Ω → DistOn upperHalfPlaneOpens),
      IsStoppedHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B V h →
      (∀ᵐ ω ∂P, V ω = R (killedHistory W VL VR V ω)) →
    ∀ {Ω₀ : Type u} {mΩ₀ : MeasurableSpace Ω₀} (P₀ : Measure Ω₀) [IsProbabilityMeasure P₀]
      (𝓕₀ : Filtration ℝ≥0 mΩ₀) (W₀ : ℝ≥0 → Ω₀ → ℝ) (VL₀ : Fin nL → ℝ≥0 → Ω₀ → ℝ)
      (VR₀ : Fin nR → ℝ≥0 → Ω₀ → ℝ) (B₀ : ℝ≥0 → Ω₀ → ℝ) (ζ₀ : Ω₀ → ℝ≥0∞)
      (h₀ : Ω₀ → DistOn upperHalfPlaneOpens),
      IsOptionalHullCoupling κ xL xR ρL ρR P₀ 𝓕₀ W₀ VL₀ VR₀ B₀ ζ₀ h₀ →
      P.map (fun ω => (killedHistory W VL VR V ω, h ω)) =
        P₀.map (fun ω₀ => (killedHistory W₀ VL₀ VR₀
          (fun ω₀ => min (R (killedHistory W₀ VL₀ VR₀ ζ₀ ω₀)) (ζ₀ ω₀)) ω₀, h₀ ω₀))

/-- **Aux. lemma 54 in kernel form for Galmarino stops** (PROVE-DOMAINMARKOV9's `StoppedHullExtendKStatement` with
the stop a Galmarino functional of the history killed at it): a coupling through `V` extends, on `Ω × C` under
`P ⊗ K`, to a full optional hull coupling of the field read through the first factor, whose coordinates agree with the
stopped ones at every time `t ≤ V` before its lifetime. -/
def StoppedHullExtendGKStatement (κ : ℝ) : Prop :=
  ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ),
    IsOrderedForceWord xL xR → ∀ R : HistorySpace nL nR → ℝ≥0∞, Measurable R → IsHistGalmarino R →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P] (𝓕 : Filtration ℝ≥0 mΩ)
      (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ)
      (V : Ω → ℝ≥0∞) (h : Ω → DistOn upperHalfPlaneOpens),
      IsStoppedHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B V h →
      (∀ᵐ ω ∂P, V ω = R (killedHistory W VL VR V ω)) →
      ∃ (C : Type u) (_ : MeasurableSpace C) (K : Kernel Ω C) (_ : IsMarkovKernel K)
        (𝓕' : Filtration ℝ≥0 (inferInstance : MeasurableSpace (Ω × C))) (W' : ℝ≥0 → Ω × C → ℝ)
        (VL' : Fin nL → ℝ≥0 → Ω × C → ℝ) (VR' : Fin nR → ℝ≥0 → Ω × C → ℝ) (B' : ℝ≥0 → Ω × C → ℝ)
        (ζ' : Ω × C → ℝ≥0∞),
        IsOptionalHullCoupling κ xL xR ρL ρR (P ⊗ₘ K) 𝓕' W' VL' VR' B' ζ' (fun p => h p.1) ∧
        ∀ᵐ p ∂(P ⊗ₘ K), V p.1 ≤ ζ' p ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ V p.1 → (t : ℝ≥0∞) < ζ' p →
          W' t p = W t p.1 ∧ (∀ i, VL' i t p = VL i t p.1) ∧ ∀ j, VR' j t p = VR j t p.1

/-- **Aux. lemma 54 for Galmarino stops, enlargement form** (PROVE-DOMAINMARKOV7's `StoppedHullExtendStatement` with
the stop a Galmarino functional of the history killed at it). -/
def StoppedHullExtendGStatement (κ : ℝ) : Prop :=
  ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ),
    IsOrderedForceWord xL xR → ∀ R : HistorySpace nL nR → ℝ≥0∞, Measurable R → IsHistGalmarino R →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P] (𝓕 : Filtration ℝ≥0 mΩ)
      (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ)
      (V : Ω → ℝ≥0∞) (h : Ω → DistOn upperHalfPlaneOpens),
      IsStoppedHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B V h →
      (∀ᵐ ω ∂P, V ω = R (killedHistory W VL VR V ω)) →
      ∃ (C : Type u) (_ : MeasurableSpace C) (E : Measure (Ω × C)) (_ : IsProbabilityMeasure E)
        (𝓕' : Filtration ℝ≥0 (inferInstance : MeasurableSpace (Ω × C))) (W' : ℝ≥0 → Ω × C → ℝ)
        (VL' : Fin nL → ℝ≥0 → Ω × C → ℝ) (VR' : Fin nR → ℝ≥0 → Ω × C → ℝ) (B' : ℝ≥0 → Ω × C → ℝ)
        (ζ' : Ω × C → ℝ≥0∞),
        E.map Prod.fst = P ∧
        IsOptionalHullCoupling κ xL xR ρL ρR E 𝓕' W' VL' VR' B' ζ' (fun p => h p.1) ∧
        ∀ᵐ p ∂E, V p.1 ≤ ζ' p ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ V p.1 → (t : ℝ≥0∞) < ζ' p →
          W' t p = W t p.1 ∧ (∀ i, VL' i t p = VL i t p.1) ∧ ∀ j, VR' j t p = VR j t p.1

/-- The kernel form gives the enlargement form (`P ⊗ K` has first marginal `P`). -/
theorem stoppedHullExtendGStatement_of_kernel {κ : ℝ} (hK : StoppedHullExtendGKStatement.{u} κ) :
    StoppedHullExtendGStatement.{u} κ := by
  intro nL nR xL xR ρL ρR hF R hRm hRg Ω mΩ P _ 𝓕 W VL VR B V h hSC hV
  obtain ⟨C, mC, K, hKm, 𝓕', W', VL', VR', B', ζ', hC, hag⟩ := hK xL xR ρL ρR hF R hRm hRg P 𝓕 W VL VR B V h hSC hV
  exact ⟨C, mC, P ⊗ₘ K, inferInstance, 𝓕', W', VL', VR', B', ζ', Measure.fst_compProd P K, hC, hag⟩

/-! ### Deterministic agreement from the dyadic samples -/

section Agree

/-- **Two paths agreeing at the dyadic times before `v` agree on `[0, v]` before `ζ`**: `f` is continuous before `v`
and on `[0, v]` when `v` is finite, `g` is continuous before `ζ ≥ v`, and `f 0 = g 0`. -/
theorem eq_of_dyadic_eq {E : Type*} [TopologicalSpace E] [T2Space E] {f g : ℝ≥0 → E} {v ζ : ℝ≥0∞}
    (hf : ContinuousOn f {s | (s : ℝ≥0∞) < v}) (hfv : ∀ T : ℝ≥0, (T : ℝ≥0∞) = v → ContinuousOn f (Iic T))
    (hg : ContinuousOn g {s | (s : ℝ≥0∞) < ζ}) (hvζ : v ≤ ζ) (h0 : f 0 = g 0)
    (hd : ∀ p : ℕ × ℕ, (dyadicTime p : ℝ≥0∞) < v → f (dyadicTime p) = g (dyadicTime p))
    {t : ℝ≥0} (htv : (t : ℝ≥0∞) ≤ v) (htζ : (t : ℝ≥0∞) < ζ) : f t = g t := by
  have hlt : ∀ s : ℝ≥0, (s : ℝ≥0∞) < v → f s = g s := fun s hs => by
    have h1 := tendsto_lowerDyadic_of_continuousOn hf hs
    have h2 := tendsto_lowerDyadic_of_continuousOn hg (hs.trans_le hvζ)
    have e : (fun n => f (dyadicTime (lowerDyadic s n))) = fun n => g (dyadicTime (lowerDyadic s n)) :=
      funext fun n => hd _ (lt_of_le_of_lt (ENNReal.coe_le_coe.2 (dyadicTime_lowerDyadic_le s n)) hs)
    rw [e] at h1
    exact tendsto_nhds_unique h1 h2
  rcases htv.lt_or_eq with ht | ht
  · exact hlt t ht
  · rcases eq_zero_or_pos t with h0t | h0t
    · rw [h0t]; exact h0
    · have heq : EqOn f g (Iio t) := fun s hs => hlt s (by rw [← ht]; exact_mod_cast hs)
      have hgI : ContinuousOn g (Iic t) := hg.mono fun s hs => lt_of_le_of_lt (by exact_mod_cast hs) htζ
      have hcl : Iic t ⊆ closure (Iio t) := by
        rw [closure_Iio' (show (Iio t).Nonempty from ⟨0, h0t⟩)]
      exact heq.of_subset_closure (hfv t ht) hgI Iio_subset_Iic_self hcl (mem_Iic.2 le_rfl)

/-- The lifetime and the samples before it, read off an equality of killed histories. -/
theorem of_killedHistory_eq {Ω Ω₀ : Type*} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞} {W₀ : ℝ≥0 → Ω₀ → ℝ} {VL₀ : Fin nL → ℝ≥0 → Ω₀ → ℝ}
    {VR₀ : Fin nR → ℝ≥0 → Ω₀ → ℝ} {V₀ : Ω₀ → ℝ≥0∞} {ω : Ω} {ω₀ : Ω₀}
    (hk : killedHistory W VL VR V ω = killedHistory W₀ VL₀ VR₀ V₀ ω₀) :
    V ω = V₀ ω₀ ∧ ∀ p : ℕ × ℕ, (dyadicTime p : ℝ≥0∞) < V ω →
      W (dyadicTime p) ω = W₀ (dyadicTime p) ω₀ ∧ (∀ i, VL i (dyadicTime p) ω = VL₀ i (dyadicTime p) ω₀) ∧
        ∀ j, VR j (dyadicTime p) ω = VR₀ j (dyadicTime p) ω₀ := by
  have h1 : V ω = V₀ ω₀ := congrArg Prod.fst hk
  refine ⟨h1, fun p hp => ?_⟩
  have h2 := congrFun (congrArg Prod.snd hk) p
  have hp₀ : (dyadicTime p : ℝ≥0∞) < V₀ ω₀ := h1 ▸ hp
  simp only [killedHistory, hp, hp₀, ↓reduceIte, Prod.mk.injEq] at h2
  obtain ⟨hW, hL, hR⟩ := h2
  exact ⟨hW, fun i => congrFun hL i, fun j => congrFun hR j⟩

/-- A killed driving process stays measurable when killed at an earlier measurable time. -/
theorem isMeasurableKilledDriving_of_le {Ω₀ : Type*} {mΩ₀ : MeasurableSpace Ω₀} {W : ℝ≥0 → Ω₀ → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω₀ → ℝ} {VR : Fin nR → ℝ≥0 → Ω₀ → ℝ} {ζ V : Ω₀ → ℝ≥0∞}
    (hX : IsMeasurableKilledDriving W VL VR ζ) (hV : Measurable V) (hVζ : ∀ ω, V ω ≤ ζ ω) :
    IsMeasurableKilledDriving W VL VR V := by
  intro r A hA
  have e : {ω | (r : ℝ≥0∞) < V ω ∧ (W r ω, fun i => VL i r ω, fun i => VR i r ω) ∈ A} =
      {ω | (r : ℝ≥0∞) < V ω} ∩ {ω | (r : ℝ≥0∞) < ζ ω ∧ (W r ω, fun i => VL i r ω, fun i => VR i r ω) ∈ A} := by
    ext ω
    simp only [mem_ofPred_eq, mem_inter_iff]
    exact ⟨fun h => ⟨h.1, h.1.trans_le (hVζ ω), h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
  rw [e]
  exact (measurableSet_lt measurable_const hV).inter (hX r A hA)

end Agree

/-! ### The extension from the joint law -/

section Extension

variable {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

/-- **Aux. lemma 54 from the joint law of the field and the stopped history.** Let a coupling through `V` and a family
reference on a standard Borel space `Ω₀` (with a measurable stop `V₀ ≤ ζ₀`) have the same joint law of (history killed
at the stop, field). Sample `ω₀` from the reference's conditional law given (killed history, field), evaluated at the
coupling's (killed history, field): `K = κ₀ ∘ (killedHistory, h)`. Under `P ⊗ K` the reference's coordinates read
through the second factor and the field `h` read through the first factor form an optional hull coupling (the two fields
agree almost surely), and the coordinates agree with the stopped ones at every `t ≤ V` before the lifetime. -/
theorem exists_extension_of_jointLaw (hκ : 0 < κ)
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    {V : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}
    (hSC : IsStoppedHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B V h)
    {Ω₀ : Type*} {mΩ₀ : MeasurableSpace Ω₀} [StandardBorelSpace Ω₀] {P₀ : Measure Ω₀} [IsProbabilityMeasure P₀]
    {𝓕₀ : Filtration ℝ≥0 mΩ₀} {W₀ : ℝ≥0 → Ω₀ → ℝ} {VL₀ : Fin nL → ℝ≥0 → Ω₀ → ℝ}
    {VR₀ : Fin nR → ℝ≥0 → Ω₀ → ℝ} {B₀ : ℝ≥0 → Ω₀ → ℝ} {ζ₀ : Ω₀ → ℝ≥0∞}
    {h₀ : Ω₀ → DistOn upperHalfPlaneOpens} (href : IsFamilyRef κ xL xR ρL ρR P₀ 𝓕₀ W₀ VL₀ VR₀ B₀ ζ₀ h₀)
    {V₀ : Ω₀ → ℝ≥0∞} (hV₀m : Measurable V₀) (hV₀ζ : ∀ ω₀, V₀ ω₀ ≤ ζ₀ ω₀)
    (hlaw : P.map (fun ω => (killedHistory W VL VR V ω, h ω)) =
      P₀.map (fun ω₀ => (killedHistory W₀ VL₀ VR₀ V₀ ω₀, h₀ ω₀))) :
    ∃ (K : Kernel Ω Ω₀) (_ : IsMarkovKernel K),
      IsOptionalHullCoupling κ xL xR ρL ρR (P ⊗ₘ K) (filtrationComap 𝓕₀ measurable_snd)
        (fun t p => W₀ t p.2) (fun i t p => VL₀ i t p.2) (fun i t p => VR₀ i t p.2) (fun t p => B₀ t p.2)
        (fun p => ζ₀ p.2) (fun p => h p.1) ∧
      ∀ᵐ p ∂(P ⊗ₘ K), V p.1 ≤ ζ₀ p.2 ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ V p.1 → (t : ℝ≥0∞) < ζ₀ p.2 →
        W₀ t p.2 = W t p.1 ∧ (∀ i, VL₀ i t p.2 = VL i t p.1) ∧ ∀ j, VR₀ j t p.2 = VR j t p.1 := by
  classical
  obtain ⟨hEv, hcont, hh, hgff, hX, -⟩ := hSC
  have hE₀ := href.1
  have hX₀ := isMeasurableKilledDriving_of_le (Coupling.IsIntegratedSLEEvolution.isMeasurableKilledDriving hE₀)
    hV₀m hV₀ζ
  have hR₁m : Measurable fun ω => (killedHistory W VL VR V ω, h ω) := (measurable_killedHistory hX).prodMk hh
  have hRrm : Measurable fun ω₀ => (killedHistory W₀ VL₀ VR₀ V₀ ω₀, h₀ ω₀) :=
    (measurable_killedHistory hX₀).prodMk href.2.1
  have : Nonempty Ω₀ := nonempty_of_isProbabilityMeasure P₀
  obtain ⟨κ₀, hκ₀, hfst, hpair⟩ := Sec7.aux54_exists_extension (Fr := id) hRrm measurable_id hR₁m hlaw
  have hKm : IsMarkovKernel (κ₀.comap (fun ω => (killedHistory W VL VR V ω, h ω)) hR₁m) := inferInstance
  set K : Kernel Ω Ω₀ := κ₀.comap (fun ω => (killedHistory W VL VR V ω, h ω)) hR₁m with hK
  set E : Measure (Ω × Ω₀) := P ⊗ₘ K with hE
  have hpm : Measurable fun p : Ω × Ω₀ => ((killedHistory W VL VR V p.1, h p.1), p.2) :=
    (hR₁m.comp measurable_fst).prodMk measurable_snd
  have hsnd : E.map Prod.snd = P₀ := by
    have e : (Prod.snd : Ω × Ω₀ → Ω₀) =
        Prod.snd ∘ fun p : Ω × Ω₀ => ((killedHistory W VL VR V p.1, h p.1), p.2) := rfl
    rw [e, ← Measure.map_map measurable_snd hpm, hpair, Measure.map_map measurable_snd (hRrm.prodMk measurable_id)]
    exact Measure.map_id
  -- the coupling's (history, field) and the reference's agree almost surely
  have hdiag : ∀ᵐ p ∂E, (killedHistory W VL VR V p.1, h p.1) = (killedHistory W₀ VL₀ VR₀ V₀ p.2, h₀ p.2) := by
    have hD : MeasurableSet {q : (HistorySpace nL nR × DistOn upperHalfPlaneOpens) × Ω₀ |
        q.1 = (killedHistory W₀ VL₀ VR₀ V₀ q.2, h₀ q.2)} :=
      measurableSet_eq_fun measurable_fst (hRrm.comp measurable_snd)
    have h1 : ∀ᵐ q ∂(P₀.map fun ω => ((killedHistory W₀ VL₀ VR₀ V₀ ω, h₀ ω), id ω)),
        q.1 = (killedHistory W₀ VL₀ VR₀ V₀ q.2, h₀ q.2) :=
      (ae_map_iff (hRrm.prodMk measurable_id).aemeasurable hD).2 (Eventually.of_forall fun ω => rfl)
    rw [← hpair] at h1
    exact (ae_map_iff hpm.aemeasurable hD).1 h1
  have hfield : ∀ᵐ p ∂E, h p.1 = h₀ p.2 := hdiag.mono fun p hp => congrArg Prod.snd hp
  have hkh : ∀ᵐ p ∂E, killedHistory W VL VR V p.1 = killedHistory W₀ VL₀ VR₀ V₀ p.2 :=
    hdiag.mono fun p hp => congrArg Prod.fst hp
  -- the optional hull coupling, inherited from the reference
  have hgff' : ∀ u₀ : ℂ → ℝ, IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀ →
      LQGMetric.IsZBGFFProcess upperHalfPlaneOpens (fun φ (p : Ω × Ω₀) => h p.1 φ - ∫ z, u₀ z * φ z) E :=
    fun u₀ hu₀ => by
      have h1 := hgff u₀ hu₀
      rw [← hfst] at h1
      exact Restart.isZBGFFProcess_comp measurable_fst h1
  have hC := (href.comap hκ measurable_snd hsnd (hh.comp measurable_fst) hgff' hfield).isOptionalHullCoupling hκ
  -- the paths of the two sides
  have hpathS : ∀ᵐ p ∂E, Sec2.IsSLEPathUpTo κ xL xR ρL ρR (fun t => W t p.1) (fun i t => VL i t p.1)
      (fun i t => VR i t p.1) (fun t => B t p.1) (V p.1) := by
    have h1 := hEv.ae_path
    rw [← hfst] at h1
    exact ae_of_ae_map measurable_fst.aemeasurable h1
  have hcontS : ∀ᵐ p ∂E, ∀ T : ℝ≥0, (T : ℝ≥0∞) = V p.1 →
      ContinuousOn (fun t => (W t p.1, fun i => VL i t p.1, fun j => VR j t p.1)) (Iic T) := by
    have h1 := hcont
    rw [← hfst] at h1
    exact ae_of_ae_map measurable_fst.aemeasurable h1
  have hpath₀ : ∀ᵐ p ∂E, Sec2.IsSLEPathUpTo κ xL xR ρL ρR (fun t => W₀ t p.2) (fun i t => VL₀ i t p.2)
      (fun i t => VR₀ i t p.2) (fun t => B₀ t p.2) (ζ₀ p.2) := by
    have h1 := hE₀.isSLEEvolutionUpTo.ae_path
    rw [← hsnd] at h1
    exact ae_of_ae_map measurable_snd.aemeasurable h1
  refine ⟨K, hKm, hC, ?_⟩
  filter_upwards [hkh, hpathS, hcontS, hpath₀] with p hk hpS hcS hp₀
  obtain ⟨hVV, hsamp⟩ := of_killedHistory_eq hk
  have hVζ : V p.1 ≤ ζ₀ p.2 := hVV ▸ hV₀ζ p.2
  refine ⟨hVζ, fun t htV htζ => ⟨?_, fun i => ?_, fun j => ?_⟩⟩
  · exact (eq_of_dyadic_eq hpS.continuousOn_w (fun T hT => (hcS T hT).fst) hp₀.continuousOn_w hVζ
      (hpS.w_zero.trans hp₀.w_zero.symm) (fun q hq => (hsamp q hq).1) htV htζ).symm
  · exact (eq_of_dyadic_eq (hpS.continuousOn_vL i)
      (fun T hT => (continuous_apply i).comp_continuousOn (hcS T hT).snd.fst) (hp₀.continuousOn_vL i) hVζ
      ((hpS.vL_zero i).trans (hp₀.vL_zero i).symm) (fun q hq => (hsamp q hq).2.1 i) htV htζ).symm
  · exact (eq_of_dyadic_eq (hpS.continuousOn_vR j)
      (fun T hT => (continuous_apply j).comp_continuousOn (hcS T hT).snd.snd) (hp₀.continuousOn_vR j) hVζ
      ((hpS.vR_zero j).trans (hp₀.vR_zero j).symm) (fun q hq => (hsamp q hq).2.2 j) htV htζ).symm

end Extension

/-! ### Aux. lemma 54 from the stopped whole-field identification -/

/-- **Aux. lemma 54 in kernel form for Galmarino stops, from the stopped whole-field identification** (every
`κ > 0`): the reference is Theorem 1.1's construction kept with its families (`exists_isFamilyRef`), stopped at
`R(its history) ∧ ζ₀`. -/
theorem stoppedHullExtendGKStatement_of_jointLaw {κ : ℝ} (hκ : 0 < κ) (hJL : StoppedJointLawStatement.{u} κ) :
    StoppedHullExtendGKStatement.{u} κ := by
  intro nL nR xL xR ρL ρR hF R hRm hRg Ω mΩ P _ 𝓕 W VL VR B V h hSC hV
  obtain ⟨Ω₀, mΩ₀, hSB, P₀, hP₀, 𝓕₀, W₀, VL₀, VR₀, B₀, ζ₀, h₀, href⟩ :=
    exists_isFamilyRef.{u} (ρL := ρL) (ρR := ρR) hκ hF
  have hlaw := hJL xL xR ρL ρR hF R hRm hRg P 𝓕 W VL VR B V h hSC hV P₀ 𝓕₀ W₀ VL₀ VR₀ B₀ ζ₀ h₀
    (href.isOptionalHullCoupling hκ)
  have hX₀ := Coupling.IsIntegratedSLEEvolution.isMeasurableKilledDriving href.1
  have hV₀m : Measurable fun ω₀ => min (R (killedHistory W₀ VL₀ VR₀ ζ₀ ω₀)) (ζ₀ ω₀) :=
    (hRm.comp (measurable_killedHistory hX₀)).min (measurable_lifetime hX₀)
  obtain ⟨K, hK, hC, hag⟩ := exists_extension_of_jointLaw hκ hSC href hV₀m (fun ω₀ => min_le_right _ _) hlaw
  exact ⟨Ω₀, mΩ₀, K, hK, _, _, _, _, _, _, hC, hag⟩

/-- **Aux. lemma 54 for Galmarino stops, enlargement form, from the stopped whole-field identification.** -/
theorem stoppedHullExtendGStatement_of_jointLaw {κ : ℝ} (hκ : 0 < κ) (hJL : StoppedJointLawStatement.{u} κ) :
    StoppedHullExtendGStatement.{u} κ :=
  stoppedHullExtendGStatement_of_kernel (stoppedHullExtendGKStatement_of_jointLaw hκ hJL)

end StoppedExtendWF

end Restart

end InteractingSLE
