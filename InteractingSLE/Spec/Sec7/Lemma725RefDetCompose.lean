/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma725RefDetShift

/-!
# The determination of the killed pocket history: ambient recovery, Proposition 5.13, pocket erasure

Packet PROVE-LEMMA725REF4, item 3. Specification §7.4, Aux. lemma 125's proof, "Recovering the local curve from its
local field" (`source/spec/p385-432.md` L197–L250, p. 398): "The pair `(ℰ, H_C)` determines the entire ambient field.
[…] The already established global field determination, followed by the measurable selected-pocket erasure, thus
makes `X_C` measurable from `(ℰ, H_C)`"; Astra's shortcut note (`source/external/AstraIG1/ig1_shortcuts_audited.txt`
L276–L292), Proposition 2.1 step 3, equation (2): `X = F(E, H)`.

The determination input `PocketHistDet0` (canonical chart, `Lemma725RefDetShift`) is the composition of three maps:

1. **the ambient recovery** (`PocketAmbientRecovery`, named input): almost surely on the pocket event, the ambient field
   `h` is a Borel function of a walls' record and the pocket field `H = chartTransport (pChart A C ψ) 1 0 χ(κ) h`
   (p. 398: the exterior Dirichlet projection is recorded; the Green potentials of tests in `C` are dense in `H¹₀(C)`,
   and the GFF isometry recovers every ambient pairing as an `L²` limit of interior coordinates; a measurable
   subsequence makes the recovery Borel);
2. **Proposition 5.13** for the centred strip exploration (named hypothesis, in the form PROVE-PROP513C proves it,
   `Prop513Wire.prop513_path_of_partA_reverseVisit`): a version of the counterflow trace that is measurable for the
   field's σ-algebra at every time; by the Doob–Dynkin lemma (`StronglyMeasurable.exists_eq_measurable_comp`) its
   values at the nonnegative rational times are a Borel function of the field (**`exists_measurable_path_of_prop513`**);
3. **the measurable pocket erasure** (`PocketErasure`, named input): almost surely on the pocket event, the killed
   relative history of the erased traversal is a Borel function of a walls' record and the counterflow at the
   nonnegative rational times.

## Main results

* `PocketAmbientRecovery`, `PocketErasure` (named inputs), `exists_measurable_path_of_prop513`;
* **`pocketHistDet0_of_recovery`**: `PocketHistDet0` from the three;
* **`pocketHistDet_of_recovery`**: `PocketHistDet` from the three (with `pocketHistDet_of_zero`).

Conditional helpers; no source theorem is replaced. Ruling R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any result taking them as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)
open SupercriticalConformalCovariance (IsConformalBijection)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.Lemma725RefChart

open PocketTraversal Lemma71C LawUnique PocketStopField

universe u

section Defs

variable {Ω : Type u}

/-- **Named input: the ambient recovery** (Aux. lemma 125's proof, p. 398, "The pair `(ℰ, H_C)` determines the entire
ambient field"): almost surely on `A`, the ambient field `h` is a Borel function of a walls-measurable standard Borel
record and the pocket field `chartTransport (pChart A C ψ) 1 0 χ(κ) h`. -/
def PocketAmbientRecovery (κ : ℝ) (𝓦 : MeasurableSpace Ω) [MeasurableSpace Ω] (P : Measure Ω) (A : Set Ω)
    (C : Ω → Set ℂ) (ψ : Ω → ℂ → ℂ) (h : Ω → DistOn upperHalfPlaneOpens) : Prop :=
  ∃ (ε : Type u) (_ : MeasurableSpace ε) (_ : StandardBorelSpace ε) (E : Ω → ε)
    (F : ε × DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens),
    Measurable[𝓦] E ∧ Measurable F ∧
      ∀ᵐ ω ∂P, ω ∈ A → ∀ hc : (pChart A C ψ ω).IsConformal,
        h ω = F (E ω, Chart.chartTransport hc 1 0 (chiC κ) (h ω))

/-- **Named input: the measurable pocket erasure** (Aux. lemma 125's proof, p. 398, "the measurable selected-pocket
erasure"): almost surely on `A`, the killed relative history of the erased traversal `γ` with marks `xL`, `xR` is a
Borel function of a walls-measurable standard Borel record and the ambient counterflow `η` at the nonnegative rational
times. -/
def PocketErasure (𝓦 : MeasurableSpace Ω) [MeasurableSpace Ω] (P : Measure Ω) (A : Set Ω) {nL nR : ℕ}
    (γ : Ω → ℝ → ℂ) (xL : Ω → Fin (nL + 1) → ℝ) (xR : Ω → Fin (nR + 1) → ℝ) (η : Ω → ℝ → ℂ) : Prop :=
  ∃ (ε : Type u) (_ : MeasurableSpace ε) (_ : StandardBorelSpace ε) (E : Ω → ε)
    (G : ε × (ℚ≥0 → ℂ) → HistorySpace (nL + 1) (nR + 1)), Measurable[𝓦] E ∧ Measurable G ∧
      ∀ᵐ ω ∂P, ω ∈ A →
        killedHistory (fun t ω => segDriver (γ ω) t) (geomLW (fun t ω => segDriver (γ ω) t) xL)
          (geomRW (fun t ω => segDriver (γ ω) t) xR) (fun ω => capLife (γ ω)) ω =
            G (E ω, fun q : ℚ≥0 => η ω (q : ℝ))

end Defs

section Compose

variable {Ω : Type u} {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **Proposition 5.13 as a Borel map** (Doob–Dynkin): if a version `Γ'` of the counterflow trace is measurable for the
field's σ-algebra at every time, the trace at the nonnegative rational times is almost surely a Borel function of the
field. -/
theorem exists_measurable_path_of_prop513 {h : Ω → DistOn upperHalfPlaneOpens} {η : Ω → ℝ → ℂ}
    (h513 : ∃ Γ' : Ω → ℝ≥0 → ℂ, (∀ t, StronglyMeasurable[MeasurableSpace.comap h inferInstance] fun ω => Γ' ω t) ∧
      ∀ᵐ ω ∂P, Γ' ω = fun t : ℝ≥0 => η ω t) :
    ∃ F : DistOn upperHalfPlaneOpens → ℚ≥0 → ℂ, Measurable F ∧
      ∀ᵐ ω ∂P, (fun q : ℚ≥0 => η ω (q : ℝ)) = F (h ω) := by
  obtain ⟨Γ', hΓm, hΓ⟩ := h513
  have hf : ∀ q : ℚ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, StronglyMeasurable f ∧
      (fun ω => Γ' ω (q : ℝ≥0)) = f ∘ h := fun q => (hΓm (q : ℝ≥0)).exists_eq_measurable_comp
  choose f hfm hfe using hf
  refine ⟨fun X q => f q X, measurable_pi_iff.2 fun q => (hfm q).measurable, ?_⟩
  filter_upwards [hΓ] with ω hω
  funext q
  have e1 := congrFun (hfe q) ω
  have e2 := congrFun hω (q : ℝ≥0)
  simp only [Function.comp_apply] at e1
  rw [← e1, e2]
  rfl

/-- **The canonical determination input from the ambient recovery, Proposition 5.13 and the pocket erasure**
(p. 398; Astra's Proposition 2.1 step 3): the record `(E₁, E₂)` and the Borel map
`((e₁, e₂), H) ↦ G (e₂, F₅₁₃ (Rec (e₁, H)))`. -/
theorem pocketHistDet0_of_recovery {κ : ℝ} {nL nR : ℕ} {A : Set Ω} {γ : Ω → ℝ → ℂ}
    {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ} {C : Ω → Set ℂ} {ψ : Ω → ℂ → ℂ}
    {h : Ω → DistOn upperHalfPlaneOpens} {η : Ω → ℝ → ℂ} (hrec : PocketAmbientRecovery κ 𝓦 P A C ψ h)
    (h513 : ∃ Γ' : Ω → ℝ≥0 → ℂ, (∀ t, StronglyMeasurable[MeasurableSpace.comap h inferInstance] fun ω => Γ' ω t) ∧
      ∀ᵐ ω ∂P, Γ' ω = fun t : ℝ≥0 => η ω t)
    (hers : PocketErasure 𝓦 P A γ xL xR η) :
    PocketHistDet0 κ 𝓦 P A γ xL xR C ψ h := by
  obtain ⟨ε₁, m₁, hSB₁, E₁, Rec, hE₁, hRec, hrecω⟩ := hrec
  obtain ⟨ε₂, m₂, hSB₂, E₂, Er, hE₂, hEr, hersω⟩ := hers
  obtain ⟨F, hF, hFω⟩ := exists_measurable_path_of_prop513 (P := P) h513
  refine ⟨ε₁ × ε₂, inferInstance, inferInstance, fun ω => (E₁ ω, E₂ ω),
    fun p => Er (p.1.2, F (Rec (p.1.1, p.2))), hE₁.prodMk hE₂,
    hEr.comp (measurable_fst.snd.prodMk (hF.comp (hRec.comp (measurable_fst.fst.prodMk measurable_snd)))), ?_⟩
  filter_upwards [hrecω, hersω, hFω] with ω h1 h2 h3 hωA hc
  rw [h2 hωA, h3, ← h1 hωA hc]

/-- **The determination input from the ambient recovery, Proposition 5.13 and the pocket erasure**, for every branch
integer and frame constant (`pocketHistDet0_of_recovery`, `pocketHistDet_of_zero`). -/
theorem pocketHistDet_of_recovery {κ : ℝ} {nL nR : ℕ} {A : Set Ω} {γ : Ω → ℝ → ℂ}
    {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ} {C : Ω → Set ℂ} {ψ : Ω → ℂ → ℂ}
    {h : Ω → DistOn upperHalfPlaneOpens} {η : Ω → ℝ → ℂ} (hCo : ∀ ω ∈ A, IsOpen (C ω)) (hCH : ∀ ω ∈ A, C ω ⊆ H)
    (hψ : ∀ ω ∈ A, IsConformalBijection (ψ ω) (C ω) H) (hrec : PocketAmbientRecovery κ 𝓦 P A C ψ h)
    (h513 : ∃ Γ' : Ω → ℝ≥0 → ℂ, (∀ t, StronglyMeasurable[MeasurableSpace.comap h inferInstance] fun ω => Γ' ω t) ∧
      ∀ᵐ ω ∂P, Γ' ω = fun t : ℝ≥0 => η ω t)
    (hers : PocketErasure 𝓦 P A γ xL xR η) :
    PocketHistDet κ 𝓦 P A γ xL xR C ψ h :=
  pocketHistDet_of_zero hCo hCH hψ (pocketHistDet0_of_recovery hrec h513 hers)

end Compose

end InteractingSLE.Sec7.Lemma725RefChart
