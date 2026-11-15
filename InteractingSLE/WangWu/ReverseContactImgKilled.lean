/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.ReverseContactImgLevy
import InteractingSLE.WangWu.ReverseContactImgCont

/-!
# The image driver of the contact step, part 6: a killed `SLE₄(ρ)` word continues to a simple transient trace

Packet PROVE-WW-B16, steps B5–B7 of PROVE-WW-B15's plan assembled. Wang–Wu
(`source/external/WW17LP/wang_wu_lean_preprocessed.pdf`, ruling R31), proof of Proposition 4.18 (text dump
L1627–L1636): "Its conditional harmonic means and conformal-radius brackets, just identified, satisfy Lemma 2.11. Hence
its law is the nonnegative-cumulative force-point law. The trace lemma and Corollary 4.13 imply … An interior endpoint
could be continued by the original continuous trace."

**`IsKilledWord.ae_exists_continuation_four`**: let `(W, VL, VR)` be a killed word before `T` (`IsKilledWord`),
adapted to a filtration whose time-zero σ-algebra contains the null sets, with `{q < T} ∈ 𝓖_q`, announced by stopping
times `σₙ < T`, whose explicit `SLE₄(ρ)` coupling means (nonnegative cumulative weights) are local martingales before
`min (swallowTime z) T`, and whose driver has a simple trace in `ℍ` before `T`. Then almost surely the driver has a
continuous continuation `X` (`X₀ = 0`, `X = W` before `T`) whose trace is a simple transient trace in `ℍ`
(`GoodPath X ⊤`; `GoodPath.trace` gives the trace as a simple proper Loewner trace).

Proof: Lemma 2.11 for the killed word (`IsKilledWord.exists_isWordEntrance`) gives, on `Ω × Ω₀`, a Brownian motion of
the product filtration driving the integrated equations before `T`; the continuation theorem
(`ae_exists_continuation`) applies on `Ω × Ω₀`, and its conclusion depends only on the first coordinate.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.WangWu

namespace ImgDrv

open MartChar Sec7.PhaseSelFull

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {nL nR : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓖 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {T : Ω → WithTop ℝ≥0} {σ : ℕ → Ω → ℝ≥0} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

/-- **A killed `SLE₄(ρ)` word with nonnegative cumulative weights continues to a simple transient trace** (Lemma 2.11,
Lemma 4.12 and Corollary 4.13 for a driver defined only before its killing time). -/
theorem IsKilledWord.ae_exists_continuation_four
    (hnull : ∀ s, MeasurableSet s → P s = 0 → MeasurableSet[𝓖 0] s)
    (hK : IsKilledWord W VL VR T) (hWa : StronglyAdapted 𝓖 W) (hVLa : ∀ i, StronglyAdapted 𝓖 (VL i))
    (hVRa : ∀ j, StronglyAdapted 𝓖 (VR j)) (hσ : ∀ n, IsStoppingTime 𝓖 fun ω => (σ n ω : WithTop ℝ≥0))
    (hσm : ∀ ω, Monotone (σ · ω)) (hσT : ∀ n ω, (σ n ω : WithTop ℝ≥0) < T ω)
    (hσlim : ∀ᵐ ω ∂P, ∀ u : ℝ≥0, (u : WithTop ℝ≥0) < T ω → ∃ n, u ≤ σ n ω)
    (hTq : ∀ q : ℝ≥0, MeasurableSet[𝓖 q] {ω | (q : WithTop ℝ≥0) < T ω})
    (hcum : HasNonnegCumWeights ρL ρR)
    (hmart : ∀ z ∈ H, IsLocalMartingaleBefore 𝓖 P
      (fun ω => min (QuantumZipper.swallowTime (wpath W ω) z : WithTop ℝ≥0) (T ω))
      (coupProc 4 ρL ρR W VL VR z))
    (hγ : ∀ᵐ ω ∂P, ∃ γ : ℝ≥0 → ℂ,
      (∀ s : ℝ≥0, (s : WithTop ℝ≥0) < T ω → Sec7.IsGeneratingTraceIcc (W · ω) s γ) ∧
      (∀ s t : ℝ≥0, (s : WithTop ℝ≥0) < T ω → (t : WithTop ℝ≥0) < T ω → γ s = γ t → s = t) ∧
      ∀ t : ℝ≥0, 0 < t → (t : WithTop ℝ≥0) < T ω → γ t ∈ H) :
    ∀ᵐ ω ∂P, ∃ X : ℝ≥0 → ℝ, Continuous X ∧ X 0 = 0 ∧
      (∀ t : ℝ≥0, (t : WithTop ℝ≥0) < T ω → X t = W t ω) ∧ GoodPath X ⊤ := by
  obtain ⟨Ω₀, m₀, P₀, hP₀, 𝓦, B, hB, hBc, hE⟩ :=
    hK.exists_isWordEntrance (by norm_num : (0 : ℝ) < 4) hnull hWa hVLa hVRa hσ hσm hσT hσlim hmart
  set 𝓘 := WholeField.prodFiltration 𝓖 𝓦 with h𝓘
  have hTq' : ∀ q : ℝ≥0, MeasurableSet[𝓘 q] {p : Ω × Ω₀ | (q : ℝ≥0∞) < T p.1} := fun q =>
    WholeField.comap_fst_le_prodFiltration 𝓖 𝓦 q _ ⟨_, hTq q, rfl⟩
  have hT0 : ∀ p : Ω × Ω₀, (0 : ℝ≥0∞) < T p.1 := fun p =>
    lt_of_le_of_lt (WithTop.coe_le_coe.2 (zero_le : (0 : ℝ≥0) ≤ σ 0 p.1)) (hσT 0 p.1)
  have hγ' : ∀ᵐ p ∂(P.prod P₀), ∃ γ : ℝ≥0 → ℂ,
      (∀ s : ℝ≥0, (s : ℝ≥0∞) < T p.1 → Sec7.IsGeneratingTraceIcc (fun t => W t p.1) s γ) ∧
      (∀ s t : ℝ≥0, (s : ℝ≥0∞) < T p.1 → (t : ℝ≥0∞) < T p.1 → γ s = γ t → s = t) ∧
      ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < T p.1 → γ t ∈ H :=
    Measure.quasiMeasurePreserving_fst.ae hγ
  have h := ae_exists_continuation (Ω := Ω × Ω₀) (P := P.prod P₀) (𝓘 := 𝓘) hB hBc
    (W := fun t p => W t p.1) (VL := fun i t p => VL i t p.1) (VR := fun j t p => VR j t p.1)
    (stronglyAdapted_fst hWa) (fun i => stronglyAdapted_fst (hVLa i)) (fun j => stronglyAdapted_fst (hVRa j))
    (T := fun p => T p.1) hTq' hT0 hcum hE (fun p t ht htT i => hK.sepL p.1 t ht htT i)
    (fun p t ht htT j => hK.sepR p.1 t ht htT j) hγ'
  have h2 := Measure.ae_ae_of_ae_prod h
  filter_upwards [h2] with ω hω
  obtain ⟨_, hX⟩ := hω.exists
  exact hX

end ImgDrv

end InteractingSLE.WangWu
