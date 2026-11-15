/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux65NegWord

/-!
# Reducing negative-side R5 to the stopped two-mark first-swallow theorem

`TwoMarkLowUpToStatement` is the exact remaining stochastic input, not a proved
theorem. The reduction supplies the local evolution from the reference kernel,
deletes the passive seeds, reflects, and projects the null event back from the
independent Brownian enlargement. It uses no determination or full trace theorem.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
universe u

namespace InteractingSLE.Sec5.Aux65Neg

open Restart Sec7.PocketTraversal Sec2

/-- **Unproved stochastic input:** the bottom-right entry of (SS1), restricted
to total weight zero, for a two-mark evolution at an announced local stop.
The given trace is injective and continuous through the stop. The conclusion
includes that stop; no extension to a maximal reference evolution is assumed. -/
def TwoMarkLowUpToStatement : Prop :=
  ∀ (κ a b r : ℝ), 0 < κ → κ < 4 → 0 < a → a < b → r ≤ κ / 2 - 4 →
  ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ) (W B : ℝ≥0 → Ω → ℝ)
    (xL ρL : Fin 0 → ℝ) (VL : Fin 0 → ℝ≥0 → Ω → ℝ)
    (VR : Fin 2 → ℝ≥0 → Ω → ℝ) (e : Ω → ℝ≥0∞),
    IsSLEEvolutionUpTo κ xL ![a, b] ρL ![r, -r] P 𝓕 W VL VR B e →
    (∀ ω, Continuous (W · ω)) → (∀ i ω, Continuous (VR i · ω)) →
    ∀ (T : ℕ → Ω → ℝ≥0), Coupling.IsAnnouncingSeq 𝓕 P e T →
    ∀ η : Ω → ℝ≥0 → ℂ,
      (∀ᵐ ω ∂P, IsGeneratingTrace (W · ω) (e ω) (η ω)) →
      (∀ᵐ ω ∂P, InjOn (η ω) {t | (t : ℝ≥0∞) ≤ e ω}) →
      ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ e ω →
        ∀ y ∈ Ioo a b, η ω t ≠ (y : ℂ)

/-- The reference characteristic kernel supplies the local SDE on the same
Brownian enlargement used in the positive-side barrier. -/
theorem exists_localEvolution_prod {S : Type u} [MeasurableSpace S]
    (D : Aux61R45.ReferenceSetting S) :
    ∃ (ν : Measure (ℕ → ℝ)) (_ : IsProbabilityMeasure ν)
      (𝓦 : Filtration ℝ≥0 (inferInstance : MeasurableSpace (ℕ → ℝ)))
      (B : ℝ≥0 → S × (ℕ → ℝ) → ℝ),
      IsSLEEvolutionUpTo D.κ (flowLineXL D.b D.J D.y) (flowLineXR D.b D.J D.y)
        (flowLineRhoL D.κ D.b D.J D.y D.θ) (flowLineRhoR D.κ D.b D.J D.y D.θ)
        (D.P.prod ν) (WholeField.prodFiltration D.filt 𝓦)
        (fun t p => D.W t p.1)
        (fun i t p => geomLW D.W (fun _ => flowLineXL D.b D.J D.y) i t p.1)
        (fun j t p => geomRW D.W (fun _ => flowLineXR D.b D.J D.y) j t p.1)
        B (fun p => D.e p.1) := by
  let _ := D.prob
  let _ := D.rightContinuous
  have hF := Theorem15.isOrderedForceWord_flowLine D.b D.J D.y
  have hinit : ∀ᵐ ω ∂D.P, 0 < D.e ω ∧
      ContinuousOn (D.W · ω) {t | (t : ℝ≥0∞) < D.e ω} ∧ D.W 0 ω = 0 ∧
      (∀ i, geomLW D.W (fun _ => flowLineXL D.b D.J D.y) i 0 ω = flowLineXL D.b D.J D.y i) ∧
      ∀ j, geomRW D.W (fun _ => flowLineXR D.b D.J D.y) j 0 ω = flowLineXR D.b D.J D.y j := by
    filter_upwards [D.ae_pos] with ω hω
    exact ⟨hω, (D.continuous ω).continuousOn, D.zero ω,
      fun i => geomLW_zero D.continuous D.zero (hF.2.1 i),
      fun j => geomRW_zero D.continuous D.zero (hF.2.2.2 j)⟩
  have hint := fun φ => Coupling.MartMeans2.integrable_apply_of_isCouplingCharFun
    D.kernel hinit φ ((LQGMetric.measurable_distOn_apply φ).comp D.measurable_field)
  obtain ⟨ν, hν, 𝓦, B, hE, -, -⟩ := StoppedK2.isRandomWordEvolutionUpTo_prod_of_isCouplingCharFun
    (𝒢 := ⊥) (F := Set.univ) D.κ_pos D.nullSets bot_le MeasurableSet.univ
    measurable_const measurable_const (fun _ => hF.2.1) (fun _ => hF.2.2.2)
    (fun _ => hF.1) (fun _ => hF.2.2.1) D.zero D.continuous D.adapted D.stopping
    D.announcing hint D.kernel (D.threshold.mono fun _ h _ => h)
  obtain ⟨-, -, -, -, hB, hW, hVL, hVR, hp⟩ := hE
  exact ⟨ν, hν, 𝓦, B, hB, hW, hVL, hVR, hp.mono fun _ h => h trivial⟩

/-- **Conditional reduction of R5:** the sole missing input is the stopped
two-mark bottom-right entry of (SS1). In particular the reference kernel,
arbitrary jump-candidate set, reflection, and Brownian projection add no inputs. -/
theorem r5NegStatement_of_twoMarkLowUpTo (hSS : TwoMarkLowUpToStatement.{u}) :
    Aux61Cov.R5NegStatement.{u} := by
  intro S mS D I hy hθ href hinj
  let _ := D.prob
  obtain ⟨x₂, x₁, r, eL, eR, h₂₁, h₁, hr, hI, hx, hρ, hzL, hzR⟩ :=
    subword_of_refNeg D.κ_pos href
  have hloc := exists_localEvolution_prod D
  rw [hy, hθ] at hloc
  obtain ⟨ν, hν, 𝓦, B, hE⟩ := hloc
  let _ := hν
  have hdel := evolution_compEmb hE eL eR hzL hzR
  let 𝓕 := WholeField.prodFiltration D.filt 𝓦
  let W : ℝ≥0 → S × (ℕ → ℝ) → ℝ := fun t p => -D.W t p.1
  let VL : Fin 0 → ℝ≥0 → S × (ℕ → ℝ) → ℝ := fun i t p =>
    -geomRW D.W (fun _ => flowLineXR D.b D.J 0) (eR i) t p.1
  let VR : Fin 2 → ℝ≥0 → S × (ℕ → ℝ) → ℝ := fun i t p =>
    -geomLW D.W (fun _ => flowLineXL D.b D.J 0) (eL i) t p.1
  let e : S × (ℕ → ℝ) → ℝ≥0∞ := fun p => D.e p.1
  let η : S × (ℕ → ℝ) → ℝ≥0 → ℂ := fun p t => LP.reflectC (D.Γ p.1 t)
  have hpos : (fun i => -(flowLineXL D.b D.J 0 (eL i))) = ![-x₁, -x₂] := by
    funext i
    rw [hx]
    fin_cases i <;> rfl
  have hweights : (fun i => flowLineRhoL D.κ D.b D.J 0 0 (eL i)) = ![r, -r] := funext hρ
  have hreflect : IsSLEEvolutionUpTo D.κ
      (fun i => -(flowLineXR D.b D.J 0 (eR i))) ![-x₁, -x₂]
      (fun i => flowLineRhoR D.κ D.b D.J 0 0 (eR i)) ![r, -r]
      (D.P.prod ν) 𝓕 W VL VR (-B) e := by
    rw [← hpos, ← hweights]
    exact ⟨hdel.brownian.neg, hdel.adapted_W.neg,
      fun i => (hdel.adapted_VR i).neg, fun i => (hdel.adapted_VL i).neg,
      hdel.ae_path.mono fun _ h => h.reflect⟩
  have hT : Coupling.IsAnnouncingSeq 𝓕 (D.P.prod ν) e (fun n p => D.T n p.1) := by
    refine ⟨fun n => Sec7.PhaseSelFull.isStoppingTime_fst (D.announcing.1 n),
      fun p => D.announcing.2.1 p.1, fun n => ?_, ?_⟩
    · exact ConverseBefore.ae_fst_of_ae (P₀ := ν) (D.announcing.2.2.1 n)
    · exact ConverseBefore.ae_fst_of_ae (P₀ := ν) D.announcing.2.2.2
  have htrace : ∀ᵐ p ∂(D.P.prod ν), IsGeneratingTrace (W · p) (e p) (η p) := by
    filter_upwards [ConverseBefore.ae_fst_of_ae (P₀ := ν) D.trace] with p hp
    simp only [hy, Complex.ofReal_zero, sub_zero] at hp
    exact LP.isGeneratingTrace_reflect hp
  have hηinj : ∀ᵐ p ∂(D.P.prod ν), InjOn (η p) {t | (t : ℝ≥0∞) ≤ e p} := by
    filter_upwards [ConverseBefore.ae_fst_of_ae (P₀ := ν) hinj] with p hp s hs t ht he
    exact hp hs ht (LP.reflectC_injective he)
  have havoid := hSS D.κ (-x₁) (-x₂) r D.κ_pos href.1 (by linarith) (by linarith) hr
    (D.P.prod ν) 𝓕 W (-B) _ _ VL VR e hreflect
    (fun p => (D.continuous p.1).neg)
    (fun i p => (isForcePath_geomLW D.continuous
      (fun _ => flowLineXL D.b D.J 0) p.1 (eL i)).1.neg)
    _ hT η htrace hηinj
  apply ConverseBefore.ae_of_ae_fst (P₀ := ν)
  filter_upwards [havoid] with p hp t ht y hyI he
  have hy' := hI hyI
  apply hp t ht (-y) ⟨by linarith [hy'.2], by linarith [hy'.1]⟩
  change LP.reflectC (D.Γ p.1 t) = ((-y : ℝ) : ℂ)
  rw [he]
  simp only [LP.reflectC, Complex.conj_ofReal, Complex.ofReal_neg]

end InteractingSLE.Sec5.Aux65Neg
