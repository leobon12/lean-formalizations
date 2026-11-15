/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.RetPlumbProofSplit
import InteractingSLE.Spec.Restart.StoppedK2Wire
import InteractingSLE.Spec.Sec7.Lemma76R

/-!
# Stopped K2, conditional-law transport, and retained determination

Packet PROVE-RETPLUMB. This file packages the exact inputs of the landed stopped
K2, transports its conclusion from a standard Borel model to a type event on an
arbitrary probability space, and glues finitely many such events. Construction
of those models remains a named mathematical hypothesis. In particular, no
capped record rule is asserted to be Galmarino: announcing times are explicit
inputs. A construction using Galmarino must use a genuine hit rule instead.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.Restart.RetAux79

open LQGMetric (DistOn TestOn)
open Sec2.Assembly Sec7.PocketTraversal
open Supp7 Sec7.Lemma76F
open DomainMarkov DomainMarkov.K2 DomainMarkov.Aux79 FCDet StoppedExtend

/-- Exact typed stochastic inputs for `ae_stoppedCodeMatch_of_hasSafeLaw`.
The initial sigma-algebra is the time-zero sigma-algebra of `filt`. -/
structure StoppedTypeData (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (κ θ : ℝ) where
  nL : ℕ
  nR : ℕ
  rhoL : Fin nL → ℝ
  rhoR : Fin nR → ℝ
  filt : Filtration ℝ≥0 mΩ
  word : Ω → BoundaryWord
  wordMeas : Measurable[filt 0] word
  xL : Ω → Fin nL → ℝ
  xR : Ω → Fin nR → ℝ
  xLMeas : Measurable[filt 0] xL
  xRMeas : Measurable[filt 0] xR
  xLNonpos : ∀ ω i, xL ω i ≤ 0
  xRNonneg : ∀ ω j, 0 ≤ xR ω j
  xLAnti : ∀ ω, Antitone (xL ω)
  xRMono : ∀ ω, Monotone (xR ω)
  typed : ∀ᵐ ω ∂P, IsFlowType κ θ (word ω) (xL ω) (xR ω) rhoL rhoR
  driver : ℝ≥0 → Ω → ℝ
  driverZero : ∀ ω, driver 0 ω = 0
  driverCont : ∀ ω, Continuous fun t => driver t ω
  driverAdapted : StronglyAdapted filt driver
  field : Ω → DistOn upperHalfPlaneOpens
  shiftedField : Ω → DistOn upperHalfPlaneOpens
  fieldMeas : Measurable field
  shiftedMeas : Measurable shiftedField
  shifted : ∀ ω, IsTranslateAddConst 0 (θ * QuantumZipper.chiC κ) (field ω) (shiftedField ω)
  integrable : ∀ φ : TestOn upperHalfPlaneOpens, Integrable (fun ω => shiftedField ω φ) P
  life : Ω → ℝ≥0∞
  lifeStop : ∀ t : ℝ≥0, MeasurableSet[filt t] {ω | life ω ≤ t}
  lifePos : ∀ᵐ ω ∂P, 0 < life ω
  lifeThreshold : ∀ᵐ ω ∂P, life ω ≤ thr rhoL rhoR driver xL xR ω
  announce : ℕ → Ω → ℝ≥0
  announcing : Coupling.IsAnnouncingSeq (usualAugmentation filt P) P life announce
  killedMeas : IsMeasurableKilledDriving driver (geomLW driver xL) (geomRW driver xR) life
  driveStops : ℕ → Ω → WithTop ℝ≥0
  driveStopping : ∀ n, IsStoppingTime (drivingFiltration P killedMeas) (driveStops n)
  driveMono : ∀ ω, Monotone fun n => driveStops n ω
  driveLt : ∀ᵐ ω ∂P, ∀ n, (driveStops n ω : ℝ≥0∞) < life ω
  driveLimit : ∀ᵐ ω ∂P, Tendsto (fun n => (driveStops n ω : ℝ≥0∞)) atTop (𝓝 (life ω))
  safeLaw : HasSafeLaw κ rhoL rhoR P filt univ life driver
    (geomLW driver xL) (geomRW driver xR) shiftedField
  safeMembers : HasSafeMembers P filt univ life driver shiftedField
  trace : Ω → ℝ≥0 → ℂ
  traceMeas : ∀ t, Measurable fun ω => trace ω t
  traceCont : ∀ ω, ContinuousOn (trace ω) {t | (t : ℝ≥0∞) ≤ life ω}
  generates : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => driver t ω) (life ω) (trace ω)

/-- A standard Borel probability model with all the typed stopped-K2 inputs. -/
structure StoppedTypeModel (κ θ : ℝ) where
  space : Type
  sigma : MeasurableSpace space
  borel : @StandardBorelSpace space sigma
  law : @Measure space sigma
  probability : @IsProbabilityMeasure space sigma law
  data : @StoppedTypeData space sigma law κ θ

instance StoppedTypeModel.measurableSpace {κ θ : ℝ} (M : StoppedTypeModel κ θ) :
    MeasurableSpace M.space := M.sigma

/-- The landed stopped K2 applies directly to the packaged model. -/
theorem StoppedTypeModel.ae_codeMatch {κ θ : ℝ} (M : StoppedTypeModel κ θ)
    (hext : StoppedHullExtendStatement.{0} κ) (h13 : Exist.Theorem13Statement.{0}) (hκ : 0 < κ)
    {Fc : (BoundaryWord × ℝ) × DistOn upperHalfPlaneOpens → (PCode × PCode) × ℝ≥0∞}
    (hFc : IsCanonicalFlowCode κ θ Fc) :
    ∀ᵐ ω ∂M.law, M.data.life ω ≤ (Fc ((M.data.word ω, 0), M.data.field ω)).2 ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ M.data.life ω →
        M.data.trace ω t = decPath (Fc ((M.data.word ω, 0), M.data.field ω)) t := by
  let _ := M.sigma
  let _ := M.borel
  let _ := M.probability
  exact StoppedK2.ae_stoppedCodeMatch_of_hasSafeLaw hext h13 hκ hFc le_rfl
    M.data.wordMeas M.data.xLMeas M.data.xRMeas M.data.xLNonpos M.data.xRNonneg
    M.data.xLAnti M.data.xRMono M.data.typed M.data.driverZero M.data.driverCont
    M.data.driverAdapted M.data.fieldMeas M.data.shiftedMeas M.data.shifted M.data.integrable
    M.data.lifeStop M.data.lifePos M.data.lifeThreshold M.data.announcing M.data.killedMeas
    M.data.driveStopping M.data.driveMono M.data.driveLt M.data.driveLimit
    M.data.safeLaw M.data.safeMembers M.data.traceMeas M.data.traceCont M.data.generates

universe v

variable {Ω : Type v} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- Concrete law-transport input for a type event. This asks for a model and
coordinate agreement, never for a canonical-code match. `mapLaw` uses a
measurable map, so it is an actual law rather than the nonmeasurable-map fallback. -/
structure StoppedModelTransfer (κ θ : ℝ) (P : Measure Ω) (F : Set Ω)
    (c : Ω → BoundaryWord) (Hc : Ω → DistOn upperHalfPlaneOpens)
    (V : Ω → ℝ≥0∞) (γ : Ω → ℝ≥0 → ℂ) where
  model : StoppedTypeModel κ θ
  read : Ω → model.space
  readMeas : @Measurable Ω model.space mΩ model.sigma read
  mapLaw : (P[|F]).map read = model.law
  agrees : ∀ᵐ ω ∂P, ω ∈ F →
    model.data.word (read ω) = c ω ∧ model.data.field (read ω) = Hc ω ∧
      model.data.life (read ω) = V ω ∧
        ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ V ω → model.data.trace (read ω) t = γ ω t

/-- Pull the stopped-K2 match back from the conditional law of a type event. -/
theorem ae_codeMatch_of_stoppedModelTransfer [IsProbabilityMeasure P]
    {κ θ : ℝ} {F : Set Ω} {c : Ω → BoundaryWord}
    {Hc : Ω → DistOn upperHalfPlaneOpens} {V : Ω → ℝ≥0∞} {γ : Ω → ℝ≥0 → ℂ}
    (T : StoppedModelTransfer κ θ P F c Hc V γ) (hF : MeasurableSet F)
    (hext : StoppedHullExtendStatement.{0} κ) (h13 : Exist.Theorem13Statement.{0}) (hκ : 0 < κ)
    {Fc : (BoundaryWord × ℝ) × DistOn upperHalfPlaneOpens → (PCode × PCode) × ℝ≥0∞}
    (hFc : IsCanonicalFlowCode κ θ Fc) :
    ∀ᵐ ω ∂P, ω ∈ F → V ω ≤ (Fc ((c ω, 0), Hc ω)).2 ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ V ω → γ ω t = decPath (Fc ((c ω, 0), Hc ω)) t := by
  have hm := T.model.ae_codeMatch hext h13 hκ hFc
  have hm' : ∀ᵐ ω ∂(P[|F]).map T.read,
      T.model.data.life ω ≤ (Fc ((T.model.data.word ω, 0), T.model.data.field ω)).2 ∧
        ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ T.model.data.life ω →
          T.model.data.trace ω t = decPath (Fc ((T.model.data.word ω, 0), T.model.data.field ω)) t :=
    (congrArg (fun μ : Measure T.model.space => ae μ) T.mapLaw).symm ▸ hm
  have hp := FCDet.ae_imp_of_ae_cond hF (ae_of_ae_map T.readMeas.aemeasurable hm')
  filter_upwards [hp, T.agrees] with ω hω he hωF
  obtain ⟨ec, eH, eV, eγ⟩ := he hωF
  obtain ⟨hV, hγ⟩ := hω hωF
  rw [ec, eH, eV] at hV hγ
  exact ⟨hV, fun t ht => (eγ t ht).symm.trans (hγ t ht)⟩

/-- Finitely many conditional models suffice. Null type events need no model. -/
theorem ae_codeMatch_of_finite_stoppedModels [IsProbabilityMeasure P]
    {κ θ : ℝ} {c : Ω → BoundaryWord} {Hc : Ω → DistOn upperHalfPlaneOpens}
    {V : Ω → ℝ≥0∞} {γ : Ω → ℝ≥0 → ℂ} {F : Set Ω} {n : ℕ} {M : Fin n → Set Ω}
    (hM : ∀ i, MeasurableSet (M i))
    (hcover : ∀ᵐ ω ∂P, ω ∈ F → ∃ i, ω ∈ M i)
    (hmodels : ∀ i, P (M i) ≠ 0 → Nonempty (StoppedModelTransfer κ θ P (M i) c Hc V γ))
    (hext : StoppedHullExtendStatement.{0} κ) (h13 : Exist.Theorem13Statement.{0}) (hκ : 0 < κ)
    {Fc : (BoundaryWord × ℝ) × DistOn upperHalfPlaneOpens → (PCode × PCode) × ℝ≥0∞}
    (hFc : IsCanonicalFlowCode κ θ Fc) :
    ∀ᵐ ω ∂P, ω ∈ F → V ω ≤ (Fc ((c ω, 0), Hc ω)).2 ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ V ω → γ ω t = decPath (Fc ((c ω, 0), Hc ω)) t := by
  have hi : ∀ i : Fin n, ∀ᵐ ω ∂P, ω ∈ M i → V ω ≤ (Fc ((c ω, 0), Hc ω)).2 ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ V ω → γ ω t = decPath (Fc ((c ω, 0), Hc ω)) t := by
    intro i
    by_cases hz : P (M i) = 0
    · filter_upwards [measure_eq_zero_iff_ae_notMem.1 hz] with ω hω hωM
      exact (hω hωM).elim
    · obtain ⟨T⟩ := hmodels i hz
      exact ae_codeMatch_of_stoppedModelTransfer T (hM i) hext h13 hκ hFc
  filter_upwards [ae_all_iff.2 hi, hcover] with ω hω hc hωF
  obtain ⟨i, hi⟩ := hc hωF
  exact hω i hi

/-- Remaining model-construction mathematics for the retained continuation.
The output contains only stopped-K2 inputs and coordinate law transport; it
contains no canonical code and no determination conclusion. It must handle
the given mean-identifying word `β`, not just a preferred explicit word. -/
def RetStoppedModelsStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ),
    IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ < x₁ → θ₁ < θ₂ + Real.pi →
    ∀ {Ω : Type v} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
    ∀ (d : RetData Ω) (hd : d.IsMeasGood),
      (∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
        (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t) →
    ∀ u₀ : ℂ → ℝ, IsBoundedHarmonicExtension b jumps u₀ →
    ∀ β : Ω → BoundaryWord, Measurable[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r] β →
      Sec7.Lemma76F.IsRetMeanIdent κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd β →
      (∀ᵐ ω ∂P, Sec7.Lemma76Exit.IsDisjointPair
        (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r → (β ω).IsSorted) →
    ∃ (n : ℕ) (M : Fin n → Set Ω), (∀ i, MeasurableSet (M i)) ∧
      Pairwise (fun i j => Disjoint (M i) (M j)) ∧
      (∀ᵐ ω ∂P, Sec7.Lemma76Exit.IsDisjointPair
        (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r → ∃ i, ω ∈ M i) ∧
      ∀ i, P (M i) ≠ 0 → Nonempty (StoppedModelTransfer κ θ₂ P (M i) β (hd.chartField κ h)
        (fun ω => canonRetLife (d.D ω) (d.fwd ω) (η₂ ω) (ζ₂ ω) d.r
          (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r ∪ realLine) 0)
        (fun ω => canonRetPath (d.D ω) (d.fwd ω) (η₂ ω) (ζ₂ ω) d.r
          (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r ∪ realLine) 0))

/-- Source-faithful retained determination, conditional on the explicitly named
model-construction input. The target statement and its hypotheses are unchanged. -/
theorem lemma76DetRStatement_of_stoppedModels
    (hext : ∀ κ : ℝ, 0 < κ → κ < 4 → StoppedHullExtendStatement.{0} κ)
    (h13 : Exist.Theorem13Statement.{0}) (hmodels : RetStoppedModelsStatement.{v}) :
    Sec7.Lemma76DetRStatement.{v} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω mΩ P _ h hh
    η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hag Fc hFc u₀ hu₀ β hβ hmean hsort
  obtain ⟨n, M, hM, -, hcover, hmodel⟩ := hmodels κ hκ hκ4 b jumps hb
    x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hag u₀ hu₀ β hβ hmean hsort
  exact ae_codeMatch_of_finite_stoppedModels hM hcover hmodel (hext κ hκ hκ4) h13 hκ hFc

end InteractingSLE.Restart.RetAux79
