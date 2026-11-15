/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossRestartMeasPathChart
import InteractingSLE.Spec.Restart.ChartMeasFlow

/-!
# Measurable versions of the restart data and a measurable restart variable

Packet PROVE-SEC5-I, layer (iv) of the counterflow restart (PROVE-SEC5-H, "What remains" 2).

**Why SEC5-H's measurability inputs are corrected here.** `RestartPathMeasurableStatement` and
`RestartVarMeasurableStatement` ask for versions `η₀`, `γ₀` with `η₀ ω = η ω` and `γ₀ ω = γ′ ω` *as functions*,
almost surely, measurable at every fixed time. The frozen `IsFlowLine` constrains `η ω` only on `[0, ζ ω]` (a.s.
`IsGeneratingTrace`), and the flow lines of §5 with `|θ| ≤ π/2` stop at `z₀` in finite capacity time; after `ζ` the
path `η` is arbitrary, possibly non-measurable, and the restart variable reads `η` on `[0, σ]` also when `ζ < σ`. So
those two statements are not provable for arbitrary `η` (only the honest form below is). Here:

* `exists_measurable_version_of_isStripCounterflowDriver`: a measurable version of the counterflow trace on its
  closed available interval (Proposition LP11's reconstruction `LP.drivingTrace`);
* **`exists_measurable_restartVar`**: versions `w` of the flow-line driver, `η₀` of the flow-line trace (equal to `η`
  before `ζ`), `γ₀` of the counterflow trace (equal to `γ′` on `[0, ζ′]`) and `ζ₀ = ζ′` such that the explicit restart
  variable `restartVar q w ζ η₀ σ ζ₀ γ₀` is **measurable**. Proof: the versions are chosen so that off the good event
  (and when `ζ ≤ σ`) the flow-line version passes through the counterflow start, which forces `lawExit = 0`; on the
  good event the restart variable is that of the measurable surrogate chart path (`surrPath_eq_restartPath`);
* `CounterflowRestartKernelOnStatement` (named input: SEC5-H's kernel statement for versions that agree with the
  traces before their lifetimes), `counterflowRestartKernelStatement_of_kernelOn`, and
  **`counterflowSegmentRestartStatement_of_kernelOn`**: SEC5-E's carrier from Zhan's Part A inputs at `16/κ` and the
  corrected kernel statement **alone** (the measurability layer is now proved).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory ProbabilityTheory
open scoped Real NNReal ENNReal

open QuantumZipper (H fwdHull extIccPath)

universe u

namespace InteractingSLE

namespace Sec5

namespace CrossRestart

open ConformalImage ConformalImageFull Sec4 Restart MarkovOther Sec2.Assembly

/-! ### Generating traces read the driver only before the horizon -/

/-- A generating trace only sees the driver before its horizon (local copy of `Sec7.IsGeneratingTrace.congr_lt`, to
avoid importing §7). -/
theorem isGeneratingTrace_congr_drive {w w' : ℝ≥0 → ℝ} {T : ℝ≥0∞} {η : ℝ≥0 → ℂ}
    (h : IsGeneratingTrace w' T η) (hww' : ∀ t : ℝ≥0, (t : ℝ≥0∞) < T → w t = w' t) :
    IsGeneratingTrace w T η := by
  refine ⟨h.1, h.2.1, fun t ht => ?_⟩
  obtain ⟨t₂, htt₂, ht₂T⟩ := exists_real_btwn_of_lt ht
  have heq : ∀ r ∈ Icc (0 : ℝ) t₂, w r.toNNReal = w' r.toNNReal := fun r hr =>
    hww' _ ((ENNReal.ofReal_le_ofReal hr.2).trans_lt ht₂T)
  rw [fwdHull_eq_of_eqOn (W' := fun s : ℝ => w' s.toNNReal) (NNReal.coe_nonneg t) htt₂ heq]
  exact h.2.2 t ht

/-! ### A flow-line trace through the counterflow start forces `lawExit = 0` -/

theorem lawExit_eq_zero_of_eq_start {q : ℝ} {η : ℝ≥0 → ℂ} {σ : ℝ≥0} {ζ' : ℝ≥0∞} {γ : ℝ≥0 → ℂ}
    (h : η σ = ((-1 - q : ℝ) : ℂ)) : lawExit q η σ ζ' γ = 0 := by
  refine le_antisymm (iSup₂_le fun r hr => ?_) bot_le
  exfalso
  obtain ⟨-, h0, -, m, h2⟩ := hr
  have := h2 σ (mem_ratGrid_self σ) 0 (zero_mem_ratGrid _)
  rw [h0, mob_zero (q := q), h, sub_self, norm_zero] at this
  have hpos : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
  linarith

/-! ### A measurable version of the counterflow trace -/

section Versions

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **A measurable version of the strip counterflow trace** on its closed available interval, and the measurability
of its lifetime. -/
theorem exists_measurable_version_of_isStripCounterflowDriver {κ α q : ℝ}
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hcf : IsStripCounterflowDriver κ α q P h W' ζ') {γ' : Ω → ℝ≥0 → ℂ}
    (htr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) (ζ' ω) (γ' ω)) :
    Measurable ζ' ∧ ∃ γ'' : Ω → ℝ≥0 → ℂ, (∀ t, Measurable fun ω => γ'' ω t) ∧
      ∀ᵐ ω ∂P, ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ' ω → γ'' ω s = γ' ω s := by
  classical
  obtain ⟨_, _, _, _, _, _, 𝓕, VL, VR, B, _, hcpl⟩ := hcf
  have hW := hcpl.1.2.1
  have hζ := measurable_of_adaptedBefore hW
  refine ⟨hζ, ?_⟩
  set W'' : ℝ≥0 → Ω → ℝ := fun t ω => if (t : ℝ≥0∞) < ζ' ω then W' t ω else 0 with hW''
  have hW''m : ∀ t, Measurable (W'' t) := fun t => measurable_ite_of_adaptedBefore hW t
  have hpm : Measurable fun ω => (ζ' ω, fun s => W'' s ω) :=
    hζ.prodMk (measurable_pi_iff.2 fun s => hW''m s)
  refine ⟨fun ω t => (LP.drivingTrace (ζ' ω, fun s => W'' s ω)).2 t, fun t => ?_, ?_⟩
  · exact (measurable_pi_apply t).comp (measurable_snd.comp (LP.measurable_drivingTrace.comp hpm))
  · filter_upwards [htr, hcpl.1.2.2.2.2] with ω hω hpath s hs
    obtain ⟨hw0, -, -, hcw, -⟩ := hpath
    have he := LP.drivingTrace_eq hω hcw hw0 (w' := fun s => W'' s ω) fun r hr => by
      simp only [hW'', hr, ↓reduceIte]
    rw [he]
    simp only [min_eq_left hs, ENNReal.toNNReal_coe]

end Versions

/-! ### The measurable restart variable -/

section Main

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **A measurable explicit restart variable.** For the angle-`θ` flow line `η` of a strip field (lifetime `ζ`), a
strip counterflow `(W′, ζ′)` with a.s. generating trace `γ′`, any `q > 0` and any time `σ`, there are versions `w` of
the flow-line driver, `η₀` of the flow-line trace (equal to `η` before `ζ`), `γ₀` of the counterflow trace (equal to
`γ′` on `[0, ζ′]`) and `ζ₀ = ζ′` for which the explicit restart variable is measurable. -/
theorem exists_measurable_restartVar {κ α θ κc αc q : ℝ} (hq : 0 < q) {bL bU : ℝ → ℝ} {JL JU : Finset ℝ}
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (hη : IsStripFlowLineAt κ α θ bL bU JL JU P h η ζ) {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hcf : IsStripCounterflowDriver κc αc q P h W' ζ') {γ' : Ω → ℝ≥0 → ℂ}
    (htr' : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) (ζ' ω) (γ' ω)) (σ : ℝ≥0) :
    ∃ (w : ℝ≥0 → Ω → ℝ) (η₀ γ₀ : Ω → ℝ≥0 → ℂ) (ζ₀ : Ω → ℝ≥0∞),
      (∀ᵐ ω ∂P, IsGeneratingTrace (fun t => w t ω) (ζ ω) (η ω) ∧
        ContinuousOn (fun t => w t ω) {t | (t : ℝ≥0∞) < ζ ω} ∧ w 0 ω = 0 ∧
        (∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → η₀ ω t = η ω t) ∧
        (∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ' ω → γ₀ ω t = γ' ω t) ∧ ζ₀ ω = ζ' ω) ∧
      Measurable (fun ω => restartVar q (fun t => w t ω) (ζ ω) (η₀ ω) σ (ζ₀ ω) (γ₀ ω)) := by
  classical
  have hηF : IsFlowLine κ (stripHData κ bL bU) (stripHJumps JL JU) 0 (α + θ) P h η ζ := hη
  obtain ⟨η', hη'm, hη'ae⟩ := exists_measurable_version_of_isFlowLine hηF
  obtain ⟨hζ'm, γ'', hγ''m, hγ''ae⟩ := exists_measurable_version_of_isStripCounterflowDriver hcf htr'
  obtain ⟨_, 𝓕, W, _, _, _, -, hcoup, htr⟩ := hηF
  have hWa : AdaptedBefore 𝓕 ζ W := hcoup.1.2.1
  have hζm : Measurable ζ := measurable_of_adaptedBefore hWa
  -- the good event
  set good : Ω → Prop := fun ω => IsGeneratingTrace (fun t => W t ω) (ζ ω) (η ω) ∧
    ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} ∧ W 0 ω = 0 ∧
    (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ ω → η' ω s = η ω s) ∧ IsGeneratingTrace (fun t => W' t ω) (ζ' ω) (γ' ω) ∧
    (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ' ω → γ'' ω s = γ' ω s) with hgooddef
  have hgood : ∀ᵐ ω ∂P, good ω := by
    filter_upwards [htr, hcoup.1.2.2.2.2, hη'ae, htr', hγ''ae] with ω h1 hp h3 h4 h5
    exact ⟨by simpa only [Complex.ofReal_zero, sub_zero] using h1, hp.2.2.2.1, hp.1, h3, h4, h5⟩
  set G : Set Ω := (toMeasurable P {ω | ¬ good ω})ᶜ with hGdef
  have hGm : MeasurableSet G := (measurableSet_toMeasurable _ _).compl
  have hGsub : ∀ ω ∈ G, good ω := fun ω hω => by
    by_contra hn
    exact hω (subset_toMeasurable _ _ hn)
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by
    rw [ae_iff]
    have h0 : P {ω | ¬ good ω} = 0 := ae_iff.1 hgood
    simpa only [hGdef, mem_compl_iff, not_not, ofPred_mem_eq, measure_toMeasurable] using h0
  have hGc : ∀ ω ∈ G, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} := fun ω hω => (hGsub ω hω).2.1
  -- the versions
  set y : ℂ := ((-1 - q : ℝ) : ℂ) with hy
  set w : ℝ≥0 → Ω → ℝ := fun t ω => if ω ∈ G ∧ (t : ℝ≥0∞) < ζ ω then W t ω else 0 with hwdef
  set η₀ : Ω → ℝ≥0 → ℂ := fun ω t => if ω ∈ G ∧ (t : ℝ≥0∞) < ζ ω then η' ω t else y with hη₀def
  have hwW : ∀ ω ∈ G, ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → w t ω = W t ω := fun ω hω t ht => by
    simp only [hwdef, hω, ht, and_self, ↓reduceIte]
  have hw0 : ∀ ω ∈ G, w 0 ω = 0 := fun ω hω => by
    by_cases h0 : ((0 : ℝ≥0) : ℝ≥0∞) < ζ ω
    · rw [hwW ω hω 0 h0]; exact (hGsub ω hω).2.2.1
    · simp only [hwdef, h0, and_false, ↓reduceIte]
  have hwc : ∀ ω ∈ G, ContinuousOn (fun t => w t ω) {t | (t : ℝ≥0∞) < ζ ω} := fun ω hω =>
    (hGc ω hω).congr fun t ht => hwW ω hω t ht
  have hwtr : ∀ ω ∈ G, IsGeneratingTrace (fun t => w t ω) (ζ ω) (η ω) := fun ω hω =>
    isGeneratingTrace_congr_drive (hGsub ω hω).1 fun t ht => hwW ω hω t ht
  have hη₀η : ∀ ω ∈ G, ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → η₀ ω t = η ω t := fun ω hω t ht => by
    simp only [hη₀def, hω, ht, and_self, ↓reduceIte]
    exact (hGsub ω hω).2.2.2.1 t ht.le
  refine ⟨w, η₀, γ'', ζ', ?_, ?_⟩
  · filter_upwards [hGae] with ω hω
    exact ⟨hwtr ω hω, hwc ω hω, hw0 ω hω, hη₀η ω hω, (hGsub ω hω).2.2.2.2.2, rfl⟩
  -- measurability
  have hη₀m : ∀ t, Measurable fun ω => η₀ ω t := fun t => by
    have hS : MeasurableSet {ω | ω ∈ G ∧ (t : ℝ≥0∞) < ζ ω} :=
      hGm.inter (measurableSet_lt measurable_const hζm)
    exact Measurable.ite hS (hη'm t) measurable_const
  let 𝓖 : Filtration ℝ≥0 mΩ := Filtration.const ℝ≥0 mΩ le_rfl
  have hW𝓖 : AdaptedBefore 𝓖 ζ W := Ito.adaptedBefore_mono (fun t => 𝓕.le t) hWa
  let _ : MeasurableSpace C(Icc (0 : ℝ) σ, ℝ) := borel _
  have _ : BorelSpace C(Icc (0 : ℝ) σ, ℝ) := ⟨rfl⟩
  set g : Ω → C(Icc (0 : ℝ) σ, ℝ) := Ito.drvPathMap W ζ G hGc σ with hgdef
  have hgm : Measurable g := Ito.measurable_drvPathMap hW𝓖 hGc hGm σ
  -- the restart variable is that of the surrogate chart path
  have hEm : Measurable fun ω => lawExit q (η₀ ω) σ (ζ' ω) (γ'' ω) := measurable_lawExit hη₀m hγ''m hζ'm
  have hsurr : ∀ ω, ∀ t : ℝ≥0, (t : ℝ≥0∞) < lawExit q (η₀ ω) σ (ζ' ω) (γ'' ω) ∨ t = 0 →
      surrPath q σ (g ω) (γ'' ω) t =
        restartPath q (segDrive (fun t => w t ω) (ζ ω) σ) σ (segStart q (fun t => w t ω) (ζ ω) σ) (γ'' ω) t := by
    intro ω t ht
    refine surrPath_eq_restartPath hq (fun hpos => ?_) t ht.symm
    have hGσ : ω ∈ G ∧ (σ : ℝ≥0∞) < ζ ω := by
      by_contra hn
      have hσy : η₀ ω σ = y := by simp only [hη₀def, hn, ↓reduceIte]
      rw [lawExit_eq_zero_of_eq_start hσy] at hpos
      exact lt_irrefl _ hpos
    obtain ⟨hω, hσζ⟩ := hGσ
    obtain ⟨-, -, -, -, hγtr, hγeq⟩ := hGsub ω hω
    have hηtr := hwtr ω hω
    have hle : ∀ t : ℝ≥0, t ≤ σ → (t : ℝ≥0∞) < ζ ω := fun t ht =>
      lt_of_le_of_lt (ENNReal.coe_le_coe.2 ht) hσζ
    have hηeq : EqOn (η₀ ω) (η ω) (Icc 0 σ) := fun t ht => hη₀η ω hω t (hle t ht.2)
    refine ⟨hσζ, hwc ω hω, hw0 ω hω, ?_, ?_, ?_, fun r hr => ?_⟩
    · exact (hηtr.2.1.mono fun t ht => (hle t ht.2).le).congr hηeq
    · rw [image_congr hηeq]
      exact hηtr.2.2 σ hσζ
    · exact hγtr.2.1.congr fun t ht => hγeq t ht
    · rw [QuantumZipper.extIccPath_of_mem σ.coe_nonneg _ hr, hgdef, Ito.drvPathMap_apply hGc ⟨hω, hσζ⟩]
      have hr' : (r.toNNReal : ℝ≥0∞) < ζ ω := hle _ (Real.toNNReal_le_iff_le_coe.2 hr.2)
      exact (hwW ω hω _ hr').symm
  have heq : (fun ω => restartVar q (fun t => w t ω) (ζ ω) (η₀ ω) σ (ζ' ω) (γ'' ω)) = fun ω =>
      encPath (pathLaw (surrPath q σ (g ω) (γ'' ω)) (lawExit q (η₀ ω) σ (ζ' ω) (γ'' ω)))
        (pathLife (surrPath q σ (g ω) (γ'' ω)) (lawExit q (η₀ ω) σ (ζ' ω) (γ'' ω))) := by
    funext ω
    rw [restartVar_eq_encPath]
    have hlt := fun t ht => (hsurr ω t (Or.inl ht)).symm
    rw [pathLaw_congr hlt (hsurr ω 0 (Or.inr rfl)).symm, pathLife_congr hlt]
  rw [heq]
  exact measurable_encPath_pathLaw (fun t => measurable_surrPath q hgm hγ''m t) hEm

end Main

/-! ### SEC5-H's kernel statement for versions that agree before the lifetimes -/

/-- **Named input: the conditional law of the explicit restart variable**, for versions that agree with the traces
before their lifetimes (the corrected form of `CounterflowRestartKernelStatement`, whose versions must equal the
traces as functions). Setting and binders of `Sec5.CounterflowSegmentRestartStatement`. For every time `σ`, every
version `w` of the flow-line driver, every version `η₀` of the flow-line trace that equals it before its lifetime,
every version `γ₀` of the counterflow trace that equals it on its closed available interval, and `ζ₀ = ζ′` a.s., for
which the explicit restart variable is measurable: a measurable event `M` (containing almost every sample where
`σ < ζ` and `η((0, σ]) ⊆ ℍ`), a measurable chart datum `β` and a Markov kernel `K`, the conditional law of the restart
variable given `β` on `M`, such that for almost every datum `d`: `d` has the Figure 5.5 data, and under `K d` the
decoded chart path with its lifetime coordinate has the flow-line trace law for `κ′ = 16/κ` and the word `d.2`. -/
def CounterflowRestartKernelOnStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ α x₀ a b a' b' θ : ℝ, IsFig51Bounds κ a b a' b' →
    -(π / 2) ≤ θ → θ ≤ π / 2 →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens) (hhm : Measurable h),
      IsFig51Field κ α x₀ a b a' b' P h →
    ∀ (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞),
      IsStripFlowLineAt κ α θ (fig51LowerFrame κ α a b) (fig51UpperFrame κ α x₀ a' b') {0} {x₀} P h η ζ →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞) (γ' : Ω → ℝ≥0 → ℂ),
      IsStripCounterflowDriver κ α (Real.exp (π * x₀)) P h W' ζ' →
      (∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) (ζ' ω) (γ' ω)) →
      CondIndep (MeasurableSpace.comap h inferInstance)
        (⨆ t : ℝ≥0, MeasurableSpace.comap (fun ω => η ω t) inferInstance)
        (⨆ t : ℝ≥0, MeasurableSpace.comap (W' t) inferInstance) hhm.comap_le P →
    ∀ (σ : ℝ≥0) (w : ℝ≥0 → Ω → ℝ) (η₀ γ₀ : Ω → ℝ≥0 → ℂ) (ζ₀ : Ω → ℝ≥0∞),
      (∀ᵐ ω ∂P, IsGeneratingTrace (fun t => w t ω) (ζ ω) (η ω) ∧
        ContinuousOn (fun t => w t ω) {t | (t : ℝ≥0∞) < ζ ω} ∧ w 0 ω = 0 ∧
        (∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → η₀ ω t = η ω t) ∧
        (∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ' ω → γ₀ ω t = γ' ω t) ∧ ζ₀ ω = ζ' ω) →
      Measurable (fun ω => restartVar (Real.exp (π * x₀)) (fun t => w t ω) (ζ ω) (η₀ ω) σ (ζ₀ ω) (γ₀ ω)) →
    ∃ (M : Set Ω) (β : Ω → ℝ × BoundaryWord) (K : Kernel (ℝ × BoundaryWord) ((PCode × PCode) × ℝ≥0∞)),
      MeasurableSet M ∧ Measurable β ∧ IsMarkovKernel K ∧
      (P.restrict M).map (fun ω => (β ω,
          restartVar (Real.exp (π * x₀)) (fun t => w t ω) (ζ ω) (η₀ ω) σ (ζ₀ ω) (γ₀ ω))) =
        (P.restrict M).map β ⊗ₘ K ∧
      (∀ᵐ d ∂(P.restrict M).map β, IsFig55RestartDatum κ α θ a b a' b' d ∧
        IsFlowLineTraceLaw (16 / κ) d.2 (K d) decPath (fun s => s.2)) ∧
      ∀ᵐ ω ∂P, (σ : ℝ≥0∞) < ζ ω → (∀ t : ℝ≥0, 0 < t → t ≤ σ → η ω t ∈ H) → ω ∈ M

/-- The corrected kernel statement implies SEC5-H's (whose versions are a special case). -/
theorem counterflowRestartKernelStatement_of_kernelOn (hK : CounterflowRestartKernelOnStatement.{u}) :
    CounterflowRestartKernelStatement.{u} := by
  intro κ hκ hκ4 α x₀ a b a' b' θ hbd hθ₁ hθ₂ Ω _ _ P _ h hhm hh η ζ hη W' ζ' γ' hcf htr' hci σ w η₀ γ₀ ζ₀
    hver hXm
  refine hK κ hκ hκ4 α x₀ a b a' b' θ hbd hθ₁ hθ₂ P h hhm hh η ζ hη W' ζ' γ' hcf htr' hci σ w η₀ γ₀ ζ₀ ?_ hXm
  filter_upwards [hver] with ω ⟨h1, h2, h3, h4, h5, h6⟩
  exact ⟨h1, h2, h3, fun t _ => by rw [h4], fun t _ => by rw [h5], h6⟩

/-- **SEC5-E's counterflow restart carrier from Zhan's Part A inputs at `16/κ` and the corrected kernel statement
alone**: the measurability of the restart variable (layer (iv)) is `exists_measurable_restartVar`, its
identification with the counterflow is `isCounterflowChartContinuation_restartVar`, and Lemma 4.5 under the kernel
makes its lifetime coordinate almost surely infinite (as in `counterflowSegmentRestartStatement_of_kernel`). -/
theorem counterflowSegmentRestartStatement_of_kernelOn (hA : PartAInputsSixteenDiv)
    (hK : CounterflowRestartKernelOnStatement.{u}) : CounterflowSegmentRestartStatement.{u} := by
  intro κ hκ hκ4 α x₀ a b a' b' θ hbd hθ₁ hθ₂ Ω _ _ P _ h hhm hh η ζ hη W' ζ' γ' hcf htr' hci σ
  obtain ⟨w, η₀, γ₀, ζ₀, hver, hXm⟩ :=
    exists_measurable_restartVar (Real.exp_pos (π * x₀)) hη hcf htr' σ
  obtain ⟨M, β, K, hM, hβ, hKm, hlaw, hdat, hMev⟩ :=
    hK κ hκ hκ4 α x₀ a b a' b' θ hbd hθ₁ hθ₂ P h hhm hh η ζ hη W' ζ' γ' hcf htr' hci σ w η₀ γ₀ ζ₀ hver hXm
  set X := fun ω => restartVar (Real.exp (π * x₀)) (fun t => w t ω) (ζ ω) (η₀ ω) σ (ζ₀ ω) (γ₀ ω) with hXdef
  have hγm : ∀ t, Measurable fun s : (PCode × PCode) × ℝ≥0∞ => decPath s t := measurable_decPath
  have hUm : Measurable fun s : (PCode × PCode) × ℝ≥0∞ => s.2 := measurable_snd
  have hγc : ∀ s : (PCode × PCode) × ℝ≥0∞, ContinuousOn (decPath s) {u | (u : ℝ≥0∞) ≤ s.2} :=
    continuousOn_decPath
  refine ⟨(PCode × PCode) × ℝ≥0∞, inferInstance, decPath, fun s => s.2, M, β, X, K, hγm, hUm, hγc, hM, hβ,
    hXm, hKm, hlaw, hdat, ?_⟩
  have hκ' : 0 < 16 / κ := by positivity
  have h7 : Aux7Statement.{0} (16 / κ) := aux7Statement_sixteen_div_of_partA hA hκ hκ4
  -- Lemma 4.5 under the kernel, integrated back (as in `counterflowSegmentRestartStatement_of_kernel`)
  have hr : ∀ r : ℚ, ∀ᵐ ω ∂P, ω ∈ M → (β ω).1 < r → X ω ∈ restartEvent decPath (fun s => s.2) r := by
    intro r
    set E : Set ((ℝ × BoundaryWord) × ((PCode × PCode) × ℝ≥0∞)) :=
      {p | (r : ℝ) ≤ p.1.1} ∪ univ ×ˢ restartEvent decPath (fun s => s.2) r
    have hE : MeasurableSet E :=
      (measurableSet_le measurable_const (measurable_fst.comp measurable_fst)).union
        (MeasurableSet.univ.prod (measurableSet_restartEvent hγm hUm hγc r))
    have hKE : ∀ᵐ d ∂(P.restrict M).map β, ∀ᵐ s ∂(K d), (d, s) ∈ E := by
      filter_upwards [hdat] with d ⟨hd, hfl⟩
      have hd' := isRestartTargetDatum_of_isFig55RestartDatum hκ hκ4 hbd hθ₁ hθ₂ hd
      by_cases hdr : (r : ℝ) ≤ d.1
      · exact Eventually.of_forall fun s => Or.inl hdr
      · push Not at hdr
        filter_upwards [ae_restartEvent_of_isFlowLineTraceLaw hκ' h7 hd' hfl] with s hs
        obtain ⟨hU, hav, him, htr⟩ := hs
        refine Or.inr ⟨mem_univ _, hU, fun t ht => hav t ?_, him, htr⟩
        obtain ⟨x, hx, hxt⟩ := ht
        refine ⟨x, ?_, hxt⟩
        rcases hx with hx | hx
        · exact Or.inl hx
        · exact Or.inr (show d.1 ≤ x from hdr.le.trans hx)
    filter_upwards [ae_mem_of_compProd_eq_prod hM hβ hXm hlaw hE hKE] with ω hω hωM hlt
    rcases hω hωM with h | ⟨-, h⟩
    · exact absurd h (not_le.2 hlt)
    · exact h
  rw [← ae_all_iff] at hr
  filter_upwards [hr, hver, htr', ae_continuousOn_of_isStripCounterflowDriver hcf, hMev]
    with ω hrω ⟨hwη, hwc, hw0, hη₀, hγ₀, hζ₀⟩ htrω hcfω hMω hσζ hηH
  have hωM := hMω hσζ hηH
  refine ⟨hωM, ?_⟩
  obtain ⟨r₀, hr₀⟩ := exists_rat_gt (β ω).1
  obtain ⟨hUX, -, -, -⟩ := hrω r₀ hωM hr₀
  have hXω : X ω = restartVar (Real.exp (π * x₀)) (fun t => w t ω) (ζ ω) (η ω) σ (ζ' ω) (γ' ω) := by
    rw [hXdef]
    simp only
    rw [hζ₀]
    exact restartVar_congr (fun t ht => hη₀ t (lt_of_le_of_lt (ENNReal.coe_le_coe.2 ht) hσζ))
      fun t ht => hγ₀ t ht.le
  rw [hXω] at hUX ⊢
  exact isCounterflowChartContinuation_restartVar (Real.exp_pos _) hwη hwc hw0 hσζ hηH htrω hcfω.1 hcfω.2 hUX

end CrossRestart

end Sec5

end InteractingSLE
