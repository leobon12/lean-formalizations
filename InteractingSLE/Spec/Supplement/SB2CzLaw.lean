/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2CzMix
import InteractingSLE.Spec.Supplement.SB2FlTail
import InteractingSLE.Spec.Supplement.KernelTower2
import InteractingSLE.Spec.Supplement.SB2QxRec

/-!
# The stage law of `Mz.TailCanonAt` from the retained law of the induction

Packet PROVE-SB2-CANON. The retained-law induction of SB2(2) (F3LAW's `Fl.mvLaw_succ_succ` from the base
`Qu`/`Fm` laws) carries, at B's stage `ℓ`, the law `Fl.MvLaw` given finer marks `𝓜` (the completed line σ-algebra of
the stage), for some retained hull `K'` read in the chart of offset `0`, with a word `β` that is measurable for the
completed retained past. `Mz.TailCanonAt` asks instead for the law given the coarser retained past
`𝒮 = Ms.stageMarks ℓ`,
for a hull `K` and an offset `x₀` that are `𝒮`-measurable, with an `𝒮`-measurable word.

**`exists_stageLaw_of_mvLaw`**: on an `𝒮`-event `G` inside the law's event where `fill K = fill K'`, there is an
`𝒮`-measurable word `c`, equal to `shiftW x₀ β` almost surely on `G`, such that given `𝒮` the field read in
`Mo.hullChart (fill K) x₀` is almost surely on `G` the GFF of the data of `c`. Steps: move the field to the chart of
`K` (`Fl.ae_isGFF_congr_on`), move the chart's offset (`Mu.ae_isGFF_hullChart_shift`), take an `𝒮`-measurable
version of the word (`Qx.exists_measurable_ae_eq_of_kernel_const`), and pass to the coarser marks
(`ae_isGFF_of_le_fine`).

R48: no source theorem is used.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (DistOn)

namespace InteractingSLE.Theorem14.SB.Cz

open Restart Exist Exist.StagedLaw LocalSets

variable {Ω : Type*} {𝒮 𝓜 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]

/-- Kernel constancy, given `𝒮`, of a map measurable for the completed `𝒮`. -/
theorem ae_ae_eq_of_measurable_aeSigma (h𝒮 : 𝒮 ≤ mΩ) {E : Type*} [TopologicalSpace E] [SecondCountableTopology E]
    [T1Space E] [MeasurableSpace E] [OpensMeasurableSpace E] {f : Ω → E} (hf : Measurable[mΩ ⊓ aeSigma 𝒮 P] f) :
    ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P 𝒮 ω₀), f ω = f ω₀ := by
  have hle : mΩ ⊓ aeSigma 𝒮 P ≤ mΩ := inf_le_left
  have hk := KernelTower.ae_condExpKernel_eq_of_le_aeSigma (P := P) h𝒮 hle
    (le_inf h𝒮 (le_aeSigma 𝒮 P) |>.trans (le_aeSigma _ P)) (inf_le_right)
  filter_upwards [Sec7.Aux122Disint.ae_ae_condExpKernel_eq (P := P) hle hf, hk] with ω₀ h1 h2
  rw [h2]
  exact h1

/-- **The stage law of `Mz.TailCanonAt` from the retained law of the induction.** -/
theorem exists_stageLaw_of_mvLaw (h𝒮𝓜 : 𝒮 ≤ 𝓜) (h𝓜 : 𝓜 ≤ mΩ) {κ : ℝ} {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : Measurable h) {A K' : Ω → Set ℂ} {G' : Set Ω} {Y : Ω → DistOn upperHalfPlaneOpens}
    {β : Ω → BoundaryWord} {M : ℝ} (hlaw : Fl.MvLaw κ 𝓜 P h A K' G' Y β M)
    (hβ𝒮 : Measurable[aeSigma 𝒮 P] β) {K : Ω → Set ℂ} (hKc : ∀ ω, IsCompact (K ω))
    (hKp : ∀ ω, IsPreconnected (K ω ∪ Restart.lowerHalf)) (hKm : @IsDyadicHitMeasurable Ω 𝒮 K)
    {x₀ : Ω → ℝ} (hx₀ : Measurable[𝒮] x₀) {G : Set Ω} (hG : MeasurableSet[𝒮] G)
    (hGG' : ∀ᵐ ω ∂P, ω ∈ G → ω ∈ G') (hKA : ∀ᵐ ω ∂P, ω ∈ G → fillH (K ω) = A ω) :
    ∃ c : Ω → BoundaryWord, Measurable[𝒮] c ∧
      (∀ᵐ ω ∂P, ω ∈ G → c ω = BoundaryWord.shiftW (x₀ ω) (β ω)) ∧
      ∀ᵐ ω₁ ∂P, ω₁ ∈ G → IsGFFWithBoundaryData (condExpKernel P 𝒮 ω₁)
        (fun ω => Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 0 (chiC κ) (h ω)) (c ω₁).fn
        (c ω₁).jumps := by
  obtain ⟨-, -, -, -, hK'A, hYm, hYt, hβm, hβs, -, -, hlY⟩ := hlaw
  have h𝒮 : 𝒮 ≤ mΩ := h𝒮𝓜.trans h𝓜
  have hG𝓜 : MeasurableSet[𝓜] G := h𝒮𝓜 _ hG
  have hKΩ : @IsDyadicHitMeasurable Ω mΩ K := fun n j => h𝒮 _ (hKm n j)
  have hY₀m := Fl.measurable_canonField κ hh hKc hKp hKΩ (measurable_const (a := (0 : ℝ)))
  have hYxm := Fl.measurable_canonField κ hh hKc hKp hKΩ (hx₀.mono h𝒮 le_rfl)
  -- the field of the induction is the offset-`0` canonical field of `K` on `G`
  have heq : ∀ᵐ ω ∂P, ω ∈ G → Y ω = Fl.canonField κ h (fun _ => (0 : ℝ)) hKc hKp ω := by
    filter_upwards [hGG', hKA, hK'A, hYt] with ω h1 h2 h3 h4 hω
    have e : fillH (K' ω) = fillH (K ω) := (h3 (h1 hω)).trans (h2 hω).symm
    have ht := h4 (h1 hω)
    rw [e] at ht
    exact Fl.canonField_eq_of_transport (x₀ := fun _ => (0 : ℝ)) hKc hKp ht
  have hlG : ∀ᵐ ω₀ ∂P, ω₀ ∈ G → IsGFFWithBoundaryData (condExpKernel P 𝓜 ω₀) Y (β ω₀).fn (β ω₀).jumps := by
    filter_upwards [hlY, hGG'] with ω₀ h1 h2 hω₀ using h1 (h2 hω₀)
  have hl0 := Fl.ae_isGFF_congr_on h𝓜 hG𝓜 hY₀m hlG heq
  have hlx := Mu.ae_isGFF_hullChart_shift h𝓜 hKc hKp (hx₀.mono h𝒮𝓜 le_rfl) hYxm hl0
  -- an `𝒮`-measurable version of the shifted word
  have hβΩ : Measurable β := hβm.mono h𝓜 le_rfl
  have hfm : Measurable fun ω => BoundaryWord.shiftW (x₀ ω) (β ω) :=
    BoundaryWord.measurable_shiftW.comp ((hx₀.mono h𝒮 le_rfl).prodMk hβΩ)
  have hβk : ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P 𝒮 ω₀), β ω = β ω₀ := by
    refine ae_ae_eq_of_measurable_aeSigma h𝒮 fun s hs => ?_
    exact MeasurableSpace.measurableSet_inf.2 ⟨hβΩ hs, hβ𝒮 hs⟩
  have hxk := Sec7.Aux122Disint.ae_ae_condExpKernel_eq (P := P) h𝒮 hx₀
  have hconst : ∀ᵐ ω₀ ∂P, ω₀ ∈ univ → ∀ᵐ ω ∂(condExpKernel P 𝒮 ω₀),
      BoundaryWord.shiftW (x₀ ω) (β ω) = BoundaryWord.shiftW (x₀ ω₀) (β ω₀) := by
    filter_upwards [hβk, hxk] with ω₀ h1 h2 _
    filter_upwards [h1, h2] with ω e1 e2
    rw [e1, e2]
  obtain ⟨c, hcm, hce⟩ := Qx.exists_measurable_ae_eq_of_kernel_const (P := P) h𝒮 hfm hconst
  refine ⟨c, hcm, ?_, ?_⟩
  · filter_upwards [hce] with ω hω _
    exact (hω (mem_univ ω)).symm
  have hlc : ∀ᵐ ω₀ ∂P, ω₀ ∈ G → IsGFFWithBoundaryData (condExpKernel P 𝓜 ω₀) (Fl.canonField κ h x₀ hKc hKp)
      (c ω₀).fn (c ω₀).jumps :=
    Fl.ae_isGFF_word_congr_on hlx (by filter_upwards [hce] with ω hω _ using hω (mem_univ ω))
  have hcs : ∀ᵐ ω ∂P, ω ∈ G → (c ω).IsSorted := by
    filter_upwards [hce] with ω hω _
    rw [← hω (mem_univ ω)]
    exact BoundaryWord.isSorted_shiftW (hβs ω) _
  exact ae_isGFF_of_le_fine h𝒮𝓜 h𝓜 hYxm hG hcs (Sec7.Aux122Disint.ae_ae_condExpKernel_eq (P := P) h𝒮 hcm) hlc

end InteractingSLE.Theorem14.SB.Cz
