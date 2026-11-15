/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2DrvLineUnion
import InteractingSLE.Spec.Supplement.SB2ZsGeo

/-!
# SB2ZsUnion: `SB2DrvLineUnion` for the lifetime-generic line version `SB2LineVersionG`

Packet PROVE-T14-SB2DRV (round 15, decision D4: SB2(1) at announced stops). The declarations of `SB2DrvLineUnion` that
depend on the line version, for `SB2LineVersionG` (guards `a t < Λ w` in place of `a t < thr`), with the suffix `G`.
The proofs are the landed ones with the guard replaced. No source theorem is replaced.
-/
/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/

/-!
# SB2(1)'s line kernels, part 4: (S) from a line union, (L) from the line sets

Packet PROVE-T14-SB2DRV (round 5). K2's (S) needs, at each physical time `t`, a marked local set `B t` (marks
`D.lineFiltC t`) whose complement contains the chart image `c(ℍ \ K_{a t})` as a clopen part, and the identification of
its mean there; (L) needs a set whose complement *is* that chart image (`lineB`, done). The two sets may differ: for
(S) the natural set is the union of the filled retained prefix with the filled upper flow up to the absolute time `T`,
whose mean FIN's union-mean lemma computes, and whose complement has, besides `c(ℍ \ K_{a t})`, the joint pockets.

* **`hasSafeLaw_of_lineUnion`**: (S) from such a family (the covariance of the clopen part,
  `zeroGFFTestCov_eq_of_isClopen`);
* **`hasSafeMembers_of_lineB`**: (L) from the line sets `lineB` and the proved line geometry;
* **`SB2LineUnionStatement`** (the remaining kernel input, weaker than `SB2LineMeanStatement`:
  `sb2LineUnionStatement_of_mean`), **`sb2LineKernelStatement_of_union`**,
  **`sb2DriverLinkAmbStatement_of_version_union`**.

**R48.** Theorems 1.2–1.3 are hypotheses; this serves Theorem 1.4 only.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H fwdHull zeroGFFTestCov)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lv

open Restart Exist Exist.Staged Exist.StagedLaw GW1W GW1Conn WalkInf Restart.DomainMarkov Restart.DomainMarkov.K2
  Supp8.Q3Stop Sec7.PocketTraversal LocalSets

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u ψ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}

/-- **(S) from a line union**: a marked local family whose complement contains `c(ℍ \ K_{a t})` as a clopen part, with
the mean identification there. -/
theorem hasSafeLaw_of_lineUnionG (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ)
    (I : K2LaunchInputs κ b jumps P h E k u ψ) {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    (D : EntranceUnion κ b jumps P h E k u η ζ u₀) (Vd : SB2LineVersionG HP I D) {w : WordType} (hw : w ∈ I.types)
    (B : ℝ≥0 → Ω → Set ℂ) (hBm : ∀ t, Measurable[mΩ, hittingSigma] (B t))
    (hBc : ∀ t ω, B t ω ⊆ H ∧ IsOpen (H \ B t ω))
    (hloc : ∀ t, WholeField.IsHistoryAvoidanceLocal (D.lineFiltC HP t) (B t) (WholeField.centredField h u₀) P)
    (hclop : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ lineLiveG Vd w t →
      chartImage (I.chart ω) (relHullG Vd t ω) ⊆ H \ B t ω ∧
        IsOpen ((H \ B t ω) \ chartImage (I.chart ω) (relHullG Vd t ω)))
    (g : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens)
    (hg : ∀ t, IsLocalSetMean (B t) (WholeField.centredField h u₀) P (g t))
    (hmean : ∀ (t : ℝ≥0) (φ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P, ω ∈ seedCell κ ψ I.word D.event w →
      Vd.a t ω < Vd.Λ w ω →
      Disjoint (tsupport φ) (fwdHull (fun s : ℝ => Vd.W s.toNNReal ω) (Vd.a t ω).toNNReal) →
      Chart.chartTransport (I.chart_measurable.1 ω) 1 (ψ * chiC κ) (chiC κ)
          (g t ω + (h ω - WholeField.centredField h u₀ ω)) φ =
        ∫ z, couplingMean κ (fun s : ℝ => Vd.W s.toNNReal ω) (Vd.a t ω).toNNReal
          (bheProc κ (typedRhoL w) (typedRhoR w) Vd.W (geomLW Vd.W (cellXL κ ψ I.word w))
            (geomRW Vd.W (cellXR κ ψ I.word w)) ω (Vd.a t ω).toNNReal) z * φ z) :
    HasSafeLaw κ (typedRhoL w) (typedRhoR w) P Vd.𝓗 (seedCell κ ψ I.word D.event w)
        (Vd.Λ w) Vd.W
        (geomLW Vd.W (cellXL κ ψ I.word w)) (geomRW Vd.W (cellXR κ ψ I.word w))
        (fun ω => Chart.chartTransport (I.chart_measurable.1 ω) 1 (ψ * chiC κ) (chiC κ) (h ω)) := by
  have hhm : Measurable (WholeField.centredField h u₀) := WholeField.measurable_centredField HP.field.1 u₀
  have hh0 := isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData HP.field hu₀
  have hpast : pastSigma κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1) ≤ D.lineFiltC HP 0 :=
    D.past_le_marks.trans (D.marks_le_lineFiltC HP 0)
  obtain ⟨hc, hliftc, -, hdom, hfwd, -, hliftm⟩ := I.chart_measurable
  have hF : MeasurableSet[D.lineFiltC HP 0] (seedCell κ ψ I.word D.event w) :=
    (D.marks_le_lineFiltC HP 0) _ (measurableSet_seedCell (I.word_measurable.mono D.past_le_marks le_rfl)
      (D.measurableSet_event HP) w)
  have hℋ : ∀ t, D.lineFiltC HP t ≤ mΩ := fun t => (D.lineFiltC HP).le t
  refine BW1Lines.hasSafeLaw_life_of_lineKernel hF hc (fun z => hpast _ (hdom z))
    (fun z => (hfwd z).mono hpast le_rfl) (fun z => (hliftm z).mono hpast le_rfl) hliftc HP.field.1 (ψ * chiC κ)
    (chiC κ) Vd.clock_cont Vd.clock_mono Vd.clock_zero Vd.clock_meas Vd.timeChange _ (Vd.reach w hw) (Vd.reg w hw)
    (Vd.safeS w hw) (fun t => germSigma (B t) (WholeField.centredField h u₀) ⊔ D.lineFiltC HP t)
    (fun t => le_sup_right) (fun t => sup_le (germSigma_le (hBm t) hhm) (hℋ t))
    (fun t ω => g t ω + (h ω - WholeField.centredField h u₀ ω)) (fun t φ => ?_) hmean
  set U₀ : ℝ := ∫ z, u₀ z * φ z with hU₀
  set X₀ : Ω → ℂ := fun ω' => Complex.exp (Complex.I * (WholeField.centredField h u₀ ω' φ : ℂ)) with hX₀def
  have hXX₀ : (fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ))) = Complex.exp (Complex.I * (U₀ : ℂ)) • X₀ := by
    funext ω'
    simp only [hX₀def, Pi.smul_apply, smul_eq_mul, ← Complex.exp_add, WholeField.centredField_apply h hu₀.1 ω' φ]
    congr 1
    push_cast
    ring
  have hsmul := condExp_smul (μ := P) (Complex.exp (Complex.I * (U₀ : ℂ))) X₀
    (germSigma (B t) (WholeField.centredField h u₀) ⊔ D.lineFiltC HP t)
  filter_upwards [hsmul, Supp8.RelSafeS.ae_condExp_cexp_marked hh0 (hBm t) (hBc t) (hℋ t) (hloc t) (hg t) φ,
    hclop t] with ω h1 h2 h3 hωF hlt hsupp
  obtain ⟨hCV, hVC⟩ := h3 ⟨hωF, hlt⟩
  have hGc : zeroGFFTestCov ((I.chart ω).2.1 '' (H \ fwdHull (fun s : ℝ => Vd.W s.toNNReal ω)
      (Vd.a t ω).toNNReal)) φ φ = zeroGFFTestCov (H \ B t ω) φ φ :=
    (zeroGFFTestCov_eq_of_isClopen (hBc t ω).2 sdiff_subset
      (isOpen_chartImage (isConformal_chart I ω) (isOpen_H_sdiff_relHullG Vd t ω)) hCV hVC φ hsupp).symm
  have hM : (g t ω + (h ω - WholeField.centredField h u₀ ω)) φ = g t ω φ + U₀ := by
    show g t ω φ + (h ω φ - WholeField.centredField h u₀ ω φ) = _
    rw [WholeField.centredField_apply h hu₀.1 ω φ]
    ring
  show P[fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ)) |
      germSigma (B t) (WholeField.centredField h u₀) ⊔ D.lineFiltC HP t] ω =
    Complex.exp (Complex.I * ((g t ω + (h ω - WholeField.centredField h u₀ ω)) φ : ℂ) -
      (((1 / 2 : ℝ) * zeroGFFTestCov ((I.chart ω).2.1 '' (H \ fwdHull (fun s : ℝ => Vd.W s.toNNReal ω)
        (Vd.a t ω).toNNReal)) φ φ : ℝ) : ℂ))
  rw [hGc, hM, hXX₀, h1, Pi.smul_apply, smul_eq_mul, h2, Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_one,
    Complex.ofReal_ofNat]
  ring
/-- **(L) from the line sets** (their locality from the proved line geometry). -/
theorem hasSafeMembers_of_lineBG (h12p : Theorem12ParamStatement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ) (I : K2LaunchInputs κ b jumps P h E k u ψ) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension b jumps u₀) (D : EntranceUnion κ b jumps P h E k u η ζ u₀)
    (Vd : SB2LineVersionG HP I D) {w : WordType} (hw : w ∈ I.types) :
    HasSafeMembers P Vd.𝓗 (seedCell κ ψ I.word D.event w)
      (Vd.Λ w) Vd.W
      (fun ω => Chart.chartTransport (I.chart_measurable.1 ω) 1 (ψ * chiC κ) (chiC κ) (h ω)) := by
  have hh0 := isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData HP.field hu₀
  have hpast : pastSigma κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1) ≤ D.lineFiltC HP 0 :=
    D.past_le_marks.trans (D.marks_le_lineFiltC HP 0)
  obtain ⟨hc, hliftc, hlift, hdom, hfwd, -, hliftm⟩ := I.chart_measurable
  have hℋ : ∀ t, D.lineFiltC HP t ≤ mΩ := fun t => (D.lineFiltC HP).le t
  have hIncl := sb2LineGeomStatementG κ b jumps P h E k u ψ η ζ HP I u₀ hu₀ D Vd w hw
  have hloc : ∀ t, WholeField.IsHistoryAvoidanceLocal (D.lineFiltC HP t) (lineBG Vd w t)
      (WholeField.centredField h u₀) P := by
    intro t
    refine isHistoryAvoidanceLocal_of_ae_enlargement
      (D.isHistoryAvoidanceLocal_lineFiltC HP t (D.isHistoryAvoidanceLocal_abs h12p h13 HP hu₀ (t : ℝ≥0∞))) ?_
      fun U hUH => measurableSet_disjoint_lineBG Vd hw t hUH
    filter_upwards [hIncl t] with ω hω
    by_cases hl : ω ∈ lineLiveG Vd w t
    · intro z hz
      unfold lineBG
      rw [ite_eq_left hl]
      exact ⟨hz.2, fun hzc => Set.disjoint_left.1 (hω hl) hz.1 hzc⟩
    · intro z hz
      unfold lineBG
      rw [ite_eq_right hl]
      exact hz.2
  exact BW1Lines.hasSafeMembers_life_of_lineLocal HP.field.1 hu₀.1 hh0 hc (fun z => hpast _ (hdom z))
    (fun z => (hfwd z).mono hpast le_rfl) (fun z => (hliftm z).mono hpast le_rfl) hliftc hlift (ψ * chiC κ)
    (chiC κ) Vd.clock_cont Vd.clock_mono Vd.clock_zero Vd.clock_meas Vd.timeChange _ (Vd.reach w hw) (Vd.reg w hw)
    (Vd.safeL w hw) (fun t => D.lineFiltC HP t) (fun t => le_rfl) hℋ (lineBG Vd w)
    (fun t => WalkMean.measurable_hitting_of_avoid ((D.lineFiltC HP).le t)
      fun U hUH => measurableSet_disjoint_lineBG Vd hw t hUH)
    (fun t ω => ⟨lineB_subset_HG Vd w t ω, isOpen_H_sdiff_lineBG Vd w t ω⟩) hloc
    (fun t => Eventually.of_forall fun ω hF hlt => H_sdiff_lineB_of_liveG Vd w t ⟨hF, hlt⟩)
/-- **Named input (the line union and its mean)**: for every type cell, a family of marked local sets for the line
filtration, relatively closed, whose complements contain `c(ℍ \ K_{a t})` as a clopen part on the live cell, with any
local-set mean read in the launch chart equal to the canonical mean off the relative hull. -/
def SB2LineUnionStatementG : Prop :=
  ∀ (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens)
    (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) (u ψ : ℝ)
    (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞)
    (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ)
    (I : K2LaunchInputs κ b jumps P h E k u ψ) (u₀ : ℂ → ℝ) (_hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    (D : EntranceUnion κ b jumps P h E k u η ζ u₀) (Vd : SB2LineVersionG HP I D),
    ∀ w ∈ I.types, ∃ B : ℝ≥0 → Ω → Set ℂ,
      (∀ t, Measurable[_, hittingSigma] (B t)) ∧ (∀ t ω, B t ω ⊆ H ∧ IsOpen (H \ B t ω)) ∧
      (∀ t, WholeField.IsHistoryAvoidanceLocal (D.lineFiltC HP t) (B t) (WholeField.centredField h u₀) P) ∧
      (∀ t : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ lineLiveG Vd w t →
        chartImage (I.chart ω) (relHullG Vd t ω) ⊆ H \ B t ω ∧
          IsOpen ((H \ B t ω) \ chartImage (I.chart ω) (relHullG Vd t ω))) ∧
      ∀ (t : ℝ≥0) (g : Ω → DistOn upperHalfPlaneOpens),
        IsLocalSetMean (B t) (WholeField.centredField h u₀) P g → ∀ φ : TestOn upperHalfPlaneOpens,
        ∀ᵐ ω ∂P, ω ∈ seedCell κ ψ I.word D.event w →
        Vd.a t ω < Vd.Λ w ω →
        Disjoint (tsupport φ) (fwdHull (fun s : ℝ => Vd.W s.toNNReal ω) (Vd.a t ω).toNNReal) →
        Chart.chartTransport (I.chart_measurable.1 ω) 1 (ψ * chiC κ) (chiC κ)
            (g ω + (h ω - WholeField.centredField h u₀ ω)) φ =
          ∫ z, couplingMean κ (fun s : ℝ => Vd.W s.toNNReal ω) (Vd.a t ω).toNNReal
            (bheProc κ (typedRhoL w) (typedRhoR w) Vd.W (geomLW Vd.W (cellXL κ ψ I.word w))
              (geomRW Vd.W (cellXR κ ψ I.word w)) ω (Vd.a t ω).toNNReal) z * φ z
/-- **The kernel half from the line union.** -/
theorem sb2LineKernelStatement_of_unionG (h12p : Theorem12ParamStatement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (hU : SB2LineUnionStatementG.{u}) : SB2LineKernelRStatementG.{u} := by
  intro κ b jumps Ω _ _ P _ h E k u ψ η ζ HP I u₀ hu₀ D Vd w hw
  obtain ⟨B, hBm, hBc, hloc, hclop, hmean⟩ := hU κ b jumps P h E k u ψ η ζ HP I u₀ hu₀ D Vd w hw
  have hh0 := isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData HP.field hu₀
  have hlocal : ∀ t, IsLocalSet (B t) (WholeField.centredField h u₀) P := fun t =>
    ((isLocalSet_tfae hh0 (hBm t) (Eventually.of_forall (hBc t))).out 4 1).2 (hloc t).isAvoidanceLocal
  choose g hg using fun t => IsLocalSet.exists_isLocalSetMean hh0 (hBm t) (hlocal t)
  exact ⟨hasSafeLaw_of_lineUnionG HP I hu₀ D Vd hw B hBm hBc hloc hclop g hg fun t φ => hmean t (g t) (hg t) φ,
    hasSafeMembers_of_lineBG h12p h13 HP I hu₀ D Vd hw⟩
end InteractingSLE.Theorem14.SB.Lv

