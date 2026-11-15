/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2MtKer
import InteractingSLE.Spec.Supplement.SB2MuStop
import InteractingSLE.Spec.Supplement.SB2NaStmt
import InteractingSLE.Spec.Supplement.SB2ChWit

/-!
# K2 with the line family and the stopped code match, over NOJUMP's version structures

Packet PROVE-SB2-CONDFIN (round 3, D39). LCMEAN's `Mt.hBK_of_hull`, `Mt.hasSafeLaw_hasSafeMembers_of_stageLines` and
`Mu.ae_isStopDrvMatch_of_stageVersionS`, verbatim, over NOJUMP's `Na.StageVersionG`/`Na.StageVersionS` (the trace
clause relaxed to the chart's domain; no proof here reads `trace`). Generated from the landed originals.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H fwdHull zeroGFFTestCov)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Ci

open Mt hiding hBK_of_hull hasSafeLaw_hasSafeMembers_of_stageLines
open Mu hiding ae_isStopDrvMatch_of_stageVersionS ae_isStopDrvMatch_of_lines
  ae_canonLife_eq_relLife hseed_of_le_thr

section Ker
open Restart Exist Exist.Staged Exist.StagedLaw Restart.DomainMarkov Restart.DomainMarkov.K2 Supp8.Q3Stop
  Sec7.PocketTraversal LocalSets Lv Ms

variable {κ ψ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {F : Set Ω}
  {𝓖 : Filtration ℝ≥0 mΩ} {A₁ : ℝ≥0 → Ω → Set ℂ} {A₂ : ℝ≥0 → Ω → Set ℂ} {Φ : Ω → Chart} {β₁ : Ω → BoundaryWord}
  {types : Set WordType} {pc : Ω → ℝ≥0 → ℂ} {tL : Ω → ℝ≥0} {L : Ω → ℝ≥0∞}

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
/-- **The hull identity of the union line sets** from the version's field `hull`. -/
theorem hBK_of_hull (V : Na.StageVersionG κ ψ P F 𝓖 A₁ A₂ Φ β₁ types pc tL L) {w : WordType} (hw : w ∈ types)
    (t : ℝ≥0) : ∀ᵐ ω ∂P, ω ∈ seedCell κ ψ β₁ F w → V.a t ω < V.Λ w ω →
      H \ (fun ω => A₁ t ω ∪ A₂ t ω) ω =
        (Φ ω).2.1 '' (H \ fwdHull (fun s : ℝ => V.W s.toNNReal ω) (V.a t ω).toNNReal) :=
  V.hull w hw t

omit [StandardBorelSpace Ω] in
/-- **K2's (S) and (L) on a type cell of F3's word from a line-set family** with its locality, hull identity and line
mean (SB2(2)'s transposition of `Lv.hasSafeLaw_hasSafeMembers_of_lineSets`). -/
theorem hasSafeLaw_hasSafeMembers_of_stageLines (hh : IsGFFWithBoundaryData P h b jumps) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension b jumps u₀) (V : Na.StageVersionG κ ψ P F 𝓖 A₁ A₂ Φ β₁ types pc tL L)
    {w : WordType} (hw : w ∈ types) (hF : MeasurableSet[lineFiltC P 𝓖 0] (seedCell κ ψ β₁ F w))
    (hc : ∀ ω, (Φ ω).IsConformal) (hliftc : ∀ ω, ContinuousOn (Φ ω).2.2 (Φ ω).dom)
    (hlift : ∀ ω, InnerProductSpace.HarmonicOnNhd (Φ ω).2.2 (Φ ω).dom)
    (hdom : ∀ z, MeasurableSet[lineFiltC P 𝓖 0] {ω | z ∈ (Φ ω).dom})
    (hfwd : ∀ z, Measurable[lineFiltC P 𝓖 0] ({ω | z ∈ (Φ ω).dom}.indicator fun ω => (Φ ω).1 z))
    (hliftm : ∀ z, Measurable[lineFiltC P 𝓖 0] ({ω | z ∈ (Φ ω).dom}.indicator fun ω => (Φ ω).2.2 z))
    (B : ℝ≥0 → Ω → Set ℂ) (hBm : ∀ t, Measurable[mΩ, hittingSigma] (B t))
    (hBc : ∀ t ω, B t ω ⊆ H ∧ IsOpen (H \ B t ω))
    (hloc : ∀ t, WholeField.IsHistoryAvoidanceLocal (lineFiltC P 𝓖 t) (B t) (WholeField.centredField h u₀) P)
    (hBK : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ seedCell κ ψ β₁ F w → V.a t ω < V.Λ w ω →
      H \ B t ω = (Φ ω).2.1 '' (H \ fwdHull (fun s : ℝ => V.W s.toNNReal ω) (V.a t ω).toNNReal))
    (g : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens)
    (hg : ∀ t, IsLocalSetMean (B t) (WholeField.centredField h u₀) P (g t))
    (hmean : ∀ (t : ℝ≥0) (φ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P, ω ∈ seedCell κ ψ β₁ F w →
      V.a t ω < V.Λ w ω →
      Disjoint (tsupport φ) (fwdHull (fun s : ℝ => V.W s.toNNReal ω) (V.a t ω).toNNReal) →
      Chart.chartTransport (hc ω) 1 (ψ * chiC κ) (chiC κ)
          (g t ω + (h ω - WholeField.centredField h u₀ ω)) φ =
        ∫ z, couplingMean κ (fun s : ℝ => V.W s.toNNReal ω) (V.a t ω).toNNReal
          (bheProc κ (typedRhoL w) (typedRhoR w) V.W (geomLW V.W (cellXL κ ψ β₁ w))
            (geomRW V.W (cellXR κ ψ β₁ w)) ω (V.a t ω).toNNReal) z * φ z) :
    HasSafeLaw κ (typedRhoL w) (typedRhoR w) P V.𝓗 (seedCell κ ψ β₁ F w) (V.Λ w) V.W
        (geomLW V.W (cellXL κ ψ β₁ w)) (geomRW V.W (cellXR κ ψ β₁ w))
        (fun ω => Chart.chartTransport (hc ω) 1 (ψ * chiC κ) (chiC κ) (h ω)) ∧
      HasSafeMembers P V.𝓗 (seedCell κ ψ β₁ F w) (V.Λ w) V.W
        (fun ω => Chart.chartTransport (hc ω) 1 (ψ * chiC κ) (chiC κ) (h ω)) := by
  have hhm : Measurable (WholeField.centredField h u₀) := WholeField.measurable_centredField hh.1 u₀
  have hh0 := isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀
  have hℋ : ∀ t, lineFiltC P 𝓖 t ≤ mΩ := fun t => (lineFiltC P 𝓖).le t
  refine ⟨?_, ?_⟩
  · refine BW1Lines.hasSafeLaw_life_of_lineKernel hF hc hdom hfwd hliftm hliftc hh.1 (ψ * chiC κ) (chiC κ)
      V.clock_cont V.clock_mono V.clock_zero V.clock_meas V.timeChange _ (V.reach w hw) (V.reg w hw)
      (V.safeS w hw) (fun t => germSigma (B t) (WholeField.centredField h u₀) ⊔ lineFiltC P 𝓖 t)
      (fun t => le_sup_right) (fun t => sup_le (germSigma_le (hBm t) hhm) (hℋ t))
      (fun t ω => g t ω + (h ω - WholeField.centredField h u₀ ω)) (fun t φ => ?_) hmean
    set U₀ : ℝ := ∫ z, u₀ z * φ z with hU₀
    set X₀ : Ω → ℂ := fun ω' => Complex.exp (Complex.I * (WholeField.centredField h u₀ ω' φ : ℂ)) with hX₀def
    have hXX₀ : (fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ))) = Complex.exp (Complex.I * (U₀ : ℂ)) • X₀ := by
      funext ω'
      simp only [hX₀def, Pi.smul_apply, smul_eq_mul, ← Complex.exp_add,
        WholeField.centredField_apply h hu₀.1 ω' φ]
      congr 1
      push_cast
      ring
    have hsmul := condExp_smul (μ := P) (Complex.exp (Complex.I * (U₀ : ℂ))) X₀
      (germSigma (B t) (WholeField.centredField h u₀) ⊔ lineFiltC P 𝓖 t)
    filter_upwards [hsmul, Supp8.RelSafeS.ae_condExp_cexp_marked hh0 (hBm t) (hBc t) (hℋ t) (hloc t) (hg t) φ,
      hBK t] with ω h1 h2 h3 hωF hlt hsupp
    have hGc : zeroGFFTestCov ((Φ ω).2.1 '' (H \ fwdHull (fun s : ℝ => V.W s.toNNReal ω)
        (V.a t ω).toNNReal)) φ φ = zeroGFFTestCov (H \ B t ω) φ φ := by rw [h3 hωF hlt]
    have hM : (g t ω + (h ω - WholeField.centredField h u₀ ω)) φ = g t ω φ + U₀ := by
      show g t ω φ + (h ω φ - WholeField.centredField h u₀ ω φ) = _
      rw [WholeField.centredField_apply h hu₀.1 ω φ]
      ring
    show P[fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ)) |
        germSigma (B t) (WholeField.centredField h u₀) ⊔ lineFiltC P 𝓖 t] ω =
      Complex.exp (Complex.I * ((g t ω + (h ω - WholeField.centredField h u₀ ω)) φ : ℂ) -
        (((1 / 2 : ℝ) * zeroGFFTestCov ((Φ ω).2.1 '' (H \ fwdHull (fun s : ℝ => V.W s.toNNReal ω)
          (V.a t ω).toNNReal)) φ φ : ℝ) : ℂ))
    rw [hGc, hM, hXX₀, h1, Pi.smul_apply, smul_eq_mul, h2, Complex.ofReal_exp, ← Complex.exp_add,
      ← Complex.exp_add]
    congr 1
    simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_ofNat]
    ring
  · exact BW1Lines.hasSafeMembers_life_of_lineLocal hh.1 hu₀.1 hh0 hc hdom hfwd hliftm hliftc hlift
      (ψ * chiC κ) (chiC κ) V.clock_cont V.clock_mono V.clock_zero V.clock_meas V.timeChange _
      (V.reach w hw) (V.reg w hw) (V.safeL w hw) (fun t => lineFiltC P 𝓖 t) (fun t => le_rfl) hℋ B hBm hBc hloc
      hBK

end Ker

section Stop
open Restart Exist Exist.Staged Exist.StagedLaw Restart.DomainMarkov Restart.DomainMarkov.K2 Supp8.Q3Stop
  Sec7.PocketTraversal LocalSets Lv Ms
open Supp8.GB6.RelDrv (IsStopDrvMatch)

variable {κ ψ : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {F : Set Ω} {𝓖 : Filtration ℝ≥0 mΩ}
  {A₁ A₂ : ℝ≥0 → Ω → Set ℂ} {Φ : Ω → Chart} {β₁ : Ω → BoundaryWord} {types : Set WordType}
  {pc : Ω → ℝ≥0 → ℂ} {tL : Ω → ℝ≥0} {L relLife : Ω → ℝ≥0∞}

/-- **SB2(2)'s relative versions are the canonical driver code before every stop.** For relative versions at
announced stops with K2's (S) and (L) at every stop on every admissible type cell of the word `β₁`, almost surely on
the live event, for every `m`, `V m` is at most the lifetime of the canonical driver code of `(β₁, chart field)` and
`W m` is that code at the dyadic times before `V m`. -/
theorem ae_isStopDrvMatch_of_stageVersionS (h12p : Theorem12ParamStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (hκ : 0 < κ) (hhm : Measurable h)
    (S : Na.StageVersionS κ ψ P F 𝓖 A₁ A₂ Φ β₁ types pc tL L relLife)
    (hβ₁ : Measurable[lineFiltC P 𝓖 0] β₁) (hF : MeasurableSet[lineFiltC P 𝓖 0] F)
    (htypes : types.Countable) (hcover : ∀ᵐ ω ∂P, ω ∈ F → angleWordType κ ψ (β₁ ω) ∈ types)
    (hc : ∀ ω, (Φ ω).IsConformal) (hdom : ∀ z, MeasurableSet {ω | z ∈ (Φ ω).dom})
    (hfwd : ∀ z, Measurable ({ω | z ∈ (Φ ω).dom}.indicator fun ω => (Φ ω).1 z))
    (hliftm : ∀ z, Measurable ({ω | z ∈ (Φ ω).dom}.indicator fun ω => (Φ ω).2.2 z))
    (hlc : ∀ ω, ContinuousOn (Φ ω).2.2 (Φ ω).dom)
    (hint : ∀ φ : TestOn upperHalfPlaneOpens,
      IntegrableOn (fun ω => Chart.chartTransport (hc ω) 1 (ψ * chiC κ) (chiC κ) (h ω) φ) F P)
    (hker : ∀ m, ∀ w ∈ types,
      HasSafeLaw κ (typedRhoL w) (typedRhoR w) P (S.ver m).𝓗 (seedCell κ ψ β₁ F w) (S.V m) (S.ver m).W
          (geomLW (S.ver m).W (cellXL κ ψ β₁ w)) (geomRW (S.ver m).W (cellXR κ ψ β₁ w))
          (fun ω => Chart.chartTransport (hc ω) 1 (ψ * chiC κ) (chiC κ) (h ω)) ∧
        HasSafeMembers P (S.ver m).𝓗 (seedCell κ ψ β₁ F w) (S.V m) (S.ver m).W
          (fun ω => Chart.chartTransport (hc ω) 1 (ψ * chiC κ) (chiC κ) (h ω)))
    (hseed : ∀ w ∈ types, ∀ᵐ ω ∂P, ω ∈ wordTypeCell κ ψ β₁ F w → ω ∈ seedCell κ ψ β₁ F w) :
    ∀ᵐ ω ∂P, ω ∈ F → ∀ m, IsStopDrvMatch (driverCode h12p hκ ψ
      (β₁ ω, Chart.chartTransport (hc ω) 1 0 (chiC κ) (h ω))) (fun t => (S.ver m).W t ω) (S.V m ω) := by
  suffices hm : ∀ m, ∀ᵐ ω ∂P, ω ∈ F → IsStopDrvMatch (driverCode h12p hκ ψ
      (β₁ ω, Chart.chartTransport (hc ω) 1 0 (chiC κ) (h ω))) (fun t => (S.ver m).W t ω) (S.V m ω) by
    filter_upwards [ae_all_iff.2 hm] with ω hω hF' m using hω m hF'
  intro m
  set Vd := S.ver m with hVd
  have hcell : ∀ w ∈ types, ∀ᵐ ω ∂P, ω ∈ seedCell κ ψ β₁ F w →
      IsStopDrvMatch (driverCode h12p hκ ψ (β₁ ω, Chart.chartTransport (hc ω) 1 0 (chiC κ) (h ω)))
        (fun t => Vd.W t ω) (S.V m ω) := by
    intro w hw
    obtain ⟨hlaw, hmem⟩ := hker m w hw
    have hxL0 : ∀ ω i, cellXL κ ψ β₁ w ω i ≤ 0 := fun ω => (FCDet.isOrderedForceWord_typeXL (β₁ ω)).2.1
    have hxR0 : ∀ ω j, 0 ≤ cellXR κ ψ β₁ w ω j := fun ω => (FCDet.isOrderedForceWord_typeXL (β₁ ω)).2.2.2
    have hxLa : ∀ ω, Antitone (cellXL κ ψ β₁ w ω) := fun ω => (FCDet.isOrderedForceWord_typeXL (β₁ ω)).1
    have hxRm : ∀ ω, Monotone (cellXR κ ψ β₁ w ω) := fun ω =>
      (FCDet.isOrderedForceWord_typeXL (β₁ ω)).2.2.1
    have hword : ∀ᵐ ω ∂P, ω ∈ seedCell κ ψ β₁ F w →
        flowLineNL (β₁ ω).fn (β₁ ω).jumps 0 = w.1 ∧ flowLineNR (β₁ ω).fn (β₁ ω).jumps 0 = w.2.1 ∧
        truncWord w.1 w.2.1 (padFL κ ψ (β₁ ω).fn (β₁ ω).jumps) =
          ((cellXL κ ψ β₁ w ω, cellXR κ ψ β₁ w ω), (typedRhoL w, typedRhoR w)) :=
      Eventually.of_forall fun ω hω => k2_word_of_mem_wordTypeCell hω.1
    have hVthr : ∀ᵐ ω ∂P, ω ∈ seedCell κ ψ β₁ F w →
        S.V m ω ≤ FCDet.thr (typedRhoL w) (typedRhoR w) Vd.W (cellXL κ ψ β₁ w) (cellXR κ ψ β₁ w) ω := by
      have h1 := Vd.Λ_le w hw
      rw [S.Λ_eq m w] at h1
      exact h1
    exact Cond.ae_isStopDrvMatch_of_hasSafeLaw_rule_on h12p h13 hκ Vd.marks_le
      (measurableSet_seedCell hβ₁ hF w) hβ₁ (measurable_cellXL hβ₁ w) (measurable_cellXR hβ₁ w) hxL0 hxR0 hxLa
      hxRm hword Vd.W_zero Vd.W_cont Vd.W_adapted hhm hc hdom hfwd hliftm hlc
      (fun φ => (hint φ).mono_set (seedCell_subset w)) S.record_meas (S.ρ_meas m) (S.ρ_rule m) (S.ρs_meas m)
      (S.ρs_rule m) (S.ρs_fin m) (S.ρs_mono m) (S.V_eq m)
      ((S.ann m).mono fun ω h hω => h (seedCell_subset w hω)) hVthr hlaw hmem
  filter_upwards [(ae_ball_iff htypes).2 hcell, hcover, (ae_ball_iff htypes).2 hseed] with ω hcode hcov hsd hF'
  obtain ⟨w₀, hw₀e⟩ : ∃ w₀, angleWordType κ ψ (β₁ ω) = w₀ := ⟨_, rfl⟩
  have hw₀ : w₀ ∈ types := hw₀e ▸ hcov hF'
  exact hcode w₀ hw₀ (hsd w₀ hw₀ ⟨hF', hw₀e⟩)

end Stop

end InteractingSLE.Theorem14.SB.Ci
