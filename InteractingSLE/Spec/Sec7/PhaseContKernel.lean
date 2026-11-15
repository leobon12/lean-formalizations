/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PhaseClauseMean
import InteractingSLE.Spec.Sec7.PhaseContMeas
import InteractingSLE.Spec.Sec7.Lemma725RefMarksGerm

/-!
# Theorem 1.2's R.7: the pocket kernel with an earlier germ retained

Packet PROVE-PHASECONT. To compare the pocket's conditional laws at two relative capacity times `q₀ ≤ p`, the later
kernel must be a conditional law given a σ-algebra that contains the earlier one. The earlier kernel σ-algebra is
`germ(K_{q₀}) ∨ 𝓦 ∨ σ(prefix events up to q₀) ∨ 𝒩`. Since `K_{q₀} ⊆ K_p` is measurable for the prefix events up to `p`
(`PhaseContMeas`), its germ can be added to the marks of the union law at `p` ("the germ of a smaller marked local set
can be added to the marks of a larger one", `Lemma725RefMarks.isHistoryAvoidanceLocal_sup_germSigma`, R69), and the
kernel at `p` holds given `germ(K_p) ∨ 𝓦 ∨ σ(prefix events up to p) ∨ germ(K_{min q₀ p}) ∨ 𝒩`.

## Main results

* `activeCompl_mono`: the canonical sets increase with the relative time;
* **`pocketChartPhaseData_retain`**: `PhaseClause.pocketChartPhaseData_of_stop`'s kernel and phase mean identification,
  with explicit kernel σ-algebras retaining the germ of `K_{min q₀ p}`.

Conditional helpers; no source theorem is replaced. Ruling R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any result taking them as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Complex
open QuantumZipper (H fwdHull fwdMap fwdMapInv logDerivFwd chiC zeroGFFTestCov)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open SupercriticalConformalCovariance (IsConformalBijection)
open SupercriticalConformalCovariance.GM24 (smoothDist)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.PhaseCont

open PocketStop PocketTraversal PocketAdapt Lemma71C LocalSets WholeField PocketCoupling PocketUnionPt PhaseSel
  Lemma725RefChart PocketStopField Lemma725RefSafe PhaseClause

universe u

/-- The canonical sets increase with the relative time. -/
theorem activeCompl_mono {Ω : Type*} {A : Set Ω} {γ : Ω → ℝ → ℂ} {c : Ω → Chart} {p p' : ℝ≥0} (hpp' : p ≤ p')
    (ω : Ω) : activeCompl A γ c p ω ⊆ activeCompl A γ c p' ω := by
  rintro z ⟨hzH, hz⟩
  refine ⟨hzH, fun hz' => hz ?_⟩
  obtain ⟨hω, hlive, w, ⟨hwH, hwK⟩, rfl⟩ := hz'
  refine ⟨hω, lt_of_le_of_lt (by exact_mod_cast hpp') hlive, w, ⟨hwH, fun hwp => hwK ?_⟩, rfl⟩
  exact WangWu.fwdHull_mono (by exact_mod_cast hpp') hwp

section Retain

variable {Ω : Type u} {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **The pocket kernel with the germ of an earlier canonical set retained** (`pocketChartPhaseData_of_stop` with
explicit kernel σ-algebras `germ(K_p) ∨ (𝓦 ∨ prefix events up to p ∨ germ(K_{min q₀ p})) ∨ 𝒩`; the additional
hypothesis `hCin` makes `K_{min q₀ p}` measurable for the prefix events up to `p`). -/
theorem pocketChartPhaseData_retain [IsProbabilityMeasure P] {κ : ℝ} (hκ : 0 < κ) {nL nR : ℕ}
    {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ} (h𝓦 : 𝓦 ≤ mΩ) {A : Set Ω} (hA : MeasurableSet[𝓦] A)
    {γ : Ω → ℝ → ℂ} (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω)) (hγm : ∀ u, 0 ≤ u → Measurable fun ω : A => γ ω u)
    {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ} {C : Ω → Set ℂ} (hCo : ∀ ω ∈ A, IsOpen (C ω))
    (hCH : ∀ ω ∈ A, C ω ⊆ H) {ψ : Ω → ℂ → ℂ} (hψ : ∀ ω ∈ A, IsConformalBijection (ψ ω) (C ω) H)
    (hCm : ∀ z, MeasurableSet[𝓦] {ω | ω ∈ A ∧ z ∈ C ω})
    (hψm : ∀ z, Measurable[𝓦] ({ω | ω ∈ A ∧ z ∈ C ω}.indicator fun ω => ψ ω z))
    (hCin : ∀ U : Set ℂ, IsOpen U → U ⊆ H → MeasurableSet[𝓦] {ω | ω ∈ A ∧ U ⊆ C ω})
    {F : ℝ≥0 → Ω → Set ℂ}
    (hFo : ∀ q : ℝ≥0, ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) → IsOpen (H \ F q ω))
    (hgeo : ∀ q : ℝ≥0, ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) →
      ψ ω '' (C ω ∩ (H \ F q ω)) = H \ fwdHull (fun s : ℝ => segDriver (γ ω) s.toNNReal) q)
    {h₀ : Ω → DistOn upperHalfPlaneOpens} (hh₀ : IsZeroBoundaryGFF upperHalfPlaneOpens h₀ P) {u : ℂ → ℝ}
    (hu : InnerProductSpace.HarmonicOnNhd u H) (hub : ∃ M : ℝ, ∀ z ∈ H, |u z| ≤ M) {n : Ω → ℤ}
    (hn : Measurable[𝓦] n) {a : ℝ} (hU : ∀ q : ℝ≥0, PocketStopUnionLaw 𝓦 P A γ C (F q) h₀ q)
    {δ : ℝ≥0 → Ω → ℝ}
    (hside : ∀ q : ℝ≥0, PocketStopSide.PocketStopPhaseSideLimit κ ρL ρR P A γ xL xR
      (fun ω => shiftChart (pChart A C ψ ω) (n ω)) a h₀ u
      (activeCompl A γ (fun ω => shiftChart (pChart A C ψ ω) (n ω)) q) (δ q) q) (q₀ : ℝ≥0) :
    ∃ M : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens,
      PocketKernel 𝓦 P A γ (fun ω => shiftChart (pChart A C ψ ω) (n ω))
        (fun ω => h₀ ω + smoothDist upperHalfPlaneOpens u)
        (fun p => germSigma (activeCompl A γ (fun ω => shiftChart (pChart A C ψ ω) (n ω)) p) h₀ ⊔
          (locPrefixSigma 𝓦 A γ p ⊔
            germSigma (activeCompl A γ (fun ω => shiftChart (pChart A C ψ ω) (n ω)) (min q₀ p)) h₀) ⊔
          Ito.nullSets P) M ∧
      ∀ (q : ℝ≥0) (ψ' : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P, ω ∈ A →
        ω ∈ Restart.DomainMarkov.avoidSet (fun t ω => segDriver (γ ω) t) (fun ω => capLife (γ ω)) ψ' q →
        ∀ hc : (shiftChart (pChart A C ψ ω) (n ω)).IsConformal, Chart.chartTransport hc 1 a (chiC κ) (M q ω) ψ' =
          ∫ z, couplingMean κ (fun s : ℝ => segDriver (γ ω) s.toNNReal) q
            (phaseProc κ ρL ρR (fun t ω => segDriver (γ ω) t) (geomLW (fun t ω => segDriver (γ ω) t) xL)
              (geomRW (fun t ω => segDriver (γ ω) t) xR) (δ q) ω q) z * ψ' z := by
  set c : Ω → Chart := fun ω => shiftChart (pChart A C ψ ω) (n ω) with hcdef
  have hprops := pChart_props hCo hCH hψ
  have hcc : ∀ ω, (c ω).IsConformal := fun ω => (hprops ω).2.2.1
  have hpch := isPocketChartOn_pChart (mΩ := 𝓦) hA hCo hCH hψ hCm hψm
  have hcOn : IsPocketChartOn 𝓦 A C ψ c := isPocketChartOn_shift hpch.1 hCm hn
  have hℓ : ∀ ω ∈ A, IsDerivLog (c ω).1 (fun z => pLog A C ψ ω z - n ω * (2 * π * I)) (c ω).dom ∧
      ∀ z ∈ (c ω).dom, (c ω).2.2 z = (pLog A C ψ ω z - n ω * (2 * π * I)).im := fun ω hω =>
    ⟨isDerivLog_sub_int (hpch.2 ω hω).1 (n ω), fun z hz => by
      change (pChart A C ψ ω).2.2 z - 2 * π * (n ω : ℝ) = _
      rw [im_sub_int_mul, (hpch.2 ω hω).2 z hz]⟩
  have hinj : ∀ ω ∈ A, InjOn (ψ ω) (C ω) := fun ω hω => (hψ ω hω).2.injOn
  have hpre : ∀ q : ℝ≥0, locPrefixSigma 𝓦 A γ q ≤ mΩ := PocketUnionPt.locPrefixSigma_le h𝓦 hA hγ hγm
  have hact : ∀ q : ℝ≥0, ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) → activeDom A γ c q ω = C ω ∩ (H \ F q ω) :=
    fun q ω hω hq => PocketUnionPt.activeDom_eq_inter hω hq (hcOn.1 ω hω).1 (hcOn.1 ω hω).2.1
      (hcOn.1 ω hω).2.2.1 (hinj ω hω) (hgeo q ω hω hq)
  have hlaw : ∀ q : ℝ≥0, PocketUnionPt.PocketStopLaw 𝓦 P A γ C (F q) h₀ (activeCompl A γ c q) q := fun q =>
    pocketStopLaw_activeCompl (hpre q) (hact q) hCo (hFo q) (hU q)
  have hloc : ∀ q, IsLocalSet (activeCompl A γ c q) h₀ P := fun q =>
    ((isLocalSet_tfae hh₀ (hlaw q).1 (hlaw q).2.1).out 1 4).1
      (IsHistoryAvoidanceLocal.isAvoidanceLocal (hlaw q).2.2.1)
  have h𝔥 : ∀ φ : TestOn upperHalfPlaneOpens, smoothDist upperHalfPlaneOpens u φ = ∫ z, u z * φ z :=
    smoothDist_eq_integral hu
  have hmeanAt : ∀ q : ℝ≥0, ∀ g : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean (activeCompl A γ c q) h₀ P g →
      ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (γ ω) → ∃ v : ℂ → ℝ, ContinuousOn v (C ω ∩ (H \ F q ω)) ∧
        (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ C ω ∩ (H \ F q ω) →
          (g ω + smoothDist upperHalfPlaneOpens u) φ = ∫ z, v z * φ z) ∧
        ∀ z ∈ C ω ∩ (H \ F q ω), v z + a + chiC κ * (c ω).2.2 z =
          couplingMean κ (fun s : ℝ => segDriver (γ ω) s.toNNReal) q
            (phaseProc κ ρL ρR (fun t ω => segDriver (γ ω) t) (geomLW (fun t ω => segDriver (γ ω) t) xL)
              (geomRW (fun t ω => segDriver (γ ω) t) xR) (δ q) ω q) ((c ω).1 z) := by
    intro q
    refine phaseMeanAt_of_phaseSideLimit hκ hh₀ (hlaw q).1 (hloc q) (fun ω hω hq => ?_)
      (fun ω hω hq => (hact q ω hω hq).symm) hγ (fun ω hω => ⟨(hcOn.1 ω hω).1, (hℓ ω hω).1, (hℓ ω hω).2⟩) hu hub
      h𝔥 (hside q)
    rw [activeCompl, sdiff_sdiff_cancel_left]
    rw [hact q ω hω hq]
    exact inter_subset_right.trans sdiff_subset
  have hgex : ∀ q, ∃ g, IsLocalSetMean (activeCompl A γ c q) h₀ P g := fun q =>
    IsLocalSet.exists_isLocalSetMean hh₀ (hlaw q).1 (hloc q)
  choose g hg using hgex
  have h𝓦ℋ : ∀ q : ℝ≥0, ∀ s, MeasurableSet[𝓦] s → MeasurableSet[locPrefixSigma 𝓦 A γ q] s :=
    fun q s hs => le_sup_left (b := MeasurableSpace.generateFrom _) _ hs
  -- the retained marks
  set ℋ : ℝ≥0 → MeasurableSpace Ω := fun p => locPrefixSigma 𝓦 A γ p ⊔ germSigma (activeCompl A γ c (min q₀ p)) h₀
    with hℋdef
  have hKpre : ∀ p : ℝ≥0, Measurable[locPrefixSigma 𝓦 A γ p, hittingSigma] (activeCompl A γ c (min q₀ p)) :=
    fun p => measurable_activeCompl_locPrefixSigma_of_le h𝓦 hA hγ hγm hCo hCH hψ hCm hψm hCin
      (fun ω hω => ⟨(hcOn.1 ω hω).1, (hcOn.1 ω hω).2.1, (hcOn.1 ω hω).2.2.1⟩) (min_le_right q₀ p)
  have hℋle : ∀ p, ℋ p ≤ mΩ := fun p =>
    sup_le (hpre p) (germSigma_le ((hKpre p).mono (hpre p) le_rfl) hh₀.measurable)
  have hℋloc : ∀ p, IsHistoryAvoidanceLocal (ℋ p) (activeCompl A γ c p) h₀ P := fun p =>
    Lemma725RefMarks.isHistoryAvoidanceLocal_sup_germSigma hh₀ (hpre p) (hlaw p).1 (hlaw p).2.2.1 (hKpre p)
      fun ω => inter_subset_left.trans (activeCompl_mono (min_le_right q₀ p) ω)
  have hUL : PocketUnionLaw 𝓦 P A γ c h₀ (fun q => activeCompl A γ c q) ℋ g := by
    intro q
    obtain ⟨hKm, -, -, hgeoK⟩ := hlaw q
    refine ⟨hKm, hℋle q, hloc q, hℋloc q, hg q, (le_sup_left.trans le_sup_right).trans le_sup_left, ?_, ?_⟩
    · exact (PocketUnionPt.measurable_compl_activeDom (h𝓦ℋ q _ hA) (PocketUnionPt.measurableSet_live A γ q) hCo
        (fun z => h𝓦ℋ q _ (hCm z)) (hact q) hgeoK).mono (sup_le_sup_left le_sup_left _) le_rfl
    · refine Eventually.of_forall fun ω => ?_
      by_cases hl : ω ∈ A ∧ (q : ℝ≥0∞) < capLife (γ ω)
      · rw [hact q ω hl.1 hl.2]
        obtain ⟨hfr, hF, hKC⟩ := hgeoK ω hl.1 hl.2
        refine ⟨fun z hz => ⟨hz.2.1, fun hzK => hz.2.2 (hKC ⟨hzK, hz.1⟩)⟩, fun z hz =>
          PocketUnionPt.connectedComponentIn_subset_inter (hCo ω hl.1) hfr (fun x hx => ?_) hz⟩
        refine hF ⟨?_, hx.1⟩
        by_contra hxF
        exact hx.2 ⟨hx.1, hxF⟩
      · rw [PocketUnionPt.activeDom_eq_empty hl]
        exact ⟨empty_subset _, fun z hz => hz.elim⟩
  have hpt : ∀ q : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (γ ω) → ∃ v : ℂ → ℝ,
      ContinuousOn v ((c ω).2.1 '' (H \ fwdHull (fun s : ℝ => segDriver (γ ω) s.toNNReal) q)) ∧
      (∀ φ : TestOn upperHalfPlaneOpens,
        tsupport φ ⊆ (c ω).2.1 '' (H \ fwdHull (fun s : ℝ => segDriver (γ ω) s.toNNReal) q) →
          (g q ω + smoothDist upperHalfPlaneOpens u) φ = ∫ z, v z * φ z) ∧
      ∀ w ∈ H \ fwdHull (fun s : ℝ => segDriver (γ ω) s.toNNReal) q,
        v ((c ω).2.1 w) + a + chiC κ * (c ω).2.2 ((c ω).2.1 w) =
          couplingMean κ (fun s : ℝ => segDriver (γ ω) s.toNNReal) q
            (phaseProc κ ρL ρR (fun t ω => segDriver (γ ω) t) (geomLW (fun t ω => segDriver (γ ω) t) xL)
              (geomRW (fun t ω => segDriver (γ ω) t) xR) (δ q) ω q) w := by
    intro q
    filter_upwards [hmeanAt q (g q) (hg q)] with ω hω hωA hq
    obtain ⟨v, hvc, hvrep, hvid⟩ := hω hωA hq
    have hE : (c ω).2.1 '' (H \ fwdHull (fun s : ℝ => segDriver (γ ω) s.toNNReal) q) = C ω ∩ (H \ F q ω) := by
      rw [← activeDom_eq hωA hq]
      exact hact q ω hωA hq
    refine ⟨v, by rw [hE]; exact hvc, fun φ hφ => hvrep φ (by rw [← hE]; exact hφ), fun w hw => ?_⟩
    have hz : (c ω).2.1 w ∈ C ω ∩ (H \ F q ω) := by
      rw [← hE]
      exact mem_image_of_mem _ hw
    have h := hvid _ hz
    rwa [(hcOn.1 ω hωA).1.2.2 w hw.1] at h
  refine ⟨_, pocketKernel_of_unionLaw hh₀ _ (fun _ => rfl) hUL, fun q ψ' => ?_⟩
  filter_upwards [hpt q] with ω hω hωA hav hc'
  obtain ⟨hq, hdisj⟩ := hav
  obtain ⟨v, hvc, hM, hid⟩ := hω hωA hq
  have hVo : IsOpen (H \ fwdHull (fun s : ℝ => segDriver (γ ω) s.toNNReal) q) :=
    Coupling.MartMeans2.isOpen_H_diff_fwdHull_rpath (hγ ω hωA).segDriver_spec.2.1 hq
  exact chartTransport_eq_of_pointwise hc' ((hcOn.1 ω hωA).2.2.2) a (chiC κ) hVo sdiff_subset hvc hM hid ψ'
    fun z hz => ⟨ψ'.tsupport_subset hz, fun h => hdisj.notMem_of_mem_left hz h⟩

end Retain

end InteractingSLE.Sec7.PhaseCont
