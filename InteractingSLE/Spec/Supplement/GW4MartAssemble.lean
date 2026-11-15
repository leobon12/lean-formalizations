/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4MartComp
import InteractingSLE.Spec.Supplement.GW4SafeRNextAssemble

/-!
# GW4's protected martingales, part 7: the phase-word martingales of one actual component

Packet PROVE-GW4-MART. Astra's follow-up 3, Q3 §§3.4–3.7 (`ig1_followup3_audited.txt` L897–L1015) for the selected
GW4 component, on an **announced** version of its relative traversal (`IsGW4RelVersionA`):

1. the marked line locality gives the Gaussian line kernels given `𝒢L t = germ(B_t) ∨ ℋ_t`
   (`ae_condExp_cexp_boundary_marked`), and the boundary representation with a lattice phase constant in time
   (`ComponentPhaseRepresentation` with phase `c`) identifies their means as the coupling means of the phase word
   (`pairing_eq_couplingMean_phaseProc`);
2. the phase is read on every line (`exists_measurableSet_iff_phase_line`) and replaced by a measurable lattice-valued
   version `c'` that is an event of the line filtration at positive capacity times
   (`exists_measurable_phase_lineFilt`); the representation keeps holding for `c'`;
3. the phase-word law (S) in the line filtration (`hasPhaseSafeLaw_lineFilt`), then the phase clause at every
   stopping time of its usual augmentation (`PhaseClause.isPhaseCouplingCharFun_of_hasPhaseSafeLaw`; `c'` is
   measurable at time `0` by right continuity);
4. the announcing path rules of the version give an announcing sequence, and the coupling means of every family of
   phase-word extensions are local martingales before `s(z) ∧ V` (`isLocalMartingaleBefore_meanProc_phase`).

## Main results

* `ae_pairing_phase_line`, `componentPhaseRepresentation_congr`;
* **`exists_componentPhaseBefore`**: `ComponentPhaseBefore` (Aux. lemma 122's protected-martingale input) with the
  representation for its own phase, from the line locality and the representation with a lattice phase.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open QuantumZipper (H fwdHull fwdMap swallowTime)
open LQGMetric (TestOn DistOn)
open SupercriticalConformalCovariance.GM24 (smoothDist)
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW4Fix.Mart

open Coupling LocalSets WholeField Restart Restart.DomainMarkov Restart.DomainMarkov.Aux79 Sec7.PhaseSel
  Sec7.PhaseClause Sec7.PocketTraversal Supp8.Q3Stop Supp8.GB6.RelDrv Supp8.RelSafe MartChar

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {k : ℝ} {c₀ : BoundaryWord} {F : Frame} {ν : Measure Ω}
  {X : Ω → DistOn upperHalfPlaneOpens} {Wd R : ℝ≥0 → Ω → ℝ} {GT : Set Ω} {V : Ω → ℝ≥0∞}
  {hWm : ∀ r, Measurable (Wd r)} {u₀ : ℂ → ℝ} {ℋ : ℝ≥0 → MeasurableSpace Ω} {B : ℝ≥0 → Ω → Set ℂ}

/-- **The line means are the coupling means of the phase word** on the live lines. -/
theorem ae_pairing_phase_line (hk : 0 < k) (hRc : ∀ ω, Continuous fun t => R t ω) (hR0 : ∀ ω, R 0 ω = 0)
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hshape : ∀ t, ∀ᵐ ω ∂ν, lineClock F Wd GT V t ω < V ω →
      H \ B t ω = H \ fwdHull (fun r : ℝ => R r.toNNReal ω) (lineClock F Wd GT V t ω).toNNReal)
    {d : Ω → ℝ} (hrep : ComponentPhaseRepresentation k c₀ F ν X Wd GT R V u₀ B (fun _ ω => d ω))
    (t : ℝ≥0) {g : Ω → DistOn upperHalfPlaneOpens} (hg : IsLocalSetMean (B t) (centredField X u₀) ν g)
    (ψ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂ν, lineClock F Wd GT V t ω < V ω →
      Disjoint (tsupport ψ) (fwdHull (fun r : ℝ => R r.toNNReal ω) (lineClock F Wd GT V t ω).toNNReal) →
      (g ω + smoothDist upperHalfPlaneOpens u₀) ψ =
        ∫ z, couplingMean k (fun r : ℝ => R r.toNNReal ω) (lineClock F Wd GT V t ω).toNNReal
          (phaseProc k (typedRhoL (wordType k c₀)) (typedRhoR (wordType k c₀)) R (componentVL k c₀ X R V)
            (componentVR k c₀ X R V) d ω (lineClock F Wd GT V t ω).toNNReal) z * ψ z := by
  filter_upwards [hrep t g hg, hshape t] with ω h1 h2 hlt hψ
  obtain ⟨w, G, hw, hpair, hG, hm⟩ := h1 hlt
  exact pairing_eq_couplingMean_phaseProc hk ((hRc ω).comp continuous_real_toNNReal) (h2 hlt) hw hu₀ hpair hm hG
    (componentVL_le hRc hR0 ω _ _) (le_componentVR hRc hR0 ω _ _) hψ

omit mΩ in
/-- At coincident seeds the phase word does not see the phase. -/
theorem phaseData_eq_of_seeds_eq {nL nR : ℕ} (ρL : Fin (nL + 1) → ℝ) (ρR : Fin (nR + 1) → ℝ)
    {vL : Fin (nL + 1) → ℝ} {vR : Fin (nR + 1) → ℝ} (hs : vL 0 = vR 0) (d d' : ℝ) :
    phaseData k ρL ρR vL vR d = phaseData k ρL ρR vL vR d' := by
  funext x
  simp only [phaseData, hs, Ioo_self, indicator_empty, mul_zero, add_zero]

/-- **The boundary representation transfers to a phase that agrees on the live lines with positive clock value.** -/
theorem componentPhaseRepresentation_congr {d d' : Ω → ℝ}
    (hrep : ComponentPhaseRepresentation k c₀ F ν X Wd GT R V u₀ B (fun _ ω => d ω))
    (hdd : ∀ t, ∀ᵐ ω ∂ν, 0 < lineClock F Wd GT V t ω → lineClock F Wd GT V t ω < V ω → d' ω = d ω) :
    ComponentPhaseRepresentation k c₀ F ν X Wd GT R V u₀ B (fun _ ω => d' ω) := by
  intro t g hg
  filter_upwards [hrep t g hg, hdd t] with ω h1 h2 hlt
  obtain ⟨w, G, hw, hpair, hG, hm⟩ := h1 hlt
  refine ⟨w, G, hw, hpair, ?_, hm⟩
  by_cases hpos : 0 < lineClock F Wd GT V t ω
  · rw [h2 hpos hlt]
    exact hG
  · have h0 : lineClock F Wd GT V t ω = 0 := le_antisymm (not_lt.1 hpos) bot_le
    have hq : (lineClock F Wd GT V t ω).toNNReal = 0 := by rw [h0]; rfl
    rw [hq] at hG ⊢
    have hs := component_seeds_zero k c₀ X R V ω
    have heq := phaseData_eq_of_seeds_eq (k := k) (typedRhoL (wordType k c₀)) (typedRhoR (wordType k c₀))
      (vL := fun i => componentVL k c₀ X R V i 0 ω - R 0 ω) (vR := fun j => componentVR k c₀ X R V j 0 ω - R 0 ω)
      (congrArg (· - R 0 ω) (hs.1.trans hs.2.symm)) (d' ω) (d ω)
    convert hG using 1

/-- **Aux. lemma 122's protected-martingale input for one actual component.** On an announced version of the
relative traversal, the component line locality and the boundary representation of the line means with a lattice
phase `c` constant in time give `ComponentPhaseBefore` (the filtration: the usual augmentation of the line
filtration; the phase: a measurable lattice version of `c`) together with the boundary representation for its
phase. -/
theorem exists_componentPhaseBefore [IsProbabilityMeasure ν] (hk : 0 < k)
    (hX : IsGFFWithBoundaryData ν X c₀.fn c₀.jumps) (hF : F.IsOk)
    (hGT : ∀ ω ∈ GT, F.IsPathOk (fun r => Wd r ω)) (hGTm : MeasurableSet GT) (hGTae : ∀ᵐ ω ∂ν, ω ∈ GT)
    (hver : IsGW4RelVersionA ν Wd F.c F.C R V)
    (hloc : ComponentLineLocality c₀ F ν X Wd GT R V hWm u₀ ℋ B)
    {c : Ω → ℝ} (hlat : ∀ ω, ∃ j : ℤ, c ω = j * phaseStep k)
    (hrep : ComponentPhaseRepresentation k c₀ F ν X Wd GT R V u₀ B (fun _ ω => c ω)) :
    ∃ h : ComponentPhaseBefore k c₀ ν X R V,
      ComponentPhaseRepresentation k c₀ F ν X Wd GT R V u₀ B h.phase := by
  classical
  obtain ⟨hu₀, hphys, hℋ, hBm, hBc, hlocB, hshape⟩ := hloc
  have hverR : IsGW4RelVersionR ν Wd F.c F.C R V := hver.isGW4RelVersionR
  have hRm : ∀ t, Measurable (R t) := hver.1.1.1
  have hRc : ∀ ω, Continuous fun t => R t ω := hver.1.1.2.1
  have hR0 : ∀ ω, R 0 ω = 0 := hver.1.1.2.2.1
  have hVm : Measurable V := hver.1.1.2.2.2.1
  -- the line σ-algebras and the line means
  have hh0 := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hX hu₀
  have hl : ∀ t, IsLocalSet (B t) (centredField X u₀) ν := fun t =>
    ((isLocalSet_tfae hh0 (hBm t) (Eventually.of_forall (hBc t))).out 4 1).2 (hlocB t).isAvoidanceLocal
  choose g hg using fun t => IsLocalSet.exists_isLocalSetMean hh0 (hBm t) (hl t)
  let 𝒢L : ℝ≥0 → MeasurableSpace Ω := fun t => germSigma (B t) (centredField X u₀) ⊔ ℋ t
  have h𝒢L : ∀ t, physFilt Frame.measurable_gw4Rec hWm ν t ≤ 𝒢L t := fun t => (hphys t).trans le_sup_right
  have h𝒢Lm : ∀ t, 𝒢L t ≤ mΩ := fun t => sup_le (germSigma_le (hBm t) hh0.measurable) (hℋ t)
  have hnull : ∀ t, Ito.nullSets ν ≤ 𝒢L t := fun t =>
    (Supp8.RelSafe.nullSets_le_physFilt Frame.measurable_gw4Rec hWm ν t).trans (h𝒢L t)
  -- the physical clock
  have haa : ∀ t, Measurable[physFilt Frame.measurable_gw4Rec hWm ν t] (lineClock F Wd GT V t) :=
    Frame.measurable_min_physClockG hF hGT hWm hGTm hGTae hverR
  have hac : ∀ ω, Continuous fun t => lineClock F Wd GT V t ω := Frame.continuous_min_physClockG hF hGT
  have ham : ∀ ω, Monotone fun t => lineClock F Wd GT V t ω := Frame.monotone_min_physClockG hF hGT
  have ha0 : ∀ ω, lineClock F Wd GT V 0 ω = 0 := Frame.min_physClockG_zero hF hGT
  have hsafe : ∀ (C : Set ℂ), IsClosed C → ∀ t, MeasurableSet[physFilt Frame.measurable_gw4Rec hWm ν t]
      {ω | lineClock F Wd GT V t ω < V ω ∧
        Disjoint C (fwdHull (fun s : ℝ => R s.toNNReal ω) (lineClock F Wd GT V t ω).toNNReal)} :=
    fun C hC t => Frame.measurableSet_lineSafe hF hGT hWm hGTm hGTae hverR hC t
  have hltV : ∀ t, MeasurableSet[physFilt Frame.measurable_gw4Rec hWm ν t]
      {ω | lineClock F Wd GT V t ω < V ω} := by
    intro t
    have h := hsafe ∅ isClosed_empty t
    simpa only [empty_disjoint, and_true] using h
  have hA : ∀ q t, MeasurableSet[𝒢L t] (liveLine (lineClock F Wd GT V) V q t) := fun q t =>
    h𝒢L t _ ((measurableSet_le measurable_const (haa t)).inter (hltV t))
  -- the canonical relative filtration
  have hΦ : Measurable fun ω => componentPoint X R V ω :=
    measurable_const.prodMk (measurable_relVar hX.1 hRm hVm)
  have hcut : ∀ (d : ℝ≥0) (D : Set Ω), MeasurableSet[Coupling.filtrationComap canonFilt hΦ d] D → ∀ t,
      MeasurableSet[𝒢L t] ({ω | (d : ℝ≥0∞) ≤ lineClock F Wd GT V t ω} ∩ D) := by
    intro d D hD t
    rw [inter_comm]
    exact h𝒢L t _ (Frame.measurableSet_inter_le_min_of_canonFilt hF hGT hWm hGTm hGTae hverR hX.1 d hD t)
  have hRcan : ∀ t, R t = fun ω => canonDrv t (componentPoint X R V ω) := fun t =>
    funext fun ω => (relDrv_relVar (hRc ω) (hR0 ω) t).symm
  have hR𝓗 : ∀ t, Measurable[Coupling.filtrationComap canonFilt hΦ t] (R t) := fun t => by
    rw [hRcan t]
    exact (measurable_canonDrv_canonFilt le_rfl).comp (comap_measurable _)
  have hxL : Measurable[canonFilt 0] fun _ : CanonSpace => typedXL k (wordType k c₀) c₀ := measurable_const
  have hxR : Measurable[canonFilt 0] fun _ : CanonSpace => typedXR k (wordType k c₀) c₀ := measurable_const
  have hgL : ∀ i, StronglyAdapted canonFilt (geomLW canonDrv (fun _ => typedXL k (wordType k c₀) c₀) i) :=
    fun i => stronglyAdapted_geomLW stronglyAdapted_canonDrv (fun y => continuous_canonDrv y) hxL i
  have hgR : ∀ j, StronglyAdapted canonFilt (geomRW canonDrv (fun _ => typedXR k (wordType k c₀) c₀) j) :=
    fun j => stronglyAdapted_geomRW stronglyAdapted_canonDrv (fun y => continuous_canonDrv y) hxR j
  have hVL𝓗 : ∀ i t, Measurable[Coupling.filtrationComap canonFilt hΦ t] (componentVL k c₀ X R V i t) :=
    fun i t => ((hgL i t).measurable).comp (comap_measurable _)
  have hVR𝓗 : ∀ j t, Measurable[Coupling.filtrationComap canonFilt hΦ t] (componentVR k c₀ X R V j t) :=
    fun j t => ((hgR j t).measurable).comp (comap_measurable _)
  have htop : ∀ (Y : ℝ≥0 → Ω → ℝ), (∀ t, Measurable[Coupling.filtrationComap canonFilt hΦ t] (Y t)) →
      AdaptedBefore (Coupling.filtrationComap canonFilt hΦ) (fun _ => ⊤) Y := by
    intro Y hY t A hA
    have e : {ω | (t : ℝ≥0∞) < ⊤ ∧ Y t ω ∈ A} = Y t ⁻¹' A := by
      ext ω
      simp only [mem_ofPred_eq, mem_preimage, ENNReal.coe_lt_top, true_and]
    rw [e]
    exact hY t hA
  have hVLc : ∀ ω i, Continuous fun t => componentVL k c₀ X R V i t ω := fun ω i =>
    continuous_componentVL hRc hR0 ω i
  have hVRc : ∀ ω j, Continuous fun t => componentVR k c₀ X R V j t ω := fun ω j =>
    continuous_componentVR hRc hR0 ω j
  have hord : ∀ ω s, (∀ i, componentVL k c₀ X R V i s ω ≤ R s ω) ∧ ∀ j, R s ω ≤ componentVR k c₀ X R V j s ω :=
    fun ω s => ⟨fun i => componentVL_le hRc hR0 ω s i, fun j => le_componentVR hRc hR0 ω s j⟩
  -- the phase is read on every line
  have hread : ∀ (t : ℝ≥0) (Bs : Set ℝ), MeasurableSet Bs → ∃ S : Set Ω, MeasurableSet[𝒢L t] S ∧
      ∀ᵐ ω ∂ν, 0 < lineClock F Wd GT V t ω ∧ lineClock F Wd GT V t ω < V ω → (c ω ∈ Bs ↔ ω ∈ S) := by
    intro t Bs hBs
    have hμ : ∀ ψ : TestOn upperHalfPlaneOpens,
        Measurable[𝒢L t] fun ω => (g t ω + smoothDist upperHalfPlaneOpens u₀) ψ := by
      intro ψ
      have h1 : Measurable[𝒢L t] (g t) := (hg t).1.mono le_sup_left le_rfl
      have h2 : Measurable[𝒢L t] fun ω => g t ω ψ := (LQGMetric.measurable_distOn_apply ψ).comp h1
      simpa only [_root_.add_apply] using h2.add_const _
    exact exists_measurableSet_iff_phase_line (P := ν) hk (𝓗 := Coupling.filtrationComap canonFilt hΦ)
      (htop R hR𝓗) hRc (fun i => htop _ (hVL𝓗 i)) (fun j => htop _ (hVR𝓗 j)) hVLc hVRc hord
      (fun ω s hs => componentSeeds_lt hRc hR0 ω hs) ((haa t).mono (h𝒢L t) le_rfl)
      (fun d D hD => hcut d D hD t) hμ (L := {ω | 0 < lineClock F Wd GT V t ω ∧ lineClock F Wd GT V t ω < V ω})
      (fun ω hω => ⟨hω.1, ne_top_of_lt hω.2⟩)
      (fun ψ => (ae_pairing_phase_line hk hRc hR0 hu₀.1 hshape hrep t (hg t) ψ).mono fun ω h hω hdis =>
        h hω.2 hdis) hBs
  obtain ⟨c', hc'm, hc'lat, hc'eq, hc'filt⟩ := exists_measurable_phase_lineFilt h𝒢Lm hnull hac
    (fun t => (haa t).mono ((physFilt Frame.measurable_gw4Rec hWm ν).le t) le_rfl) hVm hA hlat hread
  have hrep' : ComponentPhaseRepresentation k c₀ F ν X Wd GT R V u₀ B (fun _ ω => c' ω) :=
    componentPhaseRepresentation_congr hrep hc'eq
  have hXψ : ∀ ψ : TestOn upperHalfPlaneOpens, Measurable fun ω => X ω ψ := fun ψ =>
    (LQGMetric.measurable_distOn_apply ψ).comp hX.1
  have hreg : ∀ ω, IsForceReg R (componentVL k c₀ X R V) (componentVR k c₀ X R V) V ω := fun ω =>
    ⟨hR0 ω, (hRc ω).continuousOn, fun i => (hVLc ω i).continuousOn, fun j => (hVRc ω j).continuousOn,
      fun s _ => hord ω s⟩
  -- the phase line laws
  have hline : ∀ (ψ : TestOn upperHalfPlaneOpens) (t : ℝ≥0), ∀ᵐ ω ∂ν, 0 < lineClock F Wd GT V t ω →
      lineClock F Wd GT V t ω < V ω →
      Disjoint (tsupport ψ) (fwdHull (fun s : ℝ => R s.toNNReal ω) (lineClock F Wd GT V t ω).toNNReal) →
      ν[fun ω => Complex.exp (Complex.I * (X ω ψ : ℂ)) | 𝒢L t] ω =
        cfAt k R (phaseProc k (typedRhoL (wordType k c₀)) (typedRhoR (wordType k c₀)) R (componentVL k c₀ X R V)
          (componentVR k c₀ X R V) c') ψ 1 (fun ω => (lineClock F Wd GT V t ω).toNNReal) ω := by
    intro ψ t
    filter_upwards [ae_condExp_cexp_boundary_marked hu₀.1 hh0 (hBm t) (hBc t) (hℋ t) (hlocB t) (hg t) ψ,
      hshape t, ae_pairing_phase_line hk hRc hR0 hu₀.1 hshape hrep' t (hg t) ψ] with ω hker hsh hpair _ hlt hdis
    rw [hker, hsh hlt, hpair hlt hdis]
    have hG := WholeField.loewnerGreenEnergy_rpath_eq_zeroGFFTestCov (w := (R · ω)) (ζ := ⊤)
      (hRc ω).continuousOn (hR0 ω) ENNReal.coe_lt_top ψ hdis
    rw [← hG]
    simp only [cfAt]
    congr 1
    push_cast
    ring
  have hlaw := hasPhaseSafeLaw_lineFilt hk (𝓖 := physFilt Frame.measurable_gw4Rec hWm ν) hXψ hac ham ha0 haa 𝒢L
    h𝒢L h𝒢Lm hA hsafe (fun q => Frame.reach_min_physClockG hF hGT hGTae hver.1.1 q) hreg c' hline
  -- the line filtration and its usual augmentation
  have h𝓜 : ∀ q D, MeasurableSet[Coupling.filtrationComap canonFilt hΦ q] D →
      MeasurableSet[lineFilt 𝒢L (lineClock F Wd GT V) V hA q] D := fun q D hD =>
    measurableSet_lineFilt_of_inter ((Coupling.filtrationComap canonFilt hΦ).le q _ hD)
      (fun t => by rw [inter_comm]; exact hcut q D hD t) (fun t => h𝒢L t _ (hltV t))
  have hV𝓜 : IsStoppingTime (lineFilt 𝒢L (lineClock F Wd GT V) V hA) V := isStoppingTime_lineFilt hVm
  have hab : ∀ (Y : ℝ≥0 → Ω → ℝ), (∀ t, Measurable[Coupling.filtrationComap canonFilt hΦ t] (Y t)) →
      AdaptedBefore (lineFilt 𝒢L (lineClock F Wd GT V) V hA) V Y := by
    intro Y hY t A hA'
    have e : {ω | (t : ℝ≥0∞) < V ω ∧ Y t ω ∈ A} = {ω | V ω ≤ (t : ℝ≥0∞)}ᶜ ∩ Y t ⁻¹' A := by
      ext ω
      simp only [mem_ofPred_eq, mem_inter_iff, mem_compl_iff, not_le, mem_preimage]
    rw [e]
    exact (hV𝓜 t).compl.inter (h𝓜 t _ (hY t hA'))
  set 𝓖 := usualAugmentation (lineFilt 𝒢L (lineClock F Wd GT V) V hA) ν with h𝓖
  have hle𝓖 := Ito.le_usualAugmentation (lineFilt 𝒢L (lineClock F Wd GT V) V hA) ν
  have hcm : Measurable[𝓖 0] c' := by
    intro Bs hBs
    exact measurableSet_zero_of_forall_pos (𝓕 := 𝓖) fun j hj => hle𝓖 j _ (hc'filt j hj Bs hBs)
  have hcf := isPhaseCouplingCharFun_of_hasPhaseSafeLaw hk hcm X hXψ hlaw (Eventually.of_forall hreg)
    (hab R hR𝓗) (fun i => hab _ (hVL𝓗 i)) (fun j => hab _ (hVR𝓗 j))
  -- the announcing sequence of the version
  obtain ⟨_, _, _, ρs, hρsm, hρs, hρsfin, hρsmono, hann⟩ := hver
  set T : ℕ → Ω → ℝ≥0 := fun n ω => (ρs n fun u => R u ω).toNNReal with hTdef
  have hTc : ∀ n ω, (T n ω : ℝ≥0∞) = ρs n fun u => R u ω := fun n ω => ENNReal.coe_toNNReal (hρsfin n _)
  have hTst : ∀ n, IsStoppingTime 𝓖 fun ω => (T n ω : WithTop ℝ≥0) := by
    intro n q
    refine hle𝓖 q _ ?_
    set Bq : Set (Exist.StagedLaw.RecData × (ℝ≥0 → ℝ)) := {p | ρs n p.2 ≤ (q : ℝ≥0∞)} with hBq
    have hBqm : MeasurableSet Bq := measurableSet_le ((hρsm n).comp measurable_snd) measurable_const
    have hdet : IsDetUpTo q Bq := by
      intro r w w' hww'
      simp only [hBq, mem_ofPred_eq]
      rw [pathRule_le_iff_freeze (hρs n) w, pathRule_le_iff_freeze (hρs n) w']
      have e : (fun u => w (min u (q : ℝ≥0∞).toNNReal)) = fun u => w' (min u (q : ℝ≥0∞).toNNReal) := by
        funext u
        exact hww' _ (by rw [ENNReal.toNNReal_coe]; exact min_le_right _ _)
      rw [e]
    have hC := measurableSet_canonFilt_of_detUpTo q hBqm hdet
    have hD : MeasurableSet[Coupling.filtrationComap canonFilt hΦ q]
        ((fun ω => componentPoint X R V ω) ⁻¹' {y : CanonSpace | (y.1, fun u => canonDrv u y) ∈ Bq}) :=
      ⟨_, hC, rfl⟩
    have e : {ω | (T n ω : WithTop ℝ≥0) ≤ (q : WithTop ℝ≥0)} =
        (fun ω => componentPoint X R V ω) ⁻¹' {y : CanonSpace | (y.1, fun u => canonDrv u y) ∈ Bq} := by
      ext ω
      simp only [mem_ofPred_eq, mem_preimage, hBq]
      rw [show (T n ω : WithTop ℝ≥0) = (T n ω : ℝ≥0∞) from rfl, hTc n ω]
      have hp : (fun u => canonDrv u (componentPoint X R V ω)) = fun u => R u ω := by
        funext u
        exact congrFun (hRcan u).symm ω
      rw [hp]
      rfl
    rw [e]
    exact h𝓜 q _ hD
  have hT : IsAnnouncingSeq 𝓖 ν V T := by
    refine ⟨hTst, fun ω n m hnm => ?_, fun n => ?_, ?_⟩
    · exact ENNReal.toNNReal_mono (hρsfin m _) (hρsmono _ hnm)
    · filter_upwards [hann] with ω hω
      rw [hTc]
      exact hω.1 n
    · filter_upwards [hann] with ω hω t ht
      rw [← hω.2] at ht
      obtain ⟨n, hn⟩ := lt_iSup_iff.1 ht
      refine ⟨n, ?_⟩
      rw [← ENNReal.coe_le_coe, hTc]
      exact hn.le
  have hint : ∀ φ : TestOn upperHalfPlaneOpens, Integrable (fun ω => X ω φ) ν := fun φ =>
    Supp8.HullDetGen.integrable_apply_of_isGFF c₀.isPiecewiseConstantBoundaryData hX φ
  have hnull𝓖 : ∀ s, MeasurableSet s → ν s = 0 → MeasurableSet[𝓖 0] s := fun s hs h0 =>
    Ito.measurableSet_usualAugmentation_of_null hs h0 0
  have hab𝓖 : ∀ (Y : ℝ≥0 → Ω → ℝ), (∀ t, Measurable[Coupling.filtrationComap canonFilt hΦ t] (Y t)) →
      AdaptedBefore 𝓖 V Y := fun Y hY t A hA' => hle𝓖 t _ (hab Y hY t A hA')
  have hR𝓖 : ∀ t, Measurable[𝓖 t] (R t) := fun t A hA' => hle𝓖 t _ (h𝓜 t _ (hR𝓗 t hA'))
  refine ⟨{ probability := inferInstance
            filtration := 𝓖
            rightContinuous := inferInstance
            adapted := fun t => (hR𝓖 t).stronglyMeasurable
            lifetimeStopping := fun q => hle𝓖 q _ (hV𝓜 q)
            phase := fun _ ω => c' ω
            value := c'
            positive_const := fun _ _ _ _ => rfl
            lattice := hc'lat
            martingales := ?_ }, hrep'⟩
  intro U hU z hz
  have hz0 : z ≠ 0 := fun h => by
    have : (0 : ℝ) < z.im := hz
    rw [h, Complex.zero_im] at this
    exact lt_irrefl _ this
  have hbhe : ∀ ω, Coupling.MartMeans.meanProc k R U z 0 ω =
      bheProc k (typedRhoL (wordType k c₀)) (typedRhoR (wordType k c₀)) R (componentVL k c₀ X R V)
        (componentVR k c₀ X R V) ω 0 z := by
    intro ω
    have hw0 : (fun s : ℝ => R s.toNNReal ω) 0 = 0 := by simp [hR0 ω]
    have h1 : Coupling.MartMeans.meanProc k R U z 0 ω = U ω 0 z := by
      simp only [Coupling.MartMeans.meanProc, NNReal.coe_zero]
      exact Coupling.MartMeans2.couplingMean_zero k hw0 (U ω 0) hz0
    have hs := component_seeds_zero k c₀ X R V ω
    have h2 := eqOn_bheProc_of_phase_zero_or_seed_eq (hU ω 0)
      (Or.inr (hs.1.trans hs.2.symm)) hz
    rw [h1, h2]
    rfl
  have hconst : ∀ ω ω', Coupling.MartMeans.meanProc k R U z 0 ω = Coupling.MartMeans.meanProc k R U z 0 ω' := by
    intro ω ω'
    rw [hbhe ω, hbhe ω']
    simp only [bheProc, componentVL_zero hRc hR0 ω, componentVR_zero hRc hR0 ω, componentVL_zero hRc hR0 ω',
      componentVR_zero hRc hR0 ω', hR0 ω, hR0 ω']
  have hu0 : Measurable[𝓖 0] (Coupling.MartMeans.meanProc k R U z 0) := by
    intro A _
    by_cases hA' : ∃ ω₀, Coupling.MartMeans.meanProc k R U z 0 ω₀ ∈ A
    · obtain ⟨ω₀, hω₀⟩ := hA'
      have e : Coupling.MartMeans.meanProc k R U z 0 ⁻¹' A = univ :=
        eq_univ_of_forall fun ω => by rw [mem_preimage, hconst ω ω₀]; exact hω₀
      rw [e]
      exact @MeasurableSet.univ Ω (𝓖 0)
    · have e : Coupling.MartMeans.meanProc k R U z 0 ⁻¹' A = ∅ :=
        eq_empty_of_forall_notMem fun ω hω => hA' ⟨ω, hω⟩
      rw [e]
      exact @MeasurableSet.empty Ω (𝓖 0)
  have hm := isLocalMartingaleBefore_meanProc_phase (𝓖 := 𝓖) hk hnull𝓖 (hab𝓖 R hR𝓗)
    (fun i => hab𝓖 _ (hVL𝓗 i)) (fun j => hab𝓖 _ (hVR𝓗 j))
    (Eventually.of_forall fun ω => ⟨hR0 ω, (hRc ω).continuousOn,
      ⟨fun i => (hVLc ω i).continuousOn, fun j => (hVRc ω j).continuousOn⟩, fun s _ => hord ω s⟩)
    hT hint hcm hcf U hU hz hu0
  exact Sec7.PhaseSelAdapt.isLocalMartingaleBefore_congr_life (fun ω => min_comm _ _) hm

end InteractingSLE.Theorem14.GW4Fix.Mart
