/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RdExt
import InteractingSLE.Spec.Supplement.RelSafeCore
import InteractingSLE.Spec.Supplement.GB6SourceCVersions
import InteractingSLE.Stochastic.Martingale.OptionalSampling
import InteractingSLE.Spec.Coupling.SafeFamily

/-!
# GW2's union locality, part 2: the extended flow driver is read from the stopped flow histories

Packet PROVE-GW2-RELDET (locality clause of `GW2Rd.HasGW2UnionLocality`). The physical σ-algebra of K2's lines reads
the EXTENDED flow driver `regW s Wα ζα` (frozen at its left limit from `ζα` on) at every time `r ≤ t`. The marks of the
union are the stopped σ-algebras of the flow at `t ∧ σₙ` (`σₙ ↑ ζα` announcing). This file shows that `regW r` is
measurable for `⨆ₙ 𝓕_{t ∧ σₙ}` and the null sets (`measurable_regW_iSup_stopping`):

* the killed driver set to `0` off a good event, `Y_u = Wα_u 1{u < ζα}`, is adapted and right continuous, hence
  progressive (`isStronglyProgressive_of_rightContinuous`), so its values at the stopping times `r ∧ σₙ ≤ t ∧ σₙ`
  are `𝓕_{t ∧ σₙ}`-measurable (`measurable_stoppedValue`);
* almost surely `regW r = limₙ Y_{r ∧ σₙ}`: for `r < ζα` the sequence is eventually `Wα_r`; for `ζα ≤ r` it is
  `Wα_{σₙ} → ` the left limit at `ζα`, which is `regW ζα = regW r` (the freezing and left-limit clauses of
  `StagedReg.isRegularDriver_regularize`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn)

namespace InteractingSLE.Theorem14.GW2Rd

open GW2TipSystem Supp8.GB6

section Drv

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {κ θ : ℝ} {b : ℝ → ℝ}
  {J : Finset ℝ} {h : Ω → DistOn upperHalfPlaneOpens} {Wα : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞}

/-- **The extended flow driver at `r ≤ t` is measurable for the stopped flow histories at `t ∧ σₙ` and the null
sets.** -/
theorem measurable_regW_iSup_stopping (hκ : 0 < κ) (hfl : IsFlowLineDriver κ b J θ P h Wα ζα)
    {𝓖 : Filtration ℝ≥0 mΩ} (hnull : ∀ N : Set Ω, MeasurableSet N → P N = 0 → MeasurableSet[𝓖 0] N)
    (hWad : ∀ (u : ℝ≥0) (A : Set ℝ), MeasurableSet A →
      MeasurableSet[𝓖 u] {ω | (u : ℝ≥0∞) < ζα ω ∧ Wα u ω ∈ A})
    {σ : ℕ → Ω → ℝ≥0} (hσ : Coupling.IsAnnouncingSeq 𝓖 P ζα σ) {t : ℝ≥0}
    (hτ : ∀ n, IsStoppingTime 𝓖 (fun ω => min (t : WithTop ℝ≥0) (σ n ω))) (s : ℝ≥0) {r : ℝ≥0}
    (hrt : r ≤ t) :
    Measurable[(⨆ n, (hτ n).measurableSpace) ⊔ Ito.nullSets P] (regW s Wα ζα r) := by
  classical
  -- the good event
  have hgood : ∀ᵐ ω ∂P, (Wα 0 ω = 0 ∧ ContinuousOn (fun u => Wα u ω) {u | (u : ℝ≥0∞) < ζα ω}) ∧
      (∀ n, (σ n ω : ℝ≥0∞) < ζα ω) ∧ (∀ u : ℝ≥0, (u : ℝ≥0∞) < ζα ω → ∃ n, u ≤ σ n ω) ∧
      (∀ T : ℝ≥0, (T : ℝ≥0∞) = ζα ω → 0 < T → ∃ w₀ : ℝ, Tendsto (fun u => Wα u ω) (𝓝[<] T) (𝓝 w₀)) := by
    filter_upwards [ae_driver_zero_continuousOn hfl, ae_all_iff.2 hσ.2.2.1, hσ.2.2.2,
      ae_tendsto_driver_at_lifetime hκ hfl] with ω h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  obtain ⟨G, hGm, hGae, hG⟩ := SourceC.exists_measurable_good hgood
  have hG0 : MeasurableSet[𝓖 0] G := by
    have hc : MeasurableSet[𝓖 0] Gᶜ := hnull _ hGm.compl (ae_iff.1 hGae)
    simpa only [compl_compl] using hc.compl
  -- the killed driver set to zero off the good event: adapted and right continuous
  set Y : ℝ≥0 → Ω → ℝ := fun u ω => if ω ∈ G ∧ (u : ℝ≥0∞) < ζα ω then Wα u ω else 0 with hYdef
  have hYad : StronglyAdapted 𝓖 Y := by
    intro u
    refine Measurable.stronglyMeasurable fun B hB => ?_
    have e : Y u ⁻¹' B = (G ∩ {ω | (u : ℝ≥0∞) < ζα ω ∧ Wα u ω ∈ B}) ∪
        ((G ∩ {ω | (u : ℝ≥0∞) < ζα ω ∧ Wα u ω ∈ univ})ᶜ ∩ {_ω | (0 : ℝ) ∈ B}) := by
      ext ω
      by_cases h1 : ω ∈ G <;> by_cases h2 : (u : ℝ≥0∞) < ζα ω <;> simp [hYdef, h1, h2]
    rw [e]
    have hGu : MeasurableSet[𝓖 u] G := 𝓖.mono (zero_le : (0 : ℝ≥0) ≤ u) _ hG0
    exact (hGu.inter (hWad u B hB)).union
      ((hGu.inter (hWad u univ MeasurableSet.univ)).compl.inter (MeasurableSet.const _))
  have hYrc : ∀ ω u, ContinuousWithinAt (fun v => Y v ω) (Ici u) u := by
    intro ω u
    by_cases hω : ω ∈ G
    · obtain ⟨⟨-, hc⟩, -⟩ := hG ω hω
      by_cases hu : (u : ℝ≥0∞) < ζα ω
      · have hopen : IsOpen {v : ℝ≥0 | (v : ℝ≥0∞) < ζα ω} := isOpen_lt ENNReal.continuous_coe continuous_const
        have hnb : {v : ℝ≥0 | (v : ℝ≥0∞) < ζα ω} ∈ 𝓝 u := hopen.mem_nhds hu
        have hca : ContinuousAt (fun v => Wα v ω) u := hc.continuousAt hnb
        have heq : (fun v => Wα v ω) =ᶠ[𝓝 u] fun v => Y v ω := by
          filter_upwards [hnb] with v hv
          have hv' : (v : ℝ≥0∞) < ζα ω := hv
          simp only [hYdef, hω, true_and, hv', ↓reduceIte]
        exact (hca.congr heq).continuousWithinAt
      · have heq : ∀ v ∈ Ici u, Y v ω = 0 := fun v hv => by
          have hv' : ¬ (v : ℝ≥0∞) < ζα ω := fun h' => hu (lt_of_le_of_lt (by exact_mod_cast hv) h')
          simp only [hYdef, hv', and_false, ↓reduceIte]
        exact (continuousWithinAt_const (b := (0 : ℝ))).congr heq (heq u (Set.mem_Ici.2 le_rfl))
    · have heq : ∀ v, Y v ω = 0 := fun v => by simp only [hYdef, hω, false_and, ↓reduceIte]
      exact (continuousWithinAt_const (b := (0 : ℝ))).congr (fun v _ => heq v) (heq u)
  have hprog := isStronglyProgressive_of_rightContinuous hYad hYrc
  -- the stopping times `r ∧ σₙ ≤ t ∧ σₙ`
  set ρ : ℕ → Ω → WithTop ℝ≥0 := fun n ω => min (r : WithTop ℝ≥0) (σ n ω) with hρdef
  have hρ : ∀ n, IsStoppingTime 𝓖 (ρ n) := fun n => (isStoppingTime_const 𝓖 r).min (hσ.1 n)
  have hρτ : ∀ n, (hρ n).measurableSpace ≤ (hτ n).measurableSpace := fun n =>
    (hρ n).measurableSpace_mono (hτ n) fun ω => min_le_min (WithTop.coe_le_coe.2 hrt) le_rfl
  have hZ : ∀ n, Measurable[⨆ m, (hτ m).measurableSpace] (stoppedValue Y (ρ n)) := fun n =>
    (measurable_stoppedValue hprog (hρ n)).mono ((hρτ n).trans (le_iSup (fun m => (hτ m).measurableSpace) n))
      le_rfl
  have hgm : Measurable[⨆ m, (hτ m).measurableSpace]
      (fun ω => limsup (fun n => stoppedValue Y (ρ n) ω) atTop) := Measurable.limsup hZ
  -- `regW r` is almost surely the limit of the stopped values
  have hae : ∀ᵐ ω ∂P, regW s Wα ζα r ω = limsup (fun n => stoppedValue Y (ρ n) ω) atTop := by
    filter_upwards [hGae] with ω hω
    obtain ⟨⟨h0, hc⟩, hlt, hreach, hlim⟩ := hG ω hω
    have hval : ∀ n, stoppedValue Y (ρ n) ω = regW s Wα ζα (min r (σ n ω)) ω := by
      intro n
      have hmin : ((min r (σ n ω) : ℝ≥0) : ℝ≥0∞) < ζα ω :=
        lt_of_le_of_lt (by exact_mod_cast min_le_right r (σ n ω)) (hlt n)
      have e : ρ n ω = ((min r (σ n ω) : ℝ≥0) : WithTop ℝ≥0) := by
        simp only [hρdef, WithTop.coe_min]
      simp only [stoppedValue, e, WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe, hYdef, hω,
        true_and, hmin, ↓reduceIte]
      exact (regW_eq_of_lt s h0 hc hmin).symm
    have htend : Tendsto (fun n => stoppedValue Y (ρ n) ω) atTop (𝓝 (regW s Wα ζα r ω)) := by
      simp only [hval]
      rcases lt_or_ge (r : ℝ≥0∞) (ζα ω) with hr | hr
      · obtain ⟨n₀, hn₀⟩ := hreach r hr
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_ge_atTop n₀] with n hn
        rw [min_eq_left (hn₀.trans (hσ.2.1 ω hn))]
      · -- finite lifetime at or before `r`
        have hfin : ζα ω ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hr
        set T : ℝ≥0 := (ζα ω).toNNReal with hTdef
        have hT : (T : ℝ≥0∞) = ζα ω := ENNReal.coe_toNNReal hfin
        have hσlt : ∀ n, σ n ω < T := fun n => by
          have := hlt n
          rw [← hT] at this
          exact_mod_cast this
        have hT0 : 0 < T := lt_of_le_of_lt (zero_le : (0 : ℝ≥0) ≤ σ 0 ω) (hσlt 0)
        obtain ⟨w₀, hw₀⟩ := hlim T hT hT0
        have hσT : Tendsto (fun n => σ n ω) atTop (𝓝[<] T) := by
          refine tendsto_nhdsWithin_iff.2 ⟨tendsto_order.2 ⟨fun a ha => ?_, fun c hc' =>
            Eventually.of_forall fun n => (hσlt n).trans hc'⟩, Eventually.of_forall fun n => hσlt n⟩
          obtain ⟨a', haa', ha'T⟩ := exists_between ha
          obtain ⟨n₀, hn₀⟩ := hreach a' (by rw [← hT]; exact_mod_cast ha'T)
          filter_upwards [eventually_ge_atTop n₀] with n hn
          exact lt_of_lt_of_le haa' (hn₀.trans (hσ.2.1 ω hn))
        have hW : Tendsto (fun n => Wα (σ n ω) ω) atTop (𝓝 w₀) := hw₀.comp hσT
        obtain ⟨-, -, hfrz, hleft⟩ :=
          StagedReg.isRegularDriver_regularize (s : ℝ≥0∞) (fun u => GW2JointKernel.cfKW Wα ζα u ω, ζα ω)
        rw [StagedReg.regularize_snd] at hfrz hleft
        have hregT : regW s Wα ζα T ω = w₀ := by
          have h1 : Tendsto (fun u => regW s Wα ζα u ω) (𝓝[<] T) (𝓝 w₀) := by
            refine hw₀.congr' ?_
            filter_upwards [self_mem_nhdsWithin] with u hu
            exact (regW_eq_of_lt s h0 hc (by rw [← hT]; exact_mod_cast hu)).symm
          exact hleft hfin (lt_of_lt_of_eq (by exact_mod_cast hT0) hT : (0 : ℝ≥0∞) < ζα ω) w₀ h1
        have hregr : regW s Wα ζα r ω = regW s Wα ζα T ω := hfrz r hr
        rw [hregr, hregT]
        refine hW.congr' (Eventually.of_forall fun n => ?_)
        have hσr : σ n ω ≤ r := (hσlt n).le.trans (by rw [← ENNReal.coe_le_coe, hT]; exact hr)
        show Wα (σ n ω) ω = regW s Wα ζα (min r (σ n ω)) ω
        rw [min_eq_right hσr]
        exact (regW_eq_of_lt s h0 hc (hlt n)).symm
    exact htend.limsup_eq.symm
  intro B hB
  refine Supp8.RelSafe.measurableSet_of_ae_eq
    (sup_le (iSup_le fun n => (hτ n).measurableSpace_le) (Ito.nullSets_le P)) le_sup_right
    ((measurable_regW hfl s r) hB) ((le_sup_left : (⨆ n, (hτ n).measurableSpace) ≤ _) _ (hgm hB)) ?_
  filter_upwards [hae] with ω hω
  apply propext
  simp only [mem_preimage, hω]

end Drv

end InteractingSLE.Theorem14.GW2Rd
