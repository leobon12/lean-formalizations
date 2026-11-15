/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2VsCons

/-!
# The frozen drivers are adapted and their safe events are line events (D19, step 4)

Packet PROVE-AUX61-NOJUMP (decision D19). For SB2(1)'s stop data:

* **`exists_lineReading`**: the canonical driver below the clock, read from the completed line filtration
  (the stop data's `read`, i.e. `exists_segReading`), on a good event of the line filtration;
* **`stronglyAdapted_W`**: each frozen driver `W m` is adapted to the time-changed completed line filtration
  (`exists_frozen_reading`, `Vf.stronglyAdapted_tcFilt_of_ae_read`);
* **`measurableSet_safe_stop`**: for a closed set `K`, `{a t < V m ∧ K ∩ K_{a t}(W m) = ∅}` is an event of the
  completed line filtration at `t`: on the good event, the rule stop is compared with `a t` on the driver stopped at
  `a t` (`GW2Bh.pathRule_le_iff`), and off the entrance event the frozen driver is `0`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Vs

open Vr Vq Exist.Staged Exist.StagedLaw Lv Sec7.PocketTraversal Supp8.Q3Stop Supp8.GB6.HullId Sec7.Lemma71C

section

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u ψ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
  {u₀ : ℂ → ℝ}

namespace SB2StopData

variable {HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ} {I : K2LaunchInputs κ b jumps P h E k u ψ}
  {D : EntranceUnion κ b jumps P h E k u η ζ u₀} (S : SB2StopData HP I D)

/-- **The canonical driver below the clock, read from the completed line filtration.** -/
theorem exists_lineReading :
    ∃ Eg : Set Ω, (∀ t : ℝ≥0, MeasurableSet[D.lineFiltC HP t] Eg) ∧ Eg ⊆ S.Gs ∧
      (∀ᵐ ω ∂P, ω ∈ D.event → ω ∈ Eg) ∧
      ∀ t r : ℝ≥0, Measurable[D.lineFiltC HP t] ((Eg ∩ {ω | (r : ℝ≥0∞) < S.a t ω}).indicator (S.Wr r)) := by
  obtain ⟨Eg, hEg, hsub, hae, hlife, hZm⟩ := S.read
  refine ⟨Eg, hEg, hsub, hae, fun t r => ?_⟩
  have e : (Eg ∩ {ω | (r : ℝ≥0∞) < S.a t ω}).indicator (S.Wr r) =
      (Eg ∩ {ω | (r : ℝ≥0∞) < S.a t ω}).indicator fun ω => segDrv (S.ρ ω) r := by
    funext ω
    by_cases hω : ω ∈ Eg ∩ {ω | (r : ℝ≥0∞) < S.a t ω}
    · simp only [indicator_of_mem hω]
      have hG : ω ∈ S.Gs := hsub hω.1
      have hrU : (r : ℝ≥0∞) < Sec7.Lemma71C.capLife (S.ρ' ω) := by
        rw [S.ρ'_eq hG]; exact lt_of_lt_of_le hω.2 (hlife ω hω.1 t)
      simp only [Wr]
      rw [Supp8.GB6.CoordB.drivenDriver_eq hrU, S.ρ'_eq hG]
      rfl
    · simp only [indicator_of_notMem hω]
  rw [e]; exact hZm t r

include HP D in
theorem measurable_rec_line (t : ℝ≥0) : Measurable[D.lineFiltC HP t] (sb2Rec I : Ω → RecData) :=
  (measurable_sb2Rec I).mono (D.past_le_marks.trans (D.marks_le_lineFiltC HP t)) le_rfl

/-- **The frozen drivers read below the clock.** -/
theorem exists_frozenLineReading (m : ℕ) :
    ∃ (Eg : Set Ω) (Y : ℝ≥0 → ℝ≥0 → Ω → ℝ), (∀ t : ℝ≥0, MeasurableSet[D.lineFiltC HP t] Eg) ∧ Eg ⊆ S.Gs ∧
      (∀ᵐ ω ∂P, ω ∈ D.event → ω ∈ Eg) ∧ (∀ q t : ℝ≥0, Measurable[D.lineFiltC HP t] (Y q t)) ∧
      (∀ (q t : ℝ≥0) (ω : Ω), ω ∉ Eg → Y q t ω = 0) ∧
      ∀ (q t : ℝ≥0) (ω : Ω), ω ∈ Eg → (q : ℝ≥0∞) ≤ S.a t ω → Y q t ω = S.W m q ω := by
  obtain ⟨Eg, hEg, hsub, hae, hZ⟩ := S.exists_lineReading
  have hex : ∀ q t : ℝ≥0, ∃ Y : Ω → ℝ, Measurable[D.lineFiltC HP t] Y ∧ (∀ ω, ω ∉ Eg → Y ω = 0) ∧
      ∀ ω ∈ Eg, (q : ℝ≥0∞) ≤ S.a t ω → Y ω = S.Wr (min q (S.Vstop m ω).toNNReal) ω := fun q t =>
    exists_frozen_reading (hEg t) (S.ha t) (hZ t) (measurable_rec_line (HP := HP) (I := I) (D := D) t)
      (measurable_stopRule m) (isPathRule_stopRule m) (U := fun ω => Sec7.Lemma71C.capLife (S.ρ' ω))
      (fun ω _ => S.continuousOn_Wr ω)
      (fun ω hω => by rw [S.ρ'_eq (hsub hω)]; exact (S.sample (hsub hω) m).2.1) (fun ω _ => S.Wr_zero ω) q
  choose Y hYm hYoff hYon using hex
  exact ⟨Eg, Y, hEg, hsub, hae, hYm, hYoff, fun q t ω hω hq => by
    rw [hYon q t ω hω hq, S.W_of_mem (hsub hω)]⟩

/-- **Each frozen driver is adapted to the time-changed completed line filtration.** -/
theorem stronglyAdapted_W (m : ℕ) : StronglyAdapted (Tc.tcFilt (D.lineFiltC HP) S.a S.ha) (S.W m) := by
  obtain ⟨Eg, Y, -, hsub, hae, hYm, hYoff, hYon⟩ := S.exists_frozenLineReading m
  refine Vf.stronglyAdapted_tcFilt_of_ae_read (fun t s s' hs hs' he => Vf.lineFiltC_closed D HP t hs hs' he)
    (S.measurable_W m) Y hYm fun q t => ?_
  filter_upwards [hae] with ω hω hq
  by_cases hD : ω ∈ D.event
  · exact (hYon q t ω (hω hD) hq).symm
  · have hG : ω ∉ S.Gs := fun h' => hD (S.Gs_subset h')
    rw [S.W_of_notMem hG, hYoff q t ω fun h' => hG (hsub h')]

/-- **The safe event of a frozen driver for a closed set is an event of the completed line filtration.** -/
theorem measurableSet_safe_stop (m : ℕ) {K : Set ℂ} (hK : IsClosed K) (t : ℝ≥0) :
    MeasurableSet[D.lineFiltC HP t] {ω | S.a t ω < S.V m ω ∧
      Disjoint K (fwdHull (fun s : ℝ => S.W m s.toNNReal ω) (S.a t ω).toNNReal)} := by
  classical
  obtain ⟨Eg, Y, hEg, hsub, hae, hYm, hYoff, hYon⟩ := S.exists_frozenLineReading m
  have h𝒢le : D.lineFiltC HP t ≤ mΩ := (D.lineFiltC HP).le t
  set τ : Ω → ℝ≥0 := fun ω => (S.a t ω).toNNReal with hτdef
  have hτm : Measurable[D.lineFiltC HP t] τ := ENNReal.measurable_toNNReal.comp (S.ha t)
  -- the frozen driver stopped at the clock, read from the line filtration
  set B : ℝ≥0 → Ω → ℝ := fun s ω => if ω ∈ Eg then S.W m (min s (τ ω)) ω else 0 with hBdef
  have hBm : ∀ s, Measurable[D.lineFiltC HP t] (B s) := fun s =>
    Vm.measurable_stopped (S.continuous_W m) hτm (Y := fun v => Y v t) (fun v => hYm v t)
      (fun v ω hω hv => hYon v t ω hω (by
        by_cases htop : S.a t ω = ⊤
        · rw [htop]; exact le_top
        · rw [← ENNReal.coe_toNNReal htop]; exact ENNReal.coe_le_coe.2 hv))
      (fun v ω hω => hYoff v t ω hω) s
  have hBc : ∀ ω, Continuous fun s => B s ω := fun ω => by
    by_cases hω : ω ∈ Eg
    · simp only [hBdef, hω, ↓reduceIte]
      exact (S.continuous_W m ω).comp (continuous_id.min continuous_const)
    · simp only [hBdef, hω, ↓reduceIte]; exact continuous_const
  have hBpath : Measurable[D.lineFiltC HP t] fun ω => fun s => B s ω :=
    @Measurable.of_eval Ω ℝ≥0 (fun _ => ℝ) (D.lineFiltC HP t) _ _ hBm
  have hrec := measurable_rec_line (HP := HP) (I := I) (D := D) t
  have hEv𝒢 : MeasurableSet[D.lineFiltC HP t] D.event := D.marks_le_lineFiltC HP t _ (D.measurableSet_event HP)
  -- the line event
  set S₁ : Set Ω := Eg ∩ {ω | S.a t ω ≠ ⊤} ∩ {ω | ¬ stopRule m (sb2Rec I ω, fun s => B s ω) ≤ S.a t ω} ∩
    {ω | Disjoint K (fwdHull (QuantumZipper.drive 1 B ω) (τ ω))} with hS₁
  set S₂ : Set Ω := D.eventᶜ ∩ {ω | S.a t ω < stopRule m (sb2Rec I ω, fun _ => 0) ∧
    Disjoint K (fwdHull (QuantumZipper.drive 1 (fun _ _ => (0 : ℝ)) ω) (τ ω))} with hS₂
  have hS₁m : MeasurableSet[D.lineFiltC HP t] S₁ :=
    (((hEg t).inter (measurableSet_eq_fun (S.ha t) measurable_const).compl).inter
      (measurableSet_le ((measurable_stopRule m).comp (hrec.prodMk hBpath)) (S.ha t)).compl).inter
      (Supp8.GB6LineL.measurableSet_disjoint_fwdHull_rand hBc hBm (measurable_coe_nnreal_real.comp hτm)
        (fun ω => (τ ω).2) hK)
  have hS₂m : MeasurableSet[D.lineFiltC HP t] S₂ :=
    hEv𝒢.compl.inter ((measurableSet_lt (S.ha t) ((measurable_stopRule m).comp
      (hrec.prodMk measurable_const))).inter (Supp8.GB6LineL.measurableSet_disjoint_fwdHull_rand
        (B := fun _ _ => (0 : ℝ)) (fun _ => continuous_const) (fun _ => measurable_const)
        (measurable_coe_nnreal_real.comp hτm) (fun ω => (τ ω).2) hK))
  -- the event is ambient-measurable
  have hSm : MeasurableSet {ω | S.a t ω < S.V m ω ∧
      Disjoint K (fwdHull (fun s : ℝ => S.W m s.toNNReal ω) (S.a t ω).toNNReal)} := by
    have h1 := Supp8.GB6LineL.measurableSet_disjoint_fwdHull_rand (m := mΩ) (S.continuous_W m) (S.measurable_W m)
      (measurable_coe_nnreal_real.comp (ENNReal.measurable_toNNReal.comp ((S.ha t).mono h𝒢le le_rfl)))
      (fun ω => ((S.a t ω).toNNReal).2) hK
    simp only [Vm.drive_one] at h1
    exact (measurableSet_lt ((S.ha t).mono h𝒢le le_rfl) (S.measurable_V m)).inter h1
  refine Vf.lineFiltC_closed D HP t hSm (hS₁m.union hS₂m) ?_
  filter_upwards [hae] with ω hω
  apply propext
  show (S.a t ω < S.V m ω ∧ _) ↔ (ω ∈ S₁ ∨ ω ∈ S₂)
  by_cases hD : ω ∈ D.event
  · have hE := hω hD
    have hG := hsub hE
    have hnS₂ : ω ∉ S₂ := fun h' => h'.1 hD
    simp only [hnS₂, or_false, hS₁, mem_inter_iff, mem_ofPred_eq, hE, true_and]
    have hBW : ∀ s ≤ τ ω, B s ω = S.W m s ω := fun s hs => by
      simp only [hBdef, hE, ↓reduceIte, min_eq_left hs]
    have hhull : fwdHull (fun s : ℝ => S.W m s.toNNReal ω) (τ ω : ℝ) =
        fwdHull (QuantumZipper.drive 1 B ω) (τ ω : ℝ) := by
      rw [Vm.drive_one]
      refine YuanCorollary13.fwdHull_eq_of_eqOn_Icc ((S.continuous_W m ω).comp continuous_real_toNNReal)
        ((hBc ω).comp continuous_real_toNNReal) (τ ω).2 fun r hr => (hBW _ ?_).symm
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hr.1]
      exact hr.2
    have hVfin : S.V m ω ≠ ⊤ := by rw [S.V_eq hG]; exact (S.sample hG m).2.2.1
    constructor
    · rintro ⟨hlt, hdisj⟩
      have htop : S.a t ω ≠ ⊤ := ne_top_of_lt hlt
      have hτa : (τ ω : ℝ≥0∞) = S.a t ω := ENNReal.coe_toNNReal htop
      refine ⟨⟨htop, ?_⟩, by rw [← hhull]; exact hdisj⟩
      rw [← hτa]
      intro hle
      have := (GW2Bh.pathRule_le_iff (isPathRule_stopRule m) (r := sb2Rec I ω) hBW).1 hle
      rw [hτa] at this
      exact absurd hlt (not_lt.2 this)
    · rintro ⟨⟨htop, hnle⟩, hdisj⟩
      have hτa : (τ ω : ℝ≥0∞) = S.a t ω := ENNReal.coe_toNNReal htop
      refine ⟨?_, by rw [hhull]; exact hdisj⟩
      by_contra hle
      rw [not_lt, ← hτa] at hle
      exact hnle (by rw [← hτa]; exact (GW2Bh.pathRule_le_iff (isPathRule_stopRule m) (r := sb2Rec I ω) hBW).2 hle)
  · have hG : ω ∉ S.Gs := fun h' => hD (S.Gs_subset h')
    have hE : ω ∉ Eg := fun h' => hG (hsub h')
    have hnS₁ : ω ∉ S₁ := fun h' => hE h'.1.1.1
    have hW0 : (fun s => S.W m s ω) = fun _ => 0 := funext fun s => S.W_of_notMem hG s
    have hV0 : S.V m ω = stopRule m (sb2Rec I ω, fun _ => 0) := by simp only [V, hW0]
    simp only [hnS₁, false_or, hS₂, mem_inter_iff, mem_compl_iff, hD, not_false_eq_true, true_and,
      mem_ofPred_eq, hV0]
    have hh : fwdHull (fun s : ℝ => S.W m s.toNNReal ω) (S.a t ω).toNNReal =
        fwdHull (QuantumZipper.drive 1 (fun _ _ => (0 : ℝ)) ω) (τ ω) := by
      rw [Vm.drive_one]; simp only [S.W_of_notMem hG]; rfl
    rw [hh]

end SB2StopData

end

end InteractingSLE.Theorem14.SB.Vs
