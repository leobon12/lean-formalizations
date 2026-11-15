/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2NdStop
import InteractingSLE.Spec.Supplement.SB2VsAdapt

/-!
# F2b′'s frozen drivers: adapted, with line-measurable safe events

Packet PROVE-AUX61-NOJUMP (round 21, D34, component D). For F2b′'s stop inputs `T` and a line filtration `𝓖` with
`𝓖 t = lineSigmaT t` (the statement's), mirroring SB2(1)'s `SB2VsAdapt`:

* `measurable_a_lineFilt`: the clock is measurable for `lineFiltC P 𝓖 t`;
* `exists_frozenLineReading`: below the clock, the frozen drivers are read from `lineFiltC P 𝓖 t`
  (`Vs.exists_frozen_reading` with `measurable_segDrv_line`);
* **`stronglyAdapted_W`**: each frozen driver is adapted to the time-changed completed line filtration;
* **`measurableSet_safe_stop`**: the safe event of a frozen driver for a closed set is a `lineFiltC P 𝓖 t` event.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Nd

open Vs Exist.StagedLaw Supp8.GB6 Supp8.GB6.HullId Supp8.GB6.RelDrv.Version Supp8.Q3Stop Sec7.PocketTraversal
  Sec7.Lemma71C Restart Exist Exist.Staged Lv Ms Mf WalkSide LocalSets Lk LuM Nc Dv

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {u : ℝ} {l : List (ℝ × ℝ≥0)} {k ℓ : ℕ} {ψ : ℝ}

namespace StopIn

variable (T : StopIn P κ b jumps E u l k ℓ ψ)
  (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
  (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
  (hlθ : ∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2))
  (hℓ : ℓ < (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length)
  (hwℓ : (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ]? = some (Sum.inl (-(Real.pi / 2), ⊤)))
  {𝓖 : Filtration ℝ≥0 mΩ} (h𝓖 : ∀ t, 𝓖 t = lineSigmaT κ b jumps E u l k ℓ t)

include T hE hER hℓ hwℓ h𝓖 in
theorem lineC0_le_lineFilt (t : ℝ≥0) : lineC0 P κ b jumps E u l k ℓ ≤ lineFiltC P 𝓖 t := by
  show mΩ ⊓ aeSigma (lineSigma0 κ b jumps E u l k ℓ) P ≤ mΩ ⊓ aeSigma (𝓖 t) P
  rw [h𝓖 t]
  exact inf_le_inf_left _ (WalkLaw.aeSigma_mono (lineSigma0_le_T (u := u) (l := l) (k := k) T.hb hE hER hℓ hwℓ t))

include hE hER hlθ hℓ hwℓ h𝓖 in
theorem measurable_a_lineFilt (t : ℝ≥0) : Measurable[lineFiltC P 𝓖 t] (T.S.a t) := by
  show Measurable[mΩ ⊓ aeSigma (𝓖 t) P] _
  rw [h𝓖 t]
  exact measurable_a_line T.hb hE hER hlθ hℓ hwℓ T.S t

include hE hER hlθ hℓ hwℓ h𝓖 in
/-- **The canonical driver below the clock is read from the completed line filtration.** -/
theorem measurable_Wr_line (t r : ℝ≥0) :
    Measurable[lineFiltC P 𝓖 t] ((T.Gs ∩ {ω | (r : ℝ≥0∞) < T.S.a t ω}).indicator (T.Wr r)) := by
  have e : (T.Gs ∩ {ω | (r : ℝ≥0∞) < T.S.a t ω}).indicator (T.Wr r) =
      T.Gr.indicator ((T.S.Eg ∩ {ω | (r : ℝ≥0∞) < T.S.a t ω}).indicator fun ω => segDrv (T.S.ρM ω) r) := by
    funext ω
    by_cases hω : ω ∈ T.Gs ∩ {ω | (r : ℝ≥0∞) < T.S.a t ω}
    · rw [indicator_of_mem hω, indicator_of_mem hω.1.2, indicator_of_mem (show ω ∈ T.S.Eg ∩
        {ω | (r : ℝ≥0∞) < T.S.a t ω} from ⟨hω.1.1, hω.2⟩)]
      unfold Wr
      rw [CoordB.drivenDriver_eq (lt_of_lt_of_le hω.2 (StageObj.a_le_capLife T.S hω.1.1 t))]
      rfl
    · rw [indicator_of_notMem hω]
      by_cases hG : ω ∈ T.Gr
      · rw [indicator_of_mem hG, indicator_of_notMem fun h' => hω ⟨⟨h'.1, hG⟩, h'.2⟩]
      · rw [indicator_of_notMem hG]
  rw [e]
  have h1 := measurable_segDrv_line T.hb hE hER hlθ hℓ hwℓ T.S t r
  have h2 : MeasurableSet[mΩ ⊓ aeSigma (lineSigmaT κ b jumps E u l k ℓ t) P] T.Gr :=
    Vf.measurableSet_cmpl_of_conull T.hGr (ae_iff.1 T.hGrae)
  show Measurable[mΩ ⊓ aeSigma (𝓖 t) P] _
  rw [h𝓖 t]
  exact h1.indicator h2

include hE hER hlθ hℓ hwℓ h𝓖 in
/-- **The frozen drivers read below the clock.** -/
theorem exists_frozenLineReading (m : ℕ) :
    ∃ Y : ℝ≥0 → ℝ≥0 → Ω → ℝ, (∀ q t : ℝ≥0, Measurable[lineFiltC P 𝓖 t] (Y q t)) ∧
      (∀ (q t : ℝ≥0) (ω : Ω), ω ∉ T.Gs → Y q t ω = 0) ∧
      ∀ (q t : ℝ≥0) (ω : Ω), ω ∈ T.Gs → (q : ℝ≥0∞) ≤ T.S.a t ω → Y q t ω = T.W m q ω := by
  have hex : ∀ q t : ℝ≥0, ∃ Y : Ω → ℝ, Measurable[lineFiltC P 𝓖 t] Y ∧ (∀ ω, ω ∉ T.Gs → Y ω = 0) ∧
      ∀ ω ∈ T.Gs, (q : ℝ≥0∞) ≤ T.S.a t ω → Y ω = T.Wr (min q (T.Vstop m ω).toNNReal) ω := fun q t =>
    exists_frozen_reading (T.lineC0_le_lineFilt hE hER hℓ hwℓ h𝓖 t _ T.measurableSet_Gs_line)
      (T.measurable_a_lineFilt hE hER hlθ hℓ hwℓ h𝓖 t) (T.measurable_Wr_line hE hER hlθ hℓ hwℓ h𝓖 t)
      (T.measurable_record_line.mono (T.lineC0_le_lineFilt hE hER hℓ hwℓ h𝓖 t) le_rfl)
      (measurable_stopRule m) (isPathRule_stopRule m) (U := fun ω => capLife (T.S.ρM ω))
      (fun ω _ => T.continuousOn_Wr ω) (fun ω hω => T.Vstop_lt hω) (fun ω _ => T.Wr_zero ω) q
  choose Y hYm hYoff hYon using hex
  exact ⟨Y, hYm, hYoff, fun q t ω hω hq => by rw [hYon q t ω hω hq, T.W_of_mem hω]⟩

include hE hER hlθ hℓ hwℓ h𝓖 in
/-- **Each frozen driver is adapted to the time-changed completed line filtration.** -/
theorem stronglyAdapted_W (m : ℕ) :
    StronglyAdapted (Tc.tcFilt (lineFiltC P 𝓖) T.S.a (T.measurable_a_lineFilt hE hER hlθ hℓ hwℓ h𝓖)) (T.W m) := by
  obtain ⟨Y, hYm, hYoff, hYon⟩ := T.exists_frozenLineReading hE hER hlθ hℓ hwℓ h𝓖 m
  refine Vf.stronglyAdapted_tcFilt_of_ae_read (P := P) (fun t s s' hs hs' he => Vf.cmpl_closed hs hs' he)
    (T.measurable_W m) Y hYm fun q t => Eventually.of_forall fun ω hq => ?_
  by_cases hω : ω ∈ T.Gs
  · exact (hYon q t ω hω hq).symm
  · rw [T.W_of_notMem hω, hYoff q t ω hω]

include hE hER hlθ hℓ hwℓ h𝓖 in
/-- **The safe event of a frozen driver for a closed set is an event of the completed line filtration.** -/
theorem measurableSet_safe_stop (m : ℕ) {K : Set ℂ} (hK : IsClosed K) (t : ℝ≥0) :
    MeasurableSet[lineFiltC P 𝓖 t] {ω | T.S.a t ω < T.V m ω ∧
      Disjoint K (fwdHull (fun s : ℝ => T.W m s.toNNReal ω) (T.S.a t ω).toNNReal)} := by
  classical
  obtain ⟨Y, hYm, hYoff, hYon⟩ := T.exists_frozenLineReading hE hER hlθ hℓ hwℓ h𝓖 m
  have ha := T.measurable_a_lineFilt hE hER hlθ hℓ hwℓ h𝓖 t
  have hGs := T.lineC0_le_lineFilt hE hER hℓ hwℓ h𝓖 t _ T.measurableSet_Gs_line
  set τ : Ω → ℝ≥0 := fun ω => (T.S.a t ω).toNNReal with hτdef
  have hτm : Measurable[lineFiltC P 𝓖 t] τ := ENNReal.measurable_toNNReal.comp ha
  set B : ℝ≥0 → Ω → ℝ := fun s ω => if ω ∈ T.Gs then T.W m (min s (τ ω)) ω else 0 with hBdef
  have hBm : ∀ s, Measurable[lineFiltC P 𝓖 t] (B s) := fun s =>
    Vm.measurable_stopped (T.continuous_W m) hτm (Y := fun v => Y v t) (fun v => hYm v t)
      (fun v ω hω hv => hYon v t ω hω (by
        by_cases htop : T.S.a t ω = ⊤
        · rw [htop]; exact le_top
        · rw [← ENNReal.coe_toNNReal htop]; exact ENNReal.coe_le_coe.2 hv))
      (fun v ω hω => hYoff v t ω hω) s
  have hBc : ∀ ω, Continuous fun s => B s ω := fun ω => by
    by_cases hω : ω ∈ T.Gs
    · simp only [hBdef, hω, ↓reduceIte]
      exact (T.continuous_W m ω).comp (continuous_id.min continuous_const)
    · simp only [hBdef, hω, ↓reduceIte]; exact continuous_const
  have hBpath : Measurable[lineFiltC P 𝓖 t] fun ω => fun s => B s ω :=
    @Measurable.of_eval Ω ℝ≥0 (fun _ => ℝ) (lineFiltC P 𝓖 t) _ _ hBm
  have hrec := T.measurable_record_line.mono (T.lineC0_le_lineFilt hE hER hℓ hwℓ h𝓖 t) le_rfl
  set S₁ : Set Ω := T.Gs ∩ {ω | T.S.a t ω ≠ ⊤} ∩
    {ω | ¬ stopRule m (T.record ω, fun s => B s ω) ≤ T.S.a t ω} ∩
    {ω | Disjoint K (fwdHull (QuantumZipper.drive 1 B ω) (τ ω))} with hS₁
  set S₂ : Set Ω := T.Gsᶜ ∩ {ω | T.S.a t ω < (((m : ℝ≥0) + 1 : ℝ≥0) : ℝ≥0∞) ∧
    Disjoint K (fwdHull (QuantumZipper.drive 1 (fun _ _ => (0 : ℝ)) ω) (τ ω))} with hS₂
  have hS₁m : MeasurableSet[lineFiltC P 𝓖 t] S₁ :=
    ((hGs.inter (measurableSet_eq_fun ha measurable_const).compl).inter
      (measurableSet_le ((measurable_stopRule m).comp (hrec.prodMk hBpath)) ha).compl).inter
      (Supp8.GB6LineL.measurableSet_disjoint_fwdHull_rand hBc hBm (measurable_coe_nnreal_real.comp hτm)
        (fun ω => (τ ω).2) hK)
  have hS₂m : MeasurableSet[lineFiltC P 𝓖 t] S₂ :=
    hGs.compl.inter ((measurableSet_lt ha measurable_const).inter
      (Supp8.GB6LineL.measurableSet_disjoint_fwdHull_rand (B := fun _ _ => (0 : ℝ)) (fun _ => continuous_const)
        (fun _ => measurable_const) (measurable_coe_nnreal_real.comp hτm) (fun ω => (τ ω).2) hK))
  have e : {ω | T.S.a t ω < T.V m ω ∧
      Disjoint K (fwdHull (fun s : ℝ => T.W m s.toNNReal ω) (T.S.a t ω).toNNReal)} = S₁ ∪ S₂ := by
    ext ω
    show (T.S.a t ω < T.V m ω ∧ _) ↔ (ω ∈ S₁ ∨ ω ∈ S₂)
    by_cases hω : ω ∈ T.Gs
    · have hnS₂ : ω ∉ S₂ := fun h' => h'.1 hω
      simp only [hnS₂, or_false, hS₁, mem_inter_iff, mem_ofPred_eq, hω, true_and]
      have hBW : ∀ s ≤ τ ω, B s ω = T.W m s ω := fun s hs => by
        simp only [hBdef, hω, ↓reduceIte, min_eq_left hs]
      have hhull : fwdHull (fun s : ℝ => T.W m s.toNNReal ω) (τ ω : ℝ) =
          fwdHull (QuantumZipper.drive 1 B ω) (τ ω : ℝ) := by
        rw [Vm.drive_one]
        refine YuanCorollary13.fwdHull_eq_of_eqOn_Icc ((T.continuous_W m ω).comp continuous_real_toNNReal)
          ((hBc ω).comp continuous_real_toNNReal) (τ ω).2 fun r hr => (hBW _ ?_).symm
        rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hr.1]
        exact hr.2
      have hVrec : T.V m ω = stopRule m (T.record ω, fun s => T.W m s ω) := rfl
      constructor
      · rintro ⟨hlt, hdisj⟩
        have htop : T.S.a t ω ≠ ⊤ := ne_top_of_lt hlt
        have hτa : (τ ω : ℝ≥0∞) = T.S.a t ω := ENNReal.coe_toNNReal htop
        refine ⟨⟨htop, ?_⟩, by rw [← hhull]; exact hdisj⟩
        rw [← hτa]
        intro hle
        have := (GW2Bh.pathRule_le_iff (isPathRule_stopRule m) (r := T.record ω) hBW).1 hle
        rw [hτa, ← hVrec] at this
        exact absurd hlt (not_lt.2 this)
      · rintro ⟨⟨htop, hnle⟩, hdisj⟩
        have hτa : (τ ω : ℝ≥0∞) = T.S.a t ω := ENNReal.coe_toNNReal htop
        refine ⟨?_, by rw [hhull]; exact hdisj⟩
        by_contra hle
        rw [not_lt, ← hτa, hVrec] at hle
        have h2 := (GW2Bh.pathRule_le_iff (isPathRule_stopRule m) (r := T.record ω) hBW).2 hle
        exact hnle (by rw [← hτa]; exact h2)
    · have hnS₁ : ω ∉ S₁ := fun h' => hω h'.1.1.1
      simp only [hnS₁, false_or, hS₂, mem_inter_iff, mem_compl_iff, hω, not_false_eq_true, true_and,
        mem_ofPred_eq, T.V_of_notMem hω]
      have hh : fwdHull (fun s : ℝ => T.W m s.toNNReal ω) (T.S.a t ω).toNNReal =
          fwdHull (QuantumZipper.drive 1 (fun _ _ => (0 : ℝ)) ω) (τ ω) := by
        rw [Vm.drive_one]; simp only [T.W_of_notMem hω]; rfl
      rw [hh]
  rw [e]
  exact hS₁m.union hS₂m

end StopIn

end InteractingSLE.Theorem14.SB.Nd
