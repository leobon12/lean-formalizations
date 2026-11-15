/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBLuPath
import InteractingSLE.Spec.Supplement.SB4RPath
import InteractingSLE.Spec.Supplement.SBLuAmb

/-!
# Upper schedule prefixes are paths with finite fibres; pinch-finiteness at the upper launch charts

Packet PROVE-T14-SB2LIFT. Lemma S2's lift (`s2LiftStatement`, reflected `Lk.s2LiftRight`) needs a continuous
finite-fibre extension of the launch chart's inverse. For a boundary walk this is PROVE-T14-SBLEAVES6's
`LuM.pinv_prefix_walk` + `LuM.finite_fibre_bdry_walk`. Here the same for the schedule histories of the upper flow:

* `finite_fibre_of_pinv`: a domain chart of `ℍ ∖ fill X` whose inverse has a continuous extension with linear growth
  has finite fibres on `ℍ̄` as soon as `X` (with a real set) is the image of a path with finite fibres (`LuM.PInv`);
* **`pinv_schedule`** (deterministic): the schedule history from a seed `x₀ ≤ 0` through `k` instructions, with the
  bridge `[x₀, 0]`, is a finite-fibre prefix path from `0` (or `{0}`), when the launched pieces are regular with
  injective generating traces: each new piece is `t ↦ g(α t)` with `α` injective and `g` the boundary map of the launch
  chart, which has finite fibres by induction; it starts at the current tip, the radial limit of the chart at `0`
  (`Lf.exists_path_schedule_seed`);
* **`finite_fibre_schedule`**: hence the boundary map of every launch chart of the schedule has finite fibres.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdMapInv)

namespace InteractingSLE.Theorem14.SB.Lk

open Exist Exist.Staged Exist.StagedLaw GW2Schedule GW1P CounterflowRange OwnHistoryPath LuM

/-! ### Pinch-finiteness from a finite-fibre path -/

/-- **Pinch-finiteness from a finite-fibre path**: if `X ∪ U` (`U` real) is a finite-fibre prefix path (or a point),
the boundary map of a chart of `ℍ ∖ fill X` with linear growth has finite fibres on `ℍ̄`. -/
theorem finite_fibre_of_pinv {v : ℝ} {X : Set ℂ} {U : Set ℝ} (hA : PInv v (X ∪ ((↑) : ℝ → ℂ) '' U)) {c : Chart}
    (hD : IsDomainChart (H \ fillH X) c) {g : ℂ → ℂ} (hgc : ContinuousOn g {z | 0 ≤ z.im})
    (hgi : EqOn g c.2.1 H) (hgb : ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ ∀ w : ℂ, 0 ≤ w.im → ‖w‖ ≤ C₁ * ‖g w‖ + C₂) :
    ∀ z, (g ⁻¹' {z} ∩ {v | 0 ≤ v.im}).Finite := by
  obtain ⟨p, hpc, hpf, hfill⟩ : ∃ p : ℝ → ℂ, ContinuousOn p (Icc 0 1) ∧ (∀ z, (p ⁻¹' {z} ∩ Icc 0 1).Finite) ∧
      fillH (p '' Icc 0 1) = fillH X := by
    rcases hA with hA | ⟨p, hp⟩
    · -- `X` is contained in a single real point: its fill is that of the empty set
      have hX : X = ((↑) : ℝ → ℂ) '' {x : ℝ | (x : ℂ) ∈ X} := by
        ext z
        constructor
        · intro hz
          have hz' : z ∈ ({(v : ℂ)} : Set ℂ) := hA ▸ Or.inl hz
          rw [mem_singleton_iff] at hz'
          exact ⟨v, by rw [mem_ofPred_eq, ← hz']; exact hz, hz'.symm⟩
        · rintro ⟨x, hx, rfl⟩; exact hx
      refine ⟨segPath 0 1, (isFFPath_segPath zero_ne_one).1, (isFFPath_segPath zero_ne_one).2.1, ?_⟩
      rw [image_segPath zero_ne_one, hX, fillH_ofReal, fillH_ofReal]
    · exact ⟨p, hp.1, hp.2.2.1, by rw [hp.2.2.2.2, Lw.fillH_union_real]⟩
  rw [← hfill] at hD
  obtain ⟨C₁, C₂, -, hb⟩ := hgb
  have hM : 0 < max C₁ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hinf : Tendsto g (Bornology.cobounded ℂ ⊓ 𝓟 H) (Bornology.cobounded ℂ) := by
    refine tendsto_norm_atTop_iff_cobounded.1 (tendsto_atTop_mono' _ ?_
      ((Tendsto.atTop_div_const hM (tendsto_atTop_add_const_right _ (-C₂)
        tendsto_norm_cobounded_atTop)).mono_left inf_le_left))
    refine eventually_inf_principal.2 (Eventually.of_forall fun w hw => ?_)
    have h1 := hb w (le_of_lt (show (0 : ℝ) < w.im from hw))
    have h2 : C₁ * ‖g w‖ ≤ max C₁ 1 * ‖g w‖ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
    rw [div_le_iff₀ hM]
    linarith
  exact Lv.finite_fibre_of_isDomainChart hpc hpf hD hgc hgi hinf

/-! ### Schedule histories are finite-fibre paths -/

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- **Injective generating traces at the launches of a run.** -/
def InjLaunches (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) : Prop :=
  ∀ (k : ℕ) (c : Chart) (θ : ℝ), (ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 k = some (c, θ) →
    ∀ α : ℝ≥0 → ℂ, IsGeneratingTrace (D k).1 (min (instrTime spec k) (D k).2) α →
      InjOn α {t : ℝ≥0 | (t : ℝ≥0∞) ≤ min (instrTime spec k) (D k).2}

/-- **The schedule history from a seed `x₀ ≤ 0`, with the bridge `[x₀, 0]`, is a finite-fibre prefix path from `0`**
(or the point `0`) when the launched pieces are regular with injective generating traces. -/
theorem pinv_schedule {x₀ : ℝ} (hx₀ : x₀ ≤ 0) (l : List (ℝ × ℝ≥0)) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hreg : ∀ (k : ℕ) (c : Chart) (θ : ℝ),
      (ExplState.run κ b jumps (Lf.sspec x₀ l) D (k + 1)).2.2.2.1 k = some (c, θ) →
      PieceRegular (D k).1 (min (instrTime (Lf.sspec x₀ l) k) (D k).2))
    (hinj : InjLaunches κ b jumps (Lf.sspec x₀ l) D) :
    ∀ k : ℕ, PInv 0 (SB.prefixPhysSet κ b jumps (Lf.sspec x₀ l) D k ∪ ((↑) : ℝ → ℂ) '' Icc x₀ 0) := by
  intro k
  induction k with
  | zero =>
    have e0 : SB.prefixPhysSet κ b jumps (Lf.sspec x₀ l) D 0 = {(x₀ : ℂ)} := by
      unfold SB.prefixPhysSet
      simp [ExplState.run, ExplState.init]
    have hmem : (x₀ : ℂ) ∈ ((↑) : ℝ → ℂ) '' Icc x₀ 0 := ⟨x₀, ⟨le_rfl, hx₀⟩, rfl⟩
    rw [e0, union_eq_right.2 (singleton_subset_iff.2 hmem)]
    rcases hx₀.lt_or_eq with hlt | heq
    · refine Or.inr ⟨segPath 0 x₀, (isFFPath_segPath (ne_of_gt hlt)).1, by rw [segPath_zero, Complex.ofReal_zero],
        (isFFPath_segPath (ne_of_gt hlt)).2.1, (isFFPath_segPath (ne_of_gt hlt)).2.2, ?_⟩
      rw [image_segPath (ne_of_gt hlt), min_eq_right hlt.le, max_eq_left hlt.le]
    · left
      rw [heq, Icc_self, image_singleton, Complex.ofReal_zero]
  | succ k ih =>
  set U : Set ℂ := ((↑) : ℝ → ℂ) '' Icc x₀ 0 with hU
  by_cases hk : k < (scheduleProgram 0 l).length
  swap
  · have e : SB.prefixPhysSet κ b jumps (Lf.sspec x₀ l) D (k + 1) = SB.prefixPhysSet κ b jumps (Lf.sspec x₀ l) D k := by
      unfold SB.prefixPhysSet
      simp only []
      rw [Lf.run_succ_sspec_of_le x₀ l D (not_lt.1 hk)]
    rw [e]; exact ih
  by_cases hs : AllSucc (schedDelta 0 l) D k
  swap
  · rw [Lf.prefixPhysSet_succ_of_not_allSucc_sspec x₀ l D hk hs]; exact ih
  -- the current tip and the launch chart
  obtain ⟨x, Γ, hrange, -, -, hlim⟩ := Lf.exists_path_schedule_seed (κ := κ) (b := b) (jumps := jumps) x₀ l D hreg k
  obtain ⟨hmaps, hx⟩ := hlim hk.le hs
  have hxA : x ∈ SB.prefixPhysSet κ b jumps (Lf.sspec x₀ l) D k ∪ U := by
    have hxΓ : x ∈ range Γ := ⟨1, Γ.target⟩
    rw [hrange] at hxΓ
    exact Or.inl hxΓ
  have hrun := run_gw2 (κ := κ) (b := b) (jumps := jumps) (spec := Lf.sspec x₀ l) rfl
    (isFlowProg_scheduleProgram 0 l) (schedDelta_ne_top 0 l) D k hk.le
  have hl := (launches_run_gw2 (κ := κ) (b := b) (jumps := jumps) (spec := Lf.sspec x₀ l) rfl
    (isFlowProg_scheduleProgram 0 l) (schedDelta_ne_top 0 l) D hk).1 hs
  have hr := hreg k _ _ hl
  have hinjk := hinj k _ _ hl
  rw [Lf.instrTime_sspec x₀ l hk] at hr hinjk
  have h3 : (ExplState.run κ b jumps (Lf.sspec x₀ l) D k).2.2.2.2.1 = succChart x₀ (schedDelta 0 l) D k :=
    (hrun.1 hs).2
  have hgood : HasProperBdryExt (succChart x₀ (schedDelta 0 l) D k) := by
    have h1 := (isClosed_pieces_run (κ := κ) (b := b) (jumps := jumps) (Lf.sspec x₀ l) D hreg k).1
    rwa [h3] at h1
  have hconf : (succChart x₀ (schedDelta 0 l) D k).IsConformal := by
    have := (GW2aCont.isConformal_runChart (κ := κ) (b := b) (jumps := jumps) (Lf.sspec x₀ l) D k
      fun j _ c θ h => hreg j c θ h).1
    rwa [h3] at this
  have hdom := Lw.isDomainChart_runChart (κ := κ) (b := b) (jumps := jumps) (Lf.sspec x₀ l) D hreg k
    (Lx.stStatus_ne_done_of_launches _ D hl)
  have hdom' : IsDomainChart (H \ fillH (SB.prefixPhysSet κ b jumps (Lf.sspec x₀ l) D k))
      (succChart x₀ (schedDelta 0 l) D k) := by
    have h3' : stChart (ExplState.run κ b jumps (Lf.sspec x₀ l) D k) = succChart x₀ (schedDelta 0 l) D k := h3
    rw [← h3']; exact hdom
  obtain ⟨g, hgc, hgi, hgb, hgt⟩ := Lw.exists_bdryMap_of_hasProperBdryExt hconf hgood
  have hfib := finite_fibre_of_pinv ih hdom' hgc hgi hgb
  obtain ⟨hW0, hWc, α, hα, -⟩ := hr
  set S := min (schedDelta 0 l k) (D k).2 with hSdef
  have hSne : S ≠ ⊤ := ne_top_of_le_ne_top (schedDelta_ne_top 0 l k) (min_le_left _ _)
  have hαH : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ S → α t ∈ Hbar := fun t ht =>
    Sec7.IsGeneratingTrace.mem_Hbar hα (hWc.mono fun _ (hs : _ < S) => (le_of_lt hs : _ ≤ S)) hW0 ht
  have hgH : ∀ z ∈ H, g z ∈ H := fun z hz => by rw [hgi hz]; exact hmaps z hz
  have hg0 : g 0 = x := by
    have h0 : (0 : ℂ) ∈ Hbar := by
      change (0 : ℝ) ≤ (0 : ℂ).im
      rw [Complex.zero_im]
    exact tendsto_nhds_unique ((hgt 0 h0).comp tendsto_mul_I_nhdsWithin_H) hx
  have htip := tipSet_stopped_eq_of_tendsto hα hWc hW0 fun t ht => hgt _ (hαH t ht)
  rw [Lf.prefixPhysSet_succ_of_allSucc_sspec x₀ l D hk hs, htip]
  have e : SB.prefixPhysSet κ b jumps (Lf.sspec x₀ l) D k ∪ g '' (α '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ S}) ∪ U =
      (SB.prefixPhysSet κ b jumps (Lf.sspec x₀ l) D k ∪ U) ∪ g '' (α '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ S}) := by
    ext z; simp only [mem_union]; tauto
  rw [e]
  set T : ℝ≥0 := S.toNNReal with hTdef
  have hTS : (T : ℝ≥0∞) = S := ENNReal.coe_toNNReal hSne
  have hset : {t : ℝ≥0 | (t : ℝ≥0∞) ≤ S} = Iic T := by
    ext t; rw [mem_ofPred_eq, mem_Iic, ← hTS, ENNReal.coe_le_coe]
  rw [hset]
  rcases eq_or_ne T 0 with hT0 | hT0
  · refine ih.union_of_subset ?_
    rintro _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩
    rw [hT0, mem_Iic, nonpos_iff_eq_zero] at ht
    rw [ht, hα.1, hg0]
    exact hxA
  · have hle : ∀ s : ℝ≥0, s ≤ T → (s : ℝ≥0∞) ≤ S := fun s hs => hTS ▸ ENNReal.coe_le_coe.2 hs
    set φ : ℝ≥0 → ℂ := fun s => g (α s) with hφ
    have hcont : ContinuousOn φ (Iic T) :=
      hgc.comp (hα.2.1.mono fun s (hs : s ≤ T) => hle s hs) fun s (hs : s ≤ T) => hαH s (hle s hs)
    have hf : ∀ z, {s | s ≤ T ∧ φ s = z}.Finite := by
      intro z
      refine Finite.of_finite_image ((hfib z).subset ?_) ((hinjk α hα).mono fun s hs => hle s hs.1)
      rintro _ ⟨s, ⟨hs, hsz⟩, rfl⟩
      exact ⟨hsz, hαH s (hle s hs)⟩
    have hH : ∀ s ≤ T, 0 ≤ (φ s).im := fun s hs =>
      mem_Hbar_of_tendsto (hαH s (hle s hs)) hmaps (hgt _ (hαH s (hle s hs)))
    obtain ⟨hq, hqi⟩ := isFFPath_reparam (pos_iff_ne_zero.2 hT0) hcont hf hH
    have hq0 : (fun t : ℝ => φ (t * T).toNNReal) 0 ∈ SB.prefixPhysSet κ b jumps (Lf.sspec x₀ l) D k ∪ U := by
      simp only [zero_mul, Real.toNNReal_zero, hφ, hα.1, hg0]
      exact hxA
    have := ih.join hq hq0
    rwa [hqi, show φ '' Iic T = g '' (α '' Iic T) from (image_image g α (Iic T)).symm] at this

/-- **Pinch-finiteness at the launch charts of a schedule**: at every launch of the schedule from `x₀ ≤ 0` (regular
pieces, injective traces) every continuous extension of the launch chart's inverse to `ℍ̄` with linear growth has
finite fibres. -/
theorem finite_fibre_schedule {x₀ : ℝ} (hx₀ : x₀ ≤ 0) (l : List (ℝ × ℝ≥0)) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hreg : ∀ (k : ℕ) (c : Chart) (θ : ℝ),
      (ExplState.run κ b jumps (Lf.sspec x₀ l) D (k + 1)).2.2.2.1 k = some (c, θ) →
      PieceRegular (D k).1 (min (instrTime (Lf.sspec x₀ l) k) (D k).2))
    (hinj : InjLaunches κ b jumps (Lf.sspec x₀ l) D) {k : ℕ} {c : Chart} {θ : ℝ}
    (hl : (ExplState.run κ b jumps (Lf.sspec x₀ l) D (k + 1)).2.2.2.1 k = some (c, θ)) {g : ℂ → ℂ}
    (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g c.2.1 H)
    (hgb : ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ ∀ w : ℂ, 0 ≤ w.im → ‖w‖ ≤ C₁ * ‖g w‖ + C₂) :
    ∀ z, (g ⁻¹' {z} ∩ {v | 0 ≤ v.im}).Finite := by
  have hc := (eq_launch_of_launches (κ := κ) (b := b) (jumps := jumps) _ D hl).2.2
  have hdom := Lw.isDomainChart_runChart (κ := κ) (b := b) (jumps := jumps) (Lf.sspec x₀ l) D hreg k
    (Lx.stStatus_ne_done_of_launches _ D hl)
  have hdom' : IsDomainChart (H \ fillH (SB.prefixPhysSet κ b jumps (Lf.sspec x₀ l) D k)) c := by
    have hsc : stChart (ExplState.run κ b jumps (Lf.sspec x₀ l) D k) = c := hc.symm
    rw [← hsc]; exact hdom
  exact finite_fibre_of_pinv (pinv_schedule hx₀ l D hreg hinj k) hdom' hgc hgi hgb

/-! ### Injective traces at the launches, almost surely -/

/-- Separation is inherited by a shorter horizon. -/
theorem sepAt_mono {A : ℝ≥0 → ℂ} {S S' : ℝ≥0∞} (hSS : S ≤ S') (h : GW1Z.SepAt A S') : GW1Z.SepAt A S := by
  intro b c d hbc hcS
  obtain ⟨n, hn⟩ := h b c d hbc (lt_of_lt_of_le hcS hSS)
  exact ⟨n, fun u v hu hv hvd hvS => hn u v hu hv hvd (lt_of_lt_of_le hvS hSS)⟩

/-- **Separation of the canonical trace of a driver makes every generating trace of an agreeing driver injective.** -/
theorem injOn_of_sepAt_traceAt {W W₁ : ℝ≥0 → ℝ} {S : ℝ≥0∞}
    (hsep : GW1Z.SepAt (fun t => LP.traceAt t W₁) S) (hagree : ∀ r : ℝ≥0, (r : ℝ≥0∞) ≤ S → W r = W₁ r)
    (hWc : ContinuousOn W {t | (t : ℝ≥0∞) < S}) (hW0 : W 0 = 0) {α : ℝ≥0 → ℂ} (hα : IsGeneratingTrace W S α) :
    InjOn α {t | (t : ℝ≥0∞) ≤ S} := by
  refine GW1Z.injOn_of_sepAt hα.2.1 (fun q hq => ?_) hsep
  rw [LP.traceAt_congr fun r hr => (hagree r ((ENNReal.coe_le_coe.2 hr).trans hq.le)).symm]
  exact LP.traceAt_eq_of_isGeneratingTrace hα hWc hW0 hq

section AE

open MeasureTheory ProbabilityTheory

universe u

/-- **The canonical trace of every launched piece is separated through its lifetime**, almost surely (for a staged
history regular at every sample): under the conditional law given the past the piece is an integrated evolution, whose
generating trace through the lifetime exists (Theorem 1.3) and is injective (Aux. lemma 25). -/
theorem ae_sepAt_launch (h13 : Exist.Theorem13Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {spec : ExplSpec}
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hS : IsStagedHistory κ b jumps P h spec E)
    (hreg : ∀ k ω, IsRegularDriver (E k ω)) (k : ℕ) :
    ∀ᵐ ω ∂P, (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none →
      GW1Z.SepAt (fun t => LP.traceAt t (E k ω).1) (E k ω).2 := by
  set L : Set Ω := {ω | (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none} with hLdef
  have hL : MeasurableSet L := (runMeasStatement κ b jumps hb spec E hS.1 hreg k).1
  set Sep : Set Ω := {ω | GW1Z.SepAt (fun t => LP.traceAt t (E k ω).1) (E k ω).2} with hSep
  have hSepm : MeasurableSet Sep := measurableSet_setOfPred.2 (GW1Z.measurable_sepAt
    (A := fun t ω => LP.traceAt t (E k ω).1) (fun t => (LP.measurable_traceAt t).comp (measurable_fst.comp (hS.1 k)))
    (measurable_snd.comp (hS.1 k)))
  have hG : MeasurableSet (Lᶜ ∪ Sep) := hL.compl.union hSepm
  have hker : ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E k) ω₀), ω ∈ Lᶜ ∪ Sep := by
    filter_upwards [ae_ae_run_eq (P := P) runMeasStatement hb spec (k := k) (fun j _ => hS.1 j)
      (fun j _ => hreg j), hS.2.2.2 k] with ω₀ hrun hfl
    rcases hl : (ExplState.run κ b jumps spec (fun j => E j ω₀) (k + 1)).2.2.2.1 k with _ | ⟨c, θ'⟩
    · filter_upwards [hrun] with ω hω
      refine Or.inl fun hωL => hωL ?_
      show (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k = none
      rw [congrFun (launches_run_succ_of_run_eq spec hω) k, hl]
    · obtain ⟨b', jumps', h', -, -, hfld⟩ := hfl c θ' hl
      obtain ⟨_, 𝓕, VL, VR, B, -, hC⟩ := hfld
      have hinj := Theorem15.aux25Statement κ hκ hκ4 _ _ _ _ (Theorem15.isOrderedForceWord_flowLine b' jumps' 0)
        _ 𝓕 _ VL VR B _ hC.1
      have htr := h13 hκ (Theorem15.isOrderedForceWord_flowLine b' jumps' 0) hC.1
      filter_upwards [hinj, htr] with ω hinjω htrω
      obtain ⟨-, η, hη, -⟩ := htrω
      exact Or.inr (GW1Z.sepAt_of_injOn (A := fun t => LP.traceAt t (E k ω).1) hη.2.1
        (fun q hq => LP.traceAt_eq_of_isGeneratingTrace hη (hreg k ω).1 (hreg k ω).2.1 hq) (hinjω η hη))
  filter_upwards [Sec5.Lemma56Stages.ae_of_ae_condExpKernel (hS.2.1 k) hG hker] with ω hω hl
  rcases hω with hω | hω
  · exact absurd hl hω
  · exact hω

/-- **The launched pieces of a regular staged history have injective generating traces**, almost surely, for every
program (the separation of `ae_sepAt_launch` for the regularized history, which agrees with the history up to each
stop). -/
theorem ae_injLaunches (h13 : Exist.Theorem13Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {spec : ExplSpec}
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hS : IsStagedHistory κ b jumps P h spec E)
    (hR : StagedPiecesRegular κ b jumps P spec E) :
    ∀ᵐ ω ∂P, InjLaunches κ b jumps spec (fun j => E j ω) := by
  have hS₁ := StagedReg.isStagedHistory_regHist hb hS hR
  have hsep := fun k => ae_sepAt_launch h13 hκ hκ4 hb hS₁ (StagedReg.isRegularDriver_regHist (spec := spec) (E := E)) k
  filter_upwards [ae_all_iff.2 hsep, StagedReg.ae_run_regHist hR, hR.ae_pieceRegular] with ω hsepω hrun hprω
  intro k c θ hl α hα
  have hl₁ : (ExplState.run κ b jumps spec (fun j => StagedReg.regHist spec E j ω) (k + 1)).2.2.2.1 k =
      some (c, θ) := by
    rw [hrun (k + 1)]; exact hl
  have hs := hsepω k (by rw [hl₁]; exact Option.some_ne_none _)
  obtain ⟨h0, hc, -⟩ := hprω k c θ hl
  have hsnd : (StagedReg.regHist spec E k ω).2 = (E k ω).2 := StagedReg.regHist_snd k ω
  rw [hsnd] at hs
  exact injOn_of_sepAt_traceAt (sepAt_mono (min_le_right _ _) hs)
    (fun r hr => (StagedReg.regularize_eq_of_le h0 hc hr).symm)
    (hc.mono fun r (hr : (r : ℝ≥0∞) < _) => (le_of_lt hr : (r : ℝ≥0∞) ≤ _)) h0 hα

end AE

end InteractingSLE.Theorem14.SB.Lk
