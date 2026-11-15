/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2KLower
import InteractingSLE.Spec.Supplement.GW1ExtTip
import InteractingSLE.Spec.Supplement.GW1WalkExitInverse
import InteractingSLE.Spec.Supplement.GW1PieceSimpleFiber
import InteractingSLE.Spec.Supplement.GW2aMulti

/-!
# SB2(2)'s right entry is right of the upper tip: `e_R ≥ 0`

Packet PROVE-T14-SB2FIN5. The first clause of SB2(2)'s word half (`Lz.SB2LowerWordStatement`): at a launch of the
upper schedule program the right entry `e_R = g_A(R⁺)` of the launch chart is `≥ 0`, the chart point of the upper tip.
This is the mirror of PROVE-GW1-EXTREC's `GW1Ext.entry_nonpos_of_tendsto` (SB2(1)'s `m ≤ 0`):

* `bdryValue_facts_right`: the real boundary values right of a free `R` are continuous and inverted by the boundary
  map (mirror of `GW1Ext.bdryValue_facts`);
* **`entry_nonneg_of_tendsto`**: if `c⁻¹ → p` at `0` from `ℍ` and `p` is not a free real point right of `R`, every
  right entry value at `R` is `≥ 0` (otherwise the boundary values, unbounded above and tending to `e < 0` at `R⁺`,
  vanish at some `x₀ > R` and `p = g 0 = x₀`); `rightEntry_runChart_nonneg` for run charts;
* **`exists_tendsto_inv_zero_run`**: along a program of flow instructions with regular pieces, the chart's inverse
  tends at `0` to a point of the physical prefix (the root, or the endpoint of the last piece:
  `CounterflowRange.tendsto_loewner_inv`, `GW1WalkExit.tendsto_inverse_trace_le`);
* **`Lu.upperEntry_nonneg`**, **`Lu.ae_upperEntry_nonneg`**: SB2(2)'s `e_R ≥ 0` at every regular upper launch;
* `Lz.SB2LowerWordAdmStatement` and **`Lz.sb2LowerWordStatement_of_adm`**: SB2(2)'s word half reduces to the
  left-of-tip admissibility and the active word.

Deterministic (and one almost-sure transfer); no named input beyond `SB2LowerWordAdmStatement`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar chiC)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lx

open Exist.Staged Exist.StagedLaw

/-- **The real boundary values right of a free `R`** (mirror of `GW1Ext.bdryValue_facts`). -/
theorem bdryValue_facts_right {c : Chart} (hcc : c.IsConformal) (M : WalkIntCanon.HullModel c) {g : ℂ → ℂ}
    (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g c.2.1 H) {R : ℝ}
    (hfree : ∀ x : ℝ, R < x → ∃ ρ > 0, Disjoint (ball (x : ℂ) ρ) M.hull) :
    (∀ x : ℝ, R < x → Tendsto c.1 (𝓝[H] (x : ℂ)) (𝓝 (bdryValue c x : ℂ))) ∧
      ContinuousOn (bdryValue c) (Ioi R) ∧ ∀ x : ℝ, R < x → g (bdryValue c x) = x := by
  have hloc : ∀ x : ℝ, R < x → ∃ ρ > 0, ∃ G : ℂ → ℂ, ContinuousOn G (ball (x : ℂ) ρ) ∧
      ∀ y : ℝ, (y : ℂ) ∈ ball (x : ℂ) ρ →
        Tendsto c.1 (𝓝[H] (y : ℂ)) (𝓝 (G y - M.shift)) ∧ (G y - M.shift).im = 0 := by
    intro x hx
    obtain ⟨ρ, hρ, hd⟩ := hfree x hx
    obtain ⟨G, hGd, -, -, hGr, -, hGt⟩ := M.mapOut.exists_reflection M.isHull hd
    refine ⟨ρ / 2, half_pos hρ, G, hGd.continuousOn, fun y hy => ⟨?_, ?_⟩⟩
    · have h1 := hGt (y : ℂ) hy (by simp)
      have hn : 𝓝[ball (x : ℂ) (ρ / 2) ∩ H] (y : ℂ) = 𝓝[H] (y : ℂ) :=
        nhdsWithin_inter_of_mem (mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds hy))
      rw [hn] at h1
      simpa using h1.sub_const (M.shift : ℂ)
    · rw [Complex.sub_im, hGr _ hy (by simp)]
      simp
  have he : ∀ x : ℝ, R < x → Tendsto c.1 (𝓝[H] (x : ℂ)) (𝓝 (bdryValue c x : ℂ)) := fun x hx => by
    obtain ⟨ρ, hρ, G, -, hG⟩ := hloc x hx
    exact (tendsto_bdryValue (hG x (mem_ball_self hρ)).1 (hG x (mem_ball_self hρ)).2).2
  have hdom : ∀ x : ℝ, R < x → ∀ᶠ z in 𝓝[H] (x : ℂ), z ∈ (c.dom : Set ℂ) := fun x hx => by
    obtain ⟨ρ, hρ, hd⟩ := hfree x hx
    filter_upwards [inter_mem_nhdsWithin H (ball_mem_nhds (x : ℂ) hρ)] with z hz
    rw [M.dom_eq]
    exact ⟨hz.1, fun h => hd.ne_of_mem hz.2 h rfl⟩
  refine ⟨he, ?_, ?_⟩
  · intro x hx
    obtain ⟨ρ, hρ, G, hGc, hG⟩ := hloc x hx
    have hball : (fun y : ℝ => (y : ℂ)) ⁻¹' ball (x : ℂ) ρ ∈ 𝓝 x :=
      Complex.continuous_ofReal.continuousAt.preimage_mem_nhds (ball_mem_nhds _ hρ)
    have heq : (fun y : ℝ => (G y).re - M.shift) =ᶠ[𝓝 x] bdryValue c := by
      filter_upwards [hball] with y hy
      rw [(tendsto_bdryValue (hG y hy).1 (hG y hy).2).1]
      simp
    have hGx : ContinuousAt G (x : ℂ) := hGc.continuousAt (ball_mem_nhds _ hρ)
    have h1 : ContinuousAt (fun y : ℝ => (G y).re - M.shift) x :=
      ((Complex.continuous_re.continuousAt.comp (hGx.comp Complex.continuous_ofReal.continuousAt)).sub
        continuousAt_const)
    exact (h1.congr heq).continuousWithinAt
  · intro x hx
    have := GW1P.neBot_nhdsWithin_H (Lw.ofReal_mem_Hbar x)
    have h1 : Tendsto c.1 (𝓝[H] (x : ℂ)) (𝓝[H] (bdryValue c x : ℂ)) :=
      tendsto_nhdsWithin_iff.2 ⟨he x hx, (hdom x hx).mono fun z hz => hcc.fwd_mem hz⟩
    have h2 : Tendsto g (𝓝[H] (bdryValue c x : ℂ)) (𝓝 (g (bdryValue c x))) :=
      (hgc _ (Lw.ofReal_mem_Hbar _)).tendsto.mono_left
        (nhdsWithin_mono _ fun z hz => le_of_lt (show (0 : ℝ) < z.im from hz))
    have h3 : Tendsto (fun z => g (c.1 z)) (𝓝[H] (x : ℂ)) (𝓝 (x : ℂ)) := by
      refine (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).congr' ?_
      filter_upwards [hdom x hx] with z hz
      rw [hgi (hcc.fwd_mem hz), hcc.inv_fwd hz]
      rfl
    exact tendsto_nhds_unique (h2.comp h1) h3

/-- **The right entry over `R` is right of the chart point `0`** (mirror of `GW1Ext.entry_nonpos_of_tendsto`). -/
theorem entry_nonneg_of_tendsto {c : Chart} (hcc : c.IsConformal) (M : WalkIntCanon.HullModel c)
    (hc : GW1P.HasProperBdryExt c) {R e : ℝ}
    (hfree : ∀ x : ℝ, R < x → ∃ ρ > 0, Disjoint (ball (x : ℂ) ρ) M.hull)
    (he : IsRightEntryValue c R e) {p : ℂ} (hp : Tendsto c.2.1 (𝓝[H] 0) (𝓝 p))
    (hpR : ∀ x : ℝ, R < x → p ≠ (x : ℂ)) : 0 ≤ e := by
  obtain ⟨g, hgc, hgi, -, hgt⟩ := SB.Lw.exists_bdryMap_of_hasProperBdryExt hcc hc
  obtain ⟨f, C, hf, hC⟩ := hc
  obtain ⟨hbe, hcont, hinv⟩ := bdryValue_facts_right hcc M hgc hgi hfree
  have hgf : ∀ q ∈ Hbar, g q = f q := fun q hq => by
    have := GW1P.neBot_nhdsWithin_H hq
    exact tendsto_nhds_unique (hgt q hq) (hf q hq)
  have hlim : Tendsto (bdryValue c) (𝓝[>] R) (𝓝 e) := by
    obtain ⟨e', he', hlim⟩ := he
    refine hlim.congr' (eventually_nhdsWithin_of_forall fun x hx => ?_)
    have h1 := tendsto_bdryValue (he' x hx) (by simp)
    rw [h1.1, Complex.ofReal_re]
  by_contra he0
  push Not at he0
  -- far right the boundary values are positive
  set x₁ : ℝ := max (R + 1) (C + 1) with hx₁
  have hRx₁ : R < x₁ := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hpos : 0 < bdryValue c x₁ := by
    have h1 := hC _ (Lw.ofReal_mem_Hbar (bdryValue c x₁))
    rw [← hgf _ (Lw.ofReal_mem_Hbar _), hinv x₁ hRx₁, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs] at h1
    have h2 := (abs_le.1 h1).2
    have h3 : C + 1 ≤ x₁ := le_max_right _ _
    linarith
  -- near `R` they are negative
  obtain ⟨x₂, hneg, hx₂⟩ := ((hlim.eventually (gt_mem_nhds he0)).and (Ioo_mem_nhdsGT hRx₁)).exists
  have hsub : Icc x₂ x₁ ⊆ Ioi R := fun z hz => lt_of_lt_of_le hx₂.1 hz.1
  obtain ⟨x₀, hx₀, h0⟩ := intermediate_value_Icc hx₂.2.le (hcont.mono hsub) ⟨hneg.le, hpos.le⟩
  have hRx₀ : R < x₀ := hsub hx₀
  have hg0 : g 0 = x₀ := by
    have := hinv x₀ hRx₀
    rwa [h0, Complex.ofReal_zero] at this
  have hp0 : p = g 0 := by
    have := GW1P.neBot_nhdsWithin_H (Lw.ofReal_mem_Hbar 0)
    rw [Complex.ofReal_zero] at this
    exact tendsto_nhds_unique hp (hgt 0 (by simpa using Lw.ofReal_mem_Hbar 0))
  exact hpR x₀ hRx₀ (hp0.trans hg0)

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- **The chart of a run of flow instructions sends a point of its prefix to `0`**: along a program of flow
instructions with regular launched pieces, before the run is finished, the chart's inverse has a limit at `0` from `ℍ`
which is a point of the physical prefix (the root `x₀` initially; after a launch the endpoint `f(α(S))` of the new
piece, `f` the proper boundary extension of the old chart's inverse; unchanged otherwise). -/
theorem exists_tendsto_inv_zero_run (spec : ExplSpec) (hprog : GW2aMulti.IsFlowProgram spec.2.2)
    (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hreg : ∀ (k : ℕ) (c : Chart) (θ : ℝ), (ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 k = some (c, θ) →
      GW1P.PieceRegular (D k).1 (min (instrTime spec k) (D k).2)) :
    ∀ n, stStatus (ExplState.run κ b jumps spec D n) ≠ GW1Conn.stDone →
      ∃ p ∈ SB.prefixPhysSet κ b jumps spec D n,
        Tendsto (stChart (ExplState.run κ b jumps spec D n)).2.1 (𝓝[H] 0) (𝓝 p)
  | 0, _ => by
    refine ⟨spec.1, ?_, ?_⟩
    · simp [SB.prefixPhysSet, ExplState.run]
    · have e : (stChart (ExplState.run κ b jumps spec D 0)).2.1 = fun z : ℂ => z + (spec.1 : ℂ) := by
        funext z
        simp [ExplState.run, ExplState.init, Chart.recenter, Chart.id, stChart]
      rw [e]
      have : Tendsto (fun z : ℂ => z + (spec.1 : ℂ)) (𝓝 0) (𝓝 (0 + (spec.1 : ℂ))) :=
        (continuous_id.add continuous_const).tendsto 0
      rw [zero_add] at this
      exact tendsto_nhdsWithin_of_tendsto_nhds this
  | n + 1, hnot => by
    have hnot' : stStatus (ExplState.run κ b jumps spec D n) ≠ GW1Conn.stDone := fun h =>
      hnot (by rw [GW1WalkFinish.done_run_succ spec D h]; exact h)
    obtain ⟨p, hp, hlim⟩ := exists_tendsto_inv_zero_run spec hprog D hreg n hnot'
    have hsub := GW1Z.prefixPhysSet_subset_succ (κ := κ) (b := b) (jumps := jumps) spec D n
    have hrun := run_succ (κ := κ) (b := b) (jumps := jumps) spec D n
    cases hk : spec.2.2[n]? with
    | none =>
      rw [hk] at hrun
      refine ⟨p, hsub hp, ?_⟩
      rw [hrun]
      exact hlim
    | some ins =>
      obtain ⟨θ, t, rfl⟩ := hprog ins (List.mem_of_getElem? hk)
      rw [hk] at hrun
      change ExplState.run κ b jumps spec D (n + 1) =
        ExplState.flowStep κ b spec.2.1 (ExplState.run κ b jumps spec D n) n (D n) θ t at hrun
      have ht : instrTime spec n = t := by unfold instrTime; rw [hk]
      rcases flowStep_trichotomy (κ := κ) (b := b) spec.2.1 (ExplState.run κ b jumps spec D n) n (D n) θ t
        with e | e | e <;> rw [e] at hrun
      · exact ⟨p, hsub hp, by rw [hrun]; exact hlim⟩
      · exact ⟨p, hsub hp, by rw [hrun]; exact hlim⟩
      · have hl : (ExplState.run κ b jumps spec D (n + 1)).2.2.2.1 n =
            some (stChart (ExplState.run κ b jumps spec D n), θ) := by
          rw [hrun, launches_launch, Function.update_self]
        have hpr := hreg n _ θ hl
        rw [ht] at hpr
        have htop : min t (D n).2 ≠ ⊤ := by
          intro htop
          apply hnot
          rw [hrun]
          exact Lx.stStatus_launch_of_top _ _ _ _ _ htop
        obtain ⟨hW0, hWc, α, hα, -⟩ := hpr
        obtain ⟨f, C, hf, -⟩ := (GW1P.isClosed_pieces_run (κ := κ) (b := b) (jumps := jumps) spec D hreg n).1
        set S : ℝ≥0∞ := min t (D n).2 with hS
        have hw : Continuous fun r : ℝ≥0 => (D n).1 (min (r : ℝ≥0∞) S).toNNReal :=
          CounterflowRange.continuous_stopped hWc
        have hw0 : (fun r : ℝ≥0 => (D n).1 (min (r : ℝ≥0∞) S).toNNReal) 0 = 0 := by
          simpa only [ENNReal.coe_zero, zero_min, ENNReal.toNNReal_zero] using hW0
        have hαS : (S.toNNReal : ℝ≥0∞) ≤ S := ENNReal.coe_toNNReal_le_self
        have hF := GW1WalkExit.tendsto_inverse_trace_le (CounterflowRange.isGeneratingTrace_stopped hα) hw hw0 hαS
        have hαH : α S.toNNReal ∈ Hbar :=
          Sec7.IsGeneratingTrace.mem_Hbar hα (hWc.mono fun _ (hs : _ < S) => (le_of_lt hs : _ ≤ S)) hW0 hαS
        have hWr : Continuous fun r : ℝ => (D n).1 (min ((r.toNNReal : ℝ≥0) : ℝ≥0∞) S).toNNReal :=
          hw.comp continuous_real_toNNReal
        have hWr0 : (fun r : ℝ => (D n).1 (min ((r.toNNReal : ℝ≥0) : ℝ≥0∞) S).toNNReal) 0 = 0 := by
          simpa only [Real.toNNReal_zero] using hw0
        have hL := CounterflowRange.tendsto_loewner_inv (c := stChart (ExplState.run κ b jumps spec D n)) hWr hWr0
          (NNReal.coe_nonneg S.toNNReal) hF (hf _ hαH)
        refine ⟨f (α S.toNNReal), ?_, ?_⟩
        · refine GW1Z.tipSet_subset_prefixPhysSet_succ (κ := κ) (b := b) (jumps := jumps) spec D hl ?_
          rw [ht, CounterflowRange.tipSet_stopped_eq_of_tendsto hα hWc hW0 fun r hr =>
            hf _ (Sec7.IsGeneratingTrace.mem_Hbar hα (hWc.mono fun _ (hs : _ < S) => (le_of_lt hs : _ ≤ S))
              hW0 hr)]
          exact ⟨α S.toNNReal, ⟨S.toNNReal, hαS, rfl⟩, rfl⟩
        · rw [hrun]
          change Tendsto (ExplState.launch (ExplState.run κ b jumps spec D n) n (D n) θ t).2.2.2.2.1.2.1 _ _
          rw [chart_launch _ _ _ _ _ htop]
          exact hL

/-- **The run chart**: the right entry at `R` (`R` at least every real point of a compact `A` with the fill of the
prefix) is `≥ 0` when the run chart's inverse tends at `0` to a point that is not a free real point right of `R`
(mirror of `GW1Ext.leftEntry_runChart_nonpos`). -/
theorem rightEntry_runChart_nonneg (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hreg : ∀ k c θ', (ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 k = some (c, θ') →
      GW1P.PieceRegular (D k).1 (min (instrTime spec k) (D k).2)) (n : ℕ)
    (hnot : stStatus (ExplState.run κ b jumps spec D n) ≠ GW1Conn.stDone) {A : Set ℂ}
    (hAc : IsCompact A) (hAf : fillH A = fillH (SB.prefixPhysSet κ b jumps spec D n)) {R : ℝ}
    (hRA : ∀ y : ℝ, (y : ℂ) ∈ A → y ≤ R) {p : ℂ}
    (hp : Tendsto (stChart (ExplState.run κ b jumps spec D n)).2.1 (𝓝[H] 0) (𝓝 p))
    (hpR : ∀ x : ℝ, R < x → p ≠ (x : ℂ)) :
    0 ≤ rightEntry (stChart (ExplState.run κ b jumps spec D n)) R := by
  obtain ⟨M, hK⟩ := SB.Lw.exists_hullModel_fill spec D hreg n hnot
  have hcc := (GW2aCont.isConformal_runChart (κ := κ) (b := b) (jumps := jumps) spec D n
    fun j _ c θ h => hreg j c θ h).1
  refine entry_nonneg_of_tendsto hcc M
    (GW1P.isClosed_pieces_run (κ := κ) (b := b) (jumps := jumps) spec D hreg n).1 (fun x hx => ?_)
    (isRightEntryValue_runChart spec D hreg n hnot hAc hAf hRA) hp hpR
  obtain ⟨ρ, hρ, hd⟩ := exists_ball_disjoint_fillH_right hAc fun y hy => lt_of_le_of_lt (hRA y hy) hx
  rw [hAf, ← hK] at hd
  exact ⟨ρ, hρ, hd⟩

end InteractingSLE.Theorem14.SB.Lx

namespace InteractingSLE.Theorem14.SB.Lu

open Lx Exist.Staged Exist.StagedLaw

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type*} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
  {u : ℝ} {l : List (ℝ × ℝ≥0)} {k : ℕ} {ω₀ : Ω}

/-- **SB2(2)'s clause `e_R ≥ 0` at one sample**: at a launch of the upper schedule program with regular launched
pieces, the right entry of the launch chart at `R = max(A ∩ ℝ)` is `≥ 0` (the chart's inverse tends at `0` to a point
of the prefix, `exists_tendsto_inv_zero_run`, which is not a real point right of `R`). -/
theorem upperEntry_nonneg
    (hreg : ∀ j c θ', (ExplState.run κ b jumps (upperSpec u l) (fun i => E (upperSpec u l) i ω₀) (j + 1)).2.2.2.1 j =
        some (c, θ') →
      GW1P.PieceRegular (E (upperSpec u l) j ω₀).1 (min (instrTime (upperSpec u l) j) (E (upperSpec u l) j ω₀).2))
    (hF : ω₀ ∈ upperLaunchSet κ b jumps E u l k) : 0 ≤ upperEntry κ b jumps E u l k ω₀ := by
  have hAc := isCompact_upperPrefix hreg hF
  obtain ⟨⟨c, θ⟩, hlk⟩ := Option.ne_none_iff_exists'.1 hF
  have hnot := stStatus_ne_done_of_launches _ _ hlk
  obtain ⟨p, hp, hlim⟩ := exists_tendsto_inv_zero_run (upperSpec u l)
    (GW2aMulti.isFlowProgram_scheduleProgram 0 l) _ hreg k hnot
  unfold upperEntry
  rw [upperLaunchChart_eq hlk, (eq_launch_of_launches _ _ hlk).2.2]
  refine rightEntry_runChart_nonneg _ _ hreg k hnot hAc (Lw.fillH_union_real _ _)
    (fun y hy => le_realMax_of_mem hAc hy) hlim fun x hx hpx => ?_
  have hmem : (x : ℂ) ∈ upperPrefix κ b jumps E u l k ω₀ := Or.inl (hpx ▸ hp)
  exact absurd (le_realMax_of_mem hAc hmem) (not_le.2 hx)

/-- **SB2(2)'s clause `e_R ≥ 0`, almost surely** (`StagedPiecesRegular` of the upper schedule program). -/
theorem ae_upperEntry_nonneg {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hER : StagedPiecesRegular κ b jumps P (upperSpec u l) (E (upperSpec u l))) (k : ℕ) :
    ∀ᵐ ω₀ ∂P, ω₀ ∈ upperLaunchSet κ b jumps E u l k → 0 ≤ upperEntry κ b jumps E u l k ω₀ := by
  filter_upwards [hER] with ω₀ hR₀ hF
  exact upperEntry_nonneg (fun j c' θ' hl' => hR₀ j θ' _ c' (eq_launch_of_launches _ _ hl').1 hl') hF

end InteractingSLE.Theorem14.SB.Lu

namespace InteractingSLE.Theorem14.SB.Lz

open Lx Lu Leaf FlowDilate Sec4 Exist.Staged Exist.StagedLaw

/-- **SB2(2)'s word half without the clause `e_R ≥ 0`** (named input): the admissibility of the relative word left of
the upper tip and SB2(2)'s active word, for every witness of the launch clause, with `m = −e_R`. -/
def SB2LowerWordAdmStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
    ∀ (u : ℝ) (l : List (ℝ × ℝ≥0)) (k : ℕ), u ≤ 0 → l.Pairwise (fun p q => p.2 < q.2) →
      (∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) →
      (∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) →
      (∀ᵐ ω ∂P, ω ∈ upperLaunchSet κ b jumps E u l k →
        upperPrefix κ b jumps E u l k ω ∩ rightSideOf (lowerWalkSet κ b jumps E ω) = ∅) →
      ∀ᵐ ω₀ ∂P, ∀ (c : Chart) (θ : ℝ),
        (ExplState.run κ b jumps (upperSpec u l) (fun j => E (upperSpec u l) j ω₀) (k + 1)).2.2.2.1 k =
            some (c, θ) →
        ∀ (b' : ℝ → ℝ) (jumps' : Finset ℝ) (h' : Ω → DistOn upperHalfPlaneOpens),
          IsPiecewiseConstantBoundaryData b' jumps' →
          (∀ ω, IsChartTransport c 1 0 (chiC κ) (h ω) (h' ω)) →
          IsGFFWithBoundaryData (condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀)
            h' b' jumps' →
          ∀ m : ℝ, m = -upperEntry κ b jumps E u l k ω₀ →
            (∀ y, y ≤ m → y ∉ affJumps 1 m jumps' →
              -2 < cumWeightLeft κ (affData 1 m b' y + -(Real.pi / 2) * chiC κ)) ∧
            IsActiveHighWord κ b jumps u l b' jumps' m

/-- **SB2(2)'s word half from its two remaining clauses** (`e_R ≥ 0` is `Lu.ae_upperEntry_nonneg`). -/
theorem sb2LowerWordStatement_of_adm (h : SB2LowerWordAdmStatement.{u}) : SB2LowerWordStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ hf hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft
  exact ⟨ae_upperEntry_nonneg (hER _ (isBoundaryContinuedProgram_upperSpec hlθ)) k,
    h κ hκ hκ4 b jumps hb P hf hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft⟩

end InteractingSLE.Theorem14.SB.Lz
