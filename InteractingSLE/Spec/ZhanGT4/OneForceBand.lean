/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.OneForceCode

/-!
# One force: no real terminal cluster point (Part B.2, (E9))

Packet PROVE-ZHAN-GT4-B3. Source: Astra, *Follow-up proofs and dependency audit*, §B.2 L1083–L1158 (ruling R38),
"From (E9) to chordal one-force transience … a chordal one-force law with separated mark and weight at least `c_κ` has
no
finite real terminal cluster point"; additional note Lemma 3.2 and Proposition 3.3, L1409–L1457 (ruling R39).

The source excludes the lower line with the swallowing time of a far point `x₀` and the extremal bounds (E8), and the
upper
line with the upper-gap diffusion (E6). In the chordal picture both reduce to one restart, as for GT4-B2's two-force
Lemma 3.4. Fix `x₀ > 0`, a time `q₀ > 0` by which `x₀` is swallowed (B.2 (E7), `ae_realSwallowAt_oneForce`), a width
`X ≥ 0` and a level `L > 0`; restart at the first time `T ≥ q₀` at which the force gap `W − V` reaches `L` (finite:
the gap
is unbounded, `ae_exists_le_gap_oneForce`). At `T` every point of `(0, x₀]` is swallowed, so by the lifting lemma and
the
same-side contraction (`exists_cluster_near_mark`, with (G5) at `T` from Part A by bounded-drift Girsanov) every
terminal
cluster point `x ∈ [p − X, x₀)` of the trace lifts to a real terminal cluster point of the restarted trace within
`D = max(X, |p|)` of its mark `V_T − W_T`, whose distance to the driver is `≥ L`: the near-mark event of fraction
`θ = D/L`. The canonical probability of that event is the same at every word (dilation), so it bounds the probability of
a cluster point in `[p − X, x₀)`, and it tends to `0` as `L → ∞` (the mark is not a cluster point, (E5)).

## Main results

* `IsIntegratedSLEEvolution.measure_cluster_le_near`: the restart inequality.
* `IsIntegratedSLEEvolution.ae_noRealCluster_oneForce`: **a separated one-force law (`κ > 4`, one left mark `p < 0` of
  weight `≥ κ/2 − 2`, no right mark) has no real terminal cluster point**, given (G5) for ordinary `SLE_κ` at positive
  stopping times (`StoppingInverseBoundaryStatement κ`, Part A).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.ZhanGT4

open Zhan Sec2 Sec2.Assembly Sec2.Restart Sec7.RandRestart QuantumZipper

section Main

variable {κ : ℝ} {xL ρL : Fin 1 → ℝ} {xR ρR : Fin 0 → ℝ} {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin 1 → ℝ≥0 → Ω → ℝ} {VR : Fin 0 → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- The pathwise facts of a separated one-force evolution used at the restart. -/
def GoodOne (xL : Fin 1 → ℝ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin 1 → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω) : Prop :=
  ζ ω = ⊤ ∧ Continuous (fun t => W t ω) ∧ W 0 ω = 0 ∧ Continuous (fun t => VL 0 t ω) ∧
    (∀ t, VL 0 t ω < W t ω) ∧
    (∀ t : ℝ≥0, VL 0 t ω = xL 0 + ∫ s in (0 : ℝ)..t, 2 / (VL 0 s.toNNReal ω - W s.toNNReal ω)) ∧
    ∀ (L : ℝ) (t₀ : ℝ≥0), ∃ t : ℝ≥0, t₀ ≤ t ∧ L ≤ W t ω - VL 0 t ω

/-- The good event holds almost surely for a separated one-force evolution (`κ > 4`). -/
theorem IsIntegratedSLEEvolution.ae_goodOne (hκ4 : 4 < κ) (hx : xL 0 < 0) (hρ : κ / 2 - 2 ≤ ρL 0)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) : ∀ᵐ ω ∂P, GoodOne xL W VL ζ ω := by
  have hκ : 0 < κ := by linarith
  filter_upwards [IsIntegratedSLEEvolution.ae_good_oneForce hκ hx hρ hE,
    IsIntegratedSLEEvolution.ae_exists_le_gap_oneForce hκ4 hx hρ hE] with ω ⟨hζ, hw, hw0, hv, hsep, hveq, _⟩ hgap
  refine ⟨hζ, hw, hw0, hv, hsep, hveq, fun L t₀ => ?_⟩
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := t₀)).exists_bound_of_continuousOn
    ((hw.sub hv).continuousOn)
  obtain ⟨t, ht⟩ := hgap (max L (K + 1))
  refine ⟨t, ?_, (le_max_left _ _).trans ht⟩
  by_contra hlt
  push Not at hlt
  have h1 := hK t ⟨bot_le, hlt.le⟩
  rw [Real.norm_eq_abs, Pi.sub_apply] at h1
  have h2 := le_abs_self (W t ω - VL 0 t ω)
  linarith [le_max_right L (K + 1)]

/-- Being alive at a later time implies being alive earlier; so a point swallowed by `q₀` is swallowed at every
`m ≥ q₀`, and so is every point of `(0, x₀]` (monotonicity in the starting point). -/
theorem dead_of_dead {Wr : ℝ → ℝ} (hW : Continuous Wr) (hW0 : Wr 0 = 0) {x₀ : ℝ} {q₀ m : ℝ}
    (hq₀ : 0 ≤ q₀) (hm : q₀ ≤ m) (hdead : ¬ ∃ u, IsForwardSol Wr (x₀ : ℂ) q₀ u) :
    ∀ x' ∈ Ioc (0 : ℝ) x₀, ¬ ∃ u, IsForwardSol Wr (x' : ℂ) m u := by
  rintro x' ⟨hx'0, hx'x⟩ ⟨u, hu⟩
  have hu' := isForwardSol_restrict hu hq₀ hm
  rcases hx'x.lt_or_eq with hlt | heq
  · exact hdead (RS.exists_isForwardSol_of_lt hW hq₀ (by rw [hW0]; exact hx'0) hlt hu')
  · exact hdead ⟨u, heq ▸ hu'⟩

/-- **The restart inequality** (B.2; additional note Lemma 3.2). For a separated one-force evolution (`κ > 4`) and
`X ≥ 0`, `x₀ > 0`, `L > 0`, `q₀ > 0`, given (G5) for ordinary `SLE_κ` at positive stopping times, the probability that
`x₀` is swallowed by `q₀` and the trace has a terminal cluster point in `[p − X, x₀)` is at most the canonical
probability of the near-mark event of fraction `max(X, |p|)/L`. -/
theorem IsIntegratedSLEEvolution.measure_cluster_le_near [IsProbabilityMeasure P] (hκ4 : 4 < κ)
    (hG5 : StoppingInverseBoundaryStatement.{u} κ) (hx : xL 0 < 0) (hρ : κ / 2 - 2 ≤ ρL 0)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) {X x₀ L : ℝ} (hL : 0 < L) {q₀ : ℝ≥0} (hq₀ : 0 < q₀) :
    P {ω | (¬ ∃ u, IsForwardSol (fun r : ℝ => W r.toNNReal ω) (x₀ : ℂ) q₀ u) ∧
        ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η ∧
          ∃ x : ℝ, xL 0 - X ≤ x ∧ x < x₀ ∧ IsTermCluster η x} ≤
      codeLaw κ ρL ρR (nearCodeSet (max X (-xL 0) / L)) (xL, xR) := by
  have hκ : 0 < κ := by linarith
  set D : ℝ := max X (-xL 0) with hD
  have hD0 : 0 < D := lt_of_lt_of_le (neg_pos.2 hx) (le_max_right _ _)
  set θ : ℝ := D / L with hθ
  have hθ0 : 0 < θ := div_pos hD0 hL
  have hsep : ∀ (i : Fin 1) (j : Fin 0), xL i < xR j := fun _ j => j.elim0
  obtain ⟨𝓖', hEa, hnull⟩ : ∃ 𝓖' : Filtration ℝ≥0 mΩ, IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓖' W VL VR B ζ ∧
      ∀ N : Set Ω, MeasurableSet N → P N = 0 → ∀ t, MeasurableSet[𝓖' t] N :=
    ⟨_, Ito.isIntegratedSLEEvolution_usualAugmentation hE,
      fun N hN hN0 t => Ito.measurableSet_usualAugmentation_of_null hN hN0 t⟩
  obtain ⟨N, hNsub, hNm0, hN0⟩ := exists_measurable_superset_of_null
    (ae_iff.1 (IsIntegratedSLEEvolution.ae_goodOne hκ4 hx hρ hE))
  have hNm : ∀ t, MeasurableSet[𝓖' t] N := hnull N hNm0 hN0
  have hgood : ∀ ω ∉ N, GoodOne xL W VL ζ ω := fun ω hω => by
    by_contra h; exact hω (hNsub h)
  -- the first time after `q₀` at which the gap reaches `L`
  set Y : ℝ≥0 → Ω → ℝ := fun t ω => L - (W t ω - VL 0 t ω) with hY
  have hYa : AdaptedBefore 𝓖' ζ (posAfterT q₀ Y) :=
    adaptedBefore_of_eq (V₂ := W) (fun t p => max (L - (p.1 - p.2.1)) ((q₀ : ℝ) - (t : ℝ)))
      (fun t => by fun_prop) hEa.2.1 (hEa.2.2.1 0) hEa.2.1 fun t ω => rfl
  have hZa : AdaptedBefore 𝓖' ζ (zeroProc (Ω := Ω)) :=
    adaptedBefore_of_eq (V₂ := W) (fun _ _ => 0) (fun _ => measurable_const) hEa.2.1 (hEa.2.2.1 0) hEa.2.1
      fun _ _ => rfl
  have hYc : ∀ ω ∉ N, Continuous fun t => Y t ω := fun ω hω => by
    obtain ⟨-, hw, -, hl, -⟩ := hgood ω hω
    exact continuous_const.sub (hw.sub hl)
  have hThs : IsStoppingTime 𝓖' fun ω =>
      (Sec7.zeroOn N (Sec7.firstMeet zeroProc (posAfterT q₀ Y) ζ) ω : WithTop ℝ≥0) :=
    Sec7.isStoppingTime_firstMeet_off hZa hYa hNm fun ω hω => continuousOn_posAfterT_sub (hYc ω hω) _
  set Th : Ω → ℝ≥0∞ := Sec7.zeroOn N (Sec7.firstMeet zeroProc (posAfterT q₀ Y) ζ) with hTh
  have hhit : ∀ ω ∉ N, ∃ m : ℝ≥0, Th ω = m ∧ q₀ ≤ m ∧ L ≤ W m ω - VL 0 m ω := fun ω hω => by
    obtain ⟨hζ, -, -, -, -, -, hgap⟩ := hgood ω hω
    obtain ⟨t₁, ht₁, hL₁⟩ := hgap L q₀
    obtain ⟨m, hm, hm1, hYm, -⟩ := exists_firstMeet_posAfterT (hYc ω hω) hζ ht₁
      (show Y t₁ ω ≤ 0 by simp only [hY]; linarith)
    refine ⟨m, ?_, hm1, ?_⟩
    · simp only [hTh, Sec7.zeroOn_of_notMem hω]; exact hm
    · simp only [hY] at hYm; linarith
  -- the capped stopping times and the restart events
  set Tn : ℕ → Ω → ℝ≥0 := fun n ω => (min (Th ω) ((n : ℝ≥0) : ℝ≥0∞)).toNNReal with hTn
  have hTn_coe : ∀ n ω, ((Tn n ω : ℝ≥0) : ℝ≥0∞) = min (Th ω) ((n : ℝ≥0) : ℝ≥0∞) := fun n ω =>
    ENNReal.coe_toNNReal (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _))
  have hTns : ∀ n, IsStoppingTime 𝓖' fun ω => ((Tn n ω : ℝ≥0) : WithTop ℝ≥0) := fun n => by
    have h := hThs.min_const (n : ℝ≥0)
    have he : (fun ω => ((Tn n ω : ℝ≥0) : WithTop ℝ≥0)) = fun ω => min (Th ω : WithTop ℝ≥0) (n : ℝ≥0) :=
      funext fun ω => hTn_coe n ω
    rw [he]; exact h
  set A : ℕ → Set Ω := fun n => Nᶜ ∩ {ω | Th ω < ((n : ℝ≥0) : ℝ≥0∞)} with hA
  have hTnA : ∀ n, ∀ ω ∈ A n, ((Tn n ω : ℝ≥0) : ℝ≥0∞) = Th ω := fun n ω hω => by
    rw [hTn_coe]; exact min_eq_left hω.2.le
  have hAm : ∀ n, MeasurableSet[(hTns n).measurableSpace] (A n) := by
    intro n
    have key : ∀ i : ℝ≥0, MeasurableSet[𝓖' i] (A n ∩ {ω | ((Tn n ω : ℝ≥0) : WithTop ℝ≥0) ≤ i}) := by
      intro i
      have heq : A n ∩ {ω | ((Tn n ω : ℝ≥0) : WithTop ℝ≥0) ≤ i} =
          Nᶜ ∩ ({ω | Th ω < ((n : ℝ≥0) : ℝ≥0∞)} ∩ {ω | Th ω ≤ (i : ℝ≥0∞)}) := by
        ext ω
        constructor
        · rintro ⟨⟨h1, h2⟩, h3⟩
          refine ⟨h1, h2, ?_⟩
          have h3' : ((Tn n ω : ℝ≥0) : ℝ≥0∞) ≤ i := h3
          rwa [hTnA n ω ⟨h1, h2⟩] at h3'
        · rintro ⟨h1, h2, h3⟩
          refine ⟨⟨h1, h2⟩, ?_⟩
          show ((Tn n ω : ℝ≥0) : ℝ≥0∞) ≤ i
          rw [hTnA n ω ⟨h1, h2⟩]; exact h3
      rw [heq]
      refine (hNm i).compl.inter ?_
      rcases lt_or_ge i (n : ℝ≥0) with hin | hni
      · have he : {ω | Th ω < ((n : ℝ≥0) : ℝ≥0∞)} ∩ {ω | Th ω ≤ (i : ℝ≥0∞)} = {ω | Th ω ≤ (i : ℝ≥0∞)} := by
          refine inter_eq_right.2 fun ω (hω : Th ω ≤ i) => ?_
          exact lt_of_le_of_lt hω (by exact_mod_cast hin)
        rw [he]; exact hThs i
      · have he : {ω | Th ω < ((n : ℝ≥0) : ℝ≥0∞)} ∩ {ω | Th ω ≤ (i : ℝ≥0∞)} = {ω | Th ω < ((n : ℝ≥0) : ℝ≥0∞)} := by
          refine inter_eq_left.2 fun ω (hω : Th ω < (n : ℝ≥0)) => ?_
          exact le_trans hω.le (by exact_mod_cast hni)
        rw [he]; exact 𝓖'.mono hni _ (hThs.measurableSet_lt (n : ℝ≥0))
    refine ((hTns n).measurableSet _).2 ⟨?_, key⟩
    have h := key (n : ℝ≥0)
    have hsub : A n ∩ {ω | ((Tn n ω : ℝ≥0) : WithTop ℝ≥0) ≤ ((n : ℝ≥0) : WithTop ℝ≥0)} = A n :=
      inter_eq_left.2 fun ω _ => by
        show ((Tn n ω : ℝ≥0) : ℝ≥0∞) ≤ ((n : ℝ≥0) : ℝ≥0∞)
        rw [hTn_coe]; exact min_le_right _ _
    rw [hsub] at h
    exact le_iSup (fun t => 𝓖' t) (n : ℝ≥0) _ h
  have hTmA : ∀ n, ∀ ω ∈ A n, ∃ m : ℝ≥0, Tn n ω = m ∧ q₀ ≤ m ∧ L ≤ W m ω - VL 0 m ω := fun n ω hω => by
    obtain ⟨m, hm, hm1, hgm⟩ := hhit ω hω.1
    exact ⟨m, by exact_mod_cast (hTnA n ω hω).trans hm, hm1, hgm⟩
  have hAT : ∀ n, ∀ ω ∈ A n, ((Tn n ω : ℝ≥0) : ℝ≥0∞) < ζ ω ∧
      (0 < Tn n ω ∨ ∀ i j, xL i < xR j) := fun n ω hω => by
    obtain ⟨hζ, -⟩ := hgood ω hω.1
    obtain ⟨m, hTm, hm1, -⟩ := hTmA n ω hω
    refine ⟨by rw [hζ]; exact ENNReal.coe_lt_top, Or.inl ?_⟩
    rw [hTm]; exact lt_of_lt_of_le hq₀ hm1
  -- the restart formulas
  have hlawN := fun n => measure_restart_codeEventS hκ hEa (hTns n) (hAm n) (hAT n)
    (measurableSet_nearCodeSet θ) (fun _ _ _ => Iff.rfl) (nearEvent_congr θ)
  have hlawT := fun n => measure_restart_codeEvent hκ hEa (hTns n) (hAm n) (hAT n)
    (Φ := fun w τ => ¬ TopEvent w τ) measurableSet_topCodeSetN.compl (fun _ _ _ => Iff.rfl) not_topEvent_congr
  have hAmeas : ∀ n, MeasurableSet (A n) := fun n => (hTns n).measurableSpace_le _ (hAm n)
  -- the canonical near-mark probability is constant along the ray of words `(−G)`
  set K := codeLaw κ ρL ρR (nearCodeSet θ) (xL, xR) with hK
  have htr : ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η := by
    filter_upwards [hE.ae_exists_isGeneratingTrace_top_of_hasAdmissiblePartialSums hκ
      (isOrderedForceWord_oneLeft hx.le) (hasAdmissiblePartialSums_oneLeft hρ)
      (fun i => by rw [Fin.fin_one_eq_zero i]; exact hx) (fun j => j.elim0)] with ω ⟨hζ, η, hη⟩
    exact ⟨hζ, η, hη⟩
  have hdil : ∀ G : ℝ, 0 < G → ∀ s₂ : Fin 0 → ℝ,
      codeLaw κ ρL ρR (nearCodeSet θ) ((fun _ => -G), s₂) = K := by
    intro G hG s₂
    have hxL0 : 0 < -xL 0 := neg_pos.2 hx
    set c : ℝ≥0 := ⟨((-xL 0) / G) ^ 2, by positivity⟩ with hcdef
    have hc : c ≠ 0 := by
      intro h
      have : ((-xL 0) / G) ^ 2 = 0 := congrArg NNReal.toReal h
      exact (pow_pos (div_pos hxL0 hG) 2).ne' this
    have hsc : (√(c : ℝ))⁻¹ = G / (-xL 0) := by
      rw [show (c : ℝ) = ((-xL 0) / G) ^ 2 from rfl, Real.sqrt_sq (div_pos hxL0 hG).le, inv_div]
    rw [hK, ← codeLaw_near_dilate hκ hE htr hc θ]
    congr 1
    refine Prod.ext (funext fun i => ?_) (funext fun j => j.elim0)
    rw [Fin.fin_one_eq_zero i]
    show -G = (√(c : ℝ))⁻¹ * xL 0
    have hx0 : xL 0 ≠ 0 := hx.ne
    rw [hsc]
    field_simp
  have hRHS : ∀ n, ∫⁻ ω in A n, codeLaw κ ρL ρR (nearCodeSet θ) (wordAt W VL VR (Tn n) ω) ∂P =
      K * P (A n) := by
    intro n
    rw [← setLIntegral_const]
    refine setLIntegral_congr_fun (hAmeas n) fun ω hω => ?_
    obtain ⟨-, -, -, -, hsL, -⟩ := hgood ω hω.1
    obtain ⟨m, hTm, -, -⟩ := hTmA n ω hω
    have hG : 0 < W m ω - VL 0 m ω := sub_pos.2 (hsL m)
    have hword : wordAt W VL VR (Tn n) ω =
        ((fun _ => -(W m ω - VL 0 m ω)), fun j => VR j (Tn n ω) ω - W (Tn n ω) ω) := by
      simp only [wordAt, hTm]
      refine Prod.ext (funext fun i => ?_) rfl
      rw [Fin.fin_one_eq_zero i]; simp only; ring
    rw [hword, hdil _ hG]
  -- the restarted driver has a trace
  have hTop0 : ∀ n, ∫⁻ ω in A n, codeLaw κ ρL ρR topCodeSetNᶜ (wordAt W VL VR (Tn n) ω) ∂P = 0 := by
    intro n
    refine (setLIntegral_congr_fun_ae (hAmeas n) ?_).trans ((setLIntegral_const _ 0).trans (zero_mul _))
    filter_upwards [ae_solvable_restart hκ hEa (hTns n) (hAm n) (hAT n)] with ω h hω
    obtain ⟨-, hsolv⟩ := h hω
    obtain ⟨-, -, -, -, hsL, -⟩ := hgood ω hω.1
    exact codeLaw_compl_topCodeSetN_eq_zero hκ hρ
      (show VL 0 (Tn n ω) ω - W (Tn n ω) ω < 0 by linarith [hsL (Tn n ω)]) hsolv
  -- (G5) at the restart times
  set T' : ℕ → Ω → ℝ≥0 := fun n ω => max (Tn n ω) q₀ with hT'
  have hT's : ∀ n, IsStoppingTime 𝓖' fun ω => ((T' n ω : ℝ≥0) : WithTop ℝ≥0) := fun n => by
    have h := (hTns n).max_const q₀
    have he : (fun ω => ((T' n ω : ℝ≥0) : WithTop ℝ≥0)) =
        fun ω => max ((Tn n ω : ℝ≥0) : WithTop ℝ≥0) (q₀ : WithTop ℝ≥0) :=
      funext fun ω => by rw [hT']; push_cast; rfl
    rw [he]; exact h
  have hG5n := fun n => IsIntegratedSLEEvolution.ae_hasInteriorInverseBoundary hκ hG5 hEa (hT's n)
    (fun ω => lt_of_lt_of_le hq₀ (le_max_right _ _))
  -- the pathwise inclusion
  set Cl : Set Ω := {ω | (¬ ∃ u, IsForwardSol (fun r : ℝ => W r.toNNReal ω) (x₀ : ℂ) q₀ u) ∧
      ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η ∧
        ∃ x : ℝ, xL 0 - X ≤ x ∧ x < x₀ ∧ IsTermCluster η x} with hCl
  have hincl : ∀ n, Cl ∩ A n ≤ᵐ[P] (A n ∩ {ω | NearEvent θ (wordAt W VL VR (Tn n) ω)
      (fun t => W (Tn n ω + t) ω - W (Tn n ω) ω) (ζ ω - Tn n ω)}) ∪
      (A n ∩ {ω | ¬ TopEvent (fun t => W (Tn n ω + t) ω - W (Tn n ω) ω) (ζ ω - Tn n ω)}) := by
    intro n
    filter_upwards [hG5n n] with ω hG ⟨⟨hdead, η, hη, x, hx1, hx2, hcl⟩, hωA⟩
    by_cases htop : TopEvent (fun t => W (Tn n ω + t) ω - W (Tn n ω) ω) (ζ ω - Tn n ω)
    swap
    · exact Or.inr ⟨hωA, htop⟩
    refine Or.inl ⟨hωA, ?_⟩
    obtain ⟨hζ, hw, hw0, hl, hsL, hLeq, -⟩ := hgood ω hωA.1
    obtain ⟨m, hTm, hm1, hgm⟩ := hTmA n ω hωA
    have hT'm : T' n ω = m := by simp only [hT', hTm]; exact max_eq_left hm1
    rw [hT'm] at hG
    have hζm : ζ ω - m = ⊤ := by rw [hζ]; exact ENNReal.top_sub_coe
    show NearEvent θ ((fun i => VL i (Tn n ω) ω - W (Tn n ω) ω), fun j => VR j (Tn n ω) ω - W (Tn n ω) ω)
      (fun t => W (Tn n ω + t) ω - W (Tn n ω) ω) (ζ ω - Tn n ω)
    rw [hTm, hζm]
    rw [hTm, hζm] at htop
    have hw₂ : Continuous (Sec7.shiftNN (fun t => W t ω) m) :=
      (hw.comp (continuous_const.add continuous_id)).sub continuous_const
    obtain ⟨η₂, hη₂⟩ := (ratVals_mem_topSet_iff hw₂ (Sec7.shiftNN_zero _ m)).1 htop.2
    have hG' := hG (by rw [hζ]; exact ENNReal.coe_lt_top) (fun s _ => ⟨fun i => by
        rw [Fin.fin_one_eq_zero i]; exact hsL s, fun j => j.elim0⟩)
      (fun s : ℝ => W s.toNNReal ω) (hw.comp continuous_real_toNNReal) fun _ _ => rfl
    have hWrc : Continuous fun s : ℝ => W s.toNNReal ω := hw.comp continuous_real_toNNReal
    have hWr0 : (fun s : ℝ => W s.toNNReal ω) 0 = 0 := by simp [hw0]
    have hdead' := dead_of_dead hWrc hWr0 q₀.coe_nonneg (show (q₀ : ℝ) ≤ m by exact_mod_cast hm1) hdead
    obtain ⟨hx0, y, hy, hyb⟩ := exists_cluster_near_mark hw hw0 hl hsL hx hLeq hη hη₂ hG' hdead' hx2 hcl
    change NearEvent θ _ (Sec7.shiftNN (fun t => W t ω) m) ⊤
    rw [nearEvent_top_iff hw₂ (Sec7.shiftNN_zero _ m) hη₂]
    refine realNear_of_isTermCluster ?_ hy
    -- the band of width `D` lies in the `θ`-band
    set G := W m ω - VL 0 m ω with hGdef
    have hxp : |x - xL 0| ≤ D := by
      rcases le_or_gt (xL 0) x with h | h
      · rw [abs_of_nonneg (by linarith)]; exact (by linarith : x - xL 0 ≤ -xL 0).trans (le_max_right _ _)
      · rw [abs_of_neg (by linarith)]; exact (by linarith : -(x - xL 0) ≤ X).trans (le_max_left _ _)
    have hθG : D ≤ θ * G := by
      rw [hθ, div_mul_eq_mul_div, le_div_iff₀ hL]
      exact mul_le_mul_of_nonneg_left hgm hD0.le
    have hyb' := (abs_le.1 (hyb.trans hxp))
    simp only
    constructor
    · nlinarith [hyb'.1]
    · nlinarith [hyb'.2]
  -- the bound for each `n`
  have hbound : ∀ n, P Cl ≤ K + P (A n)ᶜ := by
    intro n
    have h1 : P (Cl ∩ A n) ≤ K := by
      calc P (Cl ∩ A n) ≤ P ((A n ∩ {ω | NearEvent θ (wordAt W VL VR (Tn n) ω)
            (fun t => W (Tn n ω + t) ω - W (Tn n ω) ω) (ζ ω - Tn n ω)}) ∪
            (A n ∩ {ω | ¬ TopEvent (fun t => W (Tn n ω + t) ω - W (Tn n ω) ω) (ζ ω - Tn n ω)})) :=
            measure_mono_ae (hincl n)
        _ ≤ P (A n ∩ {ω | NearEvent θ (wordAt W VL VR (Tn n) ω)
            (fun t => W (Tn n ω + t) ω - W (Tn n ω) ω) (ζ ω - Tn n ω)}) +
            P (A n ∩ {ω | ¬ TopEvent (fun t => W (Tn n ω + t) ω - W (Tn n ω) ω) (ζ ω - Tn n ω)}) :=
            measure_union_le _ _
        _ = K * P (A n) := by rw [hlawN n, hRHS n, hlawT n, hTop0 n, add_zero]
        _ ≤ K := mul_le_of_le_one_right' prob_le_one
    calc P Cl ≤ P (Cl ∩ A n) + P (A n)ᶜ := by
          refine (measure_mono fun ω hω => ?_).trans (measure_union_le _ _)
          by_cases h : ω ∈ A n
          · exact Or.inl ⟨hω, h⟩
          · exact Or.inr h
      _ ≤ K + P (A n)ᶜ := by gcongr
  -- the restart events exhaust the good event
  have hmonoA : Monotone A := fun n n' hnn' ω hω =>
    ⟨hω.1, show Th ω < ((n' : ℝ≥0) : ℝ≥0∞) from lt_of_lt_of_le hω.2 (by exact_mod_cast hnn')⟩
  have hcover : Nᶜ ⊆ ⋃ n, A n := fun ω hω => by
    obtain ⟨m, hm, -, -⟩ := hhit ω hω
    obtain ⟨n, hn⟩ := exists_nat_gt (m : ℝ)
    refine mem_iUnion.2 ⟨n, hω, ?_⟩
    show Th ω < ((n : ℝ≥0) : ℝ≥0∞)
    rw [hm]
    exact_mod_cast (show m < (n : ℝ≥0) by rw [← NNReal.coe_lt_coe]; exact_mod_cast hn)
  have hU : P (⋃ n, A n) = 1 := by
    refine le_antisymm prob_le_one ?_
    calc (1 : ℝ≥0∞) = P Nᶜ := by rw [prob_compl_eq_one_sub hNm0, hN0, tsub_zero]
      _ ≤ P (⋃ n, A n) := measure_mono hcover
  have hlim : Tendsto (fun n => P (A n)ᶜ) atTop (𝓝 0) := by
    have h1 := tendsto_measure_iUnion_atTop (μ := P) hmonoA
    rw [hU] at h1
    have e : (fun n => P (A n)ᶜ) = fun n => 1 - P (A n) := funext fun n => prob_compl_eq_one_sub (hAmeas n)
    rw [e]
    have h2 := ENNReal.Tendsto.sub (tendsto_const_nhds (x := (1 : ℝ≥0∞))) h1 (Or.inl ENNReal.one_ne_top)
    simpa using h2
  have h := ge_of_tendsto (tendsto_const_nhds.add hlim) (Eventually.of_forall hbound)
  simpa using h

/-- **No real terminal cluster point for a separated one-force law** (B.2 (E9); additional note Proposition 3.3, first
paragraph), `κ > 4`: for one left mark `p < 0` of weight `≥ κ/2 − 2` and no right mark, given (G5) for ordinary
`SLE_κ` at positive stopping times, almost surely no generating trace on `[0, ∞)` has a real terminal cluster point. -/
theorem IsIntegratedSLEEvolution.ae_noRealCluster_oneForce (hκ4 : 4 < κ)
    (hG5 : StoppingInverseBoundaryStatement.{u} κ) (hx : xL 0 < 0) (hρ : κ / 2 - 2 ≤ ρL 0)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η → NoRealCluster η := by
  have : IsProbabilityMeasure P := hE.1.1.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  have hκ : 0 < κ := by linarith
  have hnull : ∀ X x₀ q₀ : ℕ, P {ω | (¬ ∃ u, IsForwardSol (fun r : ℝ => W r.toNNReal ω)
      (((x₀ : ℝ) + 1 : ℝ) : ℂ) ((q₀ : ℝ≥0) + 1 : ℝ≥0) u) ∧
      ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η ∧
        ∃ x : ℝ, xL 0 - X ≤ x ∧ x < (x₀ : ℝ) + 1 ∧ IsTermCluster η x} = 0 := by
    intro X x₀ q₀
    set D : ℝ := max (X : ℝ) (-xL 0) with hD
    have hD0 : 0 < D := lt_of_lt_of_le (neg_pos.2 hx) (le_max_right _ _)
    have hlim := IsIntegratedSLEEvolution.tendsto_codeLaw_near hκ hx hρ hE
    refine le_antisymm (ge_of_tendsto hlim (Eventually.of_forall fun m => ?_)) bot_le
    have hL : 0 < D * ((m : ℝ) + 1) := by positivity
    have h := IsIntegratedSLEEvolution.measure_cluster_le_near hκ4 hG5 hx hρ hE (X := X) (x₀ := (x₀ : ℝ) + 1)
      hL (q₀ := (q₀ : ℝ≥0) + 1) (by positivity)
    have e : max (X : ℝ) (-xL 0) / (D * ((m : ℝ) + 1)) = 1 / ((m : ℝ) + 1) := by
      rw [← hD]; field_simp
    rwa [e] at h
  have hbad := ae_all_iff.2 fun X : ℕ => ae_all_iff.2 fun x₀ : ℕ => ae_all_iff.2 fun q₀ : ℕ =>
    measure_eq_zero_iff_ae_notMem.1 (hnull X x₀ q₀)
  have hsw := ae_all_iff.2 fun x₀ : ℕ =>
    IsIntegratedSLEEvolution.ae_realSwallowAt_oneForce hκ4 hx hρ hE (x₀ := (x₀ : ℝ) + 1) (by positivity)
  filter_upwards [hbad, hsw] with ω hbadω hswω η hη x
  have hnot : ¬ IsTermCluster η x := by
    intro hcl
    obtain ⟨X, hX⟩ := exists_nat_ge (xL 0 - x)
    obtain ⟨x₀, hx₀⟩ := exists_nat_ge x
    obtain ⟨σ, hσ⟩ := hswω x₀
    obtain ⟨q₀, hq₀⟩ := exists_nat_ge σ
    refine hbadω X x₀ q₀ ⟨?_, η, hη, x, by linarith, by linarith, hcl⟩
    rintro ⟨u, hu⟩
    refine hσ.2.2 ⟨u, isForwardSol_restrict hu hσ.1.le ?_⟩
    push_cast
    linarith
  rw [isTermCluster_iff_not, not_not] at hnot
  exact hnot

end Main

end InteractingSLE.ZhanGT4
