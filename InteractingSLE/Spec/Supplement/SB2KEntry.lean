/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2KReal

/-!
# SB2(1)'s entry point is measurable for the retained past (up to null sets)

Packet PROVE-T14-SB2FIN5, the first open item of PROVE-T14-SB2FIN4's round 2: K2
(`SB.Cond.isCondFlowLineDriverOn_of_markedKernel`, through FIN4's `exists_k2ChartInputs`) needs SB2(1)'s entry point
`m = Lv.launchEntry … k u` as a function measurable for the lower walk's retained past `pastSigma k`.

* `ae_arcs_subset_Ici`: under GW1's ambient bound every connector of the lower walk lies in `[0, ∞)` almost surely
  (no left threshold, `GW1W.ae_status_ne_left_right_walk`; `GW1Conn.arcs_subset_Ici_of_forall_ne`);
* `launchEntry_eq_of_run_eq`: the launch event and the entry point are functions of the run through `k` instructions;
* **`exists_measurable_realMin`**: a measurable version of `L = realMin (lowerPrefix …)` on a measurable conull event
  of launches (`SB2KReal`: `L < q` iff `u < q` or a launched piece has a real point left of `q`, a measurable event);
* **`exists_measurable_launchEntry_amb`**: a measurable version of the entry point: `m = lim_N e(x_N)` for the dyadic
  points `x_N = (⌈2ᴺ L⌉ − 1)/2ᴺ ↑ L`, with `e(x) = lim_n Re c(x + i/(n + 1))` the real boundary values of the launch
  chart (FIN3's `isLeftEntryValue_launchChart`);
* **`exists_measurable_launchEntry`**: a `pastSigma k`-measurable `m'` equal to the entry point almost surely on the
  launch event (`exists_measurable_eq_of_frozen`: the entry point is frozen under the regular conditional laws given
  the past, `Exist.StagedLaw.ae_ae_run_eq`);
* **`exists_k2ChartInputs_launch`**: with FIN4's `exists_k2ChartInputs`, K2's chart and word inputs in the recentred
  version chart, which is almost surely SB2(1)'s chart `(launchChart k).recenter (launchEntry k u)` on the launch event
  (the premise of `IsCondFlowLineDriverOn.congr_chart`).

The statements take the lower walk's program as `w` with `hw : w = boundaryWalkSpec b jumps (−π/2) true` (pass
`rfl`).

Families regular at every sample (the form of `SB2RelCoreCfRegStatement`); GW1's ambient bound is a hypothesis (in
the counterflow setting it is `GW1Conn.ambient_bounds`). No named input.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (chiC H)

universe u

namespace InteractingSLE.Theorem14.SB.Lv

open Exist.Staged Exist.StagedLaw

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- After the end of its program a run does not change. -/
theorem run_eq_of_length_le (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) {n : ℕ} (hn : spec.2.2.length ≤ n) :
    ExplState.run κ b jumps spec D n = ExplState.run κ b jumps spec D spec.2.2.length := by
  induction n, hn using Nat.le_induction with
  | base => rfl
  | succ n hn ih => rw [Ly.run_succ_of_length_le spec D hn, ih]

/-- **Every connector of the lower walk lies in `[0, ∞)`, almost surely**, under GW1's ambient bound. -/
theorem ae_arcs_subset_Ici (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hS : IsStagedHistory κ b jumps P h (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) E)
    (hreg : ∀ j ω, IsRegularDriver (E j ω))
    (hamb : ∀ t, t < 0 → t ∉ jumps → b t + -(Real.pi / 2) * chiC κ < sleLambda κ) :
    ∀ᵐ ω ∂P, ∀ n, ∀ a ∈ (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun j => E j ω) n).2.1, a ⊆ Ici 0 := by
  filter_upwards [GW1W.ae_status_ne_left_right_walk hκ hb hh hS hreg hamb] with ω hno
  have hfull := GW1Conn.arcs_subset_Ici_of_forall_ne (Ly.leftLim_zero_lt_of_bound hb hamb) (fun j => E j ω)
    (fun k => hno k)
  intro n a ha
  rcases le_total n (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length with hn | hn
  · exact hfull a (WalkIntChrono.mem_arcs_run_mono _ _ ha hn)
  · rw [run_eq_of_length_le _ _ hn] at ha
    exact hfull a ha

/-- **The launch event and the entry point are functions of the run through `k` instructions.** -/
theorem launchEntry_eq_of_run_eq {Ω : Type*} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u : ℝ}
    {ω ω' : Ω}
    (h : ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) k =
      ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω') k) :
    (ω ∈ launchSet κ b jumps E k ↔ ω' ∈ launchSet κ b jumps E k) ∧
      launchEntry κ b jumps E k u ω = launchEntry κ b jumps E k u ω' := by
  have hl := launches_run_succ_of_run_eq (κ := κ) (b := b) (jumps := jumps) _ h
  refine ⟨by simp only [launchSet, mem_ofPred_eq, hl], ?_⟩
  have hc : launchChart κ b jumps E k ω = launchChart κ b jumps E k ω' := by
    simp only [launchChart, hl]
  have hp : lowerPrefix κ b jumps E k u ω = lowerPrefix κ b jumps E k u ω' := by
    simp only [lowerPrefix, prefixPhysSet, h]
  simp only [launchEntry, hc, hp]

/-- The hypothesis "the launched pieces are regular" at one sample. -/
def PiecesRegAt (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type*} (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (ω : Ω) : Prop :=
  ∀ (j : ℕ) (c : Chart) (θ : ℝ),
    (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) (j + 1)).2.2.2.1 j = some (c, θ) →
      GW1P.PieceRegular (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω).1
        (min (instrTime (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j)
          (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω).2)

/-- **A measurable version of the leftmost real point `L` of the retained prefix**, on a measurable conull event `M`
of samples with regular launched pieces, at the launches of instruction `k`. -/
theorem exists_measurable_realMin (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {w : ExplSpec} (hw : w = boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
    (hS : IsStagedHistory κ b jumps P h w (E w)) (hR : StagedPiecesRegular κ b jumps P w (E w))
    (hreg : ∀ j ω, IsRegularDriver (E w j ω))
    (hamb : ∀ t, t < 0 → t ∉ jumps → b t + -(Real.pi / 2) * chiC κ < sleLambda κ) (k : ℕ) {u : ℝ} (hu : u ≤ 0) :
    ∃ (M : Set Ω) (Lm : Ω → ℝ), MeasurableSet M ∧ (∀ᵐ ω ∂P, ω ∈ M) ∧ Measurable Lm ∧
      (∀ ω ∈ M, PiecesRegAt κ b jumps E ω) ∧
      ∀ ω ∈ M, ω ∈ launchSet κ b jumps E k → Lm ω = realMin (lowerPrefix κ b jumps E k u ω) := by
  subst hw
  set w : ExplSpec := boundaryWalkSpec b jumps (-(Real.pi / 2)) true with hwdef
  set G0 : Set Ω := {ω | PiecesRegAt κ b jumps E ω ∧
    ∀ n, ∀ a ∈ (ExplState.run κ b jumps w (fun j => E w j ω) n).2.1, a ⊆ Ici 0} with hG0def
  have hG0 : ∀ᵐ ω ∂P, ω ∈ G0 := by
    filter_upwards [hR, ae_arcs_subset_Ici hκ hb hh hS hreg hamb] with ω hr ha
    exact ⟨fun j c θ' hl => hr j θ' _ c (eq_launch_of_launches _ _ hl).1 hl, ha⟩
  set M : Set Ω := (toMeasurable P G0ᶜ)ᶜ with hMdef
  have hM : MeasurableSet M := (measurableSet_toMeasurable _ _).compl
  have hMG : M ⊆ G0 := fun ω hω => by
    by_contra hn
    exact hω (subset_toMeasurable P G0ᶜ hn)
  have hMae : ∀ᵐ ω ∂P, ω ∈ M := by
    rw [ae_iff]
    have e : {ω | ¬ ω ∈ M} = toMeasurable P G0ᶜ := by
      ext ω
      simp [hMdef]
    rw [e, measure_toMeasurable]
    exact ae_iff.1 hG0
  have hLS : MeasurableSet (launchSet κ b jumps E k) :=
    (runMeasStatement κ b jumps hb w (E w) hS.1 hreg k).1
  obtain ⟨S, hSm, hSiff⟩ := exists_measurableSet_physPiece_real hb w hS.1 hreg hM
    (fun ω hω => (hMG hω).1) k
  classical
  set F : Set Ω := M ∩ launchSet κ b jumps E k with hF
  refine ⟨M, fun ω => if ω ∈ F then realMin (lowerPrefix κ b jumps E k u ω) else 0, hM, hMae, ?_,
    fun ω hω => (hMG hω).1, fun ω hω hl => by simp only [hF, mem_inter_iff, hω, hl, and_self, ↓reduceIte]⟩
  refine measurable_of_Iio fun q => ?_
  have e : (fun ω => if ω ∈ F then realMin (lowerPrefix κ b jumps E k u ω) else 0) ⁻¹' Iio q =
      (F ∩ ({_ω | u < q} ∪ S q)) ∪ (Fᶜ ∩ {_ω | (0 : ℝ) < q}) := by
    ext ω
    by_cases hω : ω ∈ F
    · obtain ⟨hωM, hωl⟩ := hω
      obtain ⟨⟨c, θ⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hωl
      have hnd := Lx.stStatus_ne_done_of_launches _ _ hcθ
      have hAc := Lx.isCompact_lowerPrefix (u := u) (hMG hωM).1 hωl
      have h1 := realMin_lt_iff hu hAc ((hMG hωM).2 k) q
      have h2 := hSiff ω hωM hnd q
      simp only [mem_preimage, mem_Iio, hF, mem_inter_iff, hωM, hωl, and_self, ↓reduceIte, mem_union,
        mem_ofPred_eq, mem_compl_iff, not_true_eq_false, false_and, or_false, true_and]
      rw [h1, h2]
    · simp only [mem_preimage, mem_Iio, hω, ↓reduceIte, mem_union, mem_inter_iff, false_and, mem_compl_iff,
        not_false_eq_true, true_and, mem_ofPred_eq, false_or]
  rw [e]
  exact ((hM.inter hLS).inter ((MeasurableSet.const _).union (hSm q))).union
    ((hM.inter hLS).compl.inter (MeasurableSet.const _))

/-- The dyadic points `(⌈2ᴺ L⌉ − 1)/2ᴺ` increase to `L` from below. -/
theorem tendsto_dyadic_below (L : ℝ) :
    (∀ N : ℕ, (((⌈L * 2 ^ N⌉ - 1 : ℤ) : ℝ) / 2 ^ N) < L) ∧
      Tendsto (fun N : ℕ => (((⌈L * 2 ^ N⌉ - 1 : ℤ) : ℝ) / 2 ^ N)) atTop (𝓝[<] L) := by
  have hlt : ∀ N : ℕ, (((⌈L * 2 ^ N⌉ - 1 : ℤ) : ℝ) / 2 ^ N) < L := fun N => by
    have hp : (0 : ℝ) < 2 ^ N := by positivity
    rw [div_lt_iff₀ hp]
    push_cast
    linarith [Int.ceil_lt_add_one (L * 2 ^ N)]
  have hge : ∀ N : ℕ, L - 1 / 2 ^ N ≤ (((⌈L * 2 ^ N⌉ - 1 : ℤ) : ℝ) / 2 ^ N) := fun N => by
    have hp : (0 : ℝ) < 2 ^ N := by positivity
    rw [le_div_iff₀ hp, sub_mul, one_div, inv_mul_cancel₀ hp.ne']
    push_cast
    linarith [Int.le_ceil (L * 2 ^ N)]
  refine ⟨hlt, tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall hlt⟩⟩
  have h1 : Tendsto (fun N : ℕ => L - 1 / (2 : ℝ) ^ N) atTop (𝓝 L) := by
    have h2 := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    have e : (fun N : ℕ => L - 1 / (2 : ℝ) ^ N) = fun N : ℕ => L - (1 / 2 : ℝ) ^ N := by
      funext N
      rw [one_div_pow]
    rw [e]
    simpa using (tendsto_const_nhds (x := L)).sub h2
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le h1 tendsto_const_nhds hge fun N => (hlt N).le

/-- **A measurable version of SB2(1)'s entry point** on a measurable conull event: `m = lim_N e(x_N)` with
`x_N = (⌈2ᴺ L⌉ − 1)/2ᴺ ↑ L` and `e(x) = lim_n Re c(x + i/(n + 1))`, `c` the chart of the run (the launch chart). -/
theorem exists_measurable_launchEntry_amb (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {w : ExplSpec} (hw : w = boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
    (hS : IsStagedHistory κ b jumps P h w (E w)) (hR : StagedPiecesRegular κ b jumps P w (E w))
    (hreg : ∀ j ω, IsRegularDriver (E w j ω))
    (hamb : ∀ t, t < 0 → t ∉ jumps → b t + -(Real.pi / 2) * chiC κ < sleLambda κ) (k : ℕ) {u : ℝ} (hu : u ≤ 0) :
    ∃ Em : Ω → ℝ, Measurable Em ∧
      ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E k → Em ω = launchEntry κ b jumps E k u ω := by
  subst hw
  set w : ExplSpec := boundaryWalkSpec b jumps (-(Real.pi / 2)) true with hwdef
  obtain ⟨M, Lm, -, hMae, hLm, hMreg, hLmeq⟩ := exists_measurable_realMin hκ hb hh rfl hS hR hreg hamb k hu
  have hchart : ∀ z : ℂ, Measurable fun ω => (stChart (ExplState.run κ b jumps w (fun j => E w j ω) k)).1 z :=
    (runMeasStatement κ b jumps hb w (E w) hS.1 hreg k).2
  obtain ⟨bl, hbl⟩ : ∃ bl : ℝ → Ω → ℝ, bl = fun (x : ℝ) ω => limUnder atTop (fun n : ℕ =>
      ((stChart (ExplState.run κ b jumps w (fun j => E w j ω) k)).1
        ((x : ℂ) + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I)).re) := ⟨_, rfl⟩
  have hblm : ∀ x, Measurable (bl x) := fun x => by
    rw [hbl]
    exact (StronglyMeasurable.limUnder fun n =>
      (Complex.measurable_re.comp (hchart _)).stronglyMeasurable).measurable
  obtain ⟨zN, hzN⟩ : ∃ zN : ℕ → Ω → ℤ, zN = fun N ω => ⌈Lm ω * 2 ^ N⌉ - 1 := ⟨_, rfl⟩
  have hzNm : ∀ N, Measurable (zN N) := fun N => by
    rw [hzN]
    exact (measurable_of_countable (fun z : ℤ => z - 1)).comp (hLm.mul_const _).ceil
  have hENm : ∀ N, Measurable fun ω => bl ((zN N ω : ℝ) / 2 ^ N) ω := fun N =>
    (measurable_from_prod_countable_left (f := fun p : Ω × ℤ => bl ((p.2 : ℝ) / 2 ^ N) p.1)
      fun z => hblm ((z : ℝ) / 2 ^ N)).comp (measurable_id.prodMk (hzNm N))
  refine ⟨fun ω => limUnder atTop (fun N => bl ((zN N ω : ℝ) / 2 ^ N) ω),
    (StronglyMeasurable.limUnder fun N => (hENm N).stronglyMeasurable).measurable, ?_⟩
  filter_upwards [hMae] with ω hω hl
  obtain ⟨fe, hfe, hlim⟩ := Lx.isLeftEntryValue_launchChart (u := u) (hMreg ω hω) hl
  obtain ⟨⟨c, θ⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hl
  have hc : launchChart κ b jumps E k ω =
      stChart (ExplState.run κ b jumps w (fun j => E
          w j ω) k) := by
    rw [launchChart_eq hcθ, (eq_launch_of_launches _ _ hcθ).2.2]
  have hLL : Lm ω = realMin (lowerPrefix κ b jumps E k u ω) := hLmeq ω hω hl
  -- the boundary values are the limits along vertical segments
  have hbl_eq : ∀ x < realMin (lowerPrefix κ b jumps E k u ω), bl x ω = fe x := by
    intro x hx
    rw [hbl]
    have h1 := hfe x hx
    rw [hc] at h1
    have hseq : Tendsto (fun n : ℕ => (x : ℂ) + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I) atTop
        (𝓝[H] (x : ℂ)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => ?_⟩
      · have h0 : Tendsto (fun n : ℕ => ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝 ((0 : ℝ) : ℂ)) :=
          (Complex.continuous_ofReal.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
        simpa using (tendsto_const_nhds (x := (x : ℂ))).add (h0.mul_const Complex.I)
      · show 0 < ((x : ℂ) + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I).im
        simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
          mul_one, Complex.I_re, mul_zero, add_zero, zero_add]
        positivity
    have h2 := (Complex.continuous_re.tendsto _).comp (h1.comp hseq)
    simp only [Complex.ofReal_re] at h2
    exact h2.limUnder_eq
  obtain ⟨hxlt, hxt⟩ := tendsto_dyadic_below (realMin (lowerPrefix κ b jumps E k u ω))
  have hEN_eq : (fun N => bl ((zN N ω : ℝ) / 2 ^ N) ω) = fun N =>
      fe ((((⌈realMin (lowerPrefix κ b jumps E k u ω) * 2 ^ N⌉ - 1 : ℤ) : ℝ) / 2 ^ N)) := funext fun N => by
    rw [hzN]
    dsimp only
    rw [hLL]
    exact hbl_eq _ (hxlt N)
  have hT : Tendsto (fun N => bl ((zN N ω : ℝ) / 2 ^ N) ω) atTop (𝓝 (launchEntry κ b jumps E k u ω)) := by
    rw [hEN_eq]
    exact hlim.comp hxt
  exact hT.limUnder_eq

/-- **SB2(1)'s entry point is measurable for the retained past, up to null sets** (the first open item of K2's
application): a `pastSigma k`-measurable `m'` equals `launchEntry … k u` almost surely on the launch event. -/
theorem exists_measurable_launchEntry (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {w : ExplSpec} (hw : w = boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
    (hS : IsStagedHistory κ b jumps P h w (E w)) (hR : StagedPiecesRegular κ b jumps P w (E w))
    (hreg : ∀ j ω, IsRegularDriver (E w j ω))
    (hamb : ∀ t, t < 0 → t ∉ jumps → b t + -(Real.pi / 2) * chiC κ < sleLambda κ) (k : ℕ) {u : ℝ} (hu : u ≤ 0) :
    ∃ m' : Ω → ℝ, Measurable[pastSigma κ b jumps w (E w) k] m' ∧
      ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E k → m' ω = launchEntry κ b jumps E k u ω := by
  subst hw
  set w : ExplSpec := boundaryWalkSpec b jumps (-(Real.pi / 2)) true with hwdef
  obtain ⟨Em, hEm, hEq⟩ := exists_measurable_launchEntry_amb hκ hb hh rfl hS hR hreg hamb k hu
  refine exists_measurable_eq_of_frozen (hS.2.1 k) hEm hEq ?_
  filter_upwards [ae_ae_run_eq runMeasStatement hb w (k := k)
      (fun j _ => hS.1 j)
    (fun j _ => hreg j)]
    with ω₀ h₀ hF
  filter_upwards [h₀] with ω hω
  have e := launchEntry_eq_of_run_eq (u := u) hω
  exact ⟨e.1.2 hF, e.2⟩

/-- **K2's chart and word inputs for SB2(1) at a launch** (FIN4's `exists_k2ChartInputs` with the past-measurable
entry point of `exists_measurable_launchEntry`): a `pastSigma k`-measurable entry point `m'` and word `cw`, the
measurable recentred version chart, which almost surely on the launch event is SB2(1)'s chart
`(launchChart k).recenter (launchEntry k u)` (the hypothesis of `IsCondFlowLineDriverOn.congr_chart`), K2's `hG` at
living states and K2's `hcc`. -/
theorem exists_k2ChartInputs_launch (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {w : ExplSpec} (hw : w = boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
    (hS : IsStagedHistory κ b jumps P h w (E w)) (hR : StagedPiecesRegular κ b jumps P w (E w))
    (hreg : ∀ j ω, IsRegularDriver (E w j ω))
    (hamb : ∀ t, t < 0 → t ∉ jumps → b t + -(Real.pi / 2) * chiC κ < sleLambda κ) (k : ℕ) {u : ℝ} (hu : u ≤ 0) :
    ∃ (m' : Ω → ℝ) (cw : Ω → Restart.BoundaryWord),
      Measurable[pastSigma κ b jumps w (E w) k] m' ∧ Measurable[pastSigma κ b jumps w (E w) k] cw ∧
      WalkInf.IsMeasChart (pastSigma κ b jumps w (E w) k)
        (fun ω => (WalkInf.verChart κ b jumps w (E w) k ω).recenter (m' ω)) ∧
      (∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E k →
        (WalkInf.verChart κ b jumps w (E w) k ω).recenter (m' ω) =
          (launchChart κ b jumps E k ω).recenter (launchEntry κ b jumps E k u ω)) ∧
      (∀ᵐ ω₀ ∂P, GW2aConn.IsLive (ExplState.run κ b jumps w (fun j => E w j ω₀) k) →
        IsPiecewiseConstantBoundaryData (cw ω₀).fn (cw ω₀).jumps ∧
        ∃ h' : Ω → LQGMetric.DistOn upperHalfPlaneOpens,
          (∀ ω, IsChartTransport ((WalkInf.verChart κ b jumps w (E w) k ω₀).recenter (m' ω₀)) 1 0 (chiC κ)
            (h ω) (h' ω)) ∧
          IsGFFWithBoundaryData (condExpKernel P (pastSigma κ b jumps w (E w) k) ω₀) h' (cw ω₀).fn
            (cw ω₀).jumps) ∧
      ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps w (E w) k) ω₀),
        (WalkInf.verChart κ b jumps w (E w) k ω).recenter (m' ω) =
          (WalkInf.verChart κ b jumps w (E w) k ω₀).recenter (m' ω₀) := by
  subst hw
  set w : ExplSpec := boundaryWalkSpec b jumps (-(Real.pi / 2)) true with hwdef
  obtain ⟨m', hm', hmeq⟩ := exists_measurable_launchEntry hκ hb hh rfl hS hR hreg hamb k hu
  obtain ⟨cw, hcw, hmc, hver, hG, hcc⟩ := exists_k2ChartInputs hκ hb hh (by simp [hwdef, boundaryWalkSpec])
    (by simp [hwdef, boundaryWalkSpec]) hS hR hreg k hm'
  refine ⟨m', cw, hm', hcw, hmc, ?_, hG, hcc⟩
  filter_upwards [hmeq, hver] with ω hm hv hl
  obtain ⟨⟨c, θ⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hl
  rw [hv, hm hl, launchChart_eq hcθ, (eq_launch_of_launches _ _ hcθ).2.2]
  rfl

/-! ### The living states at the launches after the first -/

/-- A launch never produces the root status. -/
theorem stStatus_launch_ne_root (s : ExplState) (k : ℕ) (D : (ℝ≥0 → ℝ) × ℝ≥0∞) (θ : ℝ) (t : ℝ≥0∞) :
    stStatus (ExplState.launch s k D θ t) ≠ .inl () := by
  by_cases htop : min t D.2 = ⊤
  · rw [Lx.stStatus_launch_of_top s k D θ t htop]
    exact Sum.inr_ne_inl
  · rcases GW2aConn.launch_status_cases (s := s) (k := k) (θ := θ) htop with h | h | h | h | h <;> rw [h] <;>
      exact Sum.inr_ne_inl

/-- **A step never creates the root status.** -/
theorem stStatus_run_succ_eq_root (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) {n : ℕ}
    (h : stStatus (ExplState.run κ b jumps spec D (n + 1)) = .inl ()) :
    stStatus (ExplState.run κ b jumps spec D n) = .inl () := by
  rw [run_succ] at h
  cases hk : spec.2.2[n]? with
  | none => rw [hk] at h; exact h
  | some ins =>
    rw [hk] at h
    rcases ins with ⟨θ, t⟩ | pref | ⟨v, pref⟩
    · change stStatus (ExplState.flowStep κ b spec.2.1 (ExplState.run κ b jumps spec D n) n (D n) θ t) = _ at h
      rcases flowStep_trichotomy (κ := κ) (b := b) spec.2.1 (ExplState.run κ b jumps spec D n) n (D n) θ t
        with e | e | e <;> rw [e] at h
      · exact h
      · exact absurd h Sum.inr_ne_inl
      · exact absurd h (stStatus_launch_ne_root _ _ _ _ _)
    all_goals
      change stStatus (ExplState.contStep κ b jumps (ExplState.run κ b jumps spec D n) _ pref) = _ at h
      rcases contStep_cases (κ := κ) (b := b) (jumps := jumps) (ExplState.run κ b jumps spec D n) _ pref
        with e | e | ⟨r, x, m, e⟩ | ⟨r, e⟩ <;> rw [e] at h
      · exact h
      · exact absurd h Sum.inr_ne_inl
      · exact absurd h Sum.inr_ne_inl
      · exact absurd h Sum.inr_ne_inl

/-- After a launch the run never returns to the root status. -/
theorem stStatus_run_ne_root (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) {j n : ℕ} (hjn : j < n)
    (hl : (ExplState.run κ b jumps spec D (j + 1)).2.2.2.1 j ≠ none) :
    stStatus (ExplState.run κ b jumps spec D n) ≠ .inl () := by
  obtain ⟨⟨c, θ⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hl
  obtain ⟨-, he, -⟩ := eq_launch_of_launches (κ := κ) (b := b) (jumps := jumps) spec D hcθ
  induction n, (Nat.succ_le_of_lt hjn : j + 1 ≤ n) using Nat.le_induction with
  | base => rw [he]; exact stStatus_launch_ne_root _ _ _ _ _
  | succ n hn ih => exact fun h => ih (Nat.lt_of_succ_le hn) (stStatus_run_succ_eq_root spec D h)

/-- A state at which an instruction launches is not terminal (neither done nor dead). -/
theorem not_isTerminal_of_launches (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) {k : ℕ}
    (hl : (ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 k ≠ none) :
    ¬ IsTerminal (ExplState.run κ b jumps spec D k) := by
  obtain ⟨⟨c, θ⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hl
  have h0 := launches_run_of_le (κ := κ) (b := b) (jumps := jumps) spec D (le_refl k)
  obtain ⟨hk, -, -⟩ := eq_launch_of_launches spec D hcθ
  intro hT
  rw [run_succ, hk] at hcθ
  simp only at hcθ
  change (ExplState.flowStep κ b spec.2.1 (ExplState.run κ b jumps spec D k) k (D k) θ
    (instrTime spec k)).2.2.2.1 k = some (c, θ) at hcθ
  have hfs : ExplState.flowStep κ b spec.2.1 (ExplState.run κ b jumps spec D k) k (D k) θ (instrTime spec k) =
      ExplState.run κ b jumps spec D k := by
    generalize ExplState.run κ b jumps spec D k = s at hT ⊢
    obtain ⟨pieces, arcs, ret, lau, chart, st, pt, ang, rR, rL⟩ := s
    rcases hT with hT | hT <;> change st = _ at hT <;> subst hT <;> rfl
  rw [hfs, h0] at hcθ
  exact absurd hcθ (by simp)

/-- **Every launch of the lower walk after the first happens at a living state** (`GW2aConn.IsLive`: not terminal,
not the root — instruction `0` always launches, `launches_zero`). -/
theorem isLive_of_launch_succ {Ω : Type*} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {ω : Ω}
    (hl : ω ∈ launchSet κ b jumps E (k + 1)) :
    GW2aConn.IsLive (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (k + 1)) := by
  refine ⟨not_isTerminal_of_launches _ _ hl, stStatus_run_ne_root _ _ (Nat.succ_pos k) ?_⟩
  rw [launches_zero (κ := κ) (b := b) (jumps := jumps) (E := E) ω]
  exact Option.some_ne_none _

/-- **K2's chart and word inputs at a launch `k + 1` of the lower walk, with `hG` on the launch event** (K2's form,
`F = launchSet (k + 1)`): `exists_k2ChartInputs_launch` with `isLive_of_launch_succ`. -/
theorem exists_k2ChartInputs_launch_succ (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {w : ExplSpec} (hw : w = boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
    (hS : IsStagedHistory κ b jumps P h w (E w)) (hR : StagedPiecesRegular κ b jumps P w (E w))
    (hreg : ∀ j ω, IsRegularDriver (E w j ω))
    (hamb : ∀ t, t < 0 → t ∉ jumps → b t + -(Real.pi / 2) * chiC κ < sleLambda κ) (k : ℕ) {u : ℝ} (hu : u ≤ 0) :
    ∃ (m' : Ω → ℝ) (cw : Ω → Restart.BoundaryWord),
      Measurable[pastSigma κ b jumps w (E w) (k + 1)] m' ∧ Measurable[pastSigma κ b jumps w (E w) (k + 1)] cw ∧
      WalkInf.IsMeasChart (pastSigma κ b jumps w (E w) (k + 1))
        (fun ω => (WalkInf.verChart κ b jumps w (E w) (k + 1) ω).recenter (m' ω)) ∧
      (∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) →
        (WalkInf.verChart κ b jumps w (E w) (k + 1) ω).recenter (m' ω) =
          (launchChart κ b jumps E (k + 1) ω).recenter (launchEntry κ b jumps E (k + 1) u ω)) ∧
      (∀ᵐ ω₀ ∂P, ω₀ ∈ launchSet κ b jumps E (k + 1) →
        IsPiecewiseConstantBoundaryData (cw ω₀).fn (cw ω₀).jumps ∧
        ∃ h' : Ω → LQGMetric.DistOn upperHalfPlaneOpens,
          (∀ ω, IsChartTransport ((WalkInf.verChart κ b jumps w (E w) (k + 1) ω₀).recenter (m' ω₀)) 1 0 (chiC κ)
            (h ω) (h' ω)) ∧
          IsGFFWithBoundaryData (condExpKernel P (pastSigma κ b jumps w (E w) (k + 1)) ω₀) h' (cw ω₀).fn
            (cw ω₀).jumps) ∧
      ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps w (E w) (k + 1)) ω₀),
        (WalkInf.verChart κ b jumps w (E w) (k + 1) ω).recenter (m' ω) =
          (WalkInf.verChart κ b jumps w (E w) (k + 1) ω₀).recenter (m' ω₀) := by
  obtain ⟨m', cw, hm', hcw, hmc, heq, hG, hcc⟩ :=
    exists_k2ChartInputs_launch hκ hb hh hw hS hR hreg hamb (k + 1) hu
  refine ⟨m', cw, hm', hcw, hmc, heq, ?_, hcc⟩
  filter_upwards [hG] with ω₀ hG₀ hF
  subst hw
  exact hG₀ (isLive_of_launch_succ hF)

end InteractingSLE.Theorem14.SB.Lv
