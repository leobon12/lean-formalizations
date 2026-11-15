/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6LineL3

/-!
# GB6's line locality, part 4: hulls at random times and the physical safe events (L4)

Packet PROVE-GB6-LINELOCAL, item (L4) of `planning/handoffs/PROVE-GB6-RELSAFE2.md` §4: GB6's safe events
`{a(t) < V, C ∩ K̃_{a(t)} = ∅}` (`a(t) = min(physClock t, V)`) are events of the physical σ-algebra at `t`.

* `measurableSet_disjoint_closedBall_fwdHull_rand`: the avoidance of a closed disc in `ℍ` by the hull of a continuous
  measurable driving process at a **measurable random time** is measurable (the tamed-flow coding of
  `Sec7.Lemma72D.disjoint_closedBall_fwdHull_iff_real`, with the rational times below the random time);
* `disjoint_iff_forall_exists_ballsK`, **`measurableSet_disjoint_fwdHull_rand`**: for every closed `D ⊆ ℂ` (a test
  support, a finite union of rational closed discs) the event `{D ∩ K_q = ∅}` is measurable (cover the compact slices
  `D ∩ {Im ≥ 1/(n+1)} ∩ B̄(0, n)` by rational discs inside `ℍ \ K_q`);
* `measurable_apply_randTime`: a continuous process read at a random time `τ ≤ a` is measurable when its values at
  deterministic times `d` are, traced on `{d ≤ a}` (dyadic approximation from below);
* the version's driver frozen at `a(t)` is physical; the version's stop is a path rule, so `{V ≤ a(t)}` is almost
  surely the physical event `{ρ(record, frozen driver) ≤ a(t)}`; the safe events are then physical up to null sets,
  and `physFilt` contains the null sets: **`gb6SafeMeasStatement`** (no input).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull tamedZ drive)

universe u

namespace InteractingSLE.Supp8.GB6LineL

open Supp8.GB6 Supp8.RelSafeS

/-! ### The hull of a driving process at a random time -/

section RandTime

variable {Ω : Type*} {m : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ}

/-- **Avoidance of a closed disc by the hull at a measurable random time is measurable** (continuous driving paths
with measurable coordinates). -/
theorem measurableSet_disjoint_closedBall_fwdHull_rand (hBc : ∀ ω, Continuous fun t => B t ω)
    (hBm : ∀ r, Measurable[m] (B r)) {q : Ω → ℝ} (hq : Measurable[m] q) (hq0 : ∀ ω, 0 ≤ q ω) {c : ℂ} {ε : ℝ}
    (hε : 0 < ε) (hcε : ε < c.im) :
    MeasurableSet[m] {ω | Disjoint (closedBall c ε) (fwdHull (drive 1 B ω) (q ω))} := by
  let _ : MeasurableSpace Ω := m
  have e : {ω | Disjoint (closedBall c ε) (fwdHull (drive 1 B ω) (q ω))} =
      ⋃ k : ℕ, ⋂ y : ℚ × ℚ, ⋂ (_ : Sec7.Coding.ratPt y ∈ closedBall c ε), ⋂ s : ℚ, ⋂ (_ : 0 ≤ (s : ℝ)),
        ({ω | q ω < s} ∪
          {ω | 2 * (1 / ((k : ℝ) + 1)) ≤ (tamedZ (drive 1 B ω) (1 / ((k : ℝ) + 1)) (Sec7.Coding.ratPt y) s).im}) := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_iInter, Set.mem_union]
    rw [Sec7.Lemma72D.disjoint_closedBall_fwdHull_iff_real (QuantumZipper.NonSwallow.continuous_drive_ns hBc 1 ω)
      (hq0 ω) hε hcε]
    refine exists_congr fun k => forall_congr' fun y => forall_congr' fun hy => forall_congr' fun s =>
      forall_congr' fun hs => ?_
    constructor
    · intro h
      by_cases hsq : (s : ℝ) ≤ q ω
      · exact Or.inr (h hsq)
      · exact Or.inl (lt_of_not_ge hsq)
    · rintro (h | h) hsq
      · exact absurd hsq (not_le.2 h)
      · exact h
  rw [e]
  refine MeasurableSet.iUnion fun k => MeasurableSet.iInter fun y => MeasurableSet.iInter fun _ =>
    MeasurableSet.iInter fun s => MeasurableSet.iInter fun hs => ?_
  have hmeas := (QuantumZipper.measurable_tamed_drive 1 (c := 1 / ((k : ℝ) + 1)) (by positivity) B hBc hs
    (fun r _ => hBm r)).1
  exact (measurableSet_lt hq measurable_const).union (measurableSet_le measurable_const
    (Complex.measurable_im.comp (hmeas.comp (measurable_const.prodMk measurable_id))))

/-- The slice of a set at height `≥ 1/(n+1)` and modulus `≤ n`. -/
def slice (D : Set ℂ) (n : ℕ) : Set ℂ := D ∩ {z | 1 / ((n : ℝ) + 1) ≤ z.im} ∩ closedBall 0 n

theorem isCompact_slice {D : Set ℂ} (hD : IsClosed D) (n : ℕ) : IsCompact (slice D n) :=
  (isCompact_closedBall 0 (n : ℝ)).inter_left (hD.inter (isClosed_le continuous_const Complex.continuous_im))

/-- **A closed set avoids a relatively closed subset `K` of `ℍ` iff each of its slices is covered by finitely many
rational closed discs of positive radius in `ℍ` that avoid `K`.** -/
theorem disjoint_iff_forall_exists_ballsK {D K : Set ℂ} (hD : IsClosed D) (hK : IsOpen (H \ K)) (hKH : K ⊆ H) :
    Disjoint D K ↔ ∀ n : ℕ, ∃ F : Finset (ℚ × ℚ × ℚ), (∀ b ∈ F, (0 : ℚ) < b.2.2) ∧ Coupling.ballsK F ⊆ H ∧
      slice D n ⊆ Coupling.ballsU F ∧ Disjoint (Coupling.ballsK F) K := by
  constructor
  · intro hd n
    have hsub : slice D n ⊆ H \ K := fun z hz => by
      have h0 : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      exact ⟨show 0 < z.im from lt_of_lt_of_le h0 hz.1.2, fun hzK => Set.disjoint_left.1 hd hz.1.1 hzK⟩
    obtain ⟨F, hF1, hF2⟩ := Coupling.exists_rationalBalls (isCompact_slice hD n) hK hsub
    refine ⟨F.filter fun b => (0 : ℚ) < b.2.2, fun b hb => (Finset.mem_filter.1 hb).2, ?_, ?_, ?_⟩
    · intro z hz
      simp only [Coupling.ballsK, mem_iUnion, Finset.mem_filter] at hz
      obtain ⟨b, ⟨hbF, -⟩, hzb⟩ := hz
      exact (hF2 (by simp only [Coupling.ballsK, mem_iUnion]; exact ⟨b, hbF, hzb⟩)).1
    · intro z hz
      have hz' := hF1 hz
      simp only [Coupling.ballsU, mem_iUnion] at hz' ⊢
      obtain ⟨b, hbF, hzb⟩ := hz'
      refine ⟨b, Finset.mem_filter.2 ⟨hbF, ?_⟩, hzb⟩
      have h0 : (0 : ℝ) < (b.2.2 : ℝ) := lt_of_le_of_lt dist_nonneg (mem_ball.1 hzb)
      exact_mod_cast h0
    · refine Set.disjoint_left.2 fun z hz hzK => ?_
      simp only [Coupling.ballsK, mem_iUnion, Finset.mem_filter] at hz
      obtain ⟨b, ⟨hbF, -⟩, hzb⟩ := hz
      exact (hF2 (by simp only [Coupling.ballsK, mem_iUnion]; exact ⟨b, hbF, hzb⟩)).2 hzK
  · intro h
    refine Set.disjoint_left.2 fun z hzD hzK => ?_
    have hzH : 0 < z.im := hKH hzK
    obtain ⟨n₁, hn₁⟩ := exists_nat_one_div_lt hzH
    obtain ⟨n₂, hn₂⟩ := exists_nat_ge ‖z‖
    set n := max n₁ n₂ with hn
    have hzs : z ∈ slice D n := by
      refine ⟨⟨hzD, ?_⟩, ?_⟩
      · have : 1 / ((n : ℝ) + 1) ≤ 1 / ((n₁ : ℝ) + 1) := by
          gcongr
          exact_mod_cast le_max_left n₁ n₂
        exact (this.trans hn₁.le)
      · rw [mem_closedBall, dist_zero_right]
        exact hn₂.trans (by exact_mod_cast le_max_right n₁ n₂)
    obtain ⟨F, -, -, hsF, hFK⟩ := h n
    exact Set.disjoint_left.1 hFK (Coupling.ballsU_subset_ballsK F (hsF hzs)) hzK

/-- **Avoidance of a closed set by the hull at a measurable random time is measurable.** -/
theorem measurableSet_disjoint_fwdHull_rand (hBc : ∀ ω, Continuous fun t => B t ω)
    (hBm : ∀ r, Measurable[m] (B r)) {q : Ω → ℝ} (hq : Measurable[m] q) (hq0 : ∀ ω, 0 ≤ q ω) {D : Set ℂ}
    (hD : IsClosed D) : MeasurableSet[m] {ω | Disjoint D (fwdHull (drive 1 B ω) (q ω))} := by
  let _ : MeasurableSpace Ω := m
  have e : {ω | Disjoint D (fwdHull (drive 1 B ω) (q ω))} =
      ⋂ n : ℕ, ⋃ F : Finset (ℚ × ℚ × ℚ),
        ⋃ (_ : (∀ b ∈ F, (0 : ℚ) < b.2.2) ∧ Coupling.ballsK F ⊆ H ∧ slice D n ⊆ Coupling.ballsU F),
          ⋂ b ∈ F, {ω | Disjoint (closedBall (Coupling.ratCentre b) (b.2.2 : ℝ))
            (fwdHull (drive 1 B ω) (q ω))} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_iInter, exists_prop]
    rw [disjoint_iff_forall_exists_ballsK hD
      (QuantumZipper.FwdHolo.isOpen_compl_fwdHull (QuantumZipper.NonSwallow.continuous_drive_ns hBc 1 ω) (hq0 ω))
      (fun z hz => hz.1)]
    refine forall_congr' fun n => exists_congr fun F => ?_
    have hiff : Disjoint (Coupling.ballsK F) (fwdHull (drive 1 B ω) (q ω)) ↔ ∀ b ∈ F,
        Disjoint (closedBall (Coupling.ratCentre b) (b.2.2 : ℝ)) (fwdHull (drive 1 B ω) (q ω)) := by
      simp only [Coupling.ballsK, disjoint_iUnion_left]
    rw [hiff]
    tauto
  rw [e]
  refine MeasurableSet.iInter fun n => MeasurableSet.iUnion fun F => MeasurableSet.iUnion fun hF => ?_
  refine Finset.measurableSet_biInter F fun b hb => ?_
  have hε : (0 : ℝ) < (b.2.2 : ℝ) := by exact_mod_cast hF.1 b hb
  have hsub : closedBall (Coupling.ratCentre b) (b.2.2 : ℝ) ⊆ H := fun z hz =>
    hF.2.1 (by simp only [Coupling.ballsK, mem_iUnion]; exact ⟨b, hb, hz⟩)
  have hcε : (b.2.2 : ℝ) < (Coupling.ratCentre b).im := by
    set c := Coupling.ratCentre b
    have hmem : c - ((b.2.2 : ℝ) : ℂ) * Complex.I ∈ closedBall c (b.2.2 : ℝ) := by
      rw [mem_closedBall, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_mul, Complex.norm_I, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
    have h1 : 0 < (c - ((b.2.2 : ℝ) : ℂ) * Complex.I).im := hsub hmem
    simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one, Complex.ofReal_im,
      Complex.I_re, mul_zero, add_zero] at h1
    linarith
  exact measurableSet_disjoint_closedBall_fwdHull_rand hBc hBm hq hq0 hε hcε

end RandTime

/-! ### A continuous process read at a random time -/

section Apply

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- The grid time below `x` at mesh `1/(n+1)`. -/
def gridBelow (n : ℕ) (x : ℝ≥0) : ℝ≥0 := (⌊x * ((n : ℝ≥0) + 1)⌋₊ : ℝ≥0) / ((n : ℝ≥0) + 1)

theorem gridBelow_le (n : ℕ) (x : ℝ≥0) : gridBelow n x ≤ x := by
  unfold gridBelow
  rw [div_le_iff₀ (by positivity)]
  exact Nat.floor_le (by positivity)

theorem tendsto_gridBelow (x : ℝ≥0) : Tendsto (fun n => gridBelow n x) atTop (𝓝 x) := by
  rw [← NNReal.tendsto_coe]
  have hup : ∀ n : ℕ, ((gridBelow n x : ℝ≥0) : ℝ) ≤ x := fun n => by exact_mod_cast gridBelow_le n x
  have hlow : ∀ n : ℕ, (x : ℝ) - 1 / ((n : ℝ) + 1) ≤ (gridBelow n x : ℝ) := fun n => by
    have h1 := Nat.lt_floor_add_one (x * ((n : ℝ≥0) + 1))
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h1' : (x : ℝ) * ((n : ℝ) + 1) < (⌊x * ((n : ℝ≥0) + 1)⌋₊ : ℝ) + 1 := by exact_mod_cast h1
    have e : ((gridBelow n x : ℝ≥0) : ℝ) = (⌊x * ((n : ℝ≥0) + 1)⌋₊ : ℝ) / ((n : ℝ) + 1) := by
      simp only [gridBelow, NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_add, NNReal.coe_one]
    rw [e, sub_le_iff_le_add, ← add_div, le_div_iff₀ hpos]
    linarith
  have hl : Tendsto (fun n : ℕ => (x : ℝ) - 1 / ((n : ℝ) + 1)) atTop (𝓝 (x : ℝ)) := by
    simpa using (tendsto_const_nhds (x := (x : ℝ))).sub tendsto_one_div_add_atTop_nhds_zero_nat
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hl tendsto_const_nhds hlow hup

/-- **A continuous process read at a random time `τ ≤ a` is measurable** when its values at deterministic times `d`
are measurable on `{d ≤ a}` (dyadic-type approximation of `τ` from below). -/
theorem measurable_apply_randTime {R : ℝ≥0 → Ω → ℝ} (hRc : ∀ ω, Continuous fun u => R u ω)
    {a : Ω → ℝ≥0∞} {τ : Ω → ℝ≥0} (hτ : Measurable[m] τ) (hτa : ∀ ω, (τ ω : ℝ≥0∞) ≤ a ω)
    (hRa : ∀ (d : ℝ≥0) {B : Set ℝ}, MeasurableSet B →
      MeasurableSet[m] ({ω | (d : ℝ≥0∞) ≤ a ω} ∩ R d ⁻¹' B)) :
    Measurable[m] fun ω => R (τ ω) ω := by
  let _ : MeasurableSpace Ω := m
  have hfm : ∀ n, Measurable fun ω => R (gridBelow n (τ ω)) ω := by
    intro n
    have hk : Measurable fun ω => ⌊τ ω * ((n : ℝ≥0) + 1)⌋₊ := Nat.measurable_floor.comp (hτ.mul_const _)
    intro B hB
    have e : (fun ω => R (gridBelow n (τ ω)) ω) ⁻¹' B = ⋃ k : ℕ, ({ω | ⌊τ ω * ((n : ℝ≥0) + 1)⌋₊ = k} ∩
        ({ω | (((k : ℝ≥0) / ((n : ℝ≥0) + 1) : ℝ≥0) : ℝ≥0∞) ≤ a ω} ∩
          R ((k : ℝ≥0) / ((n : ℝ≥0) + 1)) ⁻¹' B)) := by
      ext ω
      simp only [mem_preimage, mem_iUnion, mem_inter_iff, mem_ofPred_eq]
      constructor
      · intro h
        exact ⟨_, rfl, (ENNReal.coe_le_coe.2 (gridBelow_le n (τ ω))).trans (hτa ω), h⟩
      · rintro ⟨k, hk, -, h⟩
        rw [gridBelow, hk]
        exact h
    rw [e]
    exact MeasurableSet.iUnion fun k => (hk (measurableSet_singleton k)).inter (hRa _ hB)
  refine measurable_of_tendsto_metrizable hfm (tendsto_pi_nhds.2 fun ω => ?_)
  exact ((hRc ω).tendsto (τ ω)).comp (tendsto_gridBelow (τ ω))

end Apply

/-! ### GB6's safe events are physical -/

section Safe

open Exist.StagedLaw Supp8.GB6 Supp8.RelSafe Supp8.RelSafeS

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {s : ℝ≥0} {W Wα : ℝ≥0 → Ω → ℝ}
  {ζα : Ω → ℝ≥0∞} {γ α : Ω → ℝ≥0 → ℂ} {GT : Set Ω} {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}

/-- **GB6's safe events are physical** (`RelSafeS.HasGB6SafeMeas`), for every R-form version and good set. For a
closed `D`, `{a(t) < V, D ∩ K̃_{a(t)} = ∅}` agrees almost surely with an event of the record, the version's driver
frozen at `a(t)` (physical: `measurable_apply_randTime`, `RelSafe.measurableSet_le_min_inter_drv`) and `a(t)`
(physical: `RelSafe.measurable_min_physClock`): `V ≤ a(t)` iff the path rule of the frozen driver is `≤ a(t)`, and
the hull at `a(t)` only sees the frozen driver. -/
theorem hasGB6SafeMeas_of (hGT : ∀ ω ∈ GT, PhysGood s W Wα ζα γ α ω) (hrec : Measurable (gb6Rec s Wα ζα))
    (hWm : ∀ r, Measurable (W r)) (hGTm : MeasurableSet GT)
    (hGTae : ∀ᵐ ω ∂P, ω ∈ GT ↔ gb6Rec s Wα ζα ω ∈ gb6TS s) (hver : HullId.IsGB6RelVersionR s P W Wα ζα γ α R V) :
    HasGB6SafeMeas P W Wα ζα GT s R V hrec hWm := by
  have hGTp : ∀ t, MeasurableSet[physFilt hrec hWm P t] GT := measurableSet_goodSet_physFilt hrec hWm hGTm hGTae
  suffices key : ∀ (D : Set ℂ), IsClosed D → ∀ t, MeasurableSet[physFilt hrec hWm P t]
      {ω | min (physClock s W Wα ζα GT t ω) (V ω) < V ω ∧ Disjoint D
        (fwdHull (fun r : ℝ => R r.toNNReal ω) (min (physClock s W Wα ζα GT t ω) (V ω)).toNNReal)} by
    exact ⟨fun ψ t => key _ (isClosed_tsupport ψ) t, fun Fb t => key _ (Coupling.isCompact_ballsK Fb).isClosed t⟩
  intro D hD t
  have ha := measurable_min_physClock hGT hrec hWm hGTp hver t
  obtain ⟨hv, ρ, hρm, hρ, hVρ⟩ := hver
  have ha' : Measurable[physFilt hrec hWm P t] fun ω => (min (physClock s W Wα ζα GT t ω) (V ω)).toNNReal :=
    ENNReal.measurable_toNNReal.comp ha
  -- the version's driver frozen at the clock is physical
  have hY : ∀ u, Measurable[physFilt hrec hWm P t]
      (fun ω => R (min u (min (physClock s W Wα ζα GT t ω) (V ω)).toNNReal) ω) := fun u =>
    measurable_apply_randTime (m := physFilt hrec hWm P t) hv.2.1
      (a := fun ω => min (physClock s W Wα ζα GT t ω) (V ω)) (measurable_const.min ha')
      (fun ω => (ENNReal.coe_le_coe.2 (min_le_right _ _)).trans ENNReal.coe_toNNReal_le_self)
      (fun d B hB => measurableSet_le_min_inter_drv hGT hrec hWm hGTp ⟨hv, ρ, hρm, hρ, hVρ⟩ t le_rfl hB)
  have hYc : ∀ ω, Continuous fun u => R (min u (min (physClock s W Wα ζα GT t ω) (V ω)).toNNReal) ω :=
    fun ω => (hv.2.1 ω).comp (continuous_id.min continuous_const)
  -- the disjointness event of the frozen driver is physical
  have hDis : MeasurableSet[physFilt hrec hWm P t] {ω | Disjoint D
      (fwdHull (drive 1 (fun u ω => R (min u (min (physClock s W Wα ζα GT t ω) (V ω)).toNNReal) ω) ω)
        ((min (physClock s W Wα ζα GT t ω) (V ω)).toNNReal : ℝ))} :=
    measurableSet_disjoint_fwdHull_rand hYc hY (measurable_coe_nnreal_real.comp ha') (fun ω => NNReal.coe_nonneg _) hD
  have hhull : ∀ ω, fwdHull (fun r : ℝ => R r.toNNReal ω) (min (physClock s W Wα ζα GT t ω) (V ω)).toNNReal =
      fwdHull (drive 1 (fun u ω => R (min u (min (physClock s W Wα ζα GT t ω) (V ω)).toNNReal) ω) ω)
        ((min (physClock s W Wα ζα GT t ω) (V ω)).toNNReal : ℝ) := fun ω => by
    refine LocalExt.fwdHull_congr_of_continuousOn ((hv.2.1 ω).comp continuous_real_toNNReal).continuousOn
      (QuantumZipper.NonSwallow.continuous_drive_ns hYc 1 ω).continuousOn (NNReal.coe_nonneg _) (lt_add_one _) ?_
    intro r hr
    simp only [drive, Real.sqrt_one, one_mul]
    rw [min_eq_left (Real.toNNReal_le_iff_le_coe.2 hr.2)]
  -- the stop: `V ≤ a(t)` iff the path rule of the frozen driver is `≤ a(t)`
  have hrecp := measurable_rec_physFilt (P := P) hrec hWm t
  have hpath : Measurable[physFilt hrec hWm P t]
      fun ω => fun u => R (min u (min (physClock s W Wα ζα GT t ω) (V ω)).toNNReal) ω :=
    (@measurable_pi_iff Ω ℝ≥0 (fun _ => ℝ) (physFilt hrec hWm P t) _ _).2 hY
  have hStop : MeasurableSet[physFilt hrec hWm P t] {ω | ρ (gb6Rec s Wα ζα ω,
      fun u => R (min u (min (physClock s W Wα ζα GT t ω) (V ω)).toNNReal) ω) ≤
        min (physClock s W Wα ζα GT t ω) (V ω)} :=
    measurableSet_le (hρm.comp (hrecp.prodMk hpath)) ha
  have hiff : ∀ᵐ ω ∂P, (min (physClock s W Wα ζα GT t ω) (V ω) < V ω ↔
      ¬ ρ (gb6Rec s Wα ζα ω, fun u => R (min u (min (physClock s W Wα ζα GT t ω) (V ω)).toNNReal) ω) ≤
        min (physClock s W Wα ζα GT t ω) (V ω)) := by
    filter_upwards [hVρ] with ω hV
    set a := min (physClock s W Wα ζα GT t ω) (V ω) with hadef
    rw [← not_le]
    refine not_congr ?_
    by_cases htop : a = ⊤
    · rw [htop]
      simp only [le_top]
    · have hcoe : ((a.toNNReal : ℝ≥0) : ℝ≥0∞) = a := ENNReal.coe_toNNReal htop
      constructor
      · intro hVa
        have hag : ∀ u : ℝ≥0, (u : ℝ≥0∞) ≤ ρ (gb6Rec s Wα ζα ω, fun u => R u ω) →
            R u ω = R (min u a.toNNReal) ω := fun u hu => by
          have h1 : (u : ℝ≥0∞) ≤ ((a.toNNReal : ℝ≥0) : ℝ≥0∞) := by
            rw [hcoe]
            exact (hu.trans (le_of_eq hV.symm)).trans hVa
          rw [min_eq_left (ENNReal.coe_le_coe.1 h1)]
        rw [hρ _ _ _ hag, ← hV]
        exact hVa
      · intro hρa
        have hag : ∀ u : ℝ≥0, (u : ℝ≥0∞) ≤ ρ (gb6Rec s Wα ζα ω, fun u => R (min u a.toNNReal) ω) →
            R (min u a.toNNReal) ω = R u ω := fun u hu => by
          have h1 : (u : ℝ≥0∞) ≤ ((a.toNNReal : ℝ≥0) : ℝ≥0∞) := by
            rw [hcoe]
            exact hu.trans hρa
          rw [min_eq_left (ENNReal.coe_le_coe.1 h1)]
        rw [hV, hρ _ _ _ hag]
        exact hρa
  have hEm : MeasurableSet {ω | min (physClock s W Wα ζα GT t ω) (V ω) < V ω ∧ Disjoint D
      (fwdHull (fun r : ℝ => R r.toNNReal ω) (min (physClock s W Wα ζα GT t ω) (V ω)).toNNReal)} := by
    have h1 : MeasurableSet {ω | min (physClock s W Wα ζα GT t ω) (V ω) < V ω} :=
      measurableSet_lt (ha.mono ((physFilt hrec hWm P).le t) le_rfl) hv.2.2.2.2.1
    have h2 := (physFilt hrec hWm P).le t _ hDis
    simp only [← hhull] at h2
    exact h1.inter h2
  refine measurableSet_of_ae_eq ((physFilt hrec hWm P).le t) (nullSets_le_physFilt hrec hWm P t) hEm
    (hStop.compl.inter hDis) ?_
  filter_upwards [hiff] with ω hω
  show (ω ∈ {ω | _}) = (ω ∈ _ ∩ _)
  simp only [mem_ofPred_eq, mem_inter_iff, mem_compl_iff, hhull ω, hω]

end Safe

/-! ### (L4) and the reduction to (L3) -/

/-- **(L4) proved: GB6's safe events are physical** (no input). -/
theorem gb6SafeMeasStatement : GB6SafeMeasStatement.{u} := by
  intro κ θ hκ hκ4 hθ₁ hθ₂ Ω mΩ P hP h b J W Wα ζ ζα γ α b' J' h' hb hG hb' hT hcf hadmL hadmR hcomp hfl hα s Hc
    hHcm hHc c hcJ hcb W' hW'm hWW GT hGT hGTm hGTae R V hver
  exact hasGB6SafeMeas_of hGT (measurable_recOf_cfE hfl s).2 hW'm hGTm hGTae hver

/-- **`GB6LineLocalStatement` from Theorems 1.2–1.3 and the union mean identification (L3).** -/
theorem gb6LineLocalStatement_of_mean (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (hM : GB6LineMeanStatement.{u}) : GB6LineLocalStatement.{u} :=
  gb6LineLocalStatement_of_mean_safe h12 h13 hM gb6SafeMeasStatement

/-- **Theorem 1.4's `GB6HullDetStatement` from Theorems 1.2–1.3 and the union mean identification (L3).** -/
theorem gb6HullDetStatement_of_mean (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (hM : GB6LineMeanStatement.{u}) : Supp8.GB6.GB6HullDetStatement.{u} :=
  gb6HullDetStatement_of_lineLocal (gb6LineLocalStatement_of_mean h12 h13 hM)

end InteractingSLE.Supp8.GB6LineL
