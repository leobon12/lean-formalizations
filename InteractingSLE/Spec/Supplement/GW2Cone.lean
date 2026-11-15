/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2ConeInputs
import InteractingSLE.Spec.Supplement.GW2aSingle

/-!
# Lemma GW2 (light-cone exhaustion) from its steps

Packet PROVE-T14-CONE. Lemma GW2 (supplement §25, `source/spec/p577-624.md` L989–L1038, pp. 621–623) as the named input
`Theorem14.GW2LightConeStatement`, proved from the four named steps of `GW2ConeInputs.lean` and Theorem 1.3
(`Exist.Theorem13Statement`, the complete transient counterflow trace at `16/κ > 4`).

Proved here (the parts of GW2's proof that use no conditional law):

* **Countability** (p. 621: "Intersect these countably many events before taking the closure"): the schedules with
  angles in a countable `Θ` and times in a countable `Q` form a countable set (`countable_setOf_isSchedule`), and the
  boundary roots are rational (`countable_lowerArcRoots`).
* **Containment of the closed union** (p. 621: "Properness makes the completed ambient range closed and proves
  containment of the whole family in that range"): `boundaryLightConeFamily_subset` and
  `CounterflowRange.isClosed_counterflowCompletedRange`.
* **The final density step** (p. 623: "Boundary time has zero occupation, so these tip times are dense in every
  nontrivial original-time interval. Continuity and the continuous terminal limit put the entire completed counterflow
  range in the closed family"): `neg_inv_mem_closure_of_rat`, `counterflowCompletedRange_subset_closure` — every point
  `−γ(t)⁻¹` of the range is a limit of interior tips at rational times (`CounterflowRange.exists_rat_mem_H_btwn`, from
  the zero boundary occupation of Lemma 2.5), and the terminal point `0` is added explicitly.
* **The assembly** `gw2LightConeStatement_of_inputs`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE

namespace Theorem14

namespace GW2Cone

open CounterflowRange

/-! ### Countability of the index sets of the GW2 family -/

/-- The finite schedules with angles in a countable `Θ` and times in a countable `Q` form a countable set. -/
theorem countable_setOf_isSchedule {Θ : Set ℝ} {Q : Set ℝ≥0} (hΘ : Θ.Countable) (hQ : Q.Countable) :
    {l | IsSchedule Θ Q l}.Countable := by
  have hS : (Θ ×ˢ Q).Countable := hΘ.prod hQ
  have : Countable (Θ ×ˢ Q) := hS.to_subtype
  refine (countable_range fun l : List (Θ ×ˢ Q) => l.map Subtype.val).mono ?_
  intro l hl
  have hl' : ∀ p ∈ l, p ∈ Θ ×ˢ Q := fun p hp => ⟨((show IsSchedule Θ Q l from hl).1 p hp).1,
    ((show IsSchedule Θ Q l from hl).1 p hp).2⟩
  refine ⟨l.pmap (fun p hp => (⟨p, hp⟩ : Θ ×ˢ Q)) hl', ?_⟩
  change List.map Subtype.val (l.pmap (fun p hp => (⟨p, hp⟩ : Θ ×ˢ Q)) hl') = l
  rw [List.map_pmap]
  exact (List.pmap_eq_map (f := id) _).trans (List.map_id l)

/-- The boundary roots of GW2 are rational, hence countable. -/
theorem countable_lowerArcRoots (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) :
    (lowerArcRoots κ b jumps).Countable := by
  unfold lowerArcRoots
  split_ifs
  · refine (countable_range fun q : ℚ => (q : ℝ)).mono fun v hv => ?_
    obtain ⟨q, rfl⟩ := hv.1
    exact ⟨q, rfl⟩
  · exact countable_empty

/-- The angles of a `Θ`-schedule lie in `[−π/2, π/2]` when `Θ ⊆ (−π/2, π/2)`. -/
theorem mem_Icc_of_isSchedule {Θ : Set ℝ} {Q : Set ℝ≥0} (hΘ : Θ ⊆ Ioo (-(Real.pi / 2)) (Real.pi / 2))
    {l : List (ℝ × ℝ≥0)} (hl : IsSchedule Θ Q l) : ∀ p ∈ l, p.1 ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) :=
  fun p hp => Ioo_subset_Icc_self (hΘ (hl.1 p hp).1)

/-! ### Containment of the family -/

/-- **The GW2 family is contained in a set `R`** once every schedule from `0`, every forced arc `[0, v]` and every
schedule from a boundary root `v` is (deterministic: the definition of `boundaryLightConeFamily`). -/
theorem boundaryLightConeFamily_subset {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Θ : Set ℝ} {Q : Set ℝ≥0}
    {D : ExplSpec → ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {R : Set ℂ}
    (h0 : ∀ l ∈ {l | IsSchedule Θ Q l}, ExplState.physSet κ b jumps ⟨0, true, scheduleProgram 0 l⟩
      (D ⟨0, true, scheduleProgram 0 l⟩) ⊆ R)
    (harc : ∀ v ∈ lowerArcRoots κ b jumps, ((↑) : ℝ → ℂ) '' Icc 0 v ⊆ R)
    (hv : ∀ v ∈ lowerArcRoots κ b jumps, ∀ l ∈ {l | IsSchedule Θ Q l},
      ExplState.physSet κ b jumps ⟨v, true, scheduleProgram 0 l⟩ (D ⟨v, true, scheduleProgram 0 l⟩) ⊆ R) :
    boundaryLightConeFamily κ b jumps Θ Q D ⊆ R := by
  unfold boundaryLightConeFamily
  exact union_subset (iUnion₂_subset h0)
    (iUnion₂_subset fun v hv' => union_subset (harc v hv') (iUnion₂_subset (hv v hv')))

/-! ### The final density step -/

/-- A continuous generating trace on `[0, ∞)` is continuous. -/
theorem continuous_of_isGeneratingTrace_top {W : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} (hγ : IsGeneratingTrace W ⊤ γ) :
    Continuous γ := by
  have := hγ.2.1
  simp only [le_top, ofPred_true] at this
  exact continuousOn_univ.1 this

/-- **Every physical point `−γ(t)⁻¹` of the counterflow is a limit of interior tips at rational times** (p. 623:
"Boundary time has zero occupation, so these tip times are dense in every nontrivial original-time interval.
Continuity … put[s] the entire completed counterflow range in the closed family"). If every interior physical tip
`−γ(q)⁻¹` at a rational time `q` lies in `closure F`, so does `−γ(t)⁻¹` for every `t` with `γ(t) ≠ 0`. -/
theorem neg_inv_mem_closure_of_rat {W : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} (hγ : IsGeneratingTrace W ⊤ γ)
    (hW : Continuous W) (hW0 : W 0 = 0) {F : Set ℂ}
    (hF : ∀ q : ℚ, γ (q : ℝ).toNNReal ∈ H → -(γ (q : ℝ).toNNReal)⁻¹ ∈ closure F) {t : ℝ≥0}
    (ht : γ t ≠ 0) : -(γ t)⁻¹ ∈ closure F := by
  have hγc := continuous_of_isGeneratingTrace_top hγ
  have hf : ContinuousAt (fun s => -(γ s)⁻¹) t := (hγc.continuousAt.inv₀ ht).neg
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.1 hf (ε / 2) (half_pos hε)
  have hlt : t < ((t : ℝ) + δ / 2).toNNReal := by
    rw [Real.lt_toNNReal_iff_coe_lt]
    linarith
  obtain ⟨q, hq1, hq2, -, hqH⟩ := exists_rat_mem_H_btwn hγ hW.continuousOn hW0 hlt le_top
  obtain ⟨y, hy, hdy⟩ := Metric.mem_closure_iff.1 (hF q hqH) (ε / 2) (half_pos hε)
  refine ⟨y, hy, ?_⟩
  have hq1' : (t : ℝ) < ((q : ℝ).toNNReal : ℝ) := NNReal.coe_lt_coe.2 hq1
  have hq2' : ((q : ℝ).toNNReal : ℝ) < (t : ℝ) + δ / 2 := Real.lt_toNNReal_iff_coe_lt.1 hq2
  have hd : dist (q : ℝ).toNNReal t < δ := by
    rw [NNReal.dist_eq, abs_of_pos (by linarith)]
    linarith
  calc dist (-(γ t)⁻¹) y ≤ dist (-(γ t)⁻¹) (-(γ (q : ℝ).toNNReal)⁻¹) + dist (-(γ (q : ℝ).toNNReal)⁻¹) y :=
        dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add (by rw [dist_comm]; exact hball hd) hdy
    _ = ε := add_halves ε

/-- **The completed counterflow range lies in the closed family** (p. 623), from the exhaustion at the interior tips
of rational times: the physical points by `neg_inv_mem_closure_of_rat`, the terminal point `0` explicitly. -/
theorem counterflowCompletedRange_subset_closure {W : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ}
    (hγ : IsGeneratingTrace W ⊤ γ) (hW : Continuous W) (hW0 : W 0 = 0) {F : Set ℂ}
    (hF : ∀ q : ℚ, γ (q : ℝ).toNNReal ∈ H → -(γ (q : ℝ).toNNReal)⁻¹ ∈ closure F) :
    counterflowCompletedRange W ⊆ closure (F ∪ {0}) := by
  unfold counterflowCompletedRange
  rw [tipSet_infinitySourceChart_top hγ hW hW0]
  rintro z (⟨t, ht, rfl⟩ | hz)
  · exact closure_mono subset_union_left (neg_inv_mem_closure_of_rat hγ hW hW0 hF ht)
  · exact subset_closure (Or.inr hz)

/-- **The closed union equals the completed counterflow range** (deterministic form of GW2's conclusion): if `F` is
contained in the range and every interior tip at a rational time is in `closure F`, then
`closure (F ∪ {0}) = counterflowCompletedRange W`, the range being closed by transience. -/
theorem closure_union_zero_eq {W : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} (hγ : IsGeneratingTrace W ⊤ γ)
    (hW : Continuous W) (hW0 : W 0 = 0) (htr : Tendsto (fun t => ‖γ t‖) atTop atTop) {F : Set ℂ}
    (hFR : F ⊆ counterflowCompletedRange W)
    (hF : ∀ q : ℚ, γ (q : ℝ).toNNReal ∈ H → -(γ (q : ℝ).toNNReal)⁻¹ ∈ closure F) :
    closure (F ∪ {0}) = counterflowCompletedRange W := by
  refine Subset.antisymm (closure_minimal (union_subset hFR ?_)
    (isClosed_counterflowCompletedRange hγ hW hW0 htr)) (counterflowCompletedRange_subset_closure hγ hW hW0 hF)
  exact singleton_subset_iff.2 (Or.inr rfl)

/-! ### Lemma GW2 -/

/-- **Lemma GW2** (unrestricted boundary-seeded light-cone exhaustion, supplement p. 621), as the named input
`Theorem14.GW2LightConeStatement`, from its four named steps (`GW2ConeInputs.lean`) and Theorem 1.3 (the complete
transient counterflow trace):
* the containment of the schedules from `0` (`GW2ScheduleContainmentStatement`), of the forced arcs `[0, v]`
  (`GW2ForcedArcStatement`) and of the schedules from the boundary roots `v` (`GW2ArcScheduleContainmentStatement`),
  intersected over the countably many schedules and roots, with the closedness of the range;
* the exhaustion at the interior tips of the counterflow at rational times (`GW2TipExhaustionStatement`, which
  supplies `Q`), followed by the density of these tips (zero boundary occupation) and continuity. -/
theorem gw2LightConeStatement_of_inputs (hT13 : Exist.Theorem13Statement.{u})
    (hC0 : GW2ScheduleContainmentStatement.{u}) (hArc : GW2ForcedArcStatement.{u})
    (hCv : GW2ArcScheduleContainmentStatement.{u}) (hEx : GW2TipExhaustionStatement.{u}) :
    GW2LightConeStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' Θ hΘ hΘc hΘd
  obtain ⟨Q, hQc, hQd, hQpos, hQ⟩ := hEx κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' Θ hΘ hΘc hΘd
  refine ⟨Q, hQc, hQd, hQpos, fun E hE => ?_⟩
  have hSc := countable_setOf_isSchedule hΘc hQc
  have hRc := countable_lowerArcRoots κ b jumps
  -- containment, simultaneously for the countably many schedules and roots
  have h0 : ∀ᵐ ω ∂P, ∀ l ∈ {l | IsSchedule Θ Q l}, ExplState.physSet κ b jumps ⟨0, true, scheduleProgram 0 l⟩
      (fun k => E ⟨0, true, scheduleProgram 0 l⟩ k ω) ⊆ counterflowCompletedRange (fun t => W' t ω) :=
    (ae_ball_iff hSc).2 fun l hl =>
      hC0 κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE l (mem_Icc_of_isSchedule hΘ hl) hl.2
  have harc : ∀ᵐ ω ∂P, ∀ v ∈ lowerArcRoots κ b jumps,
      ((↑) : ℝ → ℂ) '' Icc 0 v ⊆ counterflowCompletedRange (fun t => W' t ω) :=
    (ae_ball_iff hRc).2 fun v hv => hArc κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' v hv
  have hv : ∀ᵐ ω ∂P, ∀ v ∈ lowerArcRoots κ b jumps, ∀ l ∈ {l | IsSchedule Θ Q l},
      ExplState.physSet κ b jumps ⟨v, true, scheduleProgram 0 l⟩ (fun k => E ⟨v, true, scheduleProgram 0 l⟩ k ω) ⊆
        counterflowCompletedRange (fun t => W' t ω) :=
    (ae_ball_iff hRc).2 fun v hv => (ae_ball_iff hSc).2 fun l hl =>
      hCv κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE v hv l (mem_Icc_of_isSchedule hΘ hl) hl.2
  -- the complete transient counterflow trace (Theorem 1.3 at `16/κ`)
  obtain ⟨b', J', h', -, -, hfl⟩ := hcf
  have hκ' : 0 < 16 / κ := by positivity
  have hγ := GW2aSingle.ae_chosenTrace hT13 hκ' hfl
  have hdrv := Supp8.GB6.ae_driver_zero_continuousOn hfl
  have hγtop : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (GW2aSingle.chosenTrace W' ζ' ω) := by
    filter_upwards [hγ, hζ'] with ω hω hζ
    rw [hζ] at hω
    exact hω.1
  -- the exhaustion at the interior tips of rational times
  have hex : ∀ᵐ ω ∂P, ∀ q : ℚ, GW2aSingle.chosenTrace W' ζ' ω (q : ℝ).toNNReal ∈ H →
      -(GW2aSingle.chosenTrace W' ζ' ω (q : ℝ).toNNReal)⁻¹ ∈
        closure (boundaryLightConeFamily κ b jumps Θ Q (fun spec k => E spec k ω)) :=
    ae_all_iff.2 fun q => hQ E hE (GW2aSingle.chosenTrace W' ζ') hγtop (q : ℝ).toNNReal
  filter_upwards [hγ, hζ', hdrv, h0, harc, hv, hex] with ω hγω hζω hdω h0ω harcω hvω hexω
  rw [hζω] at hγω hdω
  have hWc : Continuous fun t => W' t ω := by
    have hc := hdω.2
    simp only [ENNReal.coe_lt_top, ofPred_true] at hc
    exact continuousOn_univ.1 hc
  exact closure_union_zero_eq hγω.1 hWc hdω.1 (hγω.2 rfl)
    (boundaryLightConeFamily_subset h0ω harcω hvω) hexω

end GW2Cone

end Theorem14

end InteractingSLE
