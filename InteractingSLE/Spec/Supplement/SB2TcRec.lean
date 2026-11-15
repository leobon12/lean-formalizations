/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2TcGeo
import InteractingSLE.Spec.Supplement.SB2KdInputs
import InteractingSLE.Spec.Supplement.SB2DrvPath
import InteractingSLE.Spec.Supplement.SB2HWire
import InteractingSLE.Spec.Supplement.SB2GLift
import InteractingSLE.Spec.Supplement.SBLwReg

/-!
# SB2(1)'s chain record almost surely (geometric and chart clauses)

Packet PROVE-AUX61-NOJUMP (Theorem 1.4, SB2(1)'s version half under ruling R108: the chain record at one time).
Almost surely at a launch of the lower walk, for every physical horizon `T ≤ ζ` after the entrance `T_L` and every
`0 < S₁` with `T_L + S₁ < T`, the geometric and chart clauses of the chain record hold in the coordinates shifted by
the upper seed `u`:

* `liftRealOn_shiftChart`: the real-vanishing lift survives the shift `shiftChart c u m`;
* `chartClause_of_launch` (deterministic): at a launch with regular pieces and an entry value `m` at `L`, the shifted
  launch chart is a left entry chart of `A − u` at `L − u`, with a boundary map and real-vanishing lift;
* `interior_im_eq_zero_of_dense` / `interior_mem_eq_empty_of_noArc`: the no-real-arc condition from the density of
  the times in `ℍ` (`Lw.ae_flowLine_regular`, Theorem 1.3), the no-common-arc condition from Lemma S3;
* **`SB2EntranceNoCommonArcStatement`** (named input, Lemma S3 in SB2(1)'s configuration, supplement pp. 579, 632):
  after its entrance at `L = min(A ∩ ℝ)`, the upper flow shares no open arc with the retained lower prefix `A`;
* **`ae_lineGeom`**: the clauses almost surely, from Theorem 1.3 and the named input.

**R48.** Theorem 1.3 enters as a hypothesis; this serves Theorem 1.4 only.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Tc

open Lv Exist.Staged Exist.StagedLaw

/-! ### The real-vanishing lift of the shifted chart -/

/-- The shift `z ↦ z + u` maps the domain of `shiftChart c u m` into the domain of `c`. -/
theorem mapsTo_dom_shiftChart (c : Chart) (u m : ℝ) :
    MapsTo (fun z : ℂ => z + u) ((Lw.shiftChart c u m).dom : Set ℂ) (c.dom : Set ℂ) := by
  intro z hz
  have h1 : (fun z : ℂ => z + u) '' ((Lw.shiftChart c u m).2.1 '' H) ⊆ c.2.1 '' H := by
    rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨w + m, (Lw.add_real_mem_H_iff m).2 hw, by simp [Lw.shiftChart_inv]⟩
  have h2 : (Homeomorph.addRight (u : ℂ)) '' interior ((Lw.shiftChart c u m).2.1 '' H) =
      interior ((Homeomorph.addRight (u : ℂ)) '' ((Lw.shiftChart c u m).2.1 '' H)) :=
    (Homeomorph.addRight (u : ℂ)).image_interior _
  have h3 : z + u ∈ interior ((Homeomorph.addRight (u : ℂ)) '' ((Lw.shiftChart c u m).2.1 '' H)) := by
    rw [← h2]; exact ⟨z, hz, rfl⟩
  exact interior_mono h1 h3

/-- **The real-vanishing lift survives the shift.** -/
theorem liftRealOn_shiftChart {c : Chart} (hL : FinRel.LiftRealOn c) (u m : ℝ) :
    FinRel.LiftRealOn (Lw.shiftChart c u m) := by
  intro y ⟨ε, hε, hball⟩
  have hball' : Metric.ball ((y + u : ℝ) : ℂ) ε ∩ H ⊆ c.dom := by
    intro z ⟨hz, hzH⟩
    have h1 : z - u ∈ Metric.ball (y : ℂ) ε ∩ H := by
      refine ⟨?_, ?_⟩
      · rw [Metric.mem_ball] at hz ⊢
        have : z - u - y = z - ((y + u : ℝ) : ℂ) := by push_cast; ring
        rwa [dist_eq_norm, this, ← dist_eq_norm]
      · have := (Lw.add_real_mem_H_iff (w := z - u) u).1 (by simpa using hzH)
        exact this
    have h2 := mapsTo_dom_shiftChart c u m (hball h1)
    simpa using h2
  have hlim := hL (y + u) ⟨ε, hε, hball'⟩
  have hmap : Tendsto (fun z : ℂ => z + u) (𝓝[((Lw.shiftChart c u m).dom : Set ℂ)] (y : ℂ))
      (𝓝[(c.dom : Set ℂ)] ((y + u : ℝ) : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun z : ℂ => z + u) (𝓝 (y : ℂ)) (𝓝 ((y + u : ℝ) : ℂ)) := by
        have hc : Continuous fun z : ℂ => z + (u : ℂ) := continuous_id.add continuous_const
        have h := hc.tendsto (y : ℂ)
        rwa [show ((y : ℂ) + (u : ℂ)) = ((y + u : ℝ) : ℂ) by push_cast; ring] at h
      exact this.mono_left nhdsWithin_le_nhds
    · exact eventually_nhdsWithin_of_forall fun z hz => mapsTo_dom_shiftChart c u m hz
  exact hlim.comp hmap

/-! ### The chart clause at a launch -/

/-- **The chart clause at a launch** (deterministic): at a sample where instruction `k` of the lower walk launches
and the launched pieces are regular, the launch chart shifted by `u` and its entry `m` is a left entry chart of
`A − u` at `L − u` (`A` the retained lower prefix, `L = min(A ∩ ℝ)`), with a boundary map and real-vanishing lift. -/
theorem chartClause_of_launch {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type*}
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u : ℝ} {ω : Ω}
    (hreg : ∀ j c θ', (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) (j + 1)).2.2.2.1 j = some (c, θ') →
      GW1P.PieceRegular (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω).1
        (min (instrTime (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j)
          (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω).2))
    (hF : ω ∈ launchSet κ b jumps E k) :
    IsLeftEntryChart ((fun z => z - (u : ℂ)) '' lowerPrefix κ b jumps E k u ω)
        (realMin (lowerPrefix κ b jumps E k u ω) - u)
        (Lw.shiftChart (Lv.launchChart κ b jumps E k ω) u (launchEntry κ b jumps E k u ω)) ∧
      ∃ g : ℂ → ℂ, ContinuousOn g {z | 0 ≤ z.im} ∧
        EqOn g (Lw.shiftChart (Lv.launchChart κ b jumps E k ω) u (launchEntry κ b jumps E k u ω)).2.1 H ∧
        FinRel.LiftRealOn (Lw.shiftChart (Lv.launchChart κ b jumps E k ω) u (launchEntry κ b jumps E k u ω)) := by
  have hent := Lx.isLeftEntryValue_launchChart (u := u) hreg hF
  have hAc := Lx.isCompact_lowerPrefix (u := u) hreg hF
  obtain ⟨⟨c, θ⟩, hl⟩ := Option.ne_none_iff_exists'.1 hF
  have hlc := Lv.launchChart_eq hl
  have hcrun := (eq_launch_of_launches _ _ hl).2.2
  have hnot := Lx.stStatus_ne_done_of_launches _ _ hl
  unfold launchEntry
  rw [hlc] at hent ⊢
  refine ⟨?_, ?_⟩
  · rw [hcrun] at hent ⊢
    exact Lx.isLeftEntryChart_shift_of_runChart_entry _ _ hreg k hnot hAc (Lw.fillH_union_real _ _)
      (fun y hy => FinRel.realMin_le_of_mem hAc hy) hent u
  · have hcc : c.IsConformal := by
      rw [hcrun]; exact (GW2aCont.isConformal_runChart _ _ k fun j _ => hreg j).1
    have hP : GW1P.HasProperBdryExt c := GW2Later.hasProperBdryExt_of_launch hreg hl
    have hL : FinRel.LiftRealOn c := by
      rw [hcrun]; exact FinRel.liftRealOn_runChart _ _ hreg k
    obtain ⟨g, hgc, hgi, -, -⟩ := Lw.exists_bdryMap_of_hasProperBdryExt hcc hP
    obtain ⟨hg'c, hg'i⟩ := Lw.bdryMap_shift u (Lx.leftEntry c (realMin (lowerPrefix κ b jumps E k u ω))) hgc hgi
    exact ⟨_, hg'c, hg'i, liftRealOn_shiftChart hL u _⟩

/-! ### The arc conditions from open time intervals -/

/-- **Empty interior from open time intervals**: if every open interval of times `(s₁, s₂)` after `t_L` with
`s₂ ≤ t_L + S` contains a time where `P` fails, then the times `r ∈ (0, S)` with `P (t_L + r)` have empty interior. -/
theorem interior_eq_empty_of_forall_Ioo {P : ℝ≥0 → Prop} {tL : ℝ≥0} {S : ℝ}
    (h : ∀ s₁ s₂ : ℝ≥0, tL ≤ s₁ → s₁ < s₂ → (s₂ : ℝ) ≤ tL + S → ∃ s ∈ Ioo s₁ s₂, ¬ P s) :
    interior {r ∈ Ioo (0 : ℝ) S | P (tL + r.toNNReal)} = ∅ := by
  by_contra hne
  obtain ⟨r₁, r₂, hr12, hsub⟩ := isOpen_interior.exists_Ioo_subset (nonempty_iff_ne_empty.2 hne)
  have hsub' := hsub.trans interior_subset
  have h0 : 0 ≤ r₁ := by
    by_contra hneg
    rw [not_le] at hneg
    have hm : r₁ < min r₂ 0 := lt_min hr12 hneg
    have hx : (r₁ + min r₂ 0) / 2 ∈ Ioo r₁ r₂ := ⟨by linarith, by linarith [min_le_left r₂ 0]⟩
    have := (hsub' hx).1.1
    linarith [min_le_right r₂ 0]
  have hS : r₂ ≤ S := by
    by_contra hgt
    rw [not_le] at hgt
    have hm : max r₁ S < r₂ := max_lt hr12 hgt
    have hx : (max r₁ S + r₂) / 2 ∈ Ioo r₁ r₂ := ⟨by linarith [le_max_left r₁ S], by linarith⟩
    have := (hsub' hx).1.2
    linarith [le_max_right r₁ S]
  have hr2 : 0 < r₂ := h0.trans_lt hr12
  obtain ⟨s, ⟨hs1, hs2⟩, hPs⟩ := h (tL + r₁.toNNReal) (tL + r₂.toNNReal) le_self_add
    (add_lt_add_right ((Real.toNNReal_lt_toNNReal_iff hr2).2 hr12) tL)
    (by rw [NNReal.coe_add, Real.coe_toNNReal _ hr2.le]; linarith)
  have hs1' : (tL : ℝ) + r₁ < s := by
    have := NNReal.coe_lt_coe.2 hs1
    rwa [NNReal.coe_add, Real.coe_toNNReal _ h0] at this
  have hs2' : (s : ℝ) < tL + r₂ := by
    have := NNReal.coe_lt_coe.2 hs2
    rwa [NNReal.coe_add, Real.coe_toNNReal _ hr2.le] at this
  have hr : (s : ℝ) - tL ∈ Ioo r₁ r₂ := ⟨by linarith, by linarith⟩
  have hP := (hsub' hr).2
  have he : tL + ((s : ℝ) - tL).toNNReal = s := by
    ext
    rw [NNReal.coe_add, Real.coe_toNNReal _ (by linarith)]
    ring
  rw [he] at hP
  exact hPs hP

/-- **No real arc from the density of the times in `ℍ`.** -/
theorem interior_im_eq_zero_of_dense {η : ℝ≥0 → ℂ} {tL : ℝ≥0} {S : ℝ}
    (hd : ∀ a c : ℝ≥0, a < c → (c : ℝ) ≤ tL + S → ∃ s ∈ Ioo a c, η s ∈ H) :
    interior {r ∈ Ioo (0 : ℝ) S | (η (tL + r.toNNReal)).im = 0} = ∅ :=
  interior_eq_empty_of_forall_Ioo (P := fun s => (η s).im = 0) fun s₁ s₂ _ h12 h2 => by
    obtain ⟨s, hs, hsH⟩ := hd s₁ s₂ h12 h2
    refine ⟨s, hs, fun h0 => ?_⟩
    have h1 : 0 < (η s).im := hsH
    rw [h0] at h1
    exact lt_irrefl _ h1

/-- **No common arc with a closed set from Lemma S3's form.** -/
theorem interior_mem_eq_empty_of_noArc {η : ℝ≥0 → ℂ} {A : Set ℂ} (hA : IsClosed A) {tL : ℝ≥0} {S : ℝ}
    (hno : ∀ s₁ s₂ : ℝ≥0, tL ≤ s₁ → s₁ < s₂ → (s₂ : ℝ) ≤ tL + S → ¬ η '' Ioo s₁ s₂ ⊆ A) :
    interior {r ∈ Ioo (0 : ℝ) S | η (tL + r.toNNReal) ∈ closure A} = ∅ := by
  rw [hA.closure_eq]
  refine interior_eq_empty_of_forall_Ioo (P := fun s => η s ∈ A) fun s₁ s₂ h1 h12 h2 => ?_
  by_contra hall
  refine hno s₁ s₂ h1 h12 h2 ?_
  rintro _ ⟨s, hs, rfl⟩
  by_contra hsA
  exact hall ⟨s, hs, hsA⟩

/-! ### Lemma S3 in SB2(1)'s configuration (named input) -/

/-- **Named input: Lemma S3 in SB2(1)'s configuration** (no open erased interval; supplement p. 579, used on p. 632):
almost surely at a launch of the lower walk, after its entrance at `L = min(A ∩ ℝ)`, the upper flow shares no open arc
with the retained lower prefix `A` (the form of `S3Statement`'s conclusion, with SB2(1)'s `A` and flow). -/
def SB2EntranceNoCommonArcStatement : Prop :=
  ∀ (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens)
    (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) (u ψ : ℝ) (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞),
    SB2LaunchProblem κ b jumps P h E k u ψ η ζ →
    ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) →
      ∀ s₁ s₂ : ℝ≥0, firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω)) ≤ s₁ → s₁ < s₂ →
        (s₂ : ℝ≥0∞) ≤ ζ ω → ¬ η ω '' Ioo s₁ s₂ ⊆ lowerPrefix κ b jumps E (k + 1) u ω

/-! ### The record almost surely -/

/-- **SB2(1)'s chain record almost surely, geometric and chart clauses** (Theorem 1.3 and Lemma S3 as hypotheses):
almost surely at a launch, for every horizon `T ≤ ζ` after the entrance `T_L` and every `0 < S₁` with
`T_L + S₁ < T`, in the coordinates shifted by `u`: the prefix path, the shifted launch chart as a left entry chart
with boundary map (finite fibres) and real-vanishing lift, the S1 witness with `t_L = T_L` and the S2 lift, the
agreement before `t_L + S₁`, one relative chain for every `S₀ < S₁`, and no real arc on `(0, S₁)`. -/
theorem ae_lineGeom (h13 : Exist.Theorem13Statement.{u}) (hS3 : SB2EntranceNoCommonArcStatement.{u})
    {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u ψ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ) :
    ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) → ∀ T : ℝ≥0, (T : ℝ≥0∞) ≤ ζ ω →
      firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω)) < T →
      ∀ S₁ : ℝ, 0 < S₁ →
        (firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω))).toReal + S₁ < T →
      ∃ (p : ℝ → ℂ) (g : ℂ → ℂ) (β' γ : ℝ≥0 → ℂ) (tL : ℝ≥0) (Wr : ℝ → ℝ) (ηr : ℝ → ℂ),
        (ContinuousOn p (Icc 0 1) ∧ p 0 = 0 ∧ (∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (p s).im) ∧
          (∀ z, (p ⁻¹' {z} ∩ Icc 0 1).Finite) ∧
          p '' Icc 0 1 = (fun z => z - (u : ℂ)) '' lowerPrefix κ b jumps E (k + 1) u ω) ∧
        (IsLeftEntryChart (p '' Icc 0 1) (realMin (p '' Icc 0 1))
            (Lw.shiftChart (Lv.launchChart κ b jumps E (k + 1) ω) u (launchEntry κ b jumps E (k + 1) u ω)) ∧
          ContinuousOn g {z | 0 ≤ z.im} ∧
          EqOn g (Lw.shiftChart (Lv.launchChart κ b jumps E (k + 1) ω) u
            (launchEntry κ b jumps E (k + 1) u ω)).2.1 H ∧
          (∀ z, (g ⁻¹' {z} ∩ {v | 0 ≤ v.im}).Finite) ∧
          FinRel.LiftRealOn (Lw.shiftChart (Lv.launchChart κ b jumps E (k + 1) ω) u
            (launchEntry κ b jumps E (k + 1) u ω))) ∧
        (Supp9B.IsProperCurve β' ∧ β' 0 = 0 ∧ p '' Icc 0 1 ⊆ Supp9B.closedRightSide β' ∧
          β' tL = realMin (p '' Icc 0 1) ∧
          ((tL : ℝ≥0) : ℝ≥0∞) = firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω)) ∧
          Supp9B.IsProperCurve γ ∧ γ 0 = 0 ∧ ∀ s, g (γ s) = β' (tL + s)) ∧
        (∀ t : ℝ≥0, (t : ℝ) < (tL : ℝ) + S₁ → β' t = η ω t - u) ∧
        ((∀ S₀ : ℝ, 0 ≤ S₀ → S₀ < S₁ → FinRel.IsSB2RelChain (p '' Icc 0 1)
            (Lw.shiftChart (Lv.launchChart κ b jumps E (k + 1) ω) u (launchEntry κ b jumps E (k + 1) u ω))
            β' γ tL S₀ Wr ηr) ∧
          interior {r ∈ Ioo (0 : ℝ) S₁ | β' (tL + r.toNNReal) ∈ {z : ℂ | z.im = 0}} = ∅) := by
  have hθ : -(Real.pi / 2) ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := ⟨le_rfl, by linarith [Real.pi_pos]⟩
  have hwp := isBoundaryContinuedProgram_boundaryWalkSpec b jumps hθ true
  have hR := HP.pieces_regular _ hwp
  filter_upwards [ae_isPrefixPath_launch HP, hR.ae_pieceRegular, HP.one_sided,
    Lw.ae_flowLine_regular h13 HP.kappa_pos HP.flow, hS3 κ b jumps P h E k u ψ η ζ HP]
    with ω hpath hpr hS1 hfl hno hF T hTζ hvis S₁ hS₁ hS₁T
  obtain ⟨p, hp⟩ := hpath hF
  have hreg : ∀ (j : ℕ) (c : Chart) (θ' : ℝ),
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) (j + 1)).2.2.2.1 j = some (c, θ') →
      GW1P.PieceRegular (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω).1
        (min (instrTime (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j)
          (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω).2) :=
    fun j c θ' hlj => hpr j c θ' hlj
  obtain ⟨hc, g, hgc, hgi, hLR⟩ := chartClause_of_launch (u := u) hreg hF
  set A := lowerPrefix κ b jumps E (k + 1) u ω with hAdef
  obtain ⟨hpc, hp0, hpf, hpH, hpA⟩ := hp
  have hAcpt : IsCompact A := Lx.isCompact_lowerPrefix (u := u) hreg hF
  have huA : ((u : ℝ) : ℂ) ∈ A := hpA ▸ ⟨0, ⟨le_rfl, zero_le_one⟩, hp0⟩
  have hbdd : BddBelow {x : ℝ | (x : ℂ) ∈ A} := by
    obtain ⟨R, hR⟩ := hAcpt.isBounded.subset_closedBall 0
    refine ⟨-R, fun x hx => ?_⟩
    have h1 := hR hx
    rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs] at h1
    linarith [neg_abs_le x]
  have hp'c : ContinuousOn (fun s => p s - u) (Icc 0 1) := hpc.sub continuousOn_const
  have hp'f : ∀ z, ((fun s => p s - u) ⁻¹' {z} ∩ Icc 0 1).Finite := fun z => by
    have e : (fun s => p s - u) ⁻¹' {z} = p ⁻¹' {z + u} := by
      ext s; simp only [mem_preimage, mem_singleton_iff]
      exact ⟨fun h => by rw [← h]; ring, fun h => by rw [h]; ring⟩
    rw [e]; exact hpf (z + u)
  have hp'A : (fun s => p s - u) '' Icc 0 1 = (fun z => z - (u : ℂ)) '' A := by
    rw [← hpA, image_image]
  have hmin : realMin ((fun s => p s - u) '' Icc 0 1) = realMin A - u := by
    rw [hp'A]; exact Lw.realMin_image_sub u ⟨u, huA⟩ hbdd
  have hc' : IsLeftEntryChart ((fun s => p s - u) '' Icc 0 1) (realMin ((fun s => p s - u) '' Icc 0 1))
      (Lw.shiftChart (Lv.launchChart κ b jumps E (k + 1) ω) u (launchEntry κ b jumps E (k + 1) u ω)) := by
    rw [hmin, hp'A]; exact hc
  have hgf := finite_fibre_of_isLeftEntryChart hp'c (by simp [hp0]) hp'f hc' hgc hgi
  -- the arc conditions on `(T_L, T)`
  set TL := firstVisit (η ω) (ζ ω) (realMin A) with hTL
  have hTLtop : TL ≠ ⊤ := ne_top_of_lt hvis
  have hTLc : ((TL.toNNReal : ℝ≥0) : ℝ≥0∞) = TL := ENNReal.coe_toNNReal hTLtop
  have hle : ∀ s₂ : ℝ≥0, (s₂ : ℝ) ≤ (TL.toNNReal : ℝ) + ((T : ℝ) - TL.toReal) → (s₂ : ℝ≥0∞) ≤ ζ ω := by
    intro s₂ hs₂
    have h1 : (s₂ : ℝ) ≤ T := by
      have : ((TL.toNNReal : ℝ≥0) : ℝ) = TL.toReal := rfl
      linarith
    exact (ENNReal.coe_le_coe.2 (NNReal.coe_le_coe.1 h1)).trans hTζ
  have hnA : interior {r ∈ Ioo (0 : ℝ) ((T : ℝ) - TL.toReal) |
      η ω (TL.toNNReal + r.toNNReal) ∈ closure A} = ∅ :=
    interior_mem_eq_empty_of_noArc hAcpt.isClosed fun s₁ s₂ h1 h12 h2 =>
      hno hF s₁ s₂ (hTLc ▸ ENNReal.coe_le_coe.2 h1) h12 (hle s₂ h2)
  have hnR : interior {r ∈ Ioo (0 : ℝ) ((T : ℝ) - TL.toReal) |
      (η ω (TL.toNNReal + r.toNNReal)).im = 0} = ∅ :=
    interior_im_eq_zero_of_dense fun a c hac hc => hfl.2.2.2.1 a c hac (hle c hc)
  obtain ⟨β', γ, tL, Wr, ηr, h1, h2, h3, h4⟩ :=
    exists_geomRecord ⟨hpc, hp0, hpf, hpH, hpA⟩ hc' hgc hgi (hS1 hF T hTζ) hfl.2.1 hvis hnA hnR hS₁ hS₁T
  exact ⟨_, g, β', γ, tL, Wr, ηr, h1, ⟨hc', hgc, hgi, hgf, hLR⟩, h2, h3, h4⟩

end InteractingSLE.Theorem14.SB.Tc
