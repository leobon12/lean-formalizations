/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2LkS2

/-!
# SB2(2): R99's set link follows from R104a's pointwise lift

Packet PROVE-T14-SB2LIFT. The erasure identity `Lk.TailIdent` asks for R99's set link (`B ∩ D_A ⊆ relPhysSet ⊆ B`) and
R104a's pointwise lift. Here the link is derived from the lift, deterministically:

* `tendsto_tip_stopped_within`, **`tipSet_trans_eq`**: a regular piece read through a chart `d` (mapping `ℍ` into `ℍ`,
  good boundary extension) and then through a chart `c` with boundary limits on `ℍ̄` is the boundary image under `c` of
  its tip set in `d`;
* `pieces_run_struct`, **`relPhysSet_eq_chartBoundaryImage`**: the physical set of a regular run read through such a
  chart `c` is the boundary image under `c` of the run's own physical set;
* **`link_of_lift`**: if the upper history `A` (a path image from `0`) is on the closed left of a proper
  parametrization `β₀` of `B`, the recentred launch chart has boundary limits on `ℍ̄`, the relative run is regular, and
  the tail of `β₀` lifts onto the relative walk (`Lf.IsTailLiftOf`), then `B ∩ (ℍ ∖ fill A) ⊆ relPhysSet ⊆ B`: the
  initial portion of `β₀` up to its visit to `R` lies in `K_A` (`s2HullRight`), its tail is the boundary image of the
  relative walk.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdMapInv)

namespace InteractingSLE.Theorem14.SB.Lk

open Supp9B Exist Exist.Staged Exist.StagedLaw GW1P

/-! ### Pieces read through a second chart -/

/-- The radial tip of a regular piece, read in a chart mapping `ℍ` into `ℍ`, converges from inside `ℍ`. -/
theorem tendsto_tip_stopped_within {d : Chart} {W : ℝ≥0 → ℝ} {S : ℝ≥0∞}
    (hW : ContinuousOn W {t | (t : ℝ≥0∞) ≤ S}) (hW0 : W 0 = 0) {t : ℝ≥0} {w : ℂ}
    (hlim : Tendsto (fun y : ℝ => d.2.1 (fwdMapInv (fun r : ℝ => W (min ((r.toNNReal : ℝ≥0) : ℝ≥0∞) S).toNNReal) t
      (y * Complex.I))) (𝓝[>] 0) (𝓝 w))
    (hdH : ∀ z ∈ H, d.2.1 z ∈ H) :
    Tendsto (fun y : ℝ => d.2.1 (fwdMapInv (fun r : ℝ => W (min ((r.toNNReal : ℝ≥0) : ℝ≥0∞) S).toNNReal) t
      (y * Complex.I))) (𝓝[>] 0) (𝓝[H] w) := by
  have h0 : W (min ((0 : ℝ≥0) : ℝ≥0∞) S).toNNReal = 0 := by
    rw [CounterflowRange.stopped_eq_of_lt (W := W) (t := 0) (by simp), hW0]
  have hU : Continuous fun r : ℝ => W (min ((r.toNNReal : ℝ≥0) : ℝ≥0∞) S).toNNReal :=
    (CounterflowRange.continuous_stopped hW).comp continuous_real_toNNReal
  have hU0 : (fun r : ℝ => W (min ((r.toNNReal : ℝ≥0) : ℝ≥0∞) S).toNNReal) 0 = 0 := by simpa using h0
  refine tendsto_nhdsWithin_iff.2 ⟨hlim, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with y hy
  have hyH : (y : ℂ) * Complex.I ∈ H := by
    show 0 < ((y : ℂ) * Complex.I).im
    simpa using hy
  exact hdH _ (QuantumZipper.RS.fwdMapInv_mem_H hU hU0 (NNReal.coe_nonneg t) hyH)

/-- **A regular piece read through two charts** is the boundary image, under the outer chart `c`, of its tip set in
the inner chart `d`. -/
theorem tipSet_trans_eq {c d : Chart} (hc : HasBdryLimits c.2.1) (hd : HasProperBdryExt d)
    (hdH : ∀ z ∈ H, d.2.1 z ∈ H) {W : ℝ≥0 → ℝ} {S : ℝ≥0∞} (h : PieceRegular W S) :
    (c.trans d).tipSet (fun r : ℝ≥0 => W (min (r : ℝ≥0∞) S).toNNReal) S =
      chartBoundaryImage c (d.tipSet (fun r : ℝ≥0 => W (min (r : ℝ≥0∞) S).toNNReal) S) := by
  obtain ⟨f, C, hf, -⟩ := hd
  obtain ⟨hW0, hWc, α, hα, -⟩ := h
  have hWc' : ContinuousOn W {s | (s : ℝ≥0∞) < S} := hWc.mono fun _ (hs : _ < S) => (le_of_lt hs : _ ≤ S)
  have hαH : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ S → α t ∈ Hbar := fun t ht =>
    Sec7.IsGeneratingTrace.mem_Hbar hα hWc' hW0 ht
  ext z
  constructor
  · rintro ⟨t, ht, hz⟩
    have hin := CounterflowRange.tendsto_tip_stopped_of_tendsto hα hWc hW0 ht (hf _ (hαH t ht))
    have hinH := tendsto_tip_stopped_within hWc hW0 hin hdH
    have hwH : f (α t) ∈ Hbar := mem_Hbar_of_tendsto (hαH t ht) hdH (hf _ (hαH t ht))
    obtain ⟨q, hq⟩ := hc _ hwH
    have hzq : z = q := tendsto_nhds_unique hz (hq.comp hinH)
    refine ⟨f (α t), ⟨t, ht, hin⟩, ?_⟩
    rw [hzq]; exact hq
  · rintro ⟨w, ⟨t, ht, hw⟩, hz⟩
    exact ⟨t, ht, hz.comp (tendsto_tip_stopped_within hWc hW0 hw hdH)⟩

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- **The recorded pieces of a regular run**: each is a regular piece (stopped driver) read in a good chart mapping `ℍ`
into `ℍ`. -/
theorem pieces_run_struct (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hreg : ∀ (k : ℕ) (c : Chart) (θ : ℝ), (ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 k = some (c, θ) →
      PieceRegular (D k).1 (min (instrTime spec k) (D k).2)) (n : ℕ) :
    ∀ p ∈ (ExplState.run κ b jumps spec D n).1, ∃ (W : ℝ≥0 → ℝ) (S : ℝ≥0∞),
      p.2.1 = (fun r : ℝ≥0 => W (min (r : ℝ≥0∞) S).toNNReal) ∧ p.2.2 = S ∧ PieceRegular W S ∧
        HasProperBdryExt p.1 ∧ ∀ z ∈ H, p.1.2.1 z ∈ H := by
  induction n with
  | zero =>
    intro p hp
    simp [ExplState.run, ExplState.init] at hp
  | succ n ih =>
    rcases hl : (ExplState.run κ b jumps spec D (n + 1)).2.2.2.1 n with _ | ⟨c, θ⟩
    · rw [pieces_run_succ_of_noLaunch spec D hl]
      exact ih
    · have hr := hreg n c θ hl
      obtain ⟨-, he, -⟩ := eq_launch_of_launches (κ := κ) (b := b) (jumps := jumps) spec D hl
      rw [he, CounterflowRange.pieces_launch]
      intro p hp'
      rcases List.mem_append.1 hp' with hq | hq
      · exact ih p hq
      · rw [List.mem_singleton] at hq
        subst hq
        have hgood := (isClosed_pieces_run (κ := κ) (b := b) (jumps := jumps) spec D hreg n).1
        have hdom := Lw.isDomainChart_runChart (κ := κ) (b := b) (jumps := jumps) spec D hreg n
          (Lx.stStatus_ne_done_of_launches spec D hl)
        refine ⟨(D n).1, min (instrTime spec n) (D n).2, rfl, rfl, hr, hgood, fun z hz => ?_⟩
        have hz' : (ExplState.run κ b jumps spec D n).2.2.2.2.1.2.1 z ∈
            (ExplState.run κ b jumps spec D n).2.2.2.2.1.2.1 '' H := mem_image_of_mem _ hz
        rw [hdom.image_eq] at hz'
        exact hz'.1

/-- The boundary image of a union. -/
theorem mem_chartBoundaryImage_iff {c : Chart} {S : Set ℂ} {z : ℂ} :
    z ∈ chartBoundaryImage c S ↔ ∃ w ∈ S, Tendsto c.2.1 (𝓝[H] w) (𝓝 z) := Iff.rfl

/-- **The physical set of a regular run read through a chart with boundary limits** is the chart's boundary image of
the run's own physical set. -/
theorem relPhysSet_eq_chartBoundaryImage {c : Chart} (hc : HasBdryLimits c.2.1) (spec : ExplSpec)
    (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hreg : ∀ (k : ℕ) (c : Chart) (θ : ℝ), (ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 k = some (c, θ) →
      PieceRegular (D k).1 (min (instrTime spec k) (D k).2)) :
    relPhysSet κ b jumps c spec D = chartBoundaryImage c (ExplState.physSet κ b jumps spec D) := by
  set s := ExplState.run κ b jumps spec D spec.2.2.length with hs
  have hpieces := pieces_run_struct (κ := κ) (b := b) (jumps := jumps) spec D hreg spec.2.2.length
  have htip : ∀ p ∈ s.1, (c.trans p.1).tipSet p.2.1 p.2.2 = chartBoundaryImage c (p.1.tipSet p.2.1 p.2.2) := by
    intro p hp
    obtain ⟨W, S, h1, h2, hr, hgood, hH⟩ := hpieces p hp
    rw [h1, h2]
    exact tipSet_trans_eq hc hgood hH hr
  have hrel : relPhysSet κ b jumps c spec D = chartBoundaryImage c {(spec.1 : ℂ)} ∪
      (⋃ p ∈ s.1, (c.trans p.1).tipSet p.2.1 p.2.2) ∪
        ⋃ a ∈ s.2.1, chartBoundaryImage c (((↑) : ℝ → ℂ) '' a) := rfl
  have hphys : ExplState.physSet κ b jumps spec D =
      {(spec.1 : ℂ)} ∪ (⋃ p ∈ s.1, p.1.tipSet p.2.1 p.2.2) ∪ ⋃ a ∈ s.2.1, ((↑) : ℝ → ℂ) '' a := rfl
  rw [hrel, hphys]
  ext z
  simp only [mem_union, mem_iUnion₂, mem_chartBoundaryImage_iff]
  constructor
  · rintro ((⟨w, hw, hz⟩ | ⟨p, hp, hz⟩) | ⟨a, ha, w, hw, hz⟩)
    · exact ⟨w, Or.inl (Or.inl hw), hz⟩
    · rw [htip p hp] at hz
      obtain ⟨w, hw, hz⟩ := hz
      exact ⟨w, Or.inl (Or.inr ⟨p, hp, hw⟩), hz⟩
    · exact ⟨w, Or.inr ⟨a, ha, hw⟩, hz⟩
  · rintro ⟨w, (hw | ⟨p, hp, hw⟩) | ⟨a, ha, hw⟩, hz⟩
    · exact Or.inl (Or.inl ⟨w, hw, hz⟩)
    · refine Or.inl (Or.inr ⟨p, hp, ?_⟩)
      rw [htip p hp]
      exact ⟨w, hw, hz⟩
    · exact Or.inr ⟨a, ha, w, hw, hz⟩

/-! ### The set link from the lift -/

/-- Recentring a chart transports its boundary limits by the real translation. -/
theorem tendsto_recenter_iff {c : Chart} {a : ℝ} {w z : ℂ} :
    Tendsto (c.recenter a).2.1 (𝓝[H] w) (𝓝 z) ↔ Tendsto c.2.1 (𝓝[H] (w + a)) (𝓝 z) := by
  have hmap : Filter.map (fun v : ℂ => v + a) (𝓝[H] w) = 𝓝[H] (w + a) := by
    have he := (Homeomorph.addRight (a : ℂ)).isEmbedding.map_nhdsWithin_eq H w
    simp only [Homeomorph.coe_addRight] at he
    rw [he]
    congr 1
    ext v
    constructor
    · rintro ⟨v', hv', rfl⟩
      exact (Lw.add_real_mem_H_iff a).2 hv'
    · intro hv
      refine ⟨v - a, (Lw.add_real_mem_H_iff a).1 ?_, ?_⟩
      · show v - a + a ∈ H
        rw [sub_add_cancel]; exact hv
      · show v - a + a = v
        rw [sub_add_cancel]
  show Tendsto (fun v => c.2.1 (v + a)) (𝓝[H] w) (𝓝 z) ↔ _
  rw [← hmap]
  exact tendsto_map'_iff.symm

/-- Recentring keeps boundary limits on `ℍ̄`. -/
theorem HasBdryLimits.recenter {c : Chart} (hc : HasBdryLimits c.2.1) (a : ℝ) :
    HasBdryLimits (c.recenter a).2.1 := fun w hw => by
  have hw' : w + a ∈ Hbar := by
    show 0 ≤ (w + a).im
    have hw0 : 0 ≤ w.im := hw
    simpa using hw0
  obtain ⟨q, hq⟩ := hc _ hw'
  exact ⟨q, tendsto_recenter_iff.2 hq⟩

/-- **R99's set link from R104a's lift** (deterministic): if the upper history `A = p([0, 1])` (a path from `0` in
`ℍ̄`) is on the closed left of a proper curve `β₀` from `0`, the recentred chart `c − (−m)` has boundary limits on
`ℍ̄`, the relative run is regular, and the tail of `β₀` after `R = max (A ∩ ℝ)` lifts onto the relative walk, then
the range of `β₀` outside the filled history is in the relative physical set, which is in the range of `β₀`. -/
theorem link_of_lift {pA : ℝ → ℂ} (hp : ContinuousOn pA (Icc 0 1)) (hp0 : pA 0 = 0)
    (hpH : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (pA s).im) {β₀ : ℝ≥0 → ℂ} (hβ : IsProperCurve β₀) (hβ0 : β₀ 0 = 0)
    (hA : pA '' Icc 0 1 ⊆ closedLeftSide β₀) {c : Chart} {m : ℝ} (hc : HasBdryLimits (c.recenter (-m)).2.1)
    (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hreg : ∀ (k : ℕ) (c' : Chart) (θ : ℝ), (ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 k = some (c', θ) →
      PieceRegular (D k).1 (min (instrTime spec k) (D k).2))
    (hlift : Lf.IsTailLiftOf c (realMax (pA '' Icc 0 1)) m β₀ (ExplState.physSet κ b jumps spec D)) :
    range β₀ ∩ (H \ fillH (pA '' Icc 0 1)) ⊆ relPhysSet κ b jumps (c.recenter (-m)) spec D ∧
      relPhysSet κ b jumps (c.recenter (-m)) spec D ⊆ range β₀ := by
  obtain ⟨tL, γ, htL, hγ, -, hγW, hγl⟩ := hlift
  have hrel := relPhysSet_eq_chartBoundaryImage hc spec D hreg
  obtain ⟨-, tR, htR, -, hhull, -, -⟩ := s2HullRight hp hp0 hpH hβ hβ0 hA
  have htt : tR = tL := hβ.2.1 (htR.trans htL.symm)
  have hγlim : ∀ s : ℝ≥0, Tendsto (c.recenter (-m)).2.1 (𝓝[H] (γ s)) (𝓝 (β₀ (tL + s))) := fun s => by
    rw [tendsto_recenter_iff]
    have h1 := hγl s
    have h2 : γ s + ((-m : ℝ) : ℂ) = γ s - m := by
      rw [Complex.ofReal_neg, sub_eq_add_neg]
    rw [h2]; exact h1
  refine ⟨?_, ?_⟩
  · rintro z ⟨⟨t, rfl⟩, hzH, hzA⟩
    rw [hrel]
    rcases le_or_gt t tL with htle | htgt
    · exfalso
      have hK : β₀ t ∈ hullK (pA '' Icc 0 1) := hhull ⟨t, ⟨zero_le, htt ▸ htle⟩, rfl⟩
      rcases hK with hf | ⟨x, -, hx⟩
      · exact hzA hf
      · have h0 : (β₀ t).im = 0 := by rw [← hx, Complex.ofReal_im]
        have h1 : 0 < (β₀ t).im := hzH
        linarith
    · obtain ⟨s, rfl⟩ : ∃ s : ℝ≥0, t = tL + s := ⟨t - tL, (add_tsub_cancel_of_le htgt.le).symm⟩
      exact ⟨γ s, hγW ▸ mem_range_self s, hγlim s⟩
  · intro z hz
    rw [hrel] at hz
    obtain ⟨w, hw, hzw⟩ := hz
    rw [← hγW] at hw
    obtain ⟨s, rfl⟩ := hw
    have := neBot_nhdsWithin_H (hγ.2.2.1 s)
    exact ⟨tL + s, (tendsto_nhds_unique hzw (hγlim s)).symm⟩

/-! ### The erasure identity from the lift alone -/

section LiftIdent

open MeasureTheory ProbabilityTheory Lx Lu Leaf FlowDilate Sec4
open LQGMetric (DistOn)

universe u

/-- **The lift half of SB2(2)'s erasure identity at one launch** (`TailIdent` without R99's set link): for `m = −e_R`
and every regular staged lower walk `EL` of the conditional field, almost surely under the retained kernel, the tail
after `R` of every proper parametrization of the actual lower walk lifts onto `EL`'s walk. -/
def TailLift (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (u : ℝ)
    (l : List (ℝ × ℝ≥0)) (k : ℕ) (ω₀ : Ω) (c : Chart) (b' : ℝ → ℝ) (J' : Finset ℝ)
    (h' : Ω → DistOn upperHalfPlaneOpens) : Prop :=
  ∀ m : ℝ, m = -upperEntry κ b jumps E u l k ω₀ → ∀ EL : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
    IsStagedHistory κ (affData 1 m b') (affJumps 1 m J')
      (condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀)
      (fun ω => affField m one_pos (h' ω)) (relLowerSpec b' J' m) EL →
    StagedPiecesRegular κ (affData 1 m b') (affJumps 1 m J')
      (condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀)
      (relLowerSpec b' J' m) EL →
    ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
      ∀ β₀ : ℝ≥0 → ℂ, IsProperCurve β₀ → β₀ 0 = 0 → range β₀ = lowerWalkSet κ b jumps E ω →
        Lf.IsTailLiftOf c (realMax (upperPrefix κ b jumps E u l k ω₀)) m β₀
          (relWalkSet κ (affData 1 m b') (affJumps 1 m J') EL ω)

/-- **Named input: the lift half of SB2(2)'s erasure identity at the later launches** (R104's pointwise clause, for
every regular staged lower walk of the conditional field). -/
def SB2LowerTailLiftIdentStatement : Prop :=
  Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ c b' J' h' =>
    0 < k → TailLift κ b jumps P E u l k ω₀ c b' J' h'

/-- **The erasure identity from its lift half**: R99's set link is a consequence of the lift (`link_of_lift`), with the
upper history at the launch as a path from `0` (`Lf.exists_path_upperPrefix`) on the closed left of the walk (the
setting's avoidance, transported to the retained kernel where the upper run is frozen), the walk a proper curve
(`RightWalkProperRegStatement`), the launch chart's boundary limits (`GW1WalkFinish.hasBdryLimits_chart_run`) and the
relative run regular. -/
theorem sb2LowerTailIdentStatement_of_liftIdent (hPR : WalkCont.RightWalkProperRegStatement.{u})
    (hli : SB2LowerTailLiftIdentStatement.{u}) : SB2LowerTailIdentStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft
  have hsp : IsBoundaryContinuedProgram (upperSpec u l).2.2 := isBoundaryContinuedProgram_upperSpec hlθ
  have hEu := hE _ hsp
  have hRu := hER _ hsp
  have hm𝒢 := hEu.2.1 k
  have hβQ := KernelTower.ae_ae_condExpKernel_of_ae hm𝒢 (hPR κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER)
  have hleftQ := KernelTower.ae_ae_condExpKernel_of_ae hm𝒢 hleft
  have hrunQ := Retain.ae_ae_run_eq (upperSpec u l) hRu hm𝒢 le_rfl
  filter_upwards [hli κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft, hβQ, hleftQ,
    hrunQ, hRu] with ω₀ hli₀ hβ₀ hleft₀ hrun₀ hR₀
  intro c θ hlaunch b' J' h' hb' hT' hG' hk m hm EL hst hreg
  have hreg₀ : ∀ (j : ℕ) (c' : Chart) (θ' : ℝ),
      (ExplState.run κ b jumps (upperSpec u l) (fun i => E (upperSpec u l) i ω₀) (j + 1)).2.2.2.1 j =
        some (c', θ') →
      PieceRegular (E (upperSpec u l) j ω₀).1 (min (instrTime (upperSpec u l) j) (E (upperSpec u l) j ω₀).2) :=
    fun j c' θ' hl' => hR₀ j θ' _ c' (eq_launch_of_launches _ _ hl').1 hl'
  obtain ⟨pA, hp, hp0, hpH, hpA, hcl⟩ :=
    Lf.exists_path_upperPrefix (κ := κ) (b := b) (jumps := jumps) hu l (fun j => E (upperSpec u l) j ω₀) hreg₀ k
  have hpA' : pA '' Icc 0 1 = upperPrefix κ b jumps E u l k ω₀ := hpA
  have hc := (eq_launch_of_launches (upperSpec u l) (fun j => E (upperSpec u l) j ω₀) hlaunch).2.2
  have hB : HasBdryLimits c.2.1 := by
    rw [hc]; exact GW1WalkFinish.hasBdryLimits_chart_run _ _ hreg₀ k
  have hB' := HasBdryLimits.recenter hB (-m)
  filter_upwards [hli₀ c θ hlaunch b' J' h' hb' hT' hG' hk m hm EL hst hreg, hβ₀, hleft₀, hrun₀, hreg]
    with ω hlω hβω hleftω hrunω hregω
  -- the upper run is frozen at `ω`: the launch and the history are those of `ω₀`
  have hlaunchω : ω ∈ upperLaunchSet κ b jumps E u l k := by
    show (ExplState.run κ b jumps (upperSpec u l) (fun j => E (upperSpec u l) j ω) (k + 1)).2.2.2.1 k ≠ none
    rw [launches_run_succ_of_run_eq (upperSpec u l) hrunω, hlaunch]
    exact Option.some_ne_none _
  have hAω : upperPrefix κ b jumps E u l k ω = upperPrefix κ b jumps E u l k ω₀ := by
    show prefixPhysSet κ b jumps (upperSpec u l) (fun j => E (upperSpec u l) j ω) k ∪ ((↑) : ℝ → ℂ) '' Icc u 0 =
      prefixPhysSet κ b jumps (upperSpec u l) (fun j => E (upperSpec u l) j ω₀) k ∪ ((↑) : ℝ → ℂ) '' Icc u 0
    unfold prefixPhysSet; rw [hrunω]
  have hav := hleftω hlaunchω
  rw [hAω] at hav
  obtain ⟨β₀, hβ, hβ0, hβr⟩ := hβω
  have hav' : prefixPhysSet κ b jumps (upperSpec u l) (fun j => E (upperSpec u l) j ω₀) k ∩
      rightSideOf (range β₀) = ∅ := by
    rw [hβr]
    exact eq_empty_of_subset_empty ((inter_subset_inter_left _ subset_union_left).trans hav.subset)
  have hAL : upperPrefix κ b jumps E u l k ω₀ ⊆ closedLeftSide β₀ :=
    Lf.subset_closedLeftSide_of_avoid hβ hβ0 hcl hav'
  have hrr : ∀ (j : ℕ) (c' : Chart) (θ' : ℝ),
      (ExplState.run κ (affData 1 m b') (affJumps 1 m J') (relLowerSpec b' J' m) (fun i => EL i ω) (j + 1)).2.2.2.1 j
        = some (c', θ') →
      PieceRegular (EL j ω).1 (min (instrTime (relLowerSpec b' J' m) j) (EL j ω).2) :=
    fun j c' θ' hl' => hregω j θ' _ c' (eq_launch_of_launches _ _ hl').1 hl'
  have hlift := hlω β₀ hβ hβ0 hβr
  rw [← hpA'] at hlift hAL
  have hlink := link_of_lift hp hp0 hpH hβ hβ0 hAL hB' (relLowerSpec b' J' m) (fun j => EL j ω) hrr hlift
  refine ⟨?_, hlω⟩
  have hβr' : range β₀ = lowerWalkSet κ b jumps E ω := hβr
  rw [hAω, ← hpA', ← hβr']
  exact hlink

/-- **SB2(2)'s combined target (R104a) from the lift half of the erasure identity** (and Theorems 1.2–1.3). -/
theorem sb2LowerLaunchLiftStatement_of_liftIdent (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (h12₀ : Exist.Theorem12Statement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (hli : SB2LowerTailLiftIdentStatement.{u}) :
    Lh.SB2LowerLaunchLiftStatement.{u} :=
  sb2LowerLaunchLiftStatement_of_tailIdent h12 h13 h12₀ h13₀
    (sb2LowerTailIdentStatement_of_liftIdent (Wire.walkProperRegStatements_of_thm12_thm13 h12 h13 h12₀ h13₀).1 hli)

end LiftIdent

end InteractingSLE.Theorem14.SB.Lk
