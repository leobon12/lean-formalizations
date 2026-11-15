/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2LwCongr
import InteractingSLE.Spec.Supplement.SB2JZero
import InteractingSLE.Spec.Supplement.SB2HFlow
import InteractingSLE.Spec.Supplement.SBLyRight
import InteractingSLE.Spec.Supplement.W5CommonSeedShift
import InteractingSLE.Spec.Supplement.BR4aPathField

/-!
# SB2(2)'s law half at the first launch (k = 0) PROVED

Packet PROVE-T14-SB2LOW (ruling R99). At the first launch of the upper schedule the upper history `A` is only the real
bridge `[u, 0]`: the launch chart is the translation `z ↦ z − u`, `R = max (A ∩ ℝ) = 0`, the right entry is `e_R = −u`
so `m = u`, the retained past is trivial (the conditional law is `P`), the witness field is `h(· + u)` and its data are
`b(· + u)` off a finite set. Read back in the frame `affField m`, the field is `h` itself and the data agree with `b`
off a finite set, so they have the same one-sided limits and genuine jumps (`SB2LwCongr`): the relative lower walk is
GW1's lower walk of `h`, and the regularized family of the lower walk is the relative staged history. Its regularity is
Theorem 1.3 (`stagedPiecesRegular_of_regular`), its right additions are `Ly.ae_walkRightAdds_of_bound` (Theorem 1.3 and
GW1's ambient bound), and the link holds with equality, since the recentred chart `(z ↦ z − u) + u` is the identity.

* **`sb2LowerLaw_zero`**: the law half's conclusion at `k = 0`;
* `SB2LowerLawSuccStatement`: the law half at the later launches `k + 1` (named input);
* **`sb2LowerLawStatement_of_succ`**: the law half from its later launches;
* **`sb2LowerLaunchEntryAdmStatement_of_succ`**: R99's target from Theorem 1.3 and the law half at later launches.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lh

open Exist Exist.StagedLaw Exist.Staged Restart FlowDilate
open PiecewiseConstantBoundaryData (leftLim rightLim jumpSet)

/-! ### Charts whose inverse is the identity -/

section IdChart

variable {c : Chart} (hc : ∀ z, c.2.1 z = z)
include hc

theorem chartBoundaryImage_ofReal_of_id (a : Set ℝ) : chartBoundaryImage c (((↑) : ℝ → ℂ) '' a) =
    ((↑) : ℝ → ℂ) '' a := by
  have hid : c.2.1 = id := funext hc
  ext z
  constructor
  · rintro ⟨w, ⟨x, hx, rfl⟩, hw⟩
    have := GW1P.neBot_nhdsWithin_H (Lw.ofReal_mem_Hbar x)
    rw [hid] at hw
    have h2 : Tendsto id (𝓝[H] (x : ℂ)) (𝓝 (x : ℂ)) := tendsto_id.mono_left nhdsWithin_le_nhds
    rw [tendsto_nhds_unique hw h2]
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    refine ⟨(x : ℂ), ⟨x, hx, rfl⟩, ?_⟩
    rw [hid]
    exact tendsto_id.mono_left nhdsWithin_le_nhds

theorem chartBoundaryImage_singleton_of_id (x : ℝ) : chartBoundaryImage c {(x : ℂ)} = {(x : ℂ)} := by
  have h := chartBoundaryImage_ofReal_of_id hc {x}
  rwa [Set.image_singleton] at h

theorem tipSet_trans_of_id (p : Chart) (W : ℝ≥0 → ℝ) (s : ℝ≥0∞) : (c.trans p).tipSet W s = p.tipSet W s := by
  unfold Chart.tipSet Chart.trans
  simp only [hc]

/-- **Through a chart whose inverse is the identity, the relative physical set is the physical set.** -/
theorem relPhysSet_of_id (κ : ℝ) (b : ℝ → ℝ) (J : Finset ℝ) (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) :
    relPhysSet κ b J c spec D = ExplState.physSet κ b J spec D := by
  rw [← prefixPhysSet_length]
  unfold relPhysSet SB.prefixPhysSet
  simp only [chartBoundaryImage_singleton_of_id hc, tipSet_trans_of_id hc, chartBoundaryImage_ofReal_of_id hc]

end IdChart

/-! ### The first launch -/

/-- **SB2(2)'s law half at the first launch of the upper schedule** (`k = 0`). -/
theorem sb2LowerLaw_zero (h13 : Exist.Theorem13Statement.{u}) (hGW0 : GW0.GW0ForwardStatement.{u}) {κ : ℝ}
    (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps) {W' : ℝ≥0 → Ω → ℝ}
    {ζ' : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    {x₀ : ℝ} (l : List (ℝ × ℝ≥0)) (hx₀ : x₀ ≤ 0) :
    ∀ᵐ ω₀ ∂P, ∀ (c : Chart) (θ : ℝ),
      (ExplState.run κ b jumps (Lu.upperSpec x₀ l) (fun j => E (Lu.upperSpec x₀ l) j ω₀) (0 + 1)).2.2.2.1 0 =
          some (c, θ) →
      ∀ (b' : ℝ → ℝ) (jumps' : Finset ℝ) (h' : Ω → DistOn upperHalfPlaneOpens),
        IsPiecewiseConstantBoundaryData b' jumps' →
        (∀ ω, IsChartTransport c 1 0 (chiC κ) (h ω) (h' ω)) →
        IsGFFWithBoundaryData (condExpKernel P (pastSigma κ b jumps (Lu.upperSpec x₀ l) (E (Lu.upperSpec x₀ l)) 0) ω₀)
          h' b' jumps' →
        ∀ m : ℝ, m = -Lu.upperEntry κ b jumps E x₀ l 0 ω₀ → ∃ EL : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
          IsStagedHistory κ (affData 1 m b') (affJumps 1 m jumps')
            (condExpKernel P (pastSigma κ b jumps (Lu.upperSpec x₀ l) (E (Lu.upperSpec x₀ l)) 0) ω₀)
            (fun ω => affField m one_pos (h' ω)) (Lu.relLowerSpec b' jumps' m) EL ∧
          StagedPiecesRegular κ (affData 1 m b') (affJumps 1 m jumps')
            (condExpKernel P (pastSigma κ b jumps (Lu.upperSpec x₀ l) (E (Lu.upperSpec x₀ l)) 0) ω₀)
            (Lu.relLowerSpec b' jumps' m) EL ∧
          (∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (Lu.upperSpec x₀ l) (E (Lu.upperSpec x₀ l)) 0) ω₀),
            Lx.WalkRightAdds κ (affData 1 m b') (affJumps 1 m jumps') (fun _ => EL) ω) ∧
          ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (Lu.upperSpec x₀ l) (E (Lu.upperSpec x₀ l)) 0) ω₀),
            lowerWalkSet κ b jumps E ω ∩ (H \ fillH (upperPrefix κ b jumps E x₀ l 0 ω)) ⊆
                relPhysSet κ (affData 1 m b') (affJumps 1 m jumps') (c.recenter (-m))
                  (Lu.relLowerSpec b' jumps' m) (fun j => EL j ω) ∧
              relPhysSet κ (affData 1 m b') (affJumps 1 m jumps') (c.recenter (-m))
                  (Lu.relLowerSpec b' jumps' m) (fun j => EL j ω) ⊆
                lowerWalkSet κ b jumps E ω := by
  have hamb := (GW1Conn.ambient_bounds hGW0 hκ hκ4 hb hh hcf hζ').1
  set lw := boundaryWalkSpec b jumps (-(Real.pi / 2)) true with hlw
  have hlwp : IsBoundaryContinuedProgram lw.2.2 :=
    isBoundaryContinuedProgram_boundaryWalkSpec b jumps ⟨le_rfl, by linarith [Real.pi_pos]⟩ true
  obtain ⟨hE', hreg', hrun⟩ := StagedReg.regFam_spec hb hE hER
  have hR' : StagedPiecesRegular κ b jumps P lw (StagedReg.regFam E lw) :=
    Exist.StagedLaw.stagedPiecesRegular_of_regular h13 hκ hb (hE' lw hlwp) (hreg' lw)
  have hWRA : ∀ᵐ ω ∂P, Lx.WalkRightAdds κ b jumps (StagedReg.regFam E) ω :=
    Ly.ae_walkRightAdds_of_bound h13 hκ hb hh (hE' lw hlwp) (hreg' lw) hamb
  filter_upwards with ω₀
  intro c θ hcθ b' J' h' hb' hT' hG' m hm
  rw [Lv.condExpKernel_pastSigma_zero] at hG'
  simp only [Lv.condExpKernel_pastSigma_zero]
  -- the launch chart is the translation to the upper seed
  obtain ⟨-, -, hc⟩ := eq_launch_of_launches _ _ hcθ
  have hc0 : c = Chart.id.recenter x₀ := hc
  have hLc := Lu.upperLaunchChart_eq hcθ
  subst hc0
  have hconf : (Chart.id.recenter x₀).IsConformal := Chart.isConformal_id.recenter x₀
  -- the entry point: `R = 0`, `e_R = −x₀`, so `m = x₀`
  have hpre : ∀ y : ℝ, (y : ℂ) ∈ upperPrefix κ b jumps E x₀ l 0 ω₀ → y ≤ 0 := by
    intro y hy
    rcases hy with hy | ⟨z, hz, hzy⟩
    · have hr0 : ExplState.run κ b jumps (Lu.upperSpec x₀ l) (fun j => E (Lu.upperSpec x₀ l) j ω₀) 0 =
          ExplState.init x₀ := rfl
      change (y : ℂ) ∈ SB.prefixPhysSet κ b jumps (Lu.upperSpec x₀ l) (fun j => E (Lu.upperSpec x₀ l) j ω₀) 0 at hy
      simp only [SB.prefixPhysSet, hr0, ExplState.init, List.not_mem_nil, iUnion_of_empty, iUnion_empty,
        union_empty, mem_singleton_iff] at hy
      have : y = x₀ := by exact_mod_cast hy
      rw [this]
      exact hx₀
    · have : z = y := by exact_mod_cast hzy
      rw [← this]
      exact hz.2
  have h0 : ((0 : ℝ) : ℂ) ∈ upperPrefix κ b jumps E x₀ l 0 ω₀ := Or.inr ⟨0, ⟨hx₀, le_rfl⟩, rfl⟩
  have hR0 : realMax (upperPrefix κ b jumps E x₀ l 0 ω₀) = 0 :=
    le_antisymm (csSup_le ⟨0, h0⟩ hpre) (le_csSup ⟨0, hpre⟩ h0)
  have hbv : Lx.bdryValue (Chart.id.recenter x₀) = fun x => x - x₀ := by
    funext x
    have ht : Tendsto (Chart.id.recenter x₀).1 (𝓝[H] (x : ℂ)) (𝓝 ((x : ℂ) - x₀)) := by
      change Tendsto (fun z : ℂ => z - x₀) (𝓝[H] (x : ℂ)) (𝓝 ((x : ℂ) - x₀))
      exact ((continuous_id.sub continuous_const).tendsto _).mono_left nhdsWithin_le_nhds
    have := (Lx.tendsto_bdryValue ht (by simp)).1
    rw [this]
    simp
  have he : Lu.upperEntry κ b jumps E x₀ l 0 ω₀ = -x₀ := by
    unfold Lu.upperEntry Lx.rightEntry
    rw [hLc, hR0, hbv]
    have : Tendsto (fun x : ℝ => x - x₀) (𝓝[>] 0) (𝓝 (0 - x₀)) :=
      ((continuous_id.sub continuous_const).tendsto _).mono_left nhdsWithin_le_nhds
    rw [this.limUnder_eq, zero_sub]
  have hmx : m = x₀ := by rw [hm, he, neg_neg]
  subst hmx
  -- the field: `h(· + x₀)`, read back in the frame `affField x₀`
  have hh' : ∀ ω, h' ω = BR4aPath.recField m (h ω) := fun ω =>
    (hT' ω).unique hconf (BR4aPath.isChartTransport_recField (chiC κ) m (h ω))
  have hfield : (fun ω => affField m one_pos (h' ω)) = h := by
    funext ω
    rw [hh' ω]
    exact Lv.affField_one_flowField m (h ω)
  -- the data: `b(· + x₀)` off a finite set
  have hbs : IsPiecewiseConstantBoundaryData (fun y => b (y + m)) (jumps.image (· - m)) := by
    intro y hy
    have hy' : y + m ∉ jumps := fun hJ => hy (Finset.mem_image.2 ⟨y + m, hJ, by ring⟩)
    have hcm : Continuous fun z : ℝ => z + m := continuous_id.add continuous_const
    exact (hcm.tendsto y).eventually (hb (y + m) hy')
  have hG2 : IsGFFWithBoundaryData P h' (fun y => b (y + m)) (jumps.image (· - m)) := by
    rw [show h' = fun ω => Exist.flowField m 0 (h ω) from funext hh']
    exact Supp9.IsGFFWithBoundaryData.recenter hb m hh
  have hagree := Exist.StagedLaw.eq_of_isGFFWithBoundaryData hb' hbs hG' hG2
  set F : Finset ℝ := (J' ∪ jumps.image (· - m)).image (· + m) with hF
  have hdat : ∀ y ∉ F, affData 1 m b' y = b y := by
    intro y hy
    have hy' : y - m ∉ J' ∪ jumps.image (· - m) := fun h1 => hy (Finset.mem_image.2 ⟨y - m, h1, by ring⟩)
    simp only [affData, div_one]
    rw [hagree _ hy', sub_add_cancel]
  have hL : leftLim (affData 1 m b') = leftLim b := Restart.leftLim_congr hdat
  have hR : rightLim (affData 1 m b') = rightLim b := Restart.rightLim_congr hdat
  have hS : jumpSet (affData 1 m b') (affJumps 1 m J') = jumpSet b jumps :=
    GW1.jumpSet_eq_of_lims (isPiecewiseConstantBoundaryData_affData one_pos hb') hb hL hR
  have hrunc := run_congr_data (κ := κ) hL hR hS
  have hspec : Lu.relLowerSpec b' J' m = lw := by
    unfold Lu.relLowerSpec
    exact boundaryWalkSpec_congr hS _ _
  refine ⟨StagedReg.regFam E lw, ?_, ?_, ?_, ?_⟩
  · rw [hspec, hfield, isStagedHistory_congr_data hrunc]
    exact hE' lw hlwp
  · rw [hspec, stagedPiecesRegular_congr_data hrunc]
    exact hR'
  · filter_upwards [hWRA] with ω hω
    have hbws : boundaryWalkSpec (affData 1 m b') (affJumps 1 m J') (-(Real.pi / 2)) true = lw :=
      boundaryWalkSpec_congr hS _ _
    unfold Lx.WalkRightAdds Lx.LowerLaunch lowerWalkState at hω ⊢
    rw [hbws, run_eq_data hrunc]
    simp only [prefixPhysSet_congr_data hrunc]
    exact hω
  · filter_upwards [hrun lw hlwp] with ω hrω
    have hid : ∀ z, ((Chart.id.recenter m).recenter (-m)).2.1 z = z := fun z => by
      change z + ((-m : ℝ) : ℂ) + (m : ℂ) = z
      push_cast
      ring
    have hset : relPhysSet κ (affData 1 m b') (affJumps 1 m J') ((Chart.id.recenter m).recenter (-m))
        (Lu.relLowerSpec b' J' m) (fun j => StagedReg.regFam E lw j ω) = lowerWalkSet κ b jumps E ω := by
      rw [relPhysSet_of_id hid, hspec]
      unfold ExplState.physSet lowerWalkSet ExplState.physSet
      rw [run_eq_data hrunc, hrω]
    rw [hset]
    exact ⟨inter_subset_left, subset_rfl⟩

end InteractingSLE.Theorem14.SB.Lh
