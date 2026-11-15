/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2JwFull
import InteractingSLE.Spec.Supplement.SB2LwFinal

/-!
# SB2(2): the ray correspondence at the upper launch chart, a.s. (item 4a)

Packet PROVE-SB2-LIFTSET (round 17). **`sb2LowerRayCorr`** (Theorem 1.3, and Theorem 1.3 at universe `0` for GW1's
ambient bound): at almost every launch of the upper schedule and for every witness `(b', J', h')` of its conditional
law, with `m = −e_R`, the ray map `ι = rayMap (bdryValue c) R e_R` is a ray correspondence between `b` and the relative
data `affData 1 m b'`, continuous on `[R, ∞)`, and the upper chart satisfies `RayChartLim` and `RayChartInj` for `ι`.

The proof runs on the regularized family (same runs almost surely): SB2(2)'s upper witnesses (`UInv`, the word `β`
original beyond the record), the witness data equal to `β` off a finite set, the whole upper pieces' traces
(`ae_pieceRegular_full_of_regular`) for the record bound `stRecR ≤ R` (`upper_rec_le`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H Hbar)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lk

open Supp9B Lx Lu Leaf FlowDilate Sec4 Exist Exist.Staged Exist.StagedLaw LuM GW1W GW1Bookkeep GW1P Lh Restart

/-- **The ray correspondence at the upper launch chart, almost surely.** -/
theorem sb2LowerRayCorr (h13 : Exist.Theorem13Statement.{u}) (h13₀ : Exist.Theorem13Statement.{0}) :
    Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ _ _ E u l k ω₀ c b' J' _ =>
      ∀ m : ℝ, m = -upperEntry κ b jumps E u l k ω₀ →
        RayCorr b jumps (affData 1 m b') (affJumps 1 m J') (realMax (upperPrefix κ b jumps E u l k ω₀))
            (rayMap (Lx.bdryValue c) (realMax (upperPrefix κ b jumps E u l k ω₀))
              (upperEntry κ b jumps E u l k ω₀)) ∧
          ContinuousOn (rayMap (Lx.bdryValue c) (realMax (upperPrefix κ b jumps E u l k ω₀))
              (upperEntry κ b jumps E u l k ω₀))
            (Ici (realMax (upperPrefix κ b jumps E u l k ω₀))) ∧
          RayChartLim c (realMax (upperPrefix κ b jumps E u l k ω₀)) m
            (rayMap (Lx.bdryValue c) (realMax (upperPrefix κ b jumps E u l k ω₀))
              (upperEntry κ b jumps E u l k ω₀)) ∧
          RayChartInj c (realMax (upperPrefix κ b jumps E u l k ω₀)) m
            (rayMap (Lx.bdryValue c) (realMax (upperPrefix κ b jumps E u l k ω₀))
              (upperEntry κ b jumps E u l k ω₀)) := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER x₀ l k hx₀ hlp hlθ hL hleft
  have hGW0 := BR3Ref.gw0ForwardStatement_of_theorem13 h13₀
  have hamb := (GW1Conn.ambient_bounds hGW0 hκ hκ4 hb hh hcf hζ').1
  have hsp : IsBoundaryContinuedProgram (Lu.upperSpec x₀ l).2.2 := Lu.isBoundaryContinuedProgram_upperSpec hlθ
  obtain ⟨hE', hreg', hrun⟩ := StagedReg.regFam_spec hb hE hER
  choose β Y hW hI using exists_witness_upper hκ hκ4 hb hh hx₀ hlθ (hE' _ hsp) (hreg' _) hamb
  have hpm' : Measurable (pastMap κ b jumps (Lu.upperSpec x₀ l) (StagedReg.regFam E (Lu.upperSpec x₀ l)) k) :=
    Measurable.of_comap_le ((hE' _ hsp).2.1 k)
  have hpm : Measurable (pastMap κ b jumps (Lu.upperSpec x₀ l) (E (Lu.upperSpec x₀ l)) k) :=
    Measurable.of_comap_le ((hE _ hsp).2.1 k)
  have hK : ∀ᵐ ω₀ ∂P, condExpKernel P (pastSigma κ b jumps (Lu.upperSpec x₀ l)
      (StagedReg.regFam E (Lu.upperSpec x₀ l)) k) ω₀ =
      condExpKernel P (pastSigma κ b jumps (Lu.upperSpec x₀ l) (E (Lu.upperSpec x₀ l)) k) ω₀ :=
    StagedReg.ae_condExpKernel_eq_of_ae_eq hpm' hpm (StagedReg.ae_pastMap_regHist (hER _ hsp) k)
  have hfullAS := ae_all_iff.2 fun j =>
    ae_pieceRegular_full_of_regular h13 hκ hb (hE' _ hsp) (hreg' (Lu.upperSpec x₀ l)) j
  have hpiecesAS := (Exist.StagedLaw.stagedPiecesRegular_of_regular h13 hκ hb (hE' _ hsp)
    (hreg' (Lu.upperSpec x₀ l))).ae_pieceRegular
  filter_upwards [hrun _ hsp, hK, ae_eq_fn_of_witness hb hh (hE' _ hsp) (hreg' _) (hW k), hER _ hsp, hfullAS,
    hpiecesAS] with ω₀ hr hk hfn hR₀ hfull₀ hpieces₀
  intro c θ hcθ b' J' h' hb' hT' hG' m hm
  set spec := Lu.upperSpec x₀ l with hspec
  set D' : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞ := fun j => StagedReg.regFam E spec j ω₀ with hD'
  -- the regularized family runs through the same states
  have hcθ' : (ExplState.run κ b jumps spec D' (k + 1)).2.2.2.1 k = some (c, θ) := by rw [hr]; exact hcθ
  rw [← hk] at hG'
  have hagree := hfn c θ hcθ' b' J' h' hb' hT' hG'
  have hlk : (ExplState.run κ b jumps spec D' (k + 1)).2.2.2.1 k ≠ none := by rw [hcθ']; simp
  have hUI := hI k ω₀ hlk
  obtain ⟨-, -, hcc⟩ := eq_launch_of_launches _ _ hcθ'
  have hnot := Lx.stStatus_ne_done_of_launches _ _ hcθ'
  -- the upper prefix and its largest real point
  have hregE : ∀ j c' θ',
      (ExplState.run κ b jumps spec (fun i => E spec i ω₀) (j + 1)).2.2.2.1 j = some (c', θ') →
      GW1P.PieceRegular (E spec j ω₀).1 (min (instrTime spec j) (E spec j ω₀).2) :=
    fun j c' θ' hl'' => hR₀ j θ' _ c' (eq_launch_of_launches _ _ hl'').1 hl''
  have hF : ω₀ ∈ Lu.upperLaunchSet κ b jumps E x₀ l k := Lu.mem_upperLaunchSet hcθ
  have hAc := Lu.isCompact_upperPrefix hregE hF
  have hpre : SB.prefixPhysSet κ b jumps spec D' k =
      SB.prefixPhysSet κ b jumps spec (fun i => E spec i ω₀) k := by
    unfold SB.prefixPhysSet; rw [hr]
  have hAf : fillH (upperPrefix κ b jumps E x₀ l k ω₀) = fillH (SB.prefixPhysSet κ b jumps spec D' k) := by
    rw [hpre]; exact Lw.fillH_union_real _ _
  have hRA : ∀ y : ℝ, (y : ℂ) ∈ upperPrefix κ b jumps E x₀ l k ω₀ →
      y ≤ realMax (upperPrefix κ b jumps E x₀ l k ω₀) :=
    fun y hy => Lx.le_realMax_of_mem hAc hy
  have hR0 : 0 ≤ realMax (upperPrefix κ b jumps E x₀ l k ω₀) := hRA 0 (Or.inr ⟨0, ⟨hx₀, le_rfl⟩, rfl⟩)
  have he : Lu.upperEntry κ b jumps E x₀ l k ω₀ =
      Lx.rightEntry (stChart (ExplState.run κ b jumps spec D' k))
        (realMax (upperPrefix κ b jumps E x₀ l k ω₀)) := by
    unfold Lu.upperEntry
    rw [Lu.upperLaunchChart_eq hcθ, hcc]
  -- the record bound
  have hregD' : ∀ j c' θ', (ExplState.run κ b jumps spec D' (j + 1)).2.2.2.1 j = some (c', θ') →
      GW1P.PieceRegular (D' j).1 (min (instrTime spec j) (D' j).2) :=
    fun j c' θ' hl'' => hpieces₀ j c' θ' hl''
  have hrec : stRecR (ExplState.run κ b jumps spec D' k) ≤ realMax (upperPrefix κ b jumps E x₀ l k ω₀) := by
    refine upper_rec_le hx₀ (fun j => hreg' spec j ω₀) hregD' (fun j hlj => ?_) (fun j hlj => (hI j ω₀ hlj).1) hlk
      hR0 fun y hy => hRA y (Or.inl
        (show (y : ℂ) ∈ SB.prefixPhysSet κ b jumps spec (fun i => E spec i ω₀) k from hpre ▸ hy))
    obtain ⟨⟨c', θ'⟩, hl''⟩ := Option.ne_none_iff_exists'.1 hlj
    exact hfull₀ j c' θ' hl''
  subst hcc
  subst hm
  rw [he]
  have hS := hUI.1
  exact ⟨rayCorr_of_run spec D' hregD' k hnot hAc hAf hRA hS hrec hb hUI.2.1 hb' hagree,
    continuousOn_rayMap (runRay_facts spec D' hregD' k hnot hAc hAf hRA).1
      (runRay_facts spec D' hregD' k hnot hAc hAf hRA).2.2.2.2,
    rayChartLim_of_run spec D' hregD' k hnot hAc hAf hRA,
    rayChartInj_of_run spec D' hregD' k hnot hAc hAf hRA hS hrec⟩

end InteractingSLE.Theorem14.SB.Lk
