/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2LwWord

/-!
# SB2(2)'s word half PROVED; R99's target reduced to the law half

Packet PROVE-T14-SB2LOW (ruling R99). See `SB2LwWord` for the route. Results:

* **`sb2LowerWordAdmStatement_of_gw0`**: `Lz.SB2LowerWordAdmStatement` from GW0's forward statement (which gives GW1's
  ambient bound through the complete counterflow, `GW1Conn.ambient_bounds`);
* **`sb2LowerWordAdmStatement_of_theorem13`**, **`sb2LowerWordStatement_of_theorem13`**: the same from Theorem 1.3 at
  universe `0` (`BR3Ref.gw0ForwardStatement_of_theorem13`), and with FIN5's `e_R ≥ 0` SB2(2)'s whole word half;
* **`sb2LowerLaunchEntryAdmStatement_of_law`**: R99's target `Lz.SB2LowerLaunchEntryAdmStatement` from Theorem 1.3 and
  the law half `Lz.SB2LowerLawStatement` only.

R48: Theorem 1.3 appears only as a hypothesis; this serves Theorem 1.4.
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

open Exist Exist.StagedLaw Exist.Staged Restart GW1W FlowDilate

/-- **SB2(2)'s word half** (`Lz.SB2LowerWordAdmStatement`) from GW0's forward statement: at almost every launch of
the upper schedule, every launch witness's data are admissible for the lower flow left of the upper tip and carry
SB2(2)'s active word on `(m, 0)`. -/
theorem sb2LowerWordAdmStatement_of_gw0 (hGW0 : GW0.GW0ForwardStatement.{u}) : Lz.SB2LowerWordAdmStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER x₀ l k hx₀ hlp hlθ hL hleft
  have hamb := (GW1Conn.ambient_bounds hGW0 hκ hκ4 hb hh hcf hζ').1
  have hsp : IsBoundaryContinuedProgram (Lu.upperSpec x₀ l).2.2 := Lu.isBoundaryContinuedProgram_upperSpec hlθ
  obtain ⟨hE', hreg', hrun⟩ := StagedReg.regFam_spec hb hE hER
  obtain ⟨β, Y, hW, hI⟩ := exists_witness_upper hκ hκ4 hb hh hx₀ hlθ (hE' _ hsp) (hreg' _) hamb k
  have hpm' : Measurable (pastMap κ b jumps (Lu.upperSpec x₀ l) (StagedReg.regFam E (Lu.upperSpec x₀ l)) k) :=
    Measurable.of_comap_le ((hE' _ hsp).2.1 k)
  have hpm : Measurable (pastMap κ b jumps (Lu.upperSpec x₀ l) (E (Lu.upperSpec x₀ l)) k) :=
    Measurable.of_comap_le ((hE _ hsp).2.1 k)
  have hK : ∀ᵐ ω₀ ∂P, condExpKernel P (pastSigma κ b jumps (Lu.upperSpec x₀ l)
      (StagedReg.regFam E (Lu.upperSpec x₀ l)) k) ω₀ =
      condExpKernel P (pastSigma κ b jumps (Lu.upperSpec x₀ l) (E (Lu.upperSpec x₀ l)) k) ω₀ :=
    StagedReg.ae_condExpKernel_eq_of_ae_eq hpm' hpm (StagedReg.ae_pastMap_regHist (hER _ hsp) k)
  filter_upwards [hrun _ hsp, hK, ae_eq_fn_of_witness hb hh (hE' _ hsp) (hreg' _) hW, hER _ hsp]
    with ω₀ hr hk hfn hR₀
  intro c θ hcθ b' J' h' hb' hT' hG' m hm
  -- the regularized family runs through the same states
  have hcθ' : (ExplState.run κ b jumps (Lu.upperSpec x₀ l)
      (fun j => StagedReg.regFam E (Lu.upperSpec x₀ l) j ω₀) (k + 1)).2.2.2.1 k = some (c, θ) := by
    rw [hr]; exact hcθ
  rw [← hk] at hG'
  have hagree := hfn c θ hcθ' b' J' h' hb' hT' hG'
  have hUI := hI ω₀ (by rw [hcθ']; simp)
  rw [hr k] at hUI
  -- the launch chart, the prefix and its largest real point
  have hregE : ∀ j c' θ', (ExplState.run κ b jumps (Lu.upperSpec x₀ l)
      (fun i => E (Lu.upperSpec x₀ l) i ω₀) (j + 1)).2.2.2.1 j = some (c', θ') →
      GW1P.PieceRegular (E (Lu.upperSpec x₀ l) j ω₀).1
        (min (instrTime (Lu.upperSpec x₀ l) j) (E (Lu.upperSpec x₀ l) j ω₀).2) :=
    fun j c' θ' hl'' => hR₀ j θ' _ c' (eq_launch_of_launches _ _ hl'').1 hl''
  have hF : ω₀ ∈ Lu.upperLaunchSet κ b jumps E x₀ l k := Lu.mem_upperLaunchSet hcθ
  have hAc := Lu.isCompact_upperPrefix hregE hF
  obtain ⟨-, -, hcc⟩ := eq_launch_of_launches _ _ hcθ
  have hnot := Lx.stStatus_ne_done_of_launches _ _ hcθ
  obtain ⟨-, hRle⟩ := realMax_upperPrefix_le hx₀ hUI.1 hAc
  obtain ⟨heq, hmono, hlim⟩ := upper_bdry_facts (Lu.upperSpec x₀ l) (fun j => E (Lu.upperSpec x₀ l) j ω₀) hregE k
    hnot hUI.1 hAc (Lw.fillH_union_real _ _) (fun y hy => Lx.le_realMax_of_mem hAc hy)
  have he : Lu.upperEntry κ b jumps E x₀ l k ω₀ = Lx.rightEntry (stChart (ExplState.run κ b jumps
      (Lu.upperSpec x₀ l) (fun j => E (Lu.upperSpec x₀ l) j ω₀) k)) (realMax (upperPrefix κ b jumps E x₀ l k ω₀)) := by
    unfold Lu.upperEntry
    rw [Lu.upperLaunchChart_eq hcθ, hcc]
  obtain ⟨hw1, hw2⟩ := word_of_uInv hUI hRle heq hmono hlim
  rw [← he] at hw2
  set e := Lu.upperEntry κ b jumps E x₀ l k ω₀ with hedef
  subst hm
  have hl := Sec4.sleLambda_pos hκ
  have haff : ∀ y, affData 1 (-e) b' y = b' (y + e) := fun y => by
    simp only [affData, sub_neg_eq_add, div_one]
  have hJaff : ∀ y, y ∉ affJumps 1 (-e) J' → y + e ∉ J' := fun y hy hJ => hy
    (Finset.mem_image.2 ⟨y + e, hJ, by unfold raff; ring⟩)
  refine ⟨fun y hy hyJ => ?_, fun y hy hyJ => ?_⟩
  · -- (a) admissible left of the upper tip
    rw [haff]
    obtain ⟨z, hz, hzF, hbz⟩ := exists_lt_near ((hb' _ (hJaff y hyJ)).filter_mono nhdsWithin_le_nhds)
      (J' ∪ (β ω₀).jumps)
    have hlt := hw1 z (by linarith) (fun hJ => hzF (Finset.mem_union_right _ hJ))
    rw [← hbz, hagree z hzF, Sec4.cumWeightLeft]
    have := (div_lt_one hl).2 hlt
    rw [neg_div]
    linarith
  · -- (b) the active word on `(m, 0)`
    rw [haff]
    have hz0 : 0 < y + e := by linarith [hy.1]
    have hze : y + e < e := by linarith [hy.2]
    have hev : ∀ᶠ z in 𝓝[<] (y + e), b' z = b' (y + e) ∧ z ∈ Ioo 0 (y + e) :=
      ((hb' _ (hJaff y hyJ)).filter_mono nhdsWithin_le_nhds).and (Ioo_mem_nhdsLT hz0)
    obtain ⟨z, -, hzF, hbz, hz⟩ := exists_lt_near hev (J' ∪ (β ω₀).jumps)
    rw [← hbz, hagree z hzF]
    rcases hw2 z ⟨hz.1, hz.2.trans hze⟩ (fun hJ => hzF (Finset.mem_union_right _ hJ)) with hs | hbr
    · exact Or.inl hs
    · exact Or.inr (Or.inr hbr)

/-- **SB2(2)'s word half from Theorem 1.3** (at universe `0`, for GW1's ambient bound). -/
theorem sb2LowerWordAdmStatement_of_theorem13 (h13 : Exist.Theorem13Statement.{0}) :
    Lz.SB2LowerWordAdmStatement.{u} :=
  sb2LowerWordAdmStatement_of_gw0 (BR3Ref.gw0ForwardStatement_of_theorem13 h13)

/-- **SB2(2)'s whole word half** (`e_R ≥ 0` is FIN5's `Lu.ae_upperEntry_nonneg`). -/
theorem sb2LowerWordStatement_of_theorem13 (h13 : Exist.Theorem13Statement.{0}) : Lz.SB2LowerWordStatement.{u} :=
  Lz.sb2LowerWordStatement_of_adm (sb2LowerWordAdmStatement_of_theorem13 h13)

/-- **R99's target from Theorem 1.3 and SB2(2)'s law half only.** -/
theorem sb2LowerLaunchEntryAdmStatement_of_law (h13 : Exist.Theorem13Statement.{0})
    (hl : Lz.SB2LowerLawStatement.{u}) : Lz.SB2LowerLaunchEntryAdmStatement.{u} :=
  Lz.sb2LowerLaunchEntryAdmStatement_of_word_law (sb2LowerWordStatement_of_theorem13 h13) hl

end InteractingSLE.Theorem14.SB.Lh
