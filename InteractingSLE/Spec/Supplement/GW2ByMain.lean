/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2ByAe
import InteractingSLE.Spec.Supplement.GW2BxMain

/-!
# nearImg for the package on a base family, under the stopped uncapped law (D83)

Packet PROVE-GW2-BUF (round 22). **`vNearImgOn_pkgS2`**: round 21's `vNearImgOn_pkgS` (same proof) with NEARIMG2's
stopped uncapped law `GW2Ni.StageLawUXSStatement` in place of the unstopped `GW2Ni.StageLawUXStatement` (D83). The
uncapped law is read only through D75's bad-set avoidance, now `ae_avoid_ZbS2`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC)

universe u

namespace InteractingSLE.Theorem14.GW2Bh

open Restart Exist Exist.StagedLaw Supp8.GB6.HullId GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootN4 GW2JDetR11
  GW2Rz GW2Rd GW2Rv GW2Sde GW2Sdh GW2Sdx GW2Sdy GW2Sdo

variable (h13 : Exist.Theorem13Statement.{u}) (ver₀ : SchedVerXFamily.{u}) (ch : SchedChoiceFamily.{u})
  (K₀ : PkgFamily.{u})

/-- **nearImg for the package on a base family** (stopped uncapped law). -/
theorem vNearImgOn_pkgS2 (hI : InstInputsX h13 (verS h13 ver₀ ch) ch) (hlaw : GW2Rd.StageLawXSStatement h13 ver₀)
    (hdeath : DeathThrXStatementS3 h13 ver₀ ch) (hlawU : GW2Ni.StageLawUXSStatement.{u})
    (hcov : Wire.T14Rk.VerCovers ver₀) (hexhS : GW2Ni.ExhStopStatement ver₀)
    (hcaps : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ), GoodRoot c r → GW2Sdx.HistOrdered c r l →
      ∀ᵐ ω ∂c.P, cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s → RootJ31.oldSuccess c r l ω →
        0 < candLife c r l a ω → ∀ n, (ver₀ Ω c r l a).V n ω < deathClockX c r l a ω)
    (hβ : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (y : RecData),
      (ch Ω c r l a).β y = upW ((RootJ31.candidateAngle c r a : ℝ) * chiC c.κ)
        (GW2Wm.baseWordX c.κ (GW2Sds.cfWordSrc c) (rootPt r.1) c.s (RootJ31.historyProgram c r l)
          ((entryList l).length + 1) (GW2Ru.length_historyProgram c r l) y))
    (k : ℕ) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) :
    GW2Sdz.VNearImgOn ((pkgS h13 ver₀ ch K₀ (kSelBS h13 ver₀ ch K₀) k).at 0) nearLam Ω c r l ((k : ℝ≥0∞) + 1)⁻¹
      (((GW2Sdz.J32S GW2Sdq.gapFam Ω c).experiment r).data.alive ((GW2Sdz.J32S GW2Sdq.gapFam Ω c).G r) l) := by
  classical
  unfold GW2Sdz.VNearImgOn
  by_cases hg : GoodRoot c r
  swap
  · filter_upwards [GW2Sds.ae_goodRoot_of_alive h13 c r l] with ω hω halive
    exact absurd (hω (GW2Sdz.alive_scaled_subset GW2Sdq.gapFam Ω c r l halive)) hg
  by_cases hTO : HistOrdered c r l
  swap
  · exact Eventually.of_forall fun ω halive => absurd
      (RootJ32.timeOrdered_historyProgram_of_alive c r l ω (GW2Sdz.alive_scaled_subset GW2Sdq.gapFam Ω c r l halive))
      hTO
  by_cases hgd : (RootJ31.historyProgram c r l).Pairwise (fun p q => p.2 < q.2) ∧
      (rootPt r.1 = 0 ∨ rootPt r.1 ∈ lowerArcRoots c.κ c.b c.jumps)
  swap
  · exact Eventually.of_forall fun ω halive => absurd (GW2Kt.guard_of_aliveS GW2Sdq.gapFam Ω c r l halive) hgd
  obtain ⟨hord', hroot⟩ := hgd
  obtain ⟨hx, hs⟩ := hg
  have hcovS := GW2Rl.verCovers_verU hcov (psiGoodS h13 ver₀ ch)
  have hbot := GW2Rl.hstructBot_junction (verS h13 ver₀ ch) (GW2Rl.refNb h13 (verS h13 ver₀ ch) cwSrc)
    (fun Ω _ _ c r l hg => GW2Rl.heq_refNb h13 (verS h13 ver₀ ch) GW2Sdq.gapFam cwSrc hcovS Ω c r l hg) Ω c r l
  have hav := ae_avoid_ZbS2 h13 ver₀ ch hcov hexhS hlawU hdeath c r l ⟨hx, hs⟩ hTO
    (fun a => hcaps Ω c r l a ⟨hx, hs⟩ hTO) (hβ Ω c r l) hroot hord'
  have hall := ae_bundleS h13 ver₀ ch hlaw hcov c r l hx hs hTO
  have hε : (0 : ℝ≥0∞) < ((k : ℝ≥0∞) + 1)⁻¹ / 2 :=
    ENNReal.div_pos (ENNReal.inv_ne_zero.2 (by simp)) (by norm_num)
  filter_upwards [ae_kernel_alive_gapFam h13 c r l, hbot,
    ae_kernel_refNb_eq h13 c r l (verS h13 ver₀ ch) ch hI hcovS, psiGoodS_spec h13 ver₀ ch c r l ⟨hx, hs⟩,
    Sec7.Aux122Disint.ae_ae_condExpKernel (sigma_le_ambient c r l) hall,
    Sec7.Aux122Disint.ae_ae_condExpKernel (sigma_le_ambient c r l) hav, ae_mem_aliveVer_iff h13 c r l,
    Sec7.Aux122Disint.ae_ae_condExpKernel_mem (sigma_le_ambient c r l) (measurableSet_aliveVer h13 c r l)]
    with ω₀ hkA hbotω hkNb hψ hkall hkav hiffA hkerA halive n
  have hA0 : condExpKernel c.P (c.sigma r l) ω₀ (aliveVer h13 c r l)ᶜ = 0 := ae_iff.1 (hkerA (hiffA.2 halive))
  -- the family at `ω₀`
  set f := (pkgS h13 ver₀ ch K₀ (kSelBS h13 ver₀ ch K₀) k Ω c r).nearFamily l ω₀ with hf
  have hb := hbotω halive
  have hlam0 : nearLam Ω c r l ω₀ ≠ 0 := nearLam_ne Ω c r l ω₀
  have hfsh := withNearSB_shape (pkgX h13 (verS h13 ver₀ ch) ch (KbS h13 ver₀ ch K₀)) nearLam
    (GW2Rl.refNb h13 (verS h13 ver₀ ch) cwSrc) (kSelBS h13 ver₀ ch K₀ k) Ω c r l ω₀ hlam0 hb
  have hfpos := positionsOf_pad (withNearSB_positions (pkgX h13 (verS h13 ver₀ ch) ch (KbS h13 ver₀ ch K₀)) nearLam
    (GW2Rl.refNb h13 (verS h13 ver₀ ch) cwSrc) (kSelBS h13 ver₀ ch K₀ k) Ω c r l ω₀ hlam0 hb)
  have hfgo := withNearSB_goLeft (pkgX h13 (verS h13 ver₀ ch) ch (KbS h13 ver₀ ch K₀)) nearLam
    (GW2Rl.refNb h13 (verS h13 ver₀ ch) cwSrc) (kSelBS h13 ver₀ ch K₀ k) Ω c r l ω₀ hlam0 hb
  have hctrl := outer_ctrl_of_nearShapeBot (f := f) hfsh hb
  -- the version loss and the selection bound, eventually
  have hψ' := hψ (fun n m => (pkgS h13 ver₀ ch K₀ (kSelBS h13 ver₀ ch K₀) k Ω c r).nearCandidate l ω₀ n (m + 1))
    n hε
  have hsm : ∀ᶠ m' : ℕ in atTop, (((m' + 1 : ℕ) : ℝ≥0∞) + 1)⁻¹ ≤ ((k : ℝ≥0∞) + 1)⁻¹ / 2 := by
    filter_upwards [ENNReal.tendsto_inv_nat_nhds_zero.eventually (gt_mem_nhds hε)] with m' hm'
    refine le_of_lt (lt_of_le_of_lt (ENNReal.inv_le_inv.2 ?_) hm')
    exact le_trans (by exact_mod_cast Nat.le_succ m') le_self_add
  rw [eventually_atTop] at hψ' hsm
  obtain ⟨M₁, hM₁⟩ := hψ'
  obtain ⟨M₂, hM₂⟩ := hsm
  refine eventually_atTop.2 ⟨M₁ + M₂ + 1, fun m hm => ?_⟩
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  -- the selected candidate
  set sel := nearSelSB c r (nearRootScale r.2 (nearLam Ω c r l ω₀)) (GW2Sdf.flipOf l.length)
    (GW2Rl.refNb h13 (verS h13 ver₀ ch) cwSrc Ω c r l ω₀)
    ((pkgX h13 (verS h13 ver₀ ch) ch (KbS h13 ver₀ ch K₀) Ω c r).nearFamily l ω₀) with hsel
  have hi₀ : angSelS h13 ver₀ ch K₀ k Ω c r l ω₀ (m' + 1) = sel.2 (m' + 1) := by
    simp only [angSelS, pkgS, withNearSB, Nat.unpair_pair]
    rfl
  set i₀ := angSelS h13 ver₀ ch K₀ k Ω c r l ω₀ (m' + 1) with hi₀def
  set kk := kSelS h13 ver₀ ch c r l ω₀ n i₀ (m' + 1) with hkk
  have hcand : (pkgS h13 ver₀ ch K₀ (kSelBS h13 ver₀ ch K₀) k Ω c r).nearCandidate l ω₀ n (m' + 1) =
      Nat.pair i₀ (Nat.pair (Nat.unpair kk).1 (Nat.unpair kk).2) := by
    rw [Nat.pair_unpair]
    exact nearCandidate_kSelBS h13 ver₀ ch K₀ k c r l ω₀ n (m' + 1)
  have hψm := hM₁ m' (by omega)
  beta_reduce at hψm
  rw [hcand] at hψm
  rw [hcand]
  set q := (Nat.unpair kk).1 with hq
  set b := (Nat.unpair kk).2 with hbq
  set a := Nat.pair i₀ (Nat.pair q b) with ha
  have hspec : GW2Sdf.PresentsO c.κ (upW ((RootJ31.angleEnumeration c r i₀ : ℝ) * chiC c.κ)
      (GW2Rl.refNb h13 (verS h13 ver₀ ch) cwSrc Ω c r l ω₀)) (nearRootScale r.2 (nearLam Ω c r l ω₀))
      (GW2Sdf.flipOf l.length) f.xL (f.ρLs (m' + 1)) f.xR (f.ρRs (m' + 1)) := by
    rw [hi₀]
    exact nearSelSB_spec c r (nearRootScale_ne_zero r.2 hlam0) (GW2Sdf.flipOf l.length) hb _ (m' + 1)
  -- the record of a kernel sample decodes `ω₀`'s near base
  have hdec : ∀ ξ : Ω, GW2Rl.refPreV h13 (verS h13 ver₀ ch) Ω c r l ξ = GW2Rl.refPreV h13 ver₀ Ω c r l ξ →
      GW2Rl.refNb h13 (verS h13 ver₀ ch) cwSrc Ω c r l ξ = GW2Rl.refNb h13 (verS h13 ver₀ ch) cwSrc Ω c r l ω₀ →
      wordD c r l (augRec (stageEncRec c r l) (fun ω => GW2Rl.refPreV h13 ver₀ Ω c r l ω) ξ) =
        GW2Rl.refNb h13 (verS h13 ver₀ ch) cwSrc Ω c r l ω₀ := by
    intro ξ hrefE hNb
    rw [← hNb]
    unfold GW2Rl.refNb wordD
    simp only [augRec, hrefE]
    rfl
  -- the kernel samples avoid D75's bad sets of `i₀`
  have havK : ∀ᵐ ξ ∂condExpKernel c.P (c.sigma r l) ω₀, ∃ Q : ℝ≥0, ∀ q' : ℕ,
      Q ≤ (RootJ31.timeEnumeration c r q' : ℝ≥0) → ∀ᶠ b' in atTop, ξ ∉ ZsS h13 ver₀ ch c r l n i₀ q' b' := by
    filter_upwards [hkav, hkA halive, hkNb halive, hkall] with ξ hG hξA hξNb hξall
    obtain ⟨hB, -, -, -⟩ := hξall
    obtain ⟨-, -, -, -, -, hrefE⟩ := hB hξA
    have hw := hdec ξ hrefE hξNb
    have hP : ξ ∈ PresS h13 ver₀ c r l i₀ := by
      refine ⟨f, m' + 1, ?_, fun i' => ?_, fun j => ?_, ?_, hctrl.1, hctrl.2⟩
      · unfold shapeD; rw [hw]; exact hfsh
      · unfold posLD; rw [hw]; exact hfpos.1 i'
      · unfold posRD; rw [hw]; exact hfpos.2 j
      · rw [hw]; exact hspec
    obtain ⟨Q, hQ⟩ := hG hξA n i₀ hP
    exact ⟨Q, fun q' hq' => (hQ q' hq').mono fun b' hb' hm => hb' hm.2⟩
  have hZb := kSelS_spec h13 ver₀ ch c r l hI hTO ω₀ n i₀ havK (m' + 1)
  rw [← hkk] at hZb
  set N : Set Ω := (({ξ | ∃ K, ξ ∈ goodFrom h13 ver₀ ch c r l hx (exitN c r l) n a K} \
      goodFrom h13 ver₀ ch c r l hx (exitN c r l) n a (psiGoodS h13 ver₀ ch Ω c r l a m')) ∪
    ZsS h13 ver₀ ch c r l n i₀ q b) ∪ (aliveVer h13 c r l)ᶜ with hN
  refine ⟨N, ?_, ?_⟩
  · calc condExpKernel c.P (c.sigma r l) ω₀ N
        ≤ condExpKernel c.P (c.sigma r l) ω₀ ({ξ | ∃ K, ξ ∈ goodFrom h13 ver₀ ch c r l hx (exitN c r l) n a K} \
            goodFrom h13 ver₀ ch c r l hx (exitN c r l) n a (psiGoodS h13 ver₀ ch Ω c r l a m')) +
          condExpKernel c.P (c.sigma r l) ω₀ (ZsS h13 ver₀ ch c r l n i₀ q b) +
          condExpKernel c.P (c.sigma r l) ω₀ (aliveVer h13 c r l)ᶜ :=
          (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
      _ ≤ ((k : ℝ≥0∞) + 1)⁻¹ / 2 + ((k : ℝ≥0∞) + 1)⁻¹ / 2 + 0 :=
          add_le_add (add_le_add hψm (hZb.trans (hM₂ m' (by omega)))) hA0.le
      _ = ((k : ℝ≥0∞) + 1)⁻¹ := by rw [add_zero, ENNReal.add_halves]
  · filter_upwards [hkA halive, hkNb halive, hkall] with ξ hξA hξNb hξall hξN
    obtain ⟨hB, hreachξ, hphysξ, hagξ⟩ := hξall
    obtain ⟨⟨hcf, hcon⟩, href, hband, hold, hGTξ, hrefE⟩ := hB hξA
    have hw := hdec ξ hrefE hξNb
    have hsh : famShapeB f = shapeD c r l
        (augRec (stageEncRec c r l) (fun ω => GW2Rl.refPreV h13 ver₀ Ω c r l ω) ξ) := by
      unfold shapeD; rw [hw]; exact hfsh
    have hL : ∀ i' : Fin f.nL, f.xL i' =
        posLD c r l (augRec (stageEncRec c r l) (fun ω => GW2Rl.refPreV h13 ver₀ Ω c r l ω) ξ) i' :=
      fun i' => by unfold posLD; rw [hw]; exact hfpos.1 i'
    have hR : ∀ j : Fin f.nR, f.xR j =
        posRD c r l (augRec (stageEncRec c r l) (fun ω => GW2Rl.refPreV h13 ver₀ Ω c r l ω) ξ) j :=
      fun j => by unfold posRD; rw [hw]; exact hfpos.2 j
    -- off the loss
    have hnot : ξ ∉ N := hξN
    rw [hN, mem_union, mem_union, not_or, not_or] at hnot
    have hAV : ξ ∈ aliveVer h13 c r l := not_not.1 hnot.2
    have hZbξ : ξ ∉ ZbS h13 ver₀ ch c r l n i₀ q b := fun h => hnot.1.2 ⟨hAV, h⟩
    have hgF : ∃ K, ξ ∈ goodFrom h13 ver₀ ch c r l hx (exitN c r l) n a K := by
      by_contra h
      exact hZbξ (not_goodFrom_subset_ZbS h13 ver₀ ch c r l ⟨hx, hs⟩ n i₀ q b h)
    have hgF' : ξ ∈ goodFrom h13 ver₀ ch c r l hx (exitN c r l) n a (psiGoodS h13 ver₀ ch Ω c r l a m') := by
      by_contra h
      exact hnot.1.1 ⟨hgF, h⟩
    have hgoodJ : ξ ∈ goodVer h13 ver₀ ch c r l hx (exitN c r l) n a (JS h13 ver₀ ch Ω c r l a m') := by
      simp only [goodFrom, mem_iInter] at hgF'
      exact hgF' _ (psiGoodS_le_JS h13 ver₀ ch Ω c r l a m')
    have hslot : ξ ∈ slotGoodS h13 ver₀ ch c r l n (m' + 1) a := by
      simp only [slotGoodS, GoodRoot, hx, hs, and_self, ↓reduceDIte, Nat.add_sub_cancel]
      exact hgoodJ
    have hsrcξ : ¬ ((GW2Sdg.rootGain c r l a ξ : ℝ≥0∞) <
        ((pkgX h13 (verS h13 ver₀ ch) ch (KbS h13 ver₀ ch K₀) Ω c r).nearVar l n (m' + 1) a).stop ξ) :=
      fun h => hZbξ (srcBadS_subset_ZbS h13 ver₀ ch K₀ c r l n (m' + 1) i₀ q b ⟨hslot, h⟩)
    exact GW2Rf.slot_clausesU h13 ver₀ (psiGoodS h13 ver₀ ch) ch K₀ c r l hx hs ξ n m' a f hgoodJ hcf (hcon a)
      (hGTξ a) (href a) (hagξ a (hGTξ a) hold) hsh hL hR hsrcξ (hreachξ a (m' + 1)) hband (hphysξ a) hfgo

end InteractingSLE.Theorem14.GW2Bh
