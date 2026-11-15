/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BvCore

/-!
# nearImg for the final package

Packet PROVE-GW2-BUF (round 19). **`vNearImgOn_pkgF`**: the `hnearImg` of the top (`GW2Sdz.VNearImgOn` with
`ε = (k + 1)⁻¹` on the alive events of `J32S GW2Sdq.gapFam`) for the final package `pkgF h13 h12 K₀ kSel k`.

Premises (consumed statements, by owner):
* `hI` — the owners' instance inputs for the final version family (RELDET's `instInputsX_of_linesX_mean` with
  STAGEMEAN's mean, the top's `hmeanF`, `hno`);
* `hlaw` — STAGEMEAN/RELDET's stage law in version form (`StageLawXStatement`, D17 (B));
* `hdeath` — NOTHR's threshold at the death (`DeathThrXStatement`, D35 (D-a));
* `hsrc` — NEARIMG2's `kSel` bound (`SrcBoundStatement`, D50).

Proof. At an alive `ω₀` (a good root and an ordered history; otherwise the alive event is null), for level `n`,
eventually in `m = m' + 1`, the loss is
`N = ({∃ k, goodFrom k} \ goodFrom (ψ a m')) ∪ srcBad (n, m, a)` at the selected candidate `a`, of conditional
probability `≤ ε/2 + ε/2` (`psiGood_spec`, `hsrc`). For almost every kernel sample `ξ`:
* it is alive (`ae_kernel_alive_gapFam`), and `pkgNb ξ = pkgNb ω₀` (`ae_kernel_pkgNb_eq`);
* the P-a.s. facts hold at `ξ` (transferred by `Aux122Disint.ae_ae_condExpKernel`);
* round 18's `ae_eventually_good_instX` puts `ξ` in some `goodFrom`: the rightward family is decoded from `ξ`'s
  reference record (`withNearSB_shape/positions`, `nearSelSB_spec`, `outer_ctrl_of_nearShapeBot`).

Off `N`, `slot_clauses` gives the three clauses.
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

variable (h13 : Exist.Theorem13Statement.{u}) (h12 : Exist.Theorem12Statement.{u}) (K₀ : PkgFamily.{u})

/-- **nearImg for the final package** (the top's `hnearImg`). -/
theorem vNearImgOn_pkgF (hI : InstInputsX h13 (pkgVerF h13 h12) (pkgCh h13 h12 cwSrc))
    (hlaw : StageLawXStatement h13 (schedVerXDeathFamily h13))
    (hdeath : DeathThrXStatement h13 (schedVerXDeathFamily h13) (pkgCh h13 h12 cwSrc))
    (kSel : NearSelB.{u}) (hsrc : SrcBoundStatement h13 h12 K₀ kSel) (k : ℕ) (Ω : Type u) [MeasurableSpace Ω]
    [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) :
    GW2Sdz.VNearImgOn ((pkgF h13 h12 K₀ kSel k).at 0) nearLam Ω c r l ((k : ℝ≥0∞) + 1)⁻¹
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
  obtain ⟨hx, hs⟩ := hg
  set A := ((GW2Sdz.J32S GW2Sdq.gapFam Ω c).experiment r).data.alive ((GW2Sdz.J32S GW2Sdq.gapFam Ω c).G r) l
    with hAdef
  set T := RootJ31.historyTime c r l with hT
  set ver₀ := schedVerXDeathFamily h13 with hver₀
  set ch := pkgCh h13 h12 cwSrc with hch
  -- the almost-sure facts at a sample
  have hβ : ∀ a (y : RecData), (ch Ω c r l a).β y = upW ((RootJ31.candidateAngle c r a : ℝ) * chiC c.κ)
      (GW2Wm.baseWordX c.κ (GW2Sds.cfWordSrc c) (rootPt r.1) c.s (RootJ31.historyProgram c r l)
        ((entryList l).length + 1) (GW2Ru.length_historyProgram c r l) y) := fun a y => by
    rw [GW2Sdt.schedChoiceLinesX_β]
    show GW2Wm.schedWordMapX c.κ (GW2Sds.cfWordSrc c) (rootPt r.1) c.s (RootJ31.historyProgram c r l)
      ((entryList l).length + 1) (GW2Ru.length_historyProgram c r l) (candAngle c r l a) y = _
    unfold GW2Wm.schedWordMapX
    rw [GW2Rj.candAngle_eq]
  have hgoodE : ∀ᵐ ξ ∂c.P, ∀ a n : ℕ, ξ ∈ A →
      ∀ (f : NearCrossingFamily.{u} c.κ) (m j₀ : ℕ),
      ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) T ξ) < (ver₀ Ω c r l a).V j₀ ξ →
      famShapeB f = shapeD c r l ((instX h13 ver₀ ch Ω c r l a j₀ hx).srecX c r l (rootPt r.1) ξ) →
      (∀ i : Fin f.nL, f.xL i = posLD c r l ((instX h13 ver₀ ch Ω c r l a j₀ hx).srecX c r l (rootPt r.1) ξ) i) →
      (∀ j : Fin f.nR, f.xR j = posRD c r l ((instX h13 ver₀ ch Ω c r l a j₀ hx).srecX c r l (rootPt r.1) ξ) j) →
      GW2Sdf.PresentsO c.κ (upW ((RootJ31.candidateAngle c r a : ℝ) * chiC c.κ)
          (GW2Wm.baseWordX c.κ (GW2Sds.cfWordSrc c) (rootPt r.1) c.s (RootJ31.historyProgram c r l)
          ((entryList l).length + 1) (GW2Ru.length_historyProgram c r l)
          ((instX h13 ver₀ ch Ω c r l a j₀ hx).srecX c r l (rootPt r.1) ξ))) (scL r l) (GW2Sdf.flipOf l.length) f.xL
          (f.ρLs m) f.xR (f.ρRs m) →
      f.mL ≤ f.nL - 1 → f.mR ≤ f.nR - 1 →
      ∀ᶠ j in atTop, ξ ∈ goodVer h13 ver₀ ch c r l hx (exitN c r l) n a j :=
    ae_all_iff.2 fun a => ae_all_iff.2 fun n =>
      (ae_eventually_good_instX h13 GW2Sdq.gapFam c r l a ⟨hx, hs⟩ hTO ver₀ ch hlaw hdeath
        (schedVerXDeath_exhausts_death h13 c r l a hx hs hTO) (GW2Sds.cfWordSrc c) (RootJ31.candidateAngle c r a)
        (hβ a) n (shapeD c r l) (posLD c r l) (posRD c r l) (c2L_pos r l) (sqrt_scL r l)
        (GW2Sdf.flipOf l.length)).mono fun ξ h hξ f m j₀ h1 h2 h3 h4 h5 h6 h7 => h hξ f m j₀ h1 h2 h3 h4 h5 h6 h7
  have hreachE : ∀ᵐ ξ ∂c.P, ∀ a m : ℕ, ∀ (lam : ℝ) (τ : ℝ≥0∞) (t : ℝ≥0), 0 < lam →
      GW2Bf.histStart c r l ξ < 2 + 1 / 8 → lam * (2 + 1 / 8 - GW2Bf.histStart c r l ξ) ≤ 2 + 1 / 8 →
      τ ≤ (GW2Sdg.rootGain c r l a ξ : ℝ≥0∞) →
      τ ≤ (pkgVerF h13 h12 Ω c r l a).V m ξ - (GW2Sdg.rootHistCap c r l a ξ : ℝ≥0∞) →
      (t : ℝ≥0∞) < (4 : ℝ≥0∞) ^ r.2 * τ →
      2 + 1 / 8 < lam * ((-1 : ℝ) ^ l.length * ((2 : ℝ) ^ r.2 *
        (instX h13 (pkgVerF h13 h12) ch Ω c r l a m hx).drvX c (rootPt r.1) (t / (4 : ℝ≥0) ^ r.2) ξ)) →
      RootJ32.sourceSample c r l a ξ ∈ RootD25.reachSet :=
    ae_all_iff.2 fun a => ae_all_iff.2 fun m =>
      ae_reach_of_visit_instX h13 c r l a hx hTO ((pkgVerF h13 h12 Ω c r l a).isA hx m) (ch Ω c r l a)
  have hphysE : ∀ᵐ ξ ∂c.P, ∀ a : ℕ, 0 < (RootJ31.sourceSample c r l a ξ).1 →
      physClockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a) T ξ =
        ((GW2Sdg.rootHistCap c r l a ξ : ℝ≥0) : ℝ≥0∞) :=
    ae_all_iff.2 fun a => ae_physClockX_eq_histCap h13 c r l a hx
  have hcanE : ∀ᵐ ξ ∂c.P, ∀ a : ℕ, ξ ∈ schedGTX h13 c r l a → RootJ31.oldSuccess c r l ξ →
      ∃ Wc : ℝ≥0 → ℝ, IsCanonX c r l a (ver₀ Ω c r l a).R (ver₀ Ω c r l a).V ξ Wc :=
    ae_all_iff.2 fun a => hlaw Ω c r l a ⟨hx, hs⟩ hTO
  have hGTE : ∀ᵐ ξ ∂c.P, ∀ a, ξ ∈ schedGTX h13 c r l a ↔ cfRec c.s c.W c.ζ ξ ∈ goodX (rootPt r.1) c.s :=
    ae_all_iff.2 fun a => (schedGTX_spec h13 c r l a).2.2
  have hcovE : ∀ᵐ ξ ∂c.P, ∀ a : ℕ, ξ ∈ (RootJ32.experiment c r).data.alive ((RootJ32.construction c).G r) l →
      cfRec c.s c.W c.ζ ξ ∈ goodX (rootPt r.1) c.s → (T : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ →
      ∀ᶠ j in atTop, ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) T ξ) <
        (ver₀ Ω c r l a).V j ξ :=
    ae_all_iff.2 fun a => GW2Sdt.hcov_death h13 Ω c r l a ⟨hx, hs⟩
  have hbundle : ∀ᵐ ξ ∂c.P, ξ ∈ A → (cfRec c.s c.W c.ζ ξ ∈ goodX (rootPt r.1) c.s ∧
      ∀ a, (T : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ) ∧
      (∀ a j : ℕ, ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) T ξ) < (ver₀ Ω c r l a).V j ξ →
        stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a) ((ver₀ Ω c r l a).V j) T
          ((ver₀ Ω c r l a).R j) ξ = refPre h13 Ω c r l ξ) ∧
      (GW2Bf.histStart c r l ξ < 2 + 1 / 8 ∧ (lamL l : ℝ) * (2 + 1 / 8 - GW2Bf.histStart c r l ξ) ≤ 2 + 1 / 8) ∧
      RootJ31.oldSuccess c r l ξ ∧ (∀ a, ξ ∈ schedGTX h13 c r l a) ∧ (∀ a, ∃ j, ENNReal.ofReal
        (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) T ξ) < (ver₀ Ω c r l a).V j ξ) := by
    filter_upwards [GW2Ru.ae_alive_goodEvent_scaled h13 GW2Sdq.gapFam c r, ae_slotRec_eq_ref h13 c r l GW2Sdq.gapFam
      ⟨hx, hs⟩, ae_startBand h13 GW2Sdq.gapFam c r l, hGTE, hcovE] with ξ h1 h2 h3 hGT hcov halive
    have halive32 := GW2Sdz.alive_scaled_subset GW2Sdq.gapFam Ω c r l halive
    obtain ⟨hcf, hcon⟩ := h1 l halive
    exact ⟨⟨hcf, hcon⟩, h2 halive, h3 halive, RootJ32.oldSuccess_of_alive c r l ξ halive32,
      fun a => (hGT a).2 hcf, fun a => (hcov a halive32 hcf (hcon a)).exists⟩
  have hall : ∀ᵐ ξ ∂c.P, (ξ ∈ A → (cfRec c.s c.W c.ζ ξ ∈ goodX (rootPt r.1) c.s ∧
      ∀ a, (T : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ) ∧
      (∀ a j : ℕ, ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) T ξ) < (ver₀ Ω c r l a).V j ξ →
        stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a) ((ver₀ Ω c r l a).V j) T
          ((ver₀ Ω c r l a).R j) ξ = refPre h13 Ω c r l ξ) ∧
      (GW2Bf.histStart c r l ξ < 2 + 1 / 8 ∧ (lamL l : ℝ) * (2 + 1 / 8 - GW2Bf.histStart c r l ξ) ≤ 2 + 1 / 8) ∧
      RootJ31.oldSuccess c r l ξ ∧ (∀ a, ξ ∈ schedGTX h13 c r l a) ∧ (∀ a, ∃ j, ENNReal.ofReal
        (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) T ξ) < (ver₀ Ω c r l a).V j ξ)) ∧
      (∀ a n : ℕ, ξ ∈ A → ∀ (f : NearCrossingFamily.{u} c.κ) (m j₀ : ℕ),
        ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) T ξ) < (ver₀ Ω c r l a).V j₀ ξ →
        famShapeB f = shapeD c r l ((instX h13 ver₀ ch Ω c r l a j₀ hx).srecX c r l (rootPt r.1) ξ) →
        (∀ i : Fin f.nL, f.xL i = posLD c r l ((instX h13 ver₀ ch Ω c r l a j₀ hx).srecX c r l (rootPt r.1) ξ) i) →
        (∀ j : Fin f.nR, f.xR j = posRD c r l ((instX h13 ver₀ ch Ω c r l a j₀ hx).srecX c r l (rootPt r.1) ξ) j) →
        GW2Sdf.PresentsO c.κ (upW ((RootJ31.candidateAngle c r a : ℝ) * chiC c.κ)
            (GW2Wm.baseWordX c.κ (GW2Sds.cfWordSrc c) (rootPt r.1) c.s (RootJ31.historyProgram c r l)
            ((entryList l).length + 1) (GW2Ru.length_historyProgram c r l)
            ((instX h13 ver₀ ch Ω c r l a j₀ hx).srecX c r l (rootPt r.1) ξ))) (scL r l) (GW2Sdf.flipOf l.length)
            f.xL (f.ρLs m) f.xR (f.ρRs m) →
        f.mL ≤ f.nL - 1 → f.mR ≤ f.nR - 1 →
        ∀ᶠ j in atTop, ξ ∈ goodVer h13 ver₀ ch c r l hx (exitN c r l) n a j) ∧
      (∀ a m : ℕ, ∀ (lam : ℝ) (τ : ℝ≥0∞) (t : ℝ≥0), 0 < lam →
        GW2Bf.histStart c r l ξ < 2 + 1 / 8 → lam * (2 + 1 / 8 - GW2Bf.histStart c r l ξ) ≤ 2 + 1 / 8 →
        τ ≤ (GW2Sdg.rootGain c r l a ξ : ℝ≥0∞) →
        τ ≤ (pkgVerF h13 h12 Ω c r l a).V m ξ - (GW2Sdg.rootHistCap c r l a ξ : ℝ≥0∞) →
        (t : ℝ≥0∞) < (4 : ℝ≥0∞) ^ r.2 * τ →
        2 + 1 / 8 < lam * ((-1 : ℝ) ^ l.length * ((2 : ℝ) ^ r.2 *
          (instX h13 (pkgVerF h13 h12) ch Ω c r l a m hx).drvX c (rootPt r.1) (t / (4 : ℝ≥0) ^ r.2) ξ)) →
        RootJ32.sourceSample c r l a ξ ∈ RootD25.reachSet) ∧
      (∀ a : ℕ, 0 < (RootJ31.sourceSample c r l a ξ).1 →
        physClockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a) T ξ =
          ((GW2Sdg.rootHistCap c r l a ξ : ℝ≥0) : ℝ≥0∞)) ∧
      (∀ a : ℕ, ξ ∈ schedGTX h13 c r l a → RootJ31.oldSuccess c r l ξ →
        ∃ Wc : ℝ≥0 → ℝ, IsCanonX c r l a (ver₀ Ω c r l a).R (ver₀ Ω c r l a).V ξ Wc) := by
    filter_upwards [hbundle, hgoodE, hreachE, hphysE, hcanE] with ξ h1 h2 h3 h4 h5
    exact ⟨h1, h2, h3, h4, h5⟩
  have hε : (0 : ℝ≥0∞) < ((k : ℝ≥0∞) + 1)⁻¹ / 2 :=
    ENNReal.div_pos (ENNReal.inv_ne_zero.2 (by simp)) (by norm_num)
  filter_upwards [ae_kernel_alive_gapFam h13 c r l, ae_nearStructBot_pkgNb h13 Ω c r l,
    ae_kernel_pkgNb_eq h13 h12 c r l hI, psiGood_spec h13 h12 c r l ⟨hx, hs⟩, hsrc k Ω c r l,
    Sec7.Aux122Disint.ae_ae_condExpKernel (sigma_le_ambient c r l) hall]
    with ω₀ hkA hbot hkNb hψ hsrcω hkall halive n
  -- the selected candidate and the family at `ω₀`
  set cand : ℕ → ℕ → ℕ := fun n m => (pkgF h13 h12 K₀ kSel k Ω c r).nearCandidate l ω₀ n m with hcand
  set f := (pkgF h13 h12 K₀ kSel k Ω c r).nearFamily l ω₀ with hf
  have hb := hbot halive
  have hlam0 : nearLam Ω c r l ω₀ ≠ 0 := nearLam_ne Ω c r l ω₀
  have hfsh := withNearSB_shape (pkgX h13 (pkgVerF h13 h12) ch (pkgKbF h13 h12 K₀)) nearLam (pkgNb h13 cwSrc)
    (kSel k) Ω c r l ω₀ hlam0 hb
  have hfpos := positionsOf_pad (withNearSB_positions (pkgX h13 (pkgVerF h13 h12) ch (pkgKbF h13 h12 K₀)) nearLam
    (pkgNb h13 cwSrc) (kSel k) Ω c r l ω₀ hlam0 hb)
  have hfgo := withNearSB_goLeft (pkgX h13 (pkgVerF h13 h12) ch (pkgKbF h13 h12 K₀)) nearLam (pkgNb h13 cwSrc)
    (kSel k) Ω c r l ω₀ hlam0 hb
  have hctrl := outer_ctrl_of_nearShapeBot (f := f) hfsh hb
  -- the two losses
  have hψ' := hψ (fun n m => cand n (m + 1)) n hε
  have hsrc' := hsrcω halive n hε
  rw [eventually_atTop] at hψ' hsrc'
  obtain ⟨M₁, hM₁⟩ := hψ'
  obtain ⟨M₂, hM₂⟩ := hsrc'
  refine eventually_atTop.2 ⟨M₁ + M₂ + 1, fun m hm => ?_⟩
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  set a := cand n (m' + 1) with ha
  set N : Set Ω := ({ξ | ∃ K, ξ ∈ goodFrom h13 ver₀ ch c r l hx (exitN c r l) n a K} \
      goodFrom h13 ver₀ ch c r l hx (exitN c r l) n a (psiGood h13 h12 Ω c r l a m')) ∪
    srcBad h13 h12 K₀ c r l n (m' + 1) a with hN
  refine ⟨N, ?_, ?_⟩
  · calc condExpKernel c.P (c.sigma r l) ω₀ N
        ≤ ((k : ℝ≥0∞) + 1)⁻¹ / 2 + ((k : ℝ≥0∞) + 1)⁻¹ / 2 :=
          (measure_union_le _ _).trans (add_le_add (hM₁ m' (by omega)) (hM₂ (m' + 1) (by omega)))
      _ = ((k : ℝ≥0∞) + 1)⁻¹ := ENNReal.add_halves _
  · filter_upwards [hkA halive, hkNb halive, hkall] with ξ hξA hξNb hξall hξN
    obtain ⟨hB, hgoodξ, hreachξ, hphysξ, hcanξ⟩ := hξall
    obtain ⟨⟨hcf, hcon⟩, href, hband, hold, hGTξ, hcov⟩ := hB hξA
    -- the reference record decodes the family
    have hrefNb : wordD c r l (augRec (stageEncRec c r l) (fun ω => refPre h13 Ω c r l ω) ξ) =
        pkgNb h13 cwSrc Ω c r l ω₀ := hξNb
    have hsh : famShapeB f = shapeD c r l (augRec (stageEncRec c r l) (fun ω => refPre h13 Ω c r l ω) ξ) := by
      unfold shapeD
      rw [hrefNb]
      exact hfsh
    have hL : ∀ i : Fin f.nL, f.xL i = posLD c r l (augRec (stageEncRec c r l) (fun ω => refPre h13 Ω c r l ω) ξ) i :=
      fun i => by unfold posLD; rw [hrefNb]; exact hfpos.1 i
    have hR : ∀ j : Fin f.nR, f.xR j = posRD c r l (augRec (stageEncRec c r l) (fun ω => refPre h13 Ω c r l ω) ξ) j :=
      fun j => by unfold posRD; rw [hrefNb]; exact hfpos.2 j
    -- some goodness of the candidate at `ξ`
    obtain ⟨j₀, hj₀⟩ := hcov a
    have hrec₀ : (instX h13 ver₀ ch Ω c r l a j₀ hx).srecX c r l (rootPt r.1) ξ =
        augRec (stageEncRec c r l) (fun ω => refPre h13 Ω c r l ω) ξ := by
      change augRec (stageEncRec c r l) (stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a)
        ((ver₀ Ω c r l a).V j₀) T ((ver₀ Ω c r l a).R j₀)) ξ = _
      simp only [augRec, href a j₀ hj₀]
    set sel := nearSelSB c r (nearRootScale r.2 (nearLam Ω c r l ω₀)) (GW2Sdf.flipOf l.length)
      (pkgNb h13 cwSrc Ω c r l ω₀)
      ((pkgX h13 (pkgVerF h13 h12) ch (pkgKbF h13 h12 K₀) Ω c r).nearFamily l ω₀) with hsel
    have hspec : GW2Sdf.PresentsO c.κ (upW ((RootJ31.angleEnumeration c r (sel.2 (m' + 1)) : ℝ) * chiC c.κ)
        (pkgNb h13 cwSrc Ω c r l ω₀)) (nearRootScale r.2 (nearLam Ω c r l ω₀)) (GW2Sdf.flipOf l.length) sel.1.xL
        (sel.1.ρLs (m' + 1)) sel.1.xR (sel.1.ρRs (m' + 1)) :=
      nearSelSB_spec c r (nearRootScale_ne_zero r.2 hlam0) (GW2Sdf.flipOf l.length) hb _ (m' + 1)
    have hca : (RootJ31.candidateAngle c r a : ℝ) = (RootJ31.angleEnumeration c r (sel.2 (m' + 1)) : ℝ) := by
      have e : a = Nat.pair (sel.2 (m' + 1)) (kSel k Ω c r l ω₀ n (m' + 1)) := rfl
      rw [e, GW2Sdy.candidateAngle_pair]
    have hpres : GW2Sdf.PresentsO c.κ (upW ((RootJ31.candidateAngle c r a : ℝ) * chiC c.κ)
        (GW2Wm.baseWordX c.κ (GW2Sds.cfWordSrc c) (rootPt r.1) c.s (RootJ31.historyProgram c r l)
        ((entryList l).length + 1) (GW2Ru.length_historyProgram c r l)
        ((instX h13 ver₀ ch Ω c r l a j₀ hx).srecX c r l (rootPt r.1) ξ))) (scL r l) (GW2Sdf.flipOf l.length)
        f.xL (f.ρLs (m' + 1)) f.xR (f.ρRs (m' + 1)) := by
      rw [hrec₀]
      change GW2Sdf.PresentsO c.κ (upW ((RootJ31.candidateAngle c r a : ℝ) * chiC c.κ)
        (wordD c r l (augRec (stageEncRec c r l) (fun ω => refPre h13 Ω c r l ω) ξ))) (scL r l)
        (GW2Sdf.flipOf l.length) sel.1.xL (sel.1.ρLs (m' + 1)) sel.1.xR (sel.1.ρRs (m' + 1))
      rw [hrefNb, hca]
      exact hspec
    have hev := hgoodξ a n hξA f (m' + 1) j₀ hj₀ (by rw [hrec₀]; exact hsh) (fun i => by rw [hrec₀]; exact hL i)
      (fun j => by rw [hrec₀]; exact hR j) hpres hctrl.1 hctrl.2
    obtain ⟨K, hK⟩ := eventually_atTop.1 hev
    have hgF : ξ ∈ goodFrom h13 ver₀ ch c r l hx (exitN c r l) n a K := by
      simp only [goodFrom, mem_iInter]
      exact fun j hj => hK j hj
    -- off the loss
    have hnot : ξ ∉ N := hξN
    rw [hN, mem_union, not_or] at hnot
    have hgF' : ξ ∈ goodFrom h13 ver₀ ch c r l hx (exitN c r l) n a (psiGood h13 h12 Ω c r l a m') := by
      by_contra h
      exact hnot.1 ⟨⟨K, hgF⟩, h⟩
    have hJ : psiGood h13 h12 Ω c r l a m' ≤ pkgPsi h13 (psiGoodFam h13 h12) Ω c r l a m' + m' :=
      (le_pkgPsi h13 (psiGoodFam h13 h12) Ω c r l a m').2.trans (Nat.le_add_right _ _)
    have hgoodJ : ξ ∈ goodVer h13 ver₀ ch c r l hx (exitN c r l) n a
        (pkgPsi h13 (psiGoodFam h13 h12) Ω c r l a m' + m') := by
      simp only [goodFrom, mem_iInter] at hgF'
      exact hgF' _ hJ
    have hslot : ξ ∈ slotGood h13 h12 c r l n (m' + 1) a := by
      simp only [slotGood, GoodRoot, hx, hs, and_self, ↓reduceDIte, Nat.add_sub_cancel]
      exact hgoodJ
    have hsrcξ : ¬ ((GW2Sdg.rootGain c r l a ξ : ℝ≥0∞) <
        ((pkgX h13 (pkgVerF h13 h12) ch (pkgKbF h13 h12 K₀) Ω c r).nearVar l n (m' + 1) a).stop ξ) :=
      fun h => hnot.2 ⟨hslot, h⟩
    exact slot_clauses h13 h12 K₀ c r l hx hs ξ n m' a f hgoodJ hcf (hcon a) (hGTξ a) (href a)
      (hcanξ a (hGTξ a) hold) hsh hL hR hsrcξ (hreachξ a (m' + 1)) hband (hphysξ a) hfgo

end InteractingSLE.Theorem14.GW2Bh
