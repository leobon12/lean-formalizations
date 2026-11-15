/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BxThr
import InteractingSLE.Spec.Supplement.GW2BxRef

/-!
# The uncapped exit before the uncapped life and death (any presenting family)

Packet PROVE-GW2-BUF (round 21; D75). Almost surely on the alive event, for every angle index `i`, every canonical
driver `Wc` of the uncapped curve (`GW2Ni.IsCanonUX`) and every near family `f` whose shape and positions are those
decoded from the reference record and which presents the reference word raised by the angle `θ_i` (outer labels
controlled): the near cell's exit on `Wc`'s stage path plus the stage start is below `min (L_u, d_u)`.

This is round 20's `ae_uncExit_lt_life` (contact first, `L_u ≤ d_u`) with the death part: when `d_u < L_u` the
uncapped piece dies before the contact, and the threshold at the death holds for `Wc` (`thr_unc_death`, from the
base family's `DeathThrXStatementS3`). The reference record is the base family's (`GW2Rl.refPreV h13 ver₀`).

* **`ae_uncExit_lt_min`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC fwdHull)

universe u

namespace InteractingSLE.Theorem14.GW2Bh

open Exist Staged StagedLaw Restart Supp8 Supp8.GB6 GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootN4 GW2Rz
  GW2Rd GW2Rv GW2Wm GW2Schedule Sec5.Prop513Schedule GW2JDetR11 GW2Sdh GW2Sde GW2Sdy GW2Sdo

variable (h13 : Exist.Theorem13Statement.{u}) (ver₀ : SchedVerXFamily.{u}) (ch : SchedChoiceFamily.{u})
  {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **The uncapped exit before the uncapped life and death**, for every presenting near family. -/
theorem ae_uncExit_lt_min (hcov : Wire.T14Rk.VerCovers ver₀) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (hg : GoodRoot c r) (hTO : GW2Sdx.HistOrdered c r l)
    (hcaps : ∀ a : ℕ, ∀ᵐ ω ∂c.P, cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s → RootJ31.oldSuccess c r l ω →
      0 < candLife c r l a ω → ∀ n, (ver₀ Ω c r l a).V n ω < deathClockX c r l a ω)
    (hβ : ∀ (a : ℕ) (y : RecData), (ch Ω c r l a).β y = upW ((RootJ31.candidateAngle c r a : ℝ) * chiC c.κ)
      (GW2Wm.baseWordX c.κ (GW2Sds.cfWordSrc c) (rootPt r.1) c.s (RootJ31.historyProgram c r l)
        ((entryList l).length + 1) (GW2Ru.length_historyProgram c r l) y))
    (hdeath : DeathThrXStatementS3 h13 ver₀ ch)
    (hroot : rootPt r.1 = 0 ∨ rootPt r.1 ∈ lowerArcRoots c.κ c.b c.jumps)
    (hord' : (RootJ31.historyProgram c r l).Pairwise (fun p q => p.2 < q.2)) (i : ℕ) :
    ∀ᵐ ξ ∂c.P, ξ ∈ ((GW2Sdz.J32S GW2Sdq.gapFam Ω c).experiment r).data.alive ((GW2Sdz.J32S GW2Sdq.gapFam Ω c).G r) l →
      ∀ Wc : ℝ≥0 → ℝ, GW2Ni.IsCanonUX c r l i ξ Wc → ∀ (n : ℕ) (f : NearCrossingFamily.{u} c.κ) (m : ℕ),
      famShapeB f = shapeD c r l (augRec (stageEncRec c r l) (fun ω => GW2Rl.refPreV h13 ver₀ Ω c r l ω) ξ) →
      (∀ i' : Fin f.nL, f.xL i' =
        posLD c r l (augRec (stageEncRec c r l) (fun ω => GW2Rl.refPreV h13 ver₀ Ω c r l ω) ξ) i') →
      (∀ j : Fin f.nR, f.xR j =
        posRD c r l (augRec (stageEncRec c r l) (fun ω => GW2Rl.refPreV h13 ver₀ Ω c r l ω) ξ) j) →
      GW2Sdf.PresentsO c.κ (upW ((RootJ31.angleEnumeration c r i : ℝ) * chiC c.κ)
          (wordD c r l (augRec (stageEncRec c r l) (fun ω => GW2Rl.refPreV h13 ver₀ Ω c r l ω) ξ))) (scL r l)
          (GW2Sdf.flipOf l.length) f.xL (f.ρLs m) f.xR (f.ρRs m) →
      f.mL ≤ f.nL - 1 → f.mR ≤ f.nR - 1 →
      exitN c r l n (augRec (stageEncRec c r l) (fun ω => GW2Rl.refPreV h13 ver₀ Ω c r l ω) ξ,
          stgDrv Wc (clockX (rootPt r.1) c.s c.W c.ζ (GW2Ni.uncW c r l i) (RootJ31.historyTime c r l) ξ).toNNReal) +
        ((clockX (rootPt r.1) c.s c.W c.ζ (GW2Ni.uncW c r l i) (RootJ31.historyTime c r l) ξ).toNNReal : ℝ≥0∞) <
        min (ENNReal.ofReal (contactLifeX (rootPt r.1) c.s (cfRec c.s c.W c.ζ ξ) (GW2Ni.uncW c r l i · ξ)
          (GW2Ni.uncTr c r l i ξ) (c.α ξ))) (GW2Ni.uncDeathX c r l i ξ) := by
  obtain ⟨hx, hs⟩ := hg
  set a₀ := GW2Ni.angCand i 0 with ha₀
  set T := RootJ31.historyTime c r l with hT
  have hverae : ∀ᵐ ξ ∂c.P, ∀ a j, cfRec c.s c.W c.ζ ξ ∈ goodX (rootPt r.1) c.s →
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ →
        ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ξ) ≤ (ver₀ Ω c r l a).V j ξ →
        fwdHull (fun q : ℝ => (ver₀ Ω c r l a).R j q.toNNReal ξ)
            (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ξ) =
          hullX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ξ :=
    ae_all_iff.2 fun a => ae_all_iff.2 fun j =>
      ((ver₀ Ω c r l a).isA hx j).1.1.2.2.2.2.2.2.mono fun ξ h hgx => (h hgx).2.2
  filter_upwards [ae_all_iff.2 fun a => ae_inst_common h13 GW2Sdq.gapFam c r l a ⟨hx, hs⟩ ver₀ c.κ
      (GW2Sds.cfWordSrc c),
    ae_slotRec_eq_refV h13 c r l ver₀ GW2Sdq.gapFam ⟨hx, hs⟩, ae_all_iff.2 fun a => hcov Ω c r l a ⟨hx, hs⟩,
    GW2Ni.uncRegStatement h13 Ω c r l i hTO, GW2Ni.uncAgreeStatement h13 Ω c r l i, hverae, ae_all_iff.2 hcaps,
    ae_all_iff.2 fun a => hdeath Ω c r l a ⟨hx, hs⟩ hroot hord', GW2Sdt.ae_candLife_pos h13 c r l a₀]
    with ξ hcomm href hcov hreg hUA hvξ hcapsξ hdeathξ hlifepos halive Wc hcan n f m hsh hL hR hPi hmL hmR
  have halive32 := GW2Sdz.alive_scaled_subset GW2Sdq.gapFam Ω c r l halive
  obtain ⟨hξ, hold, -, hcf, hTc, hS, -, hbase⟩ := hcomm a₀ halive
  have hGT : ∀ a, ξ ∈ schedGTX h13 c r l a := fun a => (hcomm a halive).1
  have hTcA : ∀ a, (T : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ :=
    fun a => (hcomm a halive).2.2.2.2.1
  obtain ⟨-, ⟨hα, hW, hW0, hζ⟩, harc, -, -⟩ := (schedGTX_spec h13 c r l a₀).1 ξ hξ
  obtain ⟨⟨hwc₀, hw0₀, hγ₀⟩, -, -, -, -⟩ := (schedGTX_spec h13 c r l a₀).1 ξ hξ
  obtain ⟨huc, hu0, huγ, hutr⟩ := hreg
  obtain ⟨hWc, hWc0, hK, ⟨ζc, ηc, hη, hLζ⟩, M, hM⟩ := hcan
  -- the candidate `a₀` explores the uncapped curve up to its cap
  have hang : RootJ31.candidateAngle c r a₀ = RootJ31.angleEnumeration c r i := GW2Ni.candidateAngle_angCand c r i 0
  have hcap0 : 0 < RootJ31.candidateCap c r a₀ := by
    rw [GW2Ni.candidateCap_angCand]
    exact c.hQpos _ (RootJ31.timeEnumeration c r 0).2
  have hw : ∀ u ≤ T + RootJ31.candidateCap c r a₀, schedW c r l a₀ u ξ = GW2Ni.uncW c r l i u ξ :=
    fun u hu => (hUA a₀ hang u hu).1
  have hγ : ∀ u ≤ T + RootJ31.candidateCap c r a₀, schedTr c r l a₀ ξ u = GW2Ni.uncTr c r l i ξ u :=
    fun u hu => (hUA a₀ hang u hu).2
  have hTt₁ : T < T + RootJ31.candidateCap c r a₀ := lt_add_of_pos_right T hcap0
  have hTcu : (T : ℝ≥0∞) < contactX (rootPt r.1) c.s (GW2Ni.uncTr c r l i) c.α ξ :=
    lt_contactX_of_agree hγ hTt₁ hTc
  -- the uncapped clock
  obtain ⟨ha0, hsm, -⟩ := GW2Rz.clock_props c.W c.ζ ξ hα hW hW0 hζ hs hx harc huc hu0 huγ
  set L := contactLifeX (rootPt r.1) c.s (cfRec c.s c.W c.ζ ξ) (GW2Ni.uncW c r l i · ξ) (GW2Ni.uncTr c r l i ξ)
    (c.α ξ) with hLdef
  set clT := clockX (rootPt r.1) c.s c.W c.ζ (GW2Ni.uncW c r l i) T ξ with hclT
  have hclT0 : 0 ≤ clT := by
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ T) with h | h
    · rw [hclT, ← h]; exact ha0.ge
    · have h0 : ((0 : ℝ≥0) : ℝ≥0∞) < contactX (rootPt r.1) c.s (GW2Ni.uncTr c r l i) c.α ξ :=
        lt_of_le_of_lt (by exact_mod_cast zero_le) hTcu
      exact le_of_lt (lt_of_eq_of_lt ha0.symm (hsm h0 hTcu h))
  have hSL : clT < L := clock_lt_life hsm hM hTcu
  have hclTa : clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a₀) T ξ = clT :=
    clockX_eq_of_agree fun u hu => hw u (hu.trans hTt₁.le)
  -- a slot of `a₀` passing the clock
  obtain ⟨j₀, hj₀⟩ := (hcov a₀ halive32 hcf hTc).exists
  have hS₀ := hS j₀ hj₀
  set N := (entryList l).length + 1 with hNdef
  set b := trueBdX (rootPt r.1) c.s c.W c.ζ (schedW c r l a₀) (schedGTX h13 c r l a₀) ((ver₀ Ω c r l a₀).V j₀)
    (RootJ31.historyProgram c r l) N T ξ with hbdef
  have hbN : b N = (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a₀) T ξ).toNNReal := by
    rw [hbdef, trueBdX_of_le _ _ le_rfl (Nat.succ_ne_zero _)]
    exact hS₀
  have hbN' : b N = clT.toNNReal := by rw [hbN, hclTa]
  have hTj : ∀ k < N, schedTime 0 (RootJ31.historyProgram c r l) k ≤ T := fun k hk =>
    GW2Ru.schedTime_le_historyTime c r l hTO (by rw [GW2Ru.length_historyProgram]; exact hk.le)
  have hbmono : Monotone b := monotone_trueBdX (schedGTX_spec h13 c r l a₀).1 hs hx ((ver₀ Ω c r l a₀).fin j₀ ξ)
    hTO (GW2Ru.length_historyProgram c r l) hTj
  have hb0 : b 0 = 0 := trueBdX_zero _ _ _
  -- the reference record is every passing slot's record, and its base word is the flowed root word
  have hyj : ∀ a j : ℕ, ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) T ξ) <
      (ver₀ Ω c r l a).V j ξ →
      augRec (stageEncRec c r l) (fun ω => GW2Rl.refPreV h13 ver₀ Ω c r l ω) ξ =
        (instX h13 ver₀ ch Ω c r l a j hx).srecX c r l (rootPt r.1) ξ := by
    intro a j hj
    change _ = augRec (stageEncRec c r l) (stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r l a)
      (schedGTX h13 c r l a) ((ver₀ Ω c r l a).V j) T ((ver₀ Ω c r l a).R j)) ξ
    simp only [augRec]
    exact congrArg (fun p => pairEnc (stageEncRec c r l ξ, p)) (href halive a j hj).symm
  set y := augRec (stageEncRec c r l) (fun ω => GW2Rl.refPreV h13 ver₀ Ω c r l ω) ξ with hydef
  have hword : wordD c r l y = GW2JDetR5.stageWord (κ := c.κ) (rootWordX c.κ (GW2Sds.cfWordSrc c) (rootPt r.1) c.s)
      (progAngle (RootJ31.historyProgram c r l)) N
      (pastOf (cfRec c.s c.W c.ζ ξ) (fun u => (ver₀ Ω c r l a₀).R j₀ u ξ) b N) := by
    unfold wordD
    rw [hyj a₀ j₀ hj₀]
    exact hbase j₀
  have hP : GW2Sdf.PresentsO c.κ (upW ((RootJ31.angleEnumeration c r i : ℝ) * chiC c.κ)
      (GW2JDetR5.stageWord (κ := c.κ) (rootWordX c.κ (GW2Sds.cfWordSrc c) (rootPt r.1) c.s)
        (progAngle (RootJ31.historyProgram c r l)) N
        (pastOf (cfRec c.s c.W c.ζ ξ) (fun u => (ver₀ Ω c r l a₀).R j₀ u ξ) b N))) (scL r l)
      (GW2Sdf.flipOf l.length) f.xL (f.ρLs m) f.xR (f.ρRs m) := by
    rw [← hword]
    exact hPi
  -- the history part of `Wc` is the slot's version
  have hag : ∀ q : ℝ≥0, q ≤ b N → (ver₀ Ω c r l a₀).R j₀ q ξ = Wc q := fun q hq => by
    have hj₀' : ENNReal.ofReal clT ≤ (ver₀ Ω c r l a₀).V j₀ ξ := by rw [← hclTa]; exact hj₀.le
    have hq' : (q : ℝ) ≤ clT := by
      rw [hbN'] at hq
      exact (Real.le_toNNReal_iff_coe_le hclT0).1 hq
    have hdu : ENNReal.ofReal clT < GW2Ni.uncDeathX c r l i ξ := by
      -- the history time is before the uncapped death
      unfold GW2Ni.uncDeathX
      split_ifs with hd
      · have hlt : T < T + (GW2Ni.uncLife c r l i ξ).toNNReal := by
          refine lt_add_of_pos_right T (ENNReal.toNNReal_pos ?_ hd.1)
          exact ne_of_gt (hlifepos halive32)
        exact (ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt hclT0 (hsm hTcu hd.2 hlt))).2 (hsm hTcu hd.2 hlt)
      · exact ENNReal.ofReal_lt_top
    exact agree_capped_unc c.W c.ζ ξ hα hW hW0 hζ hs hx harc hwc₀ hw0₀ hγ₀ hw hγ
      (((ver₀ Ω c r l a₀).isA hx j₀).1.1.2.1 ξ) (((ver₀ Ω c r l a₀).isA hx j₀).1.1.2.2.1 ξ) (hvξ a₀ j₀ hcf)
      hWc hWc0 hK hTt₁ hTcu hj₀' hdu q hq'
  -- root bounds and junctions
  obtain ⟨hxR_eq, hxL_eq, hxR_pos, hxL_neg⟩ :=
    root_bounds_eq_junctions c.W c.ζ ξ hα hW hW0 hζ hx harc huc hu0 huγ hcf.1
  have hjR₀ : ∀ z ∈ (rootWordX c.κ (GW2Sds.cfWordSrc c) (rootPt r.1) c.s (cfRec c.s c.W c.ζ ξ)).jumps, 0 < z →
      z ≤ labelL (rdrv (cfRec c.s c.W c.ζ ξ)) (rtime (cfRec c.s c.W c.ζ ξ)) 0 -
        GW2Rz.baseRead (rootPt r.1) c.s (cfRec c.s c.W c.ζ ξ) :=
    fun z hz _ => (rootWordX_label_bounds hcf.1.2.2.1 hcf.1.2.2.2 hz).2
  have hjL₀ : ∀ z ∈ (rootWordX c.κ (GW2Sds.cfWordSrc c) (rootPt r.1) c.s (cfRec c.s c.W c.ζ ξ)).jumps, z < 0 →
      labelR (rdrv (cfRec c.s c.W c.ζ ξ)) (rtime (cfRec c.s c.W c.ζ ξ)) 0 -
        GW2Rz.baseRead (rootPt r.1) c.s (cfRec c.s c.W c.ζ ξ) ≤ z :=
    fun z hz _ => (rootWordX_label_bounds hcf.1.2.2.1 hcf.1.2.2.2 hz).1
  -- the contact clause of the uncapped curve
  have hcon : ENNReal.ofReal L ≤ GW2Ni.uncDeathX c r l i ξ →
      GapVanishes (rp Wc) (labelL (rdrv (cfRec c.s c.W c.ζ ξ)) (rtime (cfRec c.s c.W c.ζ ξ)) 0 -
        GW2Rz.baseRead (rootPt r.1) c.s (cfRec c.s c.W c.ζ ξ)) L ∨
      GapVanishes (fun q => -rp Wc q) (-(labelR (rdrv (cfRec c.s c.W c.ζ ξ)) (rtime (cfRec c.s c.W c.ζ ξ)) 0 -
        GW2Rz.baseRead (rootPt r.1) c.s (cfRec c.s c.W c.ζ ξ))) L := fun hLd => by
    rcases gapVanishes_contactX_cond c.W c.ζ ξ hα hW hW0 hζ hs hx harc huc hu0 huγ hutr hWc hWc0 hη hK ⟨M, hM⟩
      hLζ hLd with ⟨-, hjR, hgap⟩ | ⟨-, hjL, hgap⟩
    · exact Or.inl (hgap _ (by rw [hxR_eq]; exact hjR))
    · exact Or.inr (hgap _ (by rw [hxL_eq]; exact hjL))
  -- the threshold at the uncapped death
  have hdeath' : GW2Ni.uncDeathX c r l i ξ < ENNReal.ofReal L → ∃ u : ℝ≥0,
      ((b N : ℝ≥0) : ℝ≥0∞) + u = GW2Ni.uncDeathX c r l i ξ ∧
      StageThreshold c.κ (upW ((RootJ31.angleEnumeration c r i : ℝ) * chiC c.κ)
        (GW2JDetR5.stageWord (κ := c.κ) (rootWordX c.κ (GW2Sds.cfWordSrc c) (rootPt r.1) c.s)
          (progAngle (RootJ31.historyProgram c r l)) N
          (pastOf (cfRec c.s c.W c.ζ ξ) (fun u => (ver₀ Ω c r l a₀).R j₀ u ξ) b N))) (stgDrv Wc (b N)) u := by
    intro hdL
    obtain ⟨a, j, u, hanga, hj, hu, hthr⟩ := thr_unc_death h13 ver₀ ch c r l hx hs ξ i hα hW hW0 hζ harc huc hu0 huγ
      hWc hWc0 hK (hUA) hGT hTcA (fun a => (hcov a halive32 hcf (hTcA a)).exists)
      (fun a => hcapsξ a hcf hold) (fun a j => hvξ a j hcf)
      (fun a => hdeathξ a (hGT a) hold) (hdL.trans ENNReal.ofReal_lt_top)
    refine ⟨u, by rw [hbN']; exact hu, ?_⟩
    rw [hβ a, ← hyj a j hj, hanga] at hthr
    rw [hbN']
    change StageThreshold c.κ (upW ((RootJ31.angleEnumeration c r i : ℝ) * chiC c.κ) (wordD c r l y))
      (stgDrv Wc clT.toNNReal) u at hthr
    rw [hword] at hthr
    exact hthr
  -- the initial state is in the cell
  obtain ⟨-, hin0⟩ := cellOf_spec f n hsh hL hR
  have hlabL : ∀ i', f.xL i' ≤ 0 := fun i' => by
    by_cases h : f.xL i' = 0
    · exact h.le
    · exact (f.hxL i' h).trans (neg_nonpos.2 f.hη.le)
  have hlabR : ∀ j, 0 ≤ f.xR j := fun j => by
    by_cases h : f.xR j = 0
    · exact h.ge
    · exact f.hη.le.trans (f.hxR j h)
  have h0 : GW2Sdg.imgState f.xL f.xR (scaledPath (c2L r l ^ 2) (GW2Sdy.nearSign (GW2Sdf.flipOf l.length) * c2L r l)
      (stgDrv Wc (b N))) 0 ∈ cellBuf (famShapeB f, (cellOf n (shapeD c r l) (posLD c r l) (posRD c r l) y).2.1,
        (cellOf n (shapeD c r l) (posLD c r l) (posRD c r l) y).2.2) := by
    rw [imgState_zero f.xL f.xR hlabL hlabR (by simp [scaledPath, stgDrv_zero])]
    exact hin0
  have hcapP : (0 : ℝ≥0) < ((n : ℝ≥0) + 1) / c2L r l ^ 2 := div_pos (by positivity) (pow_pos (c2L_pos r l) 2)
  have hSL' : ((b N : ℝ≥0) : ℝ) < L := by rw [hbN', Real.coe_toNNReal _ hclT0]; exact hSL
  have hfl := exit_add_lt_life_of_flow f (cellOf n (shapeD c r l) (posLD c r l) (posRD c r l)) (posLD c r l)
    (posRD c r l) hsh hL hR (c2L_pos r l) (sqrt_scL r l) (GW2Sdf.flipOf l.length) m
    (rootWordX c.κ (GW2Sds.cfWordSrc c) (rootPt r.1) c.s) (progAngle (RootJ31.historyProgram c r l))
    (cfRec c.s c.W c.ζ ξ) (((ver₀ Ω c r l a₀).isA hx j₀).1.1.2.1 ξ) (((ver₀ Ω c r l a₀).isA hx j₀).1.1.2.2.1 ξ)
    hbmono hb0 N hP hmL hmR hcapP hWc hag h0 (by rw [hxR_eq]; exact hxR_pos.le)
    (by rw [hxL_eq]; exact hxL_neg.le) hjR₀ hjL₀ hSL' hcon hdeath'
  rw [hbN'] at hfl
  exact hfl

end InteractingSLE.Theorem14.GW2Bh
