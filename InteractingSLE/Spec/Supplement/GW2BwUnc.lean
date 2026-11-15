/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BwCmp
import InteractingSLE.Spec.Supplement.GW2NiUncTrans
import InteractingSLE.Spec.Supplement.GW2NiUncGlue

/-!
# The uncapped exit before the uncapped life (contact first)

Packet PROVE-GW2-BUF (round 20; `hsrc`). Almost surely on the alive event, for every angle index `i`, every canonical
driver `Wc` of the uncapped curve (`GW2Ni.IsCanonUX`), whenever the relative life `L_u` is at most the uncapped death
clock `d_u`, the near cell's exit on `Wc`'s stage path plus the stage start is below `L_u`. This is round 18's
`exit_add_lt_life_of_flow` with:

* the rightward family at the sample (`exists_nearSelection_bot` on `pkgNb`, any presented angle; the contact part
  reads only positions);
* the root word flowed through the prefix decoded by the candidate `angCand i 0` (`ae_inst_common`,
  `ae_slotRec_eq_ref`);
* the history part of `Wc` equal to that candidate's version (`agree_capped_unc` at the history time);
* round 17's contact clause for `Wc` (`gapVanishes_contactX_cond`, with the uncapped transience of
  `GW2Ni.uncRegStatement`); the death part is void with `d = ⊤`.

* **`ae_uncExit_lt_life`**.
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

variable (h13 : Exist.Theorem13Statement.{u}) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **The uncapped exit before the uncapped life**, when the contact comes first. -/
theorem ae_uncExit_lt_life (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q))
    (hg : GoodRoot c r) (hTO : GW2Sdx.HistOrdered c r l) (i : ℕ) :
    ∀ᵐ ξ ∂c.P, ξ ∈ ((GW2Sdz.J32S GW2Sdq.gapFam Ω c).experiment r).data.alive ((GW2Sdz.J32S GW2Sdq.gapFam Ω c).G r) l →
      ∀ Wc : ℝ≥0 → ℝ, GW2Ni.IsCanonUX c r l i ξ Wc →
      ENNReal.ofReal (contactLifeX (rootPt r.1) c.s (cfRec c.s c.W c.ζ ξ) (GW2Ni.uncW c r l i · ξ)
        (GW2Ni.uncTr c r l i ξ) (c.α ξ)) ≤ GW2Ni.uncDeathX c r l i ξ →
      ∀ n : ℕ, exitN c r l n (augRec (stageEncRec c r l) (fun ω => refPre h13 Ω c r l ω) ξ,
          stgDrv Wc (clockX (rootPt r.1) c.s c.W c.ζ (GW2Ni.uncW c r l i) (RootJ31.historyTime c r l) ξ).toNNReal) +
        ((clockX (rootPt r.1) c.s c.W c.ζ (GW2Ni.uncW c r l i) (RootJ31.historyTime c r l) ξ).toNNReal : ℝ≥0∞) <
        ENNReal.ofReal (contactLifeX (rootPt r.1) c.s (cfRec c.s c.W c.ζ ξ) (GW2Ni.uncW c r l i · ξ)
          (GW2Ni.uncTr c r l i ξ) (c.α ξ)) := by
  obtain ⟨hx, hs⟩ := hg
  set a₀ := GW2Ni.angCand i 0 with ha₀
  set ver₀ := schedVerXDeathFamily h13 with hver₀
  set T := RootJ31.historyTime c r l with hT
  have hverae : ∀ᵐ ξ ∂c.P, ∀ j, cfRec c.s c.W c.ζ ξ ∈ goodX (rootPt r.1) c.s →
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a₀) c.α ξ →
        ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a₀) t ξ) ≤ (ver₀ Ω c r l a₀).V j ξ →
        fwdHull (fun q : ℝ => (ver₀ Ω c r l a₀).R j q.toNNReal ξ)
            (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a₀) t ξ) =
          hullX (rootPt r.1) c.s c.W c.ζ (schedW c r l a₀) t ξ :=
    ae_all_iff.2 fun j => ((ver₀ Ω c r l a₀).isA hx j).1.1.2.2.2.2.2.2.mono fun ξ h hg => (h hg).2.2
  filter_upwards [ae_inst_common h13 GW2Sdq.gapFam c r l a₀ ⟨hx, hs⟩ ver₀ c.κ (GW2Sds.cfWordSrc c),
    ae_slotRec_eq_ref h13 c r l GW2Sdq.gapFam ⟨hx, hs⟩, GW2Sdt.hcov_death h13 Ω c r l a₀ ⟨hx, hs⟩,
    GW2Ni.uncRegStatement h13 Ω c r l i hTO, GW2Ni.uncAgreeStatement h13 Ω c r l i, hverae,
    ae_nearStructBot_pkgNb h13 Ω c r l] with ξ hcomm href hcov hreg hUA hvξ hbotξ halive Wc hcan hLd n
  have halive32 := GW2Sdz.alive_scaled_subset GW2Sdq.gapFam Ω c r l halive
  obtain ⟨hξ, hold, -, hcf, hTc, hS, -, hbase⟩ := hcomm halive
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
  obtain ⟨j₀, hj₀⟩ := (hcov halive32 hcf hTc).exists
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
  -- the reference record is the slot's record, and its base word is the flowed root word
  have hy : augRec (stageEncRec c r l) (fun ω => refPre h13 Ω c r l ω) ξ =
      augRec (stageEncRec c r l) (stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r l a₀) (schedGTX h13 c r l a₀)
        ((ver₀ Ω c r l a₀).V j₀) T ((ver₀ Ω c r l a₀).R j₀)) ξ := by
    simp only [augRec]
    exact congrArg (fun p => pairEnc (stageEncRec c r l ξ, p)) (href halive a₀ j₀ hj₀).symm
  set y := augRec (stageEncRec c r l) (fun ω => refPre h13 Ω c r l ω) ξ with hydef
  have hword : wordD c r l y = GW2JDetR5.stageWord (κ := c.κ) (rootWordX c.κ (GW2Sds.cfWordSrc c) (rootPt r.1) c.s)
      (progAngle (RootJ31.historyProgram c r l)) N
      (pastOf (cfRec c.s c.W c.ζ ξ) (fun u => (ver₀ Ω c r l a₀).R j₀ u ξ) b N) := by
    unfold wordD
    rw [hy]
    exact hbase j₀
  -- the rightward family at the sample
  have hb := hbotξ halive
  have hs0 : nearRootScale r.2 (nearLam Ω c r l ξ) ≠ 0 := nearRootScale_ne_zero r.2 (nearLam_ne Ω c r l ξ)
  obtain ⟨f, ι, hfsh, hfpos, hfpres⟩ := exists_nearSelection_bot.{u} c r hs0 (GW2Sdf.flipOf l.length) hb
  have hpkg : pkgNb h13 cwSrc Ω c r l ξ = wordD c r l y := rfl
  have hsh : famShapeB f = shapeD c r l y := by
    unfold shapeD
    rw [← hpkg]
    exact hfsh
  have hpos' := positionsOf_pad hfpos
  have hL : ∀ i' : Fin f.nL, f.xL i' = posLD c r l y i' := fun i' => by
    unfold posLD
    rw [← hpkg]
    exact hpos'.1 i'
  have hR : ∀ j : Fin f.nR, f.xR j = posRD c r l y j := fun j => by
    unfold posRD
    rw [← hpkg]
    exact hpos'.2 j
  have hctrl := outer_ctrl_of_nearShapeBot (f := f) hfsh hb
  have hP : GW2Sdf.PresentsO c.κ (upW ((RootJ31.angleEnumeration c r (ι 0) : ℝ) * chiC c.κ)
      (GW2JDetR5.stageWord (κ := c.κ) (rootWordX c.κ (GW2Sds.cfWordSrc c) (rootPt r.1) c.s)
        (progAngle (RootJ31.historyProgram c r l)) N
        (pastOf (cfRec c.s c.W c.ζ ξ) (fun u => (ver₀ Ω c r l a₀).R j₀ u ξ) b N))) (scL r l)
      (GW2Sdf.flipOf l.length) f.xL (f.ρLs 0) f.xR (f.ρRs 0) := by
    rw [← hword, ← hpkg]
    exact hfpres 0
  -- the history part of `Wc` is the slot's version
  have hdu : ENNReal.ofReal clT < GW2Ni.uncDeathX c r l i ξ :=
    lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt hclT0 hSL)).2 hSL) hLd
  have hag : ∀ q : ℝ≥0, q ≤ b N → (ver₀ Ω c r l a₀).R j₀ q ξ = Wc q := fun q hq => by
    have hj₀' : ENNReal.ofReal clT ≤ (ver₀ Ω c r l a₀).V j₀ ξ := by rw [← hclTa]; exact hj₀.le
    have hq' : (q : ℝ) ≤ clT := by
      rw [hbN'] at hq
      exact (Real.le_toNNReal_iff_coe_le hclT0).1 hq
    exact agree_capped_unc c.W c.ζ ξ hα hW hW0 hζ hs hx harc hwc₀ hw0₀ hγ₀ hw hγ
      (((ver₀ Ω c r l a₀).isA hx j₀).1.1.2.1 ξ) (((ver₀ Ω c r l a₀).isA hx j₀).1.1.2.2.1 ξ) (hvξ j₀ hcf)
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
  have hcon : ENNReal.ofReal L ≤ ⊤ →
      GapVanishes (rp Wc) (labelL (rdrv (cfRec c.s c.W c.ζ ξ)) (rtime (cfRec c.s c.W c.ζ ξ)) 0 -
        GW2Rz.baseRead (rootPt r.1) c.s (cfRec c.s c.W c.ζ ξ)) L ∨
      GapVanishes (fun q => -rp Wc q) (-(labelR (rdrv (cfRec c.s c.W c.ζ ξ)) (rtime (cfRec c.s c.W c.ζ ξ)) 0 -
        GW2Rz.baseRead (rootPt r.1) c.s (cfRec c.s c.W c.ζ ξ))) L := fun _ => by
    rcases gapVanishes_contactX_cond c.W c.ζ ξ hα hW hW0 hζ hs hx harc huc hu0 huγ hutr hWc hWc0 hη hK ⟨M, hM⟩
      hLζ hLd with ⟨-, hjR, hgap⟩ | ⟨-, hjL, hgap⟩
    · exact Or.inl (hgap _ (by rw [hxR_eq]; exact hjR))
    · exact Or.inr (hgap _ (by rw [hxL_eq]; exact hjL))
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
    (posRD c r l) hsh hL hR (c2L_pos r l) (sqrt_scL r l) (GW2Sdf.flipOf l.length) 0
    (rootWordX c.κ (GW2Sds.cfWordSrc c) (rootPt r.1) c.s) (progAngle (RootJ31.historyProgram c r l))
    (cfRec c.s c.W c.ζ ξ) (((ver₀ Ω c r l a₀).isA hx j₀).1.1.2.1 ξ) (((ver₀ Ω c r l a₀).isA hx j₀).1.1.2.2.1 ξ)
    hbmono hb0 N hP hctrl.1 hctrl.2 hcapP hWc hag h0 (by rw [hxR_eq]; exact hxR_pos.le)
    (by rw [hxL_eq]; exact hxL_neg.le) hjR₀ hjL₀ hSL' hcon (fun h => absurd h not_top_lt)
  rw [min_top_right, hbN'] at hfl
  exact hfl

end InteractingSLE.Theorem14.GW2Bh
