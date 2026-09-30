import QuantumZipper.Proofs.Zipper.LocLenR6wDens
import QuantumZipper.Proofs.Zipper.LocLenR6fReg
import QuantumZipper.Proofs.Zipper.LocLenPairCfgMain
import QuantumZipper.Proofs.Zipper.LogShiftW2Cap
import QuantumZipper.Proofs.Zipper.LswZMain

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# D75, task R6w (2): `LogShiftLenWeightArcStmt` (proved from `YMergeOffTipStmt`)

Open-arc port of `F1.logShiftLenWeightStmt_of_w2` (LogShiftW2Main.lean:119). Every open-arc
length of the target is read at one stage `T` (the `Γ⁰` field cocycle
`RegUnif.capCocycleRegAllStmt_holds` and the `Z` field cocycle `lswZCocycleRegStmt_holds`, with
`arcLen_congr`): the new piece `η(r, T)` has, at stage `T`, the open arcs `(a_T(r), 0)` and
`(0, b_T(r))` (`lswPos`, `lswPosStmt_holds`). By the open-arc stage density
(`ae_stageDensArc`, rule (5.1) off the root images) the `Z` measure on these arcs is
`e^{γφ(E_T ·)/2} ν_Y`, and `lsw2_stage` transports it to capacity time with the weight
`w(r) = e^{γ φ(η(r))/2}`. The `Γ⁰` open-arc cocycle (R6a) and regularity
(`lenRegCfgArc_holds`) supply the representing measures' finiteness and atomlessness.
Sources: Sheffield arXiv:1012.4797 §1.4, §5.4 pp. 71–72, rule (5.1); B-P arXiv:2404.16642
Def 6.41 p. 229 (only the open arcs are read). Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace LocLen

open F1

/-- An atomless measure restricted to a set containing `(a,b)`, on `[a,b]` (deterministic). -/
theorem restrict_Icc_eq_Ioo {ν : Measure ℝ} (hat : ∀ x, ν {x} = 0) {V : Set ℝ}
    {a b : ℝ} (h : Ioo a b ⊆ V) :
    (ν.restrict V) (Icc a b) = ν (Ioo a b) := by
  rw [Measure.restrict_apply measurableSet_Icc]
  refine le_antisymm ?_ (measure_mono fun x hx => ⟨Ioo_subset_Icc_self hx, h hx⟩)
  calc ν (Icc a b ∩ V) ≤ ν (Icc a b) := measure_mono inter_subset_left
    _ = ν (Ioo a b) := measure_Icc_eq_Ioo_of_noAtoms (hat a) (hat b)

/-- **`LogShiftLenWeightArcStmt` from the offset merging input** (no tip input). -/
theorem logShiftLenWeightArc_of_yMergeOffTip (hYO : WedgeUnzip.YMergeOffTipStmt) :
    LogShiftLenWeightArcStmt := by
  intro κ hκ hκ4 Ω _ P _ B X G Z hB hX hI hGZ
  obtain ⟨δt, -, htrace⟩ := RS.ae_sleTrace_good hB hκ (by linarith)
  have hCC : ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ u s : ℝ, 0 ≤ u → 0 ≤ s → u + s ≤ (n : ℝ) + 1 →
      RegEq (zipCapDown (Real.sqrt κ) s (zipCapDown (Real.sqrt κ) u (B2.cfg κ B X ω))).1
        (zipCapDown (Real.sqrt κ) (u + s) (B2.cfg κ B X ω)).1 := by
    rw [ae_all_iff]
    intro n
    filter_upwards [RegUnif.capCocycleRegAllStmt_holds (κ := κ) hB hX hI ((n : ℝ) + 1)
      (by positivity)] with ω h u s hu hs hus
    exact (h u s hu hs hus).1
  filter_upwards [lenPairCocycleCfgArc_holds κ P B X hκ hκ4 hB hX hI,
    lenRegCfgArc_holds κ P B X hκ hκ4 hB hX hI, lswPosStmt_holds κ hκ hκ4 P B hB,
    lswZCocycleRegStmt_holds κ hκ hκ4 P B X G Z hB hX hI hGZ,
    ae_stageDensArc hYO hκ hκ4 hB hX hI hGZ, hGZ, hCC,
    WedgeUnzip.globalCaraStmt_holds κ hκ hκ4 P B hB,
    hB.eval_zero_ae_eq_zero, htrace] with ω hPω hRω hPosω hZCω hDω hGω hCCω hCω h0 htrω
  obtain ⟨hLf, c1, -, c2, -⟩ := hRω
  set γ := Real.sqrt κ with hγ
  set W := drive κ B ω with hW
  set L : ℝ → ℝ≥0∞ × ℝ≥0∞ := fun t => unzipLengthsArc γ (B2.cfg κ B X ω) t with hL
  set N : ℝ → ℝ → ℝ≥0∞ × ℝ≥0∞ := fun r s =>
    unzipLengthsArc γ (zipCapDown γ r (B2.cfg κ B X ω)) s with hN
  set w : ℝ → ℝ≥0∞ := lswDens κ (G ω) (fun r => trace W (max r 0)) with hw
  -- the `Γ⁰` new pieces at stage `T`
  have hsub : ∀ T r : ℝ, 0 ≤ r → r ≤ T →
      (N r (T - r)).1 = arcLen γ (unzippedField γ (B2.cfg κ B X ω) T) (lswPos W T r).1 0 ∧
      (N r (T - r)).2 = arcLen γ (unzippedField γ (B2.cfg κ B X ω) T) 0 (lswPos W T r).2 := by
    intro T r hr hrT
    obtain ⟨n, hn⟩ := exists_nat_ge T
    have hRE := hCCω n r (T - r) hr (sub_nonneg.2 hrT) (by linarith)
    have e : r + (T - r) = T := by ring
    rw [e] at hRE
    have hav : avgReg (unzippedField γ (zipCapDown γ r (B2.cfg κ B X ω)) (T - r)) =
        avgReg (unzippedField γ (B2.cfg κ B X ω) T) := B3d.avgReg_eq_of_regEq hRE
    exact ⟨arcLen_congr hav _ _, arcLen_congr hav _ _⟩
  -- common stage data
  have hstage : ∀ T : ℝ, 0 ≤ T → ∀ u : ℝ, 0 ≤ u → u ≤ T → ∀ μm μp : Measure ℝ,
      (∀ r ∈ Icc u T, (N r (T - r)).1 = μm (Ioc r T) ∧ (N r (T - r)).2 = μp (Ioc r T)) →
      (∀ r ∈ Ioc u T, μm {r} = 0 ∧ μp {r} = 0) →
      μm (Ioc u T) ≠ ⊤ → μp (Ioc u T) ≠ ⊤ →
      (arcLen γ (unzippedField γ (Z ω, W) T) (lswPos W T u).1 0,
        arcLen γ (unzippedField γ (Z ω, W) T) 0 (lswPos W T u).2) =
      (∫⁻ r in Ioc u T, w r ∂μm, ∫⁻ r in Ioc u T, w r ∂μp) := by
    intro T hT u hu huT μm μp hnew hat hfm hfp
    obtain ⟨hac, hbc, ham, hbm, htr⟩ := hPosω T hT
    obtain ⟨νY, hatY, hyreg, hνY, hzreg, hνZ⟩ := hDω T hT
    have hE : Continuous (fun x : ℝ => F2.extInv W T x) :=
      (hCω T hT).comp_continuous Complex.continuous_ofReal
        (fun x => show (0 : ℝ) ≤ ((x : ℝ) : ℂ).im by simp)
    have hself := lswPos_self W T
    have hzero : lswPos W T 0 = sideImages W T := lswPos_zero_drive h0 T
    have h0I : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
    have hTI : T ∈ Icc 0 T := ⟨hT, le_rfl⟩
    -- positions of the arcs
    have hOa : ∀ r ∈ Icc 0 T, (sideImages W T).1 ≤ (lswPos W T r).1 ∧ (lswPos W T r).1 ≤ 0 :=
      fun r hr => ⟨by rw [← hzero]; exact ham.monotoneOn h0I hr hr.1,
        by have := ham.monotoneOn hr hTI hr.2; rwa [hself] at this⟩
    have hOb : ∀ r ∈ Icc 0 T, 0 ≤ (lswPos W T r).2 ∧ (lswPos W T r).2 ≤ (sideImages W T).2 :=
      fun r hr => ⟨by have := hbm.antitoneOn hr hTI hr.2; rwa [hself] at this,
        by rw [← hzero]; exact hbm.antitoneOn h0I hr hr.1⟩
    set Vc := (offSet W T)ᶜ with hVc
    have hIa : ∀ r ∈ Icc 0 T, Ioo (lswPos W T r).1 0 ⊆ Vc := by
      intro r hr x hx hmem
      obtain ⟨h1, h2⟩ := hOa r hr
      obtain ⟨h3, -⟩ := hOb 0 h0I
      rw [hzero] at h3
      simp only [offSet, mem_insert_iff, mem_singleton_iff] at hmem
      rcases hmem with h | h | h <;> linarith [hx.1, hx.2]
    have hIb : ∀ r ∈ Icc 0 T, Ioo 0 (lswPos W T r).2 ⊆ Vc := by
      intro r hr x hx hmem
      obtain ⟨h1, h2⟩ := hOb r hr
      obtain ⟨-, h3⟩ := hOa 0 h0I
      rw [hzero] at h3
      simp only [offSet, mem_insert_iff, mem_singleton_iff] at hmem
      rcases hmem with h | h | h <;> linarith [hx.1, hx.2]
    set νΓ := νY.restrict Vc with hνΓ
    set ρ := lswDens κ (G ω) (fun x => F2.extInv W T x) with hρ
    set νZ := νΓ.withDensity ρ with hνZdef
    have hatZ : ∀ x, νZ {x} = 0 := fun x =>
      withDensity_absolutelyContinuous _ _
        (le_antisymm ((Measure.restrict_apply_le _ _).trans (hatY x).le) zero_le)
    have hsub0 : Ioo (lswPos W T u).1 0 ⊆ Vc := hIa u ⟨hu, huT⟩
    have hsub0' : Ioo 0 (lswPos W T u).2 ⊆ Vc := hIb u ⟨hu, huT⟩
    have hZa : arcLen γ (unzippedField γ (Z ω, W) T) (lswPos W T u).1 0 =
        νZ (Icc (lswPos W T u).1 0) := by
      rw [arcLen_eq_of_hasBdryLimitOn hzreg hνZ hsub0,
        measure_Icc_eq_Ioo_of_noAtoms (hatZ _) (hatZ _)]
    have hZb : arcLen γ (unzippedField γ (Z ω, W) T) 0 (lswPos W T u).2 =
        νZ (Icc 0 (lswPos W T u).2) := by
      rw [arcLen_eq_of_hasBdryLimitOn hzreg hνZ hsub0',
        measure_Icc_eq_Ioo_of_noAtoms (hatZ _) (hatZ _)]
    rw [hZa, hZb]
    have hsubY : ∀ {a b : ℝ}, Ioo a b ⊆ ({0} : Set ℝ)ᶜ → arcLen γ
        (unzippedField γ (B2.cfg κ B X ω) T) a b = νY (Ioo a b) := fun hab =>
      arcLen_eq_of_hasBdryLimitOn hyreg hνY hab
    have hoff : Vc ⊆ ({(lswPos W T 0).1, (lswPos W T 0).2} : Set ℝ)ᶜ := by
      rw [hzero]
      intro x hx hmem
      apply hx
      simp only [mem_insert_iff, mem_singleton_iff] at hmem
      simp only [offSet, mem_insert_iff, mem_singleton_iff]
      tauto
    have hZ : νZ = (νΓ.restrict ({(lswPos W T 0).1, (lswPos W T 0).2} : Set ℝ)ᶜ).withDensity ρ := by
      rw [hνZdef, hνΓ, Measure.restrict_restrict
        ((measurableSet_singleton _).insert _).compl, inter_eq_right.2 hoff]
    refine lsw2_stage hu huT hac hbc ham hbm (by rw [hself]) (by rw [hself])
      (fun r hr => ?_) (fun r hr => ?_) (fun r hr => (hat r hr).1) (fun r hr => (hat r hr).2)
      hfm hfp (measurable_lswDens hGω.1 hE.measurable) (fun r hr => ?_) (fun r hr => ?_) hZ
    · have hr0 : r ∈ Icc 0 T := ⟨hu.trans hr.1, hr.2⟩
      rw [hνΓ, restrict_Icc_eq_Ioo hatY (hIa r hr0), ← (hnew r hr).1,
        (hsub T r hr0.1 hr.2).1, hsubY]
      intro x hx hx0
      exact (ne_of_lt hx.2) hx0
    · have hr0 : r ∈ Icc 0 T := ⟨hu.trans hr.1, hr.2⟩
      rw [hνΓ, restrict_Icc_eq_Ioo hatY (hIb r hr0), ← (hnew r hr).2,
        (hsub T r hr0.1 hr.2).2, hsubY]
      intro x hx hx0
      exact (ne_of_gt hx.1) hx0
    · have hr0 : r ∈ Ioc 0 T := ⟨lt_of_le_of_lt hu hr.1, hr.2⟩
      simp only [hw, lswDens]
      rw [(htr r hr0).1, max_eq_left hr0.1.le]
    · have hr0 : r ∈ Ioc 0 T := ⟨lt_of_le_of_lt hu hr.1, hr.2⟩
      simp only [hw, lswDens]
      rw [(htr r hr0).2, max_eq_left hr0.1.le]
  -- finiteness of the new pieces
  have hNf : ∀ u s : ℝ, 0 ≤ u → 0 ≤ s → (N u s).1 ≠ ⊤ ∧ (N u s).2 ≠ ⊤ := by
    intro u s hu hs
    obtain ⟨k1, k2⟩ := hPω u s hu hs
    obtain ⟨f1, f2⟩ := hLf (u + s) (add_nonneg hu hs)
    refine ⟨ne_top_of_le_ne_top f1 ?_, ne_top_of_le_ne_top f2 ?_⟩
    · rw [k1]; exact le_add_self
    · rw [k2]; exact le_add_self
  refine ⟨w, measurable_lswDens hGω.1 ?_, fun _ _ => (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne',
    ?_, ?_⟩
  · exact (htrω.2.1.comp_continuous (continuous_id.max continuous_const)
      (fun r => mem_Ici.2 (le_max_right _ _))).measurable
  · intro μm μp hrep t ht
    have hnew : ∀ r ∈ Icc 0 t, (N r (t - r)).1 = μm (Ioc r t) ∧ (N r (t - r)).2 = μp (Ioc r t) := by
      intro r hr
      obtain ⟨k1, k2⟩ := hPω r (t - r) hr.1 (sub_nonneg.2 hr.2)
      have e : r + (t - r) = t := by ring
      rw [e] at k1 k2
      have ht' := hrep t ht
      have hr' := hrep r hr.1
      exact ⟨lsw2_alg_zero (hLf r hr.1).1 k1 (congrArg Prod.fst ht') (congrArg Prod.fst hr')
          (lsw2_Ioc_split μm hr.1 hr.2),
        lsw2_alg_zero (hLf r hr.1).2 k2 (congrArg Prod.snd ht') (congrArg Prod.snd hr')
          (lsw2_Ioc_split μp hr.1 hr.2)⟩
    have hat : ∀ r ∈ Ioc 0 t, μm {r} = 0 ∧ μp {r} = 0 := fun r hr =>
      ⟨lsw2_atom_zero (u := 0) (F := fun r => (L r).1)
          (fun r hr => (congrArg Prod.fst (hrep r hr)).symm) (fun r hr => (hLf r hr).1) c1 hr.1,
        lsw2_atom_zero (u := 0) (F := fun r => (L r).2)
          (fun r hr => (congrArg Prod.snd (hrep r hr)).symm) (fun r hr => (hLf r hr).2) c2 hr.1⟩
    have hfm : μm (Ioc 0 t) ≠ ⊤ := by
      rw [← show (L t).1 = μm (Ioc 0 t) from congrArg Prod.fst (hrep t ht)]; exact (hLf t ht).1
    have hfp : μp (Ioc 0 t) ≠ ⊤ := by
      rw [← show (L t).2 = μp (Ioc 0 t) from congrArg Prod.snd (hrep t ht)]; exact (hLf t ht).2
    have h := hstage t ht 0 le_rfl ht μm μp hnew hat hfm hfp
    rw [lswPos_zero_drive h0] at h
    exact h
  · intro u hu μm μp hrep s hs
    set T := u + s with hTdef
    have hnew : ∀ r ∈ Icc u T, (N r (T - r)).1 = μm (Ioc r T) ∧ (N r (T - r)).2 = μp (Ioc r T) := by
      intro r hr
      obtain ⟨k1, k2⟩ := hPω r (T - r) (hu.trans hr.1) (sub_nonneg.2 hr.2)
      obtain ⟨l1, l2⟩ := hPω u s hu hs
      obtain ⟨m1, m2⟩ := hPω u (r - u) hu (sub_nonneg.2 hr.1)
      have e : r + (T - r) = T := by ring
      have e' : u + (r - u) = r := by ring
      rw [e] at k1 k2
      rw [e'] at m1 m2
      have hs' := hrep s hs
      have hr' := hrep (r - u) (sub_nonneg.2 hr.1)
      rw [e'] at hr'
      exact ⟨lsw2_alg_shift (hLf r (hu.trans hr.1)).1 k1 (l1.trans (by rw [congrArg Prod.fst hs']))
          (m1.trans (by rw [congrArg Prod.fst hr'])) (lsw2_Ioc_split μm hr.1 hr.2),
        lsw2_alg_shift (hLf r (hu.trans hr.1)).2 k2 (l2.trans (by rw [congrArg Prod.snd hs']))
          (m2.trans (by rw [congrArg Prod.snd hr'])) (lsw2_Ioc_split μp hr.1 hr.2)⟩
    have hF : ∀ r, u ≤ r → μm (Ioc u r) = (N u (r - u)).1 ∧ μp (Ioc u r) = (N u (r - u)).2 := by
      intro r hr
      have h := hrep (r - u) (sub_nonneg.2 hr)
      have e' : u + (r - u) = r := by ring
      rw [e'] at h
      exact ⟨(congrArg Prod.fst h).symm, (congrArg Prod.snd h).symm⟩
    have hcont : ContinuousOn (fun r => (N u (r - u)).1.toReal) (Ici u) ∧
        ContinuousOn (fun r => (N u (r - u)).2.toReal) (Ici u) := by
      have hsub : Ici u ⊆ Ici (0 : ℝ) := Ici_subset_Ici.2 hu
      refine ⟨((c1.mono hsub).sub (continuousOn_const (c := (L u).1.toReal))).congr fun r hr => ?_,
        ((c2.mono hsub).sub (continuousOn_const (c := (L u).2.toReal))).congr fun r hr => ?_⟩
      · obtain ⟨m1, -⟩ := hPω u (r - u) hu (sub_nonneg.2 (mem_Ici.1 hr))
        have e' : u + (r - u) = r := by ring
        rw [e'] at m1
        show (N u (r - u)).1.toReal = (L r).1.toReal - (L u).1.toReal
        rw [show (L r).1 = _ from m1, ENNReal.toReal_add (hLf u hu).1
          (hNf u (r - u) hu (sub_nonneg.2 (mem_Ici.1 hr))).1]
        ring
      · obtain ⟨-, m2⟩ := hPω u (r - u) hu (sub_nonneg.2 (mem_Ici.1 hr))
        have e' : u + (r - u) = r := by ring
        rw [e'] at m2
        show (N u (r - u)).2.toReal = (L r).2.toReal - (L u).2.toReal
        rw [show (L r).2 = _ from m2, ENNReal.toReal_add (hLf u hu).2
          (hNf u (r - u) hu (sub_nonneg.2 (mem_Ici.1 hr))).2]
        ring
    have hat : ∀ r ∈ Ioc u T, μm {r} = 0 ∧ μp {r} = 0 := fun r hr =>
      ⟨lsw2_atom_zero (F := fun r => (N u (r - u)).1) (fun r hr => (hF r hr).1)
          (fun r hr => (hNf u (r - u) hu (sub_nonneg.2 hr)).1) hcont.1 hr.1,
        lsw2_atom_zero (F := fun r => (N u (r - u)).2) (fun r hr => (hF r hr).2)
          (fun r hr => (hNf u (r - u) hu (sub_nonneg.2 hr)).2) hcont.2 hr.1⟩
    have hfm : μm (Ioc u T) ≠ ⊤ := by
      rw [← show (N u s).1 = μm (Ioc u T) from congrArg Prod.fst (hrep s hs)]
      exact (hNf u s hu hs).1
    have hfp : μp (Ioc u T) ≠ ⊤ := by
      rw [← show (N u s).2 = μp (Ioc u T) from congrArg Prod.snd (hrep s hs)]
      exact (hNf u s hu hs).2
    have hav : avgReg (unzippedField γ (zipCapDown γ u (Z ω, W)) s) =
        avgReg (unzippedField γ (Z ω, W) T) := B3d.avgReg_eq_of_regEq (hZCω u s hu hs)
    have e1 : unzipLengthsArc γ (zipCapDown γ u (Z ω, W)) s =
        (arcLen γ (unzippedField γ (Z ω, W) T) (lswPos W T u).1 0,
          arcLen γ (unzippedField γ (Z ω, W) T) 0 (lswPos W T u).2) := by
      show (arcLen γ (unzippedField γ (zipCapDown γ u (Z ω, W)) s)
          (sideImages (zipCapDown γ u (Z ω, W)).2 s).1 0,
        arcLen γ (unzippedField γ (zipCapDown γ u (Z ω, W)) s) 0
          (sideImages (zipCapDown γ u (Z ω, W)).2 s).2) = _
      rw [arcLen_congr hav, arcLen_congr hav]
      unfold lswPos
      rw [hTdef, add_sub_cancel_left]
      rfl
    rw [e1]
    exact hstage T (by linarith) u hu (by linarith) μm μp hnew hat hfm hfp

end LocLen
end QuantumZipper
