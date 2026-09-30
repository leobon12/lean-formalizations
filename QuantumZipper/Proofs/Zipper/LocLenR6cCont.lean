import QuantumZipper.Proofs.Zipper.LocLenR6cAtom
import QuantumZipper.Proofs.Zipper.LocLenR6cMono

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# D75 / R6h (2): continuity of the open-arc left length, `L⁻_0 = 0` (`LenLeftRegArcStmt`)

Sheffield, arXiv:1012.4797, §1.4 and p. 70 (`t ↦ L⁻_t` is continuous): fix a horizon `T > 0`.
For `t₀ ∈ [0,T)`, lengths add (`LenPairCocycleArcStmt`) and the restarted length is
`ν_T (m(t₀), 0)` with `m(t₀) = 0₋^{vrev W T}(T − t₀)` (`stage_arcLen_eq`, R6c), so
`L⁻_{t₀} = L⁻_T − ν_T (m(t₀), 0)`. The map `m` is continuous with values in `[O⁻_T, 0]`, and
`ν_T` is finite on `(O⁻_T, 0)` (its mass there is `L⁻_T`, X1) and has no atoms there
(`pStarAtomOff_of_core`), so `t₀ ↦ L⁻_{t₀}` is continuous on `[0,T)`; at `t₀ = 0`,
`m(0) = O⁻_T` gives `L⁻_0 + L⁻_T = L⁻_T`, i.e. `L⁻_0 = 0`. This is the reading of the lengths in
the fixed chart of time `T` (the `Γ⁰`-picture argument of FOLLOW-PAPER-13 row R6h), with the
chart-`T` measure the local limit off the root images. Bookkeeping own.

* `pStarAtomOff_of_core` (copy of `pStarPosOff_of_core` with `AtomOff`).
* `continuousOn_measure_Ioo_left_r6c` (copy of `continuousOn_measure_Icc_left_s3a`,
  LocLenStep3Arcs.lean).
* `continuousOn_arc_of_stage`, `lenLeftRegArc_det` (deterministic).
* **`lenLeftRegArc_of_yMergeOffTip`**.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace LocLen

open WedgeUnzip

/-- **`P_*` fields: no atoms off the root images** (copy of `pStarPosOff_of_core`). -/
theorem pStarAtomOff_of_core (hR : WedgeUnzip.PStarRealizeStmt) (hP : WedgeAtomOffAllStmt)
    (hG : WedgeGoodOffAllStmt) (hE : WedgeUnzip.WedgeExactAllStmt)
    (hC : WedgeUnzip.WedgeContinuumStmt) (κ : ℝ) {Ω' : Type} [MeasurableSpace Ω']
    (P' : Measure Ω') [IsProbabilityMeasure P'] (Y : Ω' → FieldSample) (B' : ℝ≥0 → Ω' → ℝ)
    (hPS : Thm13Asm.IsPStarSample κ P' Y B') :
    ∀ᵐ ω ∂P', ∀ t : ℝ, 0 < t → AtomOff (Real.sqrt κ)
      (unzippedField (Real.sqrt κ) (Y ω, drive κ B' ω) t) (offSet (drive κ B' ω) t) := by
  obtain ⟨hκ, hκ4, -⟩ := id hPS
  obtain ⟨Ω₂, _, Q, _, X', A, B'', hX, hA, hI, hB, hIB, hae⟩ := hR κ P' Y B' hPS
  have hγ : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  have hγ2 : Real.sqrt κ < 2 := F2.sqrt_lt_two_of' hκ hκ4
  refine WedgeUnzip.ae_of_ae_prod_fst (Q := Q) ?_
  filter_upwards [hae, hP κ hκ hκ4 _ X' A B'' hX hA hI hB hIB,
    hG κ hκ hκ4 _ X' A B'' hX hA hI hB hIB,
    hE κ hκ hκ4 _ X' A B'' hX hA hI hB hIB, hC κ hκ hκ4 _ X' A B'' hX hA hI hB hIB,
    Wire2.ae_wedge_canonical_spec hγ hγ2 (F2.alpha_lt_Qc' hγ hγ2) hX hA hI,
    hB.cont, hB.eval_zero_ae_eq_zero, RS.ae_real_alive hB hκ hκ4.le]
    with ω hRω hPω hGω hEω hCω hspec hc h0 halive
  obtain ⟨havg, hcfg⟩ := hRω
  intro t ht
  set Z := F2.zU (Real.sqrt κ) X' A ω
  have ha : 0 < scaleParam (Real.sqrt κ) Z := hspec.1
  have hW : Continuous (drive κ B'' ω) := by
    unfold drive
    exact continuous_const.mul (hc.comp continuous_real_toNNReal)
  have hW0 : drive κ B'' ω 0 = 0 := by simp [drive, h0]
  have hWmax := F2.drive_max κ B'' ω
  have e1 : unzippedField (Real.sqrt κ) (Y ω.1, drive κ B' ω.1) t =
      unzippedField (Real.sqrt κ) (canonConfig (Real.sqrt κ) (Z, drive κ B'' ω)) t := by
    rw [hcfg]
    exact Factorization.coordChange_congr havg _ _
  have has : 0 < scaleParam (Real.sqrt κ) Z ^ 2 * t := by positivity
  have hraw := WedgeUnzip.unzippedField_canonConfig_fc hW hW0 hWmax ha ht.le (fun d r hr => by
      rw [B3d.canonConfig_snd_of_max hWmax]
      have hC' := hCω.2 _ has.le ((scaleParam (Real.sqrt κ) Z : ℂ) * d) _ (mul_pos ha hr)
      exact WedgeUnzip.scaleConsistent_of_continuum hCω.1 _ hW hW0 ha ht.le d hr hC'.1 hC'.2)
    (hEω _ has.le)
  have hdrvY : drive κ B' ω.1 = fun r =>
      drive κ B'' ω (scaleParam (Real.sqrt κ) Z ^ 2 * r) / scaleParam (Real.sqrt κ) Z := by
    have h := B3d.canonConfig_snd_of_max (γ := Real.sqrt κ) (y := Z) hWmax
    rw [hcfg] at h
    exact h
  obtain ⟨l, m, hl, hm⟩ := F1.exists_tendsto_sideImages_of_alive has.le
    (fun x hx => halive x hx _ has.le)
  have s1 : (sideImages (drive κ B' ω.1) t).1 = l / scaleParam (Real.sqrt κ) Z := by
    rw [hdrvY]; exact B3d.sideImages_fst_scale _ ha ht.le hl
  have s2 : (sideImages (drive κ B' ω.1) t).2 = m / scaleParam (Real.sqrt κ) Z := by
    rw [hdrvY]; exact B3d.sideImages_snd_scale _ ha ht.le hm
  have s1' : (sideImages (drive κ B'' ω) (scaleParam (Real.sqrt κ) Z ^ 2 * t)).1 = l :=
    hl.limUnder_eq
  have s2' : (sideImages (drive κ B'' ω) (scaleParam (Real.sqrt κ) Z ^ 2 * t)).2 = m :=
    hm.limUnder_eq
  have hoff : offSet (drive κ B' ω.1) t = (fun u => scaleParam (Real.sqrt κ) Z * u) ⁻¹'
      offSet (drive κ B'' ω) (scaleParam (Real.sqrt κ) Z ^ 2 * t) := by
    ext u
    simp only [offSet, mem_preimage, mem_insert_iff, mem_singleton_iff, s1, s2, s1', s2']
    rw [eq_div_iff ha.ne', eq_div_iff ha.ne', mul_comm u, mul_eq_zero]
    simp [ha.ne']
  rw [e1, hoff]
  refine AtomOff.congr_coords (WedgeUnzip.coords_eq_of_fc fun d _ r hr => hraw d r hr) ?_
  exact (hPω _ has).rescale (hGω _ has.le).1 hγ ha

/-- **Closed form**: `P_*` atomlessness off the root images from the offset merging input. -/
theorem pStarAtomOff_of_yMergeOffTip (hYO : WedgeUnzip.YMergeOffTipStmt) (κ : ℝ) {Ω' : Type}
    [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P'] (Y : Ω' → FieldSample)
    (B' : ℝ≥0 → Ω' → ℝ) (hPS : Thm13Asm.IsPStarSample κ P' Y B') :
    ∀ᵐ ω ∂P', ∀ t : ℝ, 0 < t → AtomOff (Real.sqrt κ)
      (unzippedField (Real.sqrt κ) (Y ω, drive κ B' ω) t) (offSet (drive κ B' ω) t) :=
  pStarAtomOff_of_core pStarRealizeStmt_holds (wedgeAtomOffAll_of_yGood
      (yGoodOffAll_of_yMergeOffTip hYO))
    (wedgeGoodOffAll_of_yMergeOffTip hYO) (wedgeExactAll_of_yMergeOffTip hYO)
    (wedgeContinuum_of_x WDec.wedgeDecompStmt_holds xContinuumStmt_holds) κ P' Y B' hPS

/-- Distribution function of an atomless finite measure on `[a, 0]`, right endpoint fixed
(copy of `continuousOn_measure_Icc_left_s3a` for `ν|_(a,0)` and open intervals). -/
theorem continuousOn_measure_Ioo_left_r6c {ν : Measure ℝ} {a : ℝ}
    (hat : ∀ p ∈ Ioo a 0, ν {p} = 0) (hfin : ν (Ioo a 0) ≠ ⊤) :
    ContinuousOn (fun x => (ν (Ioo x 0)).toReal) (Icc a 0) := by
  set μ := ν.restrict (Ioo a 0) with hμ
  have hμat : ∀ x, μ {x} = 0 := fun x => by
    rw [hμ, Measure.restrict_apply (measurableSet_singleton x)]
    by_cases hx : x ∈ Ioo a 0
    · rw [inter_eq_left.2 (singleton_subset_iff.2 hx)]; exact hat x hx
    · rw [singleton_inter_eq_empty.2 hx, measure_empty]
  have : NullSingletonClass μ := ⟨hμat⟩
  have hfin' : μ (Icc a 0) ≠ ⊤ := by
    rw [hμ, Measure.restrict_apply measurableSet_Icc]
    exact ne_top_of_le_ne_top hfin (measure_mono inter_subset_right)
  have hi : IntegrableOn (fun _ => (1 : ℝ)) (Icc a 0) μ := integrableOn_const hfin'
  have hR : ContinuousOn (fun x => (μ (Icc a x)).toReal) (Icc a 0) :=
    (intervalIntegral.continuousOn_primitive_Icc hi).congr fun x _ => by
      simp [Measure.real]
  refine ((continuousOn_const (c := (μ (Icc a 0)).toReal)).sub hR).congr fun x hx => ?_
  have hsplit : μ (Icc a 0) = μ (Icc a x) + μ (Icc x 0) := by
    rw [← Ico_union_Icc_eq_Icc hx.1 hx.2, measure_union
      (Set.disjoint_left.2 fun y hy hy' => (not_le.2 hy.2) hy'.1) measurableSet_Icc,
      measure_congr (Ico_ae_eq_Icc (μ := μ))]
  have h1 : μ (Icc a x) ≠ ⊤ := ne_top_of_le_ne_top hfin' (measure_mono (Icc_subset_Icc le_rfl hx.2))
  have h2 : μ (Icc x 0) ≠ ⊤ := ne_top_of_le_ne_top hfin' (measure_mono (Icc_subset_Icc hx.1 le_rfl))
  have e : ν (Ioo x 0) = μ (Icc x 0) := by
    rw [← measure_congr (Ioo_ae_eq_Icc (μ := μ)), hμ, Measure.restrict_apply measurableSet_Ioo,
      inter_eq_left.2 (Ioo_subset_Ioo_left hx.1)]
  show (ν (Ioo x 0)).toReal = (μ (Icc a 0)).toReal - (μ (Icc a x)).toReal
  rw [e, hsplit, ENNReal.toReal_add h1 h2]
  ring

/-- **Deterministic continuity on `[0,T)`** from the chart-`T` reading
`L t₀ + ν (m t₀, 0) = L T`. -/
theorem continuousOn_arc_of_stage {L : ℝ → ℝ≥0∞} {ν : Measure ℝ} {m : ℝ → ℝ} {a T : ℝ}
    (hm : ContinuousOn m (Icc 0 T)) (hmI : ∀ t₀ ∈ Icc 0 T, a ≤ m t₀ ∧ m t₀ ≤ 0)
    (hat : ∀ p ∈ Ioo a 0, ν {p} = 0) (hfin : ν (Ioo a 0) ≠ ⊤) (hLT : L T ≠ ⊤)
    (heq : ∀ t₀ ∈ Ico 0 T, L t₀ + ν (Ioo (m t₀) 0) = L T) :
    ContinuousOn (fun t => (L t).toReal) (Ico 0 T) := by
  have hg := continuousOn_measure_Ioo_left_r6c hat hfin
  have hcomp : ContinuousOn (fun t₀ => (ν (Ioo (m t₀) 0)).toReal) (Ico 0 T) :=
    hg.comp (hm.mono Ico_subset_Icc_self) fun t₀ ht₀ => ⟨(hmI t₀ (Ico_subset_Icc_self ht₀)).1,
      (hmI t₀ (Ico_subset_Icc_self ht₀)).2⟩
  refine ((continuousOn_const (c := (L T).toReal)).sub hcomp).congr fun t₀ ht₀ => ?_
  have e := heq t₀ ht₀
  have h1 : L t₀ ≠ ⊤ := fun h => hLT (by rw [← e, h, top_add])
  have h2 : ν (Ioo (m t₀) 0) ≠ ⊤ := fun h => hLT (by rw [← e, h, add_top])
  show (L t₀).toReal = (L T).toReal - (ν (Ioo (m t₀) 0)).toReal
  rw [← e, ENNReal.toReal_add h1 h2]
  ring

/-- **Deterministic `LenLeftRegArc`**: continuity on every `[0,T)` gives continuity on
`[0,∞)`; the reading at `t₀ = 0` with `m 0 = a`, `ν (a,0) = L T` gives `L 0 = 0`. -/
theorem lenLeftRegArc_det {L : ℝ → ℝ≥0∞}
    (hT : ∀ T : ℝ, 0 < T → ContinuousOn (fun t => (L t).toReal) (Ico 0 T))
    (h0 : L 1 ≠ ⊤ → L 0 + L 1 = L 1) (h1 : L 1 ≠ ⊤) :
    ContinuousOn (fun t => (L t).toReal) (Ici 0) ∧ L 0 = 0 := by
  refine ⟨fun t ht => ?_, (ENNReal.add_right_inj h1).1 (by rw [add_comm, h0 h1, add_zero])⟩
  have ht' : (0 : ℝ) < t + 1 := by linarith [mem_Ici.1 ht]
  have hmem : t ∈ Ico (0 : ℝ) (t + 1) := ⟨mem_Ici.1 ht, by linarith⟩
  refine ((hT (t + 1) ht') t hmem).mono_of_mem_nhdsWithin ?_
  rw [← Ici_inter_Iio]
  exact inter_mem_nhdsWithin _ (Iio_mem_nhds (by linarith))

/-- **`LenLeftRegArcStmt` from the capacity field cocycle, goodness and atomlessness off the root
images, the pair cocycle and finiteness.** -/
theorem lenLeftRegArc_of_parts
    (hCap : ∀ (κ : ℝ) {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω')
      [IsProbabilityMeasure P'] (Y : Ω' → FieldSample) (B' : ℝ≥0 → Ω' → ℝ),
      Thm13Asm.IsPStarSample κ P' Y B' →
      ∀ᵐ ω ∂P', Thm18Asm.UnzipCapRegData (Real.sqrt κ) (Y ω, drive κ B' ω))
    (hPG : PStarGoodOffAllStmt)
    (hAt : ∀ (κ : ℝ) {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω')
      [IsProbabilityMeasure P'] (Y : Ω' → FieldSample) (B' : ℝ≥0 → Ω' → ℝ),
      Thm13Asm.IsPStarSample κ P' Y B' → ∀ᵐ ω ∂P', ∀ t : ℝ, 0 < t → AtomOff (Real.sqrt κ)
        (unzippedField (Real.sqrt κ) (Y ω, drive κ B' ω) t) (offSet (drive κ B' ω) t))
    (hC : LenPairCocycleArcStmt) (hF : LenFiniteArcStmt) : LenLeftRegArcStmt := by
  intro κ Ω' _ P' _ Y B' hP
  filter_upwards [hCap κ P' Y B' hP, hPG κ P' Y B' hP, hAt κ P' Y B' hP, hC κ P' Y B' hP,
    ae_unzipLengthsArc_lt_top_all hC hF κ P' Y B' hP, ae_pstar_zeroMinus_facts hP,
    hP.2.2.2.1.cont, hP.2.2.2.1.eval_zero_ae_eq_zero]
    with ω hcap hg hat hc hf hz hcB h0
  set W := drive κ B' ω with hWdef
  have hW : Continuous W := by
    rw [hWdef]; unfold drive
    exact continuous_const.mul (hcB.comp continuous_real_toNNReal)
  have hW0 : W 0 = 0 := by simp [hWdef, drive, h0]
  set L : ℝ → ℝ≥0∞ := fun t => (unzipLengthsArc (Real.sqrt κ) (F1.pcfg κ Y B' ω) t).1 with hL
  have key : ∀ T : ℝ, 0 < T → ∃ ν : Measure ℝ,
      (∀ p ∈ Ioo (sideImages W T).1 0, ν {p} = 0) ∧ ν (Ioo (sideImages W T).1 0) = L T ∧
      ∀ t₀ ∈ Ico 0 T, L t₀ + ν (Ioo (zeroMinus (B2.vrev W T) (T - t₀)) 0) = L T := by
    intro T hT
    obtain ⟨-, hanti, -, hO, hside⟩ := hz T hT
    obtain ⟨hr, ⟨ν, hν⟩, -⟩ := hg T hT.le
    obtain ⟨ν', hν', hat'⟩ := hat T hT
    have hνν : ν = ν' := hν.unique (isClosed_offSet _ T).isOpen_compl hν'
    have hp := sideImages_snd_nonneg_of_cont hW hW0 hT.le
    refine ⟨ν, fun p hp' => by
      rw [hνν]; exact hat' p (disjoint_left.1 (Ioo_left_disjoint_offSet _ T hp) hp'), ?_, ?_⟩
    · show _ = arcLen (Real.sqrt κ) (unzippedField (Real.sqrt κ) (F1.pcfg κ Y B' ω) T)
        (sideImages W T).1 0
      unfold arcLen
      rw [IsLQGGoodOff.qBoundaryMeasureOn_eq hr hν isOpen_Ioo (Ioo_left_disjoint_offSet _ T hp),
        Measure.restrict_apply_self]
    · intro t₀ ht₀
      have hmle : (sideImages W T).1 ≤ zeroMinus (B2.vrev W T) (T - t₀) := by
        rw [hO]
        exact hanti.antitoneOn ⟨sub_nonneg.2 ht₀.2.le, by linarith [ht₀.1]⟩ ⟨hT.le, le_rfl⟩
          (by linarith [ht₀.1])
      have hcapT := hcap t₀ (T - t₀) ht₀.1 (sub_nonneg.2 ht₀.2.le)
      rw [add_sub_cancel] at hcapT
      have h := (hc t₀ (T - t₀) ht₀.1 (sub_nonneg.2 ht₀.2.le)).1
      rw [add_sub_cancel] at h
      simp only [hL]
      rw [h, stage_arcLen_eq (c := F1.pcfg κ Y B' ω) hcapT (hside t₀ ht₀.1 ht₀.2) hmle hp hr hν]
  refine lenLeftRegArc_det (L := L) (fun T hT => ?_) (fun _ => ?_) (hf 1 zero_le_one).1.ne
  · obtain ⟨ν, hat, hνL, heq⟩ := key T hT
    obtain ⟨hcont, hanti, hz0, hO, -⟩ := hz T hT
    refine continuousOn_arc_of_stage (a := (sideImages W T).1)
      (m := fun t₀ => zeroMinus (B2.vrev W T) (T - t₀)) ?_ ?_ hat
      (by rw [hνL]; exact (hf T hT.le).1.ne) (hf T hT.le).1.ne heq
    · exact hcont.comp (continuousOn_const.sub continuousOn_id) fun t₀ ht₀ =>
        ⟨sub_nonneg.2 ht₀.2, by linarith [ht₀.1]⟩
    · intro t₀ ht₀
      refine ⟨?_, ?_⟩
      · rw [hO]
        exact hanti.antitoneOn ⟨sub_nonneg.2 ht₀.2, by linarith [ht₀.1]⟩ ⟨hT.le, le_rfl⟩
          (by linarith [ht₀.1])
      · rw [← hz0]
        exact hanti.antitoneOn ⟨le_rfl, hT.le⟩ ⟨sub_nonneg.2 ht₀.2, by linarith [ht₀.1]⟩
          (sub_nonneg.2 ht₀.2)
  · obtain ⟨ν, -, hνL, heq⟩ := key 1 one_pos
    obtain ⟨-, -, -, hO, -⟩ := hz 1 one_pos
    have := heq 0 ⟨le_rfl, one_pos⟩
    rw [sub_zero, ← hO, hνL] at this
    exact this

/-- **`LenLeftRegArcStmt`, closed form**: from the offset merging input, the open-arc pair
cocycle (R6a) and the fixed-time finiteness (X1 in `P_*` form, R6g). -/
theorem lenLeftRegArc_of_yMergeOffTip (hYO : WedgeUnzip.YMergeOffTipStmt)
    (hC : LenPairCocycleArcStmt) (hF : LenFiniteArcStmt) : LenLeftRegArcStmt :=
  lenLeftRegArc_of_parts (pStarCapRegOff_of_yMergeOffTip hYO)
    (pStarGoodOffAll_of_yMergeOffTip hYO) (pStarAtomOff_of_yMergeOffTip hYO) hC hF

end LocLen
end QuantumZipper
