import QuantumZipper.Proofs.Zipper.LocLenR5cPStar
import QuantumZipper.Proofs.Zipper.LocLenR5aPalm

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R5b (D75): B5 locality with the deterministic open-arc regularity set

Copy of `E6NodeReg.lean` (`localAbs_regDet`, `ae_hitScaleGood_pstar`, `pstar_regDet`) with `zipLenDown ↦ zipLenDownArc`, `tHit ↦ lenTimeArc`
and the open-arc local readers of `LocLenR5cRead`/`LocLenR5cMain` (`tauLocArc`, `aLocArc`,
`goodSetHitArc`, `HitScaleGoodArc`, `conclusionsArc_of_mem`, `eventually_mem_goodSetHitArc`), from
`HitScaleZipArcStmt` (LocLenR5cPStar). `gOutArc`/`RegDetArc` are the same terms as
`gOutArc`/`RegDetArc` of `LocLenR5aStmts` (which re-declares `lenLocArc`, `tauLocArc`, `aLocArc`,
`goodSetHitArc` and so cannot be imported together with `LocLenR5cRead`). Own bookkeeping, as for
the originals (the paper asserts the locality without proof; Sheffield arXiv:1012.4797 §5.4,
pp. 70–72; B-P arXiv:2404.16642 p. 294).
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped NNReal ENNReal Topology

namespace QuantumZipper.LocLen
open R5c

open E6 D3Plus MeasUnzip CharFun

variable {Ω' : Type} [MeasurableSpace Ω']

/-- **`LocalAbs` with the deterministic regularity set** for a sample with a.e.-measurable local
data that is almost surely `HitScaleGood` (the tightness argument of
`E6.locHitScaleStmt_of_good`, keeping the explicit good sets). -/
theorem localAbsArc_regDetArc {γ κ ℓ : ℝ} (hκ : 0 < κ) {P' : Measure Ω'} [IsProbabilityMeasure P']
    {c' : Ω' → Cfg} (hc : ∀ R' : ℕ, AEMeasurable (fun ω' => locRich R' (c' ω')) P')
    (hg : ∀ᵐ ω' ∂P', HitScaleGoodArc γ ℓ (c' ω')) :
    LocalAbsArc γ ℓ P' c' (RegDetArc γ κ ℓ) := by
  intro R ε hε
  set G : ℕ → ℕ → Set Ω' := fun n m =>
    {ω' | locRich (Rp R (n + 1) m) (c' ω') ∈ goodSetHitArc γ κ ℓ R (n + 1) m} with hGdef
  have hGn : ∀ n m, NullMeasurableSet (G n m) P' := fun n m =>
    (hc _).nullMeasurable (measurableSet_goodSetHitArc γ κ ℓ R (n + 1) m)
  set F : ℕ → Set Ω' := fun n => ⋃ M0 : ℕ, ⋂ m ≥ M0, G n m with hFdef
  set Hs : ℕ → Set Ω' := fun k => ⋂ n ≥ k, F n with hHsdef
  have hHmono : Monotone Hs := fun k k' hkk' ω hω =>
    mem_iInter₂.2 fun n hn => mem_iInter₂.1 hω n (hkk'.trans hn)
  have hae : ∀ᵐ ω' ∂P', ω' ∈ ⋃ k, Hs k := by
    filter_upwards [hg] with ω' hω'
    obtain ⟨k, hk⟩ := eventually_mem_goodSetHitArc (κ := κ) hκ R hω'
    refine mem_iUnion.2 ⟨k, mem_iInter₂.2 fun n hn => ?_⟩
    obtain ⟨M0, hM0⟩ := hk n hn
    exact mem_iUnion.2 ⟨M0, mem_iInter₂.2 fun m hm => hM0 m hm⟩
  have hfull : P' (⋃ k, Hs k) = 1 := by
    refine le_antisymm prob_le_one ?_
    have h1 : P' (⋃ k, Hs k)ᶜ = 0 := ae_iff.1 hae
    calc (1 : ℝ≥0∞) = P' univ := measure_univ.symm
      _ ≤ P' (⋃ k, Hs k) + P' (⋃ k, Hs k)ᶜ := by
        rw [← union_compl_self (⋃ k, Hs k)]; exact measure_union_le _ _
      _ = P' (⋃ k, Hs k) := by rw [h1, add_zero]
  have hε1 : 1 - ε < 1 := ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hε.ne'
  obtain ⟨k, hk⟩ := ((tendsto_measure_iUnion_atTop (μ := P') hHmono).eventually
    (lt_mem_nhds (hfull.symm ▸ hε1 : 1 - ε < P' (⋃ k, Hs k)))).exists
  have hFk : 1 - ε < P' (F k) :=
    hk.trans_le (measure_mono (iInter₂_subset (s := fun n (_ : n ≥ k) => F n) k le_rfl))
  set Gs : ℕ → Set Ω' := fun M0 => ⋂ m ≥ M0, G k m with hGsdef
  have hGmono : Monotone Gs := fun a b hab ω hω =>
    mem_iInter₂.2 fun m hm => mem_iInter₂.1 hω m (hab.trans hm)
  obtain ⟨M0, hM0⟩ := ((tendsto_measure_iUnion_atTop (μ := P') hGmono).eventually
    (lt_mem_nhds (show 1 - ε < P' (⋃ M0, Gs M0) from hFk))).exists
  have hGk : 1 - ε < P' (G k M0) :=
    hM0.trans_le (measure_mono (iInter₂_subset (s := fun m (_ : m ≥ M0) => G k m) M0 le_rfl))
  refine ⟨Rp R (k + 1) M0, gOutArc γ κ ℓ R (k + 1) M0, goodSetHitArc γ κ ℓ R (k + 1) M0,
    measurable_gOutArc hκ _ _ _, measurableSet_goodSetHitArc _ _ _ _ _ _, ?_,
    fun y hy hmem => hy R (k + 1) M0 (Nat.succ_pos k) hmem⟩
  have e : {ω' | locRich (Rp R (k + 1) M0) (c' ω') ∉ goodSetHitArc γ κ ℓ R (k + 1) M0} =
      (G k M0)ᶜ := rfl
  rw [e, prob_compl_eq_one_sub₀ (hGn k M0)]
  refine tsub_le_iff_right.2 ?_
  calc (1 : ℝ≥0∞) ≤ 1 - ε + ε := le_tsub_add
    _ ≤ P' (G k M0) + ε := add_le_add hGk.le le_rfl
    _ = ε + P' (G k M0) := add_comm _ _

/-- A `P_*` sample is almost surely `HitScaleGood`, given `HitScaleZipStmt` (as in
`E6.locHitScaleStmt_pstar`). -/
theorem ae_hitScaleGoodArc_pstar (h : HitScaleZipArcStmt) (κ : ℝ) (P' : Measure Ω')
    [IsProbabilityMeasure P'] (Y : Ω' → FieldSample) (B' : ℝ≥0 → Ω' → ℝ)
    (hP : Thm13Asm.IsPStarSample κ P' Y B') (ℓ₁ : ℝ) (hℓ : 0 < ℓ₁) :
    ∀ᵐ ω' ∂P', HitScaleGoodArc (Real.sqrt κ) ℓ₁ (Y ω', drive κ B' ω') := by
  have hB := hP.2.2.2.1
  filter_upwards [h κ P' Y B' hP ℓ₁ hℓ, hB.cont, hB.toIsPreBrownianReal.eval_zero_ae_eq_zero,
    RS.ae_real_alive hB hP.1 hP.2.1.le] with ω hz hc h0 hal
  exact ⟨continuous_const.mul (hc.comp continuous_real_toNNReal), by simp [drive, h0],
    fun z hz s hs => hal z hz s hs, hz.lim, hz.mono, hz.reach, hz.pos, hz.area, hz.scale⟩

/-- **B5 locality with the deterministic regularity set, for every `P_*` sample**, from
`HitScaleZipStmt`. -/
theorem pstar_regDetArc (h : HitScaleZipArcStmt) (κ : ℝ) (P' : Measure Ω') [IsProbabilityMeasure P']
    (Y : Ω' → FieldSample) (B' : ℝ≥0 → Ω' → ℝ) (hP : Thm13Asm.IsPStarSample κ P' Y B')
    (ℓ₁ : ℝ) (hℓ : 0 < ℓ₁) :
    (∀ᵐ ω' ∂P', (Y ω', drive κ B' ω') ∈ RegDetArc (Real.sqrt κ) κ ℓ₁) ∧
      LocalAbsArc (Real.sqrt κ) ℓ₁ P' (fun ω' => (Y ω', drive κ B' ω'))
        (RegDetArc (Real.sqrt κ) κ ℓ₁) := by
  have hg := ae_hitScaleGoodArc_pstar h κ P' Y B' hP ℓ₁ hℓ
  exact ⟨hg.mono fun ω' hω' => mem_regDetArc_of_good hP.1 hω',
    localAbsArc_regDetArc hP.1 (aemeasurable_locRich_pstar hP) hg⟩
end QuantumZipper.LocLen
