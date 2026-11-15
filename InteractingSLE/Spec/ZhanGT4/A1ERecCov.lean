/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1ERecMeas
import InteractingSLE.Spec.ZhanGT4.A2TipSepGeom
import InteractingSLE.Foundations.Loewner.ConformalImageFullClearance

/-!
# Zhan's A.1 (Eight), large direction: the cofinal rectangles exhaust the pre-contact configurations (`hcov`)

Packet PROVE-A1-EIGHTREC. Astra, *Follow-up proofs*, §A.1.5 (`ig1_followup_proofs.txt` L409–L425: "Any pair of
disjoint compact prefixes is contained in a member of the countable enclosure family"); A1-COMMON's `exists_rect_le`.

* **`disjoint_prefix_of_lt_contactTime`** (deterministic): before the first contact of the large curve (from `0`)
  with the frozen small hull (from `x < 0`), the two prefixes in the small curve's frame — `closure K₁(τ) ∪ {0}` and the
  closed large hull shifted to the source `−x`, with `−x` — are disjoint. The large curve's force point `x` is alive
  before `lifeEnd`, hence off the closed large hull; the large start `0` lies in the closed large hull at a positive
  time, hence `−x` is off the closed small hull.
* **`eightRec_hcov`**: the record fact `hcov` of A1-RECTLAW2's `eightFstResStop` for regular good Eight marginals: on
  the live event every pre-contact own time of the large curve has its clock below some raw cap.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1ERec

open QuantumZipper (H fwdHull IsForwardSol)
open A2X A1Ref A1Canon A1Core A1Marg A1Law A1Patch A1SeedField A1EightSeed A1G3Calc A1Common A1EightFin A1ELaw
  A1Good A1LargeDens A1Asm A1Forces A1MultiMark A1Family A1RLaw A1Frozen A1SeedGeom A1RectLaw

/-! ### Disjoint prefixes before the contact -/

section Det

/-- **An alive force point is off the closed hull**: a force point `v` started at `p` and strictly left of the driver
on `[0, s]` (`s` before the lifetime) is not in the closed hull at time `s`. -/
theorem notMem_closure_fwdHull_of_force {w v : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ})
    (hv : ContinuousOn v {t | (t : ℝ≥0∞) < ζ}) {p : ℝ}
    (hveq : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → v t = p + ∫ s in (0 : ℝ)..t, 2 / (v s.toNNReal - w s.toNNReal))
    {s : ℝ≥0} (hs : (s : ℝ≥0∞) < ζ) (hsep : ∀ r ≤ s, v r ≠ w r) :
    (p : ℂ) ∉ closure (fwdHull (Strip.extPath w) s) := by
  obtain ⟨T', hsT', hcT'⟩ := exists_gt_continuousOn_extPath hw hs
  have hT'0 : 0 ≤ T' := s.coe_nonneg.trans hsT'.le
  have hAc : Continuous (A1Ref.stopDrv (Strip.extPath w) T') := A1Ref.continuous_stopDrv hcT' hT'0
  rw [LocalExt.fwdHull_congr_of_eqOn_of_lt s.coe_nonneg hsT' fun u hu => (A1Ref.stopDrv_eqOn _ T' hu).symm]
  have hsol := A1G3Calc.isForwardSol_of_force hv hveq hs hsep hAc.continuousOn
    fun u hu => A1Ref.stopDrv_eqOn _ T' ⟨hu.1, hu.2.trans hsT'.le⟩
  exact A2TipSep.not_mem_closure_fwdHull_of_isForwardSol hAc s.coe_nonneg hsol

/-- **The start is in the closed hull at a positive time** (for a driver continuous before its lifetime). -/
theorem zero_mem_closure_fwdHull_extPath {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ})
    (hw0 : w 0 = 0) {s : ℝ≥0} (hs0 : 0 < (s : ℝ)) (hs : (s : ℝ≥0∞) < ζ) :
    (0 : ℂ) ∈ closure (fwdHull (Strip.extPath w) s) := by
  obtain ⟨T', hsT', hcT'⟩ := exists_gt_continuousOn_extPath hw hs
  have hT'0 : 0 ≤ T' := s.coe_nonneg.trans hsT'.le
  have hAc : Continuous (A1Ref.stopDrv (Strip.extPath w) T') := A1Ref.continuous_stopDrv hcT' hT'0
  rw [LocalExt.fwdHull_congr_of_eqOn_of_lt s.coe_nonneg hsT' fun u hu => (A1Ref.stopDrv_eqOn _ T' hu).symm]
  refine ConformalImageFull.zero_mem_closure_fwdHull hAc ?_ hs0
  simp only [A1Ref.stopDrv, min_eq_left hT'0, max_self, Strip.extPath, Real.toNNReal_zero, hw0]

/-- **Disjoint prefixes before the contact.** For the large curve (driver `w₂` from `0`, force point `v₂` from
`x < 0`, lifetime `ζ₂`) and the frozen small hull (driver `w₁` from `x`, time `τ`), at a positive large time `s` before
their first contact, the small prefix `closure K₁(τ) ∪ {0}` and the large prefix shifted to `−x`, with `−x`, are
disjoint (A1-COMMON's `exists_rect_le` premise, frame of the small curve). -/
theorem disjoint_prefix_of_lt_contactTime {x : ℝ} (hx : x < 0) {w₁ w₂ v₂ : ℝ≥0 → ℝ} {ζ₂ : ℝ≥0∞}
    (hw₂ : ContinuousOn w₂ {t | (t : ℝ≥0∞) < ζ₂}) (hw₂0 : w₂ 0 = 0)
    (hv₂ : ContinuousOn v₂ {t | (t : ℝ≥0∞) < ζ₂})
    (hv₂eq : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ₂ → v₂ t = x + ∫ s in (0 : ℝ)..t, 2 / (v₂ s.toNNReal - w₂ s.toNNReal))
    {τ s : ℝ≥0} (hs0 : 0 < (s : ℝ))
    (hs : (s : ℝ≥0∞) < contactTime 0 (Strip.extPath w₂) (lifeEnd w₂ v₂ ζ₂) x (Strip.extPath w₁) τ) :
    Disjoint (closure (fwdHull (Strip.extPath w₁) τ) ∪ {0})
      (closure (fwdHull (Strip.extPath fun u => w₂ u + -x) s) ∪ {((-x : ℝ) : ℂ)}) := by
  have hsL : (s : ℝ≥0∞) < lifeEnd w₂ v₂ ζ₂ := hs.trans_le (min_le_left _ _)
  have hsl := A2X.P3.isStripLife_of_lt_lifeEnd hsL
  have hgood : IsGoodTime 0 (Strip.extPath w₂) (lifeEnd w₂ v₂ ζ₂) x (Strip.extPath w₁) τ s :=
    ⟨hs0, by rwa [ENNReal.ofReal_coe_nnreal]⟩
  have hd := disjoint_of_isGoodTime hgood
  rw [physHull_zero] at hd
  have hxK : (x : ℂ) ∉ closure (fwdHull (Strip.extPath w₂) s) :=
    notMem_closure_fwdHull_of_force hw₂ hv₂ hv₂eq hsl.1 fun r hr => (hsl.2 r hr).ne
  have h0K : (0 : ℂ) ∈ closure (fwdHull (Strip.extPath w₂) s) :=
    zero_mem_closure_fwdHull_extPath hw₂ hw₂0 hs0 hsl.1
  have eK : fwdHull (Strip.extPath fun u => w₂ u + -x) s =
      (fun z : ℂ => z + ((-x : ℝ) : ℂ)) '' fwdHull (Strip.extPath w₂) s :=
    ConformalImageFull.fwdHull_add_const (Strip.extPath w₂) (-x) s
  have hcont : Continuous fun z : ℂ => z + (x : ℂ) := continuous_id.add continuous_const
  -- translating by `x` maps both prefixes into the physical frame
  have hA : ∀ a ∈ closure (fwdHull (Strip.extPath w₁) τ), a + x ∈ closure (physHull x (Strip.extPath w₁) τ) :=
    fun a ha => map_mem_closure (f := fun z : ℂ => z + (x : ℂ)) hcont ha fun z hz => ⟨z, hz, rfl⟩
  have hB : ∀ b ∈ closure (fwdHull (Strip.extPath fun u => w₂ u + -x) s),
      b + x ∈ closure (fwdHull (Strip.extPath w₂) s) := fun b hb => by
    rw [eK] at hb
    refine map_mem_closure (f := fun z : ℂ => z + (x : ℂ)) hcont hb ?_
    rintro _ ⟨z, hz, rfl⟩
    simpa only [ofReal_neg, neg_add_cancel_right] using hz
  rw [Set.disjoint_left]
  rintro a (ha | ha) (hb | hb)
  · exact Set.disjoint_left.1 hd (hA a ha) (hB a hb)
  · rw [mem_singleton_iff] at hb
    subst hb
    have h0 := hA _ ha
    simp only [ofReal_neg, neg_add_cancel] at h0
    exact Set.disjoint_left.1 hd h0 h0K
  · rw [mem_singleton_iff] at ha
    subst ha
    have h := hB _ hb
    rw [zero_add] at h
    exact hxK h
  · rw [mem_singleton_iff] at ha hb
    rw [ha] at hb
    have : (x : ℂ) = 0 := by
      have h' := congrArg Neg.neg hb
      simpa only [neg_zero, ofReal_neg, neg_neg] using h'.symm
    exact hx.ne (by exact_mod_cast this)

end Det

/-! ### `hcov` for regular good Eight marginals -/

section Eight

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]
  {κ x : ℝ} {P₁ : Measure X} {P₂ : Measure Y} {𝓖₁ : Filtration ℝ≥0 mX} {𝓖₂ : Filtration ℝ≥0 mY}
  {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ} {VR₁ : Fin 2 → ℝ≥0 → X → ℝ} {B₁ : ℝ≥0 → X → ℝ}
  {ζ₁ : X → ℝ≥0∞} {W₂ : ℝ≥0 → Y → ℝ} {VL₂ : Fin 1 → ℝ≥0 → Y → ℝ} {VR₂ : Fin 0 → ℝ≥0 → Y → ℝ}
  {B₂ : ℝ≥0 → Y → ℝ} {ζ₂ : Y → ℝ≥0∞}

/-- **`hcov`: the cofinal rectangles exhaust every pre-contact configuration.** At a live sample (`τ < ζ₁`) every own
time of the large curve before its first contact with the frozen small hull has its clock below the raw cap of some
rectangle: a slightly later pre-contact time and the frozen time give disjoint prefixes
(`disjoint_prefix_of_lt_contactTime`), which lie in a member of the cofinal family (`exists_rect_le`); the clock up to
the protected large exit is finite (`eightRec_hfin`). -/
theorem eightRec_hcov (hκ8 : 8 ≤ κ) (hx : x < 0)
    (h₁ : IsRegMarginal (kh κ) ![0] ![0, -x] (smallEightRhoL κ) (smallEightRhoR κ) P₁ 𝓖₁ W₁ VL₁ VR₁ B₁ ζ₁)
    (hB₁ : ∀ ω, Continuous (B₁ · ω))
    (hg₁ : ∀ ω, GoodSmallEight (W₁ · ω) (fun i t => VL₁ i t ω) (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω))
    (h₂ : IsRegMarginal κ ![x] ![] ![0] ![] P₂ 𝓖₂ W₂ VL₂ VR₂ B₂ ζ₂) (hB₂ : ∀ ω, Continuous (B₂ · ω))
    (τ : X → ℝ≥0) (z : X × Y) (hlive : (τ z.1 : ℝ≥0∞) < ζ₁ z.1) :
    ∀ s : ℝ≥0, (s : ℝ≥0∞) < contactTime 0 (Strip.extPath (W₂ · z.2)) (lifeEnd (W₂ · z.2) (VL₂ 0 · z.2) (ζ₂ z.2)) x
        (Strip.extPath (W₁ · z.1)) (τ z.1) →
      ∃ m, A1Ref.imgClk 0 (Strip.extPath (W₂ · z.2)) x (Strip.extPath (W₁ · z.1)) (τ z.1) s ≤
        eightFstCap x W₁ ζ₁ W₂ VL₂ ζ₂ W₁ ζ₁ W₂ ζ₂ (τ z.1) m z := by
  have hx₂ : 0 < -x := by linarith
  obtain ⟨hw0, -, -, hcw, hcvL, -, -, -, -, -, -, -, -, hvLeq, -⟩ := id (h₂.path z.2)
  have hveq : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ₂ z.2 →
      VL₂ 0 t z.2 = x + ∫ s in (0 : ℝ)..t, 2 / (VL₂ 0 s.toNNReal z.2 - W₂ s.toNNReal z.2) := fun t ht => by
    simpa using hvLeq t ht 0
  have hex : ∀ s : ℝ≥0, (s : ℝ≥0∞) < contactTime 0 (Strip.extPath (W₂ · z.2))
      (lifeEnd (W₂ · z.2) (VL₂ 0 · z.2) (ζ₂ z.2)) x (Strip.extPath (W₁ · z.1)) (τ z.1) →
      ∃ m, (s : ℝ) < (fun m z => eightFstOwn x W₁ ζ₁ W₂ ζ₂ (τ z.1) m z) m z := by
    intro s hs
    obtain ⟨s', hss', hs'c⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hs
    have hss'' : s < s' := ENNReal.coe_lt_coe.1 hss'
    have hs'0 : 0 < (s' : ℝ) := lt_of_le_of_lt s.coe_nonneg (NNReal.coe_lt_coe.2 hss'')
    have hs'ζ : (s' : ℝ≥0∞) < ζ₂ z.2 :=
      (hs'c.trans_le (min_le_left _ _)).trans_le (A2X.P3.lifeEnd_le_lifetime _ _ _)
    have hdisj := disjoint_prefix_of_lt_contactTime hx hcw hw0 (hcvL 0) hveq hs'0 hs'c
    obtain ⟨m, hm₁, hm₂⟩ := exists_rect_le (pm := (![] : Fin 0 → ℝ)) hx₂ (h₁.path z.1).2.2.2.1 hcw hlive hs'ζ
      hdisj fun j => j.elim0
    have hm₁' : τ z.1 ≤ eightS₁ x W₁ ζ₁ m z.1 := hm₁
    have hm₂' : s' ≤ eightS₂ x W₂ ζ₂ m z.2 := hm₂
    refine ⟨m, ?_⟩
    simp only [eightFstOwn, hm₁', ↓reduceIte]
    exact lt_of_lt_of_le (NNReal.coe_lt_coe.2 hss'') (NNReal.coe_le_coe.2 hm₂')
  intro s hs
  obtain ⟨T₁, hT₁, hcT₁⟩ := exists_gt_continuousOn_extPath (h₁.path z.1).2.2.2.1 hlive
  have hcov := cover_capFst (X := X) (Y := Y) (live := fun t ω => (t : ℝ≥0∞) < ζ₁ ω) (xj := 0) (Wj := W₂)
    (ζj := fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) (xk := x) (Wk := W₁) (τ := τ) (z := z)
    (Tm := fun m z => eightFstOwn x W₁ ζ₁ W₂ ζ₂ (τ z.1) m z) hlive
    (fun T hT => A1Ref.continuousOn_extPath_Icc hcw (hT.trans_le (A2X.P3.lifeEnd_le_lifetime _ _ _))) hw0
    ⟨T₁, hT₁, hcT₁⟩ (h₁.path z.1).1 hex (fun m => eightRec_hfin hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ (τ := τ) m z)
  obtain ⟨m, hm⟩ := hcov s hs
  refine ⟨m, le_of_le_of_eq hm ?_⟩
  exact congrArg (fun c : ℝ≥0 => (c : ℝ)) (congrFun (eightFstCap_stop (VL₂ := VL₂) τ m) z).symm

end Eight

end InteractingSLE.ZhanGT4.A1ERec
