/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB11GateFinalEnclosure

/-! # GB11: exact single-wall compactified prefix arcs -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Filter Topology Metric Bornology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)
open InteractingSLE.YuanSimpleApprox (trMap)

namespace InteractingSLE.Theorem14.GB11Chart
open GW4Traverse GW4Reg GB11Conn

/-- The intrinsic compactified current image of the exit. At the original
physical target the image is the compactification point, rather than `mu 0`. -/
def prefixJunction (d : GateSetup) (α : ℝ≥0 → ℂ) (exit : ℝ≥0) : ℂ :=
  if exit = 0 then 0 else mu (forwardExt d.driver d.t (-(α exit)⁻¹))

/-- One exact compactified incoming prefix. The finite gate value is retained,
so its old-trace membership and physical exclusion can be proved separately. -/
structure CompactifiedPrefixArc (d : GateSetup) (α : ℝ≥0 → ℂ)
    (exit : ℝ≥0) (cut : ℝ≥0∞) where
  q : ℝ
  wall : ℝ → ℂ
  continuous : ContinuousOn wall (Icc 0 1)
  injective : InjOn wall (Icc 0 1)
  zero : wall 0 = mu q
  one : wall 1 = prefixJunction d α exit
  image : wall '' Icc 0 1 = selectedPrefixImage d α exit cut q
  gate_value : trMap d.driver 0 d.t q = if cut = ⊤ then 0 else -(α cut.toNNReal)⁻¹

/-- A lifted finite interval, reversed and compactified, realizes its exact
selected prefix, including the old trace value at the gate. -/
theorem exists_compactifiedPrefixArc_finite {d : GateSetup} {α : ℝ≥0 → ℂ}
    (hα : GB11.IsCompleteSimpleFlow α)
    (hrev : ∀ r r' : ℝ≥0, 0 < r → r < r' →
      GB11.firstVisit d.γ (α r') < GB11.firstVisit d.γ (α r))
    {exit cut : ℝ≥0} (hexit : 0 < exit) (hlt : exit < cut)
    (hcut : IsWallVisitCut d.γ α d.t (cut : ℝ≥0∞)) :
    Nonempty (CompactifiedPrefixArc d α exit (cut : ℝ≥0∞)) := by
  obtain ⟨q, β, hβc, hβi, hβH, hF, hβb, heq⟩ := exists_lift_finite_wall_cut
    d.continuous_driver d.driver_zero d.generating hα hrev hexit hlt hcut.2
  change (∀ u ∈ Icc (exit : ℝ) cut, trMap d.driver 0 d.t (β u) =
    -(α u.toNNReal)⁻¹) at hF
  change EqOn β (fun u => forwardExt d.driver d.t (-(α u.toNNReal)⁻¹))
    (Ico (exit : ℝ) cut) at heq
  let φ : ℝ → ℝ := fun u => cut - u * ((cut : ℝ) - exit)
  have hba : 0 < (cut : ℝ) - exit := sub_pos.2 (NNReal.coe_lt_coe.2 hlt)
  have hφc : Continuous φ := continuous_const.sub (continuous_id.mul continuous_const)
  have hφ : MapsTo φ (Icc 0 1) (Icc (exit : ℝ) cut) := by
    intro u hu
    constructor <;> dsimp [φ]
    · nlinarith [mul_le_mul_of_nonneg_right hu.2 hba.le]
    · nlinarith [mul_nonneg hu.1 hba.le]
  have hφ0 : φ 0 = cut := by simp [φ]
  have hφ1 : φ 1 = exit := by simp [φ]
  let b : ℝ → ℂ := fun u => mu (β (φ u))
  have hb0 : b 0 = mu q := by simp only [b, hφ0, hβb]
  have hb1 : b 1 = prefixJunction d α exit := by
    rw [prefixJunction, ite_eq_right hexit.ne']
    dsimp [b]
    rw [hφ1, heq ⟨le_rfl, NNReal.coe_lt_coe.2 hlt⟩]
    simp only [Real.toNNReal_coe]
  have hbimg : b '' Icc 0 1 = selectedPrefixImage d α exit (cut : ℝ≥0∞) q := by
    rw [selectedPrefixImage, ite_eq_right hexit.ne', union_empty]
    ext z
    constructor
    · rintro ⟨u, hu, rfl⟩
      by_cases hu0 : u = 0
      · exact Or.inl (by simpa only [mem_singleton_iff, hu0] using hb0)
      · have hpos : 0 < u := lt_of_le_of_ne hu.1 (Ne.symm hu0)
        have hφlt : φ u < cut := by dsimp [φ]; nlinarith [mul_pos hpos hba]
        have hφnn : 0 ≤ φ u := exit.2.trans (hφ hu).1
        have hr : (φ u).toNNReal ∈ {r : ℝ≥0 | 0 < r ∧ exit ≤ r ∧ (r : ℝ≥0∞) < cut} := by
          refine ⟨Real.toNNReal_pos.2 ((NNReal.coe_pos.2 hexit).trans_le (hφ hu).1),
            (Real.le_toNNReal_iff_coe_le hφnn).2 (hφ hu).1, ?_⟩
          rw [ENNReal.coe_lt_coe]
          exact (Real.toNNReal_lt_iff_lt_coe hφnn).2 hφlt
        refine Or.inr ⟨(φ u).toNNReal, hr, ?_⟩
        dsimp [b]
        rw [heq ⟨(hφ hu).1, hφlt⟩]
    · rintro (hz | ⟨r, hr, rfl⟩)
      · exact ⟨0, ⟨le_rfl, zero_le_one⟩, hb0.trans (mem_singleton_iff.1 hz).symm⟩
      · let u : ℝ := ((cut : ℝ) - r) / ((cut : ℝ) - exit)
        have hrb : (r : ℝ) < cut := NNReal.coe_lt_coe.2 (ENNReal.coe_lt_coe.1 hr.2.2)
        have hura : (exit : ℝ) ≤ r := NNReal.coe_le_coe.2 hr.2.1
        have hu : u ∈ Icc (0 : ℝ) 1 :=
          ⟨(div_pos (sub_pos.2 hrb) hba).le, (div_le_one hba).2 (by linarith)⟩
        have hφr : φ u = r := by dsimp [φ, u]; field_simp; ring
        refine ⟨u, hu, ?_⟩
        dsimp [b]
        rw [hφr, heq ⟨hura, hrb⟩]
        simp only [Real.toNNReal_coe]
  refine ⟨{
    q := q, wall := b,
    continuous := continuousOn_mu_Hbar.comp (hβc.comp hφc.continuousOn hφ)
      (fun u hu => hβH (hφ hu)),
    injective := ?_, zero := hb0, one := hb1, image := hbimg, gate_value := ?_ }⟩
  · intro u hu v hv he
    have hφeq := hβi (hφ hu) (hφ hv) (mu_injective he)
    dsimp [φ] at hφeq
    nlinarith
  · rw [ite_eq_right ENNReal.coe_ne_top, ENNReal.toNNReal_coe, ← hβb]
    simpa only [Real.toNNReal_coe] using hF cut ⟨(NNReal.coe_lt_coe.2 hlt).le, le_rfl⟩

/-- The unattained global cut at infinity also has an exact compactified
incoming arm whenever the exit is a positive wall parameter. -/
theorem exists_compactifiedPrefixArc_infinite {d : GateSetup} {α : ℝ≥0 → ℂ}
    (hα : GB11.IsCompleteSimpleFlow α)
    (hrev : ∀ r r' : ℝ≥0, 0 < r → r < r' →
      GB11.firstVisit d.γ (α r') < GB11.firstVisit d.γ (α r))
    {exit : ℝ≥0} (hexit : 0 < exit) (hcut : IsWallVisitCut d.γ α d.t ⊤) :
    Nonempty (CompactifiedPrefixArc d α exit ⊤) := by
  have hempty : wallHitParameters d.γ α d.t = ∅ := by
    ext r
    exact iff_of_false (fun hr => (not_le.2 ENNReal.coe_lt_top) ((hcut.2 r).1 hr))
      (notMem_empty r)
  obtain ⟨A, β, q, hAc, hAi, hA0, hA1, hAimg, hβc, hβi, hβH, hF, hβ1, heq⟩ :=
    exists_lift_infinite_wall_cut d.continuous_driver d.driver_zero d.generating
      hα hrev hexit hempty
  change (∀ u ∈ Icc (0 : ℝ) 1, trMap d.driver 0 d.t (β u) = A u) at hF
  change EqOn β (fun u => forwardExt d.driver d.t (A u)) (Ico (0 : ℝ) 1) at heq
  let b : ℝ → ℂ := fun u => mu (β (1 - u))
  have hrevI : MapsTo (fun u : ℝ => 1 - u) (Icc 0 1) (Icc 0 1) :=
    fun u hu => ⟨sub_nonneg.2 hu.2, sub_le_self _ hu.1⟩
  have hb0 : b 0 = mu q := by simp only [b, sub_zero, hβ1]
  have hb1 : b 1 = prefixJunction d α exit := by
    rw [prefixJunction, ite_eq_right hexit.ne']
    dsimp [b]
    rw [sub_self, heq ⟨le_rfl, zero_lt_one⟩]
    exact congrArg (fun z => mu (forwardExt d.driver d.t z)) hA0
  have hbimg : b '' Icc 0 1 = selectedPrefixImage d α exit ⊤ q := by
    rw [selectedPrefixImage, ite_eq_right hexit.ne', union_empty]
    ext z
    constructor
    · rintro ⟨u, hu, rfl⟩
      by_cases hu0 : u = 0
      · exact Or.inl (by simpa only [mem_singleton_iff, hu0] using hb0)
      · have hpos : 0 < u := lt_of_le_of_ne hu.1 (Ne.symm hu0)
        have hv : 1 - u ∈ Ico (0 : ℝ) 1 := ⟨(hrevI hu).1, by linarith⟩
        have hAne : A (1 - u) ≠ 0 := fun he => hv.2.ne
          (hAi (hrevI hu) ⟨zero_le_one, le_rfl⟩ (he.trans hA1.symm))
        have hm := hAimg ▸ mem_image_of_mem A (hrevI hu)
        rcases hm with ⟨_, ⟨r, hr, rfl⟩, he⟩ | he
        · refine Or.inr ⟨r, ⟨hexit.trans_le hr, hr, ENNReal.coe_lt_top⟩, ?_⟩
          dsimp [b]
          rw [heq hv]
          exact congrArg (fun z => mu (forwardExt d.driver d.t z)) he
        · exact False.elim (hAne he)
    · rintro (hz | ⟨r, hr, rfl⟩)
      · exact ⟨0, ⟨le_rfl, zero_le_one⟩, hb0.trans (mem_singleton_iff.1 hz).symm⟩
      · have hAne : -(α r)⁻¹ ≠ 0 := by
          intro he
          have hzero : α r = 0 := inv_eq_zero.1 (neg_eq_zero.1 he)
          exact hr.1.ne' (hα.2.1 (hzero.trans hα.2.2.1.symm))
        obtain ⟨v, hv, he⟩ : -(α r)⁻¹ ∈ A '' Icc 0 1 :=
          hAimg.symm ▸ Or.inl ⟨α r, ⟨r, hr.2.1, rfl⟩, rfl⟩
        have hv1 : v < 1 := lt_of_le_of_ne hv.2 (fun he1 => hAne (by rw [← he, he1, hA1]))
        refine ⟨1 - v, hrevI hv, ?_⟩
        dsimp [b]
        rw [show 1 - (1 - v) = v by ring, heq ⟨hv.1, hv1⟩]
        exact congrArg (fun z => mu (forwardExt d.driver d.t z)) he
  refine ⟨{
    q := q, wall := b,
    continuous := continuousOn_mu_Hbar.comp
      (hβc.comp (continuous_const.sub continuous_id).continuousOn hrevI)
      (fun u hu => hβH (hrevI hu)),
    injective := ?_, zero := hb0, one := hb1, image := hbimg, gate_value := ?_ }⟩
  · intro u hu v hv he
    have hh := hβi (hrevI hu) (hrevI hv) (mu_injective he)
    linarith
  · rw [ite_eq_left rfl, ← hβ1]
    exact (hF 1 ⟨zero_le_one, le_rfl⟩).trans hA1

/-- Both finite and infinite global cuts are realized for positive exits. -/
theorem exists_compactifiedPrefixArc_of_pos {d : GateSetup} {α : ℝ≥0 → ℂ}
    (hα : GB11.IsCompleteSimpleFlow α)
    (hrev : ∀ r r' : ℝ≥0, 0 < r → r < r' →
      GB11.firstVisit d.γ (α r') < GB11.firstVisit d.γ (α r))
    {exit : ℝ≥0} {cut : ℝ≥0∞} (hexit : 0 < exit) (hlt : (exit : ℝ≥0∞) < cut)
    (hcut : IsWallVisitCut d.γ α d.t cut) :
    Nonempty (CompactifiedPrefixArc d α exit cut) := by
  by_cases htop : cut = ⊤
  · subst cut
    exact exists_compactifiedPrefixArc_infinite hα hrev hexit hcut
  · have he := ENNReal.coe_toNNReal htop
    rw [← he] at hlt hcut ⊢
    exact exists_compactifiedPrefixArc_finite hα hrev hexit
      (ENNReal.coe_lt_coe.1 hlt) hcut

end InteractingSLE.Theorem14.GB11Chart
