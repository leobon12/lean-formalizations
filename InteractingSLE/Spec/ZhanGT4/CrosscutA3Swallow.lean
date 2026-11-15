/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.CrosscutA3Meas
import InteractingSLE.Foundations.Loewner.RealPoints
import InteractingSLE.Foundations.SLE.SpaceFilling.SwallowReal
import QuantumZipper.Proofs.Loewner.Algebra

/-!
# A.3.2: the first swallowing time of `−1` is the end of the strip life

Packet PROVE-ZHAN-A34. Source: Astra, *Follow-up proofs and dependency audit*, §A.3.2
(`source/external/AstraIG1/ig1_followup_proofs.txt` L657–L667, ruling R38): "ordinary SLE stopped at `T_x` becomes
the strip chain". In the R36 form the end mark `v` of the strip evolution is the real Loewner flow of `−1` as long as
it stays left of the driver; so the strip life (`v < w`) is exactly the time interval before the first swallowing
time `T_{−1}`.

## Main results

* `isForwardSol_congr_Icc`, `realSwallowAt_congr_Icc`, `fwdHull_congr_of_lt`: forward solutions, real swallowing and
  hulls before `T` only depend on the driver before `T`;
* `isForwardSol_neg_one_of_lt`: while `v < w` on `[0, s]`, `v − w` is the forward solution from `−1` on `[0, s]`;
* `lt_of_lt_of_realSwallowAt`: before the first swallowing time of `−1`, `v < w`;
* **`isStripLife_iff_lt_of_realSwallowAt`**: for a mark path solving the Loewner equation from `−1` at every time and
  staying `≤ w`, chordal time `s` lies in the strip life iff `s < T_{−1}`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A34

open QuantumZipper

/-! ### Dependence on the driver before a time -/

theorem isForwardSol_congr_Icc {W₁ W₂ : ℝ → ℝ} {z : ℂ} {T : ℝ} {u : ℝ → ℂ}
    (h : ∀ r ∈ Icc (0 : ℝ) T, W₁ r = W₂ r) : IsForwardSol W₁ z T u ↔ IsForwardSol W₂ z T u := by
  unfold IsForwardSol
  refine and_congr Iff.rfl (forall₂_congr fun t ht => ?_)
  rw [h t ht]

theorem realSwallowAt_congr_Icc {W₁ W₂ : ℝ → ℝ} {x σ : ℝ} (h : ∀ r ∈ Icc (0 : ℝ) σ, W₁ r = W₂ r) :
    RealSwallowAt W₁ x σ ↔ RealSwallowAt W₂ x σ := by
  have hs : ∀ s ∈ Icc (0 : ℝ) σ, ∀ u, IsForwardSol W₁ (x : ℂ) s u ↔ IsForwardSol W₂ (x : ℂ) s u :=
    fun s hs u => isForwardSol_congr_Icc fun r hr => h r ⟨hr.1, hr.2.trans hs.2⟩
  unfold RealSwallowAt
  refine and_congr Iff.rfl (and_congr ?_ ?_)
  · refine forall₂_congr fun s hs' => ?_
    exact exists_congr fun u => hs s ⟨hs'.1, hs'.2.le⟩ u
  · exact not_congr (exists_congr fun u => isForwardSol_congr_Icc h)

/-- **Hulls before `T` only depend on the driver before `T`.** -/
theorem fwdHull_congr_of_lt {W₁ W₂ : ℝ → ℝ} {T₀ t : ℝ} (ht : 0 ≤ t) (htT : t < T₀)
    (h : ∀ r ∈ Ico (0 : ℝ) T₀, W₁ r = W₂ r) : fwdHull W₁ t = fwdHull W₂ t := by
  have key : ∀ {V₁ V₂ : ℝ → ℝ}, (∀ r ∈ Ico (0 : ℝ) T₀, V₁ r = V₂ r) →
      ∀ z, z ∈ fwdHull V₁ t → z ∈ fwdHull V₂ t := by
    intro V₁ V₂ hV z hz
    rw [LoewnerAlgebra.mem_fwdHull_iff ht] at hz ⊢
    refine ⟨hz.1, fun T hT ⟨u, hu⟩ => ?_⟩
    by_contra hlt
    have hlt := not_le.1 hlt
    set T'' := min T ((t + T₀) / 2) with hT''
    have htT'' : t < T'' := lt_min hlt (by linarith)
    have hT''T₀ : T'' < T₀ := (min_le_right _ _).trans_lt (by linarith)
    have hu'' := QuantumZipper.isForwardSol_restrict hu (by linarith) (min_le_left _ _)
    have hu1 : IsForwardSol V₁ z T'' u :=
      (isForwardSol_congr_Icc fun r hr => hV r ⟨hr.1, hr.2.trans_lt hT''T₀⟩).2 hu''
    have := hz.2 T'' (by linarith) ⟨u, hu1⟩
    linarith
  ext z
  exact ⟨key h z, key (fun r hr => (h r hr).symm) z⟩

/-! ### The end mark is the flow of `−1` while it is left of the driver -/

section Mark

variable {w v : ℝ≥0 → ℝ}

/-- While `v < w` on `[0, s]`, `v − w` is the centred forward solution from `−1`. -/
theorem isForwardSol_neg_one_of_lt (hw : Continuous w) (hv : Continuous v)
    (hveq : ∀ t : ℝ≥0, v t = -1 + ∫ r in (0 : ℝ)..t, 2 / (v r.toNNReal - w r.toNNReal)) {s : ℝ}
    (hlt : ∀ r ∈ Icc (0 : ℝ) s, Strip.extPath v r < Strip.extPath w r) :
    IsForwardSol (Strip.extPath w) (((-1 : ℝ)) : ℂ) s
      (fun r => ((Strip.extPath v r - Strip.extPath w r : ℝ) : ℂ)) := by
  refine ⟨(Complex.continuous_ofReal.comp ((hv.sub hw).comp continuous_real_toNNReal)).continuousOn,
    fun t ht => ⟨Complex.ofReal_ne_zero.2 (sub_ne_zero.2 (hlt t ht).ne), ?_⟩⟩
  have h1 : (∫ r in (0 : ℝ)..t, (2 : ℂ) / ((Strip.extPath v r - Strip.extPath w r : ℝ) : ℂ)) =
      ((∫ r in (0 : ℝ)..t, 2 / (v r.toNNReal - w r.toNNReal) : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr fun r _ => ?_
    simp only [Strip.extPath]
    push_cast; rfl
  have h2 := hveq t.toNNReal
  rw [Real.coe_toNNReal _ ht.1] at h2
  rw [h1]
  simp only [Strip.extPath]
  rw [h2]
  push_cast; ring

/-- **Before the first swallowing time of `−1`, the mark stays strictly left of the driver.** -/
theorem lt_of_lt_of_realSwallowAt (hw : Continuous w) (hv : Continuous v) (hw0 : w 0 = 0)
    (hveq : ∀ t : ℝ≥0, v t = -1 + ∫ r in (0 : ℝ)..t, 2 / (v r.toNNReal - w r.toNNReal))
    (hle : ∀ t, v t ≤ w t) {σ : ℝ} (hσ : RealSwallowAt (Strip.extPath w) (-1) σ) {s : ℝ} (hs : 0 ≤ s)
    (hsσ : s < σ) : ∀ r ∈ Icc (0 : ℝ) s, Strip.extPath v r < Strip.extPath w r := by
  have hW : Continuous (Strip.extPath w) := hw.comp continuous_real_toNNReal
  have hV : Continuous (Strip.extPath v) := hv.comp continuous_real_toNNReal
  obtain ⟨u, hu⟩ := hσ.2.1 s ⟨hs, hsσ⟩
  by_contra hcon
  push Not at hcon
  set A : Set ℝ := {r | r ∈ Icc (0 : ℝ) s ∧ Strip.extPath w r ≤ Strip.extPath v r} with hA
  have hAne : A.Nonempty := by obtain ⟨r, hr, hr'⟩ := hcon; exact ⟨r, hr, hr'⟩
  have hAcl : IsClosed A := isClosed_Icc.inter (isClosed_le hW hV)
  have hAbdd : BddBelow A := ⟨0, fun r hr => hr.1.1⟩
  set τ := sInf A with hτ
  have hτA : τ ∈ A := hAcl.csInf_mem hAne hAbdd
  have hv0 : Strip.extPath v 0 = -1 := by
    have := hveq 0; simp only [NNReal.coe_zero, intervalIntegral.integral_same, add_zero] at this
    simp [Strip.extPath, this]
  have hw0' : Strip.extPath w 0 = 0 := by simp [Strip.extPath, hw0]
  have hτ0 : 0 < τ := by
    rcases hτA.1.1.eq_or_lt with h | h
    · have := hτA.2; rw [← h, hv0, hw0'] at this; norm_num at this
    · exact h
  have hbelow : ∀ r ∈ Ico (0 : ℝ) τ, Strip.extPath v r < Strip.extPath w r := by
    intro r hr
    by_contra hge
    exact absurd (csInf_le hAbdd ⟨⟨hr.1, hr.2.le.trans hτA.1.2⟩, not_lt.1 hge⟩) (not_le.2 hr.2)
  -- `u` agrees with `v − w` on `[0, τ)`, hence at `τ`
  set Y : ℝ → ℂ := fun r => ((Strip.extPath v r - Strip.extPath w r : ℝ) : ℂ) with hY
  have heq : EqOn u Y (Ico 0 τ) := by
    intro r hr
    have hY' := isForwardSol_neg_one_of_lt hw hv hveq (s := r) fun q hq =>
      hbelow q ⟨hq.1, hq.2.trans_lt hr.2⟩
    have hur := QuantumZipper.isForwardSol_restrict hu hr.1 (hr.2.le.trans hτA.1.2)
    exact eqOn_of_isForwardSol hW hur hY' ⟨hr.1, le_rfl⟩
  have hYc : Continuous Y := Complex.continuous_ofReal.comp (hV.sub hW)
  have heqτ : EqOn u Y (Icc 0 τ) :=
    heq.of_subset_closure (hu.1.mono (Icc_subset_Icc_right hτA.1.2)) hYc.continuousOn Ico_subset_Icc_self
      (by rw [closure_Ico hτ0.ne])
  have hzero : Y τ = 0 := by
    have h1 := hτA.2
    have h2 : Strip.extPath v τ ≤ Strip.extPath w τ := hle _
    simp only [hY, Complex.ofReal_eq_zero, sub_eq_zero]
    exact le_antisymm h2 h1
  exact (hu.2 τ hτA.1).1 (by rw [heqτ ⟨hτ0.le, le_rfl⟩, hzero])

/-- **The strip life is the time before the first swallowing of `−1`.** -/
theorem isStripLife_iff_lt_of_realSwallowAt (hw : Continuous w) (hv : Continuous v) (hw0 : w 0 = 0)
    (hveq : ∀ t : ℝ≥0, v t = -1 + ∫ r in (0 : ℝ)..t, 2 / (v r.toNNReal - w r.toNNReal))
    (hle : ∀ t, v t ≤ w t) {σ : ℝ} (hσ : RealSwallowAt (Strip.extPath w) (-1) σ) (s : ℝ≥0) :
    Strip.IsStripLife w v ⊤ s ↔ (s : ℝ) < σ := by
  constructor
  · intro hs
    by_contra hge
    have hge := not_lt.1 hge
    have hsol := isForwardSol_neg_one_of_lt hw hv hveq (s := s) fun r hr => by
      have := hs.2 r.toNNReal (Real.toNNReal_le_iff_le_coe.2 hr.2)
      simpa [Strip.extPath] using this
    exact hσ.2.2 ⟨_, QuantumZipper.isForwardSol_restrict hsol hσ.1.le hge⟩
  · intro hs
    refine ⟨ENNReal.coe_lt_top, fun r hr => ?_⟩
    have := lt_of_lt_of_realSwallowAt hw hv hw0 hveq hle hσ s.coe_nonneg hs r ⟨r.coe_nonneg, by exact_mod_cast hr⟩
    simpa [Strip.extPath] using this

end Mark

end InteractingSLE.ZhanGT4.A34
