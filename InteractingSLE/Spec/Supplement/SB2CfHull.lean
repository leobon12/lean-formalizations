/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2JtRule

/-!
# Hull and chosen-trace congruences for drivers agreeing before a time

Packet PROVE-SB2-CONDFIN (Target 1, the root record, step (b)). The forward hull `QuantumZipper.fwdHull W T` reads
the driver through the existence of forward solutions on `[0, T']` for every `T'`, so two drivers agreeing on
`[0, t₀]` with `T < t₀` have the same hull at `T` — no continuity is needed (the library's
`QuantumZipper.fwdHull_eq_of_eqOn` asks for continuous drivers). Hence:

* `isForwardSol_mono`, `isForwardSol_congr`, **`swallowTime_le_congr`**, **`fwdHull_congr`**;
* **`isGeneratingTrace_congr`**: generation up to `T` only sees the driver before `T`;
* **`trOf_congr`**: drivers with the same lifetime agreeing before it have the same chosen trace
  (`LuM.trOf`: the two defining predicates are equal, so are the choices);
* `pcPt_congr`, **`visitTime_congr`**.

All statements are deterministic (no input).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.SB.Cf

open QuantumZipper (IsForwardSol swallowTime fwdHull)

theorem isForwardSol_mono {W : ℝ → ℝ} {z : ℂ} {T T' : ℝ} {u : ℝ → ℂ} (h : IsForwardSol W z T u)
    (hT : T' ≤ T) : IsForwardSol W z T' u :=
  ⟨h.1.mono (Icc_subset_Icc le_rfl hT), fun t ht => h.2 t ⟨ht.1, ht.2.trans hT⟩⟩

theorem isForwardSol_congr {W W' : ℝ → ℝ} {z : ℂ} {T : ℝ} {u : ℝ → ℂ}
    (h : ∀ s ∈ Icc (0 : ℝ) T, W s = W' s) (hu : IsForwardSol W z T u) : IsForwardSol W' z T u :=
  ⟨hu.1, fun t ht => ⟨(hu.2 t ht).1, by rw [← h t ht]; exact (hu.2 t ht).2⟩⟩

/-- **Swallowing by time `T` only sees the driver on `[0, t₀]`, `T < t₀`.** -/
theorem swallowTime_le_congr {W W' : ℝ → ℝ} {T t₀ : ℝ} (hT0 : 0 ≤ T) (hT : T < t₀)
    (h : ∀ s ∈ Icc (0 : ℝ) t₀, W s = W' s) (z : ℂ) (hW : swallowTime W z ≤ ENNReal.ofReal T) :
    swallowTime W' z ≤ ENNReal.ofReal T := by
  unfold swallowTime at hW ⊢
  rw [sSup_le_iff] at hW ⊢
  rintro _ ⟨T', ⟨hT'0, u, hu⟩, rfl⟩
  by_contra hlt
  push Not at hlt
  have hTT' : T < T' := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hT0).1 hlt
  have hu' : IsForwardSol W z (min T' t₀) u :=
    isForwardSol_congr (fun s hs => (h s ⟨hs.1, hs.2.trans (min_le_right _ _)⟩).symm)
      (isForwardSol_mono hu (min_le_left _ _))
  have h1 := hW _ ⟨min T' t₀, ⟨le_min hT'0 (hT0.trans hT.le), u, hu'⟩, rfl⟩
  have h2 : min T' t₀ ≤ T := (ENNReal.ofReal_le_ofReal_iff hT0).1 h1
  have h3 : T < min T' t₀ := lt_min hTT' hT
  linarith

/-- **The forward hull at `T` only sees the driver on `[0, t₀]`, `T < t₀`** (no continuity). -/
theorem fwdHull_congr {W W' : ℝ → ℝ} {T t₀ : ℝ} (hT0 : 0 ≤ T) (hT : T < t₀)
    (h : ∀ s ∈ Icc (0 : ℝ) t₀, W s = W' s) : fwdHull W T = fwdHull W' T := by
  ext z
  simp only [QuantumZipper.fwdHull, mem_ofPred_eq]
  exact ⟨fun hz => ⟨hz.1, swallowTime_le_congr hT0 hT h z hz.2⟩,
    fun hz => ⟨hz.1, swallowTime_le_congr hT0 hT (fun s hs => (h s hs).symm) z hz.2⟩⟩

/-- **Generation up to `T` only sees the driver before `T`.** -/
theorem isGeneratingTrace_congr {w w' : ℝ≥0 → ℝ} {T : ℝ≥0∞}
    (h : ∀ s : ℝ≥0, (s : ℝ≥0∞) < T → w s = w' s) {η : ℝ≥0 → ℂ} (hη : IsGeneratingTrace w T η) :
    IsGeneratingTrace w' T η := by
  refine ⟨hη.1, hη.2.1, fun t ht => ?_⟩
  have hfill := hη.2.2 t ht
  obtain ⟨t₀, ht₀, ht₀T⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht
  have ht₀' : (t : ℝ) < (t₀ : ℝ) := by exact_mod_cast ENNReal.coe_lt_coe.1 ht₀
  have heq : fwdHull (fun s : ℝ => w s.toNNReal) t = fwdHull (fun s : ℝ => w' s.toNNReal) t := by
    refine fwdHull_congr t.2 ht₀' fun s hs => ?_
    have hs' : s.toNNReal ≤ t₀ := by
      rw [Real.toNNReal_le_iff_le_coe]
      exact hs.2
    exact h _ (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hs') ht₀T)
  rw [← heq]
  exact hfill

/-- **Drivers with the same lifetime agreeing before it have the same chosen trace.** -/
theorem trOf_congr {e e' : (ℝ≥0 → ℝ) × ℝ≥0∞} (h2 : e.2 = e'.2)
    (h1 : ∀ s : ℝ≥0, (s : ℝ≥0∞) < e.2 → e.1 s = e'.1 s) : LuM.trOf e = LuM.trOf e' := by
  have hP : (fun η : ℝ≥0 → ℂ => IsGeneratingTrace e.1 e.2 η ∧
      (e.2 = ⊤ → Tendsto (fun t => ‖η t‖) atTop atTop)) =
      (fun η : ℝ≥0 → ℂ => IsGeneratingTrace e'.1 e'.2 η ∧
        (e'.2 = ⊤ → Tendsto (fun t => ‖η t‖) atTop atTop)) := by
    funext η
    rw [← h2]
    exact propext ⟨fun h => ⟨isGeneratingTrace_congr h1 h.1, h.2⟩,
      fun h => ⟨isGeneratingTrace_congr (fun s hs => (h1 s hs).symm) h.1, h.2⟩⟩
  unfold LuM.trOf
  rw [hP]

theorem pcPt_congr (s : ExplState) {e e' : (ℝ≥0 → ℝ) × ℝ≥0∞} (h2 : e.2 = e'.2)
    (h1 : ∀ t : ℝ≥0, (t : ℝ≥0∞) < e.2 → e.1 t = e'.1 t) : Lk.pcPt s e = Lk.pcPt s e' := by
  funext t
  unfold Lk.pcPt
  rw [trOf_congr h2 h1]

theorem visitTime_congr (s : ExplState) {e e' : (ℝ≥0 → ℝ) × ℝ≥0∞} (h2 : e.2 = e'.2)
    (h1 : ∀ t : ℝ≥0, (t : ℝ≥0∞) < e.2 → e.1 t = e'.1 t) (R : ℝ) :
    Lk.visitTime s e R = Lk.visitTime s e' R := by
  unfold Lk.visitTime
  rw [pcPt_congr s h2 h1, h2]

end InteractingSLE.Theorem14.SB.Cf
