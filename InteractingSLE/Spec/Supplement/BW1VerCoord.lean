/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.BW1VerAtlas
import InteractingSLE.Spec.Supplement.BW1VerSample

/-!
# Measurable relative coordinates when the retained time is read from the record

Packet PROVE-BW1-INPUTS2. GB6's `SourceC.exists_relative_driver` with the fixed own time of the retained prefix
replaced by the record's own time `recS (rec ω)`: from a measurable record, a measurable continuous counterflow
driver version with a measurable trace version, a measurable continuous version `A` of the retained trace, and a
measurable set `M` of good samples (`IsGoodSample`), there are measurable relative coordinates `(D, L)` which are the
sample coordinates (`IsSampleCoord`) of every sample of `M` (`exists_coord`). The random own time enters through the
atlas `exists_measurable_driver_rand` and the contact events `measurableSet_lt_contactT`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Complex
open QuantumZipper (H fwdHull)
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.BW1Ver

open Exist.StagedLaw Supp8.GB6 Supp8.GB6.ReadD Sec7.PocketTraversal

theorem rpath_rdrv (r : RecData) : Ito.rpath (fun t : ℝ≥0 => rdrv r t) = rdrv r := rdrv_toNNReal r

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- A frozen retained prefix has the same image on every horizon beyond the stop. -/
theorem image_freeze_eq (A : ℝ≥0 → ℂ) {s N : ℝ≥0} (hsN : s ≤ N) :
    (fun v => A (min v s)) '' Icc 0 N = A '' Icc 0 s := by
  ext z
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨min v s, ⟨zero_le, min_le_right v s⟩, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v, ⟨zero_le, hv.2.trans hsN⟩, by simp only [min_eq_left hv.2]⟩

/-- **The contact events with a retained prefix of random length are measurable.** -/
theorem measurableSet_lt_contactT {Γ A : Ω → ℝ≥0 → ℂ} (hΓc : ∀ ω, Continuous (Γ ω))
    (hAc : ∀ ω, Continuous (A ω)) (hΓm : ∀ t, Measurable fun ω => Γ ω t)
    (hAm : ∀ t, Measurable fun ω => A ω t) {s : Ω → ℝ≥0} (hs : Measurable s) (T : ℝ≥0) :
    MeasurableSet {ω | (T : ℝ≥0∞) < contactT (Γ ω) (A ω) (s ω)} := by
  let Af : Ω → ℝ≥0 → ℂ := fun ω v => A ω (min v (s ω))
  have hAU : Measurable (Function.uncurry fun (t : ℝ≥0) (ω : Ω) => A ω t) :=
    measurable_uncurry_of_continuous_of_measurable (fun ω => hAc ω) hAm
  have hAfm : ∀ t, Measurable fun ω => Af ω t := fun t =>
    hAU.comp ((measurable_const.min hs).prodMk measurable_id)
  have hAfc : ∀ ω, Continuous (Af ω) := fun ω => (hAc ω).comp (continuous_id.min continuous_const)
  have he : {ω | (T : ℝ≥0∞) < contactT (Γ ω) (A ω) (s ω)} = ⋃ N : ℕ, {ω | s ω ≤ (N : ℝ≥0)} ∩
      {ω | (T : ℝ≥0∞) < firstContactTime (fun t => sphereInv (Γ ω t : OnePoint ℂ))
        ((fun u => (Af ω u : OnePoint ℂ)) '' Icc 0 (N : ℝ≥0))} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff]
    have himg : ∀ N : ℕ, s ω ≤ (N : ℝ≥0) → (fun u => (Af ω u : OnePoint ℂ)) '' Icc 0 (N : ℝ≥0) =
        (fun v => (A ω v : OnePoint ℂ)) '' Icc 0 (s ω) := by
      intro N hN
      have h := image_freeze_eq (A ω) hN
      rw [show (fun u => (Af ω u : OnePoint ℂ)) = (fun z : ℂ => (z : OnePoint ℂ)) ∘ fun v => A ω (min v (s ω))
        from rfl, image_comp, h, ← image_comp]
      rfl
    constructor
    · intro h
      obtain ⟨N, hN⟩ := exists_nat_ge (s ω)
      exact ⟨N, hN, by rw [himg N hN]; exact h⟩
    · rintro ⟨N, hN, h⟩
      rw [himg N hN] at h
      exact h
  rw [he]
  exact MeasurableSet.iUnion fun N => (measurableSet_le hs measurable_const).inter
    (SourceC.measurableSet_lt_firstContactTime hΓc hAfc hΓm hAfm T N)

/-- **Measurable relative coordinates of good samples, the retained time read from the record.** -/
theorem exists_coord {rec : Ω → RecData} (hrec : Measurable rec) {Wd : ℝ≥0 → Ω → ℝ}
    {Γ A : Ω → ℝ≥0 → ℂ} (hΓc : ∀ ω, Continuous (Γ ω))
    (hAc : ∀ ω, Continuous (A ω)) (hΓm : ∀ t, Measurable fun ω => Γ ω t)
    (hAm : ∀ t, Measurable fun ω => A ω t) {M : Set Ω} (hM : MeasurableSet M)
    (hgood : ∀ ω ∈ M, IsGoodSample (rec ω) (A ω) (Wd · ω) (Γ ω)) :
    ∃ (D : ℝ≥0 → Ω → ℝ) (L : Ω → ℝ≥0∞), (∀ t, Measurable (D t)) ∧ Measurable L ∧ (∀ ω, 0 < L ω) ∧
      (∀ ω, ContinuousOn (D · ω) {u | (u : ℝ≥0∞) < L ω}) ∧ (∀ ω, D 0 ω = 0) ∧
      AdaptedBefore (Filtration.const ℝ≥0 mΩ le_rfl) L D ∧ (∀ ω ∉ M, L ω = ⊤) ∧
      ∀ ω ∈ M, IsSampleCoord (rec ω) (A ω) (Wd · ω) (Γ ω) (D · ω) (L ω) := by
  classical
  let V : ℝ≥0 → Ω → ℝ := fun t ω => rdrv (rec ω) t
  have hVm : ∀ t, Measurable (V t) := fun t => (measurable_rdrv_apply t).comp hrec
  have hVc : ∀ ω, Continuous (V · ω) := fun ω => continuous_rdrv_nn (rec ω)
  have hV0 : ∀ ω, V 0 ω = 0 := fun ω => rdrv_zero (rec ω)
  have hVr : ∀ ω, Ito.rpath (V · ω) = rdrv (rec ω) := fun ω => rpath_rdrv (rec ω)
  let s : Ω → ℝ≥0 := fun ω => recS (rec ω)
  have hsm : Measurable s := measurable_recS.comp hrec
  let Tc : Ω → ℝ≥0∞ := fun ω => contactT (Γ ω) (A ω) (s ω)
  obtain ⟨T, hT, hcover⟩ := SourceC.exists_prefix_times
  let E : ℕ → Set Ω := fun n => M ∩ {ω | (T n : ℝ≥0∞) < Tc ω}
  have hEm : ∀ n, MeasurableSet (E n) := fun n =>
    hM.inter (measurableSet_lt_contactT hΓc hAc hΓm hAm hsm (T n))
  have hgeom : ∀ n ω, ω ∈ E n → Continuous ((fun ω t => Wd t ω) ω) ∧ (fun ω t => Wd t ω) ω 0 = 0 ∧
      IsGeneratingTrace ((fun ω t => Wd t ω) ω) ⊤ (Γ ω) ∧ ∃ p : ℂ,
        Tendsto (QuantumZipper.fwdMapInv (Ito.rpath (V · ω)) (s ω)) (𝓝[H] 0) (𝓝 p) ∧
        Disjoint (closure (fwdHull (Ito.rpath (V · ω)) (s ω)))
          (closure ((fun z : ℂ => -z⁻¹) '' fwdHull (Ito.rpath ((fun ω t => Wd t ω) ω)) (T n))) := by
    intro n ω hω
    have hg := hgood ω hω.1
    refine ⟨hg.cont, hg.zero, hg.ctrace, A ω (s ω), ?_, ?_⟩
    · rw [hVr]; exact hg.tip
    · rw [hVr]; exact hg.disjoint hω.2
  obtain ⟨D, L, hDm, hLm, hDc, hD0, -, hcov, hK⟩ :=
    exists_measurable_driver_rand hVm hVc hV0 hΓm hsm hEm (fun n ω hω => (hgood ω hω.1).pos) hT hgeom
  let D' : ℝ≥0 → Ω → ℝ := fun t ω => if ω ∈ M then D t ω else 0
  let L' : Ω → ℝ≥0∞ := fun ω => if ω ∈ M then L ω else ⊤
  have hD'm : ∀ t, Measurable (D' t) := fun t => Measurable.ite hM (hDm t) measurable_const
  have hL'm : Measurable L' := Measurable.ite hM hLm measurable_const
  have hpos : ∀ ω ∈ M, 0 < L ω := by
    intro ω hω
    obtain ⟨n, -, hn⟩ := hcover (Tc ω) 0 (by simpa only [ENNReal.coe_zero] using (hgood ω hω).contactT_pos)
    have hKn := (hK n ω ⟨hω, hn⟩ 0 (hT n)).2.1
    exact (show (0 : ℝ≥0∞) ≤ ENNReal.ofReal _ from zero_le).trans_lt hKn
  refine ⟨D', L', hD'm, hL'm, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ω
    by_cases hω : ω ∈ M
    · simpa only [L', hω, ↓reduceIte] using hpos ω hω
    · simp only [L', hω, ↓reduceIte]; exact ENNReal.zero_lt_top
  · intro ω
    by_cases hω : ω ∈ M
    · simpa only [D', L', hω, ↓reduceIte] using hDc ω
    · simp only [D', L', hω, ↓reduceIte]
      exact continuous_const.continuousOn
  · intro ω
    by_cases hω : ω ∈ M
    · simpa only [D', hω, ↓reduceIte] using hD0 ω
    · simp only [D', hω, ↓reduceIte]
  · intro t B hB
    exact (measurableSet_lt measurable_const hL'm).inter (hD'm t hB)
  · intro ω hω
    simp only [L', hω, ↓reduceIte]
  · intro ω hω
    have hD'e : (D' · ω) = (D · ω) := funext fun t => by simp only [D', hω, ↓reduceIte]
    have hL'e : L' ω = L ω := by simp only [L', hω, ↓reduceIte]
    rw [hD'e, hL'e]
    refine ⟨hDc ω, hD0 ω, hpos ω hω, ?_, ?_⟩
    · intro u hu
      obtain ⟨n, hn, t, ht, hut⟩ := hcov ω u hu
      refine ⟨t, (ENNReal.coe_lt_coe.2 ht).trans hn.2, ?_⟩
      have h := hut
      rw [hVr] at h
      exact h
    · intro t ht
      obtain ⟨n, htn, hn⟩ := hcover (Tc ω) t ht
      have hkt := hK n ω ⟨hω, hn⟩ t htn
      rw [hVr] at hkt
      exact hkt

end InteractingSLE.Theorem14.BW1Ver
