/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7PocketStop
import InteractingSLE.Spec.Sec7.Lemma725RefMarksPocket

/-!
# Aux. lemma 131's two-seed pocket: the stop data `R7PocketStop` consumes, with the walls' union law

Packet PROVE-R7-AUX131. Specification §7.4.1, Aux. lemma 131 (`source/spec/p385-432.md` L516–L548, pp. 414–416) and
Theorem R.7 (`source/spec/p433-480.md` L1050–L1068, pp. 477–478: "If neither side is outer, at least one is extremal and
the same claims are already the contained reference of Aux. 131").

PROVE-R7POCKET's named input `R7Pocket.R7PocketStopStatement κ r_L r_R Good` asks, for one two-seed pocket, for the
union law and Aux. lemma 124's exterior decomposition at ONE σ-algebra that also records the exterior projection.
PROVE-LEMMA725REF6 built that σ-algebra from the walls' σ-algebra `𝓦` alone for Lemma 7.25's words
(`Lemma725RefMarks.pocketChartFieldStatement_of_stop_marks`). This file does the same for the constant two-seed word
`SLE_κ(r_L; r_R)` (no distant marks; marks `LP.twoSeedXL`, `LP.twoSeedXR`):

* **`r7PocketStopStatement_of_stop_marks`**: `R7PocketStopStatement κ r_L r_R Good` from one two-seed pocket with the
  union law at the walls' `𝓦`, the pocket-inclusion events walls' events (`hCin`), the two-seed side limits, `Good`,
  a standard Borel record `E₀` generating `𝓦` up to null sets, Proposition 5.13 and the measurable erasure for `𝓦`; the
  record σ-algebra of the conclusion is `marksSigma 𝓦 h₁` (Aux. lemma 124's exterior projection, R68 as amended in R69);
* `pocketChartTwoSeedStatement_of_stop_marks`: the same concluding `PocketChartTwoSeedStatement`.

Conditional helpers; no source theorem is replaced. Ruling R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any result taking them as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (H chiC fwdHull)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open SupercriticalConformalCovariance (IsConformalBijection)
open SupercriticalConformalCovariance.GM24 (smoothDist)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R7Aux131

open PocketTraversal Lemma71C LawUnique PocketStop PocketStopField Lemma725RefChart Lemma725RefSafe PocketCoupling
  Lemma725RefRecovery PocketUnionPt LocalSets WholeField Lemma725RefMarks R7Pocket

universe u

section Stop

variable {Ω : Type u} {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **`R7PocketStopStatement κ r_L r_R Good` from one two-seed pocket, with the union law at the walls' σ-algebra and
the exterior decomposition built inside** (Aux. lemma 124 with R68's enlarged record; the two-seed form of
`Lemma725RefMarks.pocketChartFieldStatement_of_stop_marks`). The record σ-algebra of the conclusion is
`marksSigma 𝓦 h₁ = 𝓦 ∨ σ(h₁)`, `h₁` the germ version of the exterior projection of `ℍ ∖ C`. -/
theorem r7PocketStopStatement_of_stop_marks [StandardBorelSpace Ω] [IsProbabilityMeasure P] {κ rL rR : ℝ}
    {Good : (ℝ≥0 → ℝ) → ℝ≥0∞ → Prop}
    (h𝓦 : 𝓦 ≤ mΩ) {A : Set Ω} (hA : MeasurableSet[𝓦] A) (hPA : 0 < P A) {γ : Ω → ℝ → ℂ}
    (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω)) (hγm : ∀ u, 0 ≤ u → Measurable fun ω : A => γ ω u)
    (hunb : ∀ ω ∈ A, ∀ M : ℝ, ∃ u, 0 ≤ u ∧ γ ω u ∈ H ∧ M < ‖γ ω u‖)
    {C : Ω → Set ℂ} (hCo : ∀ ω ∈ A, IsOpen (C ω)) (hCH : ∀ ω ∈ A, C ω ⊆ H) {ψ : Ω → ℂ → ℂ}
    (hψ : ∀ ω ∈ A, IsConformalBijection (ψ ω) (C ω) H) (hCm : ∀ z, MeasurableSet[𝓦] {ω | ω ∈ A ∧ z ∈ C ω})
    (hψm : ∀ z, Measurable[𝓦] ({ω | ω ∈ A ∧ z ∈ C ω}.indicator fun ω => ψ ω z))
    (hCin : ∀ U : Set ℂ, IsOpen U → U ⊆ H → MeasurableSet[𝓦] {ω | ω ∈ A ∧ U ⊆ C ω})
    {F : ℝ≥0 → Ω → Set ℂ}
    (hFo : ∀ q : ℝ≥0, ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) → IsOpen (H \ F q ω))
    (hgeo : ∀ q : ℝ≥0, ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) →
      ψ ω '' (C ω ∩ (H \ F q ω)) = H \ fwdHull (fun s : ℝ => segDriver (γ ω) s.toNNReal) q)
    {h₀ : Ω → DistOn upperHalfPlaneOpens} (hh₀ : IsZeroBoundaryGFF upperHalfPlaneOpens h₀ P) {u : ℂ → ℝ}
    (hu : InnerProductSpace.HarmonicOnNhd u H) (hub : ∃ M : ℝ, ∀ z ∈ H, |u z| ≤ M) {n : Ω → ℤ}
    (hn : Measurable[𝓦] n) {a : ℝ} (hU : ∀ q : ℝ≥0, PocketStopUnionLaw 𝓦 P A γ C (F q) h₀ q)
    (hside : ∀ q : ℝ≥0, PocketStopSideLimit κ (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) P A γ
      (fun _ => LP.twoSeedXL) (fun _ => LP.twoSeedXR) (fun ω => shiftChart (pChart A C ψ ω) (n ω)) a h₀ u
      (activeCompl A γ (fun ω => shiftChart (pChart A C ψ ω) (n ω)) q) q)
    (hGood : ∀ᵐ ω ∂P, ω ∈ A → capLife (γ ω) = ⊤ → Good (fun t => segDriver (γ ω) t) ⊤)
    {ε₀ : Type u} [MeasurableSpace ε₀] [StandardBorelSpace ε₀] {E₀ : Ω → ε₀} (hE₀ : Measurable[𝓦] E₀)
    (hgen : 𝓦 ≤ MeasurableSpace.comap E₀ inferInstance ⊔ Ito.nullSets P) {η : Ω → ℝ → ℂ}
    (h513 : ∃ Γ' : Ω → ℝ≥0 → ℂ, (∀ t, StronglyMeasurable[MeasurableSpace.comap
      (fun ω => h₀ ω + smoothDist upperHalfPlaneOpens u) inferInstance] fun ω => Γ' ω t) ∧
      ∀ᵐ ω ∂P, Γ' ω = fun t : ℝ≥0 => η ω t)
    (hers : PocketErasure 𝓦 P A γ (fun _ => LP.twoSeedXL) (fun _ => LP.twoSeedXR) η) :
    R7PocketStopStatement.{u} κ rL rR Good := by
  have hpre : ∀ q : ℝ≥0, locPrefixSigma 𝓦 A γ q ≤ mΩ := locPrefixSigma_le h𝓦 hA hγ hγm
  have hlive : ∀ ω ∈ A, ((0 : ℝ≥0) : ℝ≥0∞) < capLife (γ ω) := fun ω hω => by
    simpa using PocketPhaseMeans.capLife_pos (hγ ω hω)
  -- the hull at relative time `0` misses the pocket
  have hF0 : ∀ ω ∈ A, Disjoint (F 0 ω) (C ω) := by
    intro ω hω
    have h0 := hgeo 0 ω hω (hlive ω hω)
    have hemp : fwdHull (Ito.rpath (segDriver (γ ω))) 0 = ∅ :=
      Coupling.MartMeans2.fwdHull_rpath_zero (hγ ω hω).segDriver_spec.2.1 (PocketPhaseMeans.capLife_pos (hγ ω hω))
    rw [NNReal.coe_zero, show (fun s : ℝ => segDriver (γ ω) s.toNNReal) = Ito.rpath (segDriver (γ ω)) from rfl,
      hemp, sdiff_empty] at h0
    refine Set.disjoint_right.2 fun z hzC hzF => ?_
    have hz : ψ ω z ∈ ψ ω '' (C ω ∩ (H \ F 0 ω)) := by
      rw [h0]
      exact (hψ ω hω).2.mapsTo hzC
    obtain ⟨w, ⟨hwC, hwF⟩, hw⟩ := hz
    have hwz : w = z := (hψ ω hω).2.injOn hwC hzC hw
    exact hwF.2 (hwz ▸ hzF)
  -- the decomposition set: the union-law set at relative time `0`
  have hE₀eq : liveExt A γ C (F 0) 0 = extA A C := by
    funext ω
    by_cases hω : ω ∈ A
    · rw [liveExt_of_live ⟨hω, hlive ω hω⟩, extA_of_mem hω, extHullSet]
      congr 1
      exact union_eq_left.2 fun z hz => Set.disjoint_left.1 (hF0 ω hω) hz
    · rw [liveExt_of_not_live fun h => hω h.1, extA_of_notMem hω]
  have hE₀m : Measurable[𝓦, hittingSigma] (extA A C) := measurable_extA hA hCin
  obtain ⟨E0, hE0m, hE0loc, hE0eq⟩ := hU 0
  have hloc0 : IsHistoryAvoidanceLocal (locPrefixSigma 𝓦 A γ 0) (extA A C) h₀ P := by
    rw [← hE₀eq]
    exact isHistoryAvoidanceLocal_liveExt (measurableSet_live (𝓦 := 𝓦) A γ 0) hE0loc hE0eq
  have hdiff : ∀ ω ∈ A, H \ extA A C ω = C ω := fun ω hω => by
    rw [extA_of_mem hω]
    ext z
    simp only [Set.mem_sdiff, mem_inter_iff, mem_compl_iff, not_and, not_not]
    exact ⟨fun h => h.2 h.1, fun h => ⟨hCH ω hω h, fun _ => h⟩⟩
  have hAc : ∀ᵐ ω ∂P, extA A C ω ⊆ H ∧ IsOpen (H \ extA A C ω) := Eventually.of_forall fun ω => by
    by_cases hω : ω ∈ A
    · refine ⟨by rw [extA_of_mem hω]; exact inter_subset_left, ?_⟩
      rw [hdiff ω hω]
      exact hCo ω hω
    · rw [extA_of_notMem hω, sdiff_self]
      exact ⟨subset_rfl, isOpen_empty⟩
  obtain ⟨h₁, hh₁m, hdecall⟩ := exists_pocketExteriorDecomp hh₀ (hE₀m.mono h𝓦 le_rfl) (hpre 0) hloc0 hAc u
  -- the record σ-algebra `𝓦 ∨ σ(h₁)`
  have hh₁mΩ : Measurable h₁ := hh₁m.mono (germSigma_le (hE₀m.mono h𝓦 le_rfl) hh₀.measurable) le_rfl
  have h𝓦𝓦' : 𝓦 ≤ marksSigma 𝓦 h₁ := le_sup_left
  have hh₁𝓦' : Measurable[marksSigma 𝓦 h₁] h₁ := (comap_measurable h₁).mono le_sup_right le_rfl
  have h𝓦'le : marksSigma 𝓦 h₁ ≤ mΩ := sup_le h𝓦 hh₁mΩ.comap_le
  have hdec : @PocketExteriorDecomp Ω (marksSigma 𝓦 h₁) mΩ P A C
      (fun ω => h₀ ω + smoothDist upperHalfPlaneOpens u) :=
    hdecall (marksSigma 𝓦 h₁)
      (sup_le ((le_sup_left : 𝓦 ≤ locPrefixSigma 𝓦 A γ 0).trans le_sup_right) (hh₁m.comap_le.trans le_sup_left))
      (hE₀m.mono h𝓦𝓦' le_rfl) hh₁𝓦' A C fun ω hω => (hdiff ω hω).subset
  -- the union law with the enlarged marks at every relative time
  have hU' : ∀ q : ℝ≥0, PocketStopUnionLaw (marksSigma 𝓦 h₁) P A γ C (F q) h₀ q := by
    intro q
    obtain ⟨Eq, hEqm, hEqloc, hEqeq⟩ := hU q
    have hLq := measurableSet_live (𝓦 := 𝓦) A γ q
    have hlocq := isHistoryAvoidanceLocal_liveExt hLq hEqloc hEqeq
    have hmq := measurable_liveExt (hpre q _ hLq) hEqm hEqeq
    have hsub : ∀ ω, extA A C ω ∩ H ⊆ liveExt A γ C (F q) q ω := by
      intro ω z hz
      by_cases hl : ω ∈ A ∧ (q : ℝ≥0∞) < capLife (γ ω)
      · rw [liveExt_of_live hl]
        rw [extA_of_mem hl.1] at hz
        exact ⟨hz.1.1, Or.inl hz.1.2⟩
      · rw [liveExt_of_not_live hl]
        exact hz.2
    have hME := isHistoryAvoidanceLocal_sup_germSigma hh₀ (hpre q) hmq hlocq
      (hE₀m.mono (le_sup_left : 𝓦 ≤ locPrefixSigma 𝓦 A γ q) le_rfl) hsub
    have hle : locPrefixSigma (marksSigma 𝓦 h₁) A γ q ≤ locPrefixSigma 𝓦 A γ q ⊔ germSigma (extA A C) h₀ := by
      unfold locPrefixSigma marksSigma
      exact sup_le (sup_le (le_sup_left.trans le_sup_left) (hh₁m.comap_le.trans le_sup_right))
        (le_sup_right.trans le_sup_left)
    exact ⟨liveExt A γ C (F q) q, hmq, fun U G hUH hG hd M hM => hME U G hUH hG hd M (hle M hM),
      fun ω hω hq => liveExt_of_live ⟨hω, hq⟩⟩
  -- the record
  have hE₀' : Measurable[marksSigma 𝓦 h₁] fun ω => (E₀ ω, h₁ ω) := (hE₀.mono h𝓦𝓦' le_rfl).prodMk hh₁𝓦'
  have hgen' : marksSigma 𝓦 h₁ ≤
      MeasurableSpace.comap (fun ω => (E₀ ω, h₁ ω)) inferInstance ⊔ Ito.nullSets P := by
    have h1 : MeasurableSpace.comap E₀ inferInstance ≤
        MeasurableSpace.comap (fun ω => (E₀ ω, h₁ ω)) inferInstance :=
      (show Measurable[MeasurableSpace.comap (fun ω => (E₀ ω, h₁ ω)) inferInstance] E₀ from
        measurable_fst.comp (comap_measurable _)).comap_le
    have h2 : MeasurableSpace.comap h₁ inferInstance ≤
        MeasurableSpace.comap (fun ω => (E₀ ω, h₁ ω)) inferInstance :=
      (show Measurable[MeasurableSpace.comap (fun ω => (E₀ ω, h₁ ω)) inferInstance] h₁ from
        measurable_snd.comp (comap_measurable _)).comap_le
    exact sup_le (hgen.trans (sup_le_sup_right h1 _)) (h2.trans le_sup_left)
  have hers' : PocketErasure (marksSigma 𝓦 h₁) P A γ (fun _ => LP.twoSeedXL) (fun _ => LP.twoSeedXR) η := by
    obtain ⟨ε, mε, hSB, E, G, hEm, hG, hae⟩ := hers
    exact ⟨ε, mε, hSB, E, G, hEm.mono h𝓦𝓦' le_rfl, hG, hae⟩
  exact ⟨Ω, marksSigma 𝓦 h₁, mΩ, inferInstance, P, inferInstance, A, γ, C, ψ, F, h₀, u, n, a,
    ε₀ × DistOn upperHalfPlaneOpens, inferInstance, inferInstance, fun ω => (E₀ ω, h₁ ω), η, h𝓦'le,
    h𝓦𝓦' _ hA, hPA, hγ, hγm, hunb, hCo, hCH, hψ, fun z => h𝓦𝓦' _ (hCm z), fun z => (hψm z).mono h𝓦𝓦' le_rfl,
    hFo, hgeo, hh₀, hu, hub, hn.mono h𝓦𝓦' le_rfl, hU', hside, hGood, hdec, hE₀', hgen', h513, hers'⟩

/-- **`PocketChartTwoSeedStatement κ r_L r_R Good` from one two-seed pocket with the walls' union law**
(`r7PocketStopStatement_of_stop_marks` and `R7Pocket.pocketChartTwoSeedStatement_of_r7PocketStop`). -/
theorem pocketChartTwoSeedStatement_of_stop_marks [StandardBorelSpace Ω] [IsProbabilityMeasure P] {κ rL rR : ℝ}
    {Good : (ℝ≥0 → ℝ) → ℝ≥0∞ → Prop}
    (h𝓦 : 𝓦 ≤ mΩ) {A : Set Ω} (hA : MeasurableSet[𝓦] A) (hPA : 0 < P A) {γ : Ω → ℝ → ℂ}
    (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω)) (hγm : ∀ u, 0 ≤ u → Measurable fun ω : A => γ ω u)
    (hunb : ∀ ω ∈ A, ∀ M : ℝ, ∃ u, 0 ≤ u ∧ γ ω u ∈ H ∧ M < ‖γ ω u‖)
    {C : Ω → Set ℂ} (hCo : ∀ ω ∈ A, IsOpen (C ω)) (hCH : ∀ ω ∈ A, C ω ⊆ H) {ψ : Ω → ℂ → ℂ}
    (hψ : ∀ ω ∈ A, IsConformalBijection (ψ ω) (C ω) H) (hCm : ∀ z, MeasurableSet[𝓦] {ω | ω ∈ A ∧ z ∈ C ω})
    (hψm : ∀ z, Measurable[𝓦] ({ω | ω ∈ A ∧ z ∈ C ω}.indicator fun ω => ψ ω z))
    (hCin : ∀ U : Set ℂ, IsOpen U → U ⊆ H → MeasurableSet[𝓦] {ω | ω ∈ A ∧ U ⊆ C ω})
    {F : ℝ≥0 → Ω → Set ℂ}
    (hFo : ∀ q : ℝ≥0, ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) → IsOpen (H \ F q ω))
    (hgeo : ∀ q : ℝ≥0, ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) →
      ψ ω '' (C ω ∩ (H \ F q ω)) = H \ fwdHull (fun s : ℝ => segDriver (γ ω) s.toNNReal) q)
    {h₀ : Ω → DistOn upperHalfPlaneOpens} (hh₀ : IsZeroBoundaryGFF upperHalfPlaneOpens h₀ P) {u : ℂ → ℝ}
    (hu : InnerProductSpace.HarmonicOnNhd u H) (hub : ∃ M : ℝ, ∀ z ∈ H, |u z| ≤ M) {n : Ω → ℤ}
    (hn : Measurable[𝓦] n) {a : ℝ} (hU : ∀ q : ℝ≥0, PocketStopUnionLaw 𝓦 P A γ C (F q) h₀ q)
    (hside : ∀ q : ℝ≥0, PocketStopSideLimit κ (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) P A γ
      (fun _ => LP.twoSeedXL) (fun _ => LP.twoSeedXR) (fun ω => shiftChart (pChart A C ψ ω) (n ω)) a h₀ u
      (activeCompl A γ (fun ω => shiftChart (pChart A C ψ ω) (n ω)) q) q)
    (hGood : ∀ᵐ ω ∂P, ω ∈ A → capLife (γ ω) = ⊤ → Good (fun t => segDriver (γ ω) t) ⊤)
    {ε₀ : Type u} [MeasurableSpace ε₀] [StandardBorelSpace ε₀] {E₀ : Ω → ε₀} (hE₀ : Measurable[𝓦] E₀)
    (hgen : 𝓦 ≤ MeasurableSpace.comap E₀ inferInstance ⊔ Ito.nullSets P) {η : Ω → ℝ → ℂ}
    (h513 : ∃ Γ' : Ω → ℝ≥0 → ℂ, (∀ t, StronglyMeasurable[MeasurableSpace.comap
      (fun ω => h₀ ω + smoothDist upperHalfPlaneOpens u) inferInstance] fun ω => Γ' ω t) ∧
      ∀ᵐ ω ∂P, Γ' ω = fun t : ℝ≥0 => η ω t)
    (hers : PocketErasure 𝓦 P A γ (fun _ => LP.twoSeedXL) (fun _ => LP.twoSeedXR) η) :
    PocketChartTwoSeedStatement.{u} κ rL rR Good :=
  pocketChartTwoSeedStatement_of_r7PocketStop (r7PocketStopStatement_of_stop_marks h𝓦 hA hPA hγ hγm hunb hCo hCH
    hψ hCm hψm hCin hFo hgeo hh₀ hu hub hn hU hside hGood hE₀ hgen h513 hers)

end Stop

end InteractingSLE.Sec7.R7Aux131
