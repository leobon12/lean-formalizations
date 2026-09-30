import QuantumZipper.Proofs.Section5.Prop17ShiftDet
import QuantumZipper.Proofs.Section5.Prop17StatPalm

/-!
# Proposition 1.7, SHIFT-DET (part 3): wiring with the corrected good set

`Prop17ShiftDetStmt'` (proved in `Prop17ShiftDet.lean`) covers only `GoodCS γ L` (good vectors
whose translate has positive scale), not all of `GoodC γ`. The passage to the limit
(`map_eq_self_of_local`) only needs the covering almost surely under the reference law, and
`GoodCS` has full measure there by `prop17ScalePosStmt_holds`. This file redoes the two short
consumer steps (`prop17ShiftLocalStmt_of_det`, `prop17RefCoordsShiftStmt_of_approx`) with the
a.s. covering and obtains

* `theorem1_7_of_palmZoom'`: Proposition 1.7 from D4⁺ (`Prop17PalmZoomStmt`) alone.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal

namespace QuantumZipper
namespace S5
namespace FieldLaw
namespace Raw

open WedgeMeas Factorization CoordsFull TV

theorem coordsFull_mem_goodCS {γ L : ℝ} {x : FieldSample} (hx : IsLQGGood γ x)
    (hb : qBoundaryMeasure γ x (Ici 0) = ⊤)
    (hs : 0 < scaleParam γ (translate x (wedgeLengthPoint γ L x : ℂ))) :
    coordsFull x ∈ GoodCS γ L := by
  refine ⟨coordsFull_mem_goodC hx hb, ?_⟩
  show 0 < scaleG γ (tcoords γ L (proj (coordsFull x)))
  rw [← coords_eq_proj]
  have hav := avgReg_reconstruct_coords x
  have hx' : IsLQGGood γ (reconstruct (coords x)) :=
    (GoodSample.isLQGGood_iff_reconstruct γ x).2 hx
  have hy : lenG γ L (reconstruct (coords x)) = wedgeLengthPoint γ L x := by
    rw [lenG_eq hx']
    unfold wedgeLengthPoint
    rw [Factorization.qBoundaryMeasure_congr hav]
  have ht : tcoords γ L (coords x) = coords (translate x (wedgeLengthPoint γ L x : ℂ)) := by
    rw [tcoords, hy, Factorization.translate_congr hav]
  rw [ht, scaleG_coords (hx.translate _)]
  exact hs

/-- The local-event form of `Prop17ShiftDetStmt'` (the proof of `prop17ShiftLocalStmt_of_det`,
with the covering of `GoodCS`). -/
theorem shiftLocal_data_of_det' {γ L : ℝ} (h : Prop17ShiftDetStmt' γ L) :
    ∃ B : ℕ → Set (ℕ → ℝ), Monotone B ∧ (∀ n, MeasurableSet (B n)) ∧
      GoodCS γ L ⊆ ⋃ n, B n ∧ (∀ n, ∃ F ∈ locEvents, B n ∩ GoodC γ = F ∩ GoodC γ) ∧
      ∀ E ∈ measurableCylinders (fun _ : ℕ => ℝ), ∀ n, ∃ F ∈ locEvents,
        shiftCoords γ L ⁻¹' E ∩ B n ∩ GoodC γ = F ∩ GoodC γ := by
  classical
  obtain ⟨B, hmono, hBm, hcov, hdet⟩ := h
  refine ⟨B, hmono, hBm, hcov, fun n => ?_, fun E hE n => ?_⟩
  · obtain ⟨R, hR⟩ := hdet n 0
    obtain ⟨F, hF, hFe⟩ := exists_locEvent_of_determined (measurableSet_goodC γ) (hBm n)
      (R := R) fun c hc c' hc' he => (hR c hc c' hc' he).1
    exact ⟨F, hF, hFe⟩
  · obtain ⟨s, S, hS, rfl⟩ := (mem_measurableCylinders E).1 hE
    choose Rf hRf using hdet n
    set R := ∑ i ∈ s, Rf i
    have hle : ∀ i ∈ s, Rf i ≤ R := fun i hi =>
      Finset.single_le_sum (f := Rf) (fun _ _ => Nat.zero_le _) hi
    have hTm : MeasurableSet (shiftCoords γ L ⁻¹' cylinder s S ∩ B n) :=
      ((measurable_shiftCoords γ L) hS.cylinder).inter (hBm n)
    obtain ⟨F, hF, hFe⟩ := exists_locEvent_of_determined (measurableSet_goodC γ) hTm
      (R := R + Rf 0) fun c hc c' hc' he => by
        have hB : c ∈ B n ↔ c' ∈ B n :=
          (hRf 0 c hc c' hc' (locFull_mono (Nat.le_add_left _ _) he)).1
        have hco : c ∈ B n → s.restrict (shiftCoords γ L c) = s.restrict (shiftCoords γ L c') :=
          fun hcB => by
            funext i
            exact (hRf i.1 c hc c' hc'
              (locFull_mono ((hle i.1 i.2).trans (Nat.le_add_right _ _)) he)).2 hcB
        simp only [mem_inter_iff, mem_preimage, mem_cylinder]
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨hco h2 ▸ h1, hB.1 h2⟩
        · rintro ⟨h1, h2⟩
          have h2' := hB.2 h2
          exact ⟨(hco h2').symm ▸ h1, h2'⟩
    exact ⟨F, hF, hFe⟩

/-- **D5-e at the level of circle coordinates** from the pre-limit approximation alone
(locality of the shift is now proved: `prop17ShiftDetStmt'_holds`). -/
theorem prop17RefCoordsShiftStmt_of_approx_det {γ L : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (happ : Prop17ApproxStmt γ L) : Prop17RefCoordsShiftStmt γ L := by
  intro Ω' _ P' X A hP hX hA hI
  have hW : IsQuantumWedge γ γ (refField γ X A) P' :=
    ⟨gamma_lt_Qc' hγ hγ2, Ω', _, P', X, A, hP, hX, hA, hI, rfl⟩
  have hm : AEMeasurable (fun ω => coordsFull (refField γ X A ω)) P' :=
    (Wire3.wedgeDataAEMeasStmt_uncond hγ hγ2 P' _ hW).fst
  have hg := Wire3.wedgeGoodStmt_uncond hγ hγ2 P' _ hW
  have hb := Wire3.wedgeBoundaryRegularStmt_all γ hγ hγ2 P' _ hW
  have hsp := prop17ScalePosStmt_holds (L := L) hγ hγ2 Ω' _ P' X A hP hX hA hI
  set μ := P'.map fun ω => coordsFull (refField γ X A ω) with hμ
  have hL : P'.map (fun ω => coordsFull (shiftL γ L (refField γ X A ω))) =
      μ.map (shiftCoords γ L) := by
    rw [hμ, AEMeasurable.map_map_of_aemeasurable (measurable_shiftCoords γ L).aemeasurable hm]
    refine Measure.map_congr ?_
    filter_upwards [hg] with ω hω
    exact coordsFull_shiftL hω
  rw [hL]
  have hgμ : ∀ᵐ c ∂μ, c ∈ GoodC γ := by
    rw [hμ]
    refine (ae_map_iff hm (measurableSet_goodC γ)).2 ?_
    filter_upwards [hg, hb] with ω h1 h2
    exact coordsFull_mem_goodC h1 h2.2.2
  have hgμS : ∀ᵐ c ∂μ, c ∈ GoodCS γ L := by
    rw [hμ]
    refine (ae_map_iff hm (measurableSet_goodCS γ L)).2 ?_
    filter_upwards [hg, hb, hsp] with ω h1 h2 h3
    exact coordsFull_mem_goodCS h1 h2.2.2 h3.2
  obtain ⟨B, hBmono, hBm, hBcov, hBloc, hTloc⟩ :=
    shiftLocal_data_of_det' (prop17ShiftDetStmt'_holds γ L)
  obtain ⟨ι, l, μs, hl, hμs, hTV, hgμs, hshift⟩ := happ Ω' _ P' X A hP hX hA hI
  haveI := hl
  exact map_eq_self_of_local (l := l) (μ := μ) (μs := μs) (measurable_shiftCoords γ L)
    (Pi0 := measurableCylinders (fun _ : ℕ => ℝ)) generateFrom_measurableCylinders.symm
    isPiSystem_measurableCylinders (tendsto_real_of_tvLocal hTV)
    measurableCylinders_subset_locEvents hshift hgμ hgμs hBmono hBm
    (hgμS.mono fun c hc => hBcov hc) hBloc hTloc

/-- **Proposition 1.7 (`theorem1_7`)**, conditional only on D4⁺ (`Prop17PalmZoomStmt`). -/
theorem theorem1_7_of_palmZoom'
    (hD4 : ∀ γ : ℝ, 0 < γ → γ < 2 → Prop17PalmZoomStmt γ) : theorem1_7 :=
  Wire3.theorem1_7_of_refShiftStmt fun γ L hγ hγ2 hL =>
    prop17RefShiftStmt_of_coordsStmt hγ hγ2
      (prop17RefCoordsShiftStmt_of_approx_det hγ hγ2
        (prop17ApproxStmt_of_palmZoom hγ hL (hD4 γ hγ hγ2)))

end Raw
end FieldLaw
end S5
end QuantumZipper
