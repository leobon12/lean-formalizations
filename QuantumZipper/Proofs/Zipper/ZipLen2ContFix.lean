import QuantumZipper.Proofs.Zipper.ZipLen2ContDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ZIPLEN-2 continuum: the fixed-driver continuous-radius Cauchy property

`FlowFixedUCcStmt` from the continuous-radius identity `Φ^c(p, ρ) = X(μ_{p,ρ}) + det^c(p, ρ)`
(a.s. at fixed `(p, ρ)`) and the uniform convergence of `det^c` as `ρ → 0⁺`: the six-parameter
continuous modification `F1.exists_contMod_flow` (Revuz–Yor, 3rd ed., Ch. I, Thm (2.1)) is
continuous in `(p, ρ) ∈ flowBox m × [0, 1]`, hence uniformly continuous on a compact cube.
The pattern is `F1.xFlowFixedUCQAllStmt_of` with the dyadic radii replaced by rational radii.
Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal

namespace QuantumZipper
namespace B3d
namespace ZipLen

open F1 RegUnif

/-- **The fixed-driver continuous-radius Cauchy property** from the continuous-radius identity
and deterministic nodes. -/
theorem flowFixedUCc_of
    (hID : ∀ {κ : ℝ}, 0 < κ → ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
      [IsProbabilityMeasure P] {X : Ω → FieldSample}, IsFreeGFFModConstH X P →
      ∀ {W : ℝ → ℝ}, Continuous W → W 0 = 0 → ∀ {p : ℝ × ℝ × ℂ × ℝ}, p ∈ F1.flowPar →
      ∀ {ρ : ℝ}, 0 < ρ → ρ ≤ 1 →
        ∀ᵐ ω ∂P, flowPhiYc κ (X ω) W ρ p = X ω (F1.flowMu W p ρ) + flowDetC κ W p ρ)
    (hD : ∀ {κ : ℝ}, 0 < κ → ∀ {W : ℝ → ℝ}, Continuous W → W 0 = 0 → ∀ m : ℕ,
      TendstoUniformlyOn (fun ρ p => flowDetC κ W p ρ)
        (fun p => ∫ v, RegUnif.PsiU κ W p.1 v ∂F1.flowNu W p) (𝓝[>] 0) (F1.flowBox m)) :
    ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (X : Ω → FieldSample), IsFreeGFFModConstH X P →
      FlowFixedUCcStmt κ P X := by
  intro κ hκ _ Ω _ P _ X hX m W a CH hWH
  have hWH' := hWH
  obtain ⟨hW, hW0, -, -, -, -⟩ := hWH'
  obtain ⟨K, c, hK, hc, hEn⟩ := flowEnergyStmt_holds m W a CH hWH
  obtain ⟨Y, hYc, hYZ⟩ := exists_contMod_flow hX flowAdmStmt_holds hW hW0 hK hc hEn
  have hgood : ∀ᵐ ω ∂P, ∀ x : (ℚ × ℚ × ℚ × ℚ × ℚ) × ℚ, flowQ x.1 ∈ flowBox m →
      0 < x.2 → (x.2 : ℝ) ≤ 1 →
      flowPhiYc κ (X ω) W x.2 (flowQ x.1) =
          X ω (flowMu W (flowQ x.1) x.2) + flowDetC κ W (flowQ x.1) x.2 ∧
        Y (embQ (flowQ x.1) x.2) ω = X ω (flowMu W (flowQ x.1) x.2) := by
    refine ae_all_iff.2 fun x => ?_
    by_cases hx : flowQ x.1 ∈ flowBox m ∧ 0 < x.2 ∧ (x.2 : ℝ) ≤ 1
    · obtain ⟨hx1, hx2, hx3⟩ := hx
      have hx2' : (0 : ℝ) < x.2 := by exact_mod_cast hx2
      have h2 := hYZ (embQ (flowQ x.1) x.2)
      rw [ptQ_embQ hx1, rhQ_embQ _ ⟨hx2'.le, hx3⟩] at h2
      filter_upwards [hID hκ hX hW hW0 (flowBox_subset_flowPar m hx1) hx2' hx3, h2]
        with ω h1 h2 _ _ _
      exact ⟨h1, h2⟩
    · exact ae_of_all _ fun ω h1 h2 h3 => absurd ⟨h1, h2, h3⟩ hx
  have hdet := Metric.tendstoUniformlyOn_iff.1 (hD hκ hW hW0 m)
  filter_upwards [hgood] with ω hω n
  set ε : ℝ := 1 / ((n : ℝ) + 1) with hε
  have hε0 : 0 < ε := by positivity
  set Kc : Set (Fin 6 → ℝ) :=
    Set.pi univ (fun _ : Fin 6 => Icc (-((m : ℝ) + 3)) ((m : ℝ) + 3)) with hKc
  have hKcc : IsCompact Kc := isCompact_univ_pi fun _ => isCompact_Icc
  obtain ⟨η, hη, hU⟩ := Metric.uniformContinuousOn_iff.1
    (hKcc.uniformContinuousOn_of_continuous (hYc ω).continuousOn) (ε / 2) (by positivity)
  obtain ⟨δ, hδ, hδs⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 (hdet (ε / 4) (by positivity))
  have hδ0 : (0 : ℝ) < δ := hδ
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt (lt_min hη hδ0)
  have hNη : 1 / ((N : ℝ) + 1) < η := lt_of_lt_of_le hN (min_le_left _ _)
  have hNδ : 1 / ((N : ℝ) + 1) < δ := lt_of_lt_of_le hN (min_le_right _ _)
  have hN1 : 1 / ((N : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  refine ⟨N, fun ρ ρ' hρ hρN hρ' hρ'N q hq => ?_⟩
  have hρr : (0 : ℝ) < ρ := by exact_mod_cast hρ
  have hρr' : (0 : ℝ) < ρ' := by exact_mod_cast hρ'
  have e1 := (hω (q, ρ) hq hρ (hρN.trans hN1)).1
  have e2 := (hω (q, ρ') hq hρ' (hρ'N.trans hN1)).1
  have e3 := (hω (q, ρ) hq hρ (hρN.trans hN1)).2
  have e4 := (hω (q, ρ') hq hρ' (hρ'N.trans hN1)).2
  simp only at e1 e2 e3 e4
  have hd : dist (embQ (flowQ q) (ρ : ℝ)) (embQ (flowQ q) (ρ' : ℝ)) < η := by
    refine (dist_embQ_le _ _ _).trans_lt ?_
    rw [abs_lt]; constructor <;> linarith
  have hY := hU _ (embQ_mem_cube hq ⟨hρr.le, hρN.trans hN1⟩) _
    (embQ_mem_cube hq ⟨hρr'.le, hρ'N.trans hN1⟩) hd
  rw [Real.dist_eq, e3, e4] at hY
  have d1 := hδs ⟨hρr, lt_of_le_of_lt hρN hNδ⟩ _ hq
  have d2 := hδs ⟨hρr', lt_of_le_of_lt hρ'N hNδ⟩ _ hq
  rw [Real.dist_eq] at d1 d2
  rw [e1, e2]
  have hdd : |flowDetC κ W (flowQ q) ρ - flowDetC κ W (flowQ q) ρ'| < ε / 2 := by
    rw [abs_lt] at d1 d2 ⊢; constructor <;> linarith
  rw [abs_lt] at hY hdd
  rw [abs_le]; constructor <;> linarith

end ZipLen
end B3d
end QuantumZipper
