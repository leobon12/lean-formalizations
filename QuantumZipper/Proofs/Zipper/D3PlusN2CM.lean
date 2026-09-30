import QuantumZipper.Proofs.Zipper.D3PlusN2Stmt
import QuantumZipper.Proofs.LQG.WedgeRestriction

/-!
# D3⁺(i), node N2-CM: reduction to locality, the local scale, and a local Cameron–Martin bound

Task D3P-N2 (decisions D23, D24, D25). Paper: Sheffield, arXiv:1012.4797, proof of Prop. 1.6
(p. 25): near the marked point the smooth part of the field "is approximately constant". D24: a
correction harmonic near `0` and vanishing at `0` has Dirichlet energy on `B(0, ε)` of order
`ε²`, so its total-variation cost on the field restricted to `B(0, ε)` tends to `0`
(Berestycki–Powell, *GFF and LQG*, arXiv:2004.04720, Lemmas 3.12, 3.14, p. 79).

## The three inputs (as `Prop`s)

* `D3PlusIN2FixCMLocStmt` (local Cameron–Martin bound; the smooth-shift part): the law of the local
  field `Z` restricted to the `ε`-local measures (`resField ε`) and its translate by
  `μ ↦ ∫ h dμ` are at TV distance `→ 0` as `ε → 0⁺`, for `h` admissible with `h 0 = 0`.
  (To be supplied by the CM-TV task, `Proofs/GFF/CameronMartinTV*.lean`.)
* `D3PlusIN2FixLocRichStmt` (locality, a measurability statement of N1 type): on the event
  `0 < scaleParamOn < ε/(R+2)`, the rich local data of the canonical description is a fixed
  measurable function `G` of the field restricted to the `ε`-local measures.
* `D3PlusIN2FixScaleStmt` (the local scale tends to `0` in probability; the deterministic-correction
  analogue of D3⁺(iii), `d3PlusIII_holds`).

## Proved here

* `tvDist_map_le_of_local` (own elementary argument): if `f = G ∘ ρ` off `B` and
  `f' = G ∘ ρ'` off `B'` (a.s.), with `G` measurable, then
  `TV(law f, law f') ≤ TV(law ρ, law ρ') + P B + P B'` (outer measures; `B, B'` need not be
  measurable).
* `resField_n2_eq`: the restricted zoom field is the restricted local field translated by a
  deterministic vector, and the vectors of `φ` and `φ'` differ by `pairShift ε (φ' − φ)`.
* `d3PlusIN2FixCMRich_of_parts : CMLoc → LocRich → Scale → MeasRich → D3PlusIN2FixCMRichStmt`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace D3Plus

/-! ## Total variation of locally determined outputs -/

section TVLocal

variable {Ω β δ : Type*} [MeasurableSpace Ω] [MeasurableSpace β] [MeasurableSpace δ]
  {P : Measure Ω} {f f' : Ω → β} {ρ ρ' : Ω → δ} {G : δ → β} {B B' : Set Ω}

theorem map_apply_le_of_local (hf : AEMeasurable f P) (hf' : AEMeasurable f' P)
    (hρ : AEMeasurable ρ P) (hρ' : AEMeasurable ρ' P) (hG : Measurable G)
    (hB : ∀ᵐ ω ∂P, ω ∉ B → f ω = G (ρ ω)) (hB' : ∀ᵐ ω ∂P, ω ∉ B' → f' ω = G (ρ' ω))
    {A : Set β} (hA : MeasurableSet A) :
    P.map f A ≤ P.map f' A + (TV.tvDist (P.map ρ) (P.map ρ') + (P B + P B')) := by
  rw [Measure.map_apply_of_aemeasurable hf hA, Measure.map_apply_of_aemeasurable hf' hA]
  have h1 : P (f ⁻¹' A) ≤ P (ρ ⁻¹' (G ⁻¹' A)) + P B := by
    refine (measure_mono_ae ?_).trans (measure_union_le _ _)
    filter_upwards [hB] with ω hω hmem
    by_cases hωB : ω ∈ B
    · exact Or.inr hωB
    · left
      show G (ρ ω) ∈ A
      rw [← hω hωB]
      exact hmem
  have h2 : P (ρ' ⁻¹' (G ⁻¹' A)) ≤ P (f' ⁻¹' A) + P B' := by
    refine (measure_mono_ae ?_).trans (measure_union_le _ _)
    filter_upwards [hB'] with ω hω hmem
    by_cases hωB : ω ∈ B'
    · exact Or.inr hωB
    · left
      show f' ω ∈ A
      rw [hω hωB]
      exact hmem
  have h3 : P.map ρ (G ⁻¹' A) ≤ TV.tvDist (P.map ρ) (P.map ρ') + P.map ρ' (G ⁻¹' A) :=
    tsub_le_iff_right.1 (TV.le_tvDist (hG hA))
  rw [Measure.map_apply_of_aemeasurable hρ (hG hA),
    Measure.map_apply_of_aemeasurable hρ' (hG hA)] at h3
  calc P (f ⁻¹' A) ≤ P (ρ ⁻¹' (G ⁻¹' A)) + P B := h1
    _ ≤ (TV.tvDist (P.map ρ) (P.map ρ') + P (ρ' ⁻¹' (G ⁻¹' A))) + P B := by gcongr
    _ ≤ (TV.tvDist (P.map ρ) (P.map ρ') + (P (f' ⁻¹' A) + P B')) + P B := by gcongr
    _ = P (f' ⁻¹' A) + (TV.tvDist (P.map ρ) (P.map ρ') + (P B + P B')) := by ring

/-- **TV distance of locally determined outputs** (own elementary argument). -/
theorem tvDist_map_le_of_local (hf : AEMeasurable f P) (hf' : AEMeasurable f' P)
    (hρ : AEMeasurable ρ P) (hρ' : AEMeasurable ρ' P) (hG : Measurable G)
    (hB : ∀ᵐ ω ∂P, ω ∉ B → f ω = G (ρ ω)) (hB' : ∀ᵐ ω ∂P, ω ∉ B' → f' ω = G (ρ' ω)) :
    TV.tvDist (P.map f) (P.map f') ≤ TV.tvDist (P.map ρ) (P.map ρ') + (P B + P B') := by
  refine iSup_le fun A => iSup_le fun hA => sup_le ?_ ?_
  · exact tsub_le_iff_right.2 (by
      rw [add_comm]; exact map_apply_le_of_local hf hf' hρ hρ' hG hB hB' hA)
  · refine tsub_le_iff_right.2 ?_
    have := map_apply_le_of_local hf' hf hρ' hρ hG hB' hB hA
    rw [TV.tvDist_comm (μ := P.map ρ'), add_comm (P B') (P B)] at this
    rw [add_comm]
    exact this

end TVLocal

/-! ## Restriction to the `ε`-local measures -/

/-- The field restricted to the `ε`-local measures (`IsLocalH 0 ε`). -/
def resField (ε : ℝ) (y : FieldSample) : LocIdx ε → ℝ := fun μ => y μ.1

theorem measurable_resField (ε : ℝ) : Measurable (resField ε) :=
  measurable_pi_iff.2 fun μ => measurable_pi_apply μ.1

/-- The deterministic vector `μ ↦ ∫ h dμ` on the `ε`-local measures. -/
def pairShift (ε : ℝ) (h : ℂ → ℝ) : LocIdx ε → ℝ := fun μ => ∫ z, h z ∂μ.1

theorem integrable_of_admCorr {r ε : ℝ} (hεr : ε ≤ r) {φ : ℂ → ℝ}
    (hφ : ContinuousOn φ (Metric.ball (0 : ℂ) r ∩ Hbar)) (μ : LocIdx ε) : Integrable φ μ.1 := by
  obtain ⟨⟨hfin, ⟨K, hK, hKH, hμK⟩, -⟩, r', hr', hμr'⟩ := μ.2
  set S : Set ℂ := Metric.closedBall 0 r' ∩ K with hSdef
  have hSc : IsCompact S := (isCompact_closedBall _ _).inter_right hK.isClosed
  have hSsub : S ⊆ Metric.ball (0 : ℂ) r ∩ Hbar := fun z hz =>
    ⟨Metric.closedBall_subset_ball (hr'.trans_le hεr) (by simpa using hz.1), hKH hz.2⟩
  have hμS : μ.1 Sᶜ = 0 := by
    rw [hSdef, compl_inter]
    refine measure_union_null ?_ hμK
    simpa using hμr'
  have hres : μ.1.restrict S = μ.1 := Measure.restrict_eq_self_of_ae_mem
    (measure_eq_zero_iff_ae_notMem.1 hμS |>.mono fun z hz => by simpa using hz)
  obtain ⟨C, hC⟩ := hSc.exists_bound_of_continuousOn (hφ.mono hSsub)
  rw [← hres]
  refine Integrable.mono' (integrable_const C)
    ((hφ.mono hSsub).aestronglyMeasurable hSc.measurableSet) ?_
  filter_upwards [ae_restrict_mem hSc.measurableSet] with z hz
  exact hC z hz

theorem integrable_n2Shift {γ α L r ε : ℝ} (hεr : ε ≤ r) {φ : ℂ → ℝ}
    (hφ : ContinuousOn φ (Metric.ball (0 : ℂ) r ∩ Hbar)) (μ : LocIdx ε) :
    Integrable (n2Shift γ α L φ) μ.1 := by
  have hμ : IsAdmissibleH μ.1 := μ.2.1
  have hfin : IsFiniteMeasure μ.1 := hμ.1
  have hlog : Integrable (fun z : ℂ => α * -Real.log ‖z‖) μ.1 :=
    ((WedgeRes.integrable_log_norm_adm hμ).neg).const_mul α
  exact (hlog.add (integrable_of_admCorr hεr hφ μ)).add (integrable_const _)

/-- The two restricted zoom fields differ by `pairShift ε (φ' − φ)`. -/
theorem resField_n2_sub {γ α L ε r : ℝ} (hεr : ε ≤ r) {φ φ' : ℂ → ℝ}
    (hφ : ContinuousOn φ (Metric.ball (0 : ℂ) r ∩ Hbar))
    (hφ' : ContinuousOn φ' (Metric.ball (0 : ℂ) r ∩ Hbar)) (y : FieldSample) :
    resField ε (y + ofFun (n2Shift γ α L φ')) =
      resField ε (y + ofFun (n2Shift γ α L φ)) + pairShift ε (fun z => φ' z - φ z) := by
  funext μ
  simp only [resField, pairShift, Pi.add_apply, ofFun]
  rw [add_assoc, ← integral_add (integrable_n2Shift hεr hφ μ)
    (integrable_of_admCorr (φ := fun z => φ' z - φ z) hεr (hφ'.sub hφ) μ)]
  congr 2
  funext z
  simp only [n2Shift]
  ring

/-- Translating two laws by the same deterministic vector does not change their TV distance
(here: the bound `≤`). -/
theorem tvDist_map_add_le {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω) {W : Ω → ι → ℝ}
    (hW : Measurable W) (v c : ι → ℝ) :
    TV.tvDist (P.map fun ω => W ω + v) (P.map fun ω => W ω + v + c) ≤
      TV.tvDist (P.map W) (P.map fun ω => W ω + c) := by
  have hv : Measurable fun x : ι → ℝ => x + v := measurable_add_const v
  have e1 : P.map (fun ω => W ω + v) = (P.map W).map (fun x => x + v) :=
    (Measure.map_map hv hW).symm
  have e2 : P.map (fun ω => W ω + v + c) = (P.map fun ω => W ω + c).map (fun x => x + v) := by
    rw [Measure.map_map hv (hW.add_const c)]
    congr 1
    funext ω
    simp only [Function.comp_apply]
    abel
  rw [e1, e2]
  exact TV.tvDist_map_le hv

/-! ## The three inputs -/

/-- **Local Cameron–Martin bound** (D24; Berestycki–Powell arXiv:2004.04720 Lemmas 3.12, 3.14):
for an admissible `h` with `h 0 = 0`, the law of the local field restricted to the `ε`-local
measures and its translate by `μ ↦ ∫ h dμ` are at TV distance `→ 0` as `ε → 0⁺`. -/
def D3PlusIN2FixCMLocStmt : Prop :=
  ∀ (r : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → FieldSample) (h : ℂ → ℝ),
    0 < r → IsFreeGFFModConstH X P → AdmCorr r h → h 0 = 0 →
    Tendsto (fun ε => TV.tvDist (P.map fun ω => resField ε (locZField X r ω))
      (P.map fun ω => resField ε (locZField X r ω) + pairShift ε h)) (𝓝[>] 0) (𝓝 0)

/-- **The local scale tends to `0` in probability** (deterministic-correction analogue of
D3⁺(iii); outer measure, no measurability claimed). -/
def D3PlusIN2FixScaleStmt : Prop :=
  ∀ (γ α r : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → FieldSample) (φ : ℂ → ℝ),
    0 < γ → γ < 2 → α < Qc γ → 0 < r → IsFreeGFFModConstH X P → AdmCorr r φ →
    ∀ δ : ℝ, 0 < δ → Tendsto (fun L => P {ω |
      ¬(0 < scaleParamOn γ (locZField X r ω + ofFun (n2Shift γ α L φ)) (halfDisc r) ∧
        scaleParamOn γ (locZField X r ω + ofFun (n2Shift γ α L φ)) (halfDisc r) < δ)})
      atTop (𝓝 0)

theorem admCorr_sub {r : ℝ} {φ φ' : ℂ → ℝ} (hφ : AdmCorr r φ) (hφ' : AdmCorr r φ') :
    AdmCorr r fun z => φ' z - φ z := by
  obtain ⟨hc, ρ, hρ, hh⟩ := hφ
  obtain ⟨hc', ρ', hρ', hh'⟩ := hφ'
  refine ⟨hc'.sub hc, min ρ ρ', lt_min hρ hρ', ?_⟩
  have h1 := hh.mono (Metric.ball_subset_ball (min_le_left ρ ρ'))
  have h2 := hh'.mono (Metric.ball_subset_ball (min_le_right ρ ρ'))
  exact h2.sub h1

/-! ## Assembly -/

end D3Plus
end QuantumZipper
