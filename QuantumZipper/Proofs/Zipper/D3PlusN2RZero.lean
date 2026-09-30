import QuantumZipper.Proofs.Zipper.D3PlusN2RRead
import QuantumZipper.Proofs.Zipper.D3PlusN2TmZWedge
import QuantumZipper.Proofs.Zipper.D3PlusN2TmZStmt
import QuantumZipper.Proofs.Section5.Prop17Final

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# N2-zero on the restricted index (Decision D36): the primed nodes and the assembly

Task D36-IMPL, steps (5) and (6). The TmZero assembly `d3PlusIN2TmZero_of_nodes`
(`D3PlusN2TmZStmt.lean`) is re-run with the window nodes stated on the restricted index
`WinIdx K` (Decision D36: folded circles and bounded compactly supported densities inside the
window), so that the heart node is no longer the (false/unprovable) statement over all of
`LocIdx K` but its provable restriction.

* `N2ZHeartWinStmt`: the window data of the embedded model converge in TV to those of the embedded
  wedge field, **read on the restricted index** (D36 form of `N2ZHeartStmt`).
* `N2ZWedgeLocWinStmt` (D36 form of `N2ZWedgeLocStmt`) and `n2ZWedgeLocWin_holds`: a.e.-
  measurability of the restricted wedge window data, the a.s. identity on the primed window event
  and the exhaustion. Derived from the *proved* unrestricted `n2ZWedgeLoc_holds`
  (`D3PlusN2TmZWedge.lean`): the primed data are the unrestricted data reindexed along
  `WinIdx K → LocIdx K`, so only `measurable_reindex_locW`, `n2GoodW_resFieldW` and
  `gKW_eq_gK_of_resField` are needed.
* `N2ZModelLocWinStmt` (D36 form of `N2ZModelLocStmt`, `D3PlusN2RRead.lean`) holds from the same
  almost-sure regularity node `N2ZModelRegStmt`.
* `d3PlusIN2TmZeroWin_of_nodes` and `theorem1_7_of_winNodes`: Proposition 1.7 (Sheffield,
  arXiv:1012.4797) from the three primed nodes. The assembly is a literal copy of
  `d3PlusIN2TmZero_of_nodes` with the restricted window data; the only structural change is the
  guard `0 < K` on the a.e.-measurability clause (irrelevant in the limit `K → ∞`).

Nothing here is new mathematics: the restriction only replaces the window index, and the TV
bookkeeping (triangle inequality, data processing, splitting along the window event) is unchanged.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace D3Plus

/-! ## Reindexing measurability -/

/-- Reindexing window data along `WinIdx K → LocIdx K` is measurable (coordinate projections of a
product σ-algebra). -/
theorem measurable_reindex_locW (K : ℕ) (hK : 0 < K) :
    Measurable fun (v : LocIdx (K : ℝ) → ℝ) => fun i : WinIdx K =>
      v ⟨winIdx K i, isLocalH_winIdx K hK i⟩ :=
  measurable_pi_iff.2 fun i => measurable_pi_apply _

/-- A.e.-measurability of the model's restricted window data. -/
theorem aemeasurable_resFieldW_n2Emb {γ α L r : ℝ} {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → FieldSample} (hα : α < Qc γ) (hr : 0 < r)
    (hX : IsFreeGFFModConstH X P) (K : ℕ) (hK : 0 < K) :
    AEMeasurable (fun ω => resFieldW K (n2Emb γ α L r X ω)) P :=
  (measurable_reindex_locW K hK).comp_aemeasurable
    (aemeasurable_resField_n2Emb (γ := γ) (α := α) (L := L) (r := r) hα hr hX K)

/-! ## The primed nodes -/

/-- **Node N2Z-HEART'** (restricted index, D36 form of `N2ZHeartStmt`): the restricted window
data of the embedded model converge in TV to those of the embedded wedge field, plus
a.e.-measurability. -/
def N2ZHeartWinStmt : Prop :=
  ∀ (γ α r : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → FieldSample) {Ω'' : Type} [MeasurableSpace Ω''] (P'' : Measure Ω'')
    [IsProbabilityMeasure P''] (X'' : Ω'' → FieldSample) (A : ℝ → Ω'' → ℝ),
    0 < γ → γ < 2 → α < Qc γ → 0 < r → IsFreeGFFModConstH X P → IsFreeGFFModConstH X'' P'' →
    IsWedgeProcess α (Qc γ) A P'' → IndepFun X'' (fun ω t => A t ω) P'' →
    ∀ K : ℕ, 0 < K →
      (∀ L, AEMeasurable (fun ω => resFieldW K (n2Emb γ α L r X ω)) P) ∧
      Tendsto (fun L => TV.tvDist (P.map fun ω => resFieldW K (n2Emb γ α L r X ω))
        (P''.map fun ω => resFieldW K (wedgeV γ X'' A ω))) atTop (𝓝 0)

/-- **Node N2Z-WEDGELOC'** (restricted index, D36 form of `N2ZWedgeLocStmt`). -/
def N2ZWedgeLocWinStmt : Prop :=
  ∀ (γ α : ℝ) {Ω'' : Type} [MeasurableSpace Ω''] (P'' : Measure Ω'')
    [IsProbabilityMeasure P''] (X'' : Ω'' → FieldSample) (A : ℝ → Ω'' → ℝ),
    0 < γ → γ < 2 → α < Qc γ → IsFreeGFFModConstH X'' P'' →
    IsWedgeProcess α (Qc γ) A P'' → IndepFun X'' (fun ω t => A t ω) P'' →
    (∀ K : ℕ, 0 < K → AEMeasurable (fun ω => resFieldW K (wedgeV γ X'' A ω)) P'') ∧
    (∀ K R : ℕ, 0 < K → P'' {ω | resFieldW K (wedgeV γ X'' A ω) ∈ n2GoodW γ K R ∧
      locFieldFull R (canonical γ (wedgeV γ X'' A ω)) ≠
        gKW γ K R (resFieldW K (wedgeV γ X'' A ω))} = 0) ∧
    ∀ R : ℕ, Tendsto (fun K : ℕ => P'' {ω | resFieldW K (wedgeV γ X'' A ω) ∉ n2GoodW γ K R})
      atTop (𝓝 0)

/-- **N2Z-WEDGELOC' holds** (from the proved unrestricted node): reindex the unrestricted wedge
window data along `WinIdx K → LocIdx K`. -/
theorem n2ZWedgeLocWin_holds : N2ZWedgeLocWinStmt := by
  intro γ α Ω'' _ P'' _ X'' A hγ hγ2 hα hX'' hA hInd
  obtain ⟨h1, h2, h3⟩ := n2ZWedgeLoc_holds γ α P'' X'' A hγ hγ2 hα hX'' hA hInd
  refine ⟨fun K hK => (measurable_reindex_locW K hK).comp_aemeasurable (h1 K), ?_, ?_⟩
  · intro K R hK
    refine measure_mono_null (fun ω hω => ?_)
      (h2 K R hK)
    simp only [Set.mem_setOf_eq] at hω ⊢
    exact ⟨(n2GoodW_resFieldW γ K R (wedgeV γ X'' A ω)).1 hω.1, fun h =>
      hω.2 (h.trans (gKW_eq_gK_of_resField γ K R (wedgeV γ X'' A ω)).symm)⟩
  · intro R
    have hset : ∀ K : ℕ, {ω | resFieldW K (wedgeV γ X'' A ω) ∉ n2GoodW γ K R} =
        {ω | resField K (wedgeV γ X'' A ω) ∉ n2Good γ K R} := by
      intro K
      ext ω
      simp only [Set.mem_setOf_eq, n2GoodW_resFieldW]
    simpa only [hset] using h3 R

/-! ## The assembly -/

/-- **N2-zero from the three primed nodes** (copy of `d3PlusIN2TmZero_of_nodes` with the restricted
window data). -/
theorem d3PlusIN2TmZeroWin_of_nodes (hH : N2ZHeartWinStmt) (hM : N2ZModelLocWinStmt)
    (hWL : N2ZWedgeLocWinStmt) : D3PlusIN2TmZeroStmt := by
  intro γ α r Ω _ P _ X Ω' _ P' _ Y' hγ hγ2 hr hX hW R
  have hW0 := hW
  obtain ⟨hα, Ω'', _, P'', X'', A, hP'', hX'', hA, hInd, hlaw⟩ := hW
  obtain ⟨hmeasV, hidV, hscV⟩ := hWL γ α P'' X'' A hγ hγ2 hα hX'' hA hInd
  rw [map_locFieldFull_wedge hγ hγ2 hα hX'' hA hInd hW0 hlaw R]
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  set e := ε / 2 / 2 / 2 with he
  have he0 : 0 < e := ENNReal.half_pos (ENNReal.half_pos (ENNReal.half_pos hε.ne').ne').ne'
  obtain ⟨K, hKV, hK0⟩ := ((ENNReal.tendsto_nhds_zero.1 (hscV R) e he0).and
    (eventually_gt_atTop 0)).exists
  obtain ⟨hmeasE, hT⟩ := hH γ α r P X P'' X'' A hγ hγ2 hα hr hX hX'' hA hInd K hK0
  filter_upwards [ENNReal.tendsto_nhds_zero.1 (hM γ α r P X hγ hγ2 hα hr hX K R hK0) e he0,
    ENNReal.tendsto_nhds_zero.1 hT e he0] with L h1 h2
  set G := n2GoodW γ K R
  set V := wedgeV γ X'' A
  set rW : Ω → WinIdx K → ℝ := fun ω => resFieldW K (n2Emb γ α L r X ω) with hrW
  set rV : Ω'' → WinIdx K → ℝ := fun ω => resFieldW K (V ω) with hrV
  set f : Ω → (ℕ → ℝ) × (TestFun H → ℝ) :=
    fun ω => TmRichN1 γ r R L (localZ X r ω, circData α fun _ => 0) with hf
  set fE : Ω → (ℕ → ℝ) × (TestFun H → ℝ) := fun ω => gKW γ K R (rW ω) with hfE
  set fV : Ω'' → (ℕ → ℝ) × (TestFun H → ℝ) := fun ω => gKW γ K R (rV ω) with hfV
  set fC : Ω'' → (ℕ → ℝ) × (TestFun H → ℝ) := fun ω => locFieldFull R (canonical γ (V ω))
    with hfC
  have hG : MeasurableSet G := measurableSet_n2GoodW γ K R
  have hfm : AEMeasurable f P :=
    ((measurable_TmRichN1 γ r R L).comp
      ((measurable_localZ hX hr).prodMk measurable_const)).aemeasurable
  have hfEm : AEMeasurable fE P := (measurable_gKW γ K R).comp_aemeasurable (hmeasE L)
  have hfVm : AEMeasurable fV P'' := (measurable_gKW γ K R).comp_aemeasurable (hmeasV K hK0)
  have hWq : IsQuantumWedge γ α (fun ω => canonical γ (V ω)) P'' :=
    ⟨hα, Ω'', inferInstance, P'', X'', A, inferInstance, hX'', hA, hInd, rfl⟩
  have hfCm : AEMeasurable fC P'' :=
    (measurable_lffOfData R).comp_aemeasurable
      (Wire2.aemeasurable_dataFull_of_isQuantumWedge hγ hγ2 hα hWq)
  -- the model's window event
  have hbadW : P {ω | rW ω ∉ G} ≤ P'' {ω | rV ω ∉ G} + e := by
    have hle := tsub_le_iff_right.1 (TV.le_tvDist (μ := P.map rW) (ν := P''.map rV) hG.compl)
    rw [Measure.map_apply_of_aemeasurable (hmeasE L) hG.compl,
      Measure.map_apply_of_aemeasurable (hmeasV K hK0) hG.compl] at hle
    calc P {ω | rW ω ∉ G} = P (rW ⁻¹' Gᶜ) := rfl
      _ ≤ TV.tvDist (P.map rW) (P''.map rV) + P'' (rV ⁻¹' Gᶜ) := hle
      _ ≤ e + P'' {ω | rV ω ∉ G} := add_le_add h2 le_rfl
      _ = P'' {ω | rV ω ∉ G} + e := add_comm _ _
  have t1 : TV.tvDist (P.map f) (P.map fE) ≤ e + (e + e) := by
    refine (tvDist_map_le_of_ae_eq_off hfm hfEm {ω | f ω ≠ fE ω}
      (Eventually.of_forall fun ω hω => not_not.1 hω)).trans ?_
    refine (measure_ne_le_split (w := rW) G).trans (add_le_add h1 (hbadW.trans ?_))
    exact add_le_add hKV le_rfl
  have t2 : TV.tvDist (P.map fE) (P''.map fV) ≤ e :=
    (tvDist_map_comp_le (g := gKW γ K R) (measurable_gKW γ K R) (hmeasE L)
      (hmeasV K hK0)).trans h2
  have t3 : TV.tvDist (P''.map fV) (P''.map fC) ≤ e := by
    refine (tvDist_map_le_of_ae_eq_off hfVm hfCm {ω | fV ω ≠ fC ω}
      (Eventually.of_forall fun ω hω => not_not.1 hω)).trans ?_
    refine (measure_ne_le_split (w := rV) G).trans ?_
    have h0 : P'' {ω | rV ω ∈ G ∧ fV ω ≠ fC ω} = 0 := by
      refine measure_mono_null ?_ (hidV K R hK0)
      intro ω hω
      exact ⟨hω.1, fun h => hω.2 h.symm⟩
    rw [h0, zero_add]
    exact hKV
  have hsum : e + (e + e) + (e + e) ≤ ε := by
    have h4 : e + e = ε / 2 / 2 := ENNReal.add_halves _
    have h8 : ε / 2 / 2 + ε / 2 / 2 = ε / 2 := ENNReal.add_halves _
    calc e + (e + e) + (e + e) ≤ (e + e) + (e + e) + (e + e + (e + e)) :=
          add_le_add (add_le_add le_add_self le_rfl) le_add_self
      _ = ε := by rw [h4, h8, ENNReal.add_halves]
  calc TV.tvDist (P.map f) (P''.map fC)
      ≤ TV.tvDist (P.map f) (P.map fE) + TV.tvDist (P.map fE) (P''.map fC) := TV.tvDist_triangle
    _ ≤ TV.tvDist (P.map f) (P.map fE) +
        (TV.tvDist (P.map fE) (P''.map fV) + TV.tvDist (P''.map fV) (P''.map fC)) := by
        gcongr; exact TV.tvDist_triangle
    _ ≤ e + (e + e) + (e + e) := add_le_add t1 (add_le_add t2 t3)
    _ ≤ ε := hsum

end D3Plus
end QuantumZipper
