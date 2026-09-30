import QuantumZipper.Proofs.Thm18.G3GeoRight
import QuantumZipper.Proofs.Thm18.G3HonestFin2

/-!
# G3-GEO, part 4: honest boundary lengths near `0`

For the Theorem 1.2 field `h = normField γ X₀` with boundary measure `ν_h = g3Hν γ ω`:

* `ae_g3Fid_sets`: F2 (`G3Fid.g3Fid2`) at the level of sets: a.s., for every index, the scheme's
  measures `ν₁+ν₀`, `ν₀+ν₂` agree with `ν_h` on every subset of their windows;
* `g3Z_eq_honest`, `g3Z_pos_lt_top`: `g3Z = E ν_h[−δ, 0] ∈ (0, ∞)` (F3, `G3HonestFin2`,
  `G3FidHonest`);
* `tendsto_lintegral_hν_left`: `E ν_h[−a, 0] → 0` as `a ↓ 0`;
* `tendsto_lintegral_hν_right`: `E min(ν_h[0, a], ν_h[−δ, 0]) → 0` as `a ↓ 0`;
  both by dominated convergence (dominated by `ν_h[−δ,0]`, integrable by F3) and the absence of an
  atom of `ν_h` at `0` (`G3Fid.ae_normField_good`).

Own elementary arguments (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm

local notation "Ω₀" => gffBase.Ω
local notation "X₀" => gffBase.X

/-- The honest boundary measure of Theorem 1.2's field `h = normField γ X₀`. -/
abbrev g3Hν (γ : ℝ) (ω : Ω₀) : Measure ℝ := qBoundaryMeasure γ (normField γ X₀ ω)

/-- **F2 for sets.** -/
theorem ae_g3Fid_sets {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∀ᵐ ω ∂gffBase.P, ∀ i : G3Idx,
      (∀ s ⊆ Ioo (-i.δ - i.η / 4) (3 * i.η / 4), (g3ν₁ γ i ω + g3ν₀ γ i ω) s = g3Hν γ ω s) ∧
      (∀ s ⊆ Ioo (-(3 * i.η / 4)) (1 / 2 + i.η / 4),
        (g3ν₀ γ i ω + g3ν₂ γ i ω) s = g3Hν γ ω s) := by
  filter_upwards [G3Fid.g3Fid2 hγ hγ2] with ω hω i
  refine ⟨fun s hs => ?_, fun s hs => ?_⟩
  · rw [← Measure.restrict_eq_self _ hs, (hω i).2.2.2.1, Measure.restrict_eq_self _ hs]
  · rw [← Measure.restrict_eq_self _ hs, (hω i).2.2.2.2, Measure.restrict_eq_self _ hs]

theorem Icc_neg_subset_win (i : G3Idx) {a : ℝ} (ha : a < i.δ + i.η / 4) :
    Icc (-a) 0 ⊆ Ioo (-i.δ - i.η / 4) (3 * i.η / 4) := fun z hz =>
  ⟨by linarith [hz.1], by linarith [hz.2, i.hη]⟩

theorem Icc_pos_subset_win (i : G3Idx) {a : ℝ} (ha : a < 1 / 2 + i.η / 4) :
    Icc 0 a ⊆ Ioo (-(3 * i.η / 4)) (1 / 2 + i.η / 4) := fun z hz =>
  ⟨by linarith [hz.1, i.hη], by linarith [hz.2]⟩

theorem g3Mass_ae_eq_honest {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (i : G3Idx) :
    ∀ᵐ ω ∂gffBase.P, g3Mass γ i ω = g3Hν γ ω (Icc (-i.δ) 0) :=
  (ae_g3Fid_sets hγ hγ2).mono fun ω hω =>
    (hω i).1 _ (Icc_neg_subset_win i (by linarith [i.hη]))

theorem g3Z_eq_honest {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (i : G3Idx) :
    g3Z γ i = ∫⁻ ω, g3Hν γ ω (Icc (-i.δ) 0) ∂gffBase.P := by
  rw [g3Z_eq_lintegral_g3Mass]
  exact lintegral_congr_ae (g3Mass_ae_eq_honest hγ hγ2 i)

theorem g3Z_pos_lt_top {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (i : G3Idx) :
    0 < g3Z γ i ∧ g3Z γ i < ⊤ := by
  rw [g3Z_eq_honest hγ hγ2 i]
  exact ⟨lintegral_qBoundaryMeasure_normField_Icc_pos gffBase.gff hγ hγ2 (i.hη.trans i.hηδ),
    g3HonestFinStmt_main i hγ hγ2⟩

/-- A reference index with window `δ`. -/
def g3RefIdx (δ : ℝ) (hδ : 0 < δ) (hδ4 : δ ≤ 1 / 4) : G3Idx :=
  ⟨(δ, δ / 2, 0), by positivity, by linarith, hδ4⟩

theorem aemeasurable_hν_left {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (i : G3Idx) {s : Set ℝ}
    (hs : MeasurableSet s) (hsub : s ⊆ Ioo (-i.δ - i.η / 4) (3 * i.η / 4)) :
    AEMeasurable (fun ω => g3Hν γ ω s) gffBase.P :=
  ((Measure.measurable_coe hs).comp ((measurable_g3sum₁ γ i).mono
    (sup_le (localSigma_le gffBase.gff i.t₁ i.r₁)
      (outsideSigma2_le gffBase.gff i.t₁ i.r₁ i.t₂ i.r₂)) le_rfl)).aemeasurable.congr
    ((ae_g3Fid_sets hγ hγ2).mono fun ω hω => (hω i).1 s hsub)

theorem aemeasurable_hν_right {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (i : G3Idx) {s : Set ℝ}
    (hs : MeasurableSet s) (hsub : s ⊆ Ioo (-(3 * i.η / 4)) (1 / 2 + i.η / 4)) :
    AEMeasurable (fun ω => g3Hν γ ω s) gffBase.P :=
  ((Measure.measurable_coe hs).comp ((measurable_g3sum₂ γ i).mono
    (sup_le (localSigma_le gffBase.gff i.t₂ i.r₂)
      (outsideSigma2_le gffBase.gff i.t₁ i.r₁ i.t₂ i.r₂)) le_rfl)).aemeasurable.congr
    ((ae_g3Fid_sets hγ hγ2).mono fun ω hω => (hω i).2 s hsub)

theorem tendsto_measure_Icc_neg_zero {m : Measure ℝ} (hfin : m (Icc (-1) 0) ≠ ⊤)
    (h0 : m {0} = 0) : Tendsto (fun a => m (Icc (-a) 0)) (𝓝[>] 0) (𝓝 0) := by
  have htend := tendsto_measure_biInter_gt (μ := m) (a := (0 : ℝ))
    (s := fun r : ℝ => Icc (-r) 0) (fun r _ => measurableSet_Icc.nullMeasurableSet)
    (fun r r' _ hrr => Icc_subset_Icc_left (by linarith)) ⟨1, one_pos, hfin⟩
  have hI : (⋂ r > (0 : ℝ), Icc (-r) (0 : ℝ)) = {0} := by
    ext z
    simp only [mem_iInter, mem_Icc, mem_singleton_iff]
    constructor
    · intro h
      exact le_antisymm (h 1 one_pos).2
        (le_of_forall_pos_le_add fun e he => by linarith [(h e he).1])
    · rintro rfl r hr
      exact ⟨by linarith, le_rfl⟩
  rw [hI, h0] at htend
  exact htend

theorem tendsto_measure_Icc_zero_pos {m : Measure ℝ} (hfin : m (Icc 0 1) ≠ ⊤)
    (h0 : m {0} = 0) : Tendsto (fun a => m (Icc 0 a)) (𝓝[>] 0) (𝓝 0) := by
  have htend := tendsto_measure_biInter_gt (μ := m) (a := (0 : ℝ))
    (s := fun r : ℝ => Icc 0 r) (fun r _ => measurableSet_Icc.nullMeasurableSet)
    (fun r r' _ hrr => Icc_subset_Icc_right hrr) ⟨1, one_pos, hfin⟩
  have hI : (⋂ r > (0 : ℝ), Icc (0 : ℝ) r) = {0} := by
    ext z
    simp only [mem_iInter, mem_Icc, mem_singleton_iff]
    constructor
    · intro h
      exact le_antisymm (le_of_forall_pos_le_add fun e he => by linarith [(h e he).2])
        (h 1 one_pos).1
    · rintro rfl r hr
      exact ⟨le_rfl, hr.le⟩
  rw [hI, h0] at htend
  exact htend

/-- **`E ν_h[−a, 0] → 0` as `a ↓ 0`** (dominated convergence). -/
theorem tendsto_lintegral_hν_left {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {δ : ℝ} (hδ : 0 < δ)
    (hδ4 : δ ≤ 1 / 4) :
    Tendsto (fun a => ∫⁻ ω, g3Hν γ ω (Icc (-a) 0) ∂gffBase.P) (𝓝[>] 0) (𝓝 0) := by
  set i := g3RefIdx δ hδ hδ4
  have hiδ : i.δ = δ := rfl
  have h := tendsto_lintegral_filter_of_dominated_convergence' (μ := gffBase.P)
    (l := 𝓝[>] (0 : ℝ)) (F := fun a ω => g3Hν γ ω (Icc (-a) 0)) (f := fun _ => 0)
    (fun ω => g3Hν γ ω (Icc (-δ) 0)) ?_ ?_ (g3HonestFinStmt_main i hγ hγ2).ne ?_
  · simpa using h
  · filter_upwards [Ioo_mem_nhdsGT hδ] with a ha
    exact aemeasurable_hν_left hγ hγ2 i measurableSet_Icc
      (Icc_neg_subset_win i (by rw [hiδ]; linarith [ha.2, i.hη]))
  · filter_upwards [Ioo_mem_nhdsGT hδ] with a ha
    exact Eventually.of_forall fun ω => measure_mono (Icc_subset_Icc_left (by linarith [ha.2]))
  · filter_upwards [G3Fid.ae_normField_good gffBase.gff hγ hγ2] with ω hω
    exact tendsto_measure_Icc_neg_zero (qBoundaryMeasure_Icc_lt_top _ _ _ _).ne (hω.2.2 0)

/-- **`E min(ν_h[0, a], ν_h[−δ, 0]) → 0` as `a ↓ 0`** (dominated convergence). -/
theorem tendsto_lintegral_hν_right {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {δ : ℝ} (hδ : 0 < δ)
    (hδ4 : δ ≤ 1 / 4) :
    Tendsto (fun a => ∫⁻ ω, min (g3Hν γ ω (Icc 0 a)) (g3Hν γ ω (Icc (-δ) 0)) ∂gffBase.P)
      (𝓝[>] 0) (𝓝 0) := by
  set i := g3RefIdx δ hδ hδ4
  have hiδ : i.δ = δ := rfl
  have h := tendsto_lintegral_filter_of_dominated_convergence' (μ := gffBase.P)
    (l := 𝓝[>] (0 : ℝ)) (F := fun a ω => min (g3Hν γ ω (Icc 0 a)) (g3Hν γ ω (Icc (-δ) 0)))
    (f := fun _ => 0) (fun ω => g3Hν γ ω (Icc (-δ) 0)) ?_ ?_
    (g3HonestFinStmt_main i hγ hγ2).ne ?_
  · simpa using h
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with a ha
    exact (aemeasurable_hν_right hγ hγ2 i measurableSet_Icc
      (Icc_pos_subset_win i (by linarith [ha.2, i.hη]))).min
      (aemeasurable_hν_left hγ hγ2 i measurableSet_Icc
        (Icc_neg_subset_win i (by rw [hiδ]; linarith [i.hη])))
  · exact Eventually.of_forall fun a => Eventually.of_forall fun ω => min_le_right _ _
  · filter_upwards [G3Fid.ae_normField_good gffBase.gff hγ hγ2] with ω hω
    have h1 := (tendsto_measure_Icc_zero_pos (m := g3Hν γ ω)
      (qBoundaryMeasure_Icc_lt_top _ _ _ _).ne (hω.2.2 0)).min
      (tendsto_const_nhds (x := g3Hν γ ω (Icc (-δ) 0)))
    rwa [min_eq_left zero_le] at h1

end Thm18Asm
end QuantumZipper
