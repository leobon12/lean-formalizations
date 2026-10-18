import MeshOnly.MeshOnlyEnergy
import MeshOnly.MeshOnlySobolevSupport
import MeshOnly.MeshOnlySobolevSupportVolume
import BouRabeeGwynne.Section3CompactCollar

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal
open MeasureTheory

namespace BouRabeeGwynne.MeshRates

/-- The constant `C_{d,K}` of MR Lemma 5.1, (64): `9 d vol(K) (1 + C_N vol(K)^{2/d} + √C_N vol(K)^{1/d})`,
where `C_N = nashConstant d` is the constant of the support inequality (23). It depends only on `d`
and `K`. -/
noncomputable def lemma51Constant (d : ℕ) (K : Set (Euc d)) : ℝ :=
  9 * (d : ℝ) * (volume K).toReal *
    (1 + MeshOnlySobolev.nashConstant d * (volume K).toReal ^ (2 / (d : ℝ)) +
      Real.sqrt (MeshOnlySobolev.nashConstant d) * (volume K).toReal ^ (1 / (d : ℝ)))

open Classical in
/-- MR Lemma 5.1, (64): for all sufficiently small mesh (threshold depending only on `U` and `K`),
`D(f) + ‖f‖²_{2,m} ≤ C_{d,K} M² ε²` for `f = h_D - h_C` on the closed region `V[U] ∪ ∂V[U]`, where
`M` bounds `‖∇²h_C‖` on `K`. -/
theorem lemma51_energy_and_l2_error {d : ℕ} (hd : 2 ≤ d) {U K : Set (Euc d)}
    (hUb : Bornology.IsBounded U) (hK : IsOpen K) (hKb : Bornology.IsBounded K)
    (hUK : closure U ⊆ K) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ (T : OrthogonalTiling d), HasAmbientCollar K T.domain →
      T.mesh ≤ ENNReal.ofReal ε₀ → (T.closedVertices U).Finite ∧ ∀ [Fintype (T.closedVertices U)]
      (h : Euc d → ℝ) (W : Set (Euc d)) (hD : T.V → ℝ) (M : ℝ),
      0 ≤ M → IsOpen W → closure K ⊆ W → IsHarmonicOn h W →
      (∀ x ∈ K, ‖fderiv ℝ (fderiv ℝ h) x‖ ≤ M) →
      T.SolvesDirichlet U (fun v => h (T.pos v)) hD →
      (T.finiteNetwork (T.closedVertices U)).energy (fun v => hD v - h (T.pos v)) +
          ∑ v : T.closedVertices U, (T.cell v).volume.toReal * (hD v - h (T.pos v)) ^ 2 ≤
        lemma51Constant d K * M ^ 2 * T.mesh.toReal ^ 2 := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  obtain ⟨ρ, hρ, hρK⟩ := hUb.isCompact_closure.exists_cthickening_subset_open hK hUK
  refine ⟨min 1 (ρ / 4), lt_min one_pos (by positivity), ?_⟩
  intro T hcol hmeshle
  have hε0 : 0 ≤ min 1 (ρ / 4) := le_min zero_le_one (by positivity)
  have hmesh : T.mesh ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hmeshle
  have hεle : T.mesh.toReal ≤ min 1 (ρ / 4) :=
    (ENNReal.toReal_le_toReal hmesh ENNReal.ofReal_ne_top).2 hmeshle |>.trans
      (ENNReal.toReal_ofReal hε0).le
  have hε1 : T.mesh.toReal ≤ 1 := hεle.trans (min_le_left _ _)
  have hερ : 4 * T.mesh.toReal ≤ ρ := by linarith [min_le_right 1 (ρ / 4)]
  have hε : 0 ≤ T.mesh.toReal := ENNReal.toReal_nonneg
  let R := T.closedVertices U
  have hball : ∀ v : R, Metric.closedBall (T.pos v) (2 * T.mesh.toReal) ⊆ K := fun v =>
    (T.closedVertex_ball_subset_cthickening hmesh v.property).trans
      ((Metric.cthickening_mono hερ (closure U)).trans hρK)
  have hcell : ∀ v : R, (T.cell v).carrier ⊆ K := by
    intro v x hx
    apply hball v
    apply Metric.mem_closedBall.mpr
    have hdist := T.toTilingData.dist_pos_le_mesh hx hmesh
    linarith
  have hKD : K ⊆ interior T.domain := subset_closure.trans hcol
  refine ⟨T.closedVertices_finite hUb ((hUK.trans hKD).trans interior_subset) fun v hv =>
    (((T.toTilingData.cell_subset_cthickening hv hmesh (by linarith)).trans hρK).trans hKD).trans
      interior_subset, ?_⟩
  intro _ h W hD M hM hW hKW hh hH hsol
  have hm : (μHE[n + 1] : Measure (Euc (n + 1))) = volume := by
    simpa using InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := Euc (n + 1))
  have hKfin : volume K ≠ ∞ := hKb.measure_lt_top.ne
  -- (65)–(66)
  have hE := T.harmonic_error_energy_le_collar (by omega) U hD h hmesh hM hsol
    (Q := K) (W := W) (by rw [hm]; exact hKfin) hKD (subset_closure.trans hKW) hW hh
    hcell hball hH
  rw [hm] at hE
  -- (23) with V_f ≤ vol(K)
  let u : R → ℝ := fun v => hD v - h (T.pos v)
  have hactive : ∀ v : R, u v ≠ 0 → T.pos v ∈ U := by
    intro v hv
    by_contra hout
    have heq := hsol.2 v (v.property.resolve_left hout)
    exact hv (by dsimp [u]; rw [heq, sub_self])
  have hneighbors : ∀ v : R, u v ≠ 0 → ∀ w : T.V, T.adj v w → w ∈ R :=
    fun v hv w hw => T.neighbor_mem_closedVertices (hactive v hv) hw
  let V : ℝ := (volume K).toReal
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  have hsupport : (∑ v : R, if u v ≠ 0 then (T.cell v).volume.toReal else 0) ≤ V :=
    T.meshOnly_supportVolume_le (by omega) R u K hK.measurableSet hKfin
      (fun v _ => hcell v)
  have hs := T.meshOnly_support_bound hd R u hmesh (fun v _ => (hcell v).trans hKD)
    hneighbors V hV hsupport
  let C₀ := MeshOnlySobolev.nashConstant (n + 1)
  have hC₀ : 0 ≤ C₀ := (MeshOnlySobolev.nashConstant_pos hd).le
  let B := C₀ * V ^ (2 / ((n + 1 : ℕ) : ℝ)) + Real.sqrt C₀ * V ^ (1 / ((n + 1 : ℕ) : ℝ))
  have hcoeff : C₀ * V ^ (2 / ((n + 1 : ℕ) : ℝ)) +
      Real.sqrt C₀ * T.mesh.toReal * V ^ (1 / ((n + 1 : ℕ) : ℝ)) ≤ B := by
    have h1 := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hε1 (Real.sqrt_nonneg C₀))
      (Real.rpow_nonneg hV (1 / ((n + 1 : ℕ) : ℝ)))
    dsimp [B]
    linarith only [h1]
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hEn : 0 ≤ (T.finiteNetwork R).energy u := (T.finiteNetwork R).energy_nonneg u
  have hL : (∑ v : R, (T.cell v).volume.toReal * u v ^ 2) ≤ B * (T.finiteNetwork R).energy u :=
    hs.trans (mul_le_mul_of_nonneg_right hcoeff hEn)
  change (T.finiteNetwork R).energy u + (∑ v : R, (T.cell v).volume.toReal * u v ^ 2) ≤ _
  have hE' : (T.finiteNetwork R).energy u ≤ 9 * ((n + 1 : ℕ) : ℝ) * V * M ^ 2 * T.mesh.toReal ^ 2 :=
    hE
  have hfin : lemma51Constant (n + 1) K = 9 * ((n + 1 : ℕ) : ℝ) * V * (1 + B) := by
    simp only [lemma51Constant, B, C₀, V]; ring
  rw [hfin]
  calc _ ≤ (1 + B) * (T.finiteNetwork R).energy u := by linarith
    _ ≤ (1 + B) * (9 * ((n + 1 : ℕ) : ℝ) * V * M ^ 2 * T.mesh.toReal ^ 2) :=
        mul_le_mul_of_nonneg_left hE' (by linarith)
    _ = _ := by ring

end BouRabeeGwynne.MeshRates
