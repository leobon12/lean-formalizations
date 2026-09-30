import QuantumZipper.Proofs.Section5.Prop16LocCoupleAnnAsm
import QuantumZipper.Proofs.Section5.Prop16AN23Norm
import QuantumZipper.Proofs.Section5.Prop16AN23Pair

/-!
# DOM-a by annulus features (D34), node AN2: the free representation

**AN2** (`freeAnnRep_holds : FreeAnnRepStmt D S`, statement in `Prop16LocCoupleAnnNodes.lean`):
for `u ⊥ M̂` and an admissible `μ` carried by `K` (uniform local radius `2R`),
`⟪v̂_μ, u⟫ = ∫ ⟪v̂_{fold_{z,s}}, u⟫ dμ(z)` for `0 < s < 2R`.

The proof is the free-field copy of the mixed proof `K3.inner_rieszVec_eq_integral_of_mem_orthogonal`
(`MixedM5Rep.lean`, blueprint M4(ii)/M5), with `μ_t = μ.bind fold_{·,t}`:

* `inner_freeVec_bind_eq_integral`: the weak Bochner identity `⟪v̂_{μ_t}, u⟫ = ∫ ⟪v̂_{fold_{z,t}}, u⟫ dμ`
  for every `u` (on the dense test vectors `anTest` it is Fubini for `anPhi g`,
  `CircleFubini.integral_bind_circle`; then `K3.inner_eq_integral_of_mem_closure_span`, with the
  uniform bound `exists_norm_freeVec_le_an` on `‖v̂_{fold_{z,t}}‖`);
* `tendsto_inner_freeVec_bind`: `v̂_{μ_t} → v̂_μ` weakly as `t → 0⁺` (on test vectors:
  `K3.tendsto_integral_bind_foldedCircle` for the continuous `anPhi g`; then
  `K3.tendsto_inner_of_mem_closure_span`, with the uniform bound on `‖v̂_{μ_t}‖` from
  `K3.lintegral_negLog_bind_le`);
* the mean value property `freeFold_inner_eq_of_radii` (`u ⊥ M̂` does not see the radius), so the
  pairing `⟪v̂_{μ_t}, u⟫` is constant `= ∫ ⟪v̂_{fold_{z,s}}, u⟫ dμ` for small `t`.

Source: Sheffield, *Gaussian free fields for mathematicians*, PTRF 139 (2007), Thm 2.17 (orthogonal
splitting of the Dirichlet space; the harmonic part is characterised by the mean value property).
The localisation by annulus features and the weak-limit argument are our own (decision D34),
copying the mixed-field proof. (A remark on an earlier draft of this file: it claimed that
`v̂_{μ_t}` cannot converge because the energy of the *integrand* `fold_{z,t} − fold_{z,s}` diverges
like `log(s/t)`; that does not bound the energy of the *integral*, and weak convergence holds, as
proved here.)
-/

noncomputable section

open MeasureTheory Set Metric Filter
open scoped RealInnerProductSpace ENNReal Topology

namespace QuantumZipper

namespace Prop16Asm

open GFFExist K3

variable {D S : Set ℂ}

/-! ## The free mean value property (pairing form) -/

/-- `v̂_{fold_{z,s}} − v̂_{fold_{z,s'}}` is the free annulus feature `freeAnnFeat z s s'`. -/
theorem freeFold_sub_eq_annFree {z : ℂ} {s s' : ℝ} (hz : z ∈ Hbar) (hs : 0 < s) (hs' : 0 < s') :
    freeFold z s - freeFold z s' = freeAnnFeat z s s' := by
  rw [freeFold_eq hz hs, freeFold_eq hz hs', ← freeAnnFeat_eq hz hs hs']

/-- **Mean value property, free side (pairing form).** For `u ⊥ M̂` the pairing of `v̂_{fold_{z,s}}`
with `u` does not depend on the (local) radius `s`. -/
theorem freeFold_inner_eq_of_radii {z : ℂ} {s s' R0 : ℝ} (hloc : LocalBall D S z R0)
    (hs : 0 < s) (hs' : 0 < s') (hsR : s < R0) (hs'R : s' < R0) {u : HkE}
    (hu : u ∈ (freeAnnSpan D S)ᗮ) : ⟪freeFold z s, u⟫ = ⟪freeFold z s', u⟫ := by
  have key : ∀ {a b : ℝ}, 0 < a → a < b → b < R0 → ⟪freeFold z a, u⟫ = ⟪freeFold z b, u⟫ := by
    intro a b ha hab hbR
    have hmem : freeAnnFeat z a b ∈ freeAnnSpan D S := by
      have h1 := annFree_mem (D := D) (S := S) ⟨(z, a, b, R0), hloc, ha, hab, hbR⟩
      simpa only [annFree] using h1
    have h0 : ⟪freeAnnFeat z a b, u⟫ = 0 := Submodule.inner_right_of_mem_orthogonal hmem hu
    rw [← freeFold_sub_eq_annFree hloc.1 ha (ha.trans hab), inner_sub_left, sub_eq_zero] at h0
    exact h0
  rcases lt_trichotomy s s' with h | rfl | h
  · exact key hs h hs'R
  · rfl
  · exact (key hs' h hsR).symm

/-! ## Free vectors of smeared measures -/

open Classical in
/-- The free vector of a measure (zero if not admissible). -/
def freeVecM (ρ : Measure ℂ) : HkE := if h : IsAdmissibleH ρ then freeVec ⟨ρ, h⟩ else 0

theorem freeVecM_eq {ρ : Measure ℂ} (h : IsAdmissibleH ρ) : freeVecM ρ = freeVec ⟨ρ, h⟩ := by
  simp [freeVecM, h]

theorem inner_freeFold_anTest {z : ℂ} {t : ℝ} (hz : z ∈ Hbar) (ht : 0 < t) {g : HkE}
    (hg : g ∈ anTest) :
    ⟪freeFold z t, g⟫ = ∫ x, anPhi g x ∂(foldedCircle z t) - ∫ x, anPhi g x ∂gffExRef := by
  rw [freeFold_eq hz ht, inner_freeVec_anTest _ hg]
  simp only [probReal_univ, one_mul]

theorem integrable_anPhi {g : HkE} (hg : g ∈ anTest) (ν : Measure ℂ) [IsFiniteMeasure ν] :
    Integrable (anPhi g) ν :=
  Integrable.of_bound (continuous_anPhi hg).aestronglyMeasurable _
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact abs_anPhi_le hg x)

/-- **Weak Bochner identity.** `⟪v̂_{μ_t}, u⟫ = ∫ ⟪v̂_{fold_{z,t}}, u⟫ dμ(z)` for every `u`. -/
theorem inner_freeVec_bind_eq_integral {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ Hbar)
    (μ : AdmT) (hμK : μ.1 Kᶜ = 0) {t : ℝ} (ht : 0 < t) (u : HkE) :
    ⟪freeVecM (μ.1.bind fun w => foldedCircle w t), u⟫ = ∫ z, ⟪freeFold z t, u⟫ ∂μ.1 := by
  have := μ.2.1
  have := CircleFubini.isFiniteMeasure_bind_circle (r := t) μ.1
  have hae : ∀ᵐ z ∂μ.1, z ∈ K := mem_ae_iff.mpr hμK
  obtain ⟨Rk, hRk⟩ := hK.isBounded.subset_closedBall 0
  obtain ⟨B, hB⟩ := exists_norm_freeVec_le_an (Rk + t)
    (C := 2 * ENNReal.ofReal (Real.log 2 + |Real.log t|)) (by finiteness) 1
  have hBz : ∀ᵐ z ∂μ.1, ‖freeFold z t‖ ≤ B := by
    filter_upwards [hae] with z hz
    have hzR : ‖z‖ ≤ Rk := by
      have := hRk hz; rwa [mem_closedBall, dist_zero_right] at this
    rw [freeFold_eq (hKH hz) ht]
    refine hB _ ?_ (lintegral_negLog_foldedCircle_le z ht) (by simp)
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp
      (K3.foldedCircle_compl_eq_zero (hKH hz) ht.le)] with x hx
    have hx' := (not_not.mp hx).1
    rw [mem_closedBall, dist_eq_norm] at hx'
    calc ‖x‖ = ‖(x - z) + z‖ := by rw [sub_add_cancel]
      _ ≤ ‖x - z‖ + ‖z‖ := norm_add_le _ _
      _ ≤ Rk + t := by linarith
  have hμt := K3.isAdmissibleH_bind μ.2 ht
  rw [freeVecM_eq hμt]
  have hu : u ∈ (Submodule.span ℝ anTest).topologicalClosure := by
    rw [anTest_dense]; trivial
  have hfold : ∀ g ∈ anTest, ∀ᵐ z ∂μ.1,
      ∫ x, anPhi g x ∂(foldedCircle z t) - ∫ x, anPhi g x ∂gffExRef = ⟪freeFold z t, g⟫ := by
    intro g hg
    filter_upwards [hae] with z hz
    exact (inner_freeFold_anTest (hKH hz) ht hg).symm
  refine (inner_eq_integral_of_mem_closure_span (G := anTest) hBz ?_ ?_ hu).2
  · intro g hg
    obtain ⟨hI, -⟩ := CircleFubini.integral_bind_circle (r := t) μ.1 (integrable_anPhi hg _)
    exact (hI.sub (integrable_const _)).aestronglyMeasurable.congr (hfold g hg)
  · intro g hg
    obtain ⟨hI, hEq⟩ := CircleFubini.integral_bind_circle (r := t) μ.1 (integrable_anPhi hg _)
    rw [inner_freeVec_anTest _ hg, ← integral_congr_ae (hfold g hg),
      integral_sub hI (integrable_const _), integral_const, smul_eq_mul, ← hEq]
    simp only [measureReal_def, CircleFubini.bind_circle_univ]

/-- **Weak convergence** `v̂_{μ_t} → v̂_μ` as `t → 0⁺`. -/
theorem tendsto_inner_freeVec_bind {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ Hbar)
    (μ : AdmT) (hμK : μ.1 Kᶜ = 0) (u : HkE) :
    Tendsto (fun t => ⟪freeVecM (μ.1.bind fun w => foldedCircle w t), u⟫) (𝓝[>] 0)
      (𝓝 ⟪freeVec μ, u⟫) := by
  have := μ.2.1
  obtain ⟨-, -, C, hC, hbd⟩ := μ.2
  obtain ⟨R1, hR1⟩ := (hK.cthickening (r := 1)).isBounded.subset_closedBall 0
  obtain ⟨B, hB⟩ := exists_norm_freeVec_le_an R1
    (C := 2 * C + 2 * ENNReal.ofReal 1 * μ.1 univ) (by finiteness) (μ.1.real univ)
  have hu : u ∈ (Submodule.span ℝ anTest).topologicalClosure := by
    rw [anTest_dense]; trivial
  refine tendsto_inner_of_mem_closure_span (G := anTest) (B := B) ?_ ?_ hu
  · filter_upwards [Ioc_mem_nhdsGT zero_lt_one] with t ht
    have hμt := K3.isAdmissibleH_bind μ.2 ht.1
    have := CircleFubini.isFiniteMeasure_bind_circle (r := t) μ.1
    rw [freeVecM_eq hμt]
    refine hB _ ?_ (fun y => ?_) ?_
    · filter_upwards [measure_eq_zero_iff_ae_notMem.mp
        (bind_cthickening_compl hK hKH hμK ht.1.le ht.2)] with x hx
      have := hR1 (not_not.mp hx).1
      rwa [mem_closedBall, dist_zero_right] at this
    · refine (lintegral_negLog_bind_le μ.2 hbd ht.1 y).trans ?_
      gcongr
      exact ht.2
    · simp only [measureReal_def, CircleFubini.bind_circle_univ, le_refl]
  · intro g hg
    have hT := (tendsto_integral_bind_foldedCircle hK hKH hμK (continuous_anPhi hg)).sub_const
      (μ.1.real univ * ∫ x, anPhi g x ∂gffExRef)
    rw [inner_freeVec_anTest _ hg]
    refine hT.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    have := CircleFubini.isFiniteMeasure_bind_circle (r := t) μ.1
    rw [freeVecM_eq (K3.isAdmissibleH_bind μ.2 ht), inner_freeVec_anTest _ hg]
    simp only [measureReal_def, CircleFubini.bind_circle_univ]

/-- **AN2 (proved).** The free representation `FreeAnnRepStmt D S`. -/
theorem freeAnnRep_holds (D S : Set ℂ) : FreeAnnRepStmt D S := by
  intro K R h μ hμK s hs hsR u hu
  have hKH : K ⊆ Hbar := fun z hz => (h.local_ z hz).1
  have hT := tendsto_inner_freeVec_bind h.compact hKH μ hμK u
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∫ z, ⟪freeFold z s, u⟫ ∂μ.1 =
      ⟪freeVecM (μ.1.bind fun w => foldedCircle w t), u⟫ := by
    filter_upwards [Ioo_mem_nhdsGT (lt_min hs h.pos)] with t ht
    have ht2 : t < 2 * R := by linarith [ht.2.trans_le (min_le_right _ _), h.pos]
    rw [inner_freeVec_bind_eq_integral h.compact hKH μ hμK ht.1 u]
    refine integral_congr_ae ?_
    filter_upwards [mem_ae_iff.mpr hμK] with z hz
    exact freeFold_inner_eq_of_radii (h.local_ z hz) hs ht.1 hsR ht2 hu
  exact tendsto_nhds_unique hT (tendsto_const_nhds.congr' hev)

end Prop16Asm

end QuantumZipper
