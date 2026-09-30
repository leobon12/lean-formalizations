import QuantumZipper.Proofs.Thm18.G1ZA1a2Base
import QuantumZipper.Proofs.Thm18.G1Z2ReflChord

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1Z-A1a2: the side of `β` (`G1zBetaSideStmt`) and A1a from the separation of the sides

* `tendsto_reroot_of_base`: `a ψ'(u) → O^∓_t` as `u → β` (from `G1zBaseLimitStmt`, the limit of
  `ψ` at `0` and the affine factorization; the argument of `g1zRerootBdryStmt_of`).
* `beta_neg_of_left`, `beta_pos_of_right`: if `ψ = φ⁻¹` (`φ` a normalized uniformizer of the side
  component) tends to a real point `r` of the side half-line as `v → β` in `ℍ`, then `β` is in the
  side half-line: `φ` has boundary values `b` on the half-line with `b(r)` of the side's sign
  (`G1Chord.exists_boundary_values_normalized`, `G1Chord.boundary_neg_of_normalized`; right side by
  the reflection `z ↦ −z̄`, `G1Z2.normalized_refl`), and `β = lim φ(ψ(v)) = b(r)`.
* `g1zBetaSideStmt_of_base`, and **`g1RerootAffineStmt_of_disjoint : ChordSidesDisjointStmt →
  G1RerootAffineStmt`**.

Own elementary arguments on top of the proved boundary-value lemmas.
-/

noncomputable section

open Filter Set Complex Function Metric
open scoped Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G1ZA1a

open QuantumZipper.CA QuantumZipper.CA.Uniformizer

theorem tendsto_reroot_of_base (hL : G1zBaseLimitStmt) {W : ℝ → ℝ} (hG : G1zDrvGood W)
    {t a : ℝ} (ht : 0 < t) (ha : 0 < a) (left : Bool) {lam β : ℝ} (hlam : 0 < lam)
    (hEq : EqOn (fun u => fwdMapInv W t ((a : ℂ) * g1zSideMap left (g1zNewDrv W t a) (u + β)))
      (fun u => g1zSideMap left W (u / lam)) H) :
    Tendsto (fun u => (a : ℂ) * g1zSideMap left (g1zNewDrv W t a) u) (𝓝[H] (β : ℂ))
      (𝓝 (g1zSideImage left W t : ℂ)) := by
  have hW := hG.1
  have hW0 := hG.2.1
  have hη' := (g1zDrvGood_newDrv hG ht ha).2.2.2.1
  have hψ'b : MapsTo (g1zSideMap left (g1zNewDrv W t a)) H
      (sideDom (trace (g1zNewDrv W t a)) left) := by
    obtain ⟨hb, -⟩ := isNormalizedUniformizer_sideDom hη' left
    exact (BijOn.symm hb.invOn_invFunOn.symm hb).mapsTo
  -- `a ψ'(v) = f_t(ψ((v − β)/λ))`
  have hkey : ∀ v ∈ H, (a : ℂ) * g1zSideMap left (g1zNewDrv W t a) v =
      fwdMap W t (g1zSideMap left W ((v - β) / lam)) := by
    intro v hv
    have hvβ : v - (β : ℂ) ∈ H := by
      show 0 < (v - (β : ℂ)).im
      simpa using (show (0 : ℝ) < v.im from hv)
    have h := hEq hvβ
    simp only [sub_add_cancel] at h
    rw [← h, RS.fwdMap_fwdMapInv hW hW0 ht.le
      (ofReal_mul_mem_H ha (sideDom_subset_H _ left (hψ'b hv)))]
  have hlam' : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam.ne'
  have hin : Tendsto (fun v : ℂ => (v - β) / lam) (𝓝[H] (β : ℂ)) (𝓝[H] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun v hv => ?_⟩
    · have hc : Continuous fun v : ℂ => (v - β) / lam := by fun_prop
      have := hc.tendsto (β : ℂ)
      simp only [sub_self, zero_div] at this
      exact this.mono_left nhdsWithin_le_nhds
    · show 0 < ((v - β) / (lam : ℂ)).im
      rw [Complex.div_ofReal_im]
      exact div_pos (by simpa using (show (0 : ℝ) < v.im from hv)) hlam
  have h := (hL W hG t ht left).comp ((tendsto_sideMap_zero hG.2.2.2.1 left).comp hin)
  refine h.congr' (eventually_nhdsWithin_of_forall fun v hv => ?_)
  exact (hkey v hv).symm

theorem neBot_nhdsWithin_H_real (β : ℝ) : (𝓝[H] (β : ℂ)).NeBot := by
  refine mem_closure_iff_nhdsWithin_neBot.1 (mem_closure_of_tendsto (f := fun y : ℝ => (β : ℂ) + y * I)
    (b := 𝓝[>] (0 : ℝ)) ?_ ?_)
  · have hc : Continuous fun y : ℝ => (β : ℂ) + y * I := by fun_prop
    have := hc.tendsto 0
    simp only [Complex.ofReal_zero, zero_mul, add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with y hy
    show 0 < ((β : ℂ) + y * I).im
    simpa using (show (0 : ℝ) < y from hy)

theorem beta_neg_of_left {η : ℝ → ℂ} (hη : IsSimpleChord η) {φ : ℂ → ℂ}
    (hφ : IsNormalizedUniformizer (leftComponent η) φ) {β r : ℝ} (hr : r < 0)
    (h : Tendsto (invFunOn φ (leftComponent η)) (𝓝[H] (β : ℂ)) (𝓝 (r : ℂ))) : β < 0 := by
  obtain ⟨b, hb, -, hb0⟩ := G1Chord.exists_boundary_values_normalized hη hφ
  have hbneg := G1Chord.boundary_neg_of_normalized hη hφ hb hb0 r hr
  have hbij := hφ.1
  have hψL : Tendsto (invFunOn φ (leftComponent η)) (𝓝[H] (β : ℂ))
      (𝓝[leftComponent η] (r : ℂ)) :=
    tendsto_nhdsWithin_iff.2 ⟨h, eventually_nhdsWithin_of_forall fun v hv =>
      (BijOn.symm hbij.invOn_invFunOn.symm hbij).mapsTo hv⟩
  have h2 : Tendsto (fun v : ℂ => v) (𝓝[H] (β : ℂ)) (𝓝 (b r : ℂ)) :=
    ((hb r hr).comp hψL).congr' (eventually_nhdsWithin_of_forall fun v hv =>
      hbij.invOn_invFunOn.2 hv)
  have h3 : Tendsto (fun v : ℂ => v) (𝓝[H] (β : ℂ)) (𝓝 (β : ℂ)) := nhdsWithin_le_nhds
  haveI := neBot_nhdsWithin_H_real β
  have e : ((b r : ℝ) : ℂ) = β := tendsto_nhds_unique h2 h3
  have e' : b r = β := by exact_mod_cast e
  linarith

theorem beta_pos_of_right {η : ℝ → ℂ} (hη : IsSimpleChord η) {φ : ℂ → ℂ}
    (hφ : IsNormalizedUniformizer (rightComponent η) φ) {β r : ℝ} (hr : 0 < r)
    (h : Tendsto (invFunOn φ (rightComponent η)) (𝓝[H] (β : ℂ)) (𝓝 (r : ℂ))) : 0 < β := by
  have hη' := isSimpleChord_refl_comp hη
  have hφ' := G1Z2.normalized_refl hη hφ
  obtain ⟨b, hb, -, hb0⟩ := G1Chord.exists_boundary_values_normalized hη' hφ'
  have hbneg := G1Chord.boundary_neg_of_normalized hη' hφ' hb hb0 (-r) (by linarith)
  have hbij := hφ.1
  have hψR : ∀ v ∈ H, invFunOn φ (rightComponent η) v ∈ rightComponent η := fun v hv =>
    (BijOn.symm hbij.invOn_invFunOn.symm hbij).mapsTo hv
  have hrefl : Tendsto (fun v => refl (invFunOn φ (rightComponent η) v)) (𝓝[H] (β : ℂ))
      (𝓝[leftComponent (refl ∘ η)] ((-r : ℝ) : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun v hv =>
      refl_mem_left_of_mem_right (hψR v hv)⟩
    have := (continuous_refl.tendsto _).comp h
    rw [refl_ofReal] at this
    exact this
  have h2 : Tendsto (fun v : ℂ => refl v) (𝓝[H] (β : ℂ)) (𝓝 (b (-r) : ℂ)) :=
    ((hb (-r) (by linarith)).comp hrefl).congr' (eventually_nhdsWithin_of_forall fun v hv => by
      show refl (φ (refl (refl (invFunOn φ (rightComponent η) v)))) = refl v
      rw [refl_refl, hbij.invOn_invFunOn.2 hv])
  have h3 : Tendsto (fun v : ℂ => refl v) (𝓝[H] (β : ℂ)) (𝓝 (refl (β : ℂ))) :=
    (continuous_refl.tendsto _).mono_left nhdsWithin_le_nhds
  haveI := neBot_nhdsWithin_H_real β
  have e := tendsto_nhds_unique h2 h3
  rw [refl_ofReal] at e
  have e' : b (-r) = -β := by exact_mod_cast e
  linarith

theorem g1zSideImage_mem_half {W : ℝ → ℝ} (hG : G1zDrvGood W) {t : ℝ} (ht : 0 < t)
    (left : Bool) : g1zSideImage left W t ∈ g1SideHalf left := by
  have hW := hG.1
  have hW0 := hG.2.1
  set V := ArcDriver.trev W t with hVdef
  have hVc : Continuous V := ArcDriver.continuous_trev hW t
  have hV0 : V 0 = 0 := ArcDriver.trev_zero W t
  have hK' : IsSimpleCurveHull (revHull V t) := by
    rw [hVdef, ArcDriver.revHull_trev hW hW0 ht]; exact isSimpleCurveHull_of_good hG ht
  obtain ⟨F, hF⟩ := CaraR.revMapCaratheodory V hVc hV0 t ht hK'
  obtain ⟨hzm, hzp, -⟩ := car_zero_facts hVc ht hF
    (WeldingConsistency.simpleCurveHull_nonempty hK')
  cases left
  · show (sideImages W t).2 ∈ Ioi 0
    rw [sideImages_snd_eq_zeroPlus_trev hG ht]; exact hzp
  · show (sideImages W t).1 ∈ Iio 0
    rw [sideImages_fst_eq_zeroMinus_trev' hW hW0 ht (isSimpleCurveHull_of_good hG ht)
      (fun x hx => real_alive_of_good hG ht.le hx)]
    exact hzm

/-- **`G1zBetaSideStmt` from the base limit.** -/
theorem g1zBetaSideStmt_of_base (hL : G1zBaseLimitStmt) : G1zBetaSideStmt := by
  intro W hG t a ht ha left lam β hlam hEq
  have hlim := tendsto_reroot_of_base hL hG ht ha left hlam hEq
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hψ : Tendsto (g1zSideMap left (g1zNewDrv W t a)) (𝓝[H] (β : ℂ))
      (𝓝 ((g1zSideImage left W t / a : ℝ) : ℂ)) := by
    have := hlim.div_const (a : ℂ)
    push_cast
    refine this.congr fun u => ?_
    field_simp
  have hη' := (g1zDrvGood_newDrv hG ht ha).2.2.2.1
  have hO := g1zSideImage_mem_half hG ht left
  cases left
  · have hr : 0 < g1zSideImage false W t / a := div_pos (by simpa [g1SideHalf] using hO) ha
    show β ∈ Ioi 0
    exact beta_pos_of_right hη' (isNormalizedUniformizer_sideDom hη' false) hr hψ
  · have hr : g1zSideImage true W t / a < 0 :=
      div_neg_of_neg_of_pos (by simpa [g1SideHalf] using hO) ha
    show β ∈ Iio 0
    exact beta_neg_of_left hη' (isNormalizedUniformizer_sideDom hη' true) hr hψ

/-- **A1a (`G1RerootAffineStmt`) from the separation of the two sides of a simple chord.** -/
theorem g1RerootAffineStmt_of_disjoint (hD : ChordSidesDisjointStmt) : G1RerootAffineStmt :=
  g1RerootAffineStmt_of_base_beta (g1zBaseLimitStmt_of_disjoint hD)
    (g1zBetaSideStmt_of_base (g1zBaseLimitStmt_of_disjoint hD))

end G1ZA1a
end Thm18Asm
end QuantumZipper
