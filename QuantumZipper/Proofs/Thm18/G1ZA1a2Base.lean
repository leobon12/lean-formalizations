import QuantumZipper.Proofs.Thm18.G1ZA1a2Alive
import QuantumZipper.Proofs.Zipper.F1Side3
import QuantumZipper.Proofs.Zipper.B5VSide
import QuantumZipper.Proofs.Zipper.F2Weld
import QuantumZipper.Proofs.Zipper.Cor15HullNull
import QuantumZipper.Proofs.Thm18.G4BSideGeom
import QuantumZipper.Proofs.Loewner.WeldingConsistency

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1Z-A1a2: the base limit `G1zBaseLimitStmt` from the separation of the two sides

* `sideImages_fst_eq_zeroMinus_trev`, `sideImages_snd_eq_zeroPlus_trev`: for a good driver
  `O⁻_t = 0⁻`, `O⁺_t = 0⁺` of `V = trev W t` (`B5.sideImages_fst_eq_zeroMinus_vrev` with the
  proved aliveness `real_alive_of_good`; the right side by the reflection `W ↦ −W`,
  `F1.sideImages_reflect_swap`, `G4Core.zeroPlus_eq_neg_zeroMinus_neg`).
* `g1zBaseLimitStmt_of_disjoint`: `G1zBaseLimitStmt` from `ChordSidesDisjointStmt` (the two
  complementary components of a simple chord are disjoint — the Jordan-curve separation, e.g.
  Pommerenke, *Boundary Behaviour of Conformal Maps*, §1.3, Newman, *Elements of the Topology of
  Plane Sets of Points*, Ch. V). Route (own argument): for `z → 0` in the side component,
  `w = f_t(z)` stays bounded in `ℍ`; a cluster point `w*` has `F(w*) = 0` for the Carathéodory
  extension `F` of `f_t⁻¹`, so `w* ∈ {0⁻, 0⁺}` (`IsCaratheodoryRevExt`, welding relation); the
  wrong one is excluded because `f_t⁻¹` sends points of `ℍ` near it into the other component
  (`g1zCompTransportStmt_holds` with `a = 1`); compactness gives the limit.
-/

noncomputable section

open Filter Set Complex Function Metric
open scoped Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G1ZA1a

open QuantumZipper.CA QuantumZipper.CA.Uniformizer

/-- **Separation of the two sides of a simple chord** (open node). -/
def ChordSidesDisjointStmt : Prop :=
  ∀ η : ℝ → ℂ, IsSimpleChord η → Disjoint (leftComponent η) (rightComponent η)

theorem isSimpleCurveHull_of_good {W : ℝ → ℝ} (hG : G1zDrvGood W) {t : ℝ} (ht : 0 < t) :
    IsSimpleCurveHull (fwdHull W t) := by
  have h := isSimpleCurveHull_fwdHull_shift hG.1 hG.2.1 hG.2.2.2.1 hG.2.2.2.2 le_rfl ht
  have e : (fun s => W (0 + s) - W 0) = W := by funext s; simp [hG.2.1]
  rwa [e, sub_zero] at h

theorem sideImages_fst_eq_zeroMinus_trev' {U : ℝ → ℝ} (hU : Continuous U) (hU0 : U 0 = 0)
    {t : ℝ} (ht : 0 < t) (hK : IsSimpleCurveHull (fwdHull U t))
    (halive : ∀ x : ℝ, x ≠ 0 → ∃ v, IsForwardSol U (x : ℂ) t v) :
    (sideImages U t).1 = zeroMinus (ArcDriver.trev U t) t := by
  rw [B5.sideImages_fst_eq_zeroMinus_vrev hU hU0 ht
    (by rw [Cor15Group.revHull_vrev_eq_fwdHull hU hU0 ht]; exact hK) halive]
  refine F2.zeroMinus_congr_drive fun r hr => ?_
  simp [B2.vrev, ArcDriver.trev, max_eq_left hr.1, min_eq_left hr.2]

theorem sideImages_snd_eq_zeroPlus_trev {W : ℝ → ℝ} (hG : G1zDrvGood W) {t : ℝ} (ht : 0 < t) :
    (sideImages W t).2 = zeroPlus (ArcDriver.trev W t) t := by
  have hW := hG.1
  have hW0 := hG.2.1
  have halive : ∀ x : ℝ, x ≠ 0 → ∃ v, IsForwardSol W (x : ℂ) t v := fun x hx =>
    real_alive_of_good hG ht.le hx
  obtain ⟨a, b, hL, hR⟩ := F1.exists_tendsto_sideImages_of_alive ht.le halive
  have hsw := F1.sideImages_reflect_swap ht.le hL hR
  have haliveN : ∀ x : ℝ, x ≠ 0 → ∃ v, IsForwardSol (fun s => -W s) (x : ℂ) t v := by
    intro x hx
    obtain ⟨v, hv⟩ := real_alive_of_good hG ht.le (neg_ne_zero.2 hx)
    have h := RS.isForwardSol_neg hv
    simp only [Complex.ofReal_neg, neg_neg] at h
    exact ⟨_, h⟩
  have h1 := sideImages_fst_eq_zeroMinus_trev' (U := fun s => -W s) hW.neg (by simp [hW0]) ht
    (isSimpleCurveHull_fwdHull_neg ht.le (isSimpleCurveHull_of_good hG ht)) haliveN
  have hneg : (fun s => -W s) = -W := rfl
  rw [hneg, hsw] at h1
  have hV : Continuous (ArcDriver.trev W t) := ArcDriver.continuous_trev hW t
  rw [G4Core.zeroPlus_eq_neg_zeroMinus_neg hV ht.le]
  have htr : -ArcDriver.trev W t = ArcDriver.trev (-W) t := by
    funext r; simp [ArcDriver.trev]; ring
  rw [htr, ← h1]
  simp

/-- Zeros of the Carathéodory extension of `revMap V T`: exactly `0⁻ < 0 < 0⁺`. -/
theorem car_zero_facts {V : ℝ → ℝ} (hV : Continuous V) {T : ℝ} (hT : 0 < T) {F : ℂ → ℂ}
    (hF : Blueprint.IsCaratheodoryRevExt V T F) (hne : (revHull V T).Nonempty) :
    zeroMinus V T < 0 ∧ 0 < zeroPlus V T ∧
      ∀ c : ℝ, F c = 0 → c = zeroMinus V T ∨ c = zeroPlus V T := by
  obtain ⟨hzm, hzp, -⟩ := WeldingConsistency.car_basic hV hT hF hne
  have hFzm : F (zeroMinus V T) = 0 := hF.2.2.2.1
  have hFzp : F (zeroPlus V T) = 0 := by
    rw [← hFzm]
    refine (hF.2.2.2.2.2.2 _ (by simp [Hbar]) _ (by simp [Hbar])).2
      (Or.inr ⟨zeroMinus V T, ⟨le_rfl, hzm.le⟩, Or.inr ⟨by rw [hF.2.2.2.2.1], rfl⟩⟩)
  refine ⟨hzm, hzp, fun c hc => ?_⟩
  rcases le_or_gt c 0 with h | h
  · exact Or.inl (WeldingConsistency.car_eq_zeroMinus hF hzm hzp h hc)
  · right
    have := (hF.2.2.2.2.2.2 _ (by simp [Hbar]) _ (by simp [Hbar])).1
      (show F c = F (zeroPlus V T) by rw [hc, hFzp])
    rcases this with h1 | ⟨s', hs', ⟨h1, -⟩ | ⟨-, h2⟩⟩
    · exact_mod_cast h1
    · have := Complex.ofReal_injective h1; linarith [hs'.2]
    · have := Complex.ofReal_injective h2; linarith [hs'.2]

/-- **Core of the base limit.** -/
theorem base_limit_core {W : ℝ → ℝ} (hG : G1zDrvGood W) {t : ℝ} (ht : 0 < t) (left : Bool)
    (hdisj : Disjoint (sideDom (trace W) left) (sideDom (trace W) (!left))) {F : ℂ → ℂ}
    (hFc : ContinuousOn F Hbar) (hFeq : EqOn F (fwdMapInv W t) H) {p q : ℝ}
    (hzeros : ∀ c : ℝ, F c = 0 → c = p ∨ c = q) (hq : q ∈ g1SideHalf (!left)) :
    Tendsto (fwdMap W t) (𝓝[sideDom (trace W) left] 0) (𝓝 (p : ℂ)) := by
  have hW := hG.1
  have hW0 := hG.2.1
  set D := sideDom (trace W) left with hDdef
  obtain ⟨C, hC⟩ := exists_bound_fwdMapInv hG ht
  have hη1 := (g1zDrvGood_newDrv hG ht one_pos).2.2.2.1
  obtain ⟨δ, hδ, hδq⟩ := sideDom_nhd hη1 (!left) hq
  have hT1 := g1zCompTransportStmt_holds W hG t 1 ht one_pos (!left)
  have hnear : ∀ w ∈ H, dist w (q : ℂ) < δ → fwdMapInv W t w ∈ sideDom (trace W) (!left) :=
    fun w hw hd => by simpa using hT1.mapsTo (hδq w hw hd)
  have hDsub : D ⊆ H \ fwdHull W t := fun z hz =>
    slitH_subset_compl_fwdHull hG ht (by cases left <;> exact hz.1)
  have hgH : ∀ z ∈ D, fwdMap W t z ∈ H := fun z hz => FwdHolo.mapsTo_fwdMap hW ht.le (hDsub hz)
  have hinv : ∀ z ∈ D, fwdMapInv W t (fwdMap W t z) = z := fun z hz =>
    RS.fwdMapInv_fwdMap hW hW0 ht.le (hDsub hz)
  have hFg : ∀ z ∈ D, F (fwdMap W t z) = z := fun z hz => by rw [hFeq (hgH z hz), hinv z hz]
  have hnorm : ∀ z ∈ D, ‖fwdMap W t z‖ ≤ ‖z‖ + C := fun z hz => by
    have h1 := hC _ (hgH z hz)
    rw [hinv z hz, norm_sub_rev] at h1
    have h2 := norm_sub_norm_le (fwdMap W t z) z
    linarith
  set s := closedBall (0 : ℂ) (1 + C) ∩ Hbar with hsdef
  have hs : IsCompact s := (isCompact_closedBall _ _).inter_right isClosed_Hbar
  have hev : ∀ᶠ z in 𝓝[D] (0 : ℂ), z ∈ D ∧ ‖z‖ < 1 :=
    (show ∀ᶠ z in 𝓝[D] (0 : ℂ), z ∈ D from self_mem_nhdsWithin).and (nhdsWithin_le_nhds
      ((isOpen_lt continuous_norm continuous_const).mem_nhds (by simp)))
  have hmem : ∀ᶠ z in 𝓝[D] (0 : ℂ), fwdMap W t z ∈ s := hev.mono fun z hz =>
    ⟨mem_closedBall_zero_iff.2 (by linarith [hnorm z hz.1]),
      show 0 ≤ (fwdMap W t z).im from le_of_lt (hgH z hz.1)⟩
  refine hs.tendsto_nhds_of_unique_mapClusterPt hmem fun w hw hcl => ?_
  have hmapH : Tendsto (fwdMap W t) (𝓝[D] 0) (𝓟 Hbar) :=
    tendsto_principal.2 (hmem.mono fun z hz => hz.2)
  have h1 : MapClusterPt (F w) (𝓝[D] 0) (F ∘ fwdMap W t) :=
    hcl.tendsto_comp' ((hFc w hw.2).tendsto.mono_left (inf_le_inf_left (𝓝 w) hmapH))
  have h2 : MapClusterPt (F w) (𝓝[D] 0) id :=
    (Filter.EventuallyEq.mapClusterPt_iff (hev.mono fun z hz => hFg z hz.1)).1 h1
  have hFw : F w = 0 := by
    have h3 : ClusterPt (F w) (𝓝[D] (0 : ℂ)) := mapClusterPt_id_iff.1 h2
    exact eq_of_nhds_neBot (h3.mono nhdsWithin_le_nhds)
  have hwim : w.im = 0 := by
    rcases eq_or_lt_of_le (show 0 ≤ w.im from hw.2) with h | h
    · exact h.symm
    · exfalso
      have h4 := RS.fwdMapInv_mem_H hW hW0 ht.le (show w ∈ H from h)
      rw [← hFeq (show w ∈ H from h), hFw] at h4
      exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from h4)
  have hwre : w = (w.re : ℂ) := Complex.ext (by simp) (by simp [hwim])
  rw [hwre] at hFw
  rcases hzeros w.re hFw with h | h
  · rw [hwre, h]
  · exfalso
    have hfr := (mapClusterPt_iff_frequently.1 hcl) (ball w δ) (ball_mem_nhds w hδ)
    obtain ⟨z, hzb, hzD⟩ := (hfr.and_eventually hev).exists
    have hd : dist (fwdMap W t z) (q : ℂ) < δ := by
      have : dist (fwdMap W t z) w < δ := hzb
      rwa [hwre, h] at this
    have hgz := hnear _ (hgH z hzD.1) hd
    rw [hinv z hzD.1] at hgz
    exact Set.disjoint_left.1 hdisj hzD.1 hgz

/-- **`G1zBaseLimitStmt` from the separation of the two sides.** -/
theorem g1zBaseLimitStmt_of_disjoint (hD : ChordSidesDisjointStmt) : G1zBaseLimitStmt := by
  intro W hG t ht left
  have hW := hG.1
  have hW0 := hG.2.1
  have hη := hG.2.2.2.1
  set V := ArcDriver.trev W t with hVdef
  have hVc : Continuous V := ArcDriver.continuous_trev hW t
  have hV0 : V 0 = 0 := ArcDriver.trev_zero W t
  have hK' : IsSimpleCurveHull (revHull V t) := by
    rw [hVdef, ArcDriver.revHull_trev hW hW0 ht]; exact isSimpleCurveHull_of_good hG ht
  obtain ⟨F, hF⟩ := CaraR.revMapCaratheodory V hVc hV0 t ht hK'
  have hFeq : EqOn F (fwdMapInv W t) H := fun u hu => by
    rw [hF.1 hu, UnzipInvariance.fwdMapInv_eq_revMap_timeRev W hW hW0 ht.le hu]
    rfl
  obtain ⟨hzm, hzp, hzeros⟩ := car_zero_facts hVc ht hF
    (WeldingConsistency.simpleCurveHull_nonempty hK')
  cases left
  · have h := base_limit_core hG ht false (hD _ hη).symm hF.2.1 hFeq
      (p := zeroPlus V t) (q := zeroMinus V t) (fun c hc => (hzeros c hc).symm)
      (by simp [g1SideHalf, hzm])
    show Tendsto _ _ (𝓝 (((sideImages W t).2 : ℝ) : ℂ))
    rw [sideImages_snd_eq_zeroPlus_trev hG ht]
    exact h
  · have h := base_limit_core hG ht true (hD _ hη) hF.2.1 hFeq
      (p := zeroMinus V t) (q := zeroPlus V t) hzeros (by simp [g1SideHalf, hzp])
    show Tendsto _ _ (𝓝 (((sideImages W t).1 : ℝ) : ℂ))
    rw [sideImages_fst_eq_zeroMinus_trev' hW hW0 ht (isSimpleCurveHull_of_good hG ht)
      (fun x hx => real_alive_of_good hG ht.le hx)]
    exact h

end G1ZA1a
end Thm18Asm
end QuantumZipper
