import QuantumZipper.Proofs.Thm18.G1ZA1aTopo
import QuantumZipper.Proofs.Loewner.CaraR8

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1Z-A1a (ii): the component transport `G1zCompTransportStmt` (PROVED)

With `W' = g1zNewDrv W t a`, `M z = f_t⁻¹(a z)`, `N w = f_t(w)/a`:

* `M`, `N` are mutually inverse continuous maps between `ℍ \ η'` and `ℍ \ η` (Loewner flow
  identities of `G1ZA1aDrv`: `η'(s) = f_t(η(t + a² s))/a`, `K_t = η(0,t]`);
* one point `p` of the side component of `η'` is sent into the side component of `η`: `p` near a
  real point `X/a` of the side half-line, with `X` beyond `0∓` and beyond the bound `C` of
  `‖f_t⁻¹(w) − w‖`, so that the Carathéodory extension `F` of `f_t⁻¹` (Pommerenke, *Boundary
  Behaviour of Conformal Maps*, Thm 2.1/2.6, `CaraR.revMapCaratheodory`) is real at `X` with the
  sign of the side;
* connected components are carried to connected components (`bijOn_cc_of_inv`).

Own elementary argument (Sheffield, arXiv:1012.4797, p. 69, takes this for granted).
-/

noncomputable section

open Filter Set Complex Function Metric
open scoped Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G1ZA1a

open QuantumZipper.CA QuantumZipper.CA.Uniformizer

variable {W : ℝ → ℝ}

theorem ofReal_mul_mem_H {a : ℝ} (ha : 0 < a) {z : ℂ} (hz : z ∈ H) : (a : ℂ) * z ∈ H := by
  show 0 < ((a : ℂ) * z).im
  simpa using mul_pos ha (show (0 : ℝ) < z.im from hz)

/-- `M` maps `ℍ \ η'` into `ℍ \ η`. -/
theorem mapsTo_M_slit (hG : G1zDrvGood W) {t a : ℝ} (ht : 0 < t) (ha : 0 < a) :
    MapsTo (fun z => fwdMapInv W t ((a : ℂ) * z)) (slitH (trace (g1zNewDrv W t a)))
      (slitH (trace W)) := by
  have hW := hG.1
  have hW0 := hG.2.1
  have hη := hG.2.2.2.1
  have hK := hG.2.2.2.2
  intro z hz
  have hzH : z ∈ H := hz.1
  have haz := ofReal_mul_mem_H ha hzH
  have hm := RS.fwdMapInv_mem_compl_fwdHull hW hW0 ht.le haz
  refine ⟨hm.1, ?_⟩
  rintro ⟨v, hv, hve⟩
  replace hve : trace W v = fwdMapInv W t ((a : ℂ) * z) := hve
  have hv0 : v ≠ 0 := by
    rintro rfl
    have := hm.1
    rw [← hve, hη.1] at this
    exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from this)
  by_cases hvt : v ≤ t
  · exact hm.2 (by rw [hK t ht.le]; exact ⟨v, ⟨lt_of_le_of_ne (mem_Ici.1 hv) (Ne.symm hv0), hvt⟩, hve⟩)
  · push Not at hvt
    have ha2 : 0 < a ^ 2 := by positivity
    set s := (v - t) / a ^ 2 with hs
    have hs0 : 0 < s := div_pos (by linarith) ha2
    have hts : t + a ^ 2 * s = v := by rw [hs]; field_simp; ring
    apply hz.2
    refine ⟨s, mem_Ici.2 hs0.le, ?_⟩
    rw [(trace_g1zNewDrv hG ht ha hs0).2, hts, hve, RS.fwdMap_fwdMapInv hW hW0 ht.le haz]
    have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
    field_simp

/-- `N` maps `ℍ \ η` into `ℍ \ η'`. -/
theorem mapsTo_N_slit (hG : G1zDrvGood W) {t a : ℝ} (ht : 0 < t) (ha : 0 < a) :
    MapsTo (fun w => fwdMap W t w / a) (slitH (trace W))
      (slitH (trace (g1zNewDrv W t a))) := by
  have hW := hG.1
  have hη := hG.2.2.2.1
  have hK := hG.2.2.2.2
  intro w hw
  have hwK : w ∈ H \ fwdHull W t := by
    refine ⟨hw.1, fun hk => hw.2 ?_⟩
    rw [hK t ht.le] at hk
    obtain ⟨v, hv, rfl⟩ := hk
    exact ⟨v, mem_Ici.2 hv.1.le, rfl⟩
  have hfH := FwdHolo.mapsTo_fwdMap hW ht.le hwK
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  refine ⟨?_, ?_⟩
  · show 0 < (fwdMap W t w / (a : ℂ)).im
    rw [Complex.div_ofReal_im]
    exact div_pos hfH ha
  · rintro ⟨s, hs, hse⟩
    replace hse : trace (g1zNewDrv W t a) s = fwdMap W t w / (a : ℂ) := hse
    rcases eq_or_lt_of_le (mem_Ici.1 hs) with h0 | h0
    · subst h0
      have h1 : fwdMap W t w / (a : ℂ) = 0 := by
        rw [← hse]; exact (isSimpleChord_trace_g1zNewDrv hG ht ha).1
      have h2 : fwdMap W t w = 0 := by
        rcases div_eq_zero_iff.1 h1 with h | h
        · exact h
        · exact absurd h ha'
      have : (0 : ℝ) < (fwdMap W t w).im := hfH
      rw [h2] at this
      exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from this)
    · rw [(trace_g1zNewDrv hG ht ha h0).2] at hse
      have h1 : fwdMap W t (trace W (t + a ^ 2 * s)) = fwdMap W t w :=
        (div_left_inj' ha').1 hse
      have hmem : trace W (t + a ^ 2 * s) ∈ H \ fwdHull W t :=
        chord_mem_diff_fwdHull hη hK ht.le (by have := mul_pos (by positivity : 0 < a ^ 2) h0; linarith)
      have h2 := FwdHolo.injOn_fwdMap hW ht.le hmem hwK h1
      exact hw.2 ⟨t + a ^ 2 * s, mem_Ici.2 (by positivity), h2⟩

/-- The Carathéodory extension of `f_t⁻¹`: continuous on `ℍ̄`, equal to `f_t⁻¹` on `ℍ`, real
exactly off `(0⁻, 0⁺)`, and within `C` of the identity. -/
theorem exists_cara_fwdMapInv (hG : G1zDrvGood W) {t : ℝ} (ht : 0 < t) :
    ∃ (F : ℂ → ℂ) (C zm zp : ℝ), ContinuousOn F Hbar ∧ EqOn F (fwdMapInv W t) H ∧
      (∀ x : ℝ, (F x).im = 0 ↔ (x ≤ zm ∨ zp ≤ x)) ∧ ∀ x : ℝ, ‖F x - x‖ ≤ C := by
  have hW := hG.1
  have hW0 := hG.2.1
  have hη := hG.2.2.2.1
  have hK := hG.2.2.2.2
  have hKs : IsSimpleCurveHull (fwdHull W t) := by
    have h := isSimpleCurveHull_fwdHull_shift hW hW0 hη hK le_rfl ht
    have e : (fun s => W (0 + s) - W 0) = W := by funext s; simp [hW0]
    rwa [e, sub_zero] at h
  have hK' : IsSimpleCurveHull (revHull (ArcDriver.trev W t) t) := by
    rw [ArcDriver.revHull_trev hW hW0 ht]; exact hKs
  obtain ⟨F, hF⟩ := CaraR.revMapCaratheodory (ArcDriver.trev W t)
    (ArcDriver.continuous_trev hW t) (ArcDriver.trev_zero W t) t ht hK'
  have hFeq : EqOn F (fwdMapInv W t) H := fun u hu => by
    rw [hF.1 hu, UnzipInvariance.fwdMapInv_eq_revMap_timeRev W hW hW0 ht.le hu]
    rfl
  obtain ⟨C, hC⟩ := exists_bound_fwdMapInv hG ht
  refine ⟨F, C, _, _, hF.2.1, hFeq, hF.2.2.2.2.2.1, fun x => ?_⟩
  have hx : (x : ℂ) ∈ Hbar := by simp [Hbar]
  have h1 : Tendsto (fun y : ℝ => (x : ℂ) + y * I) (𝓝[>] 0) (𝓝[Hbar] (x : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun y : ℝ => (x : ℂ) + y * I) (𝓝 0) (𝓝 ((x : ℂ) + (0 : ℝ) * I)) :=
        ((continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).tendsto 0)
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with y hy
      show 0 ≤ ((x : ℂ) + y * I).im
      simpa using (le_of_lt (show (0 : ℝ) < y from hy))
  have h2 : Tendsto (fun y : ℝ => ‖F ((x : ℂ) + y * I) - ((x : ℂ) + y * I)‖) (𝓝[>] 0)
      (𝓝 ‖F x - x‖) :=
    (((hF.2.1 _ hx).tendsto.comp h1).sub (h1.mono_right nhdsWithin_le_nhds)).norm
  refine le_of_tendsto h2 ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  have hyH : (x : ℂ) + y * I ∈ H := by
    show 0 < ((x : ℂ) + y * I).im
    simpa using (show (0 : ℝ) < y from hy)
  rw [hFeq hyH]
  exact hC _ hyH

theorem slitH_subset_compl_fwdHull (hG : G1zDrvGood W) {t : ℝ} (ht : 0 < t) :
    slitH (trace W) ⊆ H \ fwdHull W t := by
  intro w hw
  refine ⟨hw.1, fun hk => hw.2 ?_⟩
  rw [hG.2.2.2.2 t ht.le] at hk
  obtain ⟨v, hv, rfl⟩ := hk
  exact ⟨v, mem_Ici.2 hv.1.le, rfl⟩

/-- One point of the new side component is sent into the old side component. -/
theorem exists_pt_side (hG : G1zDrvGood W) {t a : ℝ} (ht : 0 < t) (ha : 0 < a) (left : Bool)
    {F : ℂ → ℂ} (hFc : ContinuousOn F Hbar) (hFeq : EqOn F (fwdMapInv W t) H) {X y : ℝ}
    (hX : X / a ∈ g1SideHalf left) (hy : y ∈ g1SideHalf left) (hFX : F X = y) :
    ∃ p ∈ sideDom (trace (g1zNewDrv W t a)) left,
      fwdMapInv W t ((a : ℂ) * p) ∈ sideDom (trace W) left := by
  have hη := hG.2.2.2.1
  have hη' := (g1zDrvGood_newDrv hG ht ha).2.2.2.1
  obtain ⟨δ₁, hδ₁, h₁⟩ := sideDom_nhd hη left hy
  obtain ⟨δ₃, hδ₃, h₃⟩ := sideDom_nhd hη' left hX
  have hXH : ((X : ℝ) : ℂ) ∈ Hbar := by simp [Hbar]
  obtain ⟨δ₂, hδ₂, h₂⟩ := Metric.continuousWithinAt_iff.1 (hFc _ hXH) δ₁ hδ₁
  set m := min δ₃ (δ₂ / a) with hm
  have hm0 : 0 < m := lt_min hδ₃ (div_pos hδ₂ ha)
  set ε := m / 2 with hε
  have hε0 : 0 < ε := by positivity
  have hε3 : ε < δ₃ := by have := min_le_left δ₃ (δ₂ / a); linarith
  have hε2 : a * ε < δ₂ := by
    have h1 := min_le_right δ₃ (δ₂ / a)
    have h2 : a * m ≤ δ₂ := by
      calc a * m ≤ a * (δ₂ / a) := mul_le_mul_of_nonneg_left h1 ha.le
        _ = δ₂ := by field_simp
    have : a * ε = a * m / 2 := by rw [hε]; ring
    linarith [mul_pos ha hm0]
  set p : ℂ := ((X / a : ℝ) : ℂ) + (ε : ℂ) * I with hp
  have hpH : p ∈ H := by
    show 0 < p.im
    simpa [hp] using hε0
  have hnorm : ∀ r : ℝ, 0 < r → ‖(r : ℂ) * I‖ = r := fun r hr => by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  refine ⟨p, h₃ p hpH ?_, ?_⟩
  · rw [dist_eq_norm, show p - ((X / a : ℝ) : ℂ) = (ε : ℂ) * I by rw [hp]; ring, hnorm ε hε0]
    exact hε3
  · have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
    have hap : (a : ℂ) * p - (X : ℂ) = ((a * ε : ℝ) : ℂ) * I := by
      rw [hp]; push_cast; field_simp; ring
    have hapH := ofReal_mul_mem_H ha hpH
    have hd : dist ((a : ℂ) * p) (X : ℂ) < δ₂ := by
      rw [dist_eq_norm, hap, hnorm _ (mul_pos ha hε0)]; exact hε2
    have h := h₂ (show 0 ≤ ((a : ℂ) * p).im from le_of_lt (show (0:ℝ) < ((a : ℂ) * p).im from hapH)) hd
    rw [← hFeq hapH]
    rw [hFX] at h
    exact h₁ _ (by rw [hFeq hapH]; exact RS.fwdMapInv_mem_H hG.1 hG.2.1 ht.le hapH) h

/-- **Component transport, PROVED.** -/
theorem g1zCompTransportStmt_holds : G1zCompTransportStmt := by
  intro W hG t a ht ha left
  have hW := hG.1
  have hW0 := hG.2.1
  have hη := hG.2.2.2.1
  have hη' := (g1zDrvGood_newDrv hG ht ha).2.2.2.1
  obtain ⟨F, C, zm, zp, hFc, hFeq, hFr, hFC⟩ := exists_cara_fwdMapInv hG ht
  have hreb : ∀ X : ℝ, |(F X).re - X| ≤ C := fun X => by
    have h2 := Complex.abs_re_le_norm (F X - X)
    simp only [Complex.sub_re, Complex.ofReal_re] at h2
    exact h2.trans (hFC X)
  have hreal : ∀ X : ℝ, (F X).im = 0 → F X = ((F X).re : ℂ) := fun X h =>
    Complex.ext (by simp) (by simp [h])
  obtain ⟨p, hp', hp⟩ : ∃ p ∈ sideDom (trace (g1zNewDrv W t a)) left,
      fwdMapInv W t ((a : ℂ) * p) ∈ sideDom (trace W) left := by
    cases left
    · set X := max zp (|C| + 1) with hX
      have hXr : (F X).im = 0 := (hFr X).2 (Or.inr (le_max_left _ _))
      have h1 := abs_le.1 (hreb X)
      have h2 := le_max_right zp (|C| + 1)
      have h3 := le_abs_self C
      refine exists_pt_side hG ht ha false hFc hFeq (X := X) (y := (F X).re) ?_ ?_ (hreal X hXr)
      · show X / a ∈ g1SideHalf false
        simp only [g1SideHalf]
        exact mem_Ioi.2 (div_pos (by linarith [abs_nonneg C]) ha)
      · show (F X).re ∈ g1SideHalf false
        simp only [g1SideHalf]
        exact mem_Ioi.2 (by linarith)
    · set X := min zm (-|C| - 1) with hX
      have hXr : (F X).im = 0 := (hFr X).2 (Or.inl (min_le_left _ _))
      have h1 := abs_le.1 (hreb X)
      have h2 := min_le_right zm (-|C| - 1)
      have h3 := le_abs_self C
      refine exists_pt_side hG ht ha true hFc hFeq (X := X) (y := (F X).re) ?_ ?_ (hreal X hXr)
      · show X / a ∈ g1SideHalf true
        simp only [g1SideHalf]
        exact mem_Iio.2 (div_neg_of_neg_of_pos (by linarith [abs_nonneg C]) ha)
      · show (F X).re ∈ g1SideHalf true
        simp only [g1SideHalf]
        exact mem_Iio.2 (by linarith)
  obtain ⟨q, hq⟩ := sideDom_eq_cc hη left
  obtain ⟨q', hq'⟩ := sideDom_eq_cc hη' left
  rw [hq] at hp ⊢
  rw [hq'] at hp' ⊢
  rw [connectedComponentIn_eq hp, connectedComponentIn_eq hp']
  have hpS : p ∈ slitH (trace (g1zNewDrv W t a)) := connectedComponentIn_subset _ _ hp'
  have hsub := slitH_subset_compl_fwdHull hG ht
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  refine bijOn_cc_of_inv (N := fun w => fwdMap W t w / a) ?_ ?_ (mapsTo_M_slit hG ht ha)
    (mapsTo_N_slit hG ht ha) ?_ ?_ hpS
  · intro z hz
    exact (ContinuousAt.comp (g := fwdMapInv W t) (f := fun z : ℂ => (a : ℂ) * z)
      (RS.continuousAt_fwdMapInv hW hW0 ht.le (ofReal_mul_mem_H ha hz.1))
      (by fun_prop)).continuousWithinAt
  · exact ((FwdHolo.differentiableOn_fwdMap hW ht.le).continuousOn.mono hsub).div_const _
  · intro z hz
    show fwdMap W t (fwdMapInv W t ((a : ℂ) * z)) / a = z
    rw [RS.fwdMap_fwdMapInv hW hW0 ht.le (ofReal_mul_mem_H ha hz.1)]
    field_simp
  · intro w hw
    show fwdMapInv W t ((a : ℂ) * (fwdMap W t w / a)) = w
    rw [mul_div_cancel₀ _ ha']
    exact RS.fwdMapInv_fwdMap hW hW0 ht.le (hsub hw)

/-- **`G1RerootAffineStmt` from the boundary node alone.** -/
theorem g1RerootAffineStmt_of_bdry (hB : G1zRerootBdryStmt) : G1RerootAffineStmt :=
  g1RerootAffineStmt_of g1zCompTransportStmt_holds hB

end G1ZA1a
end Thm18Asm
end QuantumZipper
