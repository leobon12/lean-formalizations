import QuantumZipper.Proofs.Thm18.ASepInvLip

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ASEP3 (step 2): pulled-back points near a good trajectory have good trajectories

* `traj_fwdMapInv_of_near`: if the forward trajectory of `z₀` stays at distance `≥ m` from the
  singularity on `[0,T]` and `ζ ∈ ℍ` is within `(m/2) e^{-8T/m²}` of `f_t(z₀)`, then
  `w = f_t⁻¹(ζ)` has a forward solution on `[0,t]` whose trajectory stays at distance `≥ m/4`
  (the continuation step inside `ASep.norm_fwdMapInv_sub_le`, recorded as a statement);
* `norm_sub_le_fwdMapInv_sub`: hence `f_t⁻¹` is co-Lipschitz on the set of such `ζ`
  (forward Lipschitz bound `ASep.norm_fwdMap_sub_le` applied to the pulled-back points).

These are the co-Lipschitz inputs of the Frostman bound for the small-radius part of the
A-sep family, needed by the scale-parameter run of the engine (`genFam_dil`, ASep3Dil.lean).

Own elementary argument (standard Loewner ODE regularity, Lawler, *Conformally invariant
processes in the plane*, §4.1; same Grönwall continuation as ASepInvLip.lean).
-/

noncomputable section

open MeasureTheory Set Filter Metric
open scoped Topology

namespace QuantumZipper
namespace ASep

/-- **The pulled-back point has a good trajectory.** -/
theorem traj_fwdMapInv_of_near {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {T m : ℝ}
    (hm : 0 < m) {z₀ : ℂ} (hsol : ∃ u, IsForwardSol W z₀ T u)
    (hlow : ∀ s ∈ Set.Icc (0 : ℝ) T, m ≤ ‖fwdMap W s z₀‖) {t : ℝ} (ht : t ∈ Set.Icc 0 T)
    {ζ : ℂ} (hζ : 0 < ζ.im)
    (hclose : ‖ζ - fwdMap W t z₀‖ ≤ m / 2 * Real.exp (-(8 * T / m ^ 2))) :
    (∃ v, IsForwardSol W (fwdMapInv W t ζ) t v) ∧
      ∀ s ∈ Set.Icc (0 : ℝ) t, m / 4 ≤ ‖fwdMap W s (fwdMapInv W t ζ)‖ := by
  obtain ⟨u, huT⟩ := hsol
  have hu : IsForwardSol W z₀ t u := isForwardSol_restrict huT ht.1 ht.2
  have hul : ∀ r ∈ Icc (0 : ℝ) t, m ≤ ‖u r‖ := fun r hr => by
    have hrT : r ∈ Icc (0 : ℝ) T := ⟨hr.1, hr.2.trans ht.2⟩
    rw [← fwdMap_eq_any huT hrT]; exact hlow r hrT
  have htt : t ∈ Icc (0 : ℝ) t := ⟨ht.1, le_rfl⟩
  have hζ₀ : fwdMap W t z₀ = u t := fwdMap_eq_any hu htt
  have hwH := RS.fwdMapInv_mem_compl_fwdHull hW hW0 ht.1 (show ζ ∈ H from hζ)
  set w := fwdMapInv W t ζ with hwdef
  obtain ⟨v, hv⟩ := exists_isForwardSol_of_not_mem_fwdHull ht.1 hwH.1 hwH.2
  have hvt : v t = ζ := by
    rw [← fwdMap_eq_any hv htt, hwdef]
    exact RS.fwdMap_fwdMapInv hW hW0 ht.1 (show ζ ∈ H from hζ)
  rw [hζ₀] at hclose
  have hmaps : MapsTo (fun y : ℝ => t - y) (Icc 0 t) (Icc 0 t) :=
    fun s hs => ⟨by linarith [hs.2], by linarith [hs.1]⟩
  set c : ℝ := 8 * T / m ^ 2 with hc
  have hexpc : ∀ y ∈ Icc (0 : ℝ) t, Real.exp (2 / (m * (m / 4)) * y) ≤ Real.exp c := by
    intro y hy
    apply Real.exp_le_exp.mpr
    rw [hc, show 2 / (m * (m / 4)) * y = 8 * y / m ^ 2 by field_simp; ring]
    gcongr
    exact hy.2.trans ht.2
  have hm4 : 0 < m / 4 := by positivity
  have claim : ∀ x ∈ Icc (0 : ℝ) t, ‖v (t - x) - u (t - x)‖ < 3 * m / 4 := by
    by_contra hcon
    push_neg at hcon
    set F : ℝ → ℝ := fun x => ‖v (t - x) - u (t - x)‖ with hF
    have hFc : ContinuousOn F (Icc 0 t) :=
      continuous_norm.comp_continuousOn
        ((hv.1.sub hu.1).comp (continuousOn_const.sub continuousOn_id) hmaps)
    set S : Set ℝ := Icc (0 : ℝ) t ∩ F ⁻¹' Ici (3 * m / 4) with hS
    have hSc : IsClosed S := hFc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
    obtain ⟨r0, hr0, hr0'⟩ := hcon
    have hSne : S.Nonempty := ⟨r0, hr0, hr0'⟩
    have hSb : BddBelow S := ⟨0, fun x hx => hx.1.1⟩
    have hmem := hSc.csInf_mem hSne hSb
    set x := sInf S with hx
    have hbefore : ∀ y ∈ Ico (0 : ℝ) x, m ≤ ‖u (t - y)‖ ∧ m / 4 ≤ ‖v (t - y)‖ := by
      intro y hy
      have hyt : y ∈ Icc (0 : ℝ) t := ⟨hy.1, (hy.2.le).trans hmem.1.2⟩
      have hyS : y ∉ S := fun h => absurd (csInf_le hSb h) (not_le.mpr hy.2)
      have hlt : F y < 3 * m / 4 := by
        by_contra h'
        exact hyS ⟨hyt, not_lt.mp h'⟩
      have hur := hul (t - y) (hmaps hyt)
      have := norm_sub_norm_le (u (t - y)) (u (t - y) - v (t - y))
      rw [sub_sub_cancel, norm_sub_rev] at this
      exact ⟨hur, by simp only [hF] at hlt; linarith⟩
    have hg := norm_sol_sub_le_gronwall_back hu hv hmem.1 hm hm4 hbefore
    rw [hvt] at hg
    have h1 := hg.trans (mul_le_mul_of_nonneg_left (hexpc x hmem.1) (norm_nonneg _))
    have hsmall : ‖ζ - u t‖ * Real.exp c ≤ m / 2 := by
      calc ‖ζ - u t‖ * Real.exp c ≤ m / 2 * Real.exp (-c) * Real.exp c :=
            mul_le_mul_of_nonneg_right hclose (Real.exp_pos _).le
        _ = m / 2 := by rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
    have hge : 3 * m / 4 ≤ F x := hmem.2
    simp only [hF] at hge
    linarith
  refine ⟨⟨v, hv⟩, fun s hs => ?_⟩
  rw [fwdMap_eq_any hv hs]
  have hy : t - s ∈ Icc (0 : ℝ) t := ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have h1 := claim (t - s) hy
  have h2 := hul s hs
  rw [sub_sub_cancel] at h1
  have := norm_sub_norm_le (u s) (u s - v s)
  rw [sub_sub_cancel, norm_sub_rev] at this
  linarith

/-- **Co-Lipschitz bound for `f_t⁻¹` near good trajectories.** -/
theorem norm_sub_le_fwdMapInv_sub {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {T m : ℝ}
    (hm : 0 < m) {t : ℝ} (ht : t ∈ Set.Icc 0 T) {z₀ z₀' : ℂ}
    (hsol : ∃ u, IsForwardSol W z₀ T u) (hlow : ∀ s ∈ Set.Icc (0 : ℝ) T, m ≤ ‖fwdMap W s z₀‖)
    (hsol' : ∃ u, IsForwardSol W z₀' T u) (hlow' : ∀ s ∈ Set.Icc (0 : ℝ) T, m ≤ ‖fwdMap W s z₀'‖)
    {ζ ζ' : ℂ} (hζ : 0 < ζ.im) (hζ' : 0 < ζ'.im)
    (hclose : ‖ζ - fwdMap W t z₀‖ ≤ m / 2 * Real.exp (-(8 * T / m ^ 2)))
    (hclose' : ‖ζ' - fwdMap W t z₀'‖ ≤ m / 2 * Real.exp (-(8 * T / m ^ 2))) :
    ‖ζ - ζ'‖ ≤ Real.exp (2 * t / (m / 4) ^ 2) * ‖fwdMapInv W t ζ - fwdMapInv W t ζ'‖ := by
  have A := traj_fwdMapInv_of_near hW hW0 hm hsol hlow ht hζ hclose
  have A' := traj_fwdMapInv_of_near hW hW0 hm hsol' hlow' ht hζ' hclose'
  set K : Set ℂ := {fwdMapInv W t ζ, fwdMapInv W t ζ'} with hK
  have hsolK : ∀ z ∈ K, ∃ u, IsForwardSol W z t u := by
    rintro z (rfl | rfl)
    · exact A.1
    · exact A'.1
  have hlowK : ∀ z ∈ K, ∀ s ∈ Set.Icc (0 : ℝ) t, m / 4 ≤ ‖fwdMap W s z‖ := by
    rintro z (rfl | rfl)
    · exact A.2
    · exact A'.2
  have htt : t ∈ Set.Icc (0 : ℝ) t := ⟨ht.1, le_rfl⟩
  have h := norm_fwdMap_sub_le hW hW0 ht.1 (by positivity : (0 : ℝ) < m / 4) hsolK hlowK
    (Or.inl rfl) (Or.inr rfl) htt htt
  rw [RS.fwdMap_fwdMapInv hW hW0 ht.1 (show ζ ∈ H from hζ),
    RS.fwdMap_fwdMapInv hW hW0 ht.1 (show ζ' ∈ H from hζ')] at h
  simpa using h

end ASep
end QuantumZipper
