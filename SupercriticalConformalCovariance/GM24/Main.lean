import SupercriticalConformalCovariance.GM24.Law

/-!
# GM Lemma 2.4, display (2.6), for the actual fields

Gwynne–Miller 1905.00384v2, `coord-change-final.tex` l. 519–520 and 547–562, with the scale repaired
(`(·)_{𝐟,|α|}` must be `(·)_{𝐟,|α|⁻¹}`, see `dilDist_smoothAvg_norm`):

  `(h ∘ φ_n⁻¹ − (h ∘ φ_n⁻¹)_{𝐟,|α|⁻¹}(0))|_B → h(α ·)|_B` in total variation,

for `h` a whole-plane GFF normalized by `h_{𝐟,1}(0) = (h, 𝐟) = 0` and any bounded open `B` containing the
support of `f_{|α|⁻¹}`. The conditional helper `tendsto_tvDist_gm24` has explicit premises for
decomposition data `(X, Y, C)`, the Cameron–Martin mixture bound `hCM`, energy decay `hE`, and IG4
Proposition 2.10(i) `hIG4`. For this conditional route, `exists_decomp_seq` supplies the
decomposition data from the Markov property on a disk `D_n ⊆ U_n`, transported by `φ_n⁻¹`
(`ZBConformal.exists_pullback_markov_normAt_joint`), while `nrm_restrict_eq_of_decomp` gives its
normalization identity.

The root closure uses `tendsto_tvDist_gm24_open` through `tendsto_tvDist_gm24_closed` instead.
There `TV.exists_markov_zb_measurable_version` and
`ZBConformal.isZeroBoundaryGFF_distPullback` supply the transported Markov field in place of
`(X, Y, C)`; `exists_tv_envelope_general`, using `TV.tvDist_zb_indep_shift_le` and
`TV.exists_lintegral_cutoff_energy_le`, together with `TV.diskVarianceEnvelope_tendsto_zero`,
supplies the mixture and energy-decay step in place of `hCM` and `hE`; and
`TV.ig4_prop210_zeroBoundary_bounded` supplies the `hIG4` comparison on the countable-law carrier.
Normalization algebra, cutoff, data processing, and the limit law complete the proof.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set TopologicalSpace
open scoped ENNReal

namespace SupercriticalConformalCovariance.GM24

open LQGMetric QuantumZipper
open SmallGammaGeodesics.CC (intDist intDist_apply testOnOfSupp)

/-- The normalizing test function `f_r = r⁻² 𝐟(r⁻¹ ·)` with `r = |α|⁻¹`, on `B`. -/
def frOn {α : ℂ} (hα : α ≠ 0) (f : TestC) {B : Opens ℂ}
    (hFB : tsupport (smoothTest (inv_pos.2 (norm_pos_iff.2 hα)) f : ℂ → ℝ) ⊆ B) : TestOn B :=
  testOnOfSupp B _ hFB

theorem integral_frOn {α : ℂ} (hα : α ≠ 0) {f : TestC} (hf1 : ∫ x, f x = 1) {B : Opens ℂ}
    (hFB : tsupport (smoothTest (inv_pos.2 (norm_pos_iff.2 hα)) f : ℂ → ℝ) ⊆ B) :
    ∫ x, frOn hα f hFB x = 1 := by
  change ∫ x, smoothTest (inv_pos.2 (norm_pos_iff.2 hα)) f x = 1
  rw [integral_smoothTest, hf1]

/-- The normalized field is GM's `(h ∘ φ⁻¹ − (h ∘ φ⁻¹)_{𝐟,r}(0))|_B`. -/
theorem nrm_invPullDist_apply {W : Set ℂ} {φ : ℂ → ℂ} (hW : IsOpen W)
    (hd : DifferentiableOn ℂ φ W) (hi : InjOn φ W) {B : Opens ℂ} (hB : (B : Set ℂ) ⊆ φ '' W)
    {α : ℂ} (hα : α ≠ 0) (f : TestC)
    (hFB : tsupport (smoothTest (inv_pos.2 (norm_pos_iff.2 hα)) f : ℂ → ℝ) ⊆ B) (u : DistC)
    (g : TestOn B) :
    nrm (frOn hα f hFB) (invPullDist hW hd hi B hB u) g =
      invPullDist hW hd hi B hB u g -
        invPullSmoothAvg W φ u f (inv_pos.2 (norm_pos_iff.2 hα)) * ∫ x, g x := by
  have e : TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := B) (Ω₂ := ⊤) (frOn hα f hFB) =
      smoothTest (inv_pos.2 (norm_pos_iff.2 hα)) f := by
    ext x
    rw [TestFunction.monoCLM_apply, ite_cond_eq_true _ _ (eq_true ⟨le_rfl, le_top⟩)]
    rfl
  rw [nrm_apply, invPullDist_apply hW hd hi B hB u (frOn hα f hFB), invPullSmoothAvg, e]

variable {U : ℕ → Set ℂ} {φ : ℕ → ℂ → ℂ} {α : ℂ}

open scoped Classical in
/-- **GM Lemma 2.4, display (2.6)** (repaired scale `|α|⁻¹`), from the explicit inputs. -/
theorem tendsto_tvDist_gm24
    (hopen : ∀ n, IsOpen (U n)) (hzeroU : ∀ n, (0 : ℂ) ∈ U n)
    (hexhaust : ∀ K : Set ℂ, IsCompact K → ∀ᶠ n in atTop, K ⊆ U n)
    (hd : ∀ n, DifferentiableOn ℂ (φ n) (U n)) (hinj : ∀ n, InjOn (φ n) (U n))
    (hzero : ∀ n, φ n 0 = 0) (hα : α ≠ 0)
    (hder : Tendsto (fun n => deriv (φ n) 0) atTop (𝓝 α⁻¹))
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC}
    (hh : IsWholePlaneGFF h P) {f : TestC} (hf1 : ∫ x, f x = 1)
    (hrot : ∀ u : ℂ, ‖u‖ = 1 → ∀ z : ℂ, f (u * z) = f z) (hnorm : ∀ᵐ ω ∂P, h ω f = 0)
    {B : Opens ℂ} (hBb : Bornology.IsBounded (B : Set ℂ))
    (hFB : tsupport (smoothTest (inv_pos.2 (norm_pos_iff.2 hα)) f : ℂ → ℝ) ⊆ B)
    -- decomposition data on `B` (transported Markov decomposition)
    {X : ℕ → Ω → DistOn B} {Y S : ℕ → Ω → ℂ → ℝ} {C E : ℕ → Ω → ℝ}
    (hX : ∀ n, Measurable (X n)) (hXS : ∀ n, Measurable fun ω => X n ω + smoothDist B (S n ω))
    (hdec : ∀ᶠ n in atTop, ∀ᵐ ω ∂P, ∀ hn : (B : Set ℂ) ⊆ φ n '' U n, ∀ g : TestOn B,
      invPullDist (hopen n) (hd n) (hinj n) B hn (h ω) g =
        X n ω g + (∫ x, g x * Y n ω x) + C n ω * ∫ x, g x)
    (hY : ∀ᶠ n in atTop, ∀ᵐ ω ∂P, ContinuousOn (Y n ω) B)
    (hcut : ∀ᶠ n in atTop, ∀ᵐ ω ∂P,
      EqOn (S n ω) (fun x => Y n ω x - smoothDist B (Y n ω) (frOn hα f hFB)) B)
    -- Cameron–Martin mixture bound
    (hCM : ∀ᶠ n in atTop, TV.tvDist (P.map fun ω => X n ω + smoothDist B (S n ω)) (P.map (X n)) ≤
      ∫⁻ ω, cmBound (E n ω) ∂P)
    -- energy decay (IG4 Prop 2.10's proof, transported)
    (hE : ∀ δ : ℝ, 0 < δ → Tendsto (fun n => P {ω | δ < E n ω}) atTop (𝓝 0))
    -- IG4 Prop 2.10(i), on the normalized fields of `B` (see `tvDist_nrm_le` for the carrier)
    (hIG4 : Tendsto (fun n => TV.tvDist (P.map (nrm (frOn hα f hFB) ∘ X n))
      (P.map (nrm (frOn hα f hFB) ∘ fun ω => restrictTo B (h ω)))) atTop (𝓝 0)) :
    Tendsto (fun n => TV.tvDist
      (P.map fun ω => if hn : (B : Set ℂ) ⊆ φ n '' U n then
        nrm (frOn hα f hFB) (invPullDist (hopen n) (hd n) (hinj n) B hn (h ω)) else 0)
      (P.map fun ω => restrictTo B (dilDist hα (h ω)))) atTop (𝓝 0) := by
  have hfr := integral_frOn hα hf1 hFB
  obtain ⟨ρ, hρ⟩ := hBb.subset_closedBall (0 : ℂ)
  have hsub : ∀ᶠ n in atTop, (B : Set ℂ) ⊆ φ n '' U n := by
    filter_upwards [eventually_closedBall_subset_image hopen hzeroU hexhaust hd hinj hzero hα hder ρ]
      with n hn
    exact hρ.trans hn
  refine tendsto_tvDist_of_inputs (H := fun ω => restrictTo B (h ω)) (Y := Y) (C := C) hfr hX hXS ?_ ?_ hCM hE
    ?_ ?_
  · filter_upwards [hdec, hsub, hY] with n hdn hsn hYn
    filter_upwards [hdn, hYn] with ω hω hYω
    rw [dif_pos hsn]
    congr 1
    ext g
    rw [hω hsn g]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, intDist_apply,
      smul_eq_mul, smoothDist_apply hYω]

  · filter_upwards [hY, hcut] with n hYn hcn
    filter_upwards [hYn, hcn] with ω h1 h2
    exact ⟨h1, h2⟩
  · exact hIG4
  · exact map_nrm_restrict_eq hh hα hf1 hrot hnorm hFB

end SupercriticalConformalCovariance.GM24
