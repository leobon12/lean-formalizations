import QuantumZipper.Proofs.Section5.Prop16AN23
import QuantumZipper.Proofs.GFF.Admissible

/-!
# DOM-a by annulus features (D34), node AN3: the free Lipschitz bound

**AN3** (`freeAnnLip_holds : FreeAnnLipStmt D S`, statement in `Prop16LocCoupleAnnNodes.lean`):
`|⟪v̂_{fold_{z,R}} − v̂_{fold_{z',R}}, u⟫| ≤ L |z − z'| ‖u‖` for `u ⊥ M̂`, `z, z' ∈ K`.

The proof copies the mixed proof `K3.exists_abs_inner_remVec_sub_le` (`MixedM5Lip.lean`): by the mean
value property the pairing does not depend on the radius `t ∈ (0, 2R)`; averaging over `t` with a
smooth radial weight `φ` turns the pairing with a test vector `g` into
`(2π)⁻¹ ∫ f_g(fold y) (ψ(y − z) − ψ(y − z')) dy`, `ψ(y) = φ(|y|)/|y|`, `f_g = anPhi g − const`
(`K3.integral_radial_foldedCircle_eq`), which is `O(|z − z'| ∫_{D_r} |f_g|)`
(`K3.ofReal_abs_integral_foldH_sub_le`). The mixed proof bounds `∫ |f|` by the Poincaré inequality;
here `lintegral_enorm_anPhi_sub_le` bounds `∫_{D_r} |f_g| ≤ 2 B ‖g‖`, since
`∫_A f_g = ⟪v̂_{Leb|_A}, g⟫` for `A ⊆ D_r` and Lebesgue measure on a compact subset of `Hbar` is
admissible with a uniform free-vector bound `B`. Density of the test vectors finishes.

Own adaptation of the mixed argument (the free-side `L¹` bound is our own elementary argument).
-/

noncomputable section

open MeasureTheory Set Metric Filter
open scoped RealInnerProductSpace ENNReal Topology NNReal Real

namespace QuantumZipper

namespace Prop16Asm

open GFFExist K3

/-! ## The test vectors form a subspace -/

theorem anSlab_mono {n m : ℕ} (h : n ≤ m) : anSlab n ⊆ anSlab m := by
  rintro q ⟨⟨h1, h2⟩, -⟩
  have hnm : (n : ℝ) ≤ m := by exact_mod_cast h
  refine ⟨⟨le_trans (inv_anti₀ (by positivity) (by linarith)) h1, by linarith⟩, mem_univ _⟩

theorem mem_anTest_of_mem_span {g : HkE} (hg : g ∈ Submodule.span ℝ anTest) : g ∈ anTest := by
  induction hg using Submodule.span_induction with
  | mem g hg => exact hg
  | zero =>
      refine ⟨0, ?_⟩
      filter_upwards [Lp.coeFn_zero ℝ 2 hkM] with q hq _
      rw [hq]; rfl
  | add f g _ _ hf hg =>
      obtain ⟨n, hn⟩ := hf
      obtain ⟨m, hm⟩ := hg
      refine ⟨max n m, ?_⟩
      filter_upwards [hn, hm, Lp.coeFn_add f g] with q h1 h2 h3 hq
      rw [h3, Pi.add_apply, h1 fun h => hq (anSlab_mono (le_max_left n m) h),
        h2 fun h => hq (anSlab_mono (le_max_right n m) h), add_zero]
  | smul c g _ hg =>
      obtain ⟨n, hn⟩ := hg
      refine ⟨n, ?_⟩
      filter_upwards [hn, Lp.coeFn_smul c g] with q h1 h2 hq
      rw [h2, Pi.smul_apply, h1 hq, smul_zero]

/-! ## Lebesgue pieces and the `L¹` bound of the test potentials -/

theorem isAdmissibleH_volume_restrict_an {Dr A : Set ℂ} (hDc : IsCompact Dr) (hDH : Dr ⊆ Hbar)
    (hA : A ⊆ Dr) : IsAdmissibleH (volume.restrict A) := by
  have hfin : IsFiniteMeasure (volume.restrict A) :=
    isFiniteMeasure_restrict.2 ((measure_mono hA).trans_lt hDc.measure_lt_top).ne
  refine ⟨hfin, ⟨Dr, hDc, hDH, ?_⟩, _, admissible_lintegral_logNeg_lt_top, fun y => ?_⟩
  · rw [Measure.restrict_apply hDc.measurableSet.compl, show Drᶜ ∩ A = ∅ from
      Set.eq_empty_of_forall_notMem fun x hx => hx.1 (hA hx.2), measure_empty]
  · rw [← admissible_lintegral_logNeg_sub y]
    exact setLIntegral_le_lintegral _ _

/-- **`L¹` bound of the test potentials** on a compact subset of `Hbar`. -/
theorem exists_lintegral_enorm_anPhi_sub_le {Dr : Set ℂ} (hDc : IsCompact Dr) (hDH : Dr ⊆ Hbar) :
    ∃ Bv : ℝ, 0 ≤ Bv ∧ ∀ g ∈ anTest,
      ∫⁻ y in Dr, ‖anPhi g y - ∫ x, anPhi g x ∂gffExRef‖ₑ ≤ ENNReal.ofReal (2 * Bv * ‖g‖) := by
  obtain ⟨Rd, hRd⟩ := hDc.isBounded.subset_closedBall 0
  obtain ⟨Bv, hBv⟩ := exists_norm_freeVec_le_an Rd
    (C := ∫⁻ x : ℂ, ENNReal.ofReal (-Real.log ‖x‖)) admissible_lintegral_logNeg_lt_top.ne
    (volume.real Dr)
  have hpiece : ∀ A ⊆ Dr, MeasurableSet A → ∀ g ∈ anTest,
      |∫ y in A, (anPhi g y - ∫ x, anPhi g x ∂gffExRef)| ≤ max Bv 0 * ‖g‖ := by
    intro A hA hAm g hg
    have hadm := isAdmissibleH_volume_restrict_an hDc hDH hA
    have := hadm.1
    have e : ∫ y in A, (anPhi g y - ∫ x, anPhi g x ∂gffExRef) = ⟪freeVec ⟨_, hadm⟩, g⟫ := by
      rw [inner_freeVec_anTest _ hg, integral_sub (integrable_anPhi hg _) (integrable_const _),
        integral_const, smul_eq_mul]
    rw [e]
    refine (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right
      ((hBv _ ?_ ?_ ?_).trans (le_max_left _ _)) (norm_nonneg _))
    · exact (ae_restrict_iff' hAm).2 (ae_of_all _ fun x hx => by
        have := hRd (hA hx); rwa [mem_closedBall, dist_zero_right] at this)
    · intro y
      rw [← admissible_lintegral_logNeg_sub y]
      exact setLIntegral_le_lintegral _ _
    · show (volume.restrict A).real univ ≤ volume.real Dr
      rw [measureReal_restrict_apply_univ]
      exact measureReal_mono hA hDc.measure_lt_top.ne
  refine ⟨max Bv 0, le_max_right _ _, fun g hg => ?_⟩
  set f : ℂ → ℝ := fun y => anPhi g y - ∫ x, anPhi g x ∂gffExRef with hf
  have hfc : Continuous f := (continuous_anPhi hg).sub continuous_const
  have hfi : IntegrableOn f Dr := hfc.continuousOn.integrableOn_compact hDc
  have hT : MeasurableSet {y | 0 ≤ f y} := measurableSet_le measurable_const hfc.measurable
  have h1 : |∫ y in Dr ∩ {y | 0 ≤ f y}, f y| ≤ max Bv 0 * ‖g‖ :=
    hpiece (Dr ∩ {y | 0 ≤ f y}) inter_subset_left (hDc.measurableSet.inter hT) g hg
  have h2 : |∫ y in Dr \ {y | 0 ≤ f y}, f y| ≤ max Bv 0 * ‖g‖ :=
    hpiece (Dr \ {y | 0 ≤ f y}) sdiff_subset (hDc.measurableSet.diff hT) g hg
  have eabs : ∫ y in Dr, ‖f y‖ =
      (∫ y in Dr ∩ {y | 0 ≤ f y}, f y) + -∫ y in Dr \ {y | 0 ≤ f y}, f y := by
    have e1 : ∫ y in Dr ∩ {y | 0 ≤ f y}, ‖f y‖ = ∫ y in Dr ∩ {y | 0 ≤ f y}, f y :=
      setIntegral_congr_fun (hDc.measurableSet.inter hT) fun y hy => by
        rw [Real.norm_eq_abs, abs_of_nonneg hy.2]
    have e2 : ∫ y in Dr \ {y | 0 ≤ f y}, ‖f y‖ = ∫ y in Dr \ {y | 0 ≤ f y}, -f y :=
      setIntegral_congr_fun (hDc.measurableSet.diff hT) fun y hy => by
        rw [Real.norm_eq_abs, abs_of_neg (not_le.1 hy.2)]
    rw [← integral_inter_add_sdiff hT hfi.norm, e1, e2, integral_neg]
  rw [← ofReal_integral_norm_eq_lintegral_enorm hfi, eabs]
  refine ENNReal.ofReal_le_ofReal ?_
  obtain ⟨a1, a2⟩ := abs_le.1 h1
  obtain ⟨b1, b2⟩ := abs_le.1 h2
  calc _ ≤ max Bv 0 * ‖g‖ + max Bv 0 * ‖g‖ := add_le_add a2 (neg_le.1 b1)
    _ = 2 * max Bv 0 * ‖g‖ := by ring

/-- **AN3 (proved).** The free Lipschitz bound `FreeAnnLipStmt D S`. -/
theorem freeAnnLip_holds (D S : Set ℂ) : FreeAnnLipStmt D S := by
  intro K R h
  have hR := h.pos
  have hKH : K ⊆ Hbar := fun z hz => (h.local_ z hz).1
  set a : ℝ := R / 2 with ha_def
  have ha : 0 < a := by positivity
  have hab : a < R := by linarith
  obtain ⟨φ, hφ, hφ0, hφa, hφb, hφ1⟩ := exists_radial_weight ha hab
  obtain ⟨L, hL⟩ := exists_lipschitz_radial hφ ha hφa hφb
  have hψb : ∀ y : ℂ, R ≤ ‖y‖ → φ ‖y‖ / ‖y‖ = 0 := fun y hy => by rw [hφb _ hy, zero_div]
  have hφcs : HasCompactSupport φ := by
    refine HasCompactSupport.intro (isCompact_Icc (a := a) (b := R)) (fun t ht => ?_)
    rw [mem_Icc, not_and_or, not_le, not_le] at ht
    rcases ht with ht | ht
    · exact hφa t ht.le
    · exact hφb t ht.le
  have hφint : IntegrableOn φ (Ioi 0) :=
    (hφ.continuous.integrable_of_hasCompactSupport hφcs).integrableOn
  obtain ⟨Rk, hRk⟩ := h.compact.isBounded.subset_closedBall 0
  have hKR : ∀ w ∈ K, ‖w‖ ≤ Rk := fun w hw => by
    have := hRk hw; rwa [mem_closedBall, dist_zero_right] at this
  set Dr : Set ℂ := closedBall 0 (Rk + R) ∩ Hbar with hDr
  have hDc : IsCompact Dr := (isCompact_closedBall _ _).inter_right isClosed_Hbar
  have hsub : ∀ w ∈ K, ∀ y ∈ H, ‖y - w‖ < R → y ∈ Dr := by
    intro w hw y hy hyw
    refine ⟨?_, show (0 : ℝ) ≤ y.im from le_of_lt hy⟩
    rw [mem_closedBall, dist_zero_right]
    calc ‖y‖ = ‖(y - w) + w‖ := by rw [sub_add_cancel]
      _ ≤ ‖y - w‖ + ‖w‖ := norm_add_le _ _
      _ ≤ Rk + R := by linarith [hKR w hw]
  obtain ⟨Bv, hBv0, hBv⟩ := exists_lintegral_enorm_anPhi_sub_le hDc inter_subset_right
  obtain ⟨Ba, hBa⟩ := exists_norm_freeVec_le_an (Rk + R)
    (C := 2 * ENNReal.ofReal (Real.log 2 + (|Real.log a| + |Real.log R|))) (by finiteness) 1
  have hfoldB : ∀ w ∈ K, ∀ t, a ≤ t → t ≤ R → ‖freeFold w t‖ ≤ Ba := by
    intro w hw t hat htR
    have ht : 0 < t := ha.trans_le hat
    rw [freeFold_eq (hKH hw) ht]
    refine hBa _ ?_ (fun y => (lintegral_negLog_foldedCircle_le w ht y).trans ?_) (by simp)
    · filter_upwards [measure_eq_zero_iff_ae_notMem.mp
        (K3.foldedCircle_compl_eq_zero (hKH hw) ht.le)] with x hx
      have hx' := (not_not.mp hx).1
      rw [mem_closedBall, dist_eq_norm] at hx'
      calc ‖x‖ = ‖(x - w) + w‖ := by rw [sub_add_cancel]
        _ ≤ ‖x - w‖ + ‖w‖ := norm_add_le _ _
        _ ≤ Rk + R := by linarith [hKR w hw]
    · have h1 : Real.log a ≤ Real.log t := Real.log_le_log ha hat
      have h2 : Real.log t ≤ Real.log R := Real.log_le_log ht htR
      have h3 : |Real.log t| ≤ |Real.log a| + |Real.log R| := by
        rw [abs_le]
        constructor
        · linarith [neg_abs_le (Real.log a), abs_nonneg (Real.log R)]
        · linarith [le_abs_self (Real.log R), abs_nonneg (Real.log a)]
      exact mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (by linarith))
  set W : ℝ := 2 * Ba with hWdef
  set K2 : ℝ := (2 * π)⁻¹ * (L * (4 * (2 * Bv))) with hK2
  refine ⟨K2, fun z hz z' hz' u hu => ?_⟩
  have hzH := hKH hz
  have hz'H := hKH hz'
  set c := ⟪freeFold z R - freeFold z' R, u⟫ with hc_def
  have hc : ∀ t, 0 < t → t < 2 * R → ⟪freeFold z t - freeFold z' t, u⟫ = c := by
    intro t ht ht2
    rw [hc_def, inner_sub_left, inner_sub_left,
      freeFold_inner_eq_of_radii (h.local_ z hz) ht hR ht2 (by linarith) hu,
      freeFold_inner_eq_of_radii (h.local_ z' hz') ht hR ht2 (by linarith) hu]
  have hW : ∀ t, a < t → t < R → ‖freeFold z t - freeFold z' t‖ ≤ W := fun t hat htR =>
    (norm_sub_le _ _).trans (by
      linarith [hfoldB z hz t hat.le htR.le, hfoldB z' hz' t hat.le htR.le])
  have hu2 : u ∈ closure (Submodule.span ℝ anTest : Set HkE) := by
    rw [← Submodule.topologicalClosure_coe, anTest_dense]; trivial
  obtain ⟨g, hg, hlim⟩ := mem_closure_iff_seq_limit.mp hu2
  have hgT : ∀ n, g n ∈ anTest := fun n => mem_anTest_of_mem_span (hg n)
  have hn : ∀ n, |c| ≤ K2 * ‖z - z'‖ * ‖g n‖ + W * ‖g n - u‖ := by
    intro n
    set f : ℂ → ℝ := fun y => anPhi (g n) y - ∫ x, anPhi (g n) x ∂gffExRef with hf
    have hfc : Continuous f := (continuous_anPhi (hgT n)).sub continuous_const
    have hpair : ∀ w ∈ K, ∀ t, 0 < t → ∫ x, f x ∂(foldedCircle w t) = ⟪freeFold w t, g n⟫ := by
      intro w hw t ht
      rw [inner_freeFold_anTest (hKH hw) ht (hgT n), hf,
        integral_sub (integrable_anPhi (hgT n) _) (integrable_const _), integral_const,
        probReal_univ, one_smul]
    obtain ⟨hIz, hAz⟩ := integral_radial_foldedCircle_eq hφ.continuous ha hφa hφb hfc z
    obtain ⟨hIz', hAz'⟩ := integral_radial_foldedCircle_eq hφ.continuous ha hφa hφb hfc z'
    set Az := ∫ t in Ioi 0, φ t * ∫ x, f x ∂(foldedCircle z t) with hAz_def
    set Az' := ∫ t in Ioi 0, φ t * ∫ x, f x ∂(foldedCircle z' t) with hAz'_def
    have hE := ofReal_abs_integral_foldH_sub_le hfc hL hψb hDc.measurableSet hzH hz'H
      (hsub z hz) (hsub z' hz')
    have hL1 := hBv (g n) (hgT n)
    have hX : |(∫ y, f (foldH y) * (φ ‖y - z‖ / ‖y - z‖)) -
        ∫ y, f (foldH y) * (φ ‖y - z'‖ / ‖y - z'‖)| ≤
          L * ‖z - z'‖ * (4 * (2 * Bv * ‖g n‖)) := by
      have h4 := hE.trans (mul_le_mul' le_rfl (mul_le_mul' le_rfl hL1))
      rw [← ENNReal.ofReal_ofNat 4, ← ENNReal.ofReal_mul (p := (4 : ℝ)) (by norm_num),
        ← ENNReal.ofReal_mul (p := (L : ℝ) * ‖z - z'‖) (by positivity)] at h4
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h4
    have hdiff : |Az - Az'| ≤ K2 * ‖z - z'‖ * ‖g n‖ := by
      rw [hAz, hAz', ← mul_sub, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (2 * π)⁻¹)]
      calc (2 * π)⁻¹ * |(∫ y, f (foldH y) * (φ ‖y - z‖ / ‖y - z‖)) -
              ∫ y, f (foldH y) * (φ ‖y - z'‖ / ‖y - z'‖)|
          ≤ (2 * π)⁻¹ * (L * ‖z - z'‖ * (4 * (2 * Bv * ‖g n‖))) :=
            mul_le_mul_of_nonneg_left hX (by positivity)
        _ = K2 * ‖z - z'‖ * ‖g n‖ := by rw [hK2]; ring
    have hDn : ∀ t ∈ Ioi (0 : ℝ), ‖φ t * (∫ x, f x ∂(foldedCircle z t) -
        ∫ x, f x ∂(foldedCircle z' t)) - φ t * c‖ ≤ φ t * (W * ‖g n - u‖) := by
      intro t ht
      by_cases hta : t ≤ a
      · rw [hφa t hta]; simp
      by_cases htR : R ≤ t
      · rw [hφb t htR]; simp
      push Not at hta htR
      have ht2 : t < 2 * R := by linarith
      rw [hpair z hz t (ha.trans hta), hpair z' hz' t (ha.trans hta), ← inner_sub_left,
        ← hc t (ha.trans hta) ht2, ← mul_sub, ← inner_sub_right, norm_mul,
        Real.norm_of_nonneg (hφ0 t)]
      refine mul_le_mul_of_nonneg_left ((norm_inner_le_norm _ _).trans ?_) (hφ0 t)
      exact mul_le_mul_of_nonneg_right (hW t hta htR) (norm_nonneg _)
    have hrel : |(Az - Az') - c| ≤ W * ‖g n - u‖ := by
      have hI3 : IntegrableOn (fun t => φ t * (∫ x, f x ∂(foldedCircle z t) -
          ∫ x, f x ∂(foldedCircle z' t))) (Ioi 0) :=
        (hIz.sub hIz').congr_fun (fun t _ => by simp only [Pi.sub_apply, mul_sub])
          measurableSet_Ioi
      have e1 : Az - Az' = ∫ t in Ioi 0, φ t * (∫ x, f x ∂(foldedCircle z t) -
          ∫ x, f x ∂(foldedCircle z' t)) := by
        rw [hAz_def, hAz'_def, ← integral_sub hIz hIz']
        congr 1; funext t; ring
      have e2 : ∫ t in Ioi 0, φ t * c = c := by rw [integral_mul_const, hφ1, one_mul]
      have e : (Az - Az') - c = ∫ t in Ioi 0, (φ t * (∫ x, f x ∂(foldedCircle z t) -
          ∫ x, f x ∂(foldedCircle z' t)) - φ t * c) := by
        rw [e1, integral_sub hI3 (hφint.mul_const c), e2]
      rw [e, ← Real.norm_eq_abs]
      calc ‖∫ t in Ioi 0, (φ t * (∫ x, f x ∂(foldedCircle z t) -
            ∫ x, f x ∂(foldedCircle z' t)) - φ t * c)‖
          ≤ ∫ t in Ioi 0, φ t * (W * ‖g n - u‖) :=
            norm_integral_le_of_norm_le (hφint.mul_const _)
              (ae_restrict_of_forall_mem measurableSet_Ioi hDn)
        _ = W * ‖g n - u‖ := by rw [integral_mul_const, hφ1, one_mul]
    calc |c| = |(Az - Az') - ((Az - Az') - c)| := by ring_nf
      _ ≤ |Az - Az'| + |(Az - Az') - c| := abs_sub _ _
      _ ≤ K2 * ‖z - z'‖ * ‖g n‖ + W * ‖g n - u‖ := add_le_add hdiff hrel
  have hT : Tendsto (fun n => K2 * ‖z - z'‖ * ‖g n‖ + W * ‖g n - u‖) atTop
      (𝓝 (K2 * ‖z - z'‖ * ‖u‖ + W * ‖u - u‖)) :=
    (hlim.norm.const_mul _).add ((hlim.sub_const u).norm.const_mul W)
  have := ge_of_tendsto' hT hn
  simpa using this

end Prop16Asm

end QuantumZipper
