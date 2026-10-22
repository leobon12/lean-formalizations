import HigherDimLQGMetric.LogEnergy.QuantCM
import HigherDimLQGMetric.LGF.Invariance
import HigherDimLQGMetric.Core.Defs

set_option autoImplicit false
noncomputable section
open Set
open HigherDimLFPP (Rd)
namespace HigherDimLQGMetric

private theorem abs_log_sub_log_le_div {A B c : ℝ}
    (hA : c ≤ A) (hB : c ≤ B) (hc : 0 < c) :
    |Real.log A - Real.log B| ≤ |A - B| / c := by
  have hAp : 0 < A := lt_of_lt_of_le hc hA
  have hBp : 0 < B := lt_of_lt_of_le hc hB
  have hupper : Real.log A - Real.log B ≤ (A-B)/B := by
    rw [← Real.log_div hAp.ne' hBp.ne']
    have := Real.log_le_sub_one_of_pos (div_pos hAp hBp)
    convert this using 1; field_simp
  have hlower : Real.log B - Real.log A ≤ (B-A)/A := by
    rw [← Real.log_div hBp.ne' hAp.ne']
    have := Real.log_le_sub_one_of_pos (div_pos hBp hAp)
    convert this using 1; field_simp
  rw [abs_le]
  constructor
  · have hden : (B - A)/A ≤ |A-B|/c := by
      have hn : B - A ≤ |A-B| := by rw [abs_sub_comm]; exact le_abs_self _
      exact (div_le_div_of_nonneg_right hn hAp.le).trans
        (div_le_div_of_nonneg_left (abs_nonneg _) hc hA)
    linarith
  · exact hupper.trans ((div_le_div_of_nonneg_right (le_abs_self _) hBp.le).trans
      (div_le_div_of_nonneg_left (abs_nonneg _) hc hB))

theorem abs_log_norm_sub_le {d : ℕ} {a ε : ℝ} (ha : 0 < a) (hε : 0 ≤ ε)
    (x u : Rd d) (hx : a ≤ ‖x‖) (hsep : ε * ‖u‖ ≤ a/2) :
    |Real.log ‖x‖ - Real.log ‖x - ε • u‖| ≤
      (2/a) * (ε * ‖u‖) := by
  have hnear : a/2 ≤ ‖x - ε • u‖ := by
    have ht : ‖x‖ ≤ ‖x - ε • u‖ + ε * ‖u‖ := by
      calc
        ‖x‖ = ‖(x - ε • u) + ε • u‖ := by simp
        _ ≤ ‖x - ε • u‖ + ‖ε • u‖ := norm_add_le _ _
        _ = _ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hε]
    linarith
  have hA : a/2 ≤ ‖x‖ := by linarith
  have hlog := abs_log_sub_log_le_div hA hnear (by positivity)
  have hnorm : |‖x‖ - ‖x - ε • u‖| ≤ ε * ‖u‖ := by
    calc
      _ ≤ ‖x - (x - ε • u)‖ := abs_norm_sub_norm_le _ _
      _ = ε * ‖u‖ := by simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg hε]
  calc
    _ ≤ |‖x‖ - ‖x - ε • u‖| / (a/2) := hlog
    _ ≤ (ε * ‖u‖) / (a/2) := div_le_div_of_nonneg_right hnorm (by positivity)
    _ = (2/a) * (ε * ‖u‖) := by ring

/-- The separated logarithmic kernel is jointly smooth in scale and both
spatial variables. -/
def logDiff {d : ℕ} (p : ℝ × Rd d × Rd d) : ℝ :=
  Real.log ‖p.2.1‖ - Real.log ‖p.2.1 - p.1 • p.2.2‖

theorem logDiff_contDiffAt {d : ℕ} (p : ℝ × Rd d × Rd d)
    (hx : p.2.1 ≠ 0) (hxu : p.2.1 - p.1 • p.2.2 ≠ 0) :
    ContDiffAt ℝ (⊤ : WithTop ℕ∞) logDiff p := by
  unfold logDiff
  have hf₁ : ContDiffAt ℝ (⊤ : WithTop ℕ∞)
      (fun q : ℝ × Rd d × Rd d => q.2.1) p := by fun_prop
  have hf₂ : ContDiffAt ℝ (⊤ : WithTop ℕ∞)
      (fun q : ℝ × Rd d × Rd d => q.2.1 - q.1 • q.2.2) p := by fun_prop
  exact (hf₁.norm ℝ hx |>.log (norm_ne_zero_iff.mpr hx)).sub
    (hf₂.norm ℝ hxu |>.log (norm_ne_zero_iff.mpr hxu))

theorem compact_iteratedFDeriv_lipschitz
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (n : ℕ) (S : Set E) (hS : IsCompact S)
    (hf : ∀ p ∈ S, ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x y : E, segment ℝ x y ⊆ S →
      ‖iteratedFDeriv ℝ n f y - iteratedFDeriv ℝ n f x‖ ≤ C * ‖y - x‖ := by
  have hcont : ContinuousOn (fun p : E => ‖iteratedFDeriv ℝ (n+1) f p‖) S := by
    intro p hp
    exact ((hf p hp).continuousAt_iteratedFDeriv
      (WithTop.coe_le_coe.mpr le_top)).norm.continuousWithinAt
  obtain ⟨M, hM⟩ := hS.bddAbove_image hcont
  let C := max 0 M
  have hC : 0 ≤ C := le_max_left _ _
  refine ⟨C, hC, ?_⟩
  intro x y hseg
  have hbound (p : E) (hp : p ∈ S) : ‖iteratedFDeriv ℝ (n+1) f p‖ ≤ C :=
    (hM ⟨p, hp, rfl⟩).trans (le_max_right _ _)
  have hdiff (p : E) (hp : p ∈ segment ℝ x y) :
      DifferentiableAt ℝ (iteratedFDeriv ℝ n f) p :=
    (hf p (hseg hp)).differentiableAt_iteratedFDeriv
      (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top n))
  have hbound' (p : E) (hp : p ∈ segment ℝ x y) :
      ‖fderiv ℝ (iteratedFDeriv ℝ n f) p‖ ≤ C := by
    rw [norm_fderiv_iteratedFDeriv]
    exact hbound p (hseg hp)
  exact (convex_segment x y).norm_image_sub_le_of_norm_fderiv_le
    hdiff hbound' (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)


theorem logDiff_iteratedFDeriv_scale_bound {d : ℕ}
    (S : Set (Rd d × Rd d)) (hS : IsCompact S)
    {ε₀ : ℝ} (hε₀ : 0 ≤ ε₀)
    (hx : ∀ p ∈ S, p.1 ≠ 0)
    (hsep : ∀ p ∈ S, ∀ t ∈ Set.Icc (0 : ℝ) ε₀,
      p.1 - t • p.2 ≠ 0)
    (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ S, ∀ ε ∈ Set.Icc (0 : ℝ) ε₀,
      ‖iteratedFDeriv ℝ n logDiff (ε, p) -
        iteratedFDeriv ℝ n logDiff (0, p)‖ ≤ C * ε := by
  let slab : Set (ℝ × Rd d × Rd d) := Set.Icc 0 ε₀ ×ˢ S
  have hcompact : IsCompact slab := isCompact_Icc.prod hS
  have hsmooth : ∀ p ∈ slab,
      ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) logDiff p := by
    intro p hp
    exact (logDiff_contDiffAt p (hx p.2 hp.2)
      (hsep p.2 hp.2 p.1 hp.1)).of_le le_top
  obtain ⟨C, hC, hbound⟩ := compact_iteratedFDeriv_lipschitz
    logDiff n slab hcompact hsmooth
  refine ⟨C, hC, ?_⟩
  intro p hp ε hε
  have hconv : Convex ℝ (Set.Icc (0 : ℝ) ε₀ ×ˢ ({p} : Set (Rd d × Rd d))) :=
    Convex.prod (convex_Icc (0 : ℝ) ε₀) (convex_singleton p)
  have hseg : segment ℝ (0, p) (ε, p) ⊆ slab := by
    intro z hz
    have hz' := hconv.segment_subset
      (show (0, p) ∈ Set.Icc (0 : ℝ) ε₀ ×ˢ ({p} : Set (Rd d × Rd d)) by
        exact ⟨⟨le_rfl, hε₀⟩, rfl⟩)
      (show (ε, p) ∈ Set.Icc (0 : ℝ) ε₀ ×ˢ ({p} : Set (Rd d × Rd d)) by
        exact ⟨hε, rfl⟩) hz
    exact ⟨hz'.1, hz'.2 ▸ hp⟩
  have hn : ‖(ε, p) - ((0 : ℝ), p)‖ = ε := by
    simp [Prod.norm_def, abs_of_nonneg hε.1, hε.1]
  simpa only [hn] using hbound (0, p) (ε, p) hseg

theorem logDiff_annulus_iteratedFDeriv_scale_bound {d : ℕ}
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x u : Rd d, x ∈ annCl 0 (a/2) (2*b) →
      u ∈ Metric.closedBall 0 (2*b) →
      ∀ ε ∈ Set.Icc (0 : ℝ) (a/(8*b)),
        ‖iteratedFDeriv ℝ n logDiff (ε, x, u) -
          iteratedFDeriv ℝ n logDiff (0, x, u)‖ ≤ C * ε := by
  let ε₀ : ℝ := a / (8*b)
  have hb : 0 < b := ha.trans hab
  have hε₀ : 0 < ε₀ := div_pos ha (by positivity)
  let Kx : Set (Rd d) := annCl 0 (a/2) (2*b)
  let Ku : Set (Rd d) := Metric.closedBall 0 (2*b)
  let S : Set (Rd d × Rd d) := Kx ×ˢ Ku
  have hKx : IsCompact Kx := by
    apply IsCompact.of_isClosed_subset (isCompact_closedBall (0 : Rd d) (2*b))
      (isClosed_annCl 0 (a/2) (2*b))
    intro x hx
    change a/2 ≤ ‖x - 0‖ ∧ ‖x - 0‖ ≤ 2*b at hx
    simpa [Metric.mem_closedBall, dist_eq_norm] using hx.2
  have hS : IsCompact S := hKx.prod (isCompact_closedBall 0 (2*b))
  have hx : ∀ p ∈ S, p.1 ≠ 0 := by
    intro p hp hzero
    have hxp : a/2 ≤ ‖p.1 - 0‖ := hp.1.1
    rw [hzero, sub_self, norm_zero] at hxp
    linarith
  have hsep : ∀ p ∈ S, ∀ t ∈ Set.Icc (0 : ℝ) ε₀,
      p.1 - t • p.2 ≠ 0 := by
    intro p hp t ht hzero
    have hxp : a/2 ≤ ‖p.1‖ := by simpa using hp.1.1
    have hup : ‖p.2‖ ≤ 2*b := by simpa [Ku, Metric.mem_closedBall] using hp.2
    have htu : t * ‖p.2‖ ≤ a/4 := by
      calc
        t * ‖p.2‖ ≤ ε₀ * (2*b) := by
          exact mul_le_mul ht.2 hup (norm_nonneg _) hε₀.le
        _ = a/4 := by dsimp [ε₀]; field_simp; ring
    have heq : p.1 = t • p.2 := sub_eq_zero.mp hzero
    rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1] at hxp
    linarith
  obtain ⟨C, hC, hbound⟩ := logDiff_iteratedFDeriv_scale_bound
    S hS hε₀.le hx hsep n
  refine ⟨C, hC, ?_⟩
  intro x u hxs hus ε hε
  exact hbound (x,u) ⟨hxs,hus⟩ ε (by simpa [ε₀] using hε)

theorem iteratedFDeriv_comp_affine_local
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (f : E → F) (g : G →L[ℝ] E) (a : E) (x : G) (n : ℕ)
    (hf : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f (a + g x)) :
    iteratedFDeriv ℝ n (fun y : G => f (a + g y)) x =
      (iteratedFDeriv ℝ n f (a + g x)).compContinuousLinearMap (fun _ => g) := by
  have hfFinite : ContDiffAt ℝ (n : WithTop ℕ∞) f (a + g x) :=
    hf.of_le (WithTop.coe_le_coe.mpr le_top)
  obtain ⟨U, hUopen, hpU, hfU⟩ :=
    hfFinite.contDiffOn' (m := (n : WithTop ℕ∞)) le_rfl (by simp)
  have hfU' : ContDiffOn ℝ (n : WithTop ℕ∞) f U := by
    simpa using hfU
  let s : Set E := {z | a + z ∈ U}
  have hsopen : IsOpen s := hUopen.preimage (continuous_const.add continuous_id)
  let f' : E → F := fun z => f (a + z)
  have hf' : ContDiffOn ℝ (n : WithTop ℕ∞) f' s := by
    intro z hz
    have hAt : ContDiffAt ℝ (n : WithTop ℕ∞) f (a+z) :=
      (hfU' (a+z) (by simpa [s] using hz)).contDiffAt
        (hUopen.mem_nhds (by simpa [s] using hz))
    have hAdd : ContDiffAt ℝ (n : WithTop ℕ∞)
        (fun z : E => a+z) z := by
      fun_prop
    exact (hAt.comp z hAdd).contDiffWithinAt
  have hx : g x ∈ s := hpU
  have hpreopen : IsOpen (g ⁻¹' s) := hsopen.preimage g.continuous
  have hchain := g.iteratedFDerivWithin_comp_right hf'
    hsopen.uniqueDiffOn hpreopen.uniqueDiffOn hx le_rfl
  rw [(iteratedFDerivWithin_of_isOpen n hpreopen) hx,
      (iteratedFDerivWithin_of_isOpen n hsopen) hx] at hchain
  simpa only [f', iteratedFDeriv_comp_add_left, Function.comp_def] using hchain

private def spatialIncl {d : ℕ} :
    (Rd d × Rd d) →L[ℝ] (ℝ × Rd d × Rd d) :=
  (LinearIsometry.inr ℝ ℝ (Rd d × Rd d)).toContinuousLinearMap

private theorem spatialIncl_apply {d : ℕ} (z : Rd d × Rd d) :
    spatialIncl z = (0,z) := rfl

def logDiffSpatial {d : ℕ} (ε : ℝ) (z : Rd d × Rd d) : ℝ :=
  logDiff (ε,z)

private theorem logDiffSpatial_iteratedFDeriv {d : ℕ} (ε : ℝ)
    (z : Rd d × Rd d) (n : ℕ)
    (hx : z.1 ≠ 0) (hsep : z.1 - ε • z.2 ≠ 0) :
    iteratedFDeriv ℝ n (logDiffSpatial ε) z =
      (iteratedFDeriv ℝ n logDiff (ε,z)).compContinuousLinearMap
        (fun _ => spatialIncl) := by
  have h := iteratedFDeriv_comp_affine_local logDiff spatialIncl
    (ε, (0 : Rd d × Rd d)) z n (by
      simpa [spatialIncl] using
        (logDiff_contDiffAt (ε,z) hx hsep).of_le le_top)
  change iteratedFDeriv ℝ n (fun y => logDiff (ε,y)) z = _
  simpa [spatialIncl] using h

theorem logDiffSpatial_deriv_bound {d : ℕ} {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (n : ℕ) :
    ∃ C ε₀ : ℝ, 0 ≤ C ∧ 0 < ε₀ ∧
      ∀ x u : Rd d, x ∈ annCl 0 (a/2) (2*b) →
      u ∈ Metric.closedBall 0 (2*b) →
      ∀ ε ∈ Set.Icc (0 : ℝ) ε₀,
      ‖iteratedFDeriv ℝ n (logDiffSpatial ε) (x,u) -
        iteratedFDeriv ℝ n (logDiffSpatial 0) (x,u)‖ ≤ C * ε := by
  obtain ⟨C, hC, hbound⟩ :=
    logDiff_annulus_iteratedFDeriv_scale_bound ha hab n
  let ε₀ : ℝ := a/(8*b)
  have hb : 0 < b := ha.trans hab
  have hε₀ : 0 < ε₀ := by dsimp [ε₀]; exact div_pos ha (by positivity)
  refine ⟨C, ε₀, hC, hε₀, ?_⟩
  intro x u hx hu ε hε
  have hx0 : x ≠ 0 := by
    intro h
    have := hx.1
    simp [h] at this
    linarith
  have hnear : x - ε • u ≠ 0 := by
    intro h
    have hxn : a/2 ≤ ‖x‖ := by simpa using hx.1
    have hun : ‖u‖ ≤ 2*b := by simpa [Metric.mem_closedBall] using hu
    have heq : x = ε • u := sub_eq_zero.mp h
    rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg hε.1] at hxn
    have heps : ε * ‖u‖ ≤ a/4 := by
      have hb : 0 < b := ha.trans hab
      calc
        _ ≤ ε₀ * (2*b) := mul_le_mul hε.2 hun (norm_nonneg _) hε₀.le
        _ = a/4 := by dsimp [ε₀]; field_simp; ring
    linarith
  rw [logDiffSpatial_iteratedFDeriv ε (x,u) n hx0 hnear,
      logDiffSpatial_iteratedFDeriv 0 (x,u) n hx0 (by simpa using hx0)]
  have hsub :
      (iteratedFDeriv ℝ n logDiff (ε,x,u)).compContinuousLinearMap
        (fun _ => spatialIncl) -
      (iteratedFDeriv ℝ n logDiff (0,x,u)).compContinuousLinearMap
        (fun _ => spatialIncl) =
      (iteratedFDeriv ℝ n logDiff (ε,x,u) -
       iteratedFDeriv ℝ n logDiff (0,x,u)).compContinuousLinearMap
        (fun _ => spatialIncl) := by
    ext v
    simp [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rw [hsub]
  have hnorm := ContinuousMultilinearMap.norm_compContinuous_linearIsometry_le
    (iteratedFDeriv ℝ n logDiff (ε,x,u) -
      iteratedFDeriv ℝ n logDiff (0,x,u))
    (fun _ => LinearIsometry.inr ℝ ℝ (Rd d × Rd d))
  exact (le_trans (by simpa [spatialIncl] using hnorm)
    (hbound x u hx hu ε (by simpa [ε₀] using hε)))

end HigherDimLQGMetric
