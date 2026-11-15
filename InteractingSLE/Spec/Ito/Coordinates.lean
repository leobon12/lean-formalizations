import InteractingSLE.Frozen.Spec.IsIntegratedSLEPath
import InteractingSLE.Spec.Ito.Loewner
import InteractingSLE.Spec.Ito.Observable
import InteractingSLE.Frozen.Spec.couplingMean

/-!
# The Loewner coordinates of an integrated `SLE_κ(ρ)` path; the Itô derivatives (a)

Packet PROVE-T11-ITO (Specification §3.3, L496–L498, graph node `SPEC.thm-1.1#ito-derivatives`). Along a path
satisfying the frozen `IsIntegratedSLEPath` (Definition 2.1, integrated form; the corrected `w_eq` of R28), up
to a time `T < ζ` at which `z` still has a forward solution, with `f_t = f_t(z)`:

* `fwdMap_eq_integral_drift` (**`df_t(z) = (2/f_t − μ_t) dt − √κ dB_t`**, integrated):
  `f_t = z − √κ b_t + ∫₀ᵗ (2/f_s − μ_s) ds`, `μ_s = ∑ ρ/(W_s − V_s)`;
* the spatial derivative and its logarithm (`Loewner.lean`, `deriv_fwdMap_eq_one_add_integral`,
  `hasDerivWithinAt_logDerivFwd`): `df' = −2 f'/f² dt`, `d log f' = −2/f² dt`;
* `coordAt_eq_add_integral`: the coordinates `Λ_t = (f_t + √κ b_t, f_t − V̂^L_t, f_t − V̂^R_t, log f_t')` are
  absolutely continuous with density `densityAt` (`coordDensity` of `Observable.lean`);
* `couplingMean_eq_meanObs`: the frozen mean `𝔥_t(z)` is `meanObs (Λ_t, b_t)`.

The Itô derivative of `log f_t(z)` is the case `Φ = log(Γ − √κ x)` of the localized Itô formula
(`Localize.lean`); the source's display is recorded in the handoff.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology Complex
open QuantumZipper
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Ito

variable {nL nR : ℕ}

/-- A path indexed by `ℝ≥0`, read in real time (`s < 0` gives the value at `0`). -/
def rpath (w : ℝ≥0 → ℝ) (s : ℝ) : ℝ := w s.toNNReal

theorem rpath_coe (w : ℝ≥0 → ℝ) (t : ℝ≥0) : rpath w t = w t := by simp [rpath]

/-- The Loewner coordinates `(f_t + √κ b_t, f_t − V̂^L_t, f_t − V̂^R_t, log f_t')` at `z`. -/
def coordAt (κ : ℝ) (z : ℂ) (w : ℝ≥0 → ℝ) (vL : Fin nL → ℝ≥0 → ℝ) (vR : Fin nR → ℝ≥0 → ℝ)
    (b : ℝ≥0 → ℝ) (t : ℝ≥0) : Coord nL nR :=
  (fwdMap (rpath w) t z + (Real.sqrt κ : ℂ) * (b t : ℂ),
    fun i => fwdMap (rpath w) t z - ((vL i t - w t : ℝ) : ℂ),
    fun i => fwdMap (rpath w) t z - ((vR i t - w t : ℝ) : ℂ),
    logDerivFwd (rpath w) t z)

/-- The time-density of the coordinates at real time `s`. -/
def densityAt (z : ℂ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (w : ℝ≥0 → ℝ) (vL : Fin nL → ℝ≥0 → ℝ)
    (vR : Fin nR → ℝ≥0 → ℝ) (s : ℝ) : Coord nL nR :=
  coordDensity ρL ρR (fun i => vL i s.toNNReal - w s.toNNReal)
    (fun i => vR i s.toNNReal - w s.toNNReal) (fwdMap (rpath w) s z)

theorem coordF_coordAt (κ : ℝ) (z : ℂ) (w : ℝ≥0 → ℝ) (vL : Fin nL → ℝ≥0 → ℝ)
    (vR : Fin nR → ℝ≥0 → ℝ) (b : ℝ≥0 → ℝ) (t : ℝ≥0) :
    coordF κ ((coordAt κ z w vL vR b t, b t) : Coord nL nR × ℝ) = fwdMap (rpath w) t z := by
  simp [coordF, coordAt]

/-! ### Integrals of coordinate-valued functions -/

theorem intervalIntegrable_coord {g : ℝ → Coord nL nR} {a b : ℝ}
    (h1 : IntervalIntegrable (fun s => (g s).1) volume a b)
    (h2 : ∀ i, IntervalIntegrable (fun s => (g s).2.1 i) volume a b)
    (h3 : ∀ i, IntervalIntegrable (fun s => (g s).2.2.1 i) volume a b)
    (h4 : IntervalIntegrable (fun s => (g s).2.2.2) volume a b) :
    IntervalIntegrable g volume a b := by
  rw [intervalIntegrable_iff] at h1 h4 ⊢
  have h2' : IntegrableOn (fun s => (g s).2.1) (uIoc a b) :=
    integrable_pi_iff.2 fun i => intervalIntegrable_iff.1 (h2 i)
  have h3' : IntegrableOn (fun s => (g s).2.2.1) (uIoc a b) :=
    integrable_pi_iff.2 fun i => intervalIntegrable_iff.1 (h3 i)
  exact h1.prodMk (h2'.prodMk (h3'.prodMk h4))

theorem integral_coord_fst {g : ℝ → Coord nL nR} {a b : ℝ} (hg : IntervalIntegrable g volume a b) :
    (∫ s in a..b, g s).1 = ∫ s in a..b, (g s).1 :=
  ((ContinuousLinearMap.fst ℝ ℂ ((Fin nL → ℂ) × (Fin nR → ℂ) × ℂ)).intervalIntegral_comp_comm
    hg).symm

theorem integral_coord_QL {g : ℝ → Coord nL nR} {a b : ℝ} (hg : IntervalIntegrable g volume a b)
    (i : Fin nL) : (∫ s in a..b, g s).2.1 i = ∫ s in a..b, (g s).2.1 i :=
  (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin nL => ℂ) i).comp
    ((ContinuousLinearMap.fst ℝ (Fin nL → ℂ) ((Fin nR → ℂ) × ℂ)).comp
      (ContinuousLinearMap.snd ℝ ℂ ((Fin nL → ℂ) × (Fin nR → ℂ) × ℂ)))).intervalIntegral_comp_comm
    hg).symm

theorem integral_coord_QR {g : ℝ → Coord nL nR} {a b : ℝ} (hg : IntervalIntegrable g volume a b)
    (i : Fin nR) : (∫ s in a..b, g s).2.2.1 i = ∫ s in a..b, (g s).2.2.1 i :=
  (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin nR => ℂ) i).comp
    ((ContinuousLinearMap.fst ℝ (Fin nR → ℂ) ℂ).comp
      ((ContinuousLinearMap.snd ℝ (Fin nL → ℂ) ((Fin nR → ℂ) × ℂ)).comp
        (ContinuousLinearMap.snd ℝ ℂ ((Fin nL → ℂ) × (Fin nR → ℂ) × ℂ))))).intervalIntegral_comp_comm
    hg).symm

theorem integral_coord_L {g : ℝ → Coord nL nR} {a b : ℝ} (hg : IntervalIntegrable g volume a b) :
    (∫ s in a..b, g s).2.2.2 = ∫ s in a..b, (g s).2.2.2 :=
  (((ContinuousLinearMap.snd ℝ (Fin nR → ℂ) ℂ).comp
      ((ContinuousLinearMap.snd ℝ (Fin nL → ℂ) ((Fin nR → ℂ) × ℂ)).comp
        (ContinuousLinearMap.snd ℝ ℂ ((Fin nL → ℂ) × (Fin nR → ℂ) × ℂ)))).intervalIntegral_comp_comm
    hg).symm

/-! ### The compact localization set -/

/-- `Im f, Im Q ≥ δ` and `‖(Λ, x)‖ ≤ R`: a compact subset of `obsRegion` for `δ > 0`. -/
def obsCompact (κ δ R : ℝ) : Set (Coord nL nR × ℝ) :=
  {p | δ ≤ (coordF κ p).im ∧ (∀ i, δ ≤ (p.1.2.1 i).im) ∧ (∀ i, δ ≤ (p.1.2.2.1 i).im) ∧ ‖p‖ ≤ R}

theorem isCompact_obsCompact (κ δ R : ℝ) : IsCompact (obsCompact κ δ R : Set (Coord nL nR × ℝ)) := by
  have hcl : IsClosed (obsCompact κ δ R : Set (Coord nL nR × ℝ)) := by
    have h : (obsCompact κ δ R : Set (Coord nL nR × ℝ)) = {p | δ ≤ (coordF κ p).im} ∩
        (⋂ i, {p : Coord nL nR × ℝ | δ ≤ (p.1.2.1 i).im}) ∩
        (⋂ i, {p : Coord nL nR × ℝ | δ ≤ (p.1.2.2.1 i).im}) ∩ {p | ‖p‖ ≤ R} := by
      ext p; simp [obsCompact, and_assoc]
    rw [h]
    exact (((isClosed_le continuous_const
      (continuous_im.comp (contDiff_coordF κ (n := 0)).continuous)).inter
      (isClosed_iInter fun i => isClosed_le continuous_const
        (continuous_im.comp (contDiff_QL (n := 0) i).continuous))).inter
      (isClosed_iInter fun i => isClosed_le continuous_const
        (continuous_im.comp (contDiff_QR (n := 0) i).continuous))).inter
      (isClosed_le continuous_norm continuous_const)
  exact (isCompact_closedBall 0 R).of_isClosed_subset hcl fun p hp => by
    rw [mem_closedBall_zero_iff]; exact hp.2.2.2

theorem obsCompact_subset {κ δ R : ℝ} (hδ : 0 < δ) :
    (obsCompact κ δ R : Set (Coord nL nR × ℝ)) ⊆ obsRegion κ := fun _ hp =>
  ⟨hδ.trans_le hp.1, fun i => hδ.trans_le (hp.2.1 i), fun i => hδ.trans_le (hp.2.2.1 i)⟩

theorem norm_pi_le_sum {n : ℕ} (f : Fin n → ℂ) : ‖f‖ ≤ ∑ i, ‖f i‖ :=
  (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)).2 fun i =>
    Finset.single_le_sum (f := fun j => ‖f j‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ i)

theorem norm_coord_le (p : Coord nL nR) : ‖p‖ ≤ ‖p.1‖ + ‖p.2.1‖ + ‖p.2.2.1‖ + ‖p.2.2.2‖ := by
  have h1 := norm_nonneg p.1
  have h2 := norm_nonneg p.2.1
  have h3 := norm_nonneg p.2.2.1
  have h4 := norm_nonneg p.2.2.2
  rw [norm_prod_le_iff, norm_prod_le_iff, norm_prod_le_iff]
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

section Path

variable {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}
  {z : ℂ} {T : ℝ≥0}

theorem continuousOn_rpath {u : ℝ≥0 → ℝ} (hu : ContinuousOn u {t | (t : ℝ≥0∞) < ζ})
    (hT : (T : ℝ≥0∞) < ζ) : ContinuousOn (rpath u) (Icc 0 (T : ℝ)) := by
  refine hu.comp continuous_real_toNNReal.continuousOn fun s hs => ?_
  have : s.toNNReal ≤ T := Real.toNNReal_le_iff_le_coe.2 hs.2
  exact lt_of_le_of_lt (by exact_mod_cast this) hT

/-- The drift `μ_s = ∑ ρL i/(W_s − V^L_s) + ∑ ρR i/(W_s − V^R_s)` of the driver at real time `s`. -/
def driftAt (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (w : ℝ≥0 → ℝ) (vL : Fin nL → ℝ≥0 → ℝ)
    (vR : Fin nR → ℝ≥0 → ℝ) (s : ℝ) : ℝ :=
  (∑ i, ρL i / (w s.toNNReal - vL i s.toNNReal)) + ∑ i, ρR i / (w s.toNNReal - vR i s.toNNReal)

theorem intervalIntegrable_driftAt (hP : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) :
    IntervalIntegrable (driftAt ρL ρR w vL vR) volume 0 t := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hgL, hgR, -⟩ := hP
  have hL : ∀ i ∈ (Finset.univ : Finset (Fin nL)), IntervalIntegrable
      (fun s : ℝ => ρL i / (w s.toNNReal - vL i s.toNNReal)) volume 0 t := fun i _ => by
    simpa only [div_eq_mul_inv] using (hgL t ht i).const_mul (ρL i)
  have hR : ∀ i ∈ (Finset.univ : Finset (Fin nR)), IntervalIntegrable
      (fun s : ℝ => ρR i / (w s.toNNReal - vR i s.toNNReal)) volume 0 t := fun i _ => by
    simpa only [div_eq_mul_inv] using (hgR t ht i).const_mul (ρR i)
  have h1 := IntervalIntegrable.sum Finset.univ hL
  have h2 := IntervalIntegrable.sum Finset.univ hR
  rw [Finset.sum_fn] at h1 h2
  exact h1.add h2

/-- The driving equation of Definition 2.1 with one drift integral: `W_t = √κ b_t + ∫₀ᵗ μ_s ds`. -/
theorem w_eq_sqrt_mul_add_integral (hP : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) :
    w t = Real.sqrt κ * b t + ∫ s in (0 : ℝ)..t, driftAt ρL ρR w vL vR s := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hgL, hgR, hweq, -⟩ := hP
  have hL : ∀ i ∈ (Finset.univ : Finset (Fin nL)), IntervalIntegrable
      (fun s : ℝ => ρL i / (w s.toNNReal - vL i s.toNNReal)) volume 0 t := fun i _ => by
    simpa only [div_eq_mul_inv] using (hgL t ht i).const_mul (ρL i)
  have hR : ∀ i ∈ (Finset.univ : Finset (Fin nR)), IntervalIntegrable
      (fun s : ℝ => ρR i / (w s.toNNReal - vR i s.toNNReal)) volume 0 t := fun i _ => by
    simpa only [div_eq_mul_inv] using (hgR t ht i).const_mul (ρR i)
  have h1 := IntervalIntegrable.sum Finset.univ hL
  have h2 := IntervalIntegrable.sum Finset.univ hR
  rw [Finset.sum_fn] at h1 h2
  unfold driftAt
  rw [hweq t ht, intervalIntegral.integral_add h1 h2, intervalIntegral.integral_finsetSum hL,
    intervalIntegral.integral_finsetSum hR]
  ring

/-- `Im f_s(z) > 0`, continuity and non-vanishing of `f_s(z)` on `[0, T]` along the path. -/
theorem fwdMap_facts (hP : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ) (hT : (T : ℝ≥0∞) < ζ)
    (hz : 0 < z.im) (hsol : ∃ u, IsForwardSol (rpath w) z T u) :
    ContinuousOn (rpath w) (Icc 0 (T : ℝ)) ∧
      (∀ s ∈ Icc (0 : ℝ) T, 0 < (fwdMap (rpath w) s z).im) ∧
      ContinuousOn (fun s => fwdMap (rpath w) s z) (Icc 0 (T : ℝ)) ∧
      AntitoneOn (fun s => (fwdMap (rpath w) s z).im) (Icc 0 (T : ℝ)) := by
  have hwc : ContinuousOn (rpath w) (Icc 0 (T : ℝ)) := continuousOn_rpath hP.2.2.2.1 hT
  exact ⟨hwc, fun s hs => im_fwdMap_pos_of_continuousOn T.coe_nonneg hwc hz hsol hs,
    continuousOn_fwdMap_of_continuousOn T.coe_nonneg hwc hz hsol,
    antitoneOn_im_fwdMap_of_continuousOn T.coe_nonneg hwc hz hsol⟩

theorem intervalIntegrable_two_div_fwdMap (hP : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ)
    (hT : (T : ℝ≥0∞) < ζ) (hz : 0 < z.im) (hsol : ∃ u, IsForwardSol (rpath w) z T u) {t : ℝ}
    (ht0 : 0 ≤ t) (htT : t ≤ T) :
    IntervalIntegrable (fun s => 2 / fwdMap (rpath w) s z) volume 0 t := by
  obtain ⟨-, hpos, hc, -⟩ := fwdMap_facts hP hT hz hsol
  refine (ContinuousOn.intervalIntegrable ?_)
  rw [uIcc_of_le ht0]
  refine (continuousOn_const.div hc fun s hs => ?_).mono (Icc_subset_Icc_right htT)
  intro h; have := hpos s hs; rw [h, zero_im] at this; exact lt_irrefl 0 this

/-- **The Itô derivative of `f_t(z)`** (Specification L498, first display):
`f_t(z) = z − √κ b_t + ∫₀ᵗ (2/f_s(z) − μ_s) ds`, i.e. `df_t = (2/f_t − ∑ ρ/(W − V)) dt − √κ dB_t`, for
`t ≤ T < ζ` and `z` with a forward solution on `[0, T]`. -/
theorem fwdMap_eq_integral_drift (hP : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ)
    (hT : (T : ℝ≥0∞) < ζ) (hz : 0 < z.im) (hsol : ∃ u, IsForwardSol (rpath w) z T u) {t : ℝ≥0}
    (htT : t ≤ T) :
    fwdMap (rpath w) t z = z - (Real.sqrt κ : ℂ) * (b t : ℂ) +
      ∫ s in (0 : ℝ)..t, (2 / fwdMap (rpath w) s z - (driftAt ρL ρR w vL vR s : ℂ)) := by
  obtain ⟨hwc, -, -, -⟩ := fwdMap_facts hP hT hz hsol
  have ht : (t : ℝ≥0∞) < ζ := lt_of_le_of_lt (by exact_mod_cast htT) hT
  have h1 := fwdMap_eq_sub_add_integral_of_continuousOn T.coe_nonneg hwc hz hsol
    (s := t) ⟨t.coe_nonneg, by exact_mod_cast htT⟩
  rw [rpath_coe, w_eq_sqrt_mul_add_integral hP ht] at h1
  have hd : IntervalIntegrable (fun s => (driftAt ρL ρR w vL vR s : ℂ)) volume 0 t :=
    ⟨(intervalIntegrable_driftAt hP ht).1.ofReal, (intervalIntegrable_driftAt hP ht).2.ofReal⟩
  have hsub : ∫ s in (0 : ℝ)..t, (2 / fwdMap (rpath w) s z - (driftAt ρL ρR w vL vR s : ℂ)) =
      (∫ s in (0 : ℝ)..t, 2 / fwdMap (rpath w) s z) -
        ((∫ s in (0 : ℝ)..t, driftAt ρL ρR w vL vR s : ℝ) : ℂ) := by
    rw [intervalIntegral.integral_sub
      (intervalIntegrable_two_div_fwdMap hP hT hz hsol t.coe_nonneg (by exact_mod_cast htT)) hd,
      intervalIntegral.integral_ofReal]
  rw [h1, hsub]
  push_cast
  ring

theorem intervalIntegrable_two_div_sub {t : ℝ} {u v : ℝ → ℝ}
    (hgap : IntervalIntegrable (fun s : ℝ => (v s - u s)⁻¹) volume 0 t) :
    IntervalIntegrable (fun s : ℝ => 2 / (u s - v s)) volume 0 t := by
  refine (hgap.const_mul (-2)).congr fun s _ => ?_
  have h : u s - v s = -(v s - u s) := by ring
  rw [div_eq_mul_inv, h, inv_neg]
  ring

/-- **The coordinates are absolutely continuous**: `Λ_t = Λ_0 + ∫₀ᵗ λ_s ds` with `λ = densityAt`, for
`t ≤ T < ζ` and `z` with a forward solution on `[0, T]`. -/
theorem coordAt_eq_add_integral (hP : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ)
    (hT : (T : ℝ≥0∞) < ζ) (hz : 0 < z.im) (hsol : ∃ u, IsForwardSol (rpath w) z T u) {t : ℝ≥0}
    (htT : t ≤ T) :
    coordAt κ z w vL vR b t = coordAt κ z w vL vR b 0 +
      ∫ s in (0 : ℝ)..t, densityAt z ρL ρR w vL vR s := by
  have ht : (t : ℝ≥0∞) < ζ := lt_of_le_of_lt (by exact_mod_cast htT) hT
  have h0T : (0 : ℝ≥0) ≤ T := bot_le
  obtain ⟨hwc, hpos, hfc, -⟩ := fwdMap_facts hP hT hz hsol
  have h2f := intervalIntegrable_two_div_fwdMap hP hT hz hsol t.coe_nonneg (by exact_mod_cast htT)
  have hd : IntervalIntegrable (fun s => (driftAt ρL ρR w vL vR s : ℂ)) volume 0 t :=
    ⟨(intervalIntegrable_driftAt hP ht).1.ofReal, (intervalIntegrable_driftAt hP ht).2.ofReal⟩
  obtain ⟨-, hvL0, hvR0, -, -, -, -, -, -, -, hgL, hgR, -, hvLeq, hvReq, -⟩ := id hP
  have hgLt : ∀ i, IntervalIntegrable (fun s : ℝ => ((2 / (vL i s.toNNReal - w s.toNNReal) : ℝ) : ℂ))
      volume 0 t := fun i =>
    ⟨(intervalIntegrable_two_div_sub (u := fun s : ℝ => vL i s.toNNReal)
        (v := fun s : ℝ => w s.toNNReal) (hgL t ht i)).1.ofReal,
      (intervalIntegrable_two_div_sub (u := fun s : ℝ => vL i s.toNNReal)
        (v := fun s : ℝ => w s.toNNReal) (hgL t ht i)).2.ofReal⟩
  have hgRt : ∀ i, IntervalIntegrable (fun s : ℝ => ((2 / (vR i s.toNNReal - w s.toNNReal) : ℝ) : ℂ))
      volume 0 t := fun i =>
    ⟨(intervalIntegrable_two_div_sub (u := fun s : ℝ => vR i s.toNNReal)
        (v := fun s : ℝ => w s.toNNReal) (hgR t ht i)).1.ofReal,
      (intervalIntegrable_two_div_sub (u := fun s : ℝ => vR i s.toNNReal)
        (v := fun s : ℝ => w s.toNNReal) (hgR t ht i)).2.ofReal⟩
  have hsq : IntervalIntegrable (fun s => -(2 / fwdMap (rpath w) s z ^ 2)) volume 0 t := by
    refine (ContinuousOn.intervalIntegrable ?_)
    rw [uIcc_of_le t.coe_nonneg]
    refine ((continuousOn_const.div (hfc.pow 2) fun s hs => ?_).neg).mono
      (Icc_subset_Icc_right (by exact_mod_cast htT))
    refine pow_ne_zero 2 fun h => ?_
    have h' : fwdMap (rpath w) s z = 0 := h
    have := hpos s hs; rw [h', zero_im] at this; exact lt_irrefl 0 this
  have hμ : ∀ s, ((∑ i, ρL i / -(vL i s.toNNReal - w s.toNNReal) +
      ∑ i, ρR i / -(vR i s.toNNReal - w s.toNNReal) : ℝ) : ℂ) = (driftAt ρL ρR w vL vR s : ℂ) := by
    intro s; simp only [neg_sub, driftAt]
  have hint : IntervalIntegrable (densityAt z ρL ρR w vL vR) volume 0 t := by
    refine intervalIntegrable_coord ?_ (fun i => ?_) (fun i => ?_) ?_
    · simp only [densityAt, coordDensity, hμ]; exact h2f.sub hd
    · simp only [densityAt, coordDensity]; exact h2f.sub (hgLt i)
    · simp only [densityAt, coordDensity]; exact h2f.sub (hgRt i)
    · simp only [densityAt, coordDensity]; exact hsq
  -- the Loewner equation `f_s + W_s = z + ∫ 2/f`
  have hfw : ∀ s : ℝ≥0, s ≤ T → fwdMap (rpath w) s z + (w s : ℂ) =
      z + ∫ r in (0 : ℝ)..s, 2 / fwdMap (rpath w) r z := fun s hs => by
    rw [fwdMap_eq_sub_add_integral_of_continuousOn T.coe_nonneg hwc hz hsol
      ⟨s.coe_nonneg, by exact_mod_cast hs⟩, rpath_coe]
    ring
  have hf0 := hfw 0 h0T
  simp only [NNReal.coe_zero, intervalIntegral.integral_same, add_zero] at hf0
  have hΓ := fwdMap_eq_integral_drift hP hT hz hsol htT
  have hΓ0 := fwdMap_eq_integral_drift hP hT hz hsol h0T
  simp only [NNReal.coe_zero, intervalIntegral.integral_same, add_zero] at hΓ0
  refine Prod.ext ?_ (Prod.ext (funext fun i => ?_) (Prod.ext (funext fun i => ?_) ?_))
  · rw [Prod.fst_add, integral_coord_fst hint]
    simp only [coordAt, densityAt, coordDensity, hμ, NNReal.coe_zero]
    rw [hΓ, hΓ0, intervalIntegral.integral_sub h2f hd]
    ring
  · rw [Prod.snd_add, Prod.fst_add, Pi.add_apply, integral_coord_QL hint]
    simp only [coordAt, densityAt, coordDensity, NNReal.coe_zero]
    rw [intervalIntegral.integral_sub h2f (hgLt i), intervalIntegral.integral_ofReal]
    have e1 := hfw t htT
    have hv := hvLeq t ht i
    have hv0 := hvL0 i
    have e2 : fwdMap (rpath w) t z = z + (∫ r in (0 : ℝ)..t, 2 / fwdMap (rpath w) r z) - (w t : ℂ) := by
      rw [← e1]; ring
    have e3 : fwdMap (rpath w) 0 z = z - (w 0 : ℂ) := eq_sub_iff_add_eq.2 hf0
    rw [e2, e3, hv]
    push_cast
    rw [hv0]
    ring
  · rw [Prod.snd_add, Prod.snd_add, Prod.fst_add, Pi.add_apply, integral_coord_QR hint]
    simp only [coordAt, densityAt, coordDensity, NNReal.coe_zero]
    rw [intervalIntegral.integral_sub h2f (hgRt i), intervalIntegral.integral_ofReal]
    have e1 := hfw t htT
    have hv := hvReq t ht i
    have hv0 := hvR0 i
    have e2 : fwdMap (rpath w) t z = z + (∫ r in (0 : ℝ)..t, 2 / fwdMap (rpath w) r z) - (w t : ℂ) := by
      rw [← e1]; ring
    have e3 : fwdMap (rpath w) 0 z = z - (w 0 : ℂ) := eq_sub_iff_add_eq.2 hf0
    rw [e2, e3, hv]
    push_cast
    rw [hv0]
    ring
  · rw [Prod.snd_add, Prod.snd_add, Prod.snd_add, integral_coord_L hint]
    simp only [coordAt, densityAt, coordDensity, logDerivFwd, NNReal.coe_zero,
      intervalIntegral.integral_same, neg_zero, zero_add]
    rw [intervalIntegral.integral_neg]

theorem mem_obsRegion_coordAt (hP : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ)
    (hT : (T : ℝ≥0∞) < ζ) (hz : 0 < z.im) (hsol : ∃ u, IsForwardSol (rpath w) z T u) {t : ℝ≥0}
    (htT : t ≤ T) : ((coordAt κ z w vL vR b t, b t) : Coord nL nR × ℝ) ∈ obsRegion κ := by
  obtain ⟨-, hpos, -, -⟩ := fwdMap_facts hP hT hz hsol
  have h := hpos t ⟨t.coe_nonneg, by exact_mod_cast htT⟩
  refine ⟨by rw [coordF_coordAt]; exact h, fun i => ?_, fun i => ?_⟩ <;>
    simpa [coordAt] using h

/-- **The frozen mean is the observable along the path**: `𝔥_t(z) = meanObs (Λ_t, b_t)` for any bounded
harmonic extension of the time-`t` boundary data, `t ≤ T < ζ`. -/
theorem couplingMean_eq_meanObs (hP : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ)
    (hT : (T : ℝ≥0∞) < ζ) (hz : 0 < z.im) (hsol : ∃ u, IsForwardSol (rpath w) z T u) {t : ℝ≥0}
    (htT : t ≤ T) {u : ℂ → ℝ}
    (hu : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR (fun i => vL i t - w t)
      (fun i => vR i t - w t)) (forceJumpSet (fun i => vL i t - w t) (fun i => vR i t - w t)) u) :
    couplingMean κ (rpath w) t u z = meanObs κ ρL ρR (coordAt κ z w vL vR b t, b t) := by
  have ht : (t : ℝ≥0∞) < ζ := lt_of_le_of_lt (by exact_mod_cast htT) hT
  obtain ⟨-, hpos, -, -⟩ := fwdMap_facts hP hT hz hsol
  obtain ⟨-, -, -, -, -, -, -, hvLw, hwvR, -⟩ := hP
  rw [couplingMean_eq_meanHarmonic (fun i => sub_nonpos.2 (hvLw t ht i))
    (fun i => sub_nonneg.2 (hwvR t ht i)) hu (hpos t ⟨t.coe_nonneg, by exact_mod_cast htT⟩),
    meanObs_eq_meanHarmonic κ ρL ρR (aL := fun i => vL i t - w t) (aR := fun i => vR i t - w t)
      (fun i => by rw [coordF_coordAt]; rfl) (fun i => by rw [coordF_coordAt]; rfl),
    coordF_coordAt]
  rfl

/-- **The drift of the mean vanishes along the path**, for almost every time (the collision sets are
Lebesgue-null): `itoGen meanObs (Λ_s, b_s) λ_s = 0` for a.e. `s ∈ (0, T]`. -/
theorem ae_itoGen_meanObs_coordAt (hκ : 0 < κ) (hP : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ)
    (hT : (T : ℝ≥0∞) < ζ) (hz : 0 < z.im) (hsol : ∃ u, IsForwardSol (rpath w) z T u) :
    ∀ᵐ s : ℝ, s ∈ Ioc (0 : ℝ) T → itoGen (meanObs κ ρL ρR)
      (coordAt κ z w vL vR b s.toNNReal, b s.toNNReal) (densityAt z ρL ρR w vL vR s) = 0 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hcolL, hcolR, -⟩ := id hP
  have hL : ∀ i, ∀ᵐ s : ℝ, ¬ (0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < ζ ∧
      w s.toNNReal = vL i s.toNNReal) := fun i => measure_eq_zero_iff_ae_notMem.1 (hcolL i)
  have hR : ∀ i, ∀ᵐ s : ℝ, ¬ (0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < ζ ∧
      w s.toNNReal = vR i s.toNNReal) := fun i => measure_eq_zero_iff_ae_notMem.1 (hcolR i)
  filter_upwards [ae_all_iff.2 hL, ae_all_iff.2 hR] with s hsL hsR hs
  have hs0 : 0 ≤ s := hs.1.le
  have hsT : s.toNNReal ≤ T := Real.toNNReal_le_iff_le_coe.2 hs.2
  have hsζ : (s.toNNReal : ℝ≥0∞) < ζ := lt_of_le_of_lt (by exact_mod_cast hsT) hT
  have hmem := mem_obsRegion_coordAt (κ := κ) hP hT hz hsol hsT
  have hdens : densityAt z ρL ρR w vL vR s = coordDensity ρL ρR
      (fun i => vL i s.toNNReal - w s.toNNReal) (fun i => vR i s.toNNReal - w s.toNNReal)
      (coordF κ ((coordAt κ z w vL vR b s.toNNReal, b s.toNNReal) : Coord nL nR × ℝ)) := by
    rw [coordF_coordAt, Real.coe_toNNReal _ hs0]; rfl
  rw [hdens]
  refine itoGen_meanObs_eq_zero hκ ρL ρR hmem (fun i => ?_) (fun i => ?_) (fun i => ?_) (fun i => ?_)
  · rw [coordF_coordAt]; rfl
  · rw [coordF_coordAt]; rfl
  · exact sub_ne_zero.2 fun h => hsL i ⟨hs0, hsζ, h.symm⟩
  · exact sub_ne_zero.2 fun h => hsR i ⟨hs0, hsζ, h.symm⟩

theorem norm_two_div_le {f : ℂ} {δ : ℝ} (hδ : 0 < δ) (hf : δ ≤ f.im) : ‖2 / f‖ ≤ 2 / δ := by
  have hn : δ ≤ ‖f‖ := hf.trans (im_le_norm f)
  rw [norm_div, Complex.norm_two]
  exact div_le_div_of_nonneg_left (by norm_num) hδ hn

theorem norm_two_div_sq_le {f : ℂ} {δ : ℝ} (hδ : 0 < δ) (hf : δ ≤ f.im) :
    ‖2 / f ^ 2‖ ≤ 2 / δ ^ 2 := by
  have hn : δ ≤ ‖f‖ := hf.trans (im_le_norm f)
  rw [norm_div, Complex.norm_two, norm_pow]
  exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (pow_le_pow_left₀ hδ.le hn 2)

/-- `Im f_s(z) ≥ δ` on `[0, T]` once `Im f_T(z) ≥ δ` (monotonicity). -/
theorem le_im_fwdMap (hP : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ) (hT : (T : ℝ≥0∞) < ζ)
    (hz : 0 < z.im) (hsol : ∃ u, IsForwardSol (rpath w) z T u) {δ : ℝ}
    (hδf : δ ≤ (fwdMap (rpath w) T z).im) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) T) :
    δ ≤ (fwdMap (rpath w) s z).im := by
  obtain ⟨-, -, -, hanti⟩ := fwdMap_facts hP hT hz hsol
  exact hδf.trans (hanti hs ⟨T.coe_nonneg, le_rfl⟩ hs.2)

/-- **The coordinates stay in a compact set** up to `T`, given `Im f_T(z) ≥ δ > 0`, `T ≤ N` and
`|W|, |b|, |V| ≤ R` on `[0, T]`. -/
theorem coordAt_mem_obsCompact (hP : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ)
    (hT : (T : ℝ≥0∞) < ζ) (hz : 0 < z.im) (hsol : ∃ u, IsForwardSol (rpath w) z T u)
    {δ R N : ℝ} (hδ : 0 < δ) (hδf : δ ≤ (fwdMap (rpath w) T z).im) (hTN : (T : ℝ) ≤ N)
    (hR : ∀ s : ℝ≥0, s ≤ T → |w s| ≤ R ∧ |b s| ≤ R ∧ (∀ i, |vL i s| ≤ R) ∧ ∀ i, |vR i s| ≤ R)
    {t : ℝ≥0} (htT : t ≤ T) :
    ((coordAt κ z w vL vR b t, b t) : Coord nL nR × ℝ) ∈
      obsCompact κ δ (‖z‖ + (3 + Real.sqrt κ) * R + 2 * N / δ + 2 * N / δ ^ 2) := by
  obtain ⟨hwc, -, -, -⟩ := fwdMap_facts hP hT hz hsol
  have htT' : (t : ℝ) ≤ T := by exact_mod_cast htT
  have hδt := le_im_fwdMap hP hT hz hsol hδf ⟨t.coe_nonneg, htT'⟩
  obtain ⟨hwR, hbR, hvLR, hvRR⟩ := hR t htT
  have hR0 : 0 ≤ R := (abs_nonneg _).trans hwR
  have hN0 : 0 ≤ N := t.coe_nonneg.trans (htT'.trans hTN)
  have hnorm_int : ‖∫ r in (0 : ℝ)..t, 2 / fwdMap (rpath w) r z‖ ≤ 2 * N / δ := by
    refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := 2 / δ) fun r hr => ?_).trans ?_
    · rw [uIoc_of_le t.coe_nonneg] at hr
      exact norm_two_div_le hδ (le_im_fwdMap hP hT hz hsol hδf ⟨hr.1.le, hr.2.trans htT'⟩)
    · rw [sub_zero, abs_of_nonneg t.coe_nonneg]
      have := mul_le_mul_of_nonneg_left (htT'.trans hTN) (by positivity : (0 : ℝ) ≤ 2 / δ)
      calc 2 / δ * (t : ℝ) ≤ 2 / δ * N := this
        _ = 2 * N / δ := by ring
  have hf : ‖fwdMap (rpath w) t z‖ ≤ ‖z‖ + R + 2 * N / δ := by
    rw [fwdMap_eq_sub_add_integral_of_continuousOn T.coe_nonneg hwc hz hsol ⟨t.coe_nonneg, htT'⟩,
      rpath_coe]
    calc ‖z - (w t : ℂ) + ∫ r in (0 : ℝ)..t, 2 / fwdMap (rpath w) r z‖
        ≤ ‖z‖ + ‖(w t : ℂ)‖ + ‖∫ r in (0 : ℝ)..t, 2 / fwdMap (rpath w) r z‖ :=
          (norm_add_le _ _).trans (add_le_add_left (norm_sub_le _ _) _)
      _ ≤ _ := by rw [Complex.norm_real, Real.norm_eq_abs]; linarith
  have hL : ‖logDerivFwd (rpath w) t z‖ ≤ 2 * N / δ ^ 2 := by
    rw [logDerivFwd, norm_neg]
    refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := 2 / δ ^ 2)
      fun r hr => ?_).trans ?_
    · rw [uIoc_of_le t.coe_nonneg] at hr
      exact norm_two_div_sq_le hδ (le_im_fwdMap hP hT hz hsol hδf ⟨hr.1.le, hr.2.trans htT'⟩)
    · rw [sub_zero, abs_of_nonneg t.coe_nonneg]
      have := mul_le_mul_of_nonneg_left (htT'.trans hTN) (by positivity : (0 : ℝ) ≤ 2 / δ ^ 2)
      calc 2 / δ ^ 2 * (t : ℝ) ≤ 2 / δ ^ 2 * N := this
        _ = 2 * N / δ ^ 2 := by ring
  have hsq : 0 ≤ Real.sqrt κ := Real.sqrt_nonneg κ
  set R' := ‖z‖ + (3 + Real.sqrt κ) * R + 2 * N / δ + 2 * N / δ ^ 2 with hR'
  have h1 : 0 ≤ 2 * N / δ ^ 2 := by positivity
  have h2 : 0 ≤ 2 * N / δ := by positivity
  refine ⟨by rw [coordF_coordAt]; exact hδt, fun i => by simpa [coordAt] using hδt,
    fun i => by simpa [coordAt] using hδt, ?_⟩
  rw [norm_prod_le_iff]
  refine ⟨?_, ?_⟩
  · simp only [coordAt]
    rw [norm_prod_le_iff, norm_prod_le_iff, norm_prod_le_iff]
    have hR'0 : 0 ≤ R' := by positivity
    refine ⟨?_, (pi_norm_le_iff_of_nonneg hR'0).2 fun i => ?_,
      (pi_norm_le_iff_of_nonneg hR'0).2 fun i => ?_, by
        simp only; linarith [norm_nonneg z, mul_nonneg (by positivity : (0:ℝ) ≤ 3 + Real.sqrt κ) hR0]⟩
    · simp only
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg hsq]
      nlinarith [mul_le_mul_of_nonneg_left hbR hsq, norm_nonneg z]
    · simp only
      refine (norm_sub_le _ _).trans ?_
      rw [Complex.norm_real, Real.norm_eq_abs]
      have := abs_sub (vL i t) (w t)
      nlinarith [hvLR i, mul_nonneg hsq hR0]
    · simp only
      refine (norm_sub_le _ _).trans ?_
      rw [Complex.norm_real, Real.norm_eq_abs]
      have := abs_sub (vR i t) (w t)
      nlinarith [hvRR i, mul_nonneg hsq hR0]
  · simp only
    rw [Real.norm_eq_abs]
    nlinarith [norm_nonneg z, mul_nonneg hsq hR0]

theorem intervalIntegrable_densityAt (hP : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ)
    (hT : (T : ℝ≥0∞) < ζ) (hz : 0 < z.im) (hsol : ∃ u, IsForwardSol (rpath w) z T u) :
    IntervalIntegrable (densityAt z ρL ρR w vL vR) volume 0 T := by
  obtain ⟨-, hpos, hfc, -⟩ := fwdMap_facts hP hT hz hsol
  have h2f := intervalIntegrable_two_div_fwdMap hP hT hz hsol T.coe_nonneg le_rfl
  have hd : IntervalIntegrable (fun s => (driftAt ρL ρR w vL vR s : ℂ)) volume 0 T :=
    ⟨(intervalIntegrable_driftAt hP hT).1.ofReal, (intervalIntegrable_driftAt hP hT).2.ofReal⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hgL, hgR, -⟩ := id hP
  have hgLt : ∀ i, IntervalIntegrable (fun s : ℝ => ((2 / (vL i s.toNNReal - w s.toNNReal) : ℝ) : ℂ))
      volume 0 T := fun i =>
    ⟨(intervalIntegrable_two_div_sub (u := fun s : ℝ => vL i s.toNNReal)
        (v := fun s : ℝ => w s.toNNReal) (hgL T hT i)).1.ofReal,
      (intervalIntegrable_two_div_sub (u := fun s : ℝ => vL i s.toNNReal)
        (v := fun s : ℝ => w s.toNNReal) (hgL T hT i)).2.ofReal⟩
  have hgRt : ∀ i, IntervalIntegrable (fun s : ℝ => ((2 / (vR i s.toNNReal - w s.toNNReal) : ℝ) : ℂ))
      volume 0 T := fun i =>
    ⟨(intervalIntegrable_two_div_sub (u := fun s : ℝ => vR i s.toNNReal)
        (v := fun s : ℝ => w s.toNNReal) (hgR T hT i)).1.ofReal,
      (intervalIntegrable_two_div_sub (u := fun s : ℝ => vR i s.toNNReal)
        (v := fun s : ℝ => w s.toNNReal) (hgR T hT i)).2.ofReal⟩
  have hsq : IntervalIntegrable (fun s => -(2 / fwdMap (rpath w) s z ^ 2)) volume 0 T := by
    refine (ContinuousOn.intervalIntegrable ?_)
    rw [uIcc_of_le T.coe_nonneg]
    refine (continuousOn_const.div (hfc.pow 2) fun s hs => ?_).neg
    refine pow_ne_zero 2 fun h => ?_
    have h' : fwdMap (rpath w) s z = 0 := h
    have := hpos s hs; rw [h', zero_im] at this; exact lt_irrefl 0 this
  have hμ : ∀ s, ((∑ i, ρL i / -(vL i s.toNNReal - w s.toNNReal) +
      ∑ i, ρR i / -(vR i s.toNNReal - w s.toNNReal) : ℝ) : ℂ) = (driftAt ρL ρR w vL vR s : ℂ) := by
    intro s; simp only [neg_sub, driftAt]
  refine intervalIntegrable_coord ?_ (fun i => ?_) (fun i => ?_) ?_
  · simp only [densityAt, coordDensity, hμ]; exact h2f.sub hd
  · simp only [densityAt, coordDensity]; exact h2f.sub (hgLt i)
  · simp only [densityAt, coordDensity]; exact h2f.sub (hgRt i)
  · simp only [densityAt, coordDensity]; exact hsq

/-- `∫₀ᵀ (W − V^{i})⁻¹ = (x_i − V^i_T)/2` for a left force point. -/
theorem integral_inv_gap_eq {t : ℝ≥0} {x : ℝ} {u : ℝ≥0 → ℝ}
    (heq : u t = x + ∫ s in (0 : ℝ)..t, 2 / (u s.toNNReal - w s.toNNReal)) :
    ∫ s in (0 : ℝ)..t, (w s.toNNReal - u s.toNNReal)⁻¹ = (x - u t) / 2 := by
  have h : ∫ s in (0 : ℝ)..t, 2 / (u s.toNNReal - w s.toNNReal) =
      -2 * ∫ s in (0 : ℝ)..t, (w s.toNNReal - u s.toNNReal)⁻¹ := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun s _ => ?_
    have e : u s.toNNReal - w s.toNNReal = -(w s.toNNReal - u s.toNNReal) := by ring
    rw [div_eq_mul_inv, e, inv_neg]
    ring
  rw [h] at heq
  linarith

/-- `∫₀ᵀ (V^{i} − W)⁻¹ = (V^i_T − x_i)/2` for a right force point. -/
theorem integral_inv_gap_eq_right {t : ℝ≥0} {x : ℝ} {u : ℝ≥0 → ℝ}
    (heq : u t = x + ∫ s in (0 : ℝ)..t, 2 / (u s.toNNReal - w s.toNNReal)) :
    ∫ s in (0 : ℝ)..t, (u s.toNNReal - w s.toNNReal)⁻¹ = (u t - x) / 2 := by
  have h : ∫ s in (0 : ℝ)..t, 2 / (u s.toNNReal - w s.toNNReal) =
      2 * ∫ s in (0 : ℝ)..t, (u s.toNNReal - w s.toNNReal)⁻¹ := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [div_eq_mul_inv]
  rw [h] at heq
  linarith

/-- The uniform bound on the total variation of the coordinates up to `T`. -/
def varBound (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    (δ R N : ℝ) : ℝ :=
  N * ((2 + 2 * nL + 2 * nR) / δ + 2 / δ ^ 2) + (∑ i, (|ρL i| + 2) * ((|xL i| + R) / 2))
    + ∑ i, (|ρR i| + 2) * ((|xR i| + R) / 2)

/-- **The coordinates have bounded variation up to `T`**: `∫₀ᵀ ‖λ_s‖ ds ≤ varBound`, given
`Im f_T(z) ≥ δ > 0`, `T ≤ N`, `|V| ≤ R` on `[0, T]`. -/
theorem integral_norm_densityAt_le (hP : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ)
    (hT : (T : ℝ≥0∞) < ζ) (hz : 0 < z.im) (hsol : ∃ u, IsForwardSol (rpath w) z T u)
    {δ R N : ℝ} (hδ : 0 < δ) (hδf : δ ≤ (fwdMap (rpath w) T z).im) (hTN : (T : ℝ) ≤ N)
    (hR : ∀ s : ℝ≥0, s ≤ T → (∀ i, |vL i s| ≤ R) ∧ ∀ i, |vR i s| ≤ R) :
    ∫ s in (0 : ℝ)..T, ‖densityAt z ρL ρR w vL vR s‖ ≤ varBound xL xR ρL ρR δ R N := by
  have hint := intervalIntegrable_densityAt (κ := κ) hP hT hz hsol
  obtain ⟨-, hvL0, hvR0, -, -, -, -, hvLw, hwvR, -, hgL, hgR, -, hvLeq, hvReq, -⟩ := id hP
  set gL : Fin nL → ℝ → ℝ := fun i s => (w s.toNNReal - vL i s.toNNReal)⁻¹ with hgLdef
  set gR : Fin nR → ℝ → ℝ := fun i s => (vR i s.toNNReal - w s.toNNReal)⁻¹ with hgRdef
  set c : ℝ := (2 + 2 * nL + 2 * nR) / δ + 2 / δ ^ 2 with hc
  set G : ℝ → ℝ := fun s => c + (∑ i, (|ρL i| + 2) * gL i s) + ∑ i, (|ρR i| + 2) * gR i s with hG
  have hgLi : ∀ i, IntervalIntegrable (gL i) volume 0 T := fun i => hgL T hT i
  have hgRi : ∀ i, IntervalIntegrable (gR i) volume 0 T := fun i =>
    (hgR T hT i).neg.congr fun s _ => by
      simp only [hgRdef, Pi.neg_apply]
      rw [← inv_neg, neg_sub]
  have hsL : IntervalIntegrable (fun s => ∑ i, (|ρL i| + 2) * gL i s) volume 0 T := by
    have := IntervalIntegrable.sum Finset.univ fun i _ => (hgLi i).const_mul (|ρL i| + 2)
    rwa [Finset.sum_fn] at this
  have hsR : IntervalIntegrable (fun s => ∑ i, (|ρR i| + 2) * gR i s) volume 0 T := by
    have := IntervalIntegrable.sum Finset.univ fun i _ => (hgRi i).const_mul (|ρR i| + 2)
    rwa [Finset.sum_fn] at this
  have hGi : IntervalIntegrable G volume 0 T := (intervalIntegrable_const.add hsL).add hsR
  -- the pointwise bound
  have hpt : ∀ s ∈ Icc (0 : ℝ) T, ‖densityAt z ρL ρR w vL vR s‖ ≤ G s := by
    intro s hs
    have hsT : s.toNNReal ≤ T := Real.toNNReal_le_iff_le_coe.2 hs.2
    have hsζ : (s.toNNReal : ℝ≥0∞) < ζ := lt_of_le_of_lt (by exact_mod_cast hsT) hT
    have hδs := le_im_fwdMap hP hT hz hsol hδf hs
    have hgL0 : ∀ i, 0 ≤ gL i s := fun i => inv_nonneg.2 (sub_nonneg.2 (hvLw _ hsζ i))
    have hgR0 : ∀ i, 0 ≤ gR i s := fun i => inv_nonneg.2 (sub_nonneg.2 (hwvR _ hsζ i))
    have h2f := norm_two_div_le hδ hδs
    have hρL : ∀ i, |ρL i / -(vL i s.toNNReal - w s.toNNReal)| = |ρL i| * gL i s := fun i => by
      rw [neg_sub, abs_div, abs_of_nonneg (sub_nonneg.2 (hvLw _ hsζ i)), div_eq_mul_inv]
    have hρR : ∀ i, |ρR i / -(vR i s.toNNReal - w s.toNNReal)| = |ρR i| * gR i s := fun i => by
      rw [abs_div, abs_neg, abs_of_nonneg (sub_nonneg.2 (hwvR _ hsζ i)), div_eq_mul_inv]
    have h2L : ∀ i, |2 / (vL i s.toNNReal - w s.toNNReal)| = 2 * gL i s := fun i => by
      have e : vL i s.toNNReal - w s.toNNReal = -(w s.toNNReal - vL i s.toNNReal) := by ring
      rw [e, div_neg, abs_neg, abs_div, abs_two, div_eq_mul_inv,
        abs_of_nonneg (sub_nonneg.2 (hvLw _ hsζ i))]
    have h2R : ∀ i, |2 / (vR i s.toNNReal - w s.toNNReal)| = 2 * gR i s := fun i => by
      rw [abs_div, abs_two, abs_of_nonneg (sub_nonneg.2 (hwvR _ hsζ i)), div_eq_mul_inv]
    refine (norm_coord_le _).trans ?_
    simp only [densityAt, coordDensity]
    have hΓ : ‖2 / fwdMap (rpath w) s z - ((∑ i, ρL i / -(vL i s.toNNReal - w s.toNNReal) +
        ∑ i, ρR i / -(vR i s.toNNReal - w s.toNNReal) : ℝ) : ℂ)‖ ≤
        2 / δ + (∑ i, |ρL i| * gL i s) + ∑ i, |ρR i| * gR i s := by
      refine (norm_sub_le _ _).trans ?_
      rw [Complex.norm_real, Real.norm_eq_abs, add_assoc]
      refine add_le_add h2f ((abs_add_le _ _).trans (add_le_add ?_ ?_))
      · exact (Finset.abs_sum_le_sum_abs _ _).trans_eq (Finset.sum_congr rfl fun i _ => hρL i)
      · exact (Finset.abs_sum_le_sum_abs _ _).trans_eq (Finset.sum_congr rfl fun i _ => hρR i)
    have hQL : ‖fun i => 2 / fwdMap (rpath w) s z - ((2 / (vL i s.toNNReal - w s.toNNReal) : ℝ) : ℂ)‖ ≤
        ∑ i, (2 / δ + 2 * gL i s) := by
      refine (norm_pi_le_sum _).trans (Finset.sum_le_sum fun i _ => ?_)
      refine (norm_sub_le _ _).trans (add_le_add h2f ?_)
      rw [Complex.norm_real, Real.norm_eq_abs, h2L i]
    have hQR : ‖fun i => 2 / fwdMap (rpath w) s z - ((2 / (vR i s.toNNReal - w s.toNNReal) : ℝ) : ℂ)‖ ≤
        ∑ i, (2 / δ + 2 * gR i s) := by
      refine (norm_pi_le_sum _).trans (Finset.sum_le_sum fun i _ => ?_)
      refine (norm_sub_le _ _).trans (add_le_add h2f ?_)
      rw [Complex.norm_real, Real.norm_eq_abs, h2R i]
    have hLd : ‖-(2 / fwdMap (rpath w) s z ^ 2)‖ ≤ 2 / δ ^ 2 := by
      rw [norm_neg]; exact norm_two_div_sq_le hδ hδs
    have hsum : (2 / δ + (∑ i, |ρL i| * gL i s) + ∑ i, |ρR i| * gR i s) + (∑ i, (2 / δ + 2 * gL i s))
        + (∑ i, (2 / δ + 2 * gR i s)) + 2 / δ ^ 2 = G s := by
      simp only [hG, hc, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, add_mul, ← Finset.mul_sum]
      ring
    calc _ ≤ (2 / δ + (∑ i, |ρL i| * gL i s) + ∑ i, |ρR i| * gR i s) + (∑ i, (2 / δ + 2 * gL i s))
          + (∑ i, (2 / δ + 2 * gR i s)) + 2 / δ ^ 2 := by gcongr
      _ = G s := hsum
  -- integrate
  refine (intervalIntegral.integral_mono_on T.coe_nonneg hint.norm hGi hpt).trans ?_
  have hIL : ∀ i, ∫ s in (0 : ℝ)..T, gL i s ≤ (|xL i| + R) / 2 := fun i => by
    rw [integral_inv_gap_eq (hvLeq T hT i)]
    have := (hR T le_rfl).1 i
    linarith [le_abs_self (xL i), neg_abs_le (vL i T), abs_le.1 this]
  have hIR : ∀ i, ∫ s in (0 : ℝ)..T, gR i s ≤ (|xR i| + R) / 2 := fun i => by
    rw [integral_inv_gap_eq_right (hvReq T hT i)]
    have := (hR T le_rfl).2 i
    linarith [neg_abs_le (xR i), le_abs_self (vR i T), abs_le.1 this]
  have hGint : ∫ s in (0 : ℝ)..T, G s = c * T + (∑ i, (|ρL i| + 2) * ∫ s in (0 : ℝ)..T, gL i s)
      + ∑ i, (|ρR i| + 2) * ∫ s in (0 : ℝ)..T, gR i s := by
    simp only [hG]
    rw [intervalIntegral.integral_add (intervalIntegrable_const.add hsL) hsR,
      intervalIntegral.integral_add intervalIntegrable_const hsL,
      intervalIntegral.integral_finsetSum fun i _ => (hgLi i).const_mul _,
      intervalIntegral.integral_finsetSum fun i _ => (hgRi i).const_mul _,
      intervalIntegral.integral_const]
    simp only [intervalIntegral.integral_const_mul, smul_eq_mul, sub_zero]
    ring
  rw [hGint, varBound]
  have hc0 : 0 ≤ c := by positivity
  have h1 : c * T ≤ N * ((2 + 2 * nL + 2 * nR) / δ + 2 / δ ^ 2) := by
    rw [hc, mul_comm]; exact mul_le_mul_of_nonneg_right hTN hc0
  have h2 : ∑ i, (|ρL i| + 2) * ∫ s in (0 : ℝ)..T, gL i s ≤ ∑ i, (|ρL i| + 2) * ((|xL i| + R) / 2) :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hIL i) (by positivity)
  have h3 : ∑ i, (|ρR i| + 2) * ∫ s in (0 : ℝ)..T, gR i s ≤ ∑ i, (|ρR i| + 2) * ((|xR i| + R) / 2) :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hIR i) (by positivity)
  linarith

/-- The coordinate path is continuous on `[0, T]` (for `b` continuous). -/
theorem continuousOn_coordAt (hP : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ)
    (hT : (T : ℝ≥0∞) < ζ) (hz : 0 < z.im) (hsol : ∃ u, IsForwardSol (rpath w) z T u)
    (hb : Continuous b) :
    ContinuousOn (fun t : ℝ≥0 => coordAt κ z w vL vR b t) (Iic T) := by
  obtain ⟨hwc, -, hfc, -⟩ := fwdMap_facts hP hT hz hsol
  obtain ⟨-, -, -, hwc', hvLc, hvRc, -⟩ := id hP
  have hLc := continuousOn_logDerivFwd_of_continuousOn T.coe_nonneg hwc hz hsol
  have hmaps : MapsTo (fun t : ℝ≥0 => (t : ℝ)) (Iic T) (Icc 0 (T : ℝ)) := fun t ht =>
    ⟨t.coe_nonneg, by exact_mod_cast ht⟩
  have hsub : Iic T ⊆ {t : ℝ≥0 | (t : ℝ≥0∞) < ζ} := fun t ht =>
    lt_of_le_of_lt (by exact_mod_cast ht) hT
  have hf : ContinuousOn (fun t : ℝ≥0 => fwdMap (rpath w) t z) (Iic T) :=
    hfc.comp NNReal.continuous_coe.continuousOn hmaps
  have hL : ContinuousOn (fun t : ℝ≥0 => logDerivFwd (rpath w) t z) (Iic T) :=
    hLc.comp NNReal.continuous_coe.continuousOn hmaps
  have hof := Complex.continuous_ofReal
  have hQL : ContinuousOn (fun t : ℝ≥0 => fun i => fwdMap (rpath w) t z - ((vL i t - w t : ℝ) : ℂ))
      (Iic T) := continuousOn_pi.2 fun i => hf.sub (hof.comp_continuousOn
        (((hvLc i).mono hsub).sub (hwc'.mono hsub)))
  have hQR : ContinuousOn (fun t : ℝ≥0 => fun i => fwdMap (rpath w) t z - ((vR i t - w t : ℝ) : ℂ))
      (Iic T) := continuousOn_pi.2 fun i => hf.sub (hof.comp_continuousOn
        (((hvRc i).mono hsub).sub (hwc'.mono hsub)))
  exact (hf.add (continuousOn_const.mul (hof.comp hb).continuousOn)).prodMk
    (hQL.prodMk (hQR.prodMk hL))

end Path

end Ito

end InteractingSLE
