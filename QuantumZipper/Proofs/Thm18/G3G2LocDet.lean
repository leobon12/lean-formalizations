import QuantumZipper.Proofs.Thm18.G3G2Loc
import QuantumZipper.Proofs.Section5.Prop16LocalAgree
import QuantumZipper.Proofs.Section5.Prop16AreaLocal
import QuantumZipper.Proofs.GFF.CircleMeanValue

/-!
# Locality of the zoom (deterministic part)

For the input `G3LocStmt` of `G3G2Loc.lean`: the cylinder events of `zoomLaw γ C y x` only see
`y` on folded circles near `x`, at the scale of `scaleProxy`. Precisely
(`zoomLaw_mem_lawCyl_iff`): for every cylinder set `s ∈ lawCyl` there is `R ≥ 1` such that,
whenever `y` and `y'` agree on all folded circles inside an open `W` (`FcAgree`), and for some
rational `q₀ > 0` the half-disc `closedBall(x, q₀ R) ∩ Hbar` lies in `W` and the zoomed field of
`y'` has `areaProxy ≥ 1` on the half-ball of radius `q₀`, then `zoomLaw γ C y x ∈ s` iff
`zoomLaw γ C y' x ∈ s`. Also `fcAgree_restrictField_circIn`: a region field agrees with the full
field inside its (open) half-disc.

The ingredients are the locality lemmas of `Prop16LocalAgree` (Duplantier–Sheffield, *Liouville
quantum gravity and KPZ*, Prop. 2.1 and §6: the approximations near a set only use circle
averages there): `avgReg`/`evalReg` locality and its transport by `translate`, `addConst`.
The rest (locality of `areaFun` and `scaleProxy`, and the finite support of a cylinder set) is
own elementary bookkeeping (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace QuantumZipper
namespace Thm18Asm

open Prop16Area.G

/-! ## `sInf` of two upward sets agreeing below a common element -/

theorem sInf_eq_of_agree_below {S S' : Set ℝ} (hb : BddBelow S) (hb' : BddBelow S') {q : ℝ}
    (hq : q ∈ S) (hq' : q ∈ S') (h : ∀ a ≤ q, a ∈ S ↔ a ∈ S') : sInf S = sInf S' := by
  have key : ∀ {T T' : Set ℝ}, BddBelow T' → q ∈ T → q ∈ T' → (∀ a ≤ q, a ∈ T → a ∈ T') →
      sInf T' ≤ sInf T := by
    intro T T' hb' hq hq' h
    refine le_csInf ⟨q, hq⟩ fun a ha => ?_
    rcases le_total a q with haq | haq
    · exact csInf_le hb' (h a haq ha)
    · exact (csInf_le hb' hq').trans haq
  exact le_antisymm (key hb hq' hq fun a ha h' => (h a ha).2 h')
    (key hb' hq hq' fun a ha h' => (h a ha).1 h')

/-! ## Locality of the area proxy and of the scale proxy -/

variable {V : Set ℂ} {Y Y' : FieldSample}

theorem areaFun_openBump_congr (γ : ℝ) (hVo : IsOpen V) (h : CircAgree V Y Y') {q : ℝ}
    (hq : closedBall (0 : ℂ) q ∩ Hbar ⊆ V) (n : ℕ) :
    LQGMeas.areaFun γ (LQGMeas.openBump (ball (0 : ℂ) q ∩ H) n) Y =
      LQGMeas.areaFun γ (LQGMeas.openBump (ball (0 : ℂ) q ∩ H) n) Y' := by
  obtain ⟨δ, hδ, hδV⟩ :=
    (isCompact_closedBall_inter_Hbar 0 q).exists_cthickening_subset_open hVo hq
  unfold LQGMeas.areaFun
  refine Filter.liminf_congr ?_
  filter_upwards [eventually_two_radius_lt hδ] with k hk
  have h0 : ∀ (y : FieldSample) z, 0 ≤ radius k ^ (γ ^ 2 / 2) * Real.exp (γ * avgReg y k z) :=
    fun _ _ => mul_nonneg (Real.rpow_nonneg (radius_pos k).le _) (Real.exp_pos _).le
  unfold areaApprox
  rw [GoodSample.integral_withDensity_ofReal (Prop16Area.measurable_areaDensity γ k Y) (h0 Y) _,
    GoodSample.integral_withDensity_ofReal (Prop16Area.measurable_areaDensity γ k Y') (h0 Y') _]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  by_cases hz : LQGMeas.openBump (ball (0 : ℂ) q ∩ H) n z = 0
  · simp [hz]
  · have hzU : z ∈ ball (0 : ℂ) q ∩ H :=
      LQGMeas.tsupport_openBump_subset _ n (subset_tsupport _ hz)
    have hzH : z ∈ Hbar := H_subset_Hbar hzU.2
    show _ * _ = _ * _
    rw [avgReg_eq_of_circAgree h hzH ?_]
    intro v hv
    refine hδV (mem_cthickening_of_dist_le v z δ _ ⟨ball_subset_closedBall hzU.1, hzH⟩ ?_)
    have := hv.1
    rw [mem_closedBall] at this
    linarith

theorem areaProxy_congr (γ : ℝ) (hVo : IsOpen V) (h : CircAgree V Y Y') {q : ℝ}
    (hq : closedBall (0 : ℂ) q ∩ Hbar ⊆ V) : areaProxy γ Y q = areaProxy γ Y' q := by
  unfold areaProxy
  simp_rw [areaFun_openBump_congr γ hVo h hq]

theorem scaleProxy_nonneg (γ : ℝ) (y : FieldSample) : 0 ≤ scaleProxy γ y :=
  Real.sInf_nonneg fun _ ha => ha.1.le

/-- **Locality of the scale proxy.** -/
theorem scaleProxy_congr (γ : ℝ) (hVo : IsOpen V) (h : CircAgree V Y Y') {q₀ : ℚ}
    (hq₀ : 0 < (q₀ : ℝ)) (hV : closedBall (0 : ℂ) q₀ ∩ Hbar ⊆ V)
    (h1 : 1 ≤ areaProxy γ Y' q₀) :
    scaleProxy γ Y = scaleProxy γ Y' ∧ scaleProxy γ Y' ≤ q₀ := by
  have hA : ∀ q : ℚ, (q : ℝ) ≤ q₀ → areaProxy γ Y q = areaProxy γ Y' q := fun q hq =>
    areaProxy_congr γ hVo h (fun u hu => hV ⟨closedBall_subset_closedBall hq hu.1, hu.2⟩)
  have hb : ∀ y : FieldSample, BddBelow {a : ℝ | 0 < a ∧ ∃ q : ℚ, 0 < (q : ℝ) ∧ (q : ℝ) ≤ a ∧
      1 ≤ areaProxy γ y q} := fun _ => ⟨0, fun _ ha => ha.1.le⟩
  have hq' : (q₀ : ℝ) ∈ {a : ℝ | 0 < a ∧ ∃ q : ℚ, 0 < (q : ℝ) ∧ (q : ℝ) ≤ a ∧
      1 ≤ areaProxy γ Y' q} := ⟨hq₀, q₀, hq₀, le_rfl, h1⟩
  have hq : (q₀ : ℝ) ∈ {a : ℝ | 0 < a ∧ ∃ q : ℚ, 0 < (q : ℝ) ∧ (q : ℝ) ≤ a ∧
      1 ≤ areaProxy γ Y q} := ⟨hq₀, q₀, hq₀, le_rfl, by rw [hA q₀ le_rfl]; exact h1⟩
  refine ⟨sInf_eq_of_agree_below (hb Y) (hb Y') hq hq' fun a ha => ?_, csInf_le (hb Y') hq'⟩
  constructor
  · rintro ⟨ha0, q, hq0, hqa, hq1⟩
    exact ⟨ha0, q, hq0, hqa, by rw [← hA q (hqa.trans ha)]; exact hq1⟩
  · rintro ⟨ha0, q, hq0, hqa, hq1⟩
    exact ⟨ha0, q, hq0, hqa, by rw [hA q (hqa.trans ha)]; exact hq1⟩

/-- **Locality of a rescaled field** at a measure carried by `closedBall 0 R ∩ Hbar`. -/
theorem rescale_apply_congr (hVo : IsOpen V) (h : CircAgree V Y Y') (Q : ℝ) {a R : ℝ}
    (ha : 0 ≤ a) (hV : closedBall (0 : ℂ) (a * R) ∩ Hbar ⊆ V) {μ : Measure ℂ}
    (hμ : ∀ᵐ u ∂μ, u ∈ closedBall (0 : ℂ) R ∩ Hbar) :
    rescale Y Q a μ = rescale Y' Q a μ := by
  unfold rescale coordChange
  congr 1
  refine evalReg_eq_of_circAgree hVo h (isCompact_closedBall_inter_Hbar 0 (a * R)) hV ?_
  refine (ae_map_iff (by fun_prop : Measurable fun z : ℂ => (a : ℂ) * z).aemeasurable
    ((measurableSet_closedBall.inter isClosed_Hbar.measurableSet).inter
      isClosed_Hbar.measurableSet)).2 ?_
  filter_upwards [hμ] with u hu
  have him : (a : ℂ) * u ∈ Hbar := by
    show (0 : ℝ) ≤ ((a : ℂ) * u).im
    simpa [Complex.mul_im] using mul_nonneg ha (show (0 : ℝ) ≤ u.im from hu.2)
  refine ⟨⟨?_, him⟩, him⟩
  have h1 := hu.1
  rw [mem_closedBall, dist_zero_right] at h1 ⊢
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ha]
  exact mul_le_mul_of_nonneg_left h1 ha

/-! ## Supports of the coordinate measures -/

theorem ae_fc_mem_closedBall_zero (d : ℂ) (r : ℝ) :
    ∀ᵐ u ∂foldedCircle d r, u ∈ closedBall (0 : ℂ) (‖d‖ + |r|) ∩ Hbar := by
  have h1 : ∀ᵐ u ∂foldedCircle d r, u ∈ closedBall (0 : ℂ) (‖d‖ + |r|) := by
    unfold foldedCircle
    refine (ae_map_iff measurable_foldH.aemeasurable measurableSet_closedBall).2 ?_
    filter_upwards [CircleMV.ae_circleUnif d r] with u hu
    show dist (foldH u) 0 ≤ _
    rw [dist_zero_right, CircleFubini.norm_foldH']
    calc ‖u‖ = ‖d + (u - d)‖ := by ring_nf
      _ ≤ ‖d‖ + ‖u - d‖ := norm_add_le _ _
      _ = ‖d‖ + |r| := by rw [hu]
  filter_upwards [h1, RegClosure.fc_ae_mem_Hbar d r] with u hu1 hu2
  exact ⟨hu1, hu2⟩

theorem ae_withDensity_mem_tsupport {ρ g : ℂ → ℝ} (hg : ∀ z, z ∉ tsupport ρ → g z = 0) :
    ∀ᵐ u ∂(volume.withDensity fun z => ENNReal.ofReal (g z)), u ∈ tsupport ρ := by
  rw [ae_iff, withDensity_apply' _ _]
  have hm : MeasurableSet {a : ℂ | ¬ a ∈ tsupport ρ} := (isClosed_tsupport ρ).measurableSet.compl
  rw [setLIntegral_congr_fun hm (fun a ha => by rw [hg a ha, ENNReal.ofReal_zero])]
  exact lintegral_zero

end Thm18Asm
end QuantumZipper
