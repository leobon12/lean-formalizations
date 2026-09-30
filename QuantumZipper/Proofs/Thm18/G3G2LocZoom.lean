import QuantumZipper.Proofs.Thm18.G3G2LocDet

/-!
# Locality of the zoom: cylinder events, and `G3LocStmt` from a scale statement

* `exists_radius_lawCyl`: a cylinder event of `lawOf Z` only depends on the values of `Z` at
  measures carried by `closedBall 0 R ∩ Hbar`, for some `R ≥ 1` depending on the cylinder;
* `zoomLaw_mem_lawCyl_iff` (**deterministic locality of the zoom**): if `y`, `y'` agree on all
  folded circles inside an open `W`, `closedBall(x, q₀ R) ∩ Hbar ⊆ W` and the zoomed field of
  `y'` has `areaProxy ≥ 1` on the half-ball of radius `q₀`, then the cylinder event has the same
  truth value for `zoomLaw γ C y x` and `zoomLaw γ C y' x`;
* `fcAgree_restrictField_circIn`: a region field agrees with the full field on every folded circle
  inside its open half-disc;
* `g3LocStmt_of_scale`: `G3LocStmt γ` follows from `G3ScaleStmt γ` (with Palm probability `→ 1`
  along `g3Filter`, some rational `q` has `closedBall(x, q R) ∩ Hbar` inside region 1 and zoomed
  area `≥ 1` on the half-ball of radius `q`; the same at `R(x)` in region 2).

Sheffield, arXiv:1012.4797, Prop. 5.5 (p. 65: "the restriction of h to an extremely small
neighborhood of x … tells us what the quantum surface looks like when we zoom in near x") and the
proof of Theorem 1.8 (p. 71). The formal argument is own elementary bookkeeping on top of the
locality lemmas of `Prop16LocalAgree` (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology ENNReal symmDiff

namespace QuantumZipper
namespace Thm18Asm

open Prop16Area.G CoordsFull

/-- A cylinder event of `lawOf Z` depends only on `Z` at measures carried by a fixed half-disc. -/
theorem exists_radius_lawCyl {s : Set LawD} (hs : s ∈ lawCyl) : ∃ R : ℝ, 1 ≤ R ∧
    ∀ Z Z' : FieldSample,
      (∀ μ : Measure ℂ, (∀ᵐ u ∂μ, u ∈ closedBall (0 : ℂ) R ∩ Hbar) → Z μ = Z' μ) →
      (lawOf Z ∈ s ↔ lawOf Z' ∈ s) := by
  obtain ⟨A, hA, B, hB, rfl⟩ := hs
  rw [mem_measurableCylinders] at hA hB
  obtain ⟨I, S, -, rfl⟩ := hA
  obtain ⟨J, T, -, rfl⟩ := hB
  have hbd : ∀ ρ : TestFun H, ∃ r : ℝ, tsupport ρ.1 ⊆ closedBall (0 : ℂ) r := fun ρ =>
    ρ.2.2.1.isCompact.isBounded.subset_closedBall 0
  choose rb hrb using hbd
  set a₁ : ℕ → ℝ := fun j => abs (‖(fullIndex j).1‖ + |(fullIndex j).2|)
  set a₂ : TestFun H → ℝ := fun ρ => |rb ρ|
  set R : ℝ := 1 + ∑ j ∈ I, a₁ j + ∑ ρ ∈ J, a₂ ρ
  have h₁ : 0 ≤ ∑ j ∈ I, a₁ j := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have h₂ : 0 ≤ ∑ ρ ∈ J, a₂ ρ := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hI : ∀ j ∈ I, ‖(fullIndex j).1‖ + |(fullIndex j).2| ≤ R := fun j hj =>
    (le_abs_self _).trans ((Finset.single_le_sum (f := a₁) (fun _ _ => abs_nonneg _) hj).trans
      (by simp only [R]; linarith))
  have hJ : ∀ ρ ∈ J, rb ρ ≤ R := fun ρ hρ =>
    (le_abs_self _).trans ((Finset.single_le_sum (f := a₂) (fun _ _ => abs_nonneg _) hρ).trans
      (by simp only [R]; linarith))
  refine ⟨R, by simp only [R]; linarith, fun Z Z' hZ => ?_⟩
  have e₁ : I.restrict (coordsFull Z) = I.restrict (coordsFull Z') := by
    funext j
    refine hZ _ ((ae_fc_mem_closedBall_zero _ _).mono fun u hu => ⟨?_, hu.2⟩)
    exact closedBall_subset_closedBall (hI j j.2) hu.1
  have hsupp : ∀ ρ ∈ J, ∀ g : ℂ → ℝ, (∀ z, z ∉ tsupport ρ.1 → g z = 0) →
      Z (volume.withDensity fun z => ENNReal.ofReal (g z)) =
        Z' (volume.withDensity fun z => ENNReal.ofReal (g z)) := fun ρ hρ g hg =>
    hZ _ ((ae_withDensity_mem_tsupport hg).mono fun u hu =>
      ⟨closedBall_subset_closedBall (hJ ρ hρ) (hrb ρ hu), H_subset_Hbar (ρ.2.2.2 hu)⟩)
  have e₂ : J.restrict (fun ρ : TestFun H => pairRaw Z ρ.1) =
      J.restrict (fun ρ : TestFun H => pairRaw Z' ρ.1) := by
    funext ρ
    simp only [Finset.restrict, pairRaw]
    rw [hsupp ρ ρ.2 (fun z => ρ.1.1 z) (fun z hz => image_eq_zero_of_notMem_tsupport hz),
      hsupp ρ ρ.2 (fun z => -ρ.1.1 z) (fun z hz => by
        rw [image_eq_zero_of_notMem_tsupport hz, neg_zero])]
  simp only [lawOf, mem_prod, mem_cylinder, e₁, e₂]

/-- **Deterministic locality of the zoom.** -/
theorem zoomLaw_mem_lawCyl_iff {s : Set LawD} (hs : s ∈ lawCyl) : ∃ R : ℝ, 1 ≤ R ∧
    ∀ (γ C : ℝ) (y y' : FieldSample) (x : ℝ) (W : Set ℂ), IsOpen W → FcAgree W y y' →
    ∀ q₀ : ℚ, 0 < (q₀ : ℝ) →
      closedBall (0 : ℂ) (q₀ * R) ∩ Hbar ⊆ (fun z => z + (x : ℂ)) ⁻¹' W →
      1 ≤ areaProxy γ (zoomField γ C y' x) q₀ →
      (zoomLaw γ C y x ∈ s ↔ zoomLaw γ C y' x ∈ s) := by
  obtain ⟨R, hR, hRs⟩ := exists_radius_lawCyl hs
  refine ⟨R, hR, fun γ C y y' x W hWo hag q₀ hq₀ hW h1 => ?_⟩
  have hVo : IsOpen ((fun z => z + (x : ℂ)) ⁻¹' W) := hWo.preimage (by fun_prop)
  have hY : FcAgree ((fun z => z + (x : ℂ)) ⁻¹' W) (zoomField γ C y x) (zoomField γ C y' x) :=
    fcAgree_addConst (fcAgree_translate hWo hag.circAgree x) (C / γ)
  have hq₀R : (q₀ : ℝ) ≤ q₀ * R := le_mul_of_one_le_right hq₀.le hR
  obtain ⟨ha, haq⟩ := scaleProxy_congr γ hVo hY.circAgree hq₀
    (fun u hu => hW ⟨closedBall_subset_closedBall hq₀R hu.1, hu.2⟩) h1
  unfold zoomLaw canonProxy
  rw [ha]
  refine hRs _ _ fun μ hμ =>
    rescale_apply_congr hVo hY.circAgree _ (scaleProxy_nonneg γ _) (R := R) ?_ hμ
  intro u hu
  exact hW ⟨closedBall_subset_closedBall
    (mul_le_mul_of_nonneg_right haq (by linarith)) hu.1, hu.2⟩

/-- A region field agrees with the full field on the folded circles inside its half-disc. -/
theorem fcAgree_restrictField_circIn (t r : ℝ) (y : FieldSample) :
    FcAgree (ball (t : ℂ) r) (restrictField (circIn t r) y) y := by
  classical
  intro d hd ρ hρ hsub
  have hK : IsCompact (closedBall d ρ ∩ Hbar) := isCompact_closedBall_inter_Hbar d ρ
  obtain ⟨u₀, hu₀, hmax⟩ := hK.exists_isMaxOn ⟨d, mem_closedBall_self hρ.le, hd⟩
    (continuous_id.dist continuous_const).continuousOn
  have hmem : foldedCircle d ρ ∈ circIn t r := by
    refine ⟨d, ρ, hρ, rfl, dist u₀ (t : ℂ), mem_ball.1 (hsub hu₀), ?_⟩
    have hae : ∀ᵐ u ∂foldedCircle d ρ, u ∈ closedBall (t : ℂ) (dist u₀ (t : ℂ)) :=
      (ae_fc_mem_ball_inter hd hρ).mono fun u hu => mem_closedBall.2 (hmax hu)
    exact ae_iff.1 hae
  simp only [restrictField, if_pos hmem]

/-- **The scale statement** (probabilistic input for the locality of the zoom): for every
`R ≥ 1`, with Palm probability `→ 1` along `g3Filter` some rational `q > 0` has
`closedBall(x, q R) ∩ Hbar` inside region 1 and the zoomed full field has `areaProxy ≥ 1` on the
half-ball of radius `q`; the same at `R(x)` and region 2. -/
def G3ScaleStmt (γ : ℝ) : Prop :=
  ∀ R : ℝ, 1 ≤ R →
    Tendsto (fun i => (g3PalmLaw γ i).real {p | ¬ ∃ q : ℚ, 0 < (q : ℝ) ∧
      closedBall (0 : ℂ) (q * R) ∩ Hbar ⊆ (fun z => z + (g3X γ i p : ℂ)) ⁻¹' ball (i.t₁ : ℂ) i.r₁ ∧
      1 ≤ areaProxy γ (zoomField γ i.C (normField γ gffBase.X p.1) (g3X γ i p)) q})
      g3Filter (𝓝 0) ∧
    Tendsto (fun i => (g3PalmLaw γ i).real {p | ¬ ∃ q : ℚ, 0 < (q : ℝ) ∧
      closedBall (0 : ℂ) (q * R) ∩ Hbar ⊆ (fun z => z + (g3R γ i p : ℂ)) ⁻¹' ball (i.t₂ : ℂ) i.r₂ ∧
      1 ≤ areaProxy γ (zoomField γ i.C (normField γ gffBase.X p.1) (g3R γ i p)) q})
      g3Filter (𝓝 0)

theorem symmDiff_subset_of_iff {α β : Type*} {f g : α → β} {s : Set β} {E : Set α}
    (h : ∀ p, p ∉ E → (f p ∈ s ↔ g p ∈ s)) : (f ⁻¹' s) ∆ (g ⁻¹' s) ⊆ E := by
  intro p hp
  by_contra hE
  have := h p hE
  rw [mem_symmDiff] at hp
  simp only [mem_preimage] at hp
  tauto

/-- **Locality of the zoom from the scale statement.** -/
theorem g3LocStmt_of_scale {γ : ℝ} (h : G3ScaleStmt γ) : G3LocStmt γ := by
  refine ⟨fun s hs => ?_, fun s hs => ?_⟩
  · obtain ⟨R, hR, hloc⟩ := zoomLaw_mem_lawCyl_iff hs
    refine squeeze_zero (fun _ => measureReal_nonneg) (fun i => measureReal_mono
      (symmDiff_subset_of_iff fun p hp => ?_)) (h R hR).1
    simp only [mem_ofPred_eq, not_not] at hp
    obtain ⟨q, hq, hW, h1⟩ := hp
    exact hloc γ i.C _ _ _ _ isOpen_ball (fcAgree_restrictField_circIn _ _ _) q hq hW h1
  · obtain ⟨R, hR, hloc⟩ := zoomLaw_mem_lawCyl_iff hs
    refine squeeze_zero (fun _ => measureReal_nonneg) (fun i => measureReal_mono
      (symmDiff_subset_of_iff fun p hp => ?_)) (h R hR).2
    simp only [mem_ofPred_eq, not_not] at hp
    obtain ⟨q, hq, hW, h1⟩ := hp
    exact hloc γ i.C _ _ _ _ isOpen_ball (fcAgree_restrictField_circIn _ _ _) q hq hW h1

end Thm18Asm
end QuantumZipper
