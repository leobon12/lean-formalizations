import QuantumZipper.Proofs.Thm18.G4WeldRound
import QuantumZipper.Proofs.Zipper.Cor15HullNull
import QuantumZipper.Proofs.Zipper.UnzipFullSplit
import QuantumZipper.Proofs.Thm14.OptB

/-!
# Theorem 1.8, node G4: removability at the random unzipping time

Blueprint `SECTION5_BLUEPRINT.md` G4 (as superseded by D6): "forward hull at a random time: the
same reduction of the forward hull to a reverse hull of the reversed driver … and removability
of compact subsets". Proved here:

* `isConformallyRemovable_mono`: a closed subset of a conformally removable compact set is
  conformally removable (immediate from the definition: a homeomorphism holomorphic off the
  smaller set is holomorphic off the larger one).
* `isConformallyRemovable_mul`: conformal removability is invariant under `z ↦ c z`, `c ≠ 0`
  (conjugate the homeomorphism by the dilation).
* `revHull_revDrv_subset`: the reverse hull of the rescaled time reversal
  `revDrv W t' a = (t'/a², u ↦ (W(t' − a²u) − W t')/a)` is contained in `a⁻¹ · fwdHull W t'`
  (Loewner scaling A1(d), `LoewnerAlgebra.revMap_scale`, and `revHull (vrev W t') t' =
  fwdHull W t'`).
* `ae_remHull_revDrv`: for the SLE_κ driver `W = √κ B` of Theorem 1.8 (`κ = γ² < 4`), a.s.
  **for all** `t' > 0` and `a > 0`, the doubled hull of `revDrv W t' a` is conformally removable.
  Route: `fwdHull W t' ⊆ fwdHull W (n+1)` for `n = ⌈t'⌉`, `fwdHull W (n+1)` is the reverse hull
  of the reverse flow driven by a Brownian motion `B'ₙ` (`UnzipFull.exists_unzip_driver`), whose
  doubled hull is a.s. removable (`JS.ae_removable_doubledHull'`, Jones–Smirnov via the
  Rohde–Schramm Hölder property); countably many `n`.

All arguments are elementary (**own argument**, following the blueprint sketch).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Complex
open scoped NNReal ENNReal ComplexConjugate

namespace QuantumZipper
namespace Thm18Asm

/-! ## Removability: subsets and dilations -/

theorem isConformallyRemovable_mono {K K' : Set ℂ} (hK : IsConformallyRemovable K)
    (hsub : K' ⊆ K) (hc : IsClosed K') : IsConformallyRemovable K' :=
  ⟨hK.1.of_isClosed_subset hc hsub, fun φ hφ => hK.2 φ (hφ.mono (compl_subset_compl.2 hsub))⟩

theorem isConformallyRemovable_mul {K : Set ℂ} (hK : IsConformallyRemovable K) {c : ℂ}
    (hc : c ≠ 0) : IsConformallyRemovable ((fun z => c * z) '' K) := by
  refine ⟨hK.1.image (continuous_const.mul continuous_id), fun φ hφ => ?_⟩
  set e : ℂ ≃ₜ ℂ := Homeomorph.mulLeft₀ c hc
  set ψ : ℂ ≃ₜ ℂ := (e.trans φ).trans e.symm
  have hψ : ∀ z, ψ z = c⁻¹ * φ (c * z) := fun z => rfl
  have hψd : DifferentiableOn ℂ ψ Kᶜ := by
    have h1 : DifferentiableOn ℂ (fun z => φ (c * z)) Kᶜ := by
      refine hφ.comp ((differentiable_const c).mul differentiable_id).differentiableOn ?_
      intro z hz hz'
      obtain ⟨y, hy, hyz⟩ := hz'
      exact hz (by rwa [mul_left_cancel₀ hc hyz] at hy)
    have := h1.const_mul c⁻¹
    exact this.congr fun z _ => hψ z
  have hψD := hK.2 ψ hψd
  have hφe : ∀ w, φ w = c * ψ (c⁻¹ * w) := fun w => by
    rw [hψ, ← mul_assoc, mul_inv_cancel₀ hc, one_mul, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  have : (fun w => φ w) = fun w => c * ψ (c⁻¹ * w) := funext hφe
  intro w
  have hd : DifferentiableAt ℂ (fun w => c * ψ (c⁻¹ * w)) w :=
    (differentiableAt_const c).mul ((hψD _).comp w ((differentiableAt_const _).mul
      differentiableAt_id))
  rw [← this] at hd
  exact hd

/-! ## The reverse hull of the rescaled time reversal -/

theorem revMap_revDrv {W : ℝ → ℝ} (hW : Continuous W) {t' a : ℝ} (ht : 0 ≤ t') (ha : 0 < a)
    {y : ℂ} (hy : y ∈ H) :
    revMap (revDrv W t' a).2 (revDrv W t' a).1 y = revMap (B2.vrev W t') t' (a * y) / a := by
  have hVc : Continuous (B2.vrev W t') := by unfold B2.vrev; fun_prop
  have heq : EqOn (revDrv W t' a).2 (fun s => B2.vrev W t' (a ^ 2 * s) / a)
      (Icc 0 (revDrv W t' a).1) := by
    intro s hs
    simp only [revDrv] at hs ⊢
    have hs2 : a ^ 2 * s ≤ t' := by
      have := hs.2
      rw [le_div_iff₀ (by positivity)] at this
      linarith
    simp only [B2.vrev, max_eq_left (mul_nonneg (sq_nonneg a) hs.1), min_eq_left hs2]
  have hT : 0 ≤ (revDrv W t' a).1 := by
    simp only [revDrv]
    positivity
  have hT' : a ^ 2 * (revDrv W t' a).1 = t' := by
    simp only [revDrv]
    field_simp
  rw [revMap_congr_lenZip heq, LoewnerAlgebra.revMap_scale _ hVc ha hT hy, hT']

theorem revHull_revDrv_subset {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {t' a : ℝ}
    (ht : 0 < t') (ha : 0 < a) :
    revHull (revDrv W t' a).2 (revDrv W t' a).1 ⊆
      (fun z => ((a : ℂ))⁻¹ * z) '' fwdHull W t' := by
  intro w hw
  obtain ⟨hwH, hwn⟩ := hw
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  refine ⟨a * w, ?_, ?_⟩
  swap
  · show (a : ℂ)⁻¹ * (a * w) = w
    rw [← mul_assoc, inv_mul_cancel₀ haC, one_mul]
  rw [← Cor15Group.revHull_vrev_eq_fwdHull hW hW0 ht]
  refine ⟨?_, fun ⟨z, hz, hzw⟩ => hwn ?_⟩
  · show 0 < ((a : ℂ) * w).im
    simpa using mul_pos ha (show 0 < w.im from hwH)
  · have hzH : (a : ℂ)⁻¹ * z ∈ H := by
      show 0 < ((a : ℂ)⁻¹ * z).im
      have : ((a : ℂ)⁻¹ * z).im = a⁻¹ * z.im := by
        rw [← Complex.ofReal_inv, Complex.im_ofReal_mul]
      rw [this]
      exact mul_pos (inv_pos.2 ha) hz
    refine ⟨_, hzH, ?_⟩
    rw [revMap_revDrv hW ht.le ha hzH, ← mul_assoc, mul_inv_cancel₀ haC, one_mul, hzw,
      mul_div_cancel_left₀ _ haC]

theorem isClosed_conj_image {C : Set ℂ} (hC : IsClosed C) : IsClosed (conj '' C) := by
  have : conj '' C = conj ⁻¹' C := congrFun
    (Set.image_eq_preimage_of_inverse (f := conj) (g := conj) (fun z => Complex.conj_conj z)
      (fun z => Complex.conj_conj z)) C
  rw [this]
  exact hC.preimage Complex.continuous_conj

/-- The doubled hull of a subset of a dilate is contained in the dilate of the doubled hull. -/
theorem doubled_subset_mul {S F : Set ℂ} {r : ℝ} (hr : r ≠ 0)
    (hsub : S ⊆ (fun z => (r : ℂ) * z) '' F) :
    closure S ∪ conj '' closure S ⊆
      (fun z => (r : ℂ) * z) '' (closure F ∪ conj '' closure F) := by
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  have hcl : closure S ⊆ (fun z => (r : ℂ) * z) '' closure F := by
    have h1 := (Homeomorph.mulLeft₀ (r : ℂ) hrC).image_closure F
    have h2 : closure S ⊆ closure ((fun z => (r : ℂ) * z) '' F) := closure_mono hsub
    exact h2.trans (le_of_eq h1.symm)
  rintro w (hw | ⟨x, hx, rfl⟩)
  · obtain ⟨y, hy, rfl⟩ := hcl hw
    exact ⟨y, Or.inl hy, rfl⟩
  · obtain ⟨y, hy, rfl⟩ := hcl hx
    refine ⟨conj y, Or.inr ⟨y, hy, rfl⟩, ?_⟩
    simp only [map_mul, Complex.conj_ofReal]

/-! ## Removability at all times, a.s. -/

/-- **Removability of the doubled hull of `revDrv W t' a`**, a.s. simultaneously for all
`t' > 0`, `a > 0`, for the SLE_κ driver of Theorem 1.8. -/
theorem ae_remHull_revDrv {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} {Y : Ω → FieldSample}
    (hS : Thm18Setting γ P B Y) :
    ∀ᵐ ω ∂P, ∀ t' a : ℝ, 0 < t' → 0 < a → RemHull (revDrv (drive (γ ^ 2) B ω) t' a) := by
  obtain ⟨hγ, hγ2, hB, -, hind⟩ := hS
  have hκ : 0 < γ ^ 2 := by positivity
  have hκ4 : γ ^ 2 < 4 := by nlinarith
  have hn : ∀ n : ℕ, ∀ᵐ ω ∂P, IsConformallyRemovable
      (closure (fwdHull (drive (γ ^ 2) B ω) ((n : ℝ) + 1)) ∪
        conj '' closure (fwdHull (drive (γ ^ 2) B ω) ((n : ℝ) + 1))) := by
    intro n
    have hT : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    obtain ⟨B', hB', -, -, -, hEq⟩ := UnzipFull.exists_unzip_driver (γ ^ 2) hB hind hT.le
    filter_upwards [JS.ae_removable_doubledHull' CaraR.revMapCaratheodory RS.rohdeSchrammSimple
      (γ ^ 2) hκ hκ4 ((n : ℝ) + 1) hT P B' hB', hEq, hB.cont, hB.eval_zero_ae_eq_zero]
      with ω hrem he hc h0
    have hW := drive_continuous (κ := γ ^ 2) hc
    have hW0 := drive_zero (κ := γ ^ 2) h0
    have e1 : fwdHull (drive (γ ^ 2) B ω) ((n : ℝ) + 1) =
        revHull (drive (γ ^ 2) B' ω) ((n : ℝ) + 1) := by
      rw [← Cor15Group.revHull_vrev_eq_fwdHull hW hW0 hT]
      unfold revHull
      congr 1
      refine EqOn.image_eq fun z hz => ?_
      exact (B2.fwdMapInv_eq_revMap_vrev hW hW0 hT.le hz).symm.trans (he hz)
    rw [e1]
    exact hrem
  filter_upwards [ae_all_iff.2 hn, hB.cont, hB.eval_zero_ae_eq_zero] with ω hrem hc h0
  intro t' a ht ha
  have hW := drive_continuous (κ := γ ^ 2) hc
  have hW0 := drive_zero (κ := γ ^ 2) h0
  set n := ⌈t'⌉₊
  have htn : t' ≤ (n : ℝ) + 1 := (Nat.le_ceil t').trans (by linarith)
  have hsub : revHull (revDrv (drive (γ ^ 2) B ω) t' a).2 (revDrv (drive (γ ^ 2) B ω) t' a).1 ⊆
      (fun z => ((a⁻¹ : ℝ) : ℂ) * z) '' fwdHull (drive (γ ^ 2) B ω) ((n : ℝ) + 1) := by
    refine (revHull_revDrv_subset hW hW0 ht ha).trans ?_
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨z, (fwdHull_mono (W := drive (γ ^ 2) B ω)).1 htn hz, by simp⟩
  have hainv : (a⁻¹ : ℝ) ≠ 0 := inv_ne_zero ha.ne'
  have hK := isConformallyRemovable_mul (hrem n) (c := ((a⁻¹ : ℝ) : ℂ)) (by exact_mod_cast hainv)
  exact isConformallyRemovable_mono hK (doubled_subset_mul hainv hsub)
    (isClosed_closure.union (isClosed_conj_image isClosed_closure))

/-! ## The round trip `Z_ℓ ∘ Z_{−ℓ}` without the removability conjunct -/

end Thm18Asm
end QuantumZipper
