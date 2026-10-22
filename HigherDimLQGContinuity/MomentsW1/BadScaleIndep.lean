import HigherDimLQGContinuity.MomentsW1.BadScaleProb
import HigherDimLQGMetric.DGZ.Sec41Nice

/-! # Finite-range independence of the enlarged-region rough sites -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace

namespace HigherDimLQGContinuity

open HigherDimLFPP HigherDimLFPP.Perc
open HigherDimLFPP.DGZ (latPt cbox closedSite)
open HigherDimLQGMetric.DGZ

/-- The masked fine-field statuses have the pinned dependence range. -/
theorem wnClosed_productBound {d : ℕ} {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ}
    (hH : IsDyadicRealization κ P W H) {ρ : ℝ}
    (hρ : ∀ y, ρ ≤ ‖y‖ → κ y = 0) (ξ R : ℝ) (q : ℝ≥0∞)
    {k n : ℕ} (hkn : k ≤ n) :
    ProductBound P (wnClosed P H ξ R q k n) ((⌈2 * (2 + ρ)⌉₊ : ℕ) : ℤ) := by
  let G : Rd d → Ω → ℝ := fun z ω => H n z ω - H k z ω
  have hG : IsBandVersion P W κ ((2 : ℝ)⁻¹ ^ n) ((2 : ℝ)⁻¹ ^ k) G :=
    isBandVersion_sub_of_realization hκ hH hkn
  apply productBound_of_local hκ hH.whiteNoise hρ (by positivity) hG
    (by positivity) le_rfl (R := 2)
  intro x
  exact (MeasurableSet.const _).inter
    (HigherDimLFPP.DGZ.measurableSet_closedSite_comap hG.continuous (by positivity)
      ξ (aQ P H ξ (n - k) q) (R + 3) x)

/-- The local coarse/fine status inherits the same dependence range as the pinned rough-site
status. Its region cutoff is deterministic and therefore does not enlarge the local field box. -/
theorem wnRough_productBound {d : ℕ} {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ}
    (hH : IsDyadicRealization κ P W H) {ρ : ℝ}
    (hρ : ∀ y, ρ ≤ ‖y‖ → κ y = 0) (ξ R : ℝ) (q : ℝ≥0∞)
    {k n : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    ProductBound P (wnRough P H ξ R q k n) ((⌈2 * (2 + ρ)⌉₊ : ℕ) : ℤ) := by
  let G₁ : Rd d → Ω → ℝ := fun z ω => H n z ω - H (k - 1) z ω
  let G₂ : Rd d → Ω → ℝ := fun z ω => H n z ω - H k z ω
  have hG₁ : IsBandVersion P W κ ((2 : ℝ)⁻¹ ^ n) ((2 : ℝ)⁻¹ ^ (k - 1)) G₁ :=
    isBandVersion_sub_of_realization hκ hH (by omega)
  have hG₂ : IsBandVersion P W κ ((2 : ℝ)⁻¹ ^ n) ((2 : ℝ)⁻¹ ^ k) G₂ :=
    isBandVersion_sub_of_realization hκ hH hkn
  let a₁ : ℝ := aQ P H ξ (n - (k - 1)) q
  let a₂ : ℝ := aQ P H ξ (n - k) q
  intro S hS
  let M : ℕ := ⌈2 * (2 + ρ)⌉₊
  have hρ0 : 0 < ρ := hκ.radius_pos hρ
  have hM : 2 * (2 + ρ) ≤ (M : ℝ) := Nat.le_ceil _
  let s₁ : ℝ := (2 : ℝ)⁻¹ ^ (k - 1)
  let s₂ : ℝ := (2 : ℝ)⁻¹ ^ k
  have hs₁ : 0 < s₁ := by positivity
  have hs₂ : 0 < s₂ := by positivity
  have hs₂₁ : s₂ ≤ s₁ := by rw [show s₁ = 2 * s₂ by exact inv_two_pow_pred hk]; linarith
  let A : S → Set (Rd d) := fun y => cbox (latPt s₁ y) (2 * s₁)
  have hfar : ∀ y₁ y₂ : S, y₁ ≠ y₂ → ∀ z ∈ A y₁, ∀ w ∈ A y₂,
      2 * ρ * s₁ ≤ ‖z - w‖ := by
    intro y₁ y₂ hne z hz w hw
    have hnot := hS y₁ y₁.2 y₂ y₂.2 fun h => hne (Subtype.ext h)
    simp only [WithinInf, not_forall, not_le] at hnot
    obtain ⟨l, hl⟩ := hnot
    have hl1 : (M : ℤ) + 1 ≤ |(y₁ : Zd d) l - (y₂ : Zd d) l| := hl
    have hl' : (M : ℝ) + 1 ≤ |((y₁ : Zd d) l : ℝ) - ((y₂ : Zd d) l : ℝ)| := by
      exact_mod_cast hl1
    have h1 := hz l
    have h2 := hw l
    rw [HigherDimLFPP.DGZ.latPt_apply] at h1 h2
    have h3 : |s₁ * ((y₁ : Zd d) l : ℝ) - s₁ * ((y₂ : Zd d) l : ℝ)| ≤
        |z l - s₁ * ((y₁ : Zd d) l : ℝ)| + |z l - w l| +
          |w l - s₁ * ((y₂ : Zd d) l : ℝ)| := by
      have e : s₁ * ((y₁ : Zd d) l : ℝ) - s₁ * ((y₂ : Zd d) l : ℝ) =
          -(z l - s₁ * ((y₁ : Zd d) l : ℝ)) + (z l - w l) +
            (w l - s₁ * ((y₂ : Zd d) l : ℝ)) := by ring
      rw [e]
      refine (abs_add_le _ _).trans (add_le_add_left ((abs_add_le _ _).trans ?_) _)
      rw [abs_neg]
    have h4 : |s₁ * ((y₁ : Zd d) l : ℝ) - s₁ * ((y₂ : Zd d) l : ℝ)| =
        s₁ * |((y₁ : Zd d) l : ℝ) - ((y₂ : Zd d) l : ℝ)| := by
      rw [← mul_sub, abs_mul, abs_of_pos hs₁]
    have h5 := HigherDimLFPP.DGZ.abs_apply_le_norm (z - w) l
    rw [PiLp.sub_apply] at h5
    nlinarith
  let F : (y : S) → (A y ⊕ A y) → WN d := fun y p =>
    Sum.elim (fun z : A y => bandVec κ ((2 : ℝ)⁻¹ ^ n) s₁ z)
      (fun z : A y => bandVec κ ((2 : ℝ)⁻¹ ^ n) s₂ z) p
  let X : (y : S) → (A y ⊕ A y) → Ω → ℝ := fun y p =>
    Sum.elim (fun z : A y => G₁ z) (fun z : A y => G₂ z) p
  have hmin : ∀ b b' : ℝ, (b = s₁ ∨ b = s₂) → (b' = s₁ ∨ b' = s₂) → min b b' ≤ s₁ := by
    rintro b b' (rfl | rfl) -
    · exact min_le_left _ _
    · exact (min_le_left _ _).trans hs₂₁
  have horth : ∀ y₁ y₂ : S, y₁ ≠ y₂ → ∀ (p₁ : A y₁ ⊕ A y₁) (p₂ : A y₂ ⊕ A y₂),
      ⟪F y₁ p₁, F y₂ p₂⟫ = 0 := by
    intro y₁ y₂ hne p₁ p₂
    have key : ∀ (b b' : ℝ), (b = s₁ ∨ b = s₂) → (b' = s₁ ∨ b' = s₂) →
        ∀ z ∈ A y₁, ∀ w ∈ A y₂,
          ⟪bandVec κ ((2 : ℝ)⁻¹ ^ n) b z,
            bandVec κ ((2 : ℝ)⁻¹ ^ n) b' w⟫ = 0 := by
      intro b b' hb hb' z hz w hw
      refine inner_bandVec_eq_zero_of_two_mul_min_le hκ hρ (by positivity) (by positivity) ?_
      calc
        2 * ρ * min b b' ≤ 2 * ρ * s₁ :=
          mul_le_mul_of_nonneg_left (hmin b b' hb hb') (by positivity)
        _ ≤ ‖z - w‖ := hfar y₁ y₂ hne z hz w hw
    rcases p₁ with z | z <;> rcases p₂ with w | w
    · exact key s₁ s₁ (Or.inl rfl) (Or.inl rfl) z z.2 w w.2
    · exact key s₁ s₂ (Or.inl rfl) (Or.inr rfl) z z.2 w w.2
    · exact key s₂ s₁ (Or.inr rfl) (Or.inl rfl) z z.2 w w.2
    · exact key s₂ s₂ (Or.inr rfl) (Or.inr rfl) z z.2 w w.2
  have hXae : ∀ (y : S) (p : A y ⊕ A y), X y p =ᵐ[P] W (F y p) := by
    intro y p
    rcases p with z | z
    · exact hG₁.ae_eq z
    · exact hG₂.ae_eq z
  have hind := hH.whiteNoise.iIndepFun_of_ae_eq F horth hXae
  have hmeas : ∀ y : S, MeasurableSet[MeasurableSpace.comap
      (fun ω (p : A y ⊕ A y) => X y p ω) MeasurableSpace.pi]
      (wnRough P H ξ R q k n y) := by
    intro y
    have hle₁ : MeasurableSpace.comap (fun ω (z : A y) => G₁ z ω) MeasurableSpace.pi ≤
        MeasurableSpace.comap (fun ω (p : A y ⊕ A y) => X y p ω) MeasurableSpace.pi := by
      have e : (fun ω (z : A y) => G₁ z ω) =
          (fun f : (A y ⊕ A y) → ℝ => fun z => f (Sum.inl z)) ∘
            (fun ω (p : A y ⊕ A y) => X y p ω) := rfl
      rw [e, ← MeasurableSpace.comap_comp]
      exact MeasurableSpace.comap_mono
        (measurable_pi_iff.2 fun z => measurable_pi_apply (Sum.inl z)).comap_le
    have hle₂ : MeasurableSpace.comap (fun ω (z : A y) => G₂ z ω) MeasurableSpace.pi ≤
        MeasurableSpace.comap (fun ω (p : A y ⊕ A y) => X y p ω) MeasurableSpace.pi := by
      have e : (fun ω (z : A y) => G₂ z ω) =
          (fun f : (A y ⊕ A y) → ℝ => fun z => f (Sum.inr z)) ∘
            (fun ω (p : A y ⊕ A y) => X y p ω) := rfl
      rw [e, ← MeasurableSpace.comap_comp]
      exact MeasurableSpace.comap_mono
        (measurable_pi_iff.2 fun z => measurable_pi_apply (Sum.inr z)).comap_le
    have hc₁ : MeasurableSet[MeasurableSpace.comap
        (fun ω (p : A y ⊕ A y) => X y p ω) MeasurableSpace.pi]
        (wnClosed P H ξ R q (k - 1) n y) :=
      (MeasurableSet.const _).inter (hle₁ _
        (HigherDimLFPP.DGZ.measurableSet_closedSite_comap hG₁.continuous hs₁ ξ a₁ _ y))
    have hc₂ : ∀ z : Zd d, WithinInf 1 z (2 • (y : Zd d)) →
        MeasurableSet[MeasurableSpace.comap
          (fun ω (p : A y ⊕ A y) => X y p ω) MeasurableSpace.pi]
          (wnClosed P H ξ R q k n z) := by
      intro z hz
      exact (MeasurableSet.const _).inter (hle₂ _
        (comap_restrict_le G₂ (cbox_fine_subset hk hz) _
          (HigherDimLFPP.DGZ.measurableSet_closedSite_comap hG₂.continuous hs₂ ξ a₂ _ z)))
    rw [wnRough_eq]
    exact hc₁.union (Finset.measurableSet_biUnion _ fun z hz => hc₂ z (mem_boxF.1 hz))
  have h := hind.meas_iInter (s := fun y : S => wnRough P H ξ R q k n y) hmeas
  have e : (⋂ y ∈ S, wnRough P H ξ R q k n y) =
      ⋂ y : S, wnRough P H ξ R q k n y := by
    ext ω
    simp only [mem_iInter, Subtype.forall]
  rw [e, h, Finset.prod_coe_sort S fun y => P (wnRough P H ξ R q k n y)]

end HigherDimLQGContinuity
