import HigherDimLQGMetric.DGZ.FunctionalsMeas
import HigherDimLFPP.Exist.Scaling

/-!
# Similarity covariance and similarity laws of the LFPP functionals (packet L3b1)

Source: MA7 (`planning/audits/MA7-ref2-sections-4-6.md`) §5 row L3b1 ("similarity laws"; reuse of
HigherDimLFPP `Field/SymmetryLaw.lean` (`map_comp_sim_eq_of_measurable`) and `Exist/Scaling.lean`),
Details (a) D-4.8 ("`selfDiam[h_{m,n}](B_{2^{1-m}}(w))` has the law of
`2^{1-m} selfDiam[h_{1,n-m+1}](B₁(0))`"), D-4.9 ("`selfDiam[h_{m,n}](obox(s x, s))` has the law of
`s · selfDiam_{n-m}(B₁(0))`"), D-4.10 and D-5.5 (across distances of rescaled shells), D-5.3
(translation invariance of the box statuses) and D-ADP (`D[G ε](r x, r y) = r · D[H](x, y)`).

Deterministic covariance under a similarity `T z = x₀ + r • O z` (`r > 0`, `O` a linear isometry):
* `lfppSetDist_sim`: `D(T A, T B; T V)(φ) = r · D(A, B; V)(φ ∘ T)`;
* `lfppDiam_sim`: `Diam(T U; T V)(φ) = r · Diam(U; V)(φ ∘ T)`;
* `lfppMetric_sim`: `D^ξ(φ)(T x, T y) = r · D^ξ(φ ∘ T)(x, y)`;
and, for `T z = x₀ + r • z` (images of `ℓ^∞` boxes are boxes: `image_obox_smul_add`,
`image_cbox_smul_add`, `image_lsph_smul_add`):
* `acrossDist_smul_add`: `D(across B_{r r₁}(T c) \ B_{r r₂}(T c))(φ) = r · D(across …)(φ ∘ T)`;
* `selfDiam_smul_add`: `selfDiam(φ)(B_{r ρ}(T c)) = r · selfDiam(φ ∘ T)(B_ρ(c))`;
* Euclidean balls (general `O`): `image_sphere_sim`, `image_ball_sim`, `image_closedBall_sim`,
  `lfppSetDist_sphere_sim`;
* shell crossings and `AroundGood` (MA7 D-5.3, rescaled certificates):
  `IsShellCrossing.comp_smul_add_inv`, **`AroundGood.smul_add`** (`AroundGood` for `φ ∘ T` at
  `(c, r₁, r₂, B, t)` gives `AroundGood` for `φ` at `(T c, r r₁, r r₂, T B, r t)`) and the converse
  `AroundGood.of_smul_add`.

Laws (versions `H` of `H_{a,b}` over `W` and `H'` of `H_{a/r,b/r}` over any white noise `W'`,
`0 < a`):
* `map_lfppSetDist_sim_eq`, `map_lfppDiam_sim_eq` (open preconnected
  `V`), `map_lfppMetric_sim_eq` (jointly in the pair of points);
* **`map_acrossDist_sim_eq`**, **`map_selfDiam_sim_eq`**: the law of the
  functional of `H` on the image box is the law of `r ×` the functional of `H'`;
* translation invariance (`r = 1`, same band): `map_acrossDist_translate_eq`,
  `map_selfDiam_translate_eq`.

(These take the band version `hH` as their first explicit argument; they live in
`HigherDimLQGMetric.DGZ`, so dot notation on `hH : HigherDimLFPP.IsBandVersion …` does not apply.)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Pointwise

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP
open HigherDimLFPP.DGZ (cbox obox)

variable {d : ℕ}

/-! ## Images of boxes under `z ↦ x₀ + r z` -/

section Images

variable (x₀ c : Rd d) {r : ℝ}

theorem smul_add_apply (x₀ z : Rd d) (r : ℝ) (i : Fin d) : (x₀ + r • z) i = x₀ i + r * z i := by
  rw [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]

theorem abs_smul_add_sub (x₀ z c : Rd d) {r : ℝ} (hr : 0 < r) (i : Fin d) :
    |(x₀ + r • z) i - (x₀ + r • c) i| = r * |z i - c i| := by
  rw [smul_add_apply, smul_add_apply, add_sub_add_left_eq_sub, ← mul_sub, abs_mul,
    abs_of_pos hr]

/-- The inverse point `r⁻¹ (w - x₀)`. -/
theorem smul_add_inv (x₀ w : Rd d) {r : ℝ} (hr : 0 < r) : x₀ + r • (r⁻¹ • (w - x₀)) = w := by
  rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul, add_sub_cancel]

theorem image_obox_smul_add (hr : 0 < r) (ρ : ℝ) :
    (fun z => x₀ + r • z) '' obox c ρ = obox (x₀ + r • c) (r * ρ) := by
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩ i
    rw [abs_smul_add_sub x₀ z c hr]
    exact mul_lt_mul_of_pos_left (hz i) hr
  · intro hw
    refine ⟨r⁻¹ • (w - x₀), fun i => ?_, smul_add_inv x₀ w hr⟩
    have h := hw i
    rw [← smul_add_inv x₀ w hr, abs_smul_add_sub x₀ _ c hr] at h
    exact lt_of_mul_lt_mul_left h hr.le

theorem image_cbox_smul_add (hr : 0 < r) (ρ : ℝ) :
    (fun z => x₀ + r • z) '' cbox c ρ = cbox (x₀ + r • c) (r * ρ) := by
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩ i
    rw [abs_smul_add_sub x₀ z c hr]
    exact mul_le_mul_of_nonneg_left (hz i) hr.le
  · intro hw
    refine ⟨r⁻¹ • (w - x₀), fun i => ?_, smul_add_inv x₀ w hr⟩
    have h := hw i
    rw [← smul_add_inv x₀ w hr, abs_smul_add_sub x₀ _ c hr] at h
    exact le_of_mul_le_mul_left h hr

theorem injective_smul_add (hr : 0 < r) : Function.Injective fun z : Rd d => x₀ + r • z :=
  fun _ _ h => smul_right_injective (Rd d) hr.ne' (add_left_cancel h)

theorem image_univ_smul_add (hr : 0 < r) : (fun z : Rd d => x₀ + r • z) '' univ = univ :=
  eq_univ_of_forall fun w => ⟨r⁻¹ • (w - x₀), mem_univ _, smul_add_inv x₀ w hr⟩

theorem image_lsph_smul_add (hr : 0 < r) (ρ : ℝ) :
    (fun z => x₀ + r • z) '' lsph c ρ = lsph (x₀ + r • c) (r * ρ) := by
  rw [lsph, image_sdiff (injective_smul_add x₀ hr), image_cbox_smul_add x₀ c hr,
    image_obox_smul_add x₀ c hr, lsph]

theorem image_shell_smul_add (hr : 0 < r) (r₁ r₂ : ℝ) :
    (fun z => x₀ + r • z) '' (cbox c r₁ \ obox c r₂) =
      cbox (x₀ + r • c) (r * r₁) \ obox (x₀ + r • c) (r * r₂) := by
  rw [image_sdiff (injective_smul_add x₀ hr), image_cbox_smul_add x₀ c hr,
    image_obox_smul_add x₀ c hr]

end Images

/-! ## Deterministic covariance -/

section Covariance

variable (O : Rd d ≃ₗᵢ[ℝ] Rd d) (x₀ : Rd d) {r : ℝ} (ξ : ℝ) (φ : Rd d → ℝ)

/-- The image of a product of sets under the similarity applied in both coordinates. -/
theorem image_prod_sim (A B : Set (Rd d)) (T : Rd d → Rd d) :
    (T '' A) ×ˢ (T '' B) = (fun p : Rd d × Rd d => (T p.1, T p.2)) '' (A ×ˢ B) := by
  ext ⟨u, v⟩
  constructor
  · rintro ⟨⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩⟩
    exact ⟨(a, b), ⟨ha, hb⟩, rfl⟩
  · rintro ⟨⟨a, b⟩, ⟨ha, hb⟩, he⟩
    simp only [Prod.mk.injEq] at he
    exact ⟨⟨a, ha, he.1⟩, ⟨b, hb, he.2⟩⟩

/-- The family of distances of image pairs is `r ×` the family of the transported field. -/
theorem image_lfppDistOn_sim (hr : 0 < r) (V A B : Set (Rd d)) :
    (fun p : Rd d × Rd d =>
        lfppDistOn ξ φ ((fun z => x₀ + r • O z) '' V) p.1 p.2) ''
      (((fun z => x₀ + r • O z) '' A) ×ˢ ((fun z => x₀ + r • O z) '' B)) =
      r • ((fun p : Rd d × Rd d =>
        lfppDistOn ξ (fun z => φ (x₀ + r • O z)) V p.1 p.2) '' (A ×ˢ B)) := by
  rw [image_prod_sim, image_image, ← image_smul, image_image]
  refine image_congr fun p _ => ?_
  rw [smul_eq_mul]
  exact lfppDistOn_sim_image O x₀ hr ξ φ V p.1 p.2

/-- **Similarity covariance of set distances**: for `T z = x₀ + r • O z`,
`D(T A, T B; T V)(φ) = r · D(A, B; V)(φ ∘ T)`. -/
theorem lfppSetDist_sim (hr : 0 < r) (V A B : Set (Rd d)) :
    lfppSetDist ξ φ ((fun z => x₀ + r • O z) '' V) ((fun z => x₀ + r • O z) '' A)
        ((fun z => x₀ + r • O z) '' B) =
      r * lfppSetDist ξ (fun z => φ (x₀ + r • O z)) V A B := by
  unfold lfppSetDist
  rw [image_lfppDistOn_sim O x₀ ξ φ hr, Real.sInf_smul_of_nonneg hr.le, smul_eq_mul]

/-- **Similarity covariance of internal diameters**: `Diam(T U; T V)(φ) = r · Diam(U; V)(φ ∘ T)`. -/
theorem lfppDiam_sim (hr : 0 < r) (U V : Set (Rd d)) :
    lfppDiam ξ φ ((fun z => x₀ + r • O z) '' U) ((fun z => x₀ + r • O z) '' V) =
      r * lfppDiam ξ (fun z => φ (x₀ + r • O z)) U V := by
  unfold lfppDiam
  rw [image_lfppDistOn_sim O x₀ ξ φ hr, Real.sSup_smul_of_nonneg hr.le, smul_eq_mul]

/-- **Similarity covariance of the whole-space metric**:
`D^ξ(φ)(T x, T y) = r · D^ξ(φ ∘ T)(x, y)`. -/
theorem lfppMetric_sim (hr : 0 < r) (x y : Rd d) :
    lfppMetric ξ φ (x₀ + r • O x) (x₀ + r • O y) =
      r * lfppMetric ξ (fun z => φ (x₀ + r • O z)) x y := by
  unfold lfppMetric
  rw [lfppDistOn_sim O x₀ hr ξ φ univ x y, preimage_univ]

theorem image_univ_sim (hr : 0 < r) : (fun z => x₀ + r • O z) '' univ = univ := by
  refine eq_univ_of_forall fun w => ⟨O.symm (r⁻¹ • (w - x₀)), mem_univ _, ?_⟩
  simp only [LinearIsometryEquiv.apply_symm_apply]
  exact smul_add_inv x₀ w hr

theorem norm_sim_sub_sim (hr : 0 < r) (z c : Rd d) :
    ‖x₀ + r • O z - (x₀ + r • O c)‖ = r * ‖z - c‖ := by
  rw [add_sub_add_left_eq_sub, ← smul_sub, ← map_sub, norm_smul, LinearIsometryEquiv.norm_map,
    Real.norm_eq_abs, abs_of_pos hr]

/-- The inverse point `O⁻¹ (r⁻¹ (w - x₀))` of a similarity. -/
theorem sim_symm_apply (hr : 0 < r) (w : Rd d) : x₀ + r • O (O.symm (r⁻¹ • (w - x₀))) = w := by
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact smul_add_inv x₀ w hr

/-- Images of Euclidean spheres under a similarity (MA7 D-ADP). -/
theorem image_sphere_sim (hr : 0 < r) (c : Rd d) (ρ : ℝ) :
    (fun z => x₀ + r • O z) '' Metric.sphere c ρ = Metric.sphere (x₀ + r • O c) (r * ρ) := by
  ext w
  simp only [mem_image, mem_sphere_iff_norm]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [norm_sim_sub_sim O x₀ hr, hz]
  · intro hw
    refine ⟨O.symm (r⁻¹ • (w - x₀)), ?_, sim_symm_apply O x₀ hr w⟩
    rw [← sim_symm_apply O x₀ hr w, norm_sim_sub_sim O x₀ hr] at hw
    exact mul_left_cancel₀ hr.ne' hw

/-- Images of Euclidean open balls under a similarity. -/
theorem image_ball_sim (hr : 0 < r) (c : Rd d) (ρ : ℝ) :
    (fun z => x₀ + r • O z) '' Metric.ball c ρ = Metric.ball (x₀ + r • O c) (r * ρ) := by
  ext w
  simp only [mem_image, mem_ball_iff_norm]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [norm_sim_sub_sim O x₀ hr]
    exact mul_lt_mul_of_pos_left hz hr
  · intro hw
    refine ⟨O.symm (r⁻¹ • (w - x₀)), ?_, sim_symm_apply O x₀ hr w⟩
    rw [← sim_symm_apply O x₀ hr w, norm_sim_sub_sim O x₀ hr] at hw
    exact lt_of_mul_lt_mul_left hw hr.le

/-- Images of Euclidean closed balls under a similarity. -/
theorem image_closedBall_sim (hr : 0 < r) (c : Rd d) (ρ : ℝ) :
    (fun z => x₀ + r • O z) '' Metric.closedBall c ρ =
      Metric.closedBall (x₀ + r • O c) (r * ρ) := by
  ext w
  simp only [mem_image, mem_closedBall_iff_norm]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [norm_sim_sub_sim O x₀ hr]
    exact mul_le_mul_of_nonneg_left hz hr.le
  · intro hw
    refine ⟨O.symm (r⁻¹ • (w - x₀)), ?_, sim_symm_apply O x₀ hr w⟩
    rw [← sim_symm_apply O x₀ hr w, norm_sim_sub_sim O x₀ hr] at hw
    exact le_of_mul_le_mul_left hw hr

/-- **Similarity covariance of the Euclidean sphere-to-sphere distance** (MA7 D-ADP):
`D(∂B(T c, r r₂), ∂B(T c, r r₁))(φ) = r · D(∂B(c, r₂), ∂B(c, r₁))(φ ∘ T)`. -/
theorem lfppSetDist_sphere_sim (hr : 0 < r) (c : Rd d) (r₁ r₂ : ℝ) :
    lfppSetDist ξ φ univ (Metric.sphere (x₀ + r • O c) (r * r₂))
        (Metric.sphere (x₀ + r • O c) (r * r₁)) =
      r * lfppSetDist ξ (fun z => φ (x₀ + r • O z)) univ (Metric.sphere c r₂)
        (Metric.sphere c r₁) := by
  have h := lfppSetDist_sim O x₀ ξ φ hr univ (Metric.sphere c r₂) (Metric.sphere c r₁)
  rw [image_univ_sim O x₀ hr, image_sphere_sim O x₀ hr, image_sphere_sim O x₀ hr] at h
  exact h

/-- **Scaling–translation covariance of the across distance**: for `T z = x₀ + r • z`,
`D(across B_{r r₁}(T c) \ B_{r r₂}(T c))(φ) = r · D(across B_{r₁}(c) \ B_{r₂}(c))(φ ∘ T)`. -/
theorem acrossDist_smul_add (hr : 0 < r) (c : Rd d) (r₁ r₂ : ℝ) :
    acrossDist ξ φ (x₀ + r • c) (r * r₁) (r * r₂) =
      r * acrossDist ξ (fun z => φ (x₀ + r • z)) c r₁ r₂ := by
  have h := lfppSetDist_sim (LinearIsometryEquiv.refl ℝ (Rd d)) x₀ ξ φ hr univ (lsph c r₂)
    (lsph c r₁)
  simp only [LinearIsometryEquiv.coe_refl, id] at h
  rw [image_univ_smul_add x₀ hr, image_lsph_smul_add x₀ c hr, image_lsph_smul_add x₀ c hr] at h
  exact h

/-- **Scaling–translation covariance of the self-internal diameter**: for `T z = x₀ + r • z`,
`selfDiam(φ)(B_{r ρ}(T c)) = r · selfDiam(φ ∘ T)(B_ρ(c))`. -/
theorem selfDiam_smul_add (hr : 0 < r) (c : Rd d) (ρ : ℝ) :
    selfDiam ξ φ (x₀ + r • c) (r * ρ) = r * selfDiam ξ (fun z => φ (x₀ + r • z)) c ρ := by
  have h := lfppDiam_sim (LinearIsometryEquiv.refl ℝ (Rd d)) x₀ ξ φ hr (obox c ρ) (obox c ρ)
  simp only [LinearIsometryEquiv.coe_refl, id] at h
  rw [image_obox_smul_add x₀ c hr] at h
  exact h

end Covariance

/-! ## Covariance of shell crossings and of `AroundGood` (MA7 D-5.3: rescaled certificates) -/

section AroundCov

variable (x₀ : Rd d) {r : ℝ} {ξ : ℝ} {φ : Rd d → ℝ} {c : Rd d} {r₁ r₂ t : ℝ} {B : Set (Rd d)}

theorem smul_inv_smul_add (hr : 0 < r) (z : Rd d) : r⁻¹ • (x₀ + r • z - x₀) = z := by
  rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]

theorem mem_image_smul_add_iff (hr : 0 < r) {S : Set (Rd d)} {w : Rd d} :
    w ∈ (fun z => x₀ + r • z) '' S ↔ r⁻¹ • (w - x₀) ∈ S := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    rwa [smul_inv_smul_add x₀ hr]
  · intro h
    exact ⟨_, h, smul_add_inv x₀ w hr⟩

theorem contDiff_smul_add (r : ℝ) : ContDiff ℝ 1 (fun z : Rd d => x₀ + r • z) :=
  contDiff_const.add (contDiff_id.const_smul r)

theorem contDiff_smul_add_inv (r : ℝ) : ContDiff ℝ 1 (fun w : Rd d => r⁻¹ • (w - x₀)) :=
  (contDiff_id.sub contDiff_const).const_smul r⁻¹

/-- Pulling a shell crossing back by `z ↦ x₀ + r z`. -/
theorem IsShellCrossing.comp_smul_add_inv (hr : 0 < r) {γ : ℝ → Rd d}
    (h : IsShellCrossing (x₀ + r • c) (r * r₁) (r * r₂) ((fun z => x₀ + r • z) '' B) γ) :
    IsShellCrossing c r₁ r₂ B (fun t => r⁻¹ • (γ t - x₀)) where
  pcw := IsPcwC1Path.comp_contDiff (T := fun w => r⁻¹ • (w - x₀)) (contDiff_smul_add_inv x₀ r)
    h.pcw
  start := by
    have h0 := h.start
    rw [← image_lsph_smul_add x₀ c hr, mem_image_smul_add_iff x₀ hr] at h0
    exact h0
  stop := by
    have h1 := h.stop
    rw [← image_lsph_smul_add x₀ c hr, mem_image_smul_add_iff x₀ hr] at h1
    exact h1
  inShell := fun _ ht => by
    have h' := h.inShell ht
    rw [← image_shell_smul_add x₀ c hr, mem_image_smul_add_iff x₀ hr] at h'
    exact h'
  inB := fun _ ht => (mem_image_smul_add_iff x₀ hr).1 (h.inB ht)

/-- **Covariance of `AroundGood`** (MA7 D-5.3: the certificate of D-4.9, proved for a rescaled
field, transfers to the scaled shell): if `AroundGood` holds for `φ ∘ T` (`T z = x₀ + r z`,
`r > 0`) at `(c, r₁, r₂, B, t)`, then it holds for `φ` at `(T c, r r₁, r r₂, T B, r t)`. -/
theorem AroundGood.smul_add (hr : 0 < r)
    (h : AroundGood ξ (fun z => φ (x₀ + r • z)) c r₁ r₂ B t) :
    AroundGood ξ φ (x₀ + r • c) (r * r₁) (r * r₂) ((fun z => x₀ + r • z) '' B) (r * t) := by
  intro γ₁ γ₂ h₁ h₂
  obtain ⟨s₁, hs₁, s₂, hs₂, hj, hle⟩ :=
    h _ _ (h₁.comp_smul_add_inv x₀ hr) (h₂.comp_smul_add_inv x₀ hr)
  have hR : (fun z => x₀ + r • z) '' ((cbox c r₁ \ obox c r₂) ∩ B) =
      (cbox (x₀ + r • c) (r * r₁) \ obox (x₀ + r • c) (r * r₂)) ∩ (fun z => x₀ + r • z) '' B := by
    rw [image_inter (injective_smul_add x₀ hr), image_shell_smul_add x₀ c hr]
  have e₁ : x₀ + r • (r⁻¹ • (γ₁ s₁ - x₀)) = γ₁ s₁ := smul_add_inv x₀ (γ₁ s₁) hr
  have e₂ : x₀ + r • (r⁻¹ • (γ₂ s₂ - x₀)) = γ₂ s₂ := smul_add_inv x₀ (γ₂ s₂) hr
  refine ⟨s₁, hs₁, s₂, hs₂, ?_, ?_⟩
  · obtain ⟨γ, hγ, hγR⟩ := hj
    refine ⟨fun u => x₀ + r • γ u, ?_, fun u hu => ?_⟩
    · have hp := hγ.comp_contDiff (contDiff_smul_add x₀ r)
      rw [e₁, e₂] at hp
      exact hp
    · rw [← hR]
      exact ⟨γ u, hγR hu, rfl⟩
  · have e := lfppDistOn_sim_image (LinearIsometryEquiv.refl ℝ (Rd d)) x₀ hr ξ φ
      ((cbox c r₁ \ obox c r₂) ∩ B) (r⁻¹ • (γ₁ s₁ - x₀)) (r⁻¹ • (γ₂ s₂ - x₀))
    simp only [LinearIsometryEquiv.coe_refl, id] at e
    rw [e₁, e₂, hR] at e
    rw [e]
    exact mul_le_mul_of_nonneg_left hle hr.le

/-- **Covariance of `AroundGood`, converse direction**: if `AroundGood` holds for `φ` at
`(T c, r r₁, r r₂, T B, t)`, then it holds for `φ ∘ T` at `(c, r₁, r₂, B, r⁻¹ t)`. -/
theorem AroundGood.of_smul_add (hr : 0 < r)
    (h : AroundGood ξ φ (x₀ + r • c) (r * r₁) (r * r₂) ((fun z => x₀ + r • z) '' B) t) :
    AroundGood ξ (fun z => φ (x₀ + r • z)) c r₁ r₂ B (r⁻¹ * t) := by
  have hr' : 0 < r⁻¹ := inv_pos.2 hr
  have hcomp : ∀ z : Rd d, x₀ + r • (-(r⁻¹ • x₀) + r⁻¹ • z) = z := fun z => by
    rw [_root_.smul_add, smul_neg, smul_smul, smul_smul, mul_inv_cancel₀ hr.ne', one_smul, one_smul,
      add_neg_cancel_left]
  have hφ : (fun z => (fun z => φ (x₀ + r • z)) (-(r⁻¹ • x₀) + r⁻¹ • z)) = φ := by
    funext z
    simp only [hcomp]
  have h' := AroundGood.smul_add (-(r⁻¹ • x₀)) hr' (ξ := ξ) (φ := fun z => φ (x₀ + r • z))
    (c := x₀ + r • c) (r₁ := r * r₁) (r₂ := r * r₂) (B := (fun z => x₀ + r • z) '' B) (t := t)
    (by rw [hφ]; exact h)
  have hc : -(r⁻¹ • x₀) + r⁻¹ • (x₀ + r • c) = c := by
    rw [_root_.smul_add, smul_smul, inv_mul_cancel₀ hr.ne', one_smul, neg_add_cancel_left]
  have h1 : r⁻¹ * (r * r₁) = r₁ := by rw [← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul]
  have h2 : r⁻¹ * (r * r₂) = r₂ := by rw [← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul]
  have hB : (fun z => -(r⁻¹ • x₀) + r⁻¹ • z) '' ((fun z => x₀ + r • z) '' B) = B := by
    rw [image_image]
    have hid : (fun z => -(r⁻¹ • x₀) + r⁻¹ • (x₀ + r • z)) = id := by
      funext z
      rw [_root_.smul_add, smul_smul, inv_mul_cancel₀ hr.ne', one_smul, neg_add_cancel_left, id]
    rw [hid, image_id]
  rw [hc, h1, h2, hB] at h'
  exact h'

end AroundCov

/-! ## Laws -/

section Laws

variable {κ : Rd d → ℝ} {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  {P : Measure Ω} {P' : Measure Ω'} {W : WN d → Ω → ℝ} {W' : WN d → Ω' → ℝ}
  {a b r : ℝ} {H : Rd d → Ω → ℝ} {H' : Rd d → Ω' → ℝ}

/-- **Similarity law of set distances** (DGZ Lemma 2.5 for set distances): for
`T z = x₀ + r • O z`, an open preconnected `V ⊇ A ∪ B`, a version `H` of `H_{a,b}` and a version
`H'` of `H_{a/r,b/r}` over any white noise (`0 < a`), `D(T A, T B; T V)(H)` has the law of
`r · D(A, B; V)(H')`. -/
theorem map_lfppSetDist_sim_eq (hH : IsBandVersion P W κ a b H)
    (hH' : IsBandVersion P' W' κ (a / r) (b / r) H') (hW : IsWhiteNoise P W)
    (hW' : IsWhiteNoise P' W') (hκ : IsLFPPKernel κ) (O : Rd d ≃ₗᵢ[ℝ] Rd d) (x₀ : Rd d)
    (hr : 0 < r) (ha : 0 < a) (ξ : ℝ) {V A B : Set (Rd d)} (hV : IsOpen V)
    (hVc : IsPreconnected V) (hA : A ⊆ V) (hB : B ⊆ V) :
    P.map (fun ω => lfppSetDist ξ (fun z => H z ω) ((fun z => x₀ + r • O z) '' V)
        ((fun z => x₀ + r • O z) '' A) ((fun z => x₀ + r • O z) '' B)) =
      P'.map (fun ω => r * lfppSetDist ξ (fun z => H' z ω) V A B) := by
  have h := hH.map_comp_sim_eq_of_measurable hH' hW hW' hκ O x₀ hr ha
    (G := fun f => r * lfppSetDist ξ f V A B)
    ((measurable_lfppSetDist_continuousMap hV hVc hA hB ξ).const_mul r)
  refine Eq.trans ?_ h
  congr 1
  funext ω
  exact lfppSetDist_sim O x₀ ξ (fun z => H z ω) hr V A B

/-- **Similarity law of internal diameters**: for `T z = x₀ + r • O z`, an open preconnected
`V ⊇ U`, `Diam(T U; T V)(H)` has the law of `r · Diam(U; V)(H')`. -/
theorem map_lfppDiam_sim_eq (hH : IsBandVersion P W κ a b H)
    (hH' : IsBandVersion P' W' κ (a / r) (b / r) H') (hW : IsWhiteNoise P W)
    (hW' : IsWhiteNoise P' W') (hκ : IsLFPPKernel κ) (O : Rd d ≃ₗᵢ[ℝ] Rd d) (x₀ : Rd d)
    (hr : 0 < r) (ha : 0 < a) (ξ : ℝ) {U V : Set (Rd d)} (hV : IsOpen V)
    (hVc : IsPreconnected V) (hU : U ⊆ V) :
    P.map (fun ω => lfppDiam ξ (fun z => H z ω) ((fun z => x₀ + r • O z) '' U)
        ((fun z => x₀ + r • O z) '' V)) =
      P'.map (fun ω => r * lfppDiam ξ (fun z => H' z ω) U V) := by
  have h := hH.map_comp_sim_eq_of_measurable hH' hW hW' hκ O x₀ hr ha
    (G := fun f => r * lfppDiam ξ f U V)
    ((measurable_lfppDiam_continuousMap hV hVc hU ξ).const_mul r)
  refine Eq.trans ?_ h
  congr 1
  funext ω
  exact lfppDiam_sim O x₀ ξ (fun z => H z ω) hr U V

/-- **Similarity law of the whole-space metric**, jointly in the pair of points: for
`T z = x₀ + r • O z`, `(D^ξ(H)(T x, T y))_{x,y}` has the law of `(r · D^ξ(H')(x, y))_{x,y}`. -/
theorem map_lfppMetric_sim_eq (hH : IsBandVersion P W κ a b H)
    (hH' : IsBandVersion P' W' κ (a / r) (b / r) H') (hW : IsWhiteNoise P W)
    (hW' : IsWhiteNoise P' W') (hκ : IsLFPPKernel κ) (O : Rd d ≃ₗᵢ[ℝ] Rd d) (x₀ : Rd d)
    (hr : 0 < r) (ha : 0 < a) (ξ : ℝ) :
    P.map (fun ω (q : Rd d × Rd d) =>
        lfppMetric ξ (fun z => H z ω) (x₀ + r • O q.1) (x₀ + r • O q.2)) =
      P'.map (fun ω (q : Rd d × Rd d) => r * lfppMetric ξ (fun z => H' z ω) q.1 q.2) := by
  have h := hH.map_lfppDistOn_sim_eq hH' hW hW' hκ O x₀ hr ha ξ isOpen_univ
  rw [image_univ_sim O x₀ hr] at h
  exact h

/-- **Similarity law of the across distance** (MA7 D-4.10, D-5.5): for `T z = x₀ + r • z`, a
version `H` of `H_{a,b}` and a version `H'` of `H_{a/r,b/r}` over any white noise (`0 < a`),
`D(across B_{r r₁}(T c) \ B_{r r₂}(T c))(H)` has the law of
`r · D(across B_{r₁}(c) \ B_{r₂}(c))(H')`. -/
theorem map_acrossDist_sim_eq (hH : IsBandVersion P W κ a b H)
    (hH' : IsBandVersion P' W' κ (a / r) (b / r) H') (hW : IsWhiteNoise P W)
    (hW' : IsWhiteNoise P' W') (hκ : IsLFPPKernel κ) (x₀ : Rd d) (hr : 0 < r) (ha : 0 < a)
    (ξ : ℝ) (c : Rd d) (r₁ r₂ : ℝ) :
    P.map (fun ω => acrossDist ξ (fun z => H z ω) (x₀ + r • c) (r * r₁) (r * r₂)) =
      P'.map (fun ω => r * acrossDist ξ (fun z => H' z ω) c r₁ r₂) := by
  have h := hH.map_comp_sim_eq_of_measurable hH' hW hW' hκ (LinearIsometryEquiv.refl ℝ (Rd d))
    x₀ hr ha (G := fun f => r * acrossDist ξ f c r₁ r₂)
    ((measurable_acrossDist_continuousMap ξ c r₁ r₂).const_mul r)
  simp only [LinearIsometryEquiv.coe_refl, id] at h
  refine Eq.trans ?_ h
  congr 1
  funext ω
  exact acrossDist_smul_add x₀ ξ (fun z => H z ω) hr c r₁ r₂

/-- **Similarity law of the self-internal diameter** (MA7 D-4.8, D-4.9): for `T z = x₀ + r • z`,
`selfDiam(H)(B_{r ρ}(T c))` has the law of `r · selfDiam(H')(B_ρ(c))`. -/
theorem map_selfDiam_sim_eq (hH : IsBandVersion P W κ a b H)
    (hH' : IsBandVersion P' W' κ (a / r) (b / r) H') (hW : IsWhiteNoise P W)
    (hW' : IsWhiteNoise P' W') (hκ : IsLFPPKernel κ) (x₀ : Rd d) (hr : 0 < r) (ha : 0 < a)
    (ξ : ℝ) (c : Rd d) (ρ : ℝ) :
    P.map (fun ω => selfDiam ξ (fun z => H z ω) (x₀ + r • c) (r * ρ)) =
      P'.map (fun ω => r * selfDiam ξ (fun z => H' z ω) c ρ) := by
  have h := hH.map_comp_sim_eq_of_measurable hH' hW hW' hκ (LinearIsometryEquiv.refl ℝ (Rd d))
    x₀ hr ha (G := fun f => r * selfDiam ξ f c ρ)
    ((measurable_selfDiam_continuousMap ξ c ρ).const_mul r)
  simp only [LinearIsometryEquiv.coe_refl, id] at h
  refine Eq.trans ?_ h
  congr 1
  funext ω
  exact selfDiam_smul_add x₀ ξ (fun z => H z ω) hr c ρ

/-- **Translation invariance of the across distance** (same band, any two white noises). -/
theorem map_acrossDist_translate_eq (hH : IsBandVersion P W κ a b H)
    (hH' : IsBandVersion P' W' κ a b H') (hW : IsWhiteNoise P W) (hW' : IsWhiteNoise P' W')
    (hκ : IsLFPPKernel κ) (ha : 0 < a) (ξ : ℝ) (x₀ c : Rd d) (r₁ r₂ : ℝ) :
    P.map (fun ω => acrossDist ξ (fun z => H z ω) (x₀ + c) r₁ r₂) =
      P'.map (fun ω => acrossDist ξ (fun z => H' z ω) c r₁ r₂) := by
  have h := map_acrossDist_sim_eq hH (hH'.congr_band (div_one a).symm (div_one b).symm) hW hW'
    hκ x₀ one_pos ha ξ c r₁ r₂
  simp only [one_smul, one_mul] at h
  exact h

/-- **Translation invariance of the self-internal diameter** (same band, any two white noises). -/
theorem map_selfDiam_translate_eq (hH : IsBandVersion P W κ a b H)
    (hH' : IsBandVersion P' W' κ a b H') (hW : IsWhiteNoise P W) (hW' : IsWhiteNoise P' W')
    (hκ : IsLFPPKernel κ) (ha : 0 < a) (ξ : ℝ) (x₀ c : Rd d) (ρ : ℝ) :
    P.map (fun ω => selfDiam ξ (fun z => H z ω) (x₀ + c) ρ) =
      P'.map (fun ω => selfDiam ξ (fun z => H' z ω) c ρ) := by
  have h := map_selfDiam_sim_eq hH (hH'.congr_band (div_one a).symm (div_one b).symm) hW hW'
    hκ x₀ one_pos ha ξ c ρ
  simp only [one_smul, one_mul] at h
  exact h

end Laws

end HigherDimLQGMetric.DGZ
