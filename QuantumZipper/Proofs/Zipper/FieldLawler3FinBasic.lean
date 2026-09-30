import QuantumZipper.Proofs.Zipper.FieldLawler2Circ

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FL3-FIN (generic part): components of an open set along a circular arc

Task FL3-FIN (Track A, input `hfin` of `flExist_loewner`). In polar coordinates
`exp (ρ + s m + θ' i)` (`m ∈ (0, δ)`, `θ' ∈ (θ - δ, θ + δ)`) the half-box `flFinQ ρ s θ δ` on one
side (`s = ±1`) of the circle `|z| = e^ρ` is preconnected. If an open set `U` contains such a
half-box at every angle `θ` of a preconnected parameter set `T`, then all these half-boxes lie in
one connected component of `U` (`flFin_piece`): nearby half-boxes overlap, and a locally true
relation on a preconnected set is true everywhere (`IsPreconnected.induction₂'`).

Own elementary argument (standard plane topology: an open set bounded by finitely many arcs has
finitely many components; FL p. 9 use this implicitly). No published proof in Lean form was found;
searched mathlib (`connectedComponentIn`, `IsPreconnected.induction₂'`) and the repository.
-/

noncomputable section

open Set Filter Metric Complex
open scoped Topology

namespace QuantumZipper
namespace FieldLawler

/-- The polar half-box `{exp (ρ + s m + θ' i) : m ∈ (0, δ), θ' ∈ (θ - δ, θ + δ)}`. -/
def flFinQ (ρ s θ δ : ℝ) : Set ℂ :=
  (fun q : ℝ × ℝ => exp (((ρ + s * q.1 : ℝ) : ℂ) + (q.2 : ℂ) * I)) ''
    (Ioo 0 δ ×ˢ Ioo (θ - δ) (θ + δ))

lemma flFinQ_preconn (ρ s θ δ : ℝ) : IsPreconnected (flFinQ ρ s θ δ) :=
  (isPreconnected_Ioo.prod isPreconnected_Ioo).image _ (by fun_prop : Continuous
    fun q : ℝ × ℝ => exp (((ρ + s * q.1 : ℝ) : ℂ) + (q.2 : ℂ) * I)).continuousOn

lemma flFinQ_mem {ρ s θ δ m θ' : ℝ} (hm : 0 < m) (hmδ : m < δ) (hθ : θ' ∈ Ioo (θ - δ) (θ + δ)) :
    exp (((ρ + s * m : ℝ) : ℂ) + (θ' : ℂ) * I) ∈ flFinQ ρ s θ δ :=
  ⟨(m, θ'), ⟨⟨hm, hmδ⟩, hθ⟩, rfl⟩

lemma flFin_norm (a b : ℝ) : ‖exp ((a : ℂ) + (b : ℂ) * I)‖ = Real.exp a := by
  rw [Complex.norm_exp]; simp

/-- The components of `U` meeting the half-boxes along the angles `T`. -/
def flFinCs (U : Set ℂ) (ρ s : ℝ) (T : Set ℝ) : Set (Set ℂ) :=
  {c | ∃ θ ∈ T, ∃ δ > 0, flFinQ ρ s θ δ ⊆ U ∧ ∃ z ∈ flFinQ ρ s θ δ, connectedComponentIn U z = c}

lemma flFin_sameComp {U S : Set ℂ} (hS : IsPreconnected S) (hSU : S ⊆ U) {z z' : ℂ}
    (hz : z ∈ S) (hz' : z' ∈ S) : connectedComponentIn U z = connectedComponentIn U z' :=
  connectedComponentIn_eq (hS.subset_connectedComponentIn hz hSU hz')

/-- **All half-boxes along a preconnected set of angles lie in one component.** -/
lemma flFin_piece {U : Set ℂ} {ρ s : ℝ} {T : Set ℝ} (hT : IsPreconnected T)
    (hloc : ∀ θ ∈ T, ∃ δ > 0, flFinQ ρ s θ δ ⊆ U) : (flFinCs U ρ s T).Subsingleton := by
  have hadj : ∀ θ θ' δ₁ : ℝ, 0 < δ₁ → flFinQ ρ s θ δ₁ ⊆ U → θ' ∈ Ioo (θ - δ₁) (θ + δ₁) →
      ∀ δ δ' : ℝ, 0 < δ → 0 < δ' → flFinQ ρ s θ δ ⊆ U → flFinQ ρ s θ' δ' ⊆ U →
      ∀ z ∈ flFinQ ρ s θ δ, ∀ z' ∈ flFinQ ρ s θ' δ',
        connectedComponentIn U z = connectedComponentIn U z' := by
    intro θ θ' δ₁ hδ₁ hQ₁ hθ' δ δ' hδ hδ' hQ hQ' z hz z' hz'
    have hm1 : 0 < min δ δ₁ / 2 := by positivity
    have hm2 : 0 < min δ' δ₁ / 2 := by positivity
    have hθc : ∀ φ d : ℝ, 0 < d → φ ∈ Ioo (φ - d) (φ + d) := fun φ d hd =>
      ⟨by linarith, by linarith⟩
    have e1 := flFin_sameComp (flFinQ_preconn ρ s θ δ) hQ hz
      (flFinQ_mem (s := s) (ρ := ρ) hm1 (by linarith [min_le_left δ δ₁]) (hθc θ δ hδ))
    have e2 := flFin_sameComp (flFinQ_preconn ρ s θ δ₁) hQ₁
      (flFinQ_mem (s := s) (ρ := ρ) hm1 (by linarith [min_le_right δ δ₁]) (hθc θ δ₁ hδ₁))
      (flFinQ_mem (s := s) (ρ := ρ) hm2 (by linarith [min_le_right δ' δ₁]) hθ')
    have e3 := flFin_sameComp (flFinQ_preconn ρ s θ' δ') hQ'
      (flFinQ_mem (s := s) (ρ := ρ) hm2 (by linarith [min_le_left δ' δ₁]) (hθc θ' δ' hδ')) hz'
    exact e1.trans (e2.trans e3)
  let P : ℝ → ℝ → Prop := fun θ θ' => ∀ δ δ' : ℝ, 0 < δ → 0 < δ' → flFinQ ρ s θ δ ⊆ U →
    flFinQ ρ s θ' δ' ⊆ U → ∀ z ∈ flFinQ ρ s θ δ, ∀ z' ∈ flFinQ ρ s θ' δ',
      connectedComponentIn U z = connectedComponentIn U z'
  have key : ∀ θ ∈ T, ∀ θ' ∈ T, P θ θ' := by
    intro θ hθ θ' hθ'
    refine hT.induction₂' P (fun x hx => ?_) (fun x y w _ hy _ hxy hyw => ?_) hθ hθ'
    · obtain ⟨δ₁, hδ₁, hQ₁⟩ := hloc x hx
      filter_upwards [nhdsWithin_le_nhds (Ioo_mem_nhds (by linarith : x - δ₁ < x)
        (by linarith : x < x + δ₁))] with y hy
      exact ⟨hadj x y δ₁ hδ₁ hQ₁ hy, fun δ δ' h1 h2 h3 h4 z hz z' hz' =>
        (hadj x y δ₁ hδ₁ hQ₁ hy δ' δ h2 h1 h4 h3 z' hz' z hz).symm⟩
    · intro δ δ'' h1 h2 h3 h4 a ha b hb
      obtain ⟨δy, hδy, hQy⟩ := hloc y hy
      have hw := flFinQ_mem (ρ := ρ) (s := s) (m := δy / 2) (θ' := y) (by positivity)
        (by linarith) (show y ∈ Ioo (y - δy) (y + δy) from ⟨by linarith, by linarith⟩)
      exact (hxy δ δy h1 hδy h3 hQy a ha _ hw).trans (hyw δy δ'' hδy h2 hQy h4 _ hw b hb)
  rintro c1 ⟨θ1, h1, δ1, hδ1, hQ1, z1, hz1, rfl⟩ c2 ⟨θ2, h2, δ2, hδ2, hQ2, z2, hz2, rfl⟩
  exact key θ1 h1 θ2 h2 δ1 δ2 hδ1 hδ2 hQ1 hQ2 z1 hz1 z2 hz2

/-- A small polar box around `exp (ρ + θ i)` lies in a given open set. -/
lemma flFin_local {O : Set ℂ} (hO : IsOpen O) {ρ θ : ℝ} (hp : exp ((ρ : ℂ) + (θ : ℂ) * I) ∈ O)
    {η : ℝ} (hη : 0 < η) : ∃ δ > 0, δ ≤ η ∧ ∀ x : ℂ, x.re ∈ Ioo (ρ - δ) (ρ + δ) →
      x.im ∈ Ioo (θ - δ) (θ + δ) → exp x ∈ O := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 (hO.preimage continuous_exp) _ hp
  refine ⟨min η (r / 2), by positivity, min_le_left _ _, fun x hre him => hball ?_⟩
  have h1 := min_le_right η (r / 2)
  rw [mem_ball, dist_eq_norm]
  refine lt_of_le_of_lt (Complex.norm_le_abs_re_add_abs_im _) ?_
  have ha : |x.re - ρ| < min η (r / 2) := abs_lt.2 ⟨by linarith [hre.1], by linarith [hre.2]⟩
  have hb : |x.im - θ| < min η (r / 2) := abs_lt.2 ⟨by linarith [him.1], by linarith [him.2]⟩
  have hre' : (x - ((ρ : ℂ) + (θ : ℂ) * I)).re = x.re - ρ := by simp
  have him' : (x - ((ρ : ℂ) + (θ : ℂ) * I)).im = x.im - θ := by simp
  rw [hre', him']
  linarith

/-- A point of a polar box is on one of the two half-boxes or on the circle. -/
lemma flFin_tri {ρ θ δ : ℝ} {x : ℂ} (hre : x.re ∈ Ioo (ρ - δ) (ρ + δ))
    (him : x.im ∈ Ioo (θ - δ) (θ + δ)) :
    exp x ∈ flFinQ ρ (-1) θ δ ∨ exp x ∈ flFinQ ρ 1 θ δ ∨
      exp x = exp ((ρ : ℂ) + (x.im : ℂ) * I) := by
  rcases lt_trichotomy x.re ρ with h | h | h
  · refine Or.inl ⟨(ρ - x.re, x.im), ⟨⟨by linarith, by linarith [hre.1]⟩, him⟩, ?_⟩
    apply congrArg; apply Complex.ext <;> simp
  · refine Or.inr (Or.inr ?_)
    apply congrArg; apply Complex.ext <;> simp [h]
  · refine Or.inr (Or.inl ⟨(x.re - ρ, x.im), ⟨⟨by linarith, by linarith [hre.2]⟩, him⟩, ?_⟩)
    apply congrArg; apply Complex.ext <;> simp

/-- A point in the closure of `C` has points of `C` in every polar box around it. -/
lemma flFin_step {C : Set ℂ} {ρ θ δ : ℝ} (hw : exp ((ρ : ℂ) + (θ : ℂ) * I) ∈ closure C)
    (hδ : 0 < δ) : ∃ x : ℂ, x.re ∈ Ioo (ρ - δ) (ρ + δ) ∧ x.im ∈ Ioo (θ - δ) (θ + δ) ∧
      exp x ∈ C := by
  have hopen : IsOpen {x : ℂ | x.re ∈ Ioo (ρ - δ) (ρ + δ) ∧ x.im ∈ Ioo (θ - δ) (θ + δ)} :=
    (isOpen_Ioo.preimage continuous_re).inter (isOpen_Ioo.preimage continuous_im)
  have hN := (isOpenMap_exp _ hopen).mem_nhds
    (mem_image_of_mem exp (show ((ρ : ℂ) + (θ : ℂ) * I) ∈
      {x : ℂ | x.re ∈ Ioo (ρ - δ) (ρ + δ) ∧ x.im ∈ Ioo (θ - δ) (θ + δ)} by
        simp only [mem_ofPred_eq, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
          mul_one, sub_self, add_zero, add_im, mul_im, zero_add]
        exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩))
  obtain ⟨_, ⟨x, hx, rfl⟩, hC⟩ := mem_closure_iff_nhds.1 hw _ hN
  exact ⟨x, hx.1, hx.2, hC⟩

/-- Points of `closure C` lying in `U` belong to the component `C` of `U`. -/
lemma flFin_closure_mem {U : Set ℂ} {z w : ℂ} (hz : z ∈ U)
    (hw : w ∈ closure (connectedComponentIn U z)) (hwU : w ∈ U) :
    w ∈ connectedComponentIn U z := by
  have hpc : IsPreconnected (insert w (connectedComponentIn U z)) :=
    isPreconnected_connectedComponentIn.subset_closure (subset_insert _ _)
      (insert_subset hw subset_closure)
  exact hpc.subset_connectedComponentIn (mem_insert_of_mem _ (mem_connectedComponentIn hz))
    (insert_subset hwU (connectedComponentIn_subset _ _)) (mem_insert _ _)

end FieldLawler
end QuantumZipper
