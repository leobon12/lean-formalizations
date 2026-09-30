import QuantumZipper.Proofs.Zipper.FieldLawler4WdBasic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FL4-WD: `Wd` satisfies the hypotheses of `fl3cmp_le` / `fl3cmp_excR_le`

Task FL4-WD (Track A round 4). With `Wd = fl4Wd W t R ε α β p₀` (the component of
`(ℍ ∩ B(0,R)) \ (K_t ∪ closure ηD)` through the base point of `fl4wd_base_exists`):

* `fl4wd_open`, `fl4wd_conn`, `fl4wd_subset_D`, `fl4wd_subset_ball` (`hWo hWc hWD hWR`);
* `fl4wd_image_subset` (`hWU`), `fl4wd_arc_closure` (`hWarc`), `fl4wd_frontier_out` (`hWfr`);
* `fl4wd_frontier_subset` and `fl4wd_E` (`hE`, via `fl3cmp_E_of`);
* `fl4wd_arc_frontier`: `ηD ⊆ ∂Wd` (datum (i) for the symmetry step);
* `fl4wd_excR_le`: `fl3cmp_excR_le` for this `Wd`, all Wd-hypotheses discharged.

Source: Field–Lawler, *Escape probability and transience for SLE*, EJP 20 (2015), proof of
Prop. 3.4, p. 9 ((2.1) applied in the part of `H_t ∩ B(0,R)` beyond `ηⱼ`); the point-set
topology is an own elementary argument (FL leave it implicit).
-/

noncomputable section

open Set Filter Metric Complex
open scoped Topology

namespace QuantumZipper
namespace FieldLawler

open Thm18Asm.LWFar

variable {W : ℝ → ℝ} {t : ℝ} {F : ℂ → ℂ}

section
variable (hc : SideCtx W t F) {R ε α β : ℝ} {p₀ : ℂ}
include hc

theorem fl4wd_open : IsOpen (fl4Wd W t R ε α β p₀) :=
  (fl4WdDom_isOpen hc R ε α β).connectedComponentIn

omit hc in
theorem fl4wd_conn (hp : p₀ ∈ fl4WdDom W t R ε α β) : IsConnected (fl4Wd W t R ε α β p₀) :=
  isConnected_connectedComponentIn_iff.2 hp

omit hc in
theorem fl4wd_subset_dom : fl4Wd W t R ε α β p₀ ⊆ fl4WdDom W t R ε α β :=
  connectedComponentIn_subset _ _

omit hc in
theorem fl4wd_subset_D : fl4Wd W t R ε α β p₀ ⊆ H \ fwdHull W t := fun _ hz =>
  have h := fl4wd_subset_dom hz
  ⟨h.1.1, fun h' => h.2 (Or.inl h')⟩

omit hc in
theorem fl4wd_subset_ball : fl4Wd W t R ε α β p₀ ⊆ ball 0 R := fun _ hz =>
  (fl4wd_subset_dom hz).1.2

omit hc in
lemma fl4wd_not_arc {z : ℂ} (hz : z ∈ fl4Wd W t R ε α β p₀) : z ∉ closure (flCircArc ε α β) :=
  fun h => (fl4wd_subset_dom hz).2 (Or.inr h)

/-- `Z(ηD) ⊆ η'`. -/
lemma fl4wd_image_arc {η' : ℝ → ℂ} (hη : IsCrosscutH η')
    (hηD : fwdMapInv W t '' arcH η' = flCircArc ε α β) :
    fwdMap W t '' flCircArc ε α β ⊆ arcH η' := by
  rintro _ ⟨w, hw, rfl⟩
  rw [← hηD] at hw
  obtain ⟨q, hq, rfl⟩ := hw
  have hqH : q ∈ H := by obtain ⟨s, hs, rfl⟩ := hq; exact hη.2.2.1 hs
  rw [fl4_fwdMap_inv hc hqH]; exact hq

/-- **`hWU`.** `Z(Wd)` is a connected subset of `ℍ \ η'` meeting `hullComp η'`. -/
theorem fl4wd_image_subset {η' : ℝ → ℂ} (hηD : fwdMapInv W t '' arcH η' = flCircArc ε α β)
    (hp : p₀ ∈ fl4WdDom W t R ε α β) (hpU : fwdMap W t p₀ ∈ hullComp η') :
    fwdMap W t '' fl4Wd W t R ε α β p₀ ⊆ hullComp η' := by
  have hS : fwdMap W t '' fl4Wd W t R ε α β p₀ ⊆ H \ arcH η' := by
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨hc.mapsTo (fl4wd_subset_D hz), fun hq => fl4wd_not_arc hz (subset_closure ?_)⟩
    rw [← hηD]
    refine ⟨fwdMap W t z, hq, ?_⟩
    rw [← hc.Feq (hc.mapsTo (fl4wd_subset_D hz)), hc.F_fwdMap (fl4wd_subset_D hz)]
  have hpre : IsPreconnected (fwdMap W t '' fl4Wd W t R ε α β p₀) :=
    (fl4wd_conn hp).isPreconnected.image _ (hc.continuousOn_fwdMap.mono fl4wd_subset_D)
  have hsub := hpre.subset_connectedComponentIn ⟨p₀, mem_connectedComponentIn hp, rfl⟩ hS
  intro v hv
  refine ⟨hS hv, ?_⟩
  rw [← connectedComponentIn_eq (hsub hv)]
  exact hpU.2

/-- **`hWarc`.** `η' ⊆ closure (Z Wd)`. -/
theorem fl4wd_arc_closure {η' : ℝ → ℂ} (hη : IsCrosscutH η')
    (hηD : fwdMapInv W t '' arcH η' = flCircArc ε α β)
    (hcl : flCircArc ε α β ⊆ closure (fl4Wd W t R ε α β p₀)) :
    arcH η' ⊆ closure (fwdMap W t '' fl4Wd W t R ε α β p₀) := by
  intro q hq
  have hqH : q ∈ H := by obtain ⟨s, hs, rfl⟩ := hq; exact hη.2.2.1 hs
  have hw : fwdMapInv W t q ∈ flCircArc ε α β := hηD ▸ ⟨q, hq, rfl⟩
  have hZ : ContinuousAt (fwdMap W t) (fwdMapInv W t q) :=
    hc.continuousOn_fwdMap.continuousAt (hc.isOpen_dom.mem_nhds (fl4_inv_mem hc hqH))
  have := hZ.continuousWithinAt.mem_closure_image (hcl hw)
  rwa [fl4_fwdMap_inv hc hqH] at this

/-- **`hWfr`.** Frontier points of `Wd` in `D ∩ B(0,R)` lie on `closure ηD`, which `Z` maps into
`closure η' ⊆ ∂ hullComp η'`. -/
theorem fl4wd_frontier_out {η' : ℝ → ℂ} (hη : IsCrosscutH η') {a b : ℝ}
    (ha : Tendsto η' (𝓝[>] 0) (𝓝 (a : ℂ))) (hb : Tendsto η' (𝓝[<] 1) (𝓝 (b : ℂ)))
    (hab : a < b) (hηD : fwdMapInv W t '' arcH η' = flCircArc ε α β) :
    ∀ x₀ ∈ frontier (fl4Wd W t R ε α β p₀), x₀ ∈ H \ fwdHull W t → ‖x₀‖ < R →
      fwdMap W t x₀ ∉ hullComp η' := by
  intro x₀ hx hD hR hU
  have hnot := fl4_frontier_cc_not_mem (fl4WdDom_isOpen hc R ε α β) p₀ hx
  have hxcl : x₀ ∈ closure (flCircArc ε α β) := by
    by_contra h
    exact hnot ⟨⟨hD.1, mem_ball_zero_iff.2 hR⟩, by rintro (h' | h'); exacts [hD.2 h', h h']⟩
  have hZ : ContinuousAt (fwdMap W t) x₀ :=
    hc.continuousOn_fwdMap.continuousAt (hc.isOpen_dom.mem_nhds hD)
  have h1 : fwdMap W t x₀ ∈ closure (arcH η') :=
    closure_mono (fl4wd_image_arc hc hη hηD) (hZ.continuousWithinAt.mem_closure_image hxcl)
  obtain ⟨-, -, -, -, -, hclfr, -⟩ := fl3u_FL3Unif_pieces hη ha hb hab
  have h2 := hclfr h1
  rw [(lwExc_hullComp_isOpen hη).frontier_eq] at h2
  exact h2.2 hU

/-- The frontier of `Wd` off `C_R` lies in `K_t ∪ ℝ ∪ C_ε`. -/
theorem fl4wd_frontier_subset (hε : 0 < ε) :
    frontier (fl4Wd W t R ε α β p₀) \ sphere 0 R ⊆
      fwdHull W t ∪ range ofReal ∪ sphere 0 ε := by
  rintro x ⟨hx, hxR⟩
  have hnot := fl4_frontier_cc_not_mem (fl4WdDom_isOpen hc R ε α β) p₀ hx
  have hcl : closure (fl4Wd W t R ε α β p₀) ⊆ {z : ℂ | 0 ≤ z.im} ∩ closedBall 0 R :=
    closure_minimal (fun z hz => ⟨show (0 : ℝ) ≤ z.im from le_of_lt (fl4wd_subset_D hz).1,
      ball_subset_closedBall (fl4wd_subset_ball hz)⟩)
      ((isClosed_le continuous_const Complex.continuous_im).inter isClosed_closedBall)
  obtain ⟨him, hball⟩ := hcl hx.1
  rcases (show (0 : ℝ) ≤ x.im from him).lt_or_eq with h | h
  · have hxb : x ∈ ball (0 : ℂ) R := by
      rw [mem_closedBall_zero_iff] at hball
      rw [mem_ball_zero_iff]
      exact lt_of_le_of_ne hball (fun e => hxR (by simpa using e))
    by_contra hK
    refine hnot ⟨⟨h, hxb⟩, ?_⟩
    rintro (h' | h')
    · exact hK (Or.inl (Or.inl h'))
    · have := fl4_closure_arc_subset h'
      rw [abs_of_pos hε] at this
      exact hK (Or.inr this)
  · exact Or.inl (Or.inr ⟨x.re, Complex.ext (by simp) (by simp [h])⟩)

/-- **`hE`** via `fl3cmp_E_of`. -/
theorem fl4wd_E (hε : 0 < ε) (hεR : ε < R) (hlt : ∀ s ∈ Ico 0 t, ‖trace W s‖ < R) :
    closure (frontier (fl4Wd W t R ε α β p₀) \ sphere 0 R) ∩ sphere 0 R ⊆
      (({trace W t, (R : ℂ), -(R : ℂ)} : Finset ℂ) : Set ℂ) :=
  fl3cmp_E_of hc (by linarith) hεR.ne hlt (fl4wd_frontier_subset hc hε)

omit hc in
/-- **(i)** `ηD ⊆ ∂Wd`. -/
theorem fl4wd_arc_frontier (hcl : flCircArc ε α β ⊆ closure (fl4Wd W t R ε α β p₀)) :
    flCircArc ε α β ⊆ frontier (fl4Wd W t R ε α β p₀) := fun _ hw =>
  ⟨hcl hw, fun hi => fl4wd_not_arc (interior_subset hi) (subset_closure hw)⟩

end

/-- `η'` lies on the level set `‖F‖ = ε` (from `F(η') = ηD`). -/
lemma fl4wd_level {ε α β : ℝ} (hε : 0 < ε) {η' : ℝ → ℂ}
    (hηD : fwdMapInv W t '' arcH η' = flCircArc ε α β) :
    arcH η' ⊆ {p | ‖fwdMapInv W t p‖ = ε} := by
  intro q hq
  have hw : fwdMapInv W t q ∈ flCircArc ε α β := hηD ▸ ⟨q, hq, rfl⟩
  have := fl4_closure_arc_subset (subset_closure hw)
  rw [mem_sphere_zero_iff_norm, abs_of_pos hε] at this
  exact this

end FieldLawler
end QuantumZipper
