/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2LnDatum

/-!
# Pulling the union word datum back through a stage chart (deterministic)

Packet PROVE-SB2-LCMEAN, round 2 (route α). SB2(2)'s explored set is a multi-stage walk `B`; in B's stage-`ℓ` chart
`c` (domain `D = ℍ ∖ fill B_{<ℓ}`) its last piece is a chordal hull and the mirrored configuration gives the union word
datum (`IsRelConfigJKL.hasUnionWordBoundaryOnK`). The P-level engine needs the datum in physical coordinates for
`A₁ = A ∪ fill B_{<ℓ}` and `A₂ = fill B_{≤ℓ,s}`. Here the datum is pulled back through any conformal chart whose
inverse has a continuous, proper boundary map `g` on `ℍ̄` with finite fibres (the S2 data of FIN's assembly):

* `chart_fwd_mem_of_mem_dom`, `image_connectedComponentIn_of_invOn`: components correspond under the chart;
* **`exists_ball_preimage_subset`**: for a continuous proper `g` on `ℍ̄` with a finite fibre over `p`, small balls
  around `p` pull back into small balls around the fibre;
* **`eventually_freeNear_pullback`**: the one-sided `freeNear` condition at a chart landing `p'` gives the one at the
  physical landing `g p'` (a component near `g p'` maps into the ball around `p'` by connectedness, the fibre being
  finite);
* **`hasUnionWordBoundaryOnC_pullback`**: the union word datum pulls back (parametrization `c.2.1 ∘ f`, chart `φ ∘ c.1`,
  lift `L ∘ c.1 + c.2.2`), given the set correspondences, the individual-mean and candidate formulas
  `w + u₀ = (w' + u₀') ∘ c.1 − χ c.2.2`, `v = v' ∘ c.1 − χ c.2.2`.

Deterministic; R48-neutral. Conditional helpers with distinct names.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open QuantumZipper (H Hbar)
open SupercriticalConformalCovariance (IsConformalBijection)

namespace InteractingSLE.Theorem14.SB.Ln

open FinRel (freeNear HasUnionWordBoundaryOnC)

/-! ### Charts and components -/

theorem chart_fwd_mem_of_mem_dom {c : Chart} (hc : c.IsConformal) {y : ℂ} (hy : y ∈ (c.dom : Set ℂ)) :
    c.1 y ∈ H ∧ c.2.1 (c.1 y) = y := by
  rw [hc.coe_dom] at hy
  obtain ⟨w, hw, rfl⟩ := hy
  rw [hc.2.2 w hw]
  exact ⟨hw, rfl⟩

theorem inv_mem_dom {c : Chart} (hc : c.IsConformal) {w : ℂ} (hw : w ∈ H) : c.2.1 w ∈ (c.dom : Set ℂ) := by
  rw [hc.coe_dom]
  exact mem_image_of_mem _ hw

/-- Components correspond under a continuous bijection with continuous inverse. -/
theorem image_connectedComponentIn_of_invOn {f g : ℂ → ℂ} {S T : Set ℂ} (hf : ContinuousOn f S)
    (hg : ContinuousOn g T) (hfS : MapsTo f S T) (hgT : MapsTo g T S) (hgf : ∀ x ∈ S, g (f x) = x)
    (hfg : ∀ y ∈ T, f (g y) = y) {x : ℂ} (hx : x ∈ S) :
    f '' connectedComponentIn S x = connectedComponentIn T (f x) := by
  apply Subset.antisymm
  · exact (isPreconnected_connectedComponentIn.image f
      (hf.mono (connectedComponentIn_subset S x))).subset_connectedComponentIn
      (mem_image_of_mem f (mem_connectedComponentIn hx))
      ((image_mono (connectedComponentIn_subset S x)).trans hfS.image_subset)
  · have h1 : g '' connectedComponentIn T (f x) ⊆ connectedComponentIn S x :=
      (isPreconnected_connectedComponentIn.image g
        (hg.mono (connectedComponentIn_subset T (f x)))).subset_connectedComponentIn
        ⟨f x, mem_connectedComponentIn (hfS hx), hgf x hx⟩
        ((image_mono (connectedComponentIn_subset _ _)).trans hgT.image_subset)
    intro y hy
    exact ⟨g y, h1 (mem_image_of_mem g hy), hfg y (connectedComponentIn_subset _ _ hy)⟩

/-! ### Small physical balls pull back near the fibre -/

theorem mem_Hbar_of_mem_H {z : ℂ} (hz : z ∈ H) : z ∈ Hbar :=
  show (0 : ℝ) ≤ z.im from le_of_lt hz

/-- **Small balls pull back near the fibre**: for `g` continuous and proper on `ℍ̄`, every point of `ℍ̄` whose image
is close enough to `p` lies within `ε` of a point of any set `Φ` containing the fibre over `p`. -/
theorem exists_ball_preimage_subset {g : ℂ → ℂ} (hgc : ContinuousOn g Hbar)
    (hgp : ∀ M : ℝ, ∃ R : ℝ, ∀ z ∈ Hbar, R < ‖z‖ → M < ‖g z‖) {p : ℂ} {Φ : Set ℂ}
    (hΦ : ∀ z ∈ Hbar, g z = p → z ∈ Φ) {ε : ℝ} (hε : 0 < ε) :
    ∃ r > 0, ∀ z ∈ Hbar, g z ∈ ball p r → z ∈ ⋃ q ∈ Φ, ball q ε := by
  obtain ⟨R, hR⟩ := hgp (‖p‖ + 1)
  set V : Set ℂ := ⋃ q ∈ Φ, ball q ε with hV
  have hVo : IsOpen V := isOpen_biUnion fun q _ => isOpen_ball
  have hHbar : IsClosed Hbar := isClosed_le continuous_const Complex.continuous_im
  set Kc : Set ℂ := (Hbar ∩ closedBall 0 R) \ V with hKc
  have hKcc : IsCompact Kc := ((isCompact_closedBall 0 R).inter_left hHbar).diff hVo
  have hfar : ∀ z ∈ Hbar, g z ∈ ball p 1 → z ∈ closedBall (0 : ℂ) R := by
    intro z hz hgz
    rw [mem_closedBall, dist_zero_right]
    by_contra hlt
    have h1 := hR z hz (lt_of_not_ge hlt)
    rw [mem_ball, dist_eq_norm] at hgz
    have h2 : ‖g z‖ ≤ ‖g z - p‖ + ‖p‖ := by
      calc ‖g z‖ = ‖(g z - p) + p‖ := by rw [sub_add_cancel]
        _ ≤ ‖g z - p‖ + ‖p‖ := norm_add_le _ _
    linarith
  rcases Kc.eq_empty_or_nonempty with hemp | hne
  · refine ⟨1, one_pos, fun z hz hgz => ?_⟩
    by_contra hzV
    have hzK : z ∈ Kc := ⟨⟨hz, hfar z hz hgz⟩, hzV⟩
    rw [hemp] at hzK
    exact hzK
  · have hgK : ContinuousOn g Kc := hgc.mono fun z hz => hz.1.1
    have hdK : ContinuousOn (fun z => dist (g z) p) Kc :=
      continuous_dist.comp_continuousOn (hgK.prodMk continuousOn_const)
    obtain ⟨z₀, hz₀, hmin⟩ := hKcc.exists_isMinOn hne hdK
    have hpos : 0 < dist (g z₀) p := by
      rw [dist_pos]
      intro he
      exact hz₀.2 (mem_biUnion (hΦ z₀ hz₀.1.1 he) (mem_ball_self hε))
    refine ⟨min (dist (g z₀) p) 1, lt_min hpos one_pos, fun z hz hgz => ?_⟩
    by_contra hzV
    have hzK : z ∈ Kc := ⟨⟨hz, hfar z hz (ball_subset_ball (min_le_right _ _) hgz)⟩, hzV⟩
    have h1 := isMinOn_iff.1 hmin z hzK
    rw [mem_ball] at hgz
    have h2 := min_le_left (dist (g z₀) p) 1
    linarith

/-- **The one-sided `freeNear` condition pulls back through a chart**: if near the chart landing `p'` the chart
parametrization stays in the `B'`-free components of `(ℍ ∖ A') ∩ B(p', r')`, then the physical one stays in the
`B`-free components of `(ℍ ∖ A) ∩ B(g p', r)` for some `r > 0`. Uses: the domain's complement lies in `A`, `A` and `B`
correspond to `A'` and `B'`, and the fibre of the boundary map over `g p'` is finite. -/
theorem eventually_freeNear_pullback {α : Type*} {l : Filter α} {c : Chart} (hc : c.IsConformal)
    {g : ℂ → ℂ} (hgc : ContinuousOn g Hbar) (hgi : EqOn g c.2.1 H)
    (hgp : ∀ M : ℝ, ∃ R : ℝ, ∀ z ∈ Hbar, R < ‖z‖ → M < ‖g z‖)
    {A A' B B' : Set ℂ} (hD : H \ (c.dom : Set ℂ) ⊆ A) (hA : ∀ w ∈ H, c.2.1 w ∈ A ↔ w ∈ A')
    (hB : ∀ w ∈ H, c.2.1 w ∈ B → w ∈ B')
    {F' : α → ℂ} {p' : ℂ} (hp' : p' ∈ Hbar) (hfin : (g ⁻¹' {g p'} ∩ Hbar).Finite)
    (hF' : Tendsto F' l (𝓝 p')) {r' : ℝ} (hr' : 0 < r') (hfree : ∀ᶠ a in l, F' a ∈ freeNear B' A' p' r') :
    ∃ r > 0, ∀ᶠ a in l, c.2.1 (F' a) ∈ freeNear B A (g p') r := by
  set Φ := g ⁻¹' {g p'} ∩ Hbar with hΦ
  set Φ' := Φ \ {p'} with hΦ'
  have hΦ'c : IsClosed Φ' := (hfin.subset sdiff_subset).isClosed
  have hp'Φ' : p' ∉ Φ' := fun h => h.2 rfl
  obtain ⟨δ, hδ, hδb⟩ := Metric.isOpen_iff.1 hΦ'c.isOpen_compl p' hp'Φ'
  set ε := min r' (δ / 2) with hε
  have hε0 : 0 < ε := lt_min hr' (half_pos hδ)
  obtain ⟨r, hr, hrb⟩ := exists_ball_preimage_subset hgc hgp (p := g p') (Φ := Φ) (fun z hz he => ⟨he, hz⟩) hε0
  refine ⟨r, hr, ?_⟩
  have hHbar_ev : ∀ᶠ a in l, F' a ∈ Hbar := hfree.mono fun a ha => mem_Hbar_of_mem_H ha.1.1.1
  have hgF : Tendsto (fun a => g (F' a)) l (𝓝 (g p')) :=
    (hgc p' hp').tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hF', hHbar_ev⟩)
  filter_upwards [hfree, hF' (ball_mem_nhds p' hε0), hgF (ball_mem_nhds (g p') hr)] with a ha hab hag
  obtain ⟨⟨⟨haH, haA⟩, -⟩, hadisj⟩ := ha
  have hgFa : g (F' a) = c.2.1 (F' a) := hgi haH
  have hzH : c.2.1 (F' a) ∈ H := hc.2.1 haH
  have hzA : c.2.1 (F' a) ∉ A := fun h => haA ((hA _ haH).1 h)
  have hzT : c.2.1 (F' a) ∈ (H \ A) ∩ ball (g p') r := ⟨⟨hzH, hzA⟩, by rw [← hgFa]; exact hag⟩
  refine ⟨hzT, ?_⟩
  set T := (H \ A) ∩ ball (g p') r with hT
  set Kz := connectedComponentIn T (c.2.1 (F' a)) with hKz
  have hKzD : Kz ⊆ (c.dom : Set ℂ) := fun y hy => by
    have hyT := connectedComponentIn_subset T _ hy
    by_contra hyD
    exact hyT.1.2 (hD ⟨hyT.1.1, hyD⟩)
  have hpre : IsPreconnected (c.1 '' Kz) :=
    isPreconnected_connectedComponentIn.image _ (hc.differentiableOn_fwd.continuousOn.mono hKzD)
  have hzKz : c.2.1 (F' a) ∈ Kz := mem_connectedComponentIn hzT
  have hc1z : c.1 (c.2.1 (F' a)) = F' a := hc.2.2 _ haH
  set V := ⋃ q ∈ Φ', ball q ε with hV
  have hsub : c.1 '' Kz ⊆ ball p' ε ∪ V := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨hyH, hyy⟩ := chart_fwd_mem_of_mem_dom hc (hKzD hy)
    have hyT := connectedComponentIn_subset T _ hy
    have hg1 : g (c.1 y) ∈ ball (g p') r := by rw [hgi hyH, hyy]; exact hyT.2
    rcases mem_iUnion₂.1 (hrb (c.1 y) (mem_Hbar_of_mem_H hyH) hg1) with ⟨q, hq, hyq⟩
    by_cases hqp : q = p'
    · subst hqp; exact Or.inl hyq
    · exact Or.inr (mem_iUnion₂.2 ⟨q, ⟨hq, hqp⟩, hyq⟩)
  have hdisj : Disjoint (ball p' ε) V := by
    rw [Set.disjoint_iUnion₂_right]
    intro q hq
    refine Metric.ball_disjoint_ball ?_
    have hqδ : q ∉ ball p' δ := fun h => hδb h hq
    rw [mem_ball, not_lt] at hqδ
    rw [dist_comm]
    linarith [min_le_right r' (δ / 2)]
  have hin : c.1 '' Kz ⊆ ball p' ε :=
    hpre.subset_left_of_subset_union isOpen_ball (isOpen_biUnion fun _ _ => isOpen_ball) hdisj hsub
      ⟨_, mem_image_of_mem _ hzKz, by rw [hc1z]; exact hab⟩
  have hin2 : c.1 '' Kz ⊆ connectedComponentIn ((H \ A') ∩ ball p' r') (F' a) := by
    refine hpre.subset_connectedComponentIn ⟨_, hzKz, hc1z⟩ ?_
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨hyH, hyy⟩ := chart_fwd_mem_of_mem_dom hc (hKzD hy)
    have hyT := connectedComponentIn_subset T _ hy
    refine ⟨⟨hyH, fun h => hyT.1.2 ?_⟩, ball_subset_ball (min_le_left _ _) (hin ⟨y, hy, rfl⟩)⟩
    rw [← hyy]
    exact (hA _ hyH).2 h
  rw [Set.disjoint_left]
  intro y hy hyB
  obtain ⟨hyH, hyy⟩ := chart_fwd_mem_of_mem_dom hc (hKzD hy)
  have hB' : c.1 y ∈ B' := hB _ hyH (by rw [hyy]; exact hyB)
  exact Set.disjoint_left.1 hadisj (hin2 ⟨y, hy, rfl⟩) hB'

/-! ### The datum pulls back -/

/-- A chart landing on `A' ∪ ℝ` pulls back to a physical landing on `A ∪ ℝ` (real chart points land on the complement
of the domain or on `ℝ`). -/
theorem landing_pullback {c : Chart} {g : ℂ → ℂ} (hgi : EqOn g c.2.1 H)
    (hgR : ∀ x : ℝ, g x ∈ (H \ (c.dom : Set ℂ)) ∪ {z : ℂ | z.im = 0}) {A A' : Set ℂ}
    (hD : H \ (c.dom : Set ℂ) ⊆ A) (hA : ∀ w ∈ H, c.2.1 w ∈ A ↔ w ∈ A') {p' : ℂ} (hp' : p' ∈ Hbar)
    (hpA : p' ∈ A' ∪ {z : ℂ | z.im = 0}) : g p' ∈ A ∪ {z : ℂ | z.im = 0} := by
  have hreal : p'.im = 0 → g p' ∈ A ∪ {z : ℂ | z.im = 0} := by
    intro h0
    have e : p' = ((p'.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [h0])
    rcases hgR p'.re with h | h
    · rw [e]; exact Or.inl (hD h)
    · rw [e]; exact Or.inr h
  rcases hpA with hpA | hpA
  · by_cases hpos : 0 < p'.im
    · have hpH : p' ∈ H := hpos
      rw [hgi hpH]
      exact Or.inl ((hA _ hpH).2 hpA)
    · exact hreal (le_antisymm (not_lt.1 hpos) hp')
  · exact hreal hpA

/-- **The union word datum pulls back through a chart**: if the chart picture `(C', A₁', A₂')` has the datum, the
physical picture `(C, A₁, A₂)` has it, with parametrization `c.2.1 ∘ f`, chart `φ ∘ c.1` and lift `L ∘ c.1 + c.2.2`.
Inputs: the chart is conformal with continuous lift equal to the argument of its derivative; its inverse has a
continuous boundary map `g` on `ℍ̄` that is proper, has finite fibres and sends `ℝ` into `ℍ ∖ D ∪ ℝ`; the domain's
complement lies in both sets; the sets correspond (`c.2.1 w ∈ Aᵢ ↔ w ∈ Aᵢ'`); the individual means and the candidate
change by the chart (`w + u₀ = (w' + u₀') ∘ c.1 − χ c.2.2`, `v = v' ∘ c.1 − χ c.2.2`). -/
theorem hasUnionWordBoundaryOnC_pullback {c : Chart} (hc : c.IsConformal) (hℓc : ContinuousOn c.2.2 c.dom)
    (hℓd : ∀ z ∈ (c.dom : Set ℂ), deriv c.1 z = ‖deriv c.1 z‖ * Complex.exp (c.2.2 z * Complex.I))
    {g : ℂ → ℂ} (hgc : ContinuousOn g Hbar) (hgi : EqOn g c.2.1 H) (hgf : ∀ z, (g ⁻¹' {z} ∩ Hbar).Finite)
    (hgp : ∀ M : ℝ, ∃ R : ℝ, ∀ z ∈ Hbar, R < ‖z‖ → M < ‖g z‖)
    (hgR : ∀ x : ℝ, g x ∈ (H \ (c.dom : Set ℂ)) ∪ {z : ℂ | z.im = 0})
    {C' A₁' A₂' C A₁ A₂ : Set ℂ} {u₀' v' w₁' w₂' u₀ v w₁ w₂ : ℂ → ℝ} {χ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ}
    (hUo : IsOpen (H \ (A₁' ∪ A₂')))
    (hD₁ : H \ (c.dom : Set ℂ) ⊆ A₁) (hD₂ : H \ (c.dom : Set ℂ) ⊆ A₂)
    (hA₁ : ∀ w ∈ H, c.2.1 w ∈ A₁ ↔ w ∈ A₁') (hA₂ : ∀ w ∈ H, c.2.1 w ∈ A₂ ↔ w ∈ A₂')
    (hC : ∀ z ∈ C, z ∈ H \ (A₁ ∪ A₂) ∧ c.1 z ∈ C')
    (hw₁ : ∀ z ∈ H \ (A₁ ∪ A₂), w₁ z + u₀ z = w₁' (c.1 z) + u₀' (c.1 z) - χ * c.2.2 z)
    (hw₂ : ∀ z ∈ H \ (A₁ ∪ A₂), w₂ z + u₀ z = w₂' (c.1 z) + u₀' (c.1 z) - χ * c.2.2 z)
    (hv : ∀ z ∈ H \ (A₁ ∪ A₂), v z = v' (c.1 z) - χ * c.2.2 z)
    (h : HasUnionWordBoundaryOnC C' A₁' A₂' u₀' v' w₁' w₂' χ b J) :
    HasUnionWordBoundaryOnC C A₁ A₂ u₀ v w₁ w₂ χ b J := by
  intro z₀ hz₀
  obtain ⟨hz₀U, hz₀C'⟩ := hC z₀ hz₀
  obtain ⟨f', φ', G, L', E, hf', hφ', hG, hL', hd', hE, hv', hlim'⟩ := h (c.1 z₀) hz₀C'
  set U := H \ (A₁ ∪ A₂) with hU
  set U' := H \ (A₁' ∪ A₂') with hU'
  have hUD : U ⊆ (c.dom : Set ℂ) := fun y hy => by
    by_contra hyD
    exact hy.2 (Or.inl (hD₁ ⟨hy.1, hyD⟩))
  have hmap' : MapsTo c.2.1 U' U := fun w hw => ⟨hc.2.1 hw.1, fun h => hw.2
    (h.elim (fun h1 => Or.inl ((hA₁ _ hw.1).1 h1)) (fun h2 => Or.inr ((hA₂ _ hw.1).1 h2)))⟩
  have hmap : MapsTo c.1 U U' := fun y hy => by
    obtain ⟨hyH, hyy⟩ := chart_fwd_mem_of_mem_dom hc (hUD hy)
    refine ⟨hyH, fun h => hy.2 ?_⟩
    rcases h with h | h
    · exact Or.inl (by rw [← hyy]; exact (hA₁ _ hyH).2 h)
    · exact Or.inr (by rw [← hyy]; exact (hA₂ _ hyH).2 h)
  have hcont' : ContinuousOn c.2.1 U' := hc.1.continuousOn.mono fun w hw => hw.1
  have hcont : ContinuousOn c.1 U := hc.differentiableOn_fwd.continuousOn.mono hUD
  have hinv' : ∀ w ∈ U', c.1 (c.2.1 w) = w := fun w hw => hc.2.2 w hw.1
  have hinv : ∀ y ∈ U, c.2.1 (c.1 y) = y := fun y hy => (chart_fwd_mem_of_mem_dom hc (hUD hy)).2
  set K' := connectedComponentIn U' (c.1 z₀) with hK'
  set K := connectedComponentIn U z₀ with hK
  have hKK : K = c.2.1 '' K' := by
    have e := image_connectedComponentIn_of_invOn hcont' hcont hmap' hmap hinv' hinv (hmap hz₀U)
    rw [hinv z₀ hz₀U] at e
    exact e.symm
  have hK'o : IsOpen K' := hUo.connectedComponentIn
  have hK'U : K' ⊆ U' := connectedComponentIn_subset _ _
  have hKU : K ⊆ U := connectedComponentIn_subset _ _
  have hKK' : ∀ {z}, z ∈ K → c.1 z ∈ K' := fun hz => by
    rw [hKK] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    rwa [hinv' w (hK'U hw)]
  have hK'K : ∀ {w}, w ∈ K' → c.2.1 w ∈ K := fun hw => by rw [hKK]; exact mem_image_of_mem _ hw
  have hdφ : ∀ z ∈ K, DifferentiableAt ℂ φ' (c.1 z) := fun z hz =>
    (hφ'.1 _ (hKK' hz)).differentiableAt (hK'o.mem_nhds (hKK' hz))
  have hdc : ∀ z ∈ K, DifferentiableAt ℂ c.1 z := fun z hz =>
    (hc.differentiableOn_fwd z (hUD (hKU hz))).differentiableAt (c.dom.isOpen.mem_nhds (hUD (hKU hz)))
  refine ⟨fun ζ => c.2.1 (f' ζ), fun z => φ' (c.1 z), G, fun z => L' (c.1 z) + c.2.2 z, E,
    ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, hG, ?_, ?_, hE, ?_, ?_⟩
  · intro ζ hζ
    have hH : f' ζ ∈ H := (hK'U (hf'.2.mapsTo hζ)).1
    exact ((hc.1 _ hH).differentiableAt (QuantumZipper.isOpen_H.mem_nhds hH)).comp ζ
      ((hf'.1 ζ hζ).differentiableAt (isOpen_ball.mem_nhds hζ)) |>.differentiableWithinAt
  · intro ζ hζ
    exact hK'K (hf'.2.mapsTo hζ)
  · intro ζ₁ hζ₁ ζ₂ hζ₂ e
    exact hf'.2.injOn hζ₁ hζ₂ (hc.injOn (hK'U (hf'.2.mapsTo hζ₁)).1 (hK'U (hf'.2.mapsTo hζ₂)).1 e)
  · intro z hz
    rw [hKK] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    obtain ⟨ζ, hζ, rfl⟩ := hf'.2.surjOn hw
    exact ⟨ζ, hζ, rfl⟩
  · intro z hz
    exact ((hdφ z hz).comp z (hdc z hz)).differentiableWithinAt
  · intro z hz
    exact hφ'.2.mapsTo (hKK' hz)
  · intro z₁ hz₁ z₂ hz₂ e
    have e1 := hφ'.2.injOn (hKK' hz₁) (hKK' hz₂) e
    rw [← hinv z₁ (hKU hz₁), ← hinv z₂ (hKU hz₂), e1]
  · intro w hw
    obtain ⟨y, hy, rfl⟩ := hφ'.2.surjOn hw
    exact ⟨c.2.1 y, hK'K hy, by simp only [hinv' y (hK'U hy)]⟩
  · exact (hL'.comp (hcont.mono hKU) fun z hz => hKK' hz).add (hℓc.mono fun z hz => hUD (hKU hz))
  · intro z hz
    have hder : deriv (fun z => φ' (c.1 z)) z = deriv φ' (c.1 z) * deriv c.1 z :=
      deriv_comp z (hdφ z hz) (hdc z hz)
    have ha := hd' _ (hKK' hz)
    have hb := hℓd z (hUD (hKU hz))
    rw [hder, norm_mul]
    conv_lhs => rw [ha, hb]
    push_cast
    rw [add_mul, Complex.exp_add]
    ring
  · intro z hz
    simp only
    rw [hv z (hKU hz), hv' (hKK' hz)]
    ring
  · intro q hq hqE
    have : (𝓝[ball (0 : ℂ) 1] q).NeBot := mem_closure_iff_nhdsWithin_neBot.1
      (by rw [closure_ball 0 one_ne_zero]; exact sphere_subset_closedBall hq)
    have hfK' : ∀ᶠ ζ in 𝓝[ball (0 : ℂ) 1] q, f' ζ ∈ K' :=
      (self_mem_nhdsWithin : ball (0 : ℂ) 1 ∈ 𝓝[ball (0 : ℂ) 1] q) |> fun h => Filter.mem_of_superset h
        fun ζ hζ => hf'.2.mapsTo hζ
    have hHbar : IsClosed Hbar := isClosed_le continuous_const Complex.continuous_im
    have hfHbar : ∀ᶠ ζ in 𝓝[ball (0 : ℂ) 1] q, f' ζ ∈ Hbar :=
      hfK'.mono fun ζ h => mem_Hbar_of_mem_H (hK'U h).1
    have hexpr : ∀ (w w' : ℂ → ℝ), (∀ z ∈ U, w z + u₀ z = w' (c.1 z) + u₀' (c.1 z) - χ * c.2.2 z) →
        Tendsto (fun ζ => (w' (f' ζ) + u₀' (f' ζ)) - (G (φ' (f' ζ)) - χ * L' (f' ζ))) (𝓝[ball (0 : ℂ) 1] q)
          (𝓝 0) →
        Tendsto (fun ζ => (w (c.2.1 (f' ζ)) + u₀ (c.2.1 (f' ζ))) -
          (G (φ' (c.1 (c.2.1 (f' ζ)))) - χ * (L' (c.1 (c.2.1 (f' ζ))) + c.2.2 (c.2.1 (f' ζ)))))
          (𝓝[ball (0 : ℂ) 1] q) (𝓝 0) := by
      intro w w' hw hl
      refine hl.congr' (hfK'.mono fun ζ hζ => ?_)
      have hy := hK'U hζ
      beta_reduce
      rw [hw _ (hmap' hy), hinv' _ hy]
      ring
    have hgt : ∀ {p' : ℂ}, Tendsto f' (𝓝[ball (0 : ℂ) 1] q) (𝓝 p') →
        p' ∈ Hbar ∧ Tendsto (fun ζ => c.2.1 (f' ζ)) (𝓝[ball (0 : ℂ) 1] q) (𝓝 (g p')) := by
      intro p' hp'
      have hpH : p' ∈ Hbar := hHbar.mem_of_tendsto hp' hfHbar
      refine ⟨hpH, ((hgc p' hpH).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hp', hfHbar⟩)).congr' ?_⟩
      exact hfK'.mono fun ζ hζ => hgi (hK'U hζ).1
    rcases hlim' q hq hqE with ⟨p', hp', hpA, ⟨r', hr', hfr⟩, hl⟩ | ⟨p', hp', hpA, ⟨r', hr', hfr⟩, hl⟩
    · obtain ⟨hpH, hlim⟩ := hgt hp'
      obtain ⟨r, hr, hev⟩ := eventually_freeNear_pullback hc hgc hgi hgp hD₁ hA₁
        (fun w hw h => (hA₂ w hw).1 h) hpH (hgf _) hp' hr' hfr
      exact Or.inl ⟨g p', hlim, landing_pullback hgi hgR hD₁ hA₁ hpH hpA, ⟨r, hr, hev⟩,
        hexpr w₁ w₁' hw₁ hl⟩
    · obtain ⟨hpH, hlim⟩ := hgt hp'
      obtain ⟨r, hr, hev⟩ := eventually_freeNear_pullback hc hgc hgi hgp hD₂ hA₂
        (fun w hw h => (hA₁ w hw).1 h) hpH (hgf _) hp' hr' hfr
      exact Or.inr ⟨g p', hlim, landing_pullback hgi hgR hD₂ hA₂ hpH hpA, ⟨r, hr, hev⟩,
        hexpr w₂ w₂' hw₂ hl⟩

end InteractingSLE.Theorem14.SB.Ln
