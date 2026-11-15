/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6GlueTrace
import InteractingSLE.Spec.Supplement.GW3Word

/-!
# Theorem GW4: a component traversal from the relative hulls (deterministic)

Packet PROVE-T14-GW4T. Theorem GW4, proof (`source/spec/p625-671.md` L248–L252, pp. 637–638): "Thus at every
nonterminal traversal stop `D_s ∩ C = E_s`, where `E_s` is the relative component incident to `x_C` […] The
continuous-trace criterion gives the actual relative continuous driver and its adapted strictly increasing clock."

Setting (one realization). The ambient counterflow is read in its own chart `R(z) = −1/z`: its hulls are the Loewner
hulls `K'_t` of a continuous driver `W'` with complete continuous generating trace `γ`, and the physical counterflow is
`η' = R ∘ γ`. A component `C ⊆ ℍ` (open) has a component chart `c = (fwd, inv, lift)`. In the ambient chart the
component is `D = R⁻¹(C)` (`relDom`), and the relative coordinate is `Φ = R ∘ fwd ∘ R : D → ℍ` (`relMapC`), with
inverse `R ∘ inv ∘ R` (`relInvC`). Suppose a continuous driver `WC` (complete continuous generating trace `Γ`, whose
interior times are dense) generates, at every relative time `s`, the image `Φ(K'_{T s} ∩ D)` of the part of the ambient
hull inside the component, for a continuous strictly increasing clock `T` (the source's `D_s ∩ C = E_s`: the relative
hull is the visited part of `C`). Suppose also that the ambient trace avoids `closure C` before the entry time `T 0`,
and that neither trace is at its chart's infinity at positive relative times. Then the frozen `IsComponentTraversal`
holds.

## Main results

* `relDom`, `relMapC`, `relInvC` and their chart facts;
* `invExt`: the boundary extension of `inv` (finite limits at every real point by `IsComponentChart`),
  continuous on `ℍ̄`;
* `mem_closure_relMapC_ball`, **`relTrace_eq_of_mem_H`**: at a relative time with `Γ(s) ∈ ℍ` the ambient tip is in
  `D` and `Γ(s) = Φ(γ(T s))` (the argument of GB6's `relTrace_eq`, for an arbitrary conformal chart);
* `invExt_relTrace_eq`: at every positive relative time `inv(R(Γ(s))) = R(γ(T s))` (density of interior times and
  continuity of both sides);
* **`isComponentTraversal_of_relHulls`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace Theorem14

namespace GW4Traverse

/-! ### The component in the ambient counterflow chart -/

/-- The component `C` read in the ambient counterflow chart: `R⁻¹(C) = {w | −1/w ∈ C}`. -/
def relDom (C : Set ℂ) : Set ℂ := (fun w : ℂ => -w⁻¹) ⁻¹' C

/-- The relative coordinate in the ambient counterflow chart: `Φ(w) = −1/fwd(−1/w)`. -/
def relMapC (c : Chart) (w : ℂ) : ℂ := -(c.1 (-w⁻¹))⁻¹

/-- The inverse relative coordinate: `Φ⁻¹(v) = −1/inv(−1/v)`. -/
def relInvC (c : Chart) (v : ℂ) : ℂ := -(c.2.1 (-v⁻¹))⁻¹

/-- The boundary extension of the inverse chart: the limit of `inv` within `ℍ`. -/
def invExt (c : Chart) (w : ℂ) : ℂ := extendFrom H c.2.1 w

theorem negInv_negInv' (z : ℂ) : -(-z⁻¹)⁻¹ = z := by rw [inv_neg, inv_inv, neg_neg]

theorem ne_zero_of_mem_H' {z : ℂ} (hz : z ∈ H) : z ≠ 0 := fun h => by
  have : (0 : ℝ) < z.im := hz
  rw [h, zero_im] at this
  exact lt_irrefl _ this

theorem negInv_mem_H' {z : ℂ} (hz : z ∈ H) : -z⁻¹ ∈ H := by
  have h0 := ne_zero_of_mem_H' hz
  have hz' : (0 : ℝ) < z.im := hz
  show (0 : ℝ) < (-z⁻¹).im
  rw [neg_im, inv_im, neg_div, neg_neg]
  exact div_pos hz' (normSq_pos.2 h0)

theorem negInv_mem_Hbar {z : ℂ} (hz : z ∈ Hbar) : -z⁻¹ ∈ Hbar := by
  have hz' : (0 : ℝ) ≤ z.im := hz
  show (0 : ℝ) ≤ (-z⁻¹).im
  rw [neg_im, inv_im, neg_div, neg_neg]
  exact div_nonneg hz' (normSq_nonneg z)

theorem continuousAt_negInv {z : ℂ} (hz : z ≠ 0) : ContinuousAt (fun w : ℂ => -w⁻¹) z :=
  (continuousAt_inv₀ hz).neg

theorem tendsto_negInv {α : Type*} {l : Filter α} {f : α → ℂ} {z : ℂ} (hf : Tendsto f l (𝓝 z)) (hz : z ≠ 0) :
    Tendsto (fun a => -(f a)⁻¹) l (𝓝 (-z⁻¹)) :=
  (continuousAt_negInv hz).tendsto.comp hf

/-- The radial approach `y ↦ i y` to `0` stays in `ℍ`. -/
theorem tendsto_radial : Tendsto (fun y : ℝ => (y : ℂ) * I) (𝓝[>] 0) (𝓝[H] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have h : Tendsto (fun y : ℝ => (y : ℂ) * I) (𝓝 0) (𝓝 ((0 : ℝ) * I)) :=
      ((continuous_ofReal.mul continuous_const).tendsto 0)
    rw [ofReal_zero, zero_mul] at h
    exact h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with y hy
    show (0 : ℝ) < ((y : ℂ) * I).im
    simpa using hy

section Chart

variable {R L C : Set ℂ} {c : Chart}

theorem relDom_subset_H (hCH : C ⊆ H) : relDom C ⊆ H := fun w hw => by
  have := negInv_mem_H' (hCH hw)
  rwa [negInv_negInv'] at this

theorem isOpen_relDom (hCo : IsOpen C) (hCH : C ⊆ H) : IsOpen (relDom C) := by
  have hc : ContinuousOn (fun w : ℂ => -w⁻¹) {w | w ≠ 0} := fun w hw => (continuousAt_negInv hw).continuousWithinAt
  have ho := hc.isOpen_inter_preimage isOpen_ne hCo
  convert ho using 1
  ext w
  refine ⟨fun hw => ⟨ne_zero_of_mem_H' (relDom_subset_H hCH hw), hw⟩, fun hw => hw.2⟩

theorem relMapC_mem_H (hc : IsComponentChart R L C c) {w : ℂ} (hw : w ∈ relDom C) : relMapC c w ∈ H :=
  negInv_mem_H' (hc.2.1 hw)

theorem relInvC_mem (hc : IsComponentChart R L C c) {v : ℂ} (hv : v ∈ H) : relInvC c v ∈ relDom C := by
  show -(-(c.2.1 (-v⁻¹))⁻¹)⁻¹ ∈ C
  rw [negInv_negInv']
  exact hc.2.2.1 (negInv_mem_H' hv)

theorem relInvC_relMapC (hc : IsComponentChart R L C c) {w : ℂ} (hw : w ∈ relDom C) :
    relInvC c (relMapC c w) = w := by
  show -(c.2.1 (-(-(c.1 (-w⁻¹))⁻¹)⁻¹))⁻¹ = w
  rw [negInv_negInv', hc.2.2.2.1.1 hw, negInv_negInv']

theorem relMapC_relInvC (hc : IsComponentChart R L C c) {v : ℂ} (hv : v ∈ H) :
    relMapC c (relInvC c v) = v := by
  show -(c.1 (-(-(c.2.1 (-v⁻¹))⁻¹)⁻¹))⁻¹ = v
  rw [negInv_negInv', hc.2.2.2.1.2 (negInv_mem_H' hv), negInv_negInv']

theorem continuousOn_relMapC (hc : IsComponentChart R L C c) (hCo : IsOpen C) (hCH : C ⊆ H) :
    ContinuousOn (relMapC c) (relDom C) := by
  intro w hw
  have hw0 : w ≠ 0 := ne_zero_of_mem_H' (relDom_subset_H hCH hw)
  have h1 : ContinuousAt c.1 (-w⁻¹) := (hc.1.continuousOn.continuousAt (hCo.mem_nhds hw))
  have h2 : ContinuousAt (fun z => c.1 (-z⁻¹)) w :=
    ContinuousAt.comp (g := c.1) (f := fun z : ℂ => -z⁻¹) h1 (continuousAt_negInv hw0)
  have h3 : c.1 (-w⁻¹) ≠ 0 := ne_zero_of_mem_H' (hc.2.1 hw)
  exact (ContinuousAt.comp (g := fun z : ℂ => -z⁻¹) (f := fun z => c.1 (-z⁻¹))
    (continuousAt_negInv h3) h2).continuousWithinAt

theorem continuousOn_relInvC (hc : IsComponentChart R L C c) (hCo : IsOpen C) (hCH : C ⊆ H) :
    ContinuousOn (relInvC c) H := by
  intro v hv
  have hinv : ContinuousOn c.2.1 H := (GW3Word.differentiableOn_inv_of_isComponentChart hc hCo).continuousOn
  have h1 : ContinuousAt c.2.1 (-v⁻¹) :=
    hinv.continuousAt (QuantumZipper.isOpen_H.mem_nhds (negInv_mem_H' hv))
  have h2 : ContinuousAt (fun z => c.2.1 (-z⁻¹)) v :=
    ContinuousAt.comp (g := c.2.1) (f := fun z : ℂ => -z⁻¹) h1 (continuousAt_negInv (ne_zero_of_mem_H' hv))
  have h3 : c.2.1 (-v⁻¹) ≠ 0 := ne_zero_of_mem_H' (hCH (hc.2.2.1 (negInv_mem_H' hv)))
  exact (ContinuousAt.comp (g := fun z : ℂ => -z⁻¹) (f := fun z => c.2.1 (-z⁻¹))
    (continuousAt_negInv h3) h2).continuousWithinAt

/-- The inverse chart maps `ℍ` onto the component. -/
theorem image_inv_eq (hc : IsComponentChart R L C c) : c.2.1 '' H = C := by
  refine Subset.antisymm (image_subset_iff.2 hc.2.2.1) fun z hz => ?_
  exact ⟨c.1 z, hc.2.1 hz, hc.2.2.2.1.1 hz⟩

/-- `inv` has a limit within `ℍ` at every point of `ℍ̄`, namely `invExt c`. -/
theorem tendsto_invExt (hc : IsComponentChart R L C c) (hCo : IsOpen C) {w : ℂ} (hw : w ∈ Hbar) :
    Tendsto c.2.1 (𝓝[H] w) (𝓝 (invExt c w)) := by
  refine tendsto_extendFrom ?_
  have hw' : (0 : ℝ) ≤ w.im := hw
  rcases hw'.eq_or_lt with h0 | hpos
  · obtain ⟨p, hp, -⟩ := hc.2.2.2.2.1 w.re
    refine ⟨p, ?_⟩
    have : ((w.re : ℝ) : ℂ) = w := Complex.ext (by simp) (by simp [h0])
    rwa [this] at hp
  · have hinv : ContinuousOn c.2.1 H := (GW3Word.differentiableOn_inv_of_isComponentChart hc hCo).continuousOn
    exact ⟨_, (hinv.continuousAt (QuantumZipper.isOpen_H.mem_nhds hpos)).tendsto.mono_left nhdsWithin_le_nhds⟩

theorem invExt_eq_of_mem_H (hc : IsComponentChart R L C c) (hCo : IsOpen C) {w : ℂ} (hw : w ∈ H) :
    invExt c w = c.2.1 w := by
  have hinv : ContinuousOn c.2.1 H := (GW3Word.differentiableOn_inv_of_isComponentChart hc hCo).continuousOn
  have ht : Tendsto c.2.1 (𝓝[H] w) (𝓝 (c.2.1 w)) :=
    (hinv.continuousAt (QuantumZipper.isOpen_H.mem_nhds hw)).tendsto.mono_left nhdsWithin_le_nhds
  exact extendFrom_eq (subset_closure hw) ht

theorem continuousOn_invExt (hc : IsComponentChart R L C c) (hCo : IsOpen C) : ContinuousOn (invExt c) Hbar := by
  have hcl : closure H = Hbar := Complex.closure_setOfPred_lt_im 0
  refine continuousOn_extendFrom (by rw [hcl]) fun w hw => ⟨_, tendsto_invExt hc hCo hw⟩

end Chart

/-! ### The relative trace -/

section Trace

variable {R L C : Set ℂ} {c : Chart} {W' WC : ℝ≥0 → ℝ} {γ Γ : ℝ≥0 → ℂ} {T : ℝ≥0 → ℝ≥0}

theorem continuous_of_isGeneratingTrace_top {w : ℝ≥0 → ℝ} {η : ℝ≥0 → ℂ} (h : IsGeneratingTrace w ⊤ η) :
    Continuous η := by
  have := h.2.1
  simp only [le_top, ofPred_true] at this
  exact continuousOn_univ.1 this

/-- **The relative tip is a limit of chart images of small ambient hull increments**: at every relative time `s` and
radius `ρ > 0`, `Γ(s)` lies in the closure of `Φ(B(γ(T s), ρ) ∩ D)` (GB6's `relTrace_eq`, first step). -/
theorem mem_closure_relMapC_ball (hW' : Continuous W') (hW'0 : W' 0 = 0) (hγ : IsGeneratingTrace W' ⊤ γ)
    (hWC : Continuous WC) (hWC0 : WC 0 = 0) (hΓ : IsGeneratingTrace WC ⊤ Γ)
    (hT : StrictMono T) (hTc : Continuous T)
    (hK : ∀ s : ℝ≥0, QuantumZipper.fwdHull (fun r : ℝ => WC r.toNNReal) s =
      relMapC c '' (QuantumZipper.fwdHull (fun r : ℝ => W' r.toNNReal) (T s) ∩ relDom C))
    (s : ℝ≥0) {ρ : ℝ} (hρ : 0 < ρ) :
    Γ s ∈ closure (relMapC c '' (ball (γ (T s)) ρ ∩ relDom C)) := by
  have hW'r : Continuous fun r : ℝ => W' r.toNNReal := hW'.comp continuous_real_toNNReal
  have hW'r0 : (fun r : ℝ => W' r.toNNReal) 0 = 0 := by simp only [Real.toNNReal_zero, hW'0]
  have htip : Tendsto (QuantumZipper.fwdMapInv (fun r : ℝ => W' r.toNNReal) (T s)) (𝓝[H] 0) (𝓝 (γ (T s))) :=
    IsGeneratingTrace.tendsto_fwdMapInv_tip hγ hW'.continuousOn hW'0 ENNReal.coe_lt_top
  obtain ⟨δ, hδ, hsub⟩ := Supp8.GB6.exists_diff_fwdHull_subset_ball hW'r hW'r0 (NNReal.coe_nonneg (T s)) htip hρ
  have hev : ∀ᶠ s' in 𝓝 s, T s' ∈ ball (T s) δ := (hTc.tendsto s).eventually (ball_mem_nhds _ hδ)
  obtain ⟨s', hs'δ, hss'⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin : Ioi s ∈ 𝓝[>] s)).exists
  have hss'' : s < s' := hss'
  have hTT : T s < T s' := hT hss''
  have hTd : ((T s' : ℝ) - T s) < δ := by
    have h1 := mem_ball.1 hs'δ
    rw [NNReal.dist_eq] at h1
    exact lt_of_le_of_lt (le_abs_self _) h1
  have hTd0 : (0 : ℝ) ≤ (T s' : ℝ) - T s := sub_nonneg.2 (by exact_mod_cast hTT.le)
  have hcl := Supp8.GB6.mem_closure_diff_of_isGeneratingTrace hΓ hWC hWC0 (u := (s : ℝ)) (u' := (s' : ℝ))
    (NNReal.coe_nonneg s) (show (s : ℝ) < s' from hss'')
  have es : (s : ℝ).toNNReal = s := by simp
  rw [es] at hcl
  refine closure_mono ?_ hcl
  rintro z ⟨hz1, hz2⟩
  rw [hK s'] at hz1
  rw [hK s] at hz2
  obtain ⟨w, ⟨hwK, hwD⟩, rfl⟩ := hz1
  refine ⟨w, ⟨?_, hwD⟩, rfl⟩
  have hwK' : w ∉ QuantumZipper.fwdHull (fun r : ℝ => W' r.toNNReal) (T s) := fun h => hz2 ⟨w, ⟨h, hwD⟩, rfl⟩
  have e : ((T s' : ℝ≥0) : ℝ) = (T s : ℝ) + ((T s' : ℝ) - T s) := by ring
  rw [e] at hwK
  exact hsub _ hTd0 hTd ⟨hwK, hwK'⟩

/-- **The relative trace at an interior time is the chart image of the ambient trace** (GB6's `relTrace_eq` for an
arbitrary component chart): if `Γ(s) ∈ ℍ`, the ambient tip `γ(T s)` lies in `D` and `Γ(s) = Φ(γ(T s))`. -/
theorem relTrace_eq_of_mem_H (hc : IsComponentChart R L C c) (hCo : IsOpen C) (hCH : C ⊆ H)
    (hW' : Continuous W') (hW'0 : W' 0 = 0) (hγ : IsGeneratingTrace W' ⊤ γ)
    (hWC : Continuous WC) (hWC0 : WC 0 = 0) (hΓ : IsGeneratingTrace WC ⊤ Γ)
    (hT : StrictMono T) (hTc : Continuous T)
    (hK : ∀ s : ℝ≥0, QuantumZipper.fwdHull (fun r : ℝ => WC r.toNNReal) s =
      relMapC c '' (QuantumZipper.fwdHull (fun r : ℝ => W' r.toNNReal) (T s) ∩ relDom C))
    (s : ℝ≥0) (hΓs : Γ s ∈ H) : γ (T s) ∈ relDom C ∧ Γ s = relMapC c (γ (T s)) := by
  have hkey : ∀ ρ : ℝ, 0 < ρ → Γ s ∈ closure (relMapC c '' (ball (γ (T s)) ρ ∩ relDom C)) :=
    fun ρ hρ => mem_closure_relMapC_ball hW' hW'0 hγ hWC hWC0 hΓ hT hTc hK s hρ
  by_cases hD : γ (T s) ∈ relDom C
  · refine ⟨hD, eq_of_forall_dist_le fun ε hε => ?_⟩
    obtain ⟨ρ, hρ, hρb⟩ := Metric.continuousAt_iff.1
      ((continuousOn_relMapC hc hCo hCH).continuousAt ((isOpen_relDom hCo hCH).mem_nhds hD)) ε hε
    have hball : relMapC c '' (ball (γ (T s)) ρ ∩ relDom C) ⊆ closedBall (relMapC c (γ (T s))) ε := by
      rintro _ ⟨w, ⟨hw, -⟩, rfl⟩
      exact (hρb (mem_ball.1 hw)).le
    exact mem_closedBall.1 (closure_minimal hball isClosed_closedBall (hkey ρ hρ))
  · exfalso
    have hΓim : (0 : ℝ) < (Γ s).im := hΓs
    set δ' : ℝ := (Γ s).im / 2 with hδ'def
    have hδ' : 0 < δ' := half_pos hΓim
    have hBH : closedBall (Γ s) δ' ⊆ H := fun v hv => by
      rw [mem_closedBall, dist_eq_norm] at hv
      have h1 : |(v - Γ s).im| ≤ ‖v - Γ s‖ := abs_im_le_norm _
      have h2 : (v - Γ s).im = v.im - (Γ s).im := sub_im _ _
      have h3 := (abs_le.1 (h1.trans hv)).1
      show (0 : ℝ) < v.im
      linarith
    set Kc := relInvC c '' closedBall (Γ s) δ' with hKcdef
    have hKc : IsCompact Kc :=
      (isCompact_closedBall _ _).image_of_continuousOn ((continuousOn_relInvC hc hCo hCH).mono hBH)
    have hnot : γ (T s) ∉ Kc := by
      rintro ⟨v, hv, hveq⟩
      exact hD (hveq ▸ relInvC_mem hc (hBH hv))
    obtain ⟨ρ, hρ, hρK⟩ := Metric.isOpen_iff.1 hKc.isClosed.isOpen_compl _ hnot
    obtain ⟨_, ⟨w, ⟨hw, hwD⟩, rfl⟩, hwz⟩ := Metric.mem_closure_iff.1 (hkey ρ hρ) δ' hδ'
    exact hρK hw ⟨relMapC c w, mem_closedBall.2 (by rw [dist_comm]; exact hwz.le), relInvC_relMapC hc hwD⟩

/-- **At every positive relative time the relative trace read in `C` is the physical counterflow point**:
`inv(R(Γ(s))) = R(γ(T s))`, with `inv` extended to the real line. Interior times by `relTrace_eq_of_mem_H`;
boundary times as limits of interior times from the right (both sides are continuous). -/
theorem invExt_relTrace_eq (hc : IsComponentChart R L C c) (hCo : IsOpen C) (hCH : C ⊆ H)
    (hW' : Continuous W') (hW'0 : W' 0 = 0) (hγ : IsGeneratingTrace W' ⊤ γ)
    (hWC : Continuous WC) (hWC0 : WC 0 = 0) (hΓ : IsGeneratingTrace WC ⊤ Γ)
    (hdense : ∀ s : ℝ≥0, ∀ ε : ℝ, 0 < ε → ∃ s' : ℝ≥0, s < s' ∧ (s' : ℝ) < s + ε ∧ Γ s' ∈ H)
    (hT : StrictMono T) (hTc : Continuous T)
    (hK : ∀ s : ℝ≥0, QuantumZipper.fwdHull (fun r : ℝ => WC r.toNNReal) s =
      relMapC c '' (QuantumZipper.fwdHull (fun r : ℝ => W' r.toNNReal) (T s) ∩ relDom C))
    (hne : ∀ s : ℝ≥0, 0 < s → γ (T s) ≠ 0 ∧ Γ s ≠ 0) (s : ℝ≥0) (hs : 0 < s) :
    invExt c (-(Γ s)⁻¹) = -(γ (T s))⁻¹ := by
  have hint : ∀ u : ℝ≥0, Γ u ∈ H → invExt c (-(Γ u)⁻¹) = -(γ (T u))⁻¹ := by
    intro u hu
    obtain ⟨hD, he⟩ := relTrace_eq_of_mem_H hc hCo hCH hW' hW'0 hγ hWC hWC0 hΓ hT hTc hK u hu
    have e1 : -(Γ u)⁻¹ = c.1 (-(γ (T u))⁻¹) := by rw [he]; exact negInv_negInv' _
    rw [e1, invExt_eq_of_mem_H hc hCo (hc.2.1 hD), hc.2.2.2.1.1 hD]
  by_cases hΓs : Γ s ∈ H
  · exact hint s hΓs
  have hseq : ∀ n : ℕ, ∃ u : ℝ≥0, s < u ∧ (u : ℝ) < s + 1 / ((n : ℝ) + 1) ∧ Γ u ∈ H :=
    fun n => hdense s _ (by positivity)
  choose u hu1 hu2 hu3 using hseq
  have hut : Tendsto u atTop (𝓝 s) := by
    rw [← NNReal.tendsto_coe]
    have hup : Tendsto (fun n : ℕ => (s : ℝ) + 1 / ((n : ℝ) + 1)) atTop (𝓝 (s : ℝ)) := by
      simpa using (tendsto_const_nhds (x := (s : ℝ))).add tendsto_one_div_add_atTop_nhds_zero_nat
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun n => (hu1 n).le)
      fun n => (hu2 n).le
  have hΓc := continuous_of_isGeneratingTrace_top hΓ
  have hγc := continuous_of_isGeneratingTrace_top hγ
  have hG : Tendsto (fun n => -(γ (T (u n)))⁻¹) atTop (𝓝 (-(γ (T s))⁻¹)) :=
    tendsto_negInv (((hγc.comp hTc).tendsto s).comp hut) (hne s hs).1
  have hHbar : ∀ v : ℝ≥0, Γ v ∈ Hbar := fun v =>
    Sec7.IsGeneratingTrace.mem_Hbar hΓ hWC.continuousOn hWC0 le_top
  have hRΓ : Tendsto (fun n => -(Γ (u n))⁻¹) atTop (𝓝[Hbar] (-(Γ s)⁻¹)) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_negInv ((hΓc.tendsto s).comp hut) (hne s hs).2,
      Eventually.of_forall fun n => negInv_mem_Hbar (hHbar (u n))⟩
  have hF : Tendsto (fun n => invExt c (-(Γ (u n))⁻¹)) atTop (𝓝 (invExt c (-(Γ s)⁻¹))) :=
    ((continuousOn_invExt hc hCo) _ (negInv_mem_Hbar (hHbar s))).tendsto.comp hRΓ
  have heq : (fun n => invExt c (-(Γ (u n))⁻¹)) = fun n => -(γ (T (u n)))⁻¹ :=
    funext fun n => hint _ (hu3 n)
  rw [heq] at hF
  exact tendsto_nhds_unique hF hG

/-- Dense interior times in the form used here, from GB6's rational form `TransientDenseQ`. -/
theorem dense_of_transientDenseQ (hΓ : Supp8.GB6.TransientDenseQ Γ) (s : ℝ≥0) (ε : ℝ) (hε : 0 < ε) :
    ∃ s' : ℝ≥0, s < s' ∧ (s' : ℝ) < s + ε ∧ Γ s' ∈ H := by
  obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn (show (s : ℝ) < s + ε / 2 by linarith)
  obtain ⟨b, hb1, hb2⟩ := exists_rat_btwn (show (s : ℝ) + ε / 2 < s + ε by linarith)
  have ha0 : (0 : ℝ) ≤ a := (NNReal.coe_nonneg s).trans ha1.le
  have hab : a < b := by exact_mod_cast ha2.trans hb1
  obtain ⟨q, hq1, hq2, hqH⟩ := hΓ.2 a b (by exact_mod_cast ha0) hab
  have hq1' : (a : ℝ) < q := by exact_mod_cast hq1
  have hq2' : (q : ℝ) < b := by exact_mod_cast hq2
  have hq0 : (0 : ℝ) ≤ q := ha0.trans hq1'.le
  refine ⟨(q : ℝ).toNNReal, ?_, ?_, hqH⟩
  · rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hq0]
    linarith
  · rw [Real.coe_toNNReal _ hq0]
    linarith

end Trace

/-! ### The traversal -/

/-- **A component traversal from the relative hulls** (deterministic; GW4 proof, "the continuous-trace criterion gives
the actual relative continuous driver and its adapted strictly increasing clock"). Let `W'` (ambient counterflow
driver, chart `R`) and `WC` (relative driver) be continuous from `0` with complete continuous generating traces `γ`
and `Γ`, the interior times of `Γ` dense. If a continuous strictly increasing clock `T` has
* the ambient trace off `closure C` before `T 0` (`R(γ(t)) ∉ closure C`),
* the relative hulls equal to the chart images of the visited parts of the component,
  `K^{WC}_s = Φ(K'_{T s} ∩ R⁻¹(C))` for every `s`,
* `γ(T s) ≠ 0` and `Γ(s) ≠ 0` at positive relative times (neither curve is at its chart's infinity),
then `IsComponentTraversal c.2.1 W' WC`. -/
theorem isComponentTraversal_of_relHulls {R L C : Set ℂ} {c : Chart} (hc : IsComponentChart R L C c)
    (hCo : IsOpen C) (hCH : C ⊆ H) {W' WC : ℝ≥0 → ℝ} {γ Γ : ℝ≥0 → ℂ}
    (hW' : Continuous W') (hW'0 : W' 0 = 0) (hγ : IsGeneratingTrace W' ⊤ γ)
    (hWC : Continuous WC) (hWC0 : WC 0 = 0) (hΓ : IsGeneratingTrace WC ⊤ Γ)
    (hdense : ∀ s : ℝ≥0, ∀ ε : ℝ, 0 < ε → ∃ s' : ℝ≥0, s < s' ∧ (s' : ℝ) < s + ε ∧ Γ s' ∈ H)
    {T : ℝ≥0 → ℝ≥0} (hT : StrictMono T) (hTc : Continuous T)
    (hentry : ∀ t : ℝ≥0, t < T 0 → γ t ≠ 0 → -(γ t)⁻¹ ∉ closure C)
    (hK : ∀ s : ℝ≥0, QuantumZipper.fwdHull (fun r : ℝ => WC r.toNNReal) s =
      relMapC c '' (QuantumZipper.fwdHull (fun r : ℝ => W' r.toNNReal) (T s) ∩ relDom C))
    (hne : ∀ s : ℝ≥0, 0 < s → γ (T s) ≠ 0 ∧ Γ s ≠ 0) :
    IsComponentTraversal c.2.1 W' WC := by
  have hW'r : Continuous fun r : ℝ => W' r.toNNReal := hW'.comp continuous_real_toNNReal
  have hW'r0 : (fun r : ℝ => W' r.toNNReal) 0 = 0 := by simp only [Real.toNNReal_zero, hW'0]
  have hWCr : Continuous fun r : ℝ => WC r.toNNReal := hWC.comp continuous_real_toNNReal
  have hWCr0 : (fun r : ℝ => WC r.toNNReal) 0 = 0 := by simp only [Real.toNNReal_zero, hWC0]
  have hradH : ∀ {V : ℝ → ℝ}, Continuous V → V 0 = 0 → ∀ t : ℝ≥0,
      ∀ᶠ (y : ℝ) in 𝓝[>] (0 : ℝ), QuantumZipper.fwdMapInv V t ((y : ℂ) * I) ∈ H := fun hV hV0 t =>
    (tendsto_radial.eventually self_mem_nhdsWithin).mono fun _ hy =>
      QuantumZipper.RS.fwdMapInv_mem_H hV hV0 (NNReal.coe_nonneg t) hy
  refine ⟨T, hT, hTc, fun t ht z hz => ?_, fun s hs => ?_⟩
  · have hf : Tendsto (fun y : ℝ => QuantumZipper.fwdMapInv (fun r : ℝ => W' r.toNNReal) t ((y : ℂ) * I))
        (𝓝[>] 0) (𝓝 (γ t)) :=
      (IsGeneratingTrace.tendsto_fwdMapInv_tip hγ hW'.continuousOn hW'0 ENNReal.coe_lt_top).comp tendsto_radial
    have hz' : Tendsto (fun y : ℝ => -(QuantumZipper.fwdMapInv (fun r : ℝ => W' r.toNNReal) t ((y : ℂ) * I))⁻¹)
        (𝓝[>] 0) (𝓝 z) := hz
    by_cases hγ0 : γ t = 0
    · exfalso
      have h1 := hf.norm.mul hz'.norm
      rw [hγ0, norm_zero, zero_mul] at h1
      have h2 : ∀ᶠ (y : ℝ) in 𝓝[>] (0 : ℝ),
          (1 : ℝ) = ‖QuantumZipper.fwdMapInv (fun r : ℝ => W' r.toNNReal) t ((y : ℂ) * I)‖ *
            ‖-(QuantumZipper.fwdMapInv (fun r : ℝ => W' r.toNNReal) t ((y : ℂ) * I))⁻¹‖ :=
        (hradH hW'r hW'r0 t).mono fun y hy => by
          rw [norm_neg, norm_inv, mul_inv_cancel₀ (norm_ne_zero_iff.2 (ne_zero_of_mem_H' hy))]
      exact zero_ne_one (tendsto_nhds_unique h1 (tendsto_const_nhds.congr' h2))
    · rw [tendsto_nhds_unique hz' (tendsto_negInv hf hγ0), image_inv_eq hc]
      exact hentry t ht hγ0
  · refine ⟨-(γ (T s))⁻¹, ?_, ?_⟩
    · exact tendsto_negInv ((IsGeneratingTrace.tendsto_fwdMapInv_tip hγ hW'.continuousOn hW'0
        ENNReal.coe_lt_top).comp tendsto_radial) (hne s hs).1
    · have hfC : Tendsto (fun y : ℝ => QuantumZipper.fwdMapInv (fun r : ℝ => WC r.toNNReal) s ((y : ℂ) * I))
          (𝓝[>] 0) (𝓝 (Γ s)) :=
        (IsGeneratingTrace.tendsto_fwdMapInv_tip hΓ hWC.continuousOn hWC0 ENNReal.coe_lt_top).comp
          tendsto_radial
      have hR : Tendsto (fun y : ℝ => -(QuantumZipper.fwdMapInv (fun r : ℝ => WC r.toNNReal) s ((y : ℂ) * I))⁻¹)
          (𝓝[>] 0) (𝓝[H] (-(Γ s)⁻¹)) :=
        tendsto_nhdsWithin_iff.2 ⟨tendsto_negInv hfC (hne s hs).2,
          (hradH hWCr hWCr0 s).mono fun _ hy => negInv_mem_H' hy⟩
      have hHbar : Γ s ∈ Hbar := Sec7.IsGeneratingTrace.mem_Hbar hΓ hWC.continuousOn hWC0 le_top
      have h := (tendsto_invExt hc hCo (negInv_mem_Hbar hHbar)).comp hR
      rw [invExt_relTrace_eq hc hCo hCH hW' hW'0 hγ hWC hWC0 hΓ hdense hT hTc hK hne s hs] at h
      exact h

end GW4Traverse

end Theorem14

end InteractingSLE
