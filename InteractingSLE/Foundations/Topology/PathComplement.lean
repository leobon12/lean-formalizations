import InteractingSLE.Foundations.Loewner.HullBasic
import InteractingSLE.Foundations.Topology.PathComplement.Basic
import InteractingSLE.Foundations.Topology.PathComplement.Torhorst

/-!
# Conformal maps onto complements of filled paths extend continuously

Packet GEO-CARA of `planning/INFRA-GEO.md` §4. The boundary extension used by the specification
for the complement of a filled continuous path (pp. 65, 70, 89, 148, 291, 333, 356, 381, …, citing
J. Luo and J. M. Thuswaldner, *On the fundamental group of self-affine plane tiles*, Ann. Inst.
Fourier 56 (2006), Propositions 3.3 and 3.9, `source/external/LT06/LT06.md`).

## Design correction

The design statement (`INFRA-GEO-Core.lean`, `exists_continuousOn_extension_of_path`) assumes only
that `ψ` is a conformal bijection of `ℍ` onto `ℍ \ fill(γ[0,t])`. That is false: a conformal
self-map of `ℍ` may send a real point to `∞`, and then no finite continuous extension exists
(`not_forall_exists_continuousOn_extension_of_path`: the constant path `γ = 0`, `t = 0`, and
`ψ(z) = -1/z`). Every use in the specification is an inverse hydrodynamic (mapping-out) map, which
fixes `∞`. The corrected statement `exists_continuousOn_extension_of_path_of_tendsto` adds the
normalization `ψ(z) → ∞` as `z → ∞` in `ℍ` and also gives `F(z) → ∞` as `z → ∞` in `ℍ̄`.

## Main results

* `isOpen_H_diff_fillH`, `frontier_H_diff_fillH_subset`: `ℍ \ fill(A)` is open with boundary in
  `ℝ ∪ closure A`.
* `not_isSimplyConnected_H_diff_fillH`: if a nonempty compact `K` stays inside `ℍ`, then
  `ℍ \ fill(K)` is not simply connected (so it is not conformally equivalent to `ℍ`).
* `exists_continuousOn_extension_of_ulc_fillH`: the extension theorem for `ℍ \ fill(K)`, `K ⊆ ℍ̄`
  compact and uniformly locally connected with `ℝ ∪ K` connected (finite unions of paths started on
  `ℝ`, for instance).
* `exists_continuousOn_extension_of_path_of_tendsto`: the path case.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology

open SupercriticalConformalCovariance (IsConformalBijection)
open QuantumZipper (H Hbar)
open QuantumZipper.CA.Topo (ULC)

namespace InteractingSLE

/-! ### The complement of a filling -/

/-- `ℍ \ fill(A)` is open for bounded `A` (it is a component of the open set `ℍ \ closure A`). -/
theorem isOpen_H_diff_fillH {A : Set ℂ} (hA : Bornology.IsBounded A) : IsOpen (H \ fillH A) := by
  obtain ⟨R, hR, hAR⟩ := exists_closure_subset_ball hA
  rw [H_diff_fillH hR hAR]
  exact (QuantumZipper.isOpen_H.sdiff isClosed_closure).connectedComponentIn

theorem disjoint_H_diff_fillH_closure (A : Set ℂ) : Disjoint (H \ fillH A) (closure A) :=
  Set.disjoint_left.2 fun _ hz hzA => hz.2 ⟨hz.1, Or.inl hzA⟩

/-- The boundary of `ℍ \ fill(A)` lies in `ℝ ∪ closure A`. -/
theorem frontier_H_diff_fillH_subset {A : Set ℂ} (hA : Bornology.IsBounded A) :
    frontier (H \ fillH A) ⊆ {z : ℂ | z.im = 0} ∪ closure A := by
  intro z hz
  rw [(isOpen_H_diff_fillH hA).frontier_eq] at hz
  obtain ⟨hzc, hzU⟩ := hz
  have hzb : z ∈ Hbar := by
    rw [← QuantumZipper.CA.Car.closure_H_eq_Hbar]; exact closure_mono sdiff_subset hzc
  rcases (show (0 : ℝ) ≤ z.im from hzb).eq_or_lt with h0 | hpos
  · exact Or.inl h0.symm
  by_contra hcon
  have hzA : z ∉ closure A := fun h => hcon (Or.inr h)
  have hzf : z ∈ fillH A := by
    by_contra h; exact hzU ⟨hpos, h⟩
  rcases hzf.2 with h | hb
  · exact hzA h
  have hWo : IsOpen (connectedComponentIn (H \ closure A) z) :=
    (QuantumZipper.isOpen_H.sdiff isClosed_closure).connectedComponentIn
  obtain ⟨u, huW, huU⟩ :=
    mem_closure_iff.1 hzc _ hWo (mem_connectedComponentIn (show z ∈ H \ closure A from ⟨hpos, hzA⟩))
  rw [connectedComponentIn_eq huW] at hb
  exact huU.2 ⟨huU.1, Or.inr hb⟩

/-- The upper half-plane is simply connected (it is convex). -/
theorem isSimplyConnected_H : IsSimplyConnected H := by
  have : ContractibleSpace H :=
    (convex_halfSpace_gt (f := fun w : ℂ => w.im) Complex.imLm.isLinear 0).contractibleSpace
      ⟨I, show (0 : ℝ) < I.im by simp⟩
  exact SimplyConnectedSpace.ofContractible _

/-- If a nonempty compact `K` lies in `ℍ`, the filling of `K` is a bounded component of the
complement of `ℍ \ fill(K)`, so `ℍ \ fill(K)` is not simply connected. -/
theorem not_isSimplyConnected_H_diff_fillH {K : Set ℂ} (hK : IsCompact K) (hne : K.Nonempty)
    (hKH : K ⊆ H) : ¬ IsSimplyConnected (H \ fillH K) := by
  intro hsc
  obtain ⟨a, haK, hmin⟩ := hK.exists_isMinOn hne Complex.continuous_im.continuousOn
  have hm : 0 < a.im := hKH haK
  have hUo := isOpen_H_diff_fillH hK.isBounded
  have hKc : closure K = K := hK.isClosed.closure_eq
  have hlow : ∀ w ∈ K, a.im ≤ w.im := fun w hw => hmin hw
  have haU : a ∉ H \ fillH K := fun h => h.2 ⟨hKH haK, Or.inl (subset_closure haK)⟩
  have hunb := not_isBounded_connectedComponentIn_compl_of_isSimplyConnected hUo hsc haU
  obtain ⟨R, hR, hKR⟩ := exists_closure_subset_ball hK.isBounded
  -- the strip `0 < Im < a.im` lies in `ℍ \ fill(K)`
  set S : Set ℂ := {w | 0 < w.im} ∩ {w | w.im < a.im} with hS
  have hSc : IsPreconnected S :=
    ((convex_halfSpace_gt (f := fun w : ℂ => w.im) Complex.imLm.isLinear 0).inter
      (convex_halfSpace_lt (f := fun w : ℂ => w.im) Complex.imLm.isLinear a.im)).isPreconnected
  have hSsub : S ⊆ H \ closure K := fun w hw =>
    ⟨hw.1, by rw [hKc]; exact fun h => absurd (hlow w h) (not_le.2 hw.2)⟩
  have hSunb : ¬ Bornology.IsBounded S := by
    intro hb
    obtain ⟨r, hr⟩ := hb.subset_closedBall 0
    have hmem : ((|r| + 1 : ℝ) : ℂ) + ((a.im / 2 : ℝ) : ℂ) * I ∈ S := by
      refine ⟨?_, ?_⟩ <;> simp only [mem_ofPred_eq, add_im, ofReal_im, mul_im, ofReal_re, I_im,
        mul_one, I_re, mul_zero, add_zero, zero_add] <;> linarith
    have h1 := mem_closedBall_zero_iff.1 (hr hmem)
    have h2 := Complex.abs_re_le_norm (((|r| + 1 : ℝ) : ℂ) + ((a.im / 2 : ℝ) : ℂ) * I)
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
      sub_self, add_zero] at h2
    rw [abs_of_pos (by positivity)] at h2
    linarith [le_abs_self r]
  have hstrip : ∀ z ∈ S, z ∈ H \ fillH K := by
    intro z hz
    refine ⟨hz.1, fun hzf => ?_⟩
    rcases hzf.2 with h | hb
    · exact (hSsub hz).2 h
    · exact hSunb (hb.subset (hSc.subset_connectedComponentIn hz hSsub))
  -- the component of `a` in the complement stays in `{Im > a.im / 2}`, hence in `fill(K)`
  have hQsub : connectedComponentIn (H \ fillH K)ᶜ a ⊆ {w : ℂ | a.im / 2 < w.im} := by
    refine IsPreconnected.subset_left_of_subset_union (v := {w : ℂ | w.im < a.im / 2})
      (isOpen_lt continuous_const Complex.continuous_im)
      (isOpen_lt Complex.continuous_im continuous_const) ?_ ?_
      ⟨a, mem_connectedComponentIn haU, show a.im / 2 < a.im by linarith⟩
      isPreconnected_connectedComponentIn
    · exact Set.disjoint_left.2 fun w (h1 : a.im / 2 < w.im) (h2 : w.im < a.im / 2) => by linarith
    · intro w hw
      have hwU : w ∉ H \ fillH K := connectedComponentIn_subset _ _ hw
      rcases lt_trichotomy w.im (a.im / 2) with h | h | h
      · exact Or.inr h
      · exact absurd (hstrip w ⟨show 0 < w.im by linarith, show w.im < a.im by linarith⟩) hwU
      · exact Or.inl h
  refine hunb ((Metric.isBounded_ball (x := (0 : ℂ)) (r := R)).subset fun w hw => ?_)
  have hwU : w ∉ H \ fillH K := connectedComponentIn_subset _ _ hw
  have hwH : w ∈ H := show 0 < w.im by have := hQsub hw; simp only [mem_ofPred_eq] at this; linarith
  exact fillH_subset_ball hR hKR (by by_contra h; exact hwU ⟨hwH, h⟩)

/-! ### The extension theorem for fillings -/

/-- **Continuous extension onto the complement of a filling.** For `K ⊆ ℍ̄` compact and uniformly
locally connected with `ℝ ∪ K` connected, a conformal bijection `ψ : ℍ → ℍ \ fill(K)` with
`ψ(z) → ∞` as `z → ∞` extends continuously to `ℍ̄`, with real boundary values in
`∂(ℍ \ fill(K))` and `F(z) → ∞` as `z → ∞` in `ℍ̄`. -/
theorem exists_continuousOn_extension_of_ulc_fillH {K : Set ℂ} (hK : IsCompact K)
    (hKH : K ⊆ Hbar) (hKu : ULC K) (hKc : IsPreconnected ({z : ℂ | z.im = 0} ∪ K)) {ψ : ℂ → ℂ}
    (hψ : IsConformalBijection ψ H (H \ fillH K))
    (hψi : Tendsto ψ (Bornology.cobounded ℂ ⊓ 𝓟 H) (Bornology.cobounded ℂ)) :
    ∃ F : ℂ → ℂ, EqOn F ψ H ∧ ContinuousOn F Hbar ∧
      MapsTo F (Hbar \ H) (frontier (H \ fillH K)) ∧
      Tendsto F (Bornology.cobounded ℂ ⊓ 𝓟 Hbar) (Bornology.cobounded ℂ) := by
  have hKc' : closure K = K := hK.isClosed.closure_eq
  refine exists_continuousOn_extension_of_ulc (isOpen_H_diff_fillH hK.isBounded) sdiff_subset
    ?_ ?_ hK hKH hKu hKc hψ hψi
  · simpa only [hKc'] using frontier_H_diff_fillH_subset hK.isBounded
  · simpa only [hKc'] using disjoint_H_diff_fillH_closure K

/-- The range of a continuous path on `[0, t]` is uniformly locally connected. -/
theorem ulc_image_Icc {γ : ℝ → ℂ} {t : ℝ} (hγ : ContinuousOn γ (Icc 0 t)) :
    ULC (γ '' Icc 0 t) := by
  rcases lt_or_ge t 0 with ht | ht
  · rw [Icc_eq_empty (not_le.2 ht), image_empty]
    exact fun _ _ => ⟨1, one_pos, fun _ ha => ha.elim⟩
  have hmaps : MapsTo (fun s : ℝ => t * s) (Icc 0 1) (Icc 0 t) := fun s hs =>
    ⟨mul_nonneg ht hs.1, mul_le_of_le_one_right ht hs.2⟩
  have himg : γ '' Icc 0 t = (fun s => γ (t * s)) '' Icc 0 1 := by
    rw [show (fun s => γ (t * s)) = γ ∘ (fun s : ℝ => t * s) from rfl, image_comp]
    congr 1
    refine Subset.antisymm (fun x hx => ?_) (image_subset_iff.2 hmaps)
    rcases ht.eq_or_lt with h0 | hpos
    · subst h0
      exact ⟨0, ⟨le_rfl, zero_le_one⟩, by
        have := le_antisymm hx.2 hx.1; simp [this]⟩
    · exact ⟨x / t, ⟨div_nonneg hx.1 ht, (div_le_one hpos).2 hx.2⟩, by
        show t * (x / t) = x; field_simp⟩
  rw [himg]
  exact QuantumZipper.CA.Topo.ULC.image_Icc
    (hγ.comp (continuousOn_const.mul continuousOn_id) hmaps)

/-- **Boundary extension for path complements** (corrected form of the design's
`exists_continuousOn_extension_of_path`; specification pp. 65, 70, 89, 148, 291, 333, 356, 381;
[LT06] Propositions 3.3 and 3.9; [Pom] Thm 2.1). For a continuous path `γ` in `ℍ̄` and a conformal
map `ψ` of `ℍ` onto `ℍ \ fill(γ[0,t])` with `ψ(z) → ∞` as `z → ∞` (for instance the inverse of
a mapping-out function), `ψ` extends to a map `F`, continuous on `ℍ̄`, with real boundary values in
`∂(ℍ \ fill(γ[0,t]))` and `F(z) → ∞` as `z → ∞` in `ℍ̄`. -/
theorem exists_continuousOn_extension_of_path_of_tendsto {γ : ℝ → ℂ} {t : ℝ}
    (hγ : ContinuousOn γ (Icc 0 t)) (hγH : MapsTo γ (Icc 0 t) Hbar) {ψ : ℂ → ℂ}
    (hψ : IsConformalBijection ψ H (H \ fillH (γ '' Icc 0 t)))
    (hψi : Tendsto ψ (Bornology.cobounded ℂ ⊓ 𝓟 H) (Bornology.cobounded ℂ)) :
    ∃ F : ℂ → ℂ, EqOn F ψ H ∧ ContinuousOn F Hbar ∧
      MapsTo F (Hbar \ H) (frontier (H \ fillH (γ '' Icc 0 t))) ∧
      Tendsto F (Bornology.cobounded ℂ ⊓ 𝓟 Hbar) (Bornology.cobounded ℂ) := by
  have hK : IsCompact (γ '' Icc 0 t) := isCompact_Icc.image_of_continuousOn hγ
  have hKpc : IsPreconnected (γ '' Icc 0 t) := isPreconnected_Icc.image _ hγ
  refine exists_continuousOn_extension_of_ulc_fillH hK hγH.image_subset (ulc_image_Icc hγ) ?_
    hψ hψi
  have hR := QuantumZipper.CA.Uniformizer.isPreconnected_setOf_im_eq_zero
  by_cases hmeet : ({z : ℂ | z.im = 0} ∩ γ '' Icc 0 t).Nonempty
  · exact hR.union' hmeet hKpc
  rcases (γ '' Icc 0 t).eq_empty_or_nonempty with h | hne
  · rw [h, union_empty]; exact hR
  exfalso
  have hKH : γ '' Icc 0 t ⊆ H := fun z hz =>
    lt_of_le_of_ne (hγH.image_subset hz) fun h => hmeet ⟨z, h.symm, hz⟩
  exact not_isSimplyConnected_H_diff_fillH hK hne hKH
    (isSimplyConnected_of_isConformalBijection QuantumZipper.isOpen_H hψ isSimplyConnected_H)

/-! ### The design statement is false -/

/-- A set whose closure misses `ℍ` has empty filling. -/
theorem fillH_eq_empty_of_disjoint {A : Set ℂ} (hA : Disjoint (closure A) H) : fillH A = ∅ := by
  refine eq_empty_of_forall_notMem fun z hz => ?_
  rcases hz.2 with h | hb
  · exact Set.disjoint_left.1 hA h hz.1
  · have hHc : IsPreconnected H :=
      (convex_halfSpace_gt (f := fun w : ℂ => w.im) Complex.imLm.isLinear 0).isPreconnected
    rw [sdiff_eq_left.2 hA.symm, hHc.connectedComponentIn hz.1] at hb
    exact not_isBounded_setOf_lt_im 0 hb

/-- **The design's `exists_continuousOn_extension_of_path` is false**: without a normalization at
`∞`, `ψ` may send a real point to `∞`. Counterexample: the constant path `γ = 0` on `[0, 1]` (its
filling is empty, so `ℍ \ fill = ℍ`) and `ψ(z) = -1/z`, which tends to `∞` at `0`. -/
theorem not_forall_exists_continuousOn_extension_of_path :
    ¬ ∀ (γ : ℝ → ℂ) (t : ℝ), ContinuousOn γ (Icc 0 t) → MapsTo γ (Icc 0 t) Hbar →
      ∀ ψ : ℂ → ℂ, IsConformalBijection ψ H (H \ fillH (γ '' Icc 0 t)) →
        ∃ F : ℂ → ℂ, EqOn F ψ H ∧ ContinuousOn F Hbar ∧
          MapsTo F (Hbar \ H) (frontier (H \ fillH (γ '' Icc 0 t))) := by
  intro h
  have hfill : fillH ((fun _ : ℝ => (0 : ℂ)) '' Icc 0 1) = ∅ := by
    rw [(nonempty_Icc.2 zero_le_one).image_const]
    refine fillH_eq_empty_of_disjoint ?_
    rw [closure_singleton, disjoint_singleton_left]
    exact fun h => lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from h)
  have hconf : IsConformalBijection (fun z : ℂ => -z⁻¹) H
      (H \ fillH ((fun _ : ℝ => (0 : ℂ)) '' Icc 0 1)) := by
    rw [hfill, sdiff_empty]
    have hne : ∀ z ∈ H, z ≠ 0 := fun z hz h0 => by
      rw [h0] at hz; exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from hz)
    have himH : ∀ z ∈ H, -z⁻¹ ∈ H := fun z hz => by
      show 0 < (-z⁻¹).im
      rw [neg_im, inv_im, neg_div, neg_neg]
      exact div_pos hz (normSq_pos.2 (hne z hz))
    refine ⟨fun z hz => ((differentiableAt_inv (hne z hz)).neg).differentiableWithinAt,
      himH, fun z _ w _ hzw => ?_, fun w hw => ⟨-w⁻¹, himH w hw, by simp⟩⟩
    simpa using hzw
  obtain ⟨F, hEq, hF, -⟩ := h (fun _ => 0) 1 continuousOn_const
    (fun _ _ => show (0 : ℝ) ≤ (0 : ℂ).im by simp) _ hconf
  -- `F` is continuous at `0 ∈ ℍ̄`, but `-1/z → ∞` as `z → 0` in `ℍ`
  have h0 : (0 : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (0 : ℂ).im by simp
  have hcl : (𝓝[H] (0 : ℂ)).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, QuantumZipper.CA.Car.closure_H_eq_Hbar]; exact h0
  have hlim : Tendsto F (𝓝[H] (0 : ℂ)) (𝓝 (F 0)) :=
    (hF 0 h0).tendsto.mono_left (nhdsWithin_mono _ QuantumZipper.H_subset_Hbar)
  have hinf : Tendsto F (𝓝[H] (0 : ℂ)) (Bornology.cobounded ℂ) := by
    have h1 : Tendsto (fun z : ℂ => -z⁻¹) (𝓝[≠] (0 : ℂ)) (Bornology.cobounded ℂ) :=
      tendsto_neg_cobounded.comp tendsto_inv₀_nhdsNE_zero
    have h2 : 𝓝[H] (0 : ℂ) ≤ 𝓝[≠] 0 := nhdsWithin_mono _ fun z hz h0 => by
      rw [mem_singleton_iff.1 h0] at hz; exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from hz)
    refine (h1.mono_left h2).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz using (hEq hz).symm
  exact not_tendsto_nhds_of_tendsto_atTop (tendsto_norm_cobounded_atTop.comp hinf) ‖F 0‖
    (continuous_norm.tendsto _ |>.comp hlim)

end InteractingSLE
