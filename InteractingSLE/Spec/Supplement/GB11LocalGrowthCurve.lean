/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB11LocalGrowth
import InteractingSLE.Foundations.Loewner.YuanCharacterisationMarkov

/-!
# Lemma GB11's relative trace and Yuan's criterion

Packet PROVE-T14-GW4T5, item (1b), the reduction to the continuous own future. The named input
`GB11RelLoewnerStatement` (`GB11LocalGrowth`: the relative hulls `B u = Φ(K'_{τ+u} ∩ R⁻¹(C))` are Loewner hulls on every
compact time interval) is proved from **`GB11RelOwnFutureStatement`**: the relative trace `ζ` of the traversal — at each
relative time `u`, the point of `ℍ̄` at which the inverse relative chart `Φ⁻¹ = relInvC c` tends to the ambient trace
point `γ(τ + u)` (`IsRelCurve`) — has continuous own futures (`YuanCharacterisation.HasContinuousOwnFuture`, property
(ii) of [Yua22, Theorem 1.1]; the source's "relative continuity by the continuous-trace criterion of Aux. lemma 41 /
Proposition 6.12").

## The argument

* **The relative trace exists and is continuous** (`exists_relCurve`, `relPt`): with the pocket coordinate of
  `GB11ChartBdry` (`IsPocketCoord`: `c⁻¹(w) = G(k w)`, `ψ ∘ G = id`), `ζ(u) = −k/ψ(−1/γ(τ + u))`, and `ζ(u) = 0` at the
  entry. It starts at `0` and stays in `ℍ̄`.
* **The fill identity** (in `exists_relCurve`): `fill(ζ([0, u])) = B u` (`fillH_eq_of_frontier`): the interior points
  of `ζ` are chart images of trace points of the ambient hull, `ℍ \ B u` is open, preconnected ((GB11.2),
  `GB11Conn.isPreconnected_relDom_diff_fwdHull`) and unbounded, and every frontier point of `B u` in `ℍ` is on `ζ`: it
  is the chart image of a frontier point of the ambient hull inside `R⁻¹(C)`, i.e. of a trace point after the entry,
  and the boundary limits of `Φ⁻¹` at real points lie on the walls (`ChartBdryCorr`), off `R⁻¹(C)`.
* **Strict growth** from the open-`C` visits (`GW4Reg.exists_mem_relDom_fwdHull_sdiff`).
* **Yuan's theorem** (`YuanCharacterisation.exists_loewner_of_hasContinuousOwnFuture`) then gives the Loewner
  representation on `[0, T]`.

## Main results

* `IsRelCurve`, `GB11RelOwnFutureStatement` (named input);
* `fillH_eq_of_frontier` (planar), `relPt` (`tendsto_relInvC_relPt`, `continuousOn_relPt`), `exists_relCurve`;
* **`gb11RelLoewnerStatement_of_ownFuture`**, `gb11RelLocalGrowthStatement_of_ownFuture`,
  `gb11RelParamStatement_of_ownFuture`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Bornology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull)

namespace InteractingSLE

namespace Theorem14

namespace GB11Chart

open GW4Traverse GW4Reg GB11Conn

/-! ### The trace and the frontier of its hulls -/

section TraceHull

variable {W' : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ}

/-- A trace point in `ℍ` is in the hull from its time on. -/
theorem mem_fwdHull_of_isGeneratingTrace (hγ : IsGeneratingTrace W' ⊤ γ) {t t' : ℝ≥0} (htt' : t ≤ t')
    (htH : γ t ∈ H) : γ t ∈ fwdHull (fun r : ℝ => W' r.toNNReal) (t' : ℝ) := by
  obtain ⟨⟨z, -, hz⟩, -⟩ := hγ.2.2 t ENNReal.coe_lt_top
  have h1 : γ t ∈ fwdHull (fun r : ℝ => W' r.toNNReal) (t : ℝ) := by
    by_contra hn
    have : γ t ∈ connectedComponentIn (H \ γ '' Icc 0 t) z := by rw [hz]; exact ⟨htH, hn⟩
    exact (connectedComponentIn_subset _ _ this).2 ⟨t, ⟨zero_le, le_rfl⟩, rfl⟩
  exact (QuantumZipper.fwdHull_mono.1 (NNReal.coe_le_coe.2 htt')) h1

/-- A frontier point of the hull inside `ℍ` is a trace point. -/
theorem mem_image_of_mem_closure_compl (hγ : IsGeneratingTrace W' ⊤ γ) {t : ℝ≥0} {w : ℂ}
    (hwK : w ∈ fwdHull (fun r : ℝ => W' r.toNNReal) (t : ℝ))
    (hwcl : w ∈ closure (H \ fwdHull (fun r : ℝ => W' r.toNNReal) (t : ℝ))) (hwH : w ∈ H) :
    w ∈ γ '' Icc 0 t := by
  obtain ⟨⟨z, -, hz⟩, -⟩ := hγ.2.2 t ENNReal.coe_lt_top
  by_contra hn
  have h1 : w ∈ connectedComponentIn (H \ γ '' Icc 0 t) z :=
    GB11Conn.mem_connectedComponentIn_of_mem_closure (by rw [hz]; exact hwcl) ⟨hwH, hn⟩
  rw [hz] at h1
  exact h1.2 hwK

end TraceHull

/-! ### The fill identity (planar) -/

/-- `ℍ` is unbounded. -/
theorem not_isBounded_H : ¬ IsBounded H := by
  intro hb
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.1 hb
  have h := hM (((|M| + 1 : ℝ) : ℂ) * Complex.I) (show (0 : ℝ) < _ by simp; positivity)
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at h
  linarith [le_abs_self M]

/-- **The filling of a closed set `S` is a set `B`** when `B ⊆ ℍ` is bounded with `ℍ \ B` open and preconnected, the
points of `S` in `ℍ` lie in `B`, and every point of `B` in the closure of `ℍ \ B` lies on `S`. -/
theorem fillH_eq_of_frontier {B S : Set ℂ} (hBH : B ⊆ H) (hBb : IsBounded B) (hO : IsOpen (H \ B))
    (hOc : IsPreconnected (H \ B)) (hS : IsClosed S) (hSB : S ∩ H ⊆ B)
    (hfr : ∀ q ∈ B, q ∈ closure (H \ B) → q ∈ S) : fillH S = B := by
  have hOu : ¬ IsBounded (H \ B) := fun h => not_isBounded_H ((h.union hBb).subset fun z hz => by
    by_cases hzB : z ∈ B
    · exact Or.inr hzB
    · exact Or.inl ⟨hz, hzB⟩)
  have hOS : H \ B ⊆ H \ closure S := by
    intro z hz
    refine ⟨hz.1, fun hzS => hz.2 (hSB ⟨?_, hz.1⟩)⟩
    rwa [hS.closure_eq] at hzS
  ext z
  constructor
  · rintro ⟨hzH, hzS | hzb⟩
    · rw [hS.closure_eq] at hzS; exact hSB ⟨hzS, hzH⟩
    · by_contra hzB
      have hsub : H \ B ⊆ connectedComponentIn (H \ closure S) z :=
        hOc.subset_connectedComponentIn ⟨hzH, hzB⟩ hOS
      exact hOu (hzb.subset hsub)
  · intro hzB
    refine ⟨hBH hzB, ?_⟩
    by_cases hzS : z ∈ closure S
    · exact Or.inl hzS
    right
    rw [hS.closure_eq] at hzS
    have hzO : z ∉ closure (H \ B) := fun h => hzS (hfr z hzB h)
    set V := connectedComponentIn (H \ closure S) z with hV
    have hVsub : V ⊆ (closure (H \ B))ᶜ := by
      have hVc : IsPreconnected V := isPreconnected_connectedComponentIn
      have hzV : z ∈ V := mem_connectedComponentIn ⟨hBH hzB, by rwa [hS.closure_eq]⟩
      refine hVc.subset_left_of_subset_union isClosed_closure.isOpen_compl hO ?_ (fun y hy => ?_)
        ⟨z, hzV, hzO⟩
      · exact disjoint_compl_left.mono_right subset_closure
      · have hyH : y ∈ H := (connectedComponentIn_subset _ _ hy).1
        have hyS : y ∉ S := fun h => (connectedComponentIn_subset _ _ hy).2 (by rwa [hS.closure_eq])
        by_cases hyB : y ∈ B
        · exact Or.inl fun hcl => hyS (hfr y hyB hcl)
        · exact Or.inr ⟨hyH, hyB⟩
    refine hBb.subset fun y hy => ?_
    have hyH : y ∈ H := (connectedComponentIn_subset _ _ hy).1
    by_contra hyB
    exact hVsub hy (subset_closure ⟨hyH, hyB⟩)

/-! ### The relative point of a counterflow-chart point -/

/-- **The relative point** of a counterflow-chart point `w` (physical point `−1/w ∈ C̄`): `Φ̄(w) = −k/ψ(−1/w)`, and `0`
at the entry (`−1/w ∈ E`, or `w = 0`, the physical source `∞`). -/
def relPt (E : Set ℂ) (ψ : ℂ → ℂ) (k : ℝ) (w : ℂ) : ℂ :=
  open scoped Classical in if w = 0 ∨ -w⁻¹ ∈ E then 0 else -(k : ℂ) * (ψ (-w⁻¹))⁻¹

/-- The counterflow-chart points of the closed pocket without its exit `P` (and `0`, the physical `∞`, for the
unbounded pocket `E = ∅`). -/
def relDomBar (C E : Set ℂ) (P : ℂ) : Set ℂ :=
  {w | (w = 0 ∧ E = ∅) ∨ (w ≠ 0 ∧ -w⁻¹ ∈ closure C ∧ -w⁻¹ ≠ P)}

section RelPt

variable {αR αL : ℝ≥0 → ℂ} {C : Set ℂ} {c : Chart} {s₁ t₁ : ℝ≥0} {E : Set ℂ} {ψ G : ℂ → ℂ} {k : ℝ}

theorem negInv_inv_mem_Hbar {k : ℝ} (hk : 0 < k) {z : ℂ} (hz : z ∈ Hbar) : -(k : ℂ) * z⁻¹ ∈ Hbar := by
  show (0 : ℝ) ≤ (-(k : ℂ) * z⁻¹).im
  simp only [neg_mul, Complex.neg_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    add_zero, Complex.inv_im]
  have hz' : (0 : ℝ) ≤ z.im := hz
  have : 0 ≤ k * (z.im / Complex.normSq z) := mul_nonneg hk.le (div_nonneg hz' (Complex.normSq_nonneg z))
  linarith [show k * (-z.im / Complex.normSq z) = -(k * (z.im / Complex.normSq z)) by ring]

/-- `ψ` vanishes only at the exit. -/
theorem IsPocketCoord.ψ_ne_zero (hpc : IsPocketCoord αR αL C c s₁ t₁ E ψ G k) {z : ℂ} (hz : z ∈ closure C \ E)
    (hzP : z ≠ αR s₁) : ψ z ≠ 0 := fun h => hzP (by rw [← hpc.right_inv z hz, h, hpc.G_zero])

theorem relPt_mem_Hbar (hpc : IsPocketCoord αR αL C c s₁ t₁ E ψ G k) {w : ℂ} (hw : w ∈ relDomBar C E (αR s₁)) :
    relPt E ψ k w ∈ Hbar := by
  unfold relPt
  split_ifs with h
  · show (0 : ℝ) ≤ (0 : ℂ).im; simp
  · push Not at h
    rcases hw with ⟨rfl, -⟩ | ⟨-, hcl, -⟩
    · exact absurd rfl h.1
    · exact negInv_inv_mem_Hbar hpc.pos (hpc.mapsTo_ψ ⟨hcl, h.2⟩)

/-- `−v⁻¹ ↦ k(−v⁻¹)` carries `𝓝[ℍ] 0` to `∞` within `ℍ`. -/
theorem tendsto_mul_negInv_zero {k : ℝ} (hk : 0 < k) :
    Tendsto (fun v : ℂ => (k : ℂ) * -v⁻¹) (𝓝[H] 0) (cobounded ℂ ⊓ 𝓟 H) := by
  have h0 := GW3.tendsto_neg_inv_nhdsWithin_zero
  have hmul : Tendsto (fun w : ℂ => (k : ℂ) * w) (cobounded ℂ ⊓ 𝓟 H) (cobounded ℂ ⊓ 𝓟 H) :=
    tendsto_inf.2 ⟨(tendsto_mul_left_cobounded (Complex.ofReal_ne_zero.2 hk.ne')).mono_left inf_le_left,
      tendsto_principal.2 (mem_inf_of_right (mem_principal.2 fun w hw => by
        show (0 : ℝ) < ((k : ℂ) * w).im
        simpa [Complex.mul_im] using mul_pos hk hw))⟩
  exact hmul.comp h0

/-- `relInvC c (v) = −1/G(k(−1/v))` on `ℍ`. -/
theorem relInvC_eq (hpc : IsPocketCoord αR αL C c s₁ t₁ E ψ G k) {v : ℂ} (hv : v ∈ H) :
    relInvC c v = -(G ((k : ℂ) * -v⁻¹))⁻¹ := by
  simp only [relInvC]
  rw [hpc.inv_eq _ (negInv_mem_H' hv)]

/-- **The inverse relative chart tends at the relative point to the counterflow-chart point.** -/
theorem tendsto_relInvC_relPt (hpc : IsPocketCoord αR αL C c s₁ t₁ E ψ G k) (hE0 : (0 : ℂ) ∉ E)
    (hGE : ∀ Q ∈ E, Tendsto G (cobounded ℂ ⊓ 𝓟 H) (𝓝 Q))
    (hGinf : E = ∅ → Tendsto G (cobounded ℂ ⊓ 𝓟 H) (cobounded ℂ)) {w : ℂ}
    (hw : w ∈ relDomBar C E (αR s₁)) :
    Tendsto (relInvC c) (𝓝[H] (relPt E ψ k w)) (𝓝 w) := by
  have hcongr : ∀ {l : Filter ℂ}, l ≤ 𝓟 H → ∀ {y : ℂ},
      Tendsto (fun v => -(G ((k : ℂ) * -v⁻¹))⁻¹) l (𝓝 y) → Tendsto (relInvC c) l (𝓝 y) :=
    fun hl _ h => h.congr' (Filter.mem_of_superset (hl (mem_principal_self H)) fun v hv => (relInvC_eq hpc hv).symm)
  rcases hw with ⟨rfl, hE⟩ | ⟨hw0, hcl, hP⟩
  · -- the physical source `∞` of the unbounded pocket
    have h0 : relPt E ψ k 0 = 0 := by simp [relPt]
    rw [h0]
    refine hcongr (le_principal_iff.2 self_mem_nhdsWithin) ?_
    simpa using ((tendsto_inv₀_cobounded.comp ((hGinf hE).comp (tendsto_mul_negInv_zero hpc.pos))).neg)
  by_cases hzE : -w⁻¹ ∈ E
  · -- the entry of a bounded pocket
    have h0 : relPt E ψ k w = 0 := by simp [relPt, hzE]
    rw [h0]
    have hz0 : -w⁻¹ ≠ 0 := fun h => hE0 (h ▸ hzE)
    refine hcongr (le_principal_iff.2 self_mem_nhdsWithin) ?_
    have := (((hGE _ hzE).comp (tendsto_mul_negInv_zero hpc.pos)).inv₀ hz0).neg
    rwa [negInv_negInv'] at this
  · -- an interior or wall point
    have hzm : -w⁻¹ ∈ closure C \ E := ⟨hcl, hzE⟩
    have hψ0 := hpc.ψ_ne_zero hzm hP
    have hval : relPt E ψ k w = -(k : ℂ) * (ψ (-w⁻¹))⁻¹ := by
      unfold relPt
      simp only [hw0, false_or, hzE, ↓reduceIte]
    rw [hval]
    have hk0 : (k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hpc.pos.ne'
    have hv0 : -(k : ℂ) * (ψ (-w⁻¹))⁻¹ ≠ 0 := mul_ne_zero (neg_ne_zero.2 hk0) (inv_ne_zero hψ0)
    have hpt : (k : ℂ) * -(-(k : ℂ) * (ψ (-w⁻¹))⁻¹)⁻¹ = ψ (-w⁻¹) := by field_simp
    have hcont : ContinuousAt (fun v : ℂ => (k : ℂ) * -v⁻¹) (-(k : ℂ) * (ψ (-w⁻¹))⁻¹) :=
      continuousAt_const.mul ((continuousAt_inv₀ hv0).neg)
    have h1 : Tendsto (fun v : ℂ => (k : ℂ) * -v⁻¹) (𝓝[H] (-(k : ℂ) * (ψ (-w⁻¹))⁻¹)) (𝓝[Hbar] (ψ (-w⁻¹))) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun v hv => ?_⟩
      · have := hcont.tendsto
        rw [hpt] at this
        exact this.mono_left nhdsWithin_le_nhds
      · refine H_subset_Hbar ?_
        show (0 : ℝ) < ((k : ℂ) * -v⁻¹).im
        simpa [Complex.mul_im] using mul_pos hpc.pos (negInv_mem_H' hv)
    have h2 := (hpc.continuousOn_G _ (hpc.mapsTo_ψ hzm)).tendsto.comp h1
    rw [hpc.right_inv _ hzm] at h2
    have hz0 : -w⁻¹ ≠ 0 := neg_ne_zero.2 (inv_ne_zero hw0)
    refine hcongr (le_principal_iff.2 self_mem_nhdsWithin) ?_
    have := (h2.inv₀ hz0).neg
    rwa [negInv_negInv'] at this

/-- **The relative point is continuous** on the closed pocket without its exit (Carathéodory: `ψ` is continuous on
`C̄ \ E`, and `ψ → ∞` at the entry). -/
theorem continuousOn_relPt (hpc : IsPocketCoord αR αL C c s₁ t₁ E ψ G k) (hEcl : IsClosed E)
    (hψE : ∀ Q ∈ E, Tendsto ψ (𝓝[closure C \ E] Q) (cobounded ℂ))
    (hψinf : E = ∅ → Tendsto ψ (cobounded ℂ ⊓ 𝓟 (closure C)) (cobounded ℂ)) :
    ContinuousOn (relPt E ψ k) (relDomBar C E (αR s₁)) := by
  set g : ℂ → ℂ := fun w => -(k : ℂ) * (ψ (-w⁻¹))⁻¹ with hg
  have hg0 : ∀ {l : Filter ℂ}, Tendsto (fun w => ψ (-w⁻¹)) l (cobounded ℂ) → Tendsto g l (𝓝 0) := by
    intro l h
    have h2 := (tendsto_inv₀_cobounded.comp h).const_mul (-(k : ℂ))
    rw [mul_zero] at h2
    exact h2
  have hfg : ∀ w, w ≠ 0 → -w⁻¹ ∉ E → relPt E ψ k w = g w := fun w hw0 hwE => by
    unfold relPt
    simp only [hw0, false_or, hwE, ↓reduceIte, hg]
  have hf0 : ∀ w, (w = 0 ∨ -w⁻¹ ∈ E) → relPt E ψ k w = 0 := fun w h => by
    unfold relPt
    simp only [h, ↓reduceIte]
  intro w₀ hw₀
  rcases hw₀ with ⟨rfl, hE⟩ | ⟨hw0, hcl, hP⟩
  · -- the physical source `∞` (unbounded pocket)
    rw [← continuousWithinAt_sdiff_self]
    show Tendsto _ _ (𝓝 (relPt E ψ k 0))
    rw [hf0 0 (Or.inl rfl)]
    have hneg : Tendsto (fun w : ℂ => -w⁻¹) (𝓝[relDomBar C E (αR s₁) \ {0}] 0)
        (cobounded ℂ ⊓ 𝓟 (closure C)) := by
      refine tendsto_inf.2 ⟨?_, tendsto_principal.2 (eventually_nhdsWithin_of_forall fun w hw => ?_)⟩
      · have h1 := (tendsto_affine_cobounded (α := (-1 : ℂ)) (β := 0) (by norm_num)).comp
          (tendsto_inv₀_nhdsNE_zero.mono_left
            (nhdsWithin_mono _ fun w (hw : w ∈ relDomBar C E (αR s₁) \ {0}) => hw.2))
        refine h1.congr fun w => ?_
        simp
      · rcases hw.1 with ⟨h, -⟩ | ⟨-, h, -⟩
        · exact absurd h hw.2
        · exact h
    refine (hg0 ((hψinf hE).comp hneg)).congr' (eventually_nhdsWithin_of_forall fun w hw => ?_)
    rw [hfg w hw.2 (by rw [hE]; exact notMem_empty _)]
  by_cases hzE : -w₀⁻¹ ∈ E
  · -- the entry of a bounded pocket
    show Tendsto _ _ (𝓝 (relPt E ψ k w₀))
    rw [hf0 w₀ (Or.inr hzE)]
    set A := relDomBar C E (αR s₁) ∩ {w | w = 0 ∨ -w⁻¹ ∈ E} with hA
    set A' := relDomBar C E (αR s₁) ∩ {w | w ≠ 0 ∧ -w⁻¹ ∉ E} with hA'
    have hsplit : relDomBar C E (αR s₁) = A ∪ A' := by
      ext w
      constructor
      · intro hw
        by_cases h : w = 0 ∨ -w⁻¹ ∈ E
        · exact Or.inl ⟨hw, h⟩
        · push Not at h
          exact Or.inr ⟨hw, h.1, h.2⟩
      · rintro (⟨hw, -⟩ | ⟨hw, -⟩) <;> exact hw
    rw [hsplit, nhdsWithin_union]
    refine tendsto_sup.2 ⟨tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun w hw =>
      (hf0 w hw.2).symm), ?_⟩
    have hneg : Tendsto (fun w : ℂ => -w⁻¹) (𝓝[A'] w₀) (𝓝[closure C \ E] (-w₀⁻¹)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨((continuousAt_inv₀ hw0).neg).tendsto.mono_left nhdsWithin_le_nhds,
        eventually_nhdsWithin_of_forall fun w hw => ⟨?_, hw.2.2⟩⟩
      rcases hw.1 with ⟨h, -⟩ | ⟨-, h, -⟩
      · exact absurd h hw.2.1
      · exact h
    refine (hg0 ((hψE _ hzE).comp hneg)).congr' (eventually_nhdsWithin_of_forall fun w hw => ?_)
    rw [hfg w hw.2.1 hw.2.2]
  · -- an interior or wall point
    have hzm : -w₀⁻¹ ∈ closure C \ E := ⟨hcl, hzE⟩
    have hψ0 := hpc.ψ_ne_zero hzm hP
    set N := {w : ℂ | w ≠ 0 ∧ -w⁻¹ ∉ E} with hN
    have hNn : N ∈ 𝓝 w₀ := by
      have h1 : ∀ᶠ w in 𝓝 w₀, w ≠ 0 := isOpen_compl_singleton.mem_nhds hw0
      have h2 : ∀ᶠ w in 𝓝 w₀, -w⁻¹ ∉ E :=
        ((continuousAt_inv₀ hw0).neg).eventually (hEcl.isOpen_compl.mem_nhds hzE)
      exact h1.and h2
    rw [← continuousWithinAt_inter hNn]
    have hneg : ContinuousWithinAt (fun w : ℂ => -w⁻¹) (relDomBar C E (αR s₁) ∩ N) w₀ :=
      ((continuousAt_inv₀ hw0).neg).continuousWithinAt
    have hmaps : MapsTo (fun w : ℂ => -w⁻¹) (relDomBar C E (αR s₁) ∩ N) (closure C \ E) := by
      intro w hw
      refine ⟨?_, hw.2.2⟩
      rcases hw.1 with ⟨h, -⟩ | ⟨-, h, -⟩
      · exact absurd h hw.2.1
      · exact h
    have hgc : ContinuousWithinAt g (relDomBar C E (αR s₁) ∩ N) w₀ :=
      continuousWithinAt_const.mul ((ContinuousWithinAt.comp (g := ψ) (f := fun w : ℂ => -w⁻¹)
        (hpc.continuousOn_ψ _ hzm) hneg hmaps).inv₀ hψ0)
    refine hgc.congr (fun w hw => hfg w hw.2.1 hw.2.2) (hfg w₀ hw0 hzE)

end RelPt

/-! ### The pocket data and the trace -/

/-- **The pocket coordinate of a shaped pocket, both cases** (`exists_isPocketCoord_of_bounded`, `…_of_unbounded`):
the entry set `E` is `{α_R(s₂)}` (bounded) or `∅` (unbounded), with the behaviour of `ψ` and `G` at the entry. -/
theorem exists_pocketData {αR αL : ℝ≥0 → ℂ} (hR : GB11.IsCompleteSimpleFlow αR)
    (hL : GB11.IsCompleteSimpleFlow αL)
    (hord : ∀ s s' t t' : ℝ≥0, αR s = αL t → αR s' = αL t' → (s < s' ↔ t < t'))
    {C : Set ℂ} (hC : C ∈ betweenComponents (range αR) (range αL)) {s₁ t₁ : ℝ≥0} {s₂ t₂ : ℝ≥0∞}
    (hs : IsPocketShape αR αL C s₁ t₁ s₂ t₂) {c : Chart}
    (hc : IsComponentChart (range αR) (range αL) C c) (hxC : Tendsto c.2.1 (𝓝[H] 0) (𝓝 (αR s₁))) :
    ∃ (E : Set ℂ) (ψ G : ℂ → ℂ) (k : ℝ), IsPocketCoord αR αL C c s₁ t₁ E ψ G k ∧ IsClosed E ∧ (0 : ℂ) ∉ E ∧
      (∀ Q ∈ E, Tendsto ψ (𝓝[closure C \ E] Q) (cobounded ℂ)) ∧
      (∀ Q ∈ E, Tendsto G (cobounded ℂ ⊓ 𝓟 H) (𝓝 Q)) ∧
      (E = ∅ → Tendsto ψ (cobounded ℂ ⊓ 𝓟 (closure C)) (cobounded ℂ)) ∧
      (E = ∅ → Tendsto G (cobounded ℂ ⊓ 𝓟 H) (cobounded ℂ)) ∧
      ((E = ∅ ∧ s₂ = ⊤) ∨ (E = {αR s₂.toNNReal} ∧ s₂ ≠ ⊤)) := by
  by_cases hs₂ : s₂ = ⊤
  · obtain ⟨ψ, G, k, hpc, hGinf, hψinf⟩ := exists_isPocketCoord_of_unbounded hR hL hord hC hs hs₂ hc hxC
    exact ⟨∅, ψ, G, k, hpc, isClosed_empty, notMem_empty _, fun Q hQ => absurd hQ (notMem_empty Q),
      fun Q hQ => absurd hQ (notMem_empty Q), fun _ => hψinf, fun _ => hGinf, Or.inl ⟨rfl, hs₂⟩⟩
  · obtain ⟨ψ, G, k, hpc, hGQ, hψQ⟩ := exists_isPocketCoord_of_bounded hR hL hord hC hs hs₂ hc hxC
    have hs12 : s₁ < s₂.toNNReal :=
      ENNReal.coe_lt_coe.1 (by rw [ENNReal.coe_toNNReal hs₂]; exact hs.lt)
    have hQ0 : αR s₂.toNNReal ≠ 0 := fun h => by
      have : s₂.toNNReal = 0 := hR.2.1 (h.trans hR.2.2.1.symm)
      exact absurd (this ▸ hs12) (not_lt.2 zero_le)
    refine ⟨{αR s₂.toNNReal}, ψ, G, k, hpc, isClosed_singleton, fun h => hQ0 (mem_singleton_iff.1 h).symm,
      fun Q hQ => ?_, fun Q hQ => ?_, fun h => absurd h (singleton_ne_empty _),
      fun h => absurd h (singleton_ne_empty _), Or.inr ⟨rfl, hs₂⟩⟩
    · rw [mem_singleton_iff.1 hQ]; exact hψQ
    · rw [mem_singleton_iff.1 hQ]; exact hGQ

/-- **The trace does not reach `0` during the traversal of a bounded pocket** (its physical point stays in the bounded
`C̄`, and every time interval of the traversal has a visit to `C`). -/
theorem trace_ne_zero_of_isBounded {γ : ℝ≥0 → ℂ} (hγc : Continuous γ) {C : Set ℂ} (hCb : IsBounded C)
    {τ : ℝ≥0} {σ : ℝ≥0∞}
    (hD : ∀ a b : ℝ≥0, τ ≤ a → a < b → (b : ℝ≥0∞) < σ → ∃ t ∈ Ioo a b, γ t ≠ 0 ∧ -(γ t)⁻¹ ∈ C)
    {t₀ : ℝ≥0} (hτt : τ ≤ t₀) (ht : (t₀ : ℝ≥0∞) < σ) : γ t₀ ≠ 0 := by
  intro h0
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.1 hCb
  set M' : ℝ := max M 1 with hM'
  have hM'pos : 0 < M' := lt_of_lt_of_le one_pos (le_max_right _ _)
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.1 hγc.continuousAt (1 / M') (by positivity)
  have hlt : (t₀ : ℝ≥0∞) < min σ ((t₀ + (δ / 2).toNNReal : ℝ≥0) : ℝ≥0∞) :=
    lt_min ht (ENNReal.coe_lt_coe.2 (lt_add_of_pos_right _ (Real.toNNReal_pos.2 (half_pos hδ))))
  obtain ⟨b, hb1, hb2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hlt
  obtain ⟨t, ht', hne, hmem⟩ := hD t₀ b hτt (ENNReal.coe_lt_coe.1 hb1) (lt_of_lt_of_le hb2 (min_le_left _ _))
  have hbt : b < t₀ + (δ / 2).toNNReal := ENNReal.coe_lt_coe.1 (lt_of_lt_of_le hb2 (min_le_right _ _))
  have hdist : dist t t₀ < δ := by
    rw [NNReal.dist_eq, abs_of_nonneg (by have := NNReal.coe_lt_coe.2 ht'.1; linarith)]
    have h1 : (t : ℝ) < (b : ℝ) := NNReal.coe_lt_coe.2 ht'.2
    have h2 : (b : ℝ) < (t₀ : ℝ) + δ / 2 := by
      have := NNReal.coe_lt_coe.2 hbt
      rwa [NNReal.coe_add, Real.coe_toNNReal _ (by linarith)] at this
    linarith
  have hsmall := hball hdist
  rw [h0, dist_zero_right] at hsmall
  have hbig := hM _ hmem
  rw [norm_neg, norm_inv] at hbig
  have hpos : 0 < ‖γ t‖ := norm_pos_iff.2 hne
  have : 1 / M' ≤ ‖γ t‖ := by
    rw [div_le_iff₀ hM'pos]
    have := (inv_le_iff_one_le_mul₀ hpos).1 (hbig.trans (le_max_left M 1))
    linarith
  linarith

/-! ### The named input and the reduction -/

/-- `ζ` is the **relative trace** of the traversal on `[0, T]` (in the relative chart `Φ = relMapC c`): at each
relative time `u`, `ζ u ∈ ℍ̄` and the inverse relative chart `Φ⁻¹ = relInvC c` tends at `ζ u` (within `ℍ`) to the
ambient trace point `γ(τ + u)` (counterflow chart). For `ζ u ∈ ℍ` this is `ζ u = Φ(γ(τ + u))`; at real points it is
Carathéodory's boundary correspondence. -/
def IsRelCurve (c : Chart) (γ : ℝ≥0 → ℂ) (τ : ℝ≥0) (T : ℝ) (ζ : ℝ → ℂ) : Prop :=
  ∀ u ∈ Icc (0 : ℝ) T, ζ u ∈ Hbar ∧ Tendsto (relInvC c) (𝓝[H] (ζ u)) (𝓝 (γ (τ + u.toNNReal)))

/-- **Named input: the relative trace has continuous own futures** (property (ii) of [Yua22, Theorem 1.1],
`YuanCharacterisation.HasContinuousOwnFuture`: after every prefix, the future of the relative trace lifts continuously
through the inverse mapping-out function of the relative hull; source: GB11, "relative continuity by the
continuous-trace criterion of Aux. lemma 41 / Proposition 6.12"). Hypotheses of `GB11Conn.GB11RelLocalGrowthStatement`;
for every `T ∈ (0, σ − τ)` and every continuous relative trace `ζ` on `[0, T]` from `0`. -/
def GB11RelOwnFutureStatement : Prop :=
  ∀ (W' : ℝ≥0 → ℝ) (γ : ℝ≥0 → ℂ), Continuous W' → W' 0 = 0 → IsGeneratingTrace W' ⊤ γ →
    GB10.NoSimpleArcInterval γ ⊤ →
    ∀ αR αL : ℝ≥0 → ℂ, GB11.IsGB11Barrier αR αL γ → WalkPocketShape αR αL →
    ∀ C ∈ betweenComponents (range αR) (range αL), ∀ (s₁ t₁ : ℝ≥0) (s₂ t₂ : ℝ≥0∞),
    IsPocketShape αR αL C s₁ t₁ s₂ t₂ →
    ∀ c : Chart, IsComponentChart (range αR) (range αL) C c → Tendsto c.2.1 (𝓝[H] 0) (𝓝 (αR s₁)) →
    (∀ t : ℝ≥0, t < entryTime γ αR s₂ → γ t ≠ 0 → -(γ t)⁻¹ ∉ closure C) →
    (∀ t : ℝ≥0, entryTime γ αR s₂ ≤ t → (t : ℝ≥0∞) < GB11.firstVisit γ (αR s₁) → γ t ≠ 0 →
      -(γ t)⁻¹ ∈ closure C) →
    (∀ a b : ℝ≥0, entryTime γ αR s₂ ≤ a → a < b → (b : ℝ≥0∞) < GB11.firstVisit γ (αR s₁) →
      ∃ t ∈ Ioo a b, γ t ≠ 0 ∧ -(γ t)⁻¹ ∈ C) →
    ∀ T ∈ horizon (GB11.firstVisit γ (αR s₁) - entryTime γ αR s₂), 0 < T →
      ∀ ζ : ℝ → ℂ, IsRelCurve c γ (entryTime γ αR s₂) T ζ → ContinuousOn ζ (Icc 0 T) → ζ 0 = 0 →
        YuanCharacterisation.HasContinuousOwnFuture ζ T

/-- **The relative trace of a pocket traversal** (deterministic): under the hypotheses of
`GB11Conn.GB11RelLocalGrowthStatement`, for every `T < σ − τ` there is a continuous relative trace `ζ` on `[0, T]` from
`0`, with `fill(ζ([0, u])) = B u` for `u ∈ [0, T]` and these fillings strictly increasing. -/
theorem exists_relCurve {W' : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} (hW' : Continuous W') (hW'0 : W' 0 = 0)
    (hγ : IsGeneratingTrace W' ⊤ γ) {αR αL : ℝ≥0 → ℂ} (hB : GB11.IsGB11Barrier αR αL γ)
    {C : Set ℂ} (hC : C ∈ betweenComponents (range αR) (range αL)) {s₁ t₁ : ℝ≥0} {s₂ t₂ : ℝ≥0∞}
    (hs : IsPocketShape αR αL C s₁ t₁ s₂ t₂) {c : Chart} (hc : IsComponentChart (range αR) (range αL) C c)
    (hxC : Tendsto c.2.1 (𝓝[H] 0) (𝓝 (αR s₁)))
    (hE : ∀ t : ℝ≥0, t < entryTime γ αR s₂ → γ t ≠ 0 → -(γ t)⁻¹ ∉ closure C)
    (hTr : ∀ t : ℝ≥0, entryTime γ αR s₂ ≤ t → (t : ℝ≥0∞) < GB11.firstVisit γ (αR s₁) → γ t ≠ 0 →
      -(γ t)⁻¹ ∈ closure C)
    (hD : ∀ a b : ℝ≥0, entryTime γ αR s₂ ≤ a → a < b → (b : ℝ≥0∞) < GB11.firstVisit γ (αR s₁) →
      ∃ t ∈ Ioo a b, γ t ≠ 0 ∧ -(γ t)⁻¹ ∈ C)
    {T : ℝ} (hT : T ∈ horizon (GB11.firstVisit γ (αR s₁) - entryTime γ αR s₂)) :
    ∃ ζ : ℝ → ℂ, IsRelCurve c γ (entryTime γ αR s₂) T ζ ∧ ContinuousOn ζ (Icc 0 T) ∧ ζ 0 = 0 ∧
      (∀ u ∈ Icc (0 : ℝ) T, fillH (ζ '' Icc 0 u) = relHull W' c C (entryTime γ αR s₂) u) ∧
      StrictMonoOn (fun u => fillH (ζ '' Icc 0 u)) (Icc 0 T) := by
  set τ := entryTime γ αR s₂ with hτ
  set σ := GB11.firstVisit γ (αR s₁) with hσ
  have hγc : Continuous γ := Sec5.continuous_of_isGeneratingTrace_top hγ
  have hRc : IsClosed (range αR) := isClosed_range_of_isCompleteSimpleFlow hB.1
  have hLc : IsClosed (range αL) := isClosed_range_of_isCompleteSimpleFlow hB.2.1
  have hCo : IsOpen C := isOpen_of_mem_betweenComponents hRc hLc hC
  have hCH : C ⊆ H := subset_H_of_mem_betweenComponents hC
  obtain ⟨z₀, hz₀, -, -, hCz⟩ := id hC
  have hCsub : C ⊆ H \ (range αR ∪ range αL) := hCz ▸ connectedComponentIn_subset _ _
  have hWc : Continuous fun r : ℝ => W' r.toNNReal := hW'.comp continuous_real_toNNReal
  -- the pocket coordinate and the boundary correspondence
  obtain ⟨E, ψ, G, k, hpc, hEcl, hE0, hψE, hGE, hψinf, hGinf, hcase⟩ :=
    exists_pocketData hB.1 hB.2.1 hB.2.2.1 hC hs hc hxC
  obtain ⟨e, rR, rL, hbc⟩ : ∃ (e : ℝ → ℂ) (rR rL : ℝ → ℝ≥0), ChartBdryCorr αR αL c s₂ e rR rL := by
    by_cases hs₂ : s₂ = ⊤
    · exact exists_chartBdryCorr_of_unbounded hB.1 hB.2.1 hB.2.2.1 hC hs hs₂ hc hxC
    · exact exists_chartBdryCorr_of_bounded hB.1 hB.2.1 hB.2.2.1 hC hs hs₂ hc hxC
  -- relative times
  set tt : ℝ → ℝ≥0 := fun u => τ + u.toNNReal with htt
  have hhor : ∀ u ∈ Icc (0 : ℝ) T, u ∈ horizon (σ - τ) := fun u hu =>
    ⟨hu.1, lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hu.2) hT.2⟩
  have htσ : ∀ u ∈ Icc (0 : ℝ) T, (tt u : ℝ≥0∞) < σ := fun u hu => coe_add_lt_of_mem_horizon (hhor u hu)
  have hτt : ∀ u : ℝ, τ ≤ tt u := fun u => le_self_add
  have httc : ∀ u ∈ Icc (0 : ℝ) T, ((tt u : ℝ≥0) : ℝ) = (τ : ℝ) + u := fun u hu => by
    rw [htt, NNReal.coe_add, Real.coe_toNNReal _ hu.1]
  -- the trace stays in the closed pocket without its exit
  have hdom : ∀ u ∈ Icc (0 : ℝ) T, γ (tt u) ∈ relDomBar C E (αR s₁) := by
    intro u hu
    by_cases h0 : γ (tt u) = 0
    · refine Or.inl ⟨h0, ?_⟩
      rcases hcase with ⟨hE', -⟩ | ⟨-, hs₂⟩
      · exact hE'
      · exact absurd h0 (trace_ne_zero_of_isBounded hγc (hs.entry hs₂).2.2 hD (hτt u) (htσ u hu))
    · refine Or.inr ⟨h0, hTr _ (hτt u) (htσ u hu) h0, fun hP => ?_⟩
      have : σ ≤ (tt u : ℝ≥0∞) := iInf₂_le (tt u) ⟨h0, hP⟩
      exact absurd (htσ u hu) (not_lt.2 this)
  -- the relative trace
  set ζ : ℝ → ℂ := fun u => relPt E ψ k (γ (tt u)) with hζ
  have hrel : IsRelCurve c γ τ T ζ := fun u hu =>
    ⟨relPt_mem_Hbar hpc (hdom u hu), tendsto_relInvC_relPt hpc hE0 hGE hGinf (hdom u hu)⟩
  have hζc : ContinuousOn ζ (Icc 0 T) :=
    (continuousOn_relPt hpc hEcl hψE hψinf).comp
      ((hγc.comp (continuous_const.add continuous_real_toNNReal)).continuousOn) hdom
  have hζ0 : ζ 0 = 0 := by
    have ht0 : tt 0 = τ := by simp [htt]
    show relPt E ψ k (γ (tt 0)) = 0
    rw [ht0]
    rcases hcase with ⟨-, hs₂⟩ | ⟨hEQ, hs₂⟩
    · have hτ0 : τ = 0 := by simp [hτ, entryTime, hs₂]
      rw [hτ0, hγ.1]
      simp [relPt]
    · have hQ0 : αR s₂.toNNReal ≠ 0 := fun h => hE0 (by rw [hEQ, h]; exact mem_singleton _)
      have hfin : GB11.firstVisit γ (αR s₂.toNNReal) < ⊤ :=
        firstVisit_lt_top_of_ne_zero hB.1.2.2.1 hB.2.2.2.2.2.1 hQ0
      obtain ⟨s₀, hs₀, hne, hp⟩ := exists_eq_firstVisit hγc hfin
      have hτs : τ = s₀ := by
        simp only [hτ, entryTime, hs₂, ↓reduceIte, ← hs₀, ENNReal.toNNReal_coe]
      rw [hτs]
      have hcond : γ s₀ = 0 ∨ -(γ s₀)⁻¹ ∈ E := Or.inr (by rw [hp, hEQ]; exact mem_singleton _)
      simp only [relPt, hcond, ↓reduceIte]
  -- the fill identity
  have hfill : ∀ u ∈ Icc (0 : ℝ) T, fillH (ζ '' Icc 0 u) = relHull W' c C τ u := by
    intro u hu
    set K := fwdHull (fun r : ℝ => W' r.toNNReal) ((τ : ℝ) + u) with hK
    have hKeq : K = fwdHull (fun r : ℝ => W' r.toNNReal) ((tt u : ℝ≥0) : ℝ) := by rw [httc u hu]
    have hKH : IsHPHull K := isHPHull_fwdHull hWc (by rw [← httc u hu]; exact NNReal.coe_nonneg _)
    show fillH (ζ '' Icc 0 u) = relMapC c '' (K ∩ relDom C)
    have hsubH : relMapC c '' (relDom C \ K) ⊆ H := by
      rintro _ ⟨w, hw, rfl⟩; exact relMapC_mem_H hc hw.1
    refine fillH_eq_of_frontier ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · rintro _ ⟨w, hw, rfl⟩; exact relMapC_mem_H hc hw.2
    · rw [hKeq]; exact isBounded_relHull hW' hW'0 hγ hB hc hxC (htσ u hu)
    · rw [H_diff_relHull_eq hc K, image_relDom_diff_eq hc K]
      have hD' : relDom C \ K = relDom C ∩ (H \ K) := by
        ext w
        exact ⟨fun h => ⟨h.1, relDom_subset_H hCH h.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
      rw [hD']
      exact (continuousOn_relInvC hc hCo hCH).isOpen_inter_preimage QuantumZipper.isOpen_H
        ((isOpen_relDom hCo hCH).inter hKH.isOpen)
    · rw [H_diff_relHull_eq hc K, hKeq]
      exact (isPreconnected_relDom_diff_fwdHull hW' hW'0 hγ hB hs hc hCo hCH hxC hbc (hτt u)
        (htσ u hu)).image _ ((continuousOn_relMapC hc hCo hCH).mono sdiff_subset)
    · exact (isCompact_Icc.image_of_continuousOn (hζc.mono (Icc_subset_Icc_right hu.2))).isClosed
    · rintro z ⟨⟨v, hv, rfl⟩, hzH⟩
      have hvT : v ∈ Icc (0 : ℝ) T := ⟨hv.1, hv.2.trans hu.2⟩
      obtain ⟨-, hlim⟩ := hrel v hvT
      have := mem_closure_iff_nhdsWithin_neBot.1 (subset_closure hzH)
      have hval : relInvC c (ζ v) = γ (tt v) :=
        tendsto_nhds_unique ((continuousOn_relInvC hc hCo hCH) _ hzH).tendsto hlim
      have hw : γ (tt v) ∈ relDom C := hval ▸ relInvC_mem hc hzH
      have hwH := relDom_subset_H hCH hw
      have hvu : tt v ≤ tt u := add_le_add_right (Real.toNNReal_le_toNNReal hv.2) τ
      have hwK : γ (tt v) ∈ K := by rw [hKeq]; exact mem_fwdHull_of_isGeneratingTrace hγ hvu hwH
      exact ⟨γ (tt v), ⟨hwK, hw⟩, by rw [← hval, relMapC_relInvC hc hzH]⟩
    · rintro _ ⟨w, ⟨hwK, hwD⟩, rfl⟩ hcl
      have hwH := relDom_subset_H hCH hwD
      have hqH := relMapC_mem_H hc hwD
      rw [H_diff_relHull_eq hc K] at hcl
      have h1 := (((continuousOn_relInvC hc hCo hCH) _ hqH).mono hsubH).mem_closure_image hcl
      rw [relInvC_relMapC hc hwD] at h1
      have hwcl : w ∈ closure (H \ K) := closure_mono (by
        rintro _ ⟨_, ⟨w', hw', rfl⟩, rfl⟩
        rw [relInvC_relMapC hc hw'.1]
        exact ⟨relDom_subset_H hCH hw'.1, hw'.2⟩) h1
      rw [hKeq] at hwK hwcl
      obtain ⟨t', ht', hγt'⟩ := mem_image_of_mem_closure_compl hγ hwK hwcl hwH
      have hγt'0 : γ t' ≠ 0 := hγt' ▸ ne_zero_of_mem_H' hwH
      have hτt' : τ ≤ t' := by
        by_contra hlt
        push Not at hlt
        exact hE t' hlt hγt'0 (subset_closure (by rw [hγt']; exact hwD))
      set v : ℝ := (t' : ℝ) - τ with hvdef
      have hv0 : 0 ≤ v := sub_nonneg.2 (NNReal.coe_le_coe.2 hτt')
      have hvu : v ≤ u := by
        have := NNReal.coe_le_coe.2 ht'.2
        rw [httc u hu] at this
        linarith
      have htv : tt v = t' := by
        apply NNReal.eq
        rw [htt, NNReal.coe_add, Real.coe_toNNReal _ hv0, hvdef]
        ring
      obtain ⟨hζH, hlim⟩ := hrel v ⟨hv0, hvu.trans hu.2⟩
      rw [show τ + v.toNNReal = t' from htv, hγt'] at hlim
      refine ⟨v, ⟨hv0, hvu⟩, ?_⟩
      by_cases hζvH : ζ v ∈ H
      · have := mem_closure_iff_nhdsWithin_neBot.1 (subset_closure hζvH)
        have hval : relInvC c (ζ v) = w :=
          tendsto_nhds_unique ((continuousOn_relInvC hc hCo hCH) _ hζvH).tendsto hlim
        rw [← hval, relMapC_relInvC hc hζvH]
      · exfalso
        have him : (ζ v).im = 0 := le_antisymm (not_lt.1 hζvH) hζH
        have hx : ζ v = (((ζ v).re : ℝ) : ℂ) := Complex.ext rfl (by simp [him])
        rw [hx] at hlim
        have := FiniteEndpoint.neBot_nhdsWithin_H (z := (((ζ v).re : ℝ) : ℂ)) (by simp)
        have hwe : w = e (ζ v).re := tendsto_nhds_unique hlim (hbc.1 _)
        have hwC : -w⁻¹ ∈ C := hwD
        obtain ⟨-, hposL, -, hnegR, -, he0top, he0⟩ := hbc
        rcases lt_trichotomy (ζ v).re 0 with hx0 | hx0 | hx0
        · obtain ⟨-, he⟩ := hnegR _ hx0
          rw [hwe, he, negInv_negInv'] at hwC
          exact (hCsub hwC).2 (Or.inl ⟨_, rfl⟩)
        · rw [hx0] at hwe
          by_cases hs₂ : s₂ = ⊤
          · rw [he0top hs₂] at hwe
            exact ne_zero_of_mem_H' hwH hwe
          · rw [he0 hs₂] at hwe
            rw [hwe, negInv_negInv'] at hwC
            exact (hCsub hwC).2 (Or.inl ⟨_, rfl⟩)
        · obtain ⟨-, he⟩ := hposL _ hx0
          rw [hwe, he, negInv_negInv'] at hwC
          exact (hCsub hwC).2 (Or.inr ⟨_, rfl⟩)
  -- strict growth
  have hmono : StrictMonoOn (fun u => fillH (ζ '' Icc 0 u)) (Icc 0 T) := by
    intro u hu u' hu' huu'
    show fillH (ζ '' Icc 0 u) < fillH (ζ '' Icc 0 u')
    rw [hfill u hu, hfill u' hu']
    have hsub : relHull W' c C τ u ⊆ relHull W' c C τ u' :=
      image_mono (inter_subset_inter_left _ (QuantumZipper.fwdHull_mono.1 (by linarith)))
    refine ⟨hsub, fun h => ?_⟩
    have hab : tt u < tt u' :=
      add_lt_add_right ((Real.toNNReal_lt_toNNReal_iff (lt_of_le_of_lt hu.1 huu')).2 huu') τ
    obtain ⟨w, hwD, hwb, hwa⟩ := exists_mem_relDom_fwdHull_sdiff hW' hW'0 hγ hCo hCH hD (hτt u) hab (htσ u' hu')
    have hmem : relMapC c w ∈ relHull W' c C τ u' := ⟨w, ⟨by rw [← httc u' hu']; exact hwb, hwD⟩, rfl⟩
    obtain ⟨w', ⟨hw'K, hw'D⟩, he⟩ := h hmem
    have : w' = w := injOn_relMapC hc hw'D hwD he
    rw [this, ← httc u hu] at hw'K
    exact hwa hw'K
  exact ⟨ζ, hrel, hζc, hζ0, hfill, hmono⟩

/-- **`GB11RelLoewnerStatement` from the continuous own futures of the relative trace** (conditional helper): the
relative trace (`exists_relCurve`) and Yuan's theorem (`YuanCharacterisation.exists_loewner_of_hasContinuousOwnFuture`);
for `T = 0` the relative hull is empty. -/
theorem gb11RelLoewnerStatement_of_ownFuture (h : GB11RelOwnFutureStatement) : GB11RelLoewnerStatement := by
  intro W' γ hW' hW'0 hγ hno αR αL hB hP C hC s₁ t₁ s₂ t₂ hs c hc hxC hE hTr hD T hT
  obtain ⟨ζ, hrel, hζc, hζ0, hfill, hmono⟩ := exists_relCurve hW' hW'0 hγ hB hC hs hc hxC hE hTr hD hT
  rcases eq_or_lt_of_le hT.1 with hT0 | hT0
  · -- `T = 0`: the empty hull
    have hγc : Continuous γ := Sec5.continuous_of_isGeneratingTrace_top hγ
    have hCo : IsOpen C := isOpen_of_mem_betweenComponents (isClosed_range_of_isCompleteSimpleFlow hB.1)
      (isClosed_range_of_isCompleteSimpleFlow hB.2.1) hC
    have hCH : C ⊆ H := subset_H_of_mem_betweenComponents hC
    have hCc : IsPreconnected C := by
      obtain ⟨z, -, -, -, rfl⟩ := hC
      exact isPreconnected_connectedComponentIn
    have hempty := fwdHull_inter_relDom_eq_empty hW' hW'0 hγ hCo hCH hCc
      (entryTime_lt_firstVisit hγ.1 hγc hB hs) hE hD
    refine ⟨fun _ => 0, continuous_const, rfl, fun _ => 0, rfl, fun a ha b hb hab => ?_, continuousOn_const,
      fun u hu => ?_⟩
    · have ha0 : a = 0 := le_antisymm (hT0 ▸ ha.2) ha.1
      have hb0 : b = 0 := le_antisymm (hT0 ▸ hb.2) hb.1
      exact absurd (ha0.trans hb0.symm) hab.ne
    · have hu0 : u = 0 := le_antisymm (hT0 ▸ hu.2) hu.1
      rw [hu0, QuantumZipper.RS.fwdHull_zero_eq_empty continuous_const]
      show ∅ = relMapC c '' (fwdHull (fun r : ℝ => W' r.toNNReal) ((entryTime γ αR s₂ : ℝ) + 0) ∩ relDom C)
      rw [add_zero, hempty, image_empty]
  · -- Yuan's theorem
    have hii := h W' γ hW' hW'0 hγ hno αR αL hB hP C hC s₁ t₁ s₂ t₂ hs c hc hxC hE hTr hD T hT hT0 ζ hrel hζc hζ0
    obtain ⟨W, hW, hW0, σ, hσ0, hσm, hσc, hK⟩ := YuanCharacterisation.exists_loewner_of_hasContinuousOwnFuture
      hT0 hζc hζ0 (fun u hu => (hrel u hu).1) hmono hii
    exact ⟨W, hW, hW0, σ, hσ0, hσm, hσc, fun u hu => (hK u hu).trans (hfill u hu)⟩

/-- **`GB11RelLocalGrowthStatement` from the continuous own futures of the relative trace** (conditional helper). -/
theorem gb11RelLocalGrowthStatement_of_ownFuture (h : GB11RelOwnFutureStatement) : GB11RelLocalGrowthStatement :=
  gb11RelLocalGrowthStatement_of_loewner (gb11RelLoewnerStatement_of_ownFuture h)

/-- **Lemma GB11's relative parametrization from the continuous own futures of the relative trace** (conditional
helper; `GB11ChartBdryStatement` is proved). -/
theorem gb11RelParamStatement_of_ownFuture (h : GB11RelOwnFutureStatement) : GW4Reg.GB11RelParamStatement :=
  gb11RelParamStatement_of_loewner (gb11RelLoewnerStatement_of_ownFuture h)

end GB11Chart

end Theorem14

end InteractingSLE
