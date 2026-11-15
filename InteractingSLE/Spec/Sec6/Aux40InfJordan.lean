/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec6.Aux40Inf
import InteractingSLE.Spec.Sec6.Aux41Full

/-!
# The Jordan coordinate of a pocket with its junction at the original target

Specification §6.2, **Aux.** lemma 41 (`source/spec/p193-240.md` L213–L215: "Let `ψ : C → ℍ` be the
Jordan coordinate with `ψ(y₀) = 0` and `ψ(x₀) = ∞`"), for the pocket of `IsReversePocketInf`, whose
junction `x₀` is the original target `∞` of the half-plane chart.

The real Möbius map `ψ_p(w) = −(w − p)⁻¹` (`p` a real point outside `C̄`) sends `C` onto a bounded
Jordan domain `C'` whose boundary consists of the two compactified arms `ψ_p ∘ α_i` and `0 = ψ_p(∞)`
(`exists_compactArm`, `psiMap_frontier`); the Jordan coordinate of `C'` with `0 ↦ ∞`
(`exists_jordanCoord`), composed with `ψ_p`, is a Jordan coordinate of `C` at infinity.

## Main results

* `IsJordanCoordInf`: a conformal bijection `C → ℍ` extending continuously and injectively to `C̄`
  with values in `ℍ̄`, real on `∂C`, `y₀ ↦ 0`, and `→ ∞` at `∞`;
* `exists_compactArm`: the compactification `[0, 1] → ℂ` of a proper simple arm by `ψ_p`;
* `IsReversePocketInf.exists_isJordanCoordInf`: **the pocket has a Jordan coordinate at infinity**.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology

open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv)
open SupercriticalConformalCovariance (IsConformalBijection)

namespace InteractingSLE.Sec6

/-- A **Jordan coordinate with the junction at infinity** of a domain `C` (Aux. lemma 41 with
`x₀ = ∞`): a conformal bijection `C → ℍ` extending continuously and injectively to `C̄` with values
in `ℍ̄`, real on `∂C`, `ψ(y₀) = 0`, and `ψ → ∞` at `∞` within `C̄`. -/
def IsJordanCoordInf (C : Set ℂ) (y₀ : ℂ) (ψ : ℂ → ℂ) : Prop :=
  ContinuousOn ψ (closure C) ∧ InjOn ψ (closure C) ∧ MapsTo ψ (closure C) Hbar ∧
    IsConformalBijection ψ C H ∧ (∀ z ∈ frontier C, (ψ z).im = 0) ∧ ψ y₀ = 0 ∧
    Tendsto ψ (cobounded ℂ ⊓ 𝓟 (closure C)) (cobounded ℂ)

variable {p : ℝ}

/-- **The compactification of a proper simple arm by `ψ_p`**: for `α : [0, ∞) → ℂ` continuous,
injective, avoiding `p`, with `‖α(v)‖ → ∞`, the arc `b(s) = ψ_p(α(s/(1 − s)))`, `b(1) = 0`, is
continuous and injective on `[0, 1]`. -/
theorem exists_compactArm {α : ℝ → ℂ} (hα : ContinuousOn α (Ici 0)) (hαi : InjOn α (Ici 0))
    (hαt : Tendsto (fun v => ‖α v‖) atTop atTop) (hαp : ∀ v ∈ Ici (0 : ℝ), α v ≠ p) :
    ∃ b : ℝ → ℂ, ContinuousOn b (Icc 0 1) ∧ InjOn b (Icc 0 1) ∧ b 0 = psiMap p (α 0) ∧
      b 1 = 0 ∧ b '' Icc 0 1 = psiMap p '' (α '' Ici 0) ∪ {0} := by
  classical
  set τ : ℝ → ℝ := fun s => s / (1 - s) with hτ
  have hτI : ∀ s ∈ Ico (0 : ℝ) 1, τ s ∈ Ici (0 : ℝ) := fun s hs =>
    div_nonneg hs.1 (by linarith [hs.2])
  have hτinj : InjOn τ (Ico 0 1) := by
    intro s hs t ht h
    have h1 : (1 : ℝ) - s ≠ 0 := by linarith [hs.2]
    have h2 : (1 : ℝ) - t ≠ 0 := by linarith [ht.2]
    simp only [hτ] at h
    rw [div_eq_div_iff h1 h2] at h
    linarith
  have hτsurj : ∀ v ∈ Ici (0 : ℝ), ∃ s ∈ Ico (0 : ℝ) 1, τ s = v := by
    intro v hv
    have hv0 : (0 : ℝ) ≤ v := hv
    have h1 : (0 : ℝ) < 1 + v := by linarith
    refine ⟨v / (1 + v), ⟨div_nonneg hv0 h1.le, (div_lt_one h1).2 (by linarith)⟩, ?_⟩
    have h2 : (1 : ℝ) - v / (1 + v) = 1 / (1 + v) := by field_simp; ring
    show v / (1 + v) / (1 - v / (1 + v)) = v
    rw [h2]
    field_simp
  set e : ℝ → ℂ := fun s => psiMap p (α (τ s)) with he
  set b : ℝ → ℂ := fun s => if s = 1 then 0 else e s with hb
  have hbI : ∀ s ∈ Ico (0 : ℝ) 1, b s = e s := fun s hs => by
    simp only [hb, hs.2.ne, ↓reduceIte]
  have hb1 : b 1 = 0 := by simp [hb]
  have hb0 : b 0 = psiMap p (α 0) := by
    rw [hbI 0 ⟨le_rfl, zero_lt_one⟩]; simp [he, hτ]
  have he0 : ∀ s ∈ Ico (0 : ℝ) 1, e s ≠ 0 := fun s hs h =>
    hαp _ (hτI s hs) (psiMap_eq_zero_iff.1 h)
  have hτc : ContinuousOn τ (Ico 0 1) :=
    continuousOn_id.div (continuousOn_const.sub continuousOn_id) fun s hs =>
      sub_ne_zero.2 (ne_of_gt hs.2)
  have hec : ContinuousOn e (Ico 0 1) :=
    continuousOn_psiMap.comp (hα.comp hτc hτI) fun s hs => hαp _ (hτI s hs)
  have hlim1 : Tendsto e (𝓝[<] 1) (𝓝 0) := by
    have h1 : Tendsto (fun s : ℝ => 1 - s) (𝓝[<] 1) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have : Tendsto (fun s : ℝ => 1 - s) (𝓝 1) (𝓝 0) :=
          (continuous_const.sub continuous_id).tendsto' 1 0 (by simp)
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with s hs
        show 0 < 1 - s
        have : s < 1 := hs
        linarith
    have h2 : Tendsto τ (𝓝[<] 1) atTop := by
      have h3 : Tendsto (fun s : ℝ => s) (𝓝[<] 1) (𝓝 1) := tendsto_nhdsWithin_of_tendsto_nhds
        (continuous_id.tendsto 1)
      exact (h3.pos_mul_atTop one_pos (tendsto_inv_nhdsGT_zero.comp h1)).congr fun s => by
        simp [hτ, div_eq_mul_inv]
    exact tendsto_psiMap_zero (hαt.comp h2)
  refine ⟨b, ?_, ?_, hb0, hb1, ?_⟩
  · -- continuity
    intro s hs
    rcases eq_or_lt_of_le hs.2 with h1 | h1
    · subst h1
      have hI : Icc (0 : ℝ) 1 = insert 1 (Ico 0 1) := (Ico_insert_right zero_le_one).symm
      show ContinuousWithinAt b (Icc 0 1) 1
      rw [hI]
      refine continuousWithinAt_insert_self.2 ?_
      show Tendsto b (𝓝[Ico 0 1] 1) (𝓝 (b 1))
      rw [hb1]
      have hle : 𝓝[Ico (0 : ℝ) 1] 1 ≤ 𝓝[<] 1 := nhdsWithin_mono _ Ico_subset_Iio_self
      refine (hlim1.mono_left hle).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with t ht using (hbI t ht).symm
    · have hs' : s ∈ Ico (0 : ℝ) 1 := ⟨hs.1, h1⟩
      have hc : ContinuousWithinAt b (Ico 0 1) s :=
        (hec s hs').congr (fun t ht => hbI t ht) (hbI s hs')
      refine hc.mono_of_mem_nhdsWithin (mem_nhdsWithin.2 ⟨Iio 1, isOpen_Iio, h1, ?_⟩)
      exact fun t ht => ⟨ht.2.1, ht.1⟩
  · -- injectivity
    intro s hs t ht hst
    rcases eq_or_lt_of_le hs.2 with hs1 | hs1 <;> rcases eq_or_lt_of_le ht.2 with ht1 | ht1
    · rw [hs1, ht1]
    · rw [hs1, hb1, hbI t ⟨ht.1, ht1⟩] at hst
      exact absurd hst.symm (he0 t ⟨ht.1, ht1⟩)
    · rw [ht1, hb1, hbI s ⟨hs.1, hs1⟩] at hst
      exact absurd hst (he0 s ⟨hs.1, hs1⟩)
    · rw [hbI s ⟨hs.1, hs1⟩, hbI t ⟨ht.1, ht1⟩] at hst
      exact hτinj ⟨hs.1, hs1⟩ ⟨ht.1, ht1⟩
        (hαi (hτI s ⟨hs.1, hs1⟩) (hτI t ⟨ht.1, ht1⟩) (psiMap_injective hst))
  · -- the image
    have hI : Icc (0 : ℝ) 1 = Ico 0 1 ∪ {1} := (Ico_union_right zero_le_one).symm
    rw [hI, image_union, image_singleton, hb1]
    congr 1
    ext w
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨α (τ s), ⟨τ s, hτI s hs, rfl⟩, (hbI s hs).symm⟩
    · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
      obtain ⟨s, hs, rfl⟩ := hτsurj v hv
      exact ⟨s, hs, hbI s hs⟩

/-- **`ψ_p` on an unbounded open set** `C` with `p ∉ C̄`: the image `C' = ψ_p(C)` is open,
`C̄' \ {0} = ψ_p(C̄)`, and `∂C' = ψ_p(∂C) ∪ {0}`. -/
theorem psiMap_frontier {C : Set ℂ} (hC : IsOpen C) (hpC : (p : ℂ) ∉ closure C)
    (hCb : ¬ IsBounded C) :
    IsOpen (psiMap p '' C) ∧ closure (psiMap p '' C) \ {0} = psiMap p '' closure C ∧
      frontier (psiMap p '' C) = psiMap p '' frontier C ∪ {0} := by
  have hclp : closure C ⊆ {(p : ℂ)}ᶜ := fun z hz h => hpC (mem_singleton_iff.1 h ▸ hz)
  have hcont : ContinuousOn (psiMap p) (closure C) := continuousOn_psiMap.mono hclp
  have himg : psiMap p '' C = psiMapInv p ⁻¹' C ∩ {(0 : ℂ)}ᶜ := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨by simp only [mem_preimage, psiMapInv_psiMap]; exact hz, fun h => ?_⟩
      exact hclp (subset_closure hz) (psiMap_eq_zero_iff.1 h)
    · rintro ⟨hw, -⟩
      exact ⟨psiMapInv p w, hw, psiMap_psiMapInv w⟩
  have hopen : IsOpen (psiMap p '' C) := by
    rw [himg, inter_comm]
    exact continuousOn_psiMapInv.isOpen_inter_preimage isOpen_compl_singleton hC
  have h0 : (0 : ℂ) ∉ psiMap p '' closure C := by
    rintro ⟨z, hz, hz0⟩
    exact hclp hz (psiMap_eq_zero_iff.1 hz0)
  -- `0` is in the closure: `ψ_p → 0` at `∞` along `C`
  have h0cl : (0 : ℂ) ∈ closure (psiMap p '' C) := by
    have hne : (cobounded ℂ ⊓ 𝓟 C).NeBot := by
      refine Filter.inf_principal_neBot_iff.2 fun U hU => ?_
      by_contra h
      rw [not_nonempty_iff_eq_empty] at h
      have hUb : IsBounded Uᶜ := isBounded_def.2 (by rwa [compl_compl])
      refine hCb (hUb.subset fun z hz hzU => ?_)
      have : z ∈ U ∩ C := ⟨hzU, hz⟩
      rw [h] at this
      exact this
    have ht : Tendsto (fun z => psiMap p z) (cobounded ℂ ⊓ 𝓟 C) (𝓝 0) :=
      tendsto_psiMap_zero (w := fun z => z)
        (tendsto_norm_atTop_iff_cobounded.2 (tendsto_id.mono_left inf_le_left))
    exact mem_closure_of_tendsto ht (eventually_inf_principal.2 (Eventually.of_forall
      fun z hz => mem_image_of_mem _ hz))
  have hcl : closure (psiMap p '' C) \ {0} = psiMap p '' closure C := by
    ext w
    constructor
    · rintro ⟨hw, hw0⟩
      have hw0' : w ≠ 0 := hw0
      have hc : ContinuousWithinAt (psiMapInv p) (psiMap p '' C) w :=
        (continuousOn_psiMapInv w hw0').mono (fun x hx => by
          rw [himg] at hx; exact hx.2)
      have hmem := hc.mem_closure_image hw
      have himg' : psiMapInv p '' (psiMap p '' C) = C := by
        rw [image_image]; simp only [psiMapInv_psiMap, image_id']
      rw [himg'] at hmem
      exact ⟨psiMapInv p w, hmem, psiMap_psiMapInv w⟩
    · rintro hw
      refine ⟨hcont.image_closure hw, fun h => h0 (mem_singleton_iff.1 h ▸ hw)⟩
  refine ⟨hopen, hcl, ?_⟩
  rw [hopen.frontier_eq, hC.frontier_eq]
  ext w
  constructor
  · rintro ⟨hw, hwC⟩
    by_cases hw0 : w = 0
    · exact Or.inr hw0
    · have : w ∈ psiMap p '' closure C := hcl ▸ ⟨hw, hw0⟩
      obtain ⟨z, hz, rfl⟩ := this
      exact Or.inl ⟨z, ⟨hz, fun hzC => hwC ⟨z, hzC, rfl⟩⟩, rfl⟩
  · rintro (⟨z, ⟨hz, hzC⟩, rfl⟩ | hw)
    · have hmem : psiMap p z ∈ closure (psiMap p '' C) \ {0} := by
        rw [hcl]; exact ⟨z, hz, rfl⟩
      refine ⟨hmem.1, ?_⟩
      rintro ⟨z', hz', he⟩
      exact hzC (psiMap_injective he ▸ hz')
    · rw [mem_singleton_iff.1 hw]
      refine ⟨h0cl, fun h => h0 ?_⟩
      obtain ⟨z, hz, he⟩ := h
      exact ⟨z, subset_closure hz, he⟩

namespace IsReversePocketInf

variable {W : ℝ → ℝ} {η : ℝ → ℂ} {C : Set ℂ} {α₁ α₂ : ℝ → ℂ} {τ : ℝ}

/-- **The pocket at infinity has a Jordan coordinate** with `x₀ = ∞ ↦ ∞` and `y₀ ↦ 0`: compose the
Jordan coordinate of the bounded Jordan domain `ψ_p(C)` (with `0 = ψ_p(∞) ↦ ∞`) with `ψ_p`. -/
theorem exists_isJordanCoordInf (hP : IsReversePocketInf W η C α₁ α₂ τ) :
    ∃ ψ : ℂ → ℂ, IsJordanCoordInf C (α₁ 0) ψ := by
  -- a real point outside `C̄`
  obtain ⟨M, hM⟩ := hP.farReal
  set p : ℝ := |M| with hpdef
  have hpC : (p : ℂ) ∉ closure C := hM p (by rw [hpdef, abs_abs]; exact le_abs_self M)
  have hclp : closure C ⊆ {(p : ℂ)}ᶜ := fun z hz h => hpC (mem_singleton_iff.1 h ▸ hz)
  obtain ⟨hopen, hcl, hfr⟩ := psiMap_frontier hP.isOpen hpC hP.not_isBounded
  set C' := psiMap p '' C with hC'def
  -- the compactified arms
  have hαp : ∀ {α : ℝ → ℂ}, (α = α₁ ∨ α = α₂) → ∀ v ∈ Ici (0 : ℝ), α v ≠ p := by
    intro α hα v hv h
    have : α v ∈ frontier C := by
      rw [hP.frontier_eq]; rcases hα with rfl | rfl
      exacts [Or.inl ⟨v, hv, rfl⟩, Or.inr ⟨v, hv, rfl⟩]
    exact hpC (h ▸ frontier_subset_closure this)
  obtain ⟨b₁, hb₁c, hb₁i, hb₁0, hb₁1, hb₁img⟩ :=
    exists_compactArm hP.cont₁ hP.inj₁ hP.tendsto₁ (hαp (Or.inl rfl))
  obtain ⟨b₂, hb₂c, hb₂i, hb₂0, hb₂1, hb₂img⟩ :=
    exists_compactArm hP.cont₂ hP.inj₂ hP.tendsto₂ (hαp (Or.inr rfl))
  have hΓeq : frontier C' = b₁ '' Icc 0 1 ∪ b₂ '' Icc 0 1 := by
    rw [hfr, hb₁img, hb₂img, hP.frontier_eq, image_union]
    ext w
    simp only [mem_union, mem_singleton_iff]
    tauto
  have hΓJ : LQGMetric.JordanMap.IsJordanCurve (frontier C') := by
    rw [hΓeq]
    refine Sec7.isJordanCurve_image_union hb₁c hb₂c hb₁i hb₂i (by rw [hb₁0, hb₂0, hP.seed])
      (by rw [hb₁1, hb₂1]) ?_
    rintro w ⟨hw₁, hw₂⟩
    rw [hb₁img] at hw₁
    rw [hb₂img] at hw₂
    rcases hw₁ with ⟨_, ⟨v, hv, rfl⟩, rfl⟩ | hw₁
    · rcases hw₂ with ⟨_, ⟨v', hv', rfl⟩, he⟩ | hw₂
      · have he' := psiMap_injective he
        left
        rw [hb₁0]
        rcases eq_or_lt_of_le (mem_Ici.1 hv) with h0 | h0
        · rw [← h0]
        rcases eq_or_lt_of_le (mem_Ici.1 hv') with h0' | h0'
        · rw [← h0', hP.seed] at he'
          exact absurd (hP.inj₁ (mem_Ici.2 le_rfl) hv he') h0.ne
        · exact absurd he'.symm (hP.sides v h0 v' h0')
      · right; rw [hb₁1]; exact hw₂
    · right; rw [hb₁1]; exact hw₁
  -- `C'` is a bounded connected component of the complement of its frontier
  obtain ⟨z₀, hz₀⟩ := hP.isConnected.nonempty
  have hz₀' : psiMap p z₀ ∈ C' := ⟨z₀, hz₀, rfl⟩
  have hC'conn : IsConnected C' :=
    hP.isConnected.image _ (continuousOn_psiMap.mono fun z hz => hclp (subset_closure hz))
  have hCeq := connectedComponentIn_compl_frontier_eq hopen hC'conn hz₀'
  have hpΓ : psiMap p z₀ ∈ (frontier C')ᶜ := by
    rw [← hCeq] at hz₀'; exact connectedComponentIn_subset _ _ hz₀'
  have hd : 0 < infDist (p : ℂ) (closure C) :=
    (isClosed_closure.notMem_iff_infDist_pos ⟨z₀, subset_closure hz₀⟩).1 hpC
  have hC'b : IsBounded C' := by
    refine isBounded_iff_forall_norm_le.2 ⟨(infDist (p : ℂ) (closure C))⁻¹, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    have h1 : infDist (p : ℂ) (closure C) ≤ ‖z - p‖ := by
      rw [← dist_eq_norm, dist_comm]; exact infDist_le_dist_of_mem (subset_closure hz)
    rw [psiMap, norm_neg, norm_inv]
    exact inv_anti₀ hd h1
  have h0Γ : (0 : ℂ) ∈ frontier C' := by rw [hfr]; exact Or.inr rfl
  have hyΓ : psiMap p (α₁ 0) ∈ frontier C' := by
    rw [hfr, hP.frontier_eq]; exact Or.inl ⟨α₁ 0, Or.inl ⟨0, mem_Ici.2 le_rfl, rfl⟩, rfl⟩
  obtain ⟨ψ', ψinv, hc, hmaps, -, -, hψinvψ, -, hconf, hreal, hy, ht⟩ :=
    exists_jordanCoord hΓJ hpΓ (by rw [hCeq]; exact hC'b) h0Γ hyΓ
  rw [hCeq] at hc hmaps hψinvψ hconf ht
  rw [hcl] at hc hmaps hψinvψ ht
  have hpsi : IsConformalBijection (psiMap p) C C' := by
    refine ⟨fun z hz => ?_, mapsTo_image _ _, psiMap_injective.injOn, surjOn_image _ _⟩
    have hzp : z - p ≠ 0 := sub_ne_zero.2 fun h => hclp (subset_closure hz) h
    exact ((differentiableAt_id.sub_const (p : ℂ)).inv hzp).neg.differentiableWithinAt
  refine ⟨ψ' ∘ psiMap p, hc.comp (continuousOn_psiMap.mono hclp) (mapsTo_image _ _), ?_,
    fun z hz => hmaps (mem_image_of_mem _ hz), isConformalBijection_comp hconf hpsi, ?_, hy, ?_⟩
  · intro z hz z' hz' h
    have := congrArg ψinv h
    simp only [Function.comp] at this
    rw [hψinvψ _ (mem_image_of_mem _ hz), hψinvψ _ (mem_image_of_mem _ hz')] at this
    exact psiMap_injective this
  · intro z hz
    refine hreal _ ⟨by rw [hfr]; exact Or.inl ⟨z, hz, rfl⟩, fun h => ?_⟩
    exact hclp (frontier_subset_closure hz) (psiMap_eq_zero_iff.1 (mem_singleton_iff.1 h))
  · have h1 : Tendsto (psiMap p) (cobounded ℂ ⊓ 𝓟 (closure C)) (𝓝[psiMap p '' closure C] 0) :=
      tendsto_nhdsWithin_iff.2 ⟨tendsto_psiMap_zero (w := fun z => z)
        (tendsto_norm_atTop_iff_cobounded.2 (tendsto_id.mono_left inf_le_left)),
        eventually_inf_principal.2 (Eventually.of_forall fun z hz => mem_image_of_mem _ hz)⟩
    exact ht.comp h1

end IsReversePocketInf

end InteractingSLE.Sec6
