/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.GlueCondUnionImgBase
import InteractingSLE.Foundations.Loewner.YuanCorollary13

/-!
# The staged cross-conditioning law: the transition map preserves the pieces of a staged prefix

Packet PROVE-CROSSCOND-STAGED3 (the multi-piece boundary datum (S2) of PROVE-CROSSCOND-STAGED §5.2). A staged flow
prefix is one simple Loewner trace `α` (driver `Wα`, time `t`) whose pieces start at switch times `0 < a < t`; the
force points created at a switch sit at the two base images of the chain shifted by `a`,
`chartAL (shiftDrive Wα a) (t − a)` and `chartAR (shiftDrive Wα a) (t − a)` (the left and right prime ends of the switch
point `α(a)`, flowed to time `t`). In the image chart (counterflow chart `Ψ = revChart Wβ s`, image chain `W′` with
`K′_T = Ψ(K_t)`) the same switch point is `η′(A)`. This file shows, deterministically, that the inverse transition
map `Θ = f_t ∘ Ψ⁻¹ ∘ F′_T` carries the pieces of the image slit onto the pieces of the flow slit:

* `extendFrom_add_shift`: `F̄_{a+u} = F̄_a ∘ F̄^{(a)}_u` on `ℍ̄` (boundary flow property);
* `mem_Ioo_chartA_iff` (L1 + L2): a real point over `η(τ)` at time `a + u` lies strictly between the base images of
  the chain shifted by `a` iff `τ > a`; `eq_chartA_of_extendFrom_eq` (L0): the real points over the switch point
  `η(a)` are exactly the two base images (the tip of the chain at `a` has one prime end);
* `lt_iff_lt_of_eq_revChart`: `Ψ` preserves the time order along the trace (intermediate values through the closed
  embedding of the image arc);
* **`mem_Ioo_chartA_iff_of_imgTheta`**: at a slit point `x` of the image chart with `Θ → x₁`, `x₁` lies beyond the
  flow switch `a` iff `x` lies beyond the image switch `A`; **`eq_imgChartA_of_eq_chartA`**: `Θ` reaches a flow born
  mark only at an image born mark; `exists_imgTime`: every flow switch has an image time.

No simplicity beyond the proper arcs of the root layer (`GlueImg`) is assumed, and no probabilistic input is used.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv logDerivFwd)
open QuantumZipper.RS (shiftDrive)
open scoped Real

namespace InteractingSLE.Sec5.CrossCond.StagedLaw

open WangWu hiding ratPt exists_ratPt_dist_lt
open GlueImg
open MartChar.RealFlow Restart.RetAux79

variable {W : ℝ → ℝ} {η : ℝ → ℂ}

/-- Boundary composition through the shifted chain: `F̄_{a+u} = F̄_a ∘ F̄^{(a)}_u` on `ℍ̄`. -/
theorem extendFrom_add_shift (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) {a u : ℝ}
    (ha : 0 ≤ a) (hu : 0 ≤ u) {x : ℂ} (hx : x ∈ Hbar) :
    extendFrom H (fwdMapInv W (a + u)) x =
      extendFrom H (fwdMapInv W a) (extendFrom H (fwdMapInv (shiftDrive W a) u) x) := by
  have hV := QuantumZipper.RS.continuous_shiftDrive hW a
  have hV0 : shiftDrive W a 0 = 0 := shiftDrive_zero W a
  have hBV := hη.hasBdryLimits_shift hW hW0 ha hu
  have hBa := hη.hasBdryLimits hW hW0 ha
  have hBt := hη.hasBdryLimits hW hW0 (add_nonneg ha hu)
  have h1 := hBV.tendsto hx
  have hp : extendFrom H (fwdMapInv (shiftDrive W a) u) x ∈ Hbar := by
    have : (𝓝[H] x).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (closure_H ▸ hx)
    rw [← closure_H]
    exact mem_closure_of_tendsto h1
      (eventually_nhdsWithin_of_forall fun w hw => QuantumZipper.RS.fwdMapInv_mem_H hV hV0 hu hw)
  have h2 : Tendsto (fun w => fwdMapInv W a (fwdMapInv (shiftDrive W a) u w)) (𝓝[H] x)
      (𝓝 (extendFrom H (fwdMapInv W a) (extendFrom H (fwdMapInv (shiftDrive W a) u) x))) :=
    (hBa.tendsto hp).comp (tendsto_nhdsWithin_iff.2 ⟨h1,
      eventually_nhdsWithin_of_forall fun w hw => QuantumZipper.RS.fwdMapInv_mem_H hV hV0 hu hw⟩)
  have h3 : Tendsto (fwdMapInv W (a + u)) (𝓝[H] x) _ := hBt.tendsto hx
  have : (𝓝[H] x).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (closure_H ▸ hx)
  refine tendsto_nhds_unique h3 (h2.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with w hw
  exact (QuantumZipper.RS.fwdMapInv_add_shift hW hW0 ha hu hw).symm


theorem isLoewnerTrace_futureArc (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) {a : ℝ}
    (ha : 0 ≤ a) : IsLoewnerTrace (shiftDrive W a) (futureArc W a) :=
  (hη.isLoewnerTrace_shift_and_extendFrom hW hW0 ha).1

/-- (L1) A real point over a later trace point lies strictly between the base images of the shifted chain. -/
theorem mem_Ioo_chartA_of_lt (hη : IsLoewnerTrace W η) (hγ : IsProperArc η) (hW : Continuous W) (hW0 : W 0 = 0)
    {a u : ℝ} (ha : 0 ≤ a) (hu : 0 ≤ u) {x τ : ℝ} (hτ : a < τ)
    (hx : extendFrom H (fwdMapInv W (a + u)) x = η τ) :
    chartAL (shiftDrive W a) u < x ∧ x < chartAR (shiftDrive W a) u := by
  have hV := QuantumZipper.RS.continuous_shiftDrive hW a
  have hV0 : shiftDrive W a 0 = 0 := shiftDrive_zero W a
  have hVt := isLoewnerTrace_futureArc hη hW hW0 ha
  rw [extendFrom_add_shift hη hW hW0 ha hu (mem_Hbar_of_im_eq_zero (by simp))] at hx
  have hp : extendFrom H (fwdMapInv (shiftDrive W a) u) x ∈ H := by
    by_contra hpH
    have him : (extendFrom H (fwdMapInv (shiftDrive W a) u) (x : ℂ)).im = 0 :=
      le_antisymm (not_lt.1 hpH) (extendFrom_im_nonneg hVt hV hV0 hu x)
    exact hη.extendFrom_not_mem hW hW0 ha him (hx ▸ mem_H_diff_fwdHull hη hγ ha hτ)
  exact chartAL_lt_of_extendFrom_mem_H hVt hV hV0 hu hp

/-- (L2) A real point over an earlier (or the same) trace point is not strictly between the base images of the
shifted chain. -/
theorem not_mem_Ioo_chartA_of_le (hη : IsLoewnerTrace W η) (hγ : IsProperArc η) (hW : Continuous W)
    (hW0 : W 0 = 0) {a u : ℝ} (ha : 0 < a) (hu : 0 < u) {x τ : ℝ} (hτ0 : 0 ≤ τ) (hτ : τ ≤ a)
    (hx : extendFrom H (fwdMapInv W (a + u)) x = η τ) :
    ¬ (chartAL (shiftDrive W a) u < x ∧ x < chartAR (shiftDrive W a) u) := by
  rintro ⟨h1, h2⟩
  have hV := QuantumZipper.RS.continuous_shiftDrive hW a
  have hV0 : shiftDrive W a 0 = 0 := shiftDrive_zero W a
  have hVt := isLoewnerTrace_futureArc hη hW hW0 ha.le
  have hVp := isProperArc_futureArc hη hγ hW hW0 ha.le
  have hp := extendFrom_mem_H_of_chartAL_lt hVt hVp hV hV0 hu h1 h2
  rw [extendFrom_add_shift hη hW hW0 ha.le hu.le (mem_Hbar_of_im_eq_zero (by simp)),
    extendFrom_fwdMapInv_eq hW hW0 ha.le hp] at hx
  have hm := QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hW hW0 ha.le hp
  rw [hx] at hm
  rcases hτ0.lt_or_eq with hτp | hτ0'
  · exact hm.2 (by rw [fwdHull_eq_image_Ioc hη hγ ha.le]; exact ⟨τ, ⟨hτp, hτ⟩, rfl⟩)
  · rw [← hτ0', hγ.zero] at hm
    have h0 : (0 : ℝ) < (0 : ℂ).im := hm.1
    simp at h0

/-- (L0) **The real points over a switch point are the two base images of the shifted chain** (the switch point is the
tip at time `a`, which has a single prime end). -/
theorem eq_chartA_of_extendFrom_eq (hη : IsLoewnerTrace W η) (hγ : IsProperArc η) (hW : Continuous W)
    (hW0 : W 0 = 0) {a u : ℝ} (ha : 0 < a) (hu : 0 < u) {x : ℝ}
    (hx : extendFrom H (fwdMapInv W (a + u)) x = η a) :
    x = chartAL (shiftDrive W a) u ∨ x = chartAR (shiftDrive W a) u := by
  have hV := QuantumZipper.RS.continuous_shiftDrive hW a
  have hV0 : shiftDrive W a 0 = 0 := shiftDrive_zero W a
  have hVt := isLoewnerTrace_futureArc hη hW hW0 ha.le
  have hVp := isProperArc_futureArc hη hγ hW hW0 ha.le
  rw [extendFrom_add_shift hη hW hW0 ha.le hu.le (mem_Hbar_of_im_eq_zero (by simp))] at hx
  have hpR : (extendFrom H (fwdMapInv (shiftDrive W a) u) (x : ℂ)).im = 0 := by
    by_contra hne
    have hpH : extendFrom H (fwdMapInv (shiftDrive W a) u) (x : ℂ) ∈ H :=
      lt_of_le_of_ne (extendFrom_im_nonneg hVt hV hV0 hu.le x) (Ne.symm hne)
    rw [extendFrom_fwdMapInv_eq hW hW0 ha.le hpH] at hx
    have hm := QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hW hW0 ha.le hpH
    rw [hx] at hm
    exact hm.2 (by rw [fwdHull_eq_image_Ioc hη hγ ha.le]; exact ⟨a, ⟨ha, le_rfl⟩, rfl⟩)
  have hpe : extendFrom H (fwdMapInv (shiftDrive W a) u) (x : ℂ) =
      (((extendFrom H (fwdMapInv (shiftDrive W a) u) (x : ℂ)).re : ℝ) : ℂ) :=
    Complex.ext (by simp) (by simp [hpR])
  rw [hpe] at hx
  have h0 := eq_zero_of_extendFrom_eq_tip hη hγ hW hW0 ha hx
  rcases extendFrom_real_cases hVt hVp hV hV0 hu hpR with ⟨-, h⟩ | ⟨hp, -⟩ | ⟨hp, -⟩
  · exact h
  · exact absurd h0 hp.ne'
  · exact absurd h0 hp.ne

/-- **The piece of a real point of the slit image.** For a simple proper Loewner trace and `0 < a`, `0 < u`, a real
point `x` over the trace point `η τ` at time `a + u` lies strictly between the base images of the chain shifted by `a`
iff `τ > a`. -/
theorem mem_Ioo_chartA_iff (hη : IsLoewnerTrace W η) (hγ : IsProperArc η) (hW : Continuous W) (hW0 : W 0 = 0)
    {a u : ℝ} (ha : 0 < a) (hu : 0 < u) {x τ : ℝ} (hτ0 : 0 ≤ τ)
    (hx : extendFrom H (fwdMapInv W (a + u)) x = η τ) :
    (chartAL (shiftDrive W a) u < x ∧ x < chartAR (shiftDrive W a) u) ↔ a < τ :=
  ⟨fun h => lt_of_not_ge fun hle => not_mem_Ioo_chartA_of_le hη hγ hW hW0 ha hu hτ0 hle hx h,
    fun h => mem_Ioo_chartA_of_lt hη hγ hW hW0 ha.le hu.le h hx⟩


section Order

variable {Wα : ℝ → ℝ} {α : ℝ → ℂ} {t : ℝ} {Wβ : ℝ → ℝ} {s : ℝ} {W' : ℝ → ℝ} {η' : ℝ → ℂ} {T : ℝ}

/-- **The counterflow chart preserves the time order along the flow trace.** If the image chain's simple trace `η'`
satisfies `K'_T = Ψ(K_t)` and `η'(T) = Ψ(α t)`, then for trace times `a, τ ∈ (0, t]` with image times `A, τ'`
(`η' A = Ψ(α a)`, `η' τ' = Ψ(α τ)`), `a < τ ↔ A < τ'`. -/
theorem lt_iff_lt_of_eq_revChart (hα : IsLoewnerTrace Wα α) (hαp : IsProperArc α) (ht : 0 ≤ t)
    (hWβ : Continuous Wβ) (hWβ0 : Wβ 0 = 0) (hs : 0 ≤ s) (hη' : IsLoewnerTrace W' η') (hη'p : IsProperArc η')
    (hT : 0 ≤ T) (hdisj : Disjoint (fwdHull Wα t) (negInv '' fwdHull Wβ s))
    (hK' : fwdHull W' T = revChart Wβ s '' fwdHull Wα t) (htip : η' T = revChart Wβ s (α t))
    {a τ A τ' : ℝ} (ha : 0 < a) (hat : a ≤ t) (hτ : 0 < τ) (hτt : τ ≤ t) (hA : 0 ≤ A) (hτ'0 : 0 ≤ τ')
    (heA : η' A = revChart Wβ s (α a)) (heτ : η' τ' = revChart Wβ s (α τ)) :
    a < τ ↔ A < τ' := by
  classical
  set f₁ : ℝ → ℂ := fun r => revChart Wβ s (α r) with hf₁
  have hmemG : ∀ r, 0 < r → r ≤ t → α r ∈ H \ negInv '' fwdHull Wβ s := fun r hr hrt => by
    have hK : α r ∈ fwdHull Wα t := by rw [fwdHull_eq_image_Ioc hα hαp ht]; exact ⟨r, ⟨hr, hrt⟩, rfl⟩
    exact ⟨hαp.mem_H r hr, fun hG => disjoint_left.1 hdisj hK hG⟩
  have hinj : ∀ r r', 0 < r → r ≤ t → 0 < r' → r' ≤ t → f₁ r = f₁ r' → r = r' := by
    intro r r' hr hrt hr' hr't e
    exact hαp.inj (mem_Ici.2 hr.le) (mem_Ici.2 hr'.le)
      (injOn_revChart hWβ hWβ0 hs (hmemG r hr hrt) (hmemG r' hr' hr't) e)
  have hcont : ∀ c, 0 < c → ContinuousOn f₁ (Icc c t) := fun c hc =>
    (continuousOn_revChart hWβ hs).comp (hαp.cont.mono fun r hr => mem_Ici.2 (hc.le.trans hr.1))
      fun r hr => hmemG r (hc.trans_le hr.1) hr.2
  have hrange : ∀ r, 0 < r → r ≤ t → ∃ p : Icc (0 : ℝ) T, η' p = f₁ r := by
    intro r hr hrt
    have h1 : f₁ r ∈ fwdHull W' T := by
      rw [hK']; exact ⟨α r, by rw [fwdHull_eq_image_Ioc hα hαp ht]; exact ⟨r, ⟨hr, hrt⟩, rfl⟩, rfl⟩
    rw [fwdHull_eq_image_Ioc hη' hη'p hT] at h1
    obtain ⟨r', hr', e⟩ := h1
    exact ⟨⟨r', hr'.1.le, hr'.2⟩, e⟩
  -- the closed embedding of the image arc
  set e : Icc (0 : ℝ) T → ℂ := fun p => η' p with he
  have : CompactSpace (Icc (0 : ℝ) T) := isCompact_iff_compactSpace.1 isCompact_Icc
  have hec : Continuous e :=
    hη'p.cont.comp_continuous continuous_subtype_val fun p => mem_Ici.2 p.2.1
  have hei : Function.Injective e := fun p q h => Subtype.ext (hη'p.inj (mem_Ici.2 p.2.1) (mem_Ici.2 q.2.1) h)
  have hemb := hec.isClosedEmbedding hei
  set g : ℝ → Icc (0 : ℝ) T := fun r => if h : ∃ p : Icc (0 : ℝ) T, η' p = f₁ r then h.choose else ⟨0, le_rfl, hT⟩
    with hg
  have hge : ∀ r, 0 < r → r ≤ t → η' (g r) = f₁ r := fun r hr hrt => by
    have h := hrange r hr hrt
    simp only [hg]
    split
    · next h' => exact h'.choose_spec
    · exact absurd h ‹_›
  set G : ℝ → ℝ := fun r => (g r : ℝ) with hG
  have hGc : ∀ c, 0 < c → ContinuousOn G (Icc c t) := fun c hc => by
    have h1 : ContinuousOn (e ∘ g) (Icc c t) :=
      (hcont c hc).congr fun r hr => hge r (hc.trans_le hr.1) hr.2
    exact continuous_subtype_val.comp_continuousOn (hemb.isInducing.continuousOn_iff.2 h1)
  have hGeq : ∀ r, 0 < r → r ≤ t → ∀ r', 0 ≤ r' → η' r' = f₁ r → G r = r' := fun r hr hrt r' hr' h =>
    hη'p.inj (mem_Ici.2 (g r).2.1) (mem_Ici.2 hr') ((hge r hr hrt).trans h.symm)
  have hGT : G t = T := hGeq t (ha.trans_le hat) le_rfl T hT htip
  have hGa : G a = A := hGeq a ha hat A hA heA
  have hGτ : G τ = τ' := hGeq τ hτ hτt τ' hτ'0 heτ
  have hGle : ∀ r, G r ≤ T := fun r => (g r).2.2
  constructor
  · intro hlt
    by_contra hle
    push Not at hle
    have hne : τ' ≠ A := fun h => by
      have := hinj τ a hτ hτt ha hat (heτ.symm.trans ((congrArg η' h).trans heA))
      linarith
    have hmem : A ∈ Icc (G τ) (G t) := ⟨by rw [hGτ]; exact hle, by rw [hGT, ← hGa]; exact hGle a⟩
    obtain ⟨r, hr, hrA⟩ := intermediate_value_Icc hτt (hGc τ hτ) hmem
    have hr0 : 0 < r := hτ.trans_le hr.1
    have := hinj r a hr0 hr.2 ha hat ((hge r hr0 hr.2).symm.trans ((congrArg η' hrA).trans heA))
    linarith [hr.1]
  · intro hlt
    by_contra hle
    push Not at hle
    have hmem : τ' ∈ Icc (G a) (G t) := ⟨by rw [hGa]; exact hlt.le, by rw [hGT, ← hGτ]; exact hGle τ⟩
    obtain ⟨r, hr, hrτ⟩ := intermediate_value_Icc hat (hGc a ha) hmem
    have hr0 : 0 < r := ha.trans_le hr.1
    have hrτ' := hinj r τ hr0 hr.2 hτ hτt ((hge r hr0 hr.2).symm.trans ((congrArg η' hrτ).trans heτ))
    have hτa : τ = a := le_antisymm hle (hrτ' ▸ hr.1)
    rw [← hGτ, hτa, hGa] at hlt
    exact lt_irrefl _ hlt

end Order


section Transport

variable {Wα : ℝ → ℝ} {α : ℝ → ℂ} {t : ℝ} {Wβ : ℝ → ℝ} {s : ℝ} {W' : ℝ → ℝ} {η' : ℝ → ℂ} {T : ℝ}

/-- **Over a slit point of the image chart, `Θ` lands over the same physical trace point.** If `F̄′_T(x) ∈ ℍ` and
`Θ → x₁` (real) at `x`, then there are trace times `τ ∈ (0, t]`, `τ' ∈ (0, T]` with `F̄′_T(x) = η'(τ') = Ψ(α τ)` and
`F̄_t(x₁) = α τ`. -/
theorem exists_trace_of_imgTheta (hα : IsLoewnerTrace Wα α) (hαp : IsProperArc α) (hWα : Continuous Wα)
    (hWα0 : Wα 0 = 0) (ht : 0 ≤ t) (hWβ : Continuous Wβ) (hWβ0 : Wβ 0 = 0) (hs : 0 ≤ s)
    (hη' : IsLoewnerTrace W' η') (hη'p : IsProperArc η') (hW' : Continuous W') (hW'0 : W' 0 = 0) (hT : 0 ≤ T)
    (hdisj : Disjoint (fwdHull Wα t) (negInv '' fwdHull Wβ s))
    (hK' : fwdHull W' T = revChart Wβ s '' fwdHull Wα t) {x x₁ : ℝ}
    (hxH : extendFrom H (fwdMapInv W' T) x ∈ H)
    (hΘ : Tendsto (imgTheta Wα t Wβ s W' T) (𝓝[H] (x : ℂ)) (𝓝 (x₁ : ℂ))) :
    ∃ τ ∈ Ioc 0 t, ∃ τ' ∈ Ioc 0 T, extendFrom H (fwdMapInv W' T) x = η' τ' ∧
      η' τ' = revChart Wβ s (α τ) ∧ extendFrom H (fwdMapInv Wα t) x₁ = α τ := by
  have hxR : ((x : ℂ)).im = 0 := by simp
  have hxK : extendFrom H (fwdMapInv W' T) x ∈ fwdHull W' T := by
    by_contra h
    exact hη'.extendFrom_not_mem hW' hW'0 hT hxR ⟨hxH, h⟩
  have hxK' := hxK
  rw [fwdHull_eq_image_Ioc hη' hη'p hT] at hxK
  obtain ⟨τ', hτ', hτ'e⟩ := hxK
  rw [hK', fwdHull_eq_image_Ioc hα hαp ht] at hxK'
  obtain ⟨_, ⟨τ, hτ, rfl⟩, hτe⟩ := hxK'
  have hmemG : α τ ∈ H \ negInv '' fwdHull Wβ s := by
    have hK : α τ ∈ fwdHull Wα t := by rw [fwdHull_eq_image_Ioc hα hαp ht]; exact ⟨τ, hτ, rfl⟩
    exact ⟨hαp.mem_H τ hτ.1, fun hG => disjoint_left.1 hdisj hK hG⟩
  refine ⟨τ, hτ, τ', hτ', hτ'e.symm, hτ'e.trans hτe.symm, ?_⟩
  -- `Φ = Ψ⁻¹ ∘ F'_T → α τ`
  have hF : Tendsto (fwdMapInv W' T) (𝓝[H] (x : ℂ)) (𝓝 (extendFrom H (fwdMapInv W' T) x)) :=
    (hη'.hasBdryLimits hW' hW'0 hT).tendsto (mem_Hbar_of_im_eq_zero hxR)
  have hΦ : Tendsto (fun y => revChartInv Wβ s (fwdMapInv W' T y)) (𝓝[H] (x : ℂ)) (𝓝 (α τ)) := by
    have hc := ((continuousOn_revChartInv hWβ hWβ0 hs).continuousAt (QuantumZipper.isOpen_H.mem_nhds hxH)).tendsto
    rw [← hτe] at hc hF
    rw [revChartInv_revChart hWβ hWβ0 hs hmemG] at hc
    exact hc.comp hF
  -- `F_t ∘ Θ = Φ` on `ℍ`
  have hmem : ∀ y ∈ H, revChartInv Wβ s (fwdMapInv W' T y) ∈ H \ fwdHull Wα t := fun y hy => by
    have h := revChartInv_fwdMapInv_mem hWβ hWβ0 hs hW' hW'0 hT hK' hy
    exact ⟨h.1, fun hK => h.2 (Or.inl hK)⟩
  have hΘH : ∀ y ∈ H, imgTheta Wα t Wβ s W' T y ∈ H := fun y hy =>
    QuantumZipper.FwdHolo.mapsTo_fwdMap hWα ht (hmem y hy)
  have hx₁ : (x₁ : ℂ) ∈ Hbar := mem_Hbar_of_im_eq_zero (by simp)
  have h1 : Tendsto (fun y => fwdMapInv Wα t (imgTheta Wα t Wβ s W' T y)) (𝓝[H] (x : ℂ))
      (𝓝 (extendFrom H (fwdMapInv Wα t) x₁)) :=
    ((hα.hasBdryLimits hWα hWα0 ht).tendsto hx₁).comp
      (tendsto_nhdsWithin_iff.2 ⟨hΘ, eventually_nhdsWithin_of_forall hΘH⟩)
  have := nhdsWithin_H_neBot x
  refine tendsto_nhds_unique h1 (hΦ.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact (QuantumZipper.RS.fwdMapInv_fwdMap hWα hWα0 ht (hmem y hy)).symm

/-- **Θ preserves the pieces of the slit** (deterministic data transport). Let `0 < a < t` be a flow time with image
time `A ∈ (0, T)` (`η' A = Ψ(α a)`). At a slit point `x` of the image chart (`F̄′_T(x) ∈ ℍ`) where `Θ` tends to the
real point `x₁`, the point `x₁` lies strictly between the two base images of the flow chain shifted by `a` iff `x`
lies strictly between the two base images of the image chain shifted by `A`: the trace beyond `α(a)` is read in the
same place in both charts. -/
theorem mem_Ioo_chartA_iff_of_imgTheta (hα : IsLoewnerTrace Wα α) (hαp : IsProperArc α) (hWα : Continuous Wα)
    (hWα0 : Wα 0 = 0) (ht : 0 ≤ t) (hWβ : Continuous Wβ) (hWβ0 : Wβ 0 = 0) (hs : 0 ≤ s)
    (hη' : IsLoewnerTrace W' η') (hη'p : IsProperArc η') (hW' : Continuous W') (hW'0 : W' 0 = 0) (hT : 0 ≤ T)
    (hdisj : Disjoint (fwdHull Wα t) (negInv '' fwdHull Wβ s))
    (hK' : fwdHull W' T = revChart Wβ s '' fwdHull Wα t) (htip : η' T = revChart Wβ s (α t))
    {a A : ℝ} (ha : 0 < a) (hat : a < t) (hA : 0 < A) (hAT : A < T) (heA : η' A = revChart Wβ s (α a))
    {x x₁ : ℝ} (hxH : extendFrom H (fwdMapInv W' T) x ∈ H)
    (hΘ : Tendsto (imgTheta Wα t Wβ s W' T) (𝓝[H] (x : ℂ)) (𝓝 (x₁ : ℂ))) :
    (chartAL (shiftDrive Wα a) (t - a) < x₁ ∧ x₁ < chartAR (shiftDrive Wα a) (t - a)) ↔
      (chartAL (shiftDrive W' A) (T - A) < x ∧ x < chartAR (shiftDrive W' A) (T - A)) := by
  obtain ⟨τ, hτ, τ', hτ', hx, heτ, hx₁⟩ :=
    exists_trace_of_imgTheta hα hαp hWα hWα0 ht hWβ hWβ0 hs hη' hη'p hW' hW'0 hT hdisj hK' hxH hΘ
  have h1 := mem_Ioo_chartA_iff hα hαp hWα hWα0 ha (sub_pos.2 hat) hτ.1.le
    (show extendFrom H (fwdMapInv Wα (a + (t - a))) x₁ = α τ by rw [add_sub_cancel]; exact hx₁)
  have h2 := mem_Ioo_chartA_iff hη' hη'p hW' hW'0 hA (sub_pos.2 hAT) hτ'.1.le
    (show extendFrom H (fwdMapInv W' (A + (T - A))) x = η' τ' by rw [add_sub_cancel]; exact hx)
  rw [h1, h2]
  exact lt_iff_lt_of_eq_revChart hα hαp ht hWβ hWβ0 hs hη' hη'p hT hdisj hK' htip ha hat.le hτ.1 hτ.2 hA.le
    hτ'.1.le heA heτ

/-- **A flow born mark is seen only at an image born mark.** If `Θ → x₁` at a slit point `x` and `x₁` is one of the
two base images of the flow chain shifted by `a`, then `x` is one of the two base images of the image chain shifted by
the image time `A`. -/
theorem eq_imgChartA_of_eq_chartA (hα : IsLoewnerTrace Wα α) (hαp : IsProperArc α) (hWα : Continuous Wα)
    (hWα0 : Wα 0 = 0) (ht : 0 ≤ t) (hWβ : Continuous Wβ) (hWβ0 : Wβ 0 = 0) (hs : 0 ≤ s)
    (hη' : IsLoewnerTrace W' η') (hη'p : IsProperArc η') (hW' : Continuous W') (hW'0 : W' 0 = 0) (hT : 0 ≤ T)
    (hdisj : Disjoint (fwdHull Wα t) (negInv '' fwdHull Wβ s))
    (hK' : fwdHull W' T = revChart Wβ s '' fwdHull Wα t)
    {a A : ℝ} (ha : 0 < a) (hat : a < t) (hA : 0 < A) (hAT : A < T) (heA : η' A = revChart Wβ s (α a))
    {x x₁ : ℝ} (hxH : extendFrom H (fwdMapInv W' T) x ∈ H)
    (hΘ : Tendsto (imgTheta Wα t Wβ s W' T) (𝓝[H] (x : ℂ)) (𝓝 (x₁ : ℂ)))
    (hx₁ : x₁ = chartAL (shiftDrive Wα a) (t - a) ∨ x₁ = chartAR (shiftDrive Wα a) (t - a)) :
    x = chartAL (shiftDrive W' A) (T - A) ∨ x = chartAR (shiftDrive W' A) (T - A) := by
  obtain ⟨τ, hτ, τ', hτ', hx, heτ, hx₁e⟩ :=
    exists_trace_of_imgTheta hα hαp hWα hWα0 ht hWβ hWβ0 hs hη' hη'p hW' hW'0 hT hdisj hK' hxH hΘ
  have hV := QuantumZipper.RS.continuous_shiftDrive hWα a
  have hV0 : shiftDrive Wα a 0 = 0 := shiftDrive_zero Wα a
  have hVt := isLoewnerTrace_futureArc hα hWα hWα0 ha.le
  have hVp := isProperArc_futureArc hα hαp hWα hWα0 ha.le
  have hFa : extendFrom H (fwdMapInv Wα t) x₁ = α a := by
    have h := extendFrom_add_shift hα hWα hWα0 ha.le (sub_pos.2 hat).le (x := (x₁ : ℂ))
      (mem_Hbar_of_im_eq_zero (by simp))
    rw [add_sub_cancel] at h
    rw [h]
    rcases hx₁ with rfl | rfl
    · rw [extendFrom_chartAL_eq_zero hVt hVp hV hV0 (sub_pos.2 hat), extendFrom_zero hα hWα hWα0 ha.le]
    · rw [extendFrom_chartAR_eq_zero hVt hVp hV hV0 (sub_pos.2 hat), extendFrom_zero hα hWα hWα0 ha.le]
  have hτa : τ = a := hαp.inj (mem_Ici.2 hτ.1.le) (mem_Ici.2 ha.le) (hx₁e.symm.trans hFa)
  have hτ'A : τ' = A := hη'p.inj (mem_Ici.2 hτ'.1.le) (mem_Ici.2 hA.le) (by rw [heτ, heA, hτa])
  refine eq_chartA_of_extendFrom_eq hη' hη'p hW' hW'0 hA (sub_pos.2 hAT) ?_
  rw [add_sub_cancel, hx, hτ'A]

end Transport

section ImgTime

variable {Wα Wβ W' : ℝ → ℝ} {t s T : ℝ}

/-- **The image switch time.** A flow switch time `a ∈ (0, t)` has an image time `A ∈ (0, T)` with `η' A = Ψ(α a)`. -/
theorem exists_imgTime {α : ℝ → ℂ} (hα : IsLoewnerTrace Wα α) (hαp : IsProperArc α) (ht : 0 ≤ t)
    (hWβ : Continuous Wβ) (hWβ0 : Wβ 0 = 0) (hs : 0 ≤ s) {η' : ℝ → ℂ} (hη' : IsLoewnerTrace W' η')
    (hη'p : IsProperArc η') (hT : 0 ≤ T) (hdisj : Disjoint (fwdHull Wα t) (negInv '' fwdHull Wβ s))
    (hK' : fwdHull W' T = revChart Wβ s '' fwdHull Wα t) (htip : η' T = revChart Wβ s (α t))
    {a : ℝ} (ha : 0 < a) (hat : a < t) : ∃ A, 0 < A ∧ A < T ∧ η' A = revChart Wβ s (α a) := by
  have hK : α a ∈ fwdHull Wα t := by rw [fwdHull_eq_image_Ioc hα hαp ht]; exact ⟨a, ⟨ha, hat.le⟩, rfl⟩
  have h1 : revChart Wβ s (α a) ∈ fwdHull W' T := by rw [hK']; exact ⟨α a, hK, rfl⟩
  rw [fwdHull_eq_image_Ioc hη' hη'p hT] at h1
  obtain ⟨A, hA, hAe⟩ := h1
  refine ⟨A, hA.1, lt_of_le_of_ne hA.2 fun h => ?_, hAe⟩
  have hmem : ∀ r, 0 < r → r ≤ t → α r ∈ H \ negInv '' fwdHull Wβ s := fun r hr hrt => by
    have hK : α r ∈ fwdHull Wα t := by rw [fwdHull_eq_image_Ioc hα hαp ht]; exact ⟨r, ⟨hr, hrt⟩, rfl⟩
    exact ⟨hαp.mem_H r hr, fun hG => disjoint_left.1 hdisj hK hG⟩
  have e : revChart Wβ s (α t) = revChart Wβ s (α a) := by rw [← htip, ← hAe, h]
  have := hαp.inj (mem_Ici.2 (ha.trans hat).le) (mem_Ici.2 ha.le)
    (injOn_revChart hWβ hWβ0 hs (hmem t (ha.trans hat) le_rfl) (hmem a ha hat.le) e)
  linarith

end ImgTime

end InteractingSLE.Sec5.CrossCond.StagedLaw
