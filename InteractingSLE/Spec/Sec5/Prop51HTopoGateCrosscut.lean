/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop51HTopoGateLift

/-! # Construction of the completed finite excursion crosscuts -/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv)

namespace InteractingSLE.Sec5.Prop51HTopo

open WangWu hiding ratPt exists_ratPt_dist_lt
open Prop51G

/-- Every finite excursion with positive starting time completes to a compact
simple real-to-real crosscut, with the original time orientation. The only tip
avoidance premise is the one already supplied by `PositiveGateExitStatement`.
Both endpoints are constructed; their order remains to be determined. -/
theorem exists_finiteExcursionCrosscut {η β : ℝ → ℂ} {w : ℝ → ℝ} {s a b : ℝ}
    (hη : IsProperArc η) (hβ : IsLoewnerTrace w β)
    (hw : Continuous w) (hw0 : w 0 = 0) (hs : 0 ≤ s)
    (ha : 0 < a) (hab : a < b)
    (hD : MapsTo η (Ioo a b) (H \ cfHullQ w s))
    (haD : η a ∉ H \ cfHullQ w s) (hbD : η b ∉ H \ cfHullQ w s)
    (htip : negInv (β s) ∉ arcRange η) :
    Nonempty (FiniteExcursionCrosscut η w s a b) := by
  let α : ℝ → ℂ := fun t => negInv (η t)
  let m : ℝ := (a + b) / 2
  have ham : a < m := by dsimp [m]; linarith
  have hmb : m < b := by dsimp [m]; linarith
  have hαc : ContinuousOn α (Icc a b) := continuousOn_negInv.comp
    (hη.cont.mono fun t ht => ha.le.trans ht.1)
    (fun t ht => hη.mem_H t (ha.trans_le ht.1))
  have hαD : MapsTo α (Ioo a b) (H \ fwdHull w s) :=
    fun _ ht => negInv_notMem_fwdHull (hD ht)
  have hαend : ∀ t ∈ Icc a b, η t ∉ H \ cfHullQ w s → α t ∉ H \ fwdHull w s := by
    intro t ht hnot hn
    apply hnot
    refine ⟨hη.mem_H t (ha.trans_le ht.1), ?_⟩
    rintro ⟨z, hz, he⟩
    apply hn.2
    change negInv (η t) ∈ fwdHull w s
    rw [← he, negInv_negInv']
    exact hz
  obtain ⟨q₀, hq₀, hlim₀⟩ := exists_tendsto_fwdMap_right hβ hw hw0 hs ham
    (hαc.mono (Icc_subset_Icc le_rfl hmb.le))
    (fun t ht => hαD ⟨ht.1, ht.2.trans_lt hmb⟩)
    (hαend a ⟨le_rfl, hab.le⟩ haD)
  obtain ⟨q₁, hq₁, hlim₁⟩ := Sec6.exists_tendsto_lift hβ hw hw0 hs hmb
    (hαc.mono (Icc_subset_Icc ham.le le_rfl))
    (fun t ht => hαD ⟨ham.trans_le ht.1, ht.2⟩)
    (hαend b ⟨hab.le, le_rfl⟩ hbD)
  rw [YuanSimpleApprox.trMap_zero_left hw0] at hq₁
  let G : ℝ → ℂ := fun t => fwdMap w s (α t)
  have hGc : ContinuousOn G (Ioo a b) :=
    (QuantumZipper.FwdHolo.differentiableOn_fwdMap hw hs).continuousOn.comp
      (hαc.mono Ioo_subset_Icc_self) hαD
  let γ : ℝ → ℂ := extendFrom (Ioo a b) G
  have hγc : ContinuousOn γ (Icc a b) := continuousOn_Icc_extendFrom_Ioo hGc hlim₀ hlim₁
  have hγ₀ : γ a = (q₀ : ℂ) := eq_lim_at_left_extendFrom_Ioo hab hlim₀
  have hγ₁ : γ b = (q₁ : ℂ) := eq_lim_at_right_extendFrom_Ioo hab hlim₁
  have hγG : EqOn γ G (Ioo a b) := extendFrom_extends hGc
  have hFγ : ∀ t ∈ Icc a b, extendFrom H (fwdMapInv w s) (γ t) = α t := by
    intro t ht
    rcases eq_endpoints_or_mem_Ioo_of_mem_Icc ht with rfl | rfl | hti
    · rwa [hγ₀]
    · rwa [hγ₁]
    · rw [hγG hti, extendFrom_fwdMapInv_eq hw hw0 hs
        (QuantumZipper.FwdHolo.mapsTo_fwdMap hw hs (hαD hti))]
      exact QuantumZipper.RS.fwdMapInv_fwdMap hw hw0 hs (hαD hti)
  have hγne : ∀ t ∈ Icc a b, γ t ≠ 0 := by
    intro t ht he
    have h := hFγ t ht
    rw [he, extendFrom_zero hβ hw hw0 hs] at h
    have heq : negInv (β s) = η t := by
      simpa only [α, negInv_negInv'] using congrArg negInv h
    exact htip ⟨t, ha.le.trans ht.1, heq.symm⟩
  have hγi : InjOn γ (Icc a b) := by
    intro u hu v hv he
    have heq : α u = α v := (hFγ u hu).symm.trans
      ((congrArg (extendFrom H (fwdMapInv w s)) he).trans (hFγ v hv))
    exact hη.inj (ha.le.trans hu.1) (ha.le.trans hv.1) (negInv_involutive.injective heq)
  refine ⟨⟨fun t => negInv (γ t), ?_, ?_, -q₀⁻¹, -q₁⁻¹, ?_, ?_, ?_, ?_⟩⟩
  · intro t ht
    exact ((continuousAt_negInv (hγne t ht)).comp_continuousWithinAt (hγc t ht))
  · intro u hu v hv he
    exact hγi hu hv (negInv_involutive.injective he)
  · simp only [hγ₀, negInv, ofReal_neg, ofReal_inv]
  · simp only [hγ₁, negInv, ofReal_neg, ofReal_inv]
  · intro t ht
    change negInv (γ t) = revChart w s (η t)
    rw [hγG ht]
    rfl
  · intro t ht
    change negInv (γ t) ∈ H
    rw [hγG ht]
    exact negInv_mem_H (QuantumZipper.FwdHolo.mapsTo_fwdMap hw hs (hαD ht))

/-- The constructed real endpoints are distinct; identifying or ordering them
is never an extra premise of the completed excursion. -/
theorem FiniteExcursionCrosscut.start_ne_finish {η : ℝ → ℂ} {w : ℝ → ℝ} {s a b : ℝ}
    (c : FiniteExcursionCrosscut η w s a b) (hab : a < b) : c.start ≠ c.finish := by
  intro he
  have hp : c.path a = c.path b := c.start_eq.trans
    ((congrArg Complex.ofReal he).trans c.finish_eq.symm)
  exact hab.ne (c.injective ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩ hp)

/-- The starting gate is the actual incoming prime-end limit. -/
theorem FiniteExcursionCrosscut.tendsto_start {η : ℝ → ℂ} {w : ℝ → ℝ} {s a b : ℝ}
    (c : FiniteExcursionCrosscut η w s a b) (hab : a < b) :
    Tendsto (fun t => revChart w s (η t)) (𝓝[>] a) (𝓝 (c.start : ℂ)) := by
  have he : ∀ᶠ t in 𝓝[>] a, t ∈ Ioo a b := Ioo_mem_nhdsGT hab
  have hle : 𝓝[>] a ≤ 𝓝[Icc a b] a :=
    le_inf nhdsWithin_le_nhds (le_principal_iff.2
      (he.mono fun _ ht => Ioo_subset_Icc_self ht))
  have hlim := ((c.continuous a ⟨le_rfl, hab.le⟩).tendsto.mono_left hle)
  rw [c.start_eq] at hlim
  exact hlim.congr' (he.mono fun _ ht => c.interior_eq ht)

/-- The finishing gate is the actual outgoing prime-end limit. -/
theorem FiniteExcursionCrosscut.tendsto_finish {η : ℝ → ℂ} {w : ℝ → ℝ} {s a b : ℝ}
    (c : FiniteExcursionCrosscut η w s a b) (hab : a < b) :
    Tendsto (fun t => revChart w s (η t)) (𝓝[<] b) (𝓝 (c.finish : ℂ)) := by
  have he : ∀ᶠ t in 𝓝[<] b, t ∈ Ioo a b := Ioo_mem_nhdsLT hab
  have hle : 𝓝[<] b ≤ 𝓝[Icc a b] b :=
    le_inf nhdsWithin_le_nhds (le_principal_iff.2
      (he.mono fun _ ht => Ioo_subset_Icc_self ht))
  have hlim := ((c.continuous b ⟨hab.le, le_rfl⟩).tendsto.mono_left hle)
  rw [c.finish_eq] at hlim
  exact hlim.congr' (he.mono fun _ ht => c.interior_eq ht)

/-- A positively finishing completed excursion supplies the exact finite
alternative of `HasPositiveExcursionEnd`. -/
theorem FiniteExcursionCrosscut.hasPositiveExcursionEnd
    {η : ℝ → ℂ} {w : ℝ → ℝ} {s a b : ℝ}
    (c : FiniteExcursionCrosscut η w s a b) (ha : 0 < a) (hab : a < b)
    (hD : MapsTo η (Ioo a b) (H \ cfHullQ w s))
    (hbD : η b ∉ H \ cfHullQ w s) (hfinish : 0 < c.finish) :
    HasPositiveExcursionEnd η w s := by
  have ham : a < (a + b) / 2 := by linarith
  have hmb : (a + b) / 2 < b := by linarith
  exact Or.inl ⟨(a + b) / 2, b, c.finish, ha.trans ham, hmb, hfinish,
    fun t ht => hD ⟨ham.trans_le ht.1, ht.2⟩, hbD, c.tendsto_finish hab⟩

end InteractingSLE.Sec5.Prop51HTopo
