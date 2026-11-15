/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop49QExitMainNR
import InteractingSLE.Spec.Sec5.Prop49QExitMainGlue

/-!
# Proposition 4.9's exit pulled back from the counterflow chart to the flow line

Packet PROVE-GLUECOND11 (G6 of Proposition 4.9's direction, deterministic part; specification p. 120: "the curve
exits at an actual finite first upper endpoint … on the left side of `η′([0, τ′])`"; ruling R59). Let `η` be a proper
arc from `0`, `w` a continuous driver from `0` with a continuous Loewner trace `β` that does not return to `0` on
`(0, s]`, and `G = R(K_s)` the reflected hull (`R z = −1/z`). Suppose the image of `η` in the chart
`Ψ = revChart w s = R ∘ f_s ∘ R`, killed at its first contact with `G` and read in capacity time, has a finite terminal
capacity and converges there either to a point of `ℍ` or to a real point left of the left junction `Ψ(∞⁻)`. Then
(**`exit_of_imgExit`**) `η` reaches `G` at a finite time `t₀ > 0`, at a point `R(β(v))`, `0 < v ≤ s`, avoids `G`
before, and `Ψ ∘ η` tends to a negative real point as `t ↑ t₀`.

* A limit in `ℍ` is impossible: `η = Ψ⁻¹ ∘ (Ψ ∘ η)` would converge to a point of `ℍ \ G`, but `η(t₀) ∈ G` (or
  `η → ∞` if there is no contact).
* Without contact, `R(η(t)) → 0` in `ℍ \ K_s` while `f_s(R(η(t))) → −1/x₀ ∈ (0, f_s(0⁺))`, so `F̄_s(−1/x₀) = 0`,
  which the no-return lemma `extendFrom_ne_zero_of_noReturn` excludes (the pinch channel of R59).
* With contact at `t₀`, `R(η(t₀))` is a point of `K_s` that is a limit of `ℍ \ K_s`, hence a trace point
  (`ZhanGT4.mem_image_of_mem_fwdHull_of_mem_closure`), not `β(0) = 0`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Prop49Exit

open WangWu WangWu.ImgWord CrossCond.Word49 MartChar.RealFlow
open Sec7.Lemma71C (capClock)

variable {w : ℝ → ℝ} {β : ℝ → ℂ} {η : ℝ → ℂ} {s : ℝ}

/-- On the pre-contact times, the killed trace at the capacity of `u` is the curve at `u`. -/
theorem kTrace_capClock {γ : ℝ → ℂ} {P : Set ℝ} (hK : IsKilledArc γ P) {u : ℝ} (hu : u ∈ P) :
    kTrace γ P (capClock γ u).toNNReal = γ u := by
  simp only [kTrace, Real.coe_toNNReal _ (hK.capClock_nonneg hu), hK.kInv_capClock hu]

/-- **The capacity clock runs up to the terminal capacity** along any filter that eventually stays in `P` and
eventually passes every element of `P`. -/
theorem tendsto_capClock_kLife {γ : ℝ → ℂ} {P : Set ℝ} (hK : IsKilledArc γ P) {T' : ℝ≥0}
    (hT' : (T' : WithTop ℝ≥0) = kLife γ P) {L : Filter ℝ} (hLP : ∀ᶠ u in L, u ∈ P)
    (hLS : ∀ S ∈ P, ∀ᶠ u in L, S ≤ u) :
    Tendsto (fun u => (capClock γ u).toNNReal) L (𝓝[<] T') := by
  have hlt : ∀ u ∈ P, (capClock γ u).toNNReal < T' := fun u hu => by
    have := hK.lt_kLife hu
    rw [← hT'] at this
    exact_mod_cast this
  refine tendsto_nhdsWithin_iff.2 ⟨tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩, ?_⟩
  · have ha' : (a : WithTop ℝ≥0) < kLife γ P := by rw [← hT']; exact_mod_cast ha
    obtain ⟨S, hS, haS⟩ := lt_kLife_iff.1 ha'
    filter_upwards [hLP, hLS S hS] with u hu hSu
    have h1 := hK.strictMonoOn_capClock.monotoneOn hS hu hSu
    exact Real.lt_toNNReal_iff_coe_lt.2 (lt_of_lt_of_le haS h1)
  · filter_upwards [hLP] with u hu
    exact (hlt u hu).trans hb
  · filter_upwards [hLP] with u hu
    exact hlt u hu

/-- **Proposition 4.9's exit, pulled back to the flow line** (deterministic). -/
theorem exit_of_imgExit (hw : Continuous w) (hw0 : w 0 = 0) (hβ : IsLoewnerTrace w β) (hs : 0 < s)
    (hNR : ∀ v ∈ Ioc 0 s, β v ≠ 0) (hjL : 0 < rightImg w 0 s - w s) (hG : IsClosed (negInv '' fwdHull w s))
    (hη : IsProperArc η) {T' : ℝ≥0}
    (hT' : (T' : WithTop ℝ≥0) = kLife (imgCurve w s η) (preContact η (negInv '' fwdHull w s))) {z : ℂ}
    (hz : Tendsto (kTrace (imgCurve w s η) (preContact η (negInv '' fwdHull w s))) (𝓝[<] T') (𝓝 z))
    (hzalt : z ∈ H ∨ ∃ x₀ : ℝ, x₀ < junL w s ∧ z = x₀) :
    ∃ t₀ x₀ : ℝ, 0 < t₀ ∧ x₀ < 0 ∧ (∃ v ∈ Ioc 0 s, η t₀ = negInv (β v)) ∧
      (∀ t ∈ Ioo 0 t₀, η t ∉ negInv '' fwdHull w s) ∧
      Tendsto (fun t => revChart w s (η t)) (𝓝[<] t₀) (𝓝 (x₀ : ℂ)) := by
  set G := negInv '' fwdHull w s with hGdef
  set γ := imgCurve w s η with hγdef
  set P := preContact η G with hPdef
  have hK : IsKilledArc γ P := isKilledArc_imgCurve hw hw0 hs.le hG hη
  have hjL' : junL w s < 0 := by
    simp only [junL]; rw [neg_div]; exact neg_neg_of_pos (div_pos one_pos hjL)
  -- on positive pre-contact times the curve is `Ψ ∘ η`, with `η` off `G`
  have hPmem : ∀ u ∈ P, 0 < u → η u ∈ H \ G := fun u hu hu0 => ⟨hη.mem_H u hu0, hu.2 u ⟨hu.1, le_rfl⟩⟩
  -- the limit of the curve along a filter running up `P`
  have hlimγ : ∀ L : Filter ℝ, (∀ᶠ u in L, u ∈ P) → (∀ S ∈ P, ∀ᶠ u in L, S ≤ u) → Tendsto γ L (𝓝 z) := by
    intro L hLP hLS
    refine (hz.comp (tendsto_capClock_kLife hK hT' hLP hLS)).congr' ?_
    filter_upwards [hLP] with u hu
    exact kTrace_capClock hK hu
  -- the limit `x = −1/x₀` of the chart coordinate in the no-contact case
  have hxpos : ∀ x₀ : ℝ, x₀ < junL w s → 0 < -x₀⁻¹ ∧ -x₀⁻¹ < rightImg w 0 s - w s := by
    intro x₀ hx₀
    have hx₀n : x₀ < 0 := hx₀.trans hjL'
    refine ⟨neg_pos.2 (inv_lt_zero.2 hx₀n), ?_⟩
    have h1 : (junL w s)⁻¹ < x₀⁻¹ := (inv_lt_inv_of_neg hjL' hx₀n).2 hx₀
    have h2 : (junL w s)⁻¹ = -(rightImg w 0 s - w s) := by
      simp only [junL]; rw [neg_div, inv_neg, inv_div, div_one]
    linarith
  by_cases hbdd : BddAbove P
  · -- a first contact at `τ = sup P`
    set τ := sSup P with hτdef
    have hPne : P.Nonempty := ⟨0, hK.zero_mem⟩
    obtain ⟨S₁, hS₁, hS₁0⟩ := hK.exists_gt 0 hK.zero_mem
    have hτ0 : 0 < τ := lt_of_lt_of_le hS₁0 (le_csSup hbdd hS₁)
    have hτP : τ ∉ P := fun h => by
      obtain ⟨S', hS', hτS'⟩ := hK.exists_gt τ h
      exact absurd (le_csSup hbdd hS') (not_le.2 hτS')
    have hIco : ∀ t, 0 ≤ t → t < τ → t ∈ P := fun t ht htτ => by
      obtain ⟨S, hS, htS⟩ := exists_lt_of_lt_csSup hPne htτ
      exact hK.icc S hS ⟨ht, htS.le⟩
    have hητG : η τ ∈ G := by
      by_contra hn
      refine hτP ⟨hτ0.le, fun u hu => ?_⟩
      rcases hu.2.lt_or_eq with hlt | rfl
      · exact (hIco u hu.1 hlt).2 u ⟨hu.1, le_rfl⟩
      · exact hn
    have hLP : ∀ᶠ u in 𝓝[<] τ, u ∈ P ∧ 0 < u := by
      filter_upwards [Ioo_mem_nhdsLT hτ0] with u hu
      exact ⟨hIco u hu.1.le hu.2, hu.1⟩
    have hLS : ∀ S ∈ P, ∀ᶠ u in 𝓝[<] τ, S ≤ u := fun S hS => by
      have hSτ : S < τ := lt_of_le_of_ne (le_csSup hbdd hS) fun h => hτP (h ▸ hS)
      filter_upwards [Ioo_mem_nhdsLT hSτ] with u hu
      exact hu.1.le
    have hγz := hlimγ _ (hLP.mono fun u hu => hu.1) hLS
    have hηc : Tendsto η (𝓝[<] τ) (𝓝 (η τ)) :=
      ((hη.cont.continuousAt (Ici_mem_nhds hτ0)).tendsto).mono_left nhdsWithin_le_nhds
    have hγΨ : ∀ᶠ u in 𝓝[<] τ, γ u = revChart w s (η u) := by
      filter_upwards [hLP] with u hu
      exact imgCurve_of_pos hu.2
    rcases hzalt with hzH | ⟨x₀, hx₀, rfl⟩
    · -- a limit in `ℍ` would put `η(τ)` off `G`
      exfalso
      have hinv : Tendsto (fun u => revChartInv w s (γ u)) (𝓝[<] τ) (𝓝 (revChartInv w s z)) :=
        ((continuousOn_revChartInv hw hw0 hs.le).continuousAt (QuantumZipper.isOpen_H.mem_nhds hzH)).tendsto.comp hγz
      have hinv' : Tendsto η (𝓝[<] τ) (𝓝 (revChartInv w s z)) := by
        refine hinv.congr' ?_
        filter_upwards [hLP, hγΨ] with u hu he
        rw [he, revChartInv_revChart hw hw0 hs.le (hPmem u hu.1 hu.2)]
      have heq := tendsto_nhds_unique hηc hinv'
      exact (revChartInv_mem hw hw0 hs.le hzH).2 (heq ▸ hητG)
    · refine ⟨τ, x₀, hτ0, hx₀.trans hjL', ?_, fun t ht => (hIco t ht.1.le ht.2).2 t ⟨ht.1.le, le_rfl⟩, ?_⟩
      · obtain ⟨k, hkK, hke⟩ := hητG
        have hkH : k ∈ H := hkK.1
        have hkc : k ∈ closure (H \ fwdHull w s) := by
          have hne : η τ ≠ 0 := fun h => by
            have := hη.mem_H τ hτ0
            rw [h] at this
            exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from this)
          have hlim : Tendsto (fun u => negInv (η u)) (𝓝[<] τ) (𝓝 k) := by
            have := (continuousAt_negInv hne).tendsto.comp hηc
            rwa [← hke, negInv_negInv] at this
          exact mem_closure_of_tendsto hlim (by
            filter_upwards [hLP] with u hu
            exact negInv_notMem_fwdHull (hPmem u hu.1 hu.2))
        obtain ⟨v, hv, hvk⟩ := ZhanGT4.mem_image_of_mem_fwdHull_of_mem_closure hβ hs.le hkK hkc
        refine ⟨v, ⟨lt_of_le_of_ne hv.1 ?_, hv.2⟩, by rw [← hke, ← hvk]⟩
        intro h
        rw [← h, hβ.1] at hvk
        rw [← hvk] at hkH
        exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from hkH)
      · exact hγz.congr' hγΨ
  · -- no contact: the pinch channel, excluded by the no-return lemma
    exfalso
    have hPall : ∀ t, 0 ≤ t → t ∈ P := fun t ht => by
      rw [not_bddAbove_iff] at hbdd
      obtain ⟨S, hS, htS⟩ := hbdd t
      exact hK.icc S hS ⟨ht, htS.le⟩
    have hLP : ∀ᶠ u in (atTop : Filter ℝ), u ∈ P ∧ 0 < u := by
      filter_upwards [eventually_gt_atTop 0] with u hu
      exact ⟨hPall u hu.le, hu⟩
    have hγz := hlimγ atTop (hLP.mono fun u hu => hu.1) fun S _ => eventually_ge_atTop S
    have hγΨ : ∀ᶠ u in (atTop : Filter ℝ), γ u = revChart w s (η u) := by
      filter_upwards [hLP] with u hu
      exact imgCurve_of_pos hu.2
    have hηinf : Tendsto η atTop (Bornology.cobounded ℂ) := by
      rw [← tendsto_norm_atTop_iff_cobounded]; exact hη.tendsto
    rcases hzalt with hzH | ⟨x₀, hx₀, rfl⟩
    · have hinv : Tendsto (fun u => revChartInv w s (γ u)) atTop (𝓝 (revChartInv w s z)) :=
        ((continuousOn_revChartInv hw hw0 hs.le).continuousAt (QuantumZipper.isOpen_H.mem_nhds hzH)).tendsto.comp hγz
      have hinv' : Tendsto η atTop (𝓝 (revChartInv w s z)) := by
        refine hinv.congr' ?_
        filter_upwards [hLP, hγΨ] with u hu he
        rw [he, revChartInv_revChart hw hw0 hs.le (hPmem u hu.1 hu.2)]
      exact not_tendsto_nhds_of_tendsto_atTop hη.tendsto _ ((continuous_norm.tendsto _).comp hinv')
    · obtain ⟨hx0, hxR⟩ := hxpos x₀ hx₀
      have hx₀0 : (x₀ : ℂ) ≠ 0 := by exact_mod_cast (hx₀.trans hjL').ne
      -- `ξ = R ∘ η → 0` in `ℍ \ K_s`
      have hξ : Tendsto (fun u => negInv (η u)) atTop (𝓝 0) := by
        have := (tendsto_inv₀_cobounded.comp hηinf).neg
        simpa [negInv, Function.comp_def] using this
      have hξH : ∀ᶠ u in (atTop : Filter ℝ), negInv (η u) ∈ H \ fwdHull w s := by
        filter_upwards [hLP] with u hu
        exact negInv_notMem_fwdHull (hPmem u hu.1 hu.2)
      -- `f_s(ξ) → −1/x₀` within `ℍ`
      have hf : Tendsto (fun u => fwdMap w s (negInv (η u))) atTop (𝓝[H] ((-x₀⁻¹ : ℝ) : ℂ)) := by
        refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
        · have h1 := (continuousAt_negInv hx₀0).tendsto.comp hγz
          have he : negInv (x₀ : ℂ) = ((-x₀⁻¹ : ℝ) : ℂ) := by simp [negInv]
          rw [he] at h1
          refine h1.congr' ?_
          filter_upwards [hγΨ] with u he'
          simp only [Function.comp_apply, he', revChart, negInv_negInv]
        · filter_upwards [hξH] with u hu
          exact QuantumZipper.FwdHolo.mapsTo_fwdMap hw hs.le hu
      have hB := (hβ.hasBdryLimits hw hw0 hs.le).tendsto (ofReal_mem_Hbar (-x₀⁻¹))
      have h2 := hB.comp hf
      have h3 : Tendsto (fun u => negInv (η u)) atTop
          (𝓝 (extendFrom H (fwdMapInv w s) ((-x₀⁻¹ : ℝ) : ℂ))) := by
        refine h2.congr' ?_
        filter_upwards [hξH] with u hu
        exact QuantumZipper.RS.fwdMapInv_fwdMap hw hw0 hs.le hu
      exact extendFrom_ne_zero_of_noReturn hβ hw hw0 hs hNR hx0 hxR (tendsto_nhds_unique h3 hξ)

end InteractingSLE.Sec5.Prop49Exit
