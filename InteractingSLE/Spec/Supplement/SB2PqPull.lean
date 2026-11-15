/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2PqHead
import InteractingSLE.Spec.Supplement.SB2OmCfg
import InteractingSLE.Spec.Sec5.TimeDensity
import InteractingSLE.Spec.Dimension.TraceBridge
import InteractingSLE.Foundations.Loewner.YuanCorollary13Slit
import InteractingSLE.Foundations.Loewner.Capacity

/-!
# The stage pull-back through a Loewner stage (deterministic)

Packet PROVE-GW2-NOTHR (round 8, D66's (P)). B's stage pull-back `Ln.IsStagePullback c g A₁ A₂ … (fwdHull W s)` in its
stage chart `c` passes to the chart `c.loewner Wτ τ` after the head (`Wτ = W` on `[0, τ]`, `τ ≤ s`), with B's own hull
read along the shifted driver: `fwdHull (shiftDrive W τ) (s − τ)`.

* `fwdMapInv_eq_of_eqOn_Icc`: the inverse map at `t` depends only on the driver on `[0, t]` (continuous drivers);
* **`isStagePullback_loewner`**: given the new chart's facts (domain chart, a boundary map continuous on `ℍ̄` within
  bounded distance of the identity, finite fibres) and `dom₁`, the stage pull-back holds in the new chart. `corr₂` is
  the Loewner composition `K_s ∖ K_τ = F_τ(K'_{s−τ})` (`Sec5.fwdHull_add_sdiff_eq_image`); `dom₂` is the old `dom₂`
  plus the head's hull inside `K_s`;
* **`dom_compl_subset_of_stageS2`**: `dom₁` from the S2 record `Om.IsStageS2 c Φ A₁ …` when the hull chart `Φ` covers
  `ℍ ∖ A₁` (`Φ.2.1 y = c.2.1 (·)` for every `y ∈ ℍ`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv)
open QuantumZipper.RS (shiftDrive)

namespace InteractingSLE.Theorem14.SB.Pq

open Restart Exist Exist.Staged Exist.StagedLaw

open Classical in
/-- **The inverse map at time `t` depends only on the driver on `[0, t]`** (continuous drivers). -/
theorem fwdMapInv_eq_of_eqOn_Icc {V V' : ℝ → ℝ} (hV : Continuous V) (hV' : Continuous V') {t : ℝ} (ht : 0 ≤ t)
    (h : ∀ r ∈ Icc (0 : ℝ) t, V r = V' r) : fwdMapInv V t = fwdMapInv V' t := by
  have hK := YuanCorollary13.fwdHull_eq_of_eqOn_Icc hV hV' ht h
  have hM : ∀ z, fwdMap V t z = fwdMap V' t z := fun z => fwdMap_eq_of_eqOn ht h
  have key : ∀ P Q : ℂ → Prop, P = Q →
      (if h : ∃! z', P z' then h.choose else (0 : ℂ)) =
        (if h : ∃! z', Q z' then h.choose else (0 : ℂ)) := by
    rintro P Q rfl
    rfl
  funext w
  exact key _ _ (funext fun z' => by rw [hK, hM z'])

/-- **The stage pull-back after a Loewner stage of the head.** -/
theorem isStagePullback_loewner {c : Chart} {g : ℂ → ℂ} {A₁ A₂ : Set ℂ} {W Wτ : ℝ → ℝ} {s τ : ℝ}
    (hp : Ln.IsStagePullback c g A₁ A₂ {w | c.2.1 w ∈ A₁} (fwdHull W s))
    (hW : Continuous W) (hW0 : W 0 = 0) (hWτ : Continuous Wτ) (hτ : 0 ≤ τ) (hτs : τ ≤ s)
    (hagree : ∀ r ∈ Icc (0 : ℝ) τ, Wτ r = W r)
    {X : Set ℂ} (hD : IsDomainChart (H \ fillH X) (c.loewner Wτ τ)) {g' : ℂ → ℂ} (hgc : ContinuousOn g' Hbar)
    (hgi : EqOn g' (c.loewner Wτ τ).2.1 H) {C : ℝ} (hgb : ∀ q ∈ Hbar, ‖g' q - q‖ ≤ C)
    (hgf : ∀ z, (g' ⁻¹' {z} ∩ Hbar).Finite) (hdom₁ : H \ ((c.loewner Wτ τ).dom : Set ℂ) ⊆ A₁) :
    Ln.IsStagePullback (c.loewner Wτ τ) g' A₁ A₂ {w | (c.loewner Wτ τ).2.1 w ∈ A₁}
      (fwdHull (shiftDrive W τ) (s - τ)) := by
  have hF : fwdMapInv Wτ τ = fwdMapInv W τ := fwdMapInv_eq_of_eqOn_Icc hWτ hW hτ hagree
  have hinv : ∀ w, (c.loewner Wτ τ).2.1 w = c.2.1 (fwdMapInv W τ w) := fun w => by
    show c.2.1 (fwdMapInv Wτ τ w) = _
    rw [hF]
  obtain ⟨-, hFm, hFi, hFs⟩ := isConformalBijection_fwdMapInv hW hW0 hτ
  have hc : c.IsConformal := hp.conf
  have hcl : (c.loewner Wτ τ).IsConformal := hD.1
  have hsτ : 0 ≤ s - τ := sub_nonneg.2 hτs
  have hdiff := Sec5.fwdHull_add_sdiff_eq_image hW hW0 hτ hsτ
  rw [add_sub_cancel] at hdiff
  refine Mk.isStagePullback_of_domainChart hD hgc hgi hgb hgf hdom₁ (fun z hz => ?_) (fun w hw => ?_)
  · -- `dom₂`: off the new domain, either off the old domain or in the head's hull
    obtain ⟨hzH, hzd⟩ := hz
    by_cases hzc : z ∈ (c.dom : Set ℂ)
    · rw [hc.coe_dom] at hzc
      obtain ⟨v, hvH, rfl⟩ := hzc
      by_cases hvK : v ∈ fwdHull W τ
      · exact (hp.corr₂ v hvH).2 ((QuantumZipper.fwdHull_mono (W := W)).1 hτs hvK)
      · exfalso
        obtain ⟨w', hw'H, hw'⟩ := hFs ⟨hvH, hvK⟩
        apply hzd
        rw [hcl.coe_dom]
        exact ⟨w', hw'H, by rw [hinv, hw']⟩
    · exact hp.dom₂ ⟨hzH, hzc⟩
  · -- `corr₂`: the Loewner composition
    rw [hinv]
    have hFw := hFm hw
    rw [hp.corr₂ _ hFw.1]
    constructor
    · intro hs
      have hmem : fwdMapInv W τ w ∈ fwdHull W s \ fwdHull W τ := ⟨hs, hFw.2⟩
      rw [hdiff] at hmem
      obtain ⟨v, hvK, hv⟩ := hmem
      have hvH : v ∈ H := (QuantumZipper.fwdHull_mono (W := shiftDrive W τ)).2 _ hvK
      rw [← hFi hvH hw hv]
      exact hvK
    · intro hwK
      have hmem : fwdMapInv W τ w ∈ fwdMapInv W τ '' fwdHull (shiftDrive W τ) (s - τ) := ⟨w, hwK, rfl⟩
      rw [← hdiff] at hmem
      exact hmem.1

/-- **`dom₁` from the S2 record**: if the hull chart `Φ` covers `ℍ ∖ A₁`, the S2 record's identity
`Φ.2.1 y = c.2.1 (reflectC (cr.2.1 (reflectC y)))` puts `ℍ ∖ A₁` inside the chart domain of `c`. -/
theorem dom_compl_subset_of_stageS2 {c Φ : Chart} {A₁ : Set ℂ} {wB : ℝ → ℝ} {sB : ℝ} {W : ℝ → ℝ} {u : ℝ}
    (hS : Om.IsStageS2 c Φ A₁ wB sB W u) (hc : c.IsConformal) (hΦ : H \ A₁ ⊆ Φ.2.1 '' H) :
    H \ (c.dom : Set ℂ) ⊆ A₁ := by
  obtain ⟨q, x₁, R, cr, g, β', γ, S₀, Sm, ηr, η, -, -, -, -, -, -, hcr, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, hΦc, -⟩ := hS
  intro z hz
  by_contra hzA
  obtain ⟨y, hy, rfl⟩ := hΦ ⟨hz.1, hzA⟩
  have hry : LP.reflectC y ∈ H := by
    show 0 < (LP.reflectC y).im
    rw [LP.im_reflectC]; exact hy
  have harg : LP.reflectC (cr.2.1 (LP.reflectC y)) ∈ H := by
    show 0 < (LP.reflectC (cr.2.1 (LP.reflectC y))).im
    rw [LP.im_reflectC]
    exact hcr.1.1.2.1 hry
  apply hz.2
  rw [hc.coe_dom, hΦc y hy]
  exact ⟨_, harg, rfl⟩

end InteractingSLE.Theorem14.SB.Pq
