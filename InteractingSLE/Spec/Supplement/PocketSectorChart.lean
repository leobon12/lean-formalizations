/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.PocketSectorShape

/-!
# Component charts through the sector map

PROVE-POCKETSHAPE continuation. A chart on a between-component gives a chart on
its sector image, with inverse exactly the sector image of the original inverse
on the upper half-plane. This also transports every finite boundary limit.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Function
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)
open SupercriticalConformalCovariance (IsConformalBijection)

namespace InteractingSLE.Theorem14.PocketSector

open GW4Reg GW3SidedProof

/-- A boundary limit of an inverse mapping into `C ⊆ ℍ` is preserved by the sector map. -/
theorem tendsto_sectorMap_comp {C : Set ℂ} (hCH : C ⊆ H) {g : ℂ → ℂ}
    (hg : MapsTo g H C) {x : ℝ} {p : ℂ}
    (hp : Tendsto g (𝓝[H] (x : ℂ)) (𝓝 p)) :
    Tendsto (sectorMap ∘ g) (𝓝[H] (x : ℂ)) (𝓝 (sectorMap p)) := by
  have : (𝓝[H] (x : ℂ)).NeBot := FiniteEndpoint.neBot_nhdsWithin_H (by simp)
  have hpcl : p ∈ closure C := isClosed_closure.mem_of_tendsto hp
    (eventually_nhdsWithin_of_forall fun z hz => subset_closure (hg hz))
  have hCb : closure C ⊆ Hbar := closure_minimal
    (fun z hz => (show 0 < z.im from hCH hz).le) QuantumZipper.isClosed_Hbar
  have hp' : Tendsto g (𝓝[H] (x : ℂ)) (𝓝[Hbar] p) := tendsto_nhdsWithin_iff.2
    ⟨hp, eventually_nhdsWithin_of_forall fun z hz => (show 0 < (g z).im from hCH (hg hz)).le⟩
  exact (continuousOn_sectorMap p (hCb hpcl)).tendsto.comp hp'

/-- The sector map transports a component chart, retaining its inverse on `ℍ`. -/
theorem exists_sector_chart {αR αL : ℝ≥0 → ℂ}
    (hR : GB11.IsCompleteSimpleFlow αR) (hL : GB11.IsCompleteSimpleFlow αL)
    {C : Set ℂ} (hC : C ∈ betweenComponents (range αR) (range αL))
    {c : Chart} (hc : IsComponentChart (range αR) (range αL) C c) :
    ∃ d : Chart,
      IsComponentChart (range (sectorMap ∘ αR)) (range (sectorMap ∘ αL)) (sectorMap '' C) d ∧
      EqOn d.2.1 (sectorMap ∘ c.2.1) H := by
  have hCH : C ⊆ H := fun z hz => (Sec7.Prop74B.subset_of_mem_betweenComponents hC hz).1
  have hIo := isOpen_of_mem_betweenComponents
    (isClosed_range_of_isSimpleProper (isSimpleProper_sector hR))
    (isClosed_range_of_isSimpleProper (isSimpleProper_sector hL)) (image_mem_between hR hL hC)
  have hIH : sectorMap '' C ⊆ H := by
    rintro _ ⟨z, hz, rfl⟩
    exact openSector_subset_H (sectorMap_mem_openSector (hCH hz))
  have hG : IsConformalBijection sectorInv (sectorMap '' C) C := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro w hw
      unfold sectorInv
      fun_prop
    · rintro _ ⟨z, hz, rfl⟩
      rwa [sectorInv_sectorMap]
    · rintro _ ⟨z, hz, rfl⟩ _ ⟨z', hz', rfl⟩ he
      simpa only [sectorInv_sectorMap] using congrArg sectorMap he
    · intro z hz
      exact ⟨sectorMap z, ⟨z, hz, rfl⟩, sectorInv_sectorMap z⟩
  have hf : IsConformalBijection c.1 C H :=
    ⟨hc.1, hc.2.2.2.1.bijOn hc.2.1 hc.2.2.1⟩
  have hfG := isConformalBijection_comp hf hG
  obtain ⟨d, -, hdi, hd⟩ := exists_isDomainChart_of_isConformalBijection hIo hIH hfG
  have heq : EqOn d.2.1 (sectorMap ∘ c.2.1) H := by
    intro w hw
    rw [hdi]
    have hp : sectorMap (c.2.1 w) ∈ sectorMap '' C := ⟨c.2.1 w, hc.2.2.1 hw, rfl⟩
    have hfw : (c.1 ∘ sectorInv) (sectorMap (c.2.1 w)) = w := by
      rw [comp_apply, sectorInv_sectorMap]
      exact hc.2.2.2.1.2 hw
    change invFunOn (c.1 ∘ sectorInv) (sectorMap '' C) w = sectorMap (c.2.1 w)
    calc
      _ = invFunOn (c.1 ∘ sectorInv) (sectorMap '' C)
          ((c.1 ∘ sectorInv) (sectorMap (c.2.1 w))) := congrArg _ hfw.symm
      _ = _ := hfG.2.injOn.leftInvOn_invFunOn hp
  refine ⟨d, GW3.isComponentChart_of_isDomainChart hd ?_, heq⟩
  intro x
  obtain ⟨p, hp, hpR, hpL⟩ := hc.2.2.2.2.1 x
  refine ⟨sectorMap p, (tendsto_sectorMap_comp hCH hc.2.2.1 hp).congr'
    (eventually_nhdsWithin_of_forall fun z hz => (heq hz).symm), ?_, ?_⟩
  · intro hx
    obtain ⟨r, hr⟩ := hpR hx
    exact ⟨r, congrArg sectorMap hr⟩
  · intro hx
    obtain ⟨t, ht⟩ := hpL hx
    exact ⟨t, congrArg sectorMap ht⟩

/-- Every oriented uniformizer on a between-component transports into the sector. -/
theorem hasOrientedUniformizer_sector_image {αR αL : ℝ≥0 → ℂ}
    (hR : GB11.IsCompleteSimpleFlow αR) (hL : GB11.IsCompleteSimpleFlow αL)
    {C : Set ℂ} (hC : C ∈ betweenComponents (range αR) (range αL))
    (hU : GW3.HasOrientedUniformizer (range αR) (range αL) C) :
    GW3.HasOrientedUniformizer (range (sectorMap ∘ αR)) (range (sectorMap ∘ αL)) (sectorMap '' C) := by
  obtain ⟨c, hc⟩ := GW3.exists_isComponentChart_of_hasOrientedUniformizer hU
  obtain ⟨d, hd, -⟩ := exists_sector_chart hR hL hC hc
  have hCo := isOpen_of_mem_betweenComponents
    (isClosed_range_of_isSimpleProper (isSimpleProper_sector hR))
    (isClosed_range_of_isSimpleProper (isSimpleProper_sector hL)) (image_mem_between hR hL hC)
  exact GW3.hasOrientedUniformizer_of_isComponentChart hd hCo
    (fun z hz => (Sec7.Prop74B.subset_of_mem_betweenComponents (image_mem_between hR hL hC) hz).1)

end InteractingSLE.Theorem14.PocketSector
