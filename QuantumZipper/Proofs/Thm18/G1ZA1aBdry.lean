import QuantumZipper.Proofs.Thm18.G1ZA1aComp
import QuantumZipper.Proofs.Thm18.G1PsiExtCara

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1Z-A1a (ii): the boundary node `G1zRerootBdryStmt`, reduced

* `tendsto_sideMap_zero` (PROVED): `ψ(w) → 0` as `w → 0` in `ℍ`, for `ψ = φ⁻¹`, `φ` the
  normalized uniformizer of a side component (Carathéodory extension `G1RC.hasHbarExt_left/right`,
  Pommerenke, *Boundary Behaviour of Conformal Maps*, Thm 2.6; the value at `0` is `0` because
  `φ(z) → 0` as `z → 0` in the component).
* `g1zRerootBdryStmt_of`: `G1zRerootBdryStmt` from
  - `G1zBaseLimitStmt`: `f_t(z) → O^∓_t` as `z → 0` inside the side component (boundary behaviour
    of the forward Loewner map at the base of the curve, on the given side);
  - `G1zBetaSideStmt`: the point `β` of an affine factorization lies in the side half-line.
* `g1RerootAffineStmt_of_base_beta`: A1a from these two nodes.
-/

noncomputable section

open Filter Set Complex Function Metric
open scoped Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G1ZA1a

open QuantumZipper.CA QuantumZipper.CA.Uniformizer

theorem nhdsWithin_zero_sideDom_neBot {η : ℝ → ℂ} (hη : IsSimpleChord η) (left : Bool) :
    (𝓝[sideDom η left] (0 : ℂ)).NeBot := by
  cases left
  · have hη' := isSimpleChord_refl_comp hη
    have hsub : refl '' leftComponent (refl ∘ η) ⊆ rightComponent η := by
      rintro _ ⟨w, hw, rfl⟩; exact refl_mem_right_of_mem_left hw
    refine mem_closure_iff_nhdsWithin_neBot.1 (closure_mono hsub ?_)
    have := mem_closure_image continuous_refl.continuousAt (zero_mem_closure_leftComponent hη')
    simpa [CA.Uniformizer.refl] using this
  · exact mem_closure_iff_nhdsWithin_neBot.1 (zero_mem_closure_leftComponent hη)

/-- **`ψ → 0` at `0`.** -/
theorem tendsto_sideMap_zero {W : ℝ → ℝ} (hη : IsSimpleChord (trace W)) (left : Bool) :
    Tendsto (g1zSideMap left W) (𝓝[H] 0) (𝓝[sideDom (trace W) left] 0) := by
  have hφ := isNormalizedUniformizer_sideDom hη left
  obtain ⟨G, hGc, -, hGeq⟩ : G1RC.HasHbarExt (g1zSideMap left W) := by
    unfold g1zSideMap
    cases left
    · exact G1RC.hasHbarExt_right hη hφ
    · exact G1RC.hasHbarExt_left hη hφ
  obtain ⟨hb, -, h0, -⟩ := hφ
  have hne := nhdsWithin_zero_sideDom_neBot hη left
  have hmemH : ∀ᶠ z in 𝓝[sideDom (trace W) left] (0 : ℂ), z ∈ sideDom (trace W) left :=
    self_mem_nhdsWithin
  have hφH : Tendsto (uniformizer (sideDom (trace W) left)) (𝓝[sideDom (trace W) left] 0)
      (𝓝[Hbar] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨h0, hmemH.mono fun z hz =>
      le_of_lt (show (0 : ℝ) < _ from hb.mapsTo hz)⟩
  have hG0 : Tendsto (fun z => G (uniformizer (sideDom (trace W) left) z))
      (𝓝[sideDom (trace W) left] 0) (𝓝 (G 0)) :=
    (hGc 0 (by simp [Hbar])).tendsto.comp hφH
  have hid : Tendsto (fun z => G (uniformizer (sideDom (trace W) left) z))
      (𝓝[sideDom (trace W) left] 0) (𝓝 0) := by
    refine (tendsto_nhdsWithin_iff.1 (tendsto_id (x := 𝓝[sideDom (trace W) left] (0 : ℂ)))).1
      |>.congr' ?_
    filter_upwards [hmemH] with z hz
    rw [← hGeq (hb.mapsTo hz)]
    exact (hb.invOn_invFunOn.1 hz).symm
  have hG00 : G 0 = 0 := tendsto_nhds_unique hG0 hid
  have hψb : MapsTo (g1zSideMap left W) H (sideDom (trace W) left) :=
    (BijOn.symm hb.invOn_invFunOn.symm hb).mapsTo
  refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun w hw => hψb hw⟩
  have hsub : H ⊆ Hbar := fun (w : ℂ) (hw : w ∈ H) => le_of_lt (show (0 : ℝ) < w.im from hw)
  have h1 : Tendsto G (𝓝[H] 0) (𝓝 (G 0)) :=
    ((hGc 0 (by simp [Hbar])).tendsto).mono_left (nhdsWithin_mono _ hsub)
  rw [hG00] at h1
  exact h1.congr' (eventually_nhdsWithin_of_forall fun w hw => (hGeq hw).symm)

/-- **Base limit of the forward map** (open): `f_t(z) → O^∓_t` as `z → 0` inside the side
component. -/
def G1zBaseLimitStmt : Prop :=
  ∀ W : ℝ → ℝ, G1zDrvGood W → ∀ t : ℝ, 0 < t → ∀ left : Bool,
    Tendsto (fwdMap W t) (𝓝[sideDom (trace W) left] 0) (𝓝 (g1zSideImage left W t : ℂ))

/-- **Side of `β`** (open): the point `β` of an affine factorization lies in the side
half-line. -/
def G1zBetaSideStmt : Prop :=
  ∀ W : ℝ → ℝ, G1zDrvGood W → ∀ t a : ℝ, 0 < t → 0 < a → ∀ left : Bool, ∀ lam β : ℝ, 0 < lam →
    EqOn (fun u => fwdMapInv W t ((a : ℂ) * g1zSideMap left (g1zNewDrv W t a) (u + β)))
      (fun u => g1zSideMap left W (u / lam)) H →
    β ∈ g1SideHalf left

theorem g1zRerootBdryStmt_of (hL : G1zBaseLimitStmt) (hS : G1zBetaSideStmt) :
    G1zRerootBdryStmt := by
  intro W hG t a ht ha left lam β hlam hEq
  refine ⟨hS W hG t a ht ha left lam β hlam hEq, ?_⟩
  have hW := hG.1
  have hW0 := hG.2.1
  have hη' := (g1zDrvGood_newDrv hG ht ha).2.2.2.1
  have hψ'b : MapsTo (g1zSideMap left (g1zNewDrv W t a)) H
      (sideDom (trace (g1zNewDrv W t a)) left) := by
    obtain ⟨hb, -⟩ := isNormalizedUniformizer_sideDom hη' left
    exact (BijOn.symm hb.invOn_invFunOn.symm hb).mapsTo
  -- `a ψ'(v) = f_t(ψ((v − β)/λ))`
  have hkey : ∀ v ∈ H, (a : ℂ) * g1zSideMap left (g1zNewDrv W t a) v =
      fwdMap W t (g1zSideMap left W ((v - β) / lam)) := by
    intro v hv
    have hvβ : v - (β : ℂ) ∈ H := by
      show 0 < (v - (β : ℂ)).im
      simpa using (show (0 : ℝ) < v.im from hv)
    have h := hEq hvβ
    simp only [sub_add_cancel] at h
    rw [← h, RS.fwdMap_fwdMapInv hW hW0 ht.le
      (ofReal_mul_mem_H ha (sideDom_subset_H _ left (hψ'b hv)))]
  have hlam' : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam.ne'
  have hin : Tendsto (fun v : ℂ => (v - β) / lam) (𝓝[H] (β : ℂ)) (𝓝[H] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun v hv => ?_⟩
    · have hc : Continuous fun v : ℂ => (v - β) / lam := by fun_prop
      have := hc.tendsto (β : ℂ)
      simp only [sub_self, zero_div] at this
      exact this.mono_left nhdsWithin_le_nhds
    · show 0 < ((v - β) / (lam : ℂ)).im
      rw [Complex.div_ofReal_im]
      exact div_pos (by simpa using (show (0 : ℝ) < v.im from hv)) hlam
  have h := (hL W hG t ht left).comp ((tendsto_sideMap_zero hG.2.2.2.1 left).comp hin)
  refine h.congr' (eventually_nhdsWithin_of_forall fun v hv => ?_)
  exact (hkey v hv).symm

/-- **A1a from the two boundary nodes** (part (i), the affine factorization, the component
transport and the limit of `ψ` at `0` are proved). -/
theorem g1RerootAffineStmt_of_base_beta (hL : G1zBaseLimitStmt) (hS : G1zBetaSideStmt) :
    G1RerootAffineStmt :=
  g1RerootAffineStmt_of_bdry (g1zRerootBdryStmt_of hL hS)

end G1ZA1a
end Thm18Asm
end QuantumZipper
