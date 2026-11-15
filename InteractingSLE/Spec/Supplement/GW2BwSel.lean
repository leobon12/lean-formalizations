/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BwAe
import InteractingSLE.Spec.Supplement.GW2NiSel

/-!
# The source-buffer bound `SrcBoundStatement` (BUF's `hsrc`)

Packet PROVE-GW2-BUF (round 20; decision D61). The selection of the final package's near candidates: at the
conditioning sample `ω₀`, the angle index is the rightward selection's (`angSel`), and the cap and buffer pair is
NEARIMG2's selection (`GW2Ni.exists_kSel`) for the bad sets `Zs = aliveVer ∩ Zb` (`aliveVer` a retained version of
the alive event). The bad sets are avoided almost surely (`ae_avoid_Zb`), so the selected pair has conditional
measure at most `1/(m+1)`; the source-buffer loss `srcBad` lies in `Zb` (`srcBad_subset_Zb`) and `aliveVer`'s
complement is conditionally null at alive `ω₀`.

* `aliveVer`, `Zs`, `SelOK`, `kSelI`, **`selOK_kSelI`**;
* `kZero`, `angSel`, **`kSelB`** (a `NearSelB`), `nearCandidate_kSelB`;
* **`srcBoundStatement_kSelB`**: `SrcBoundStatement h13 h12 K₀ (kSelB h13 h12 K₀)` from `InstInputsX` (for the
  measurability of the bad sets) and NEARIMG2's uncapped stage law `GW2Ni.StageLawUXStatement` (as stated).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Bh

open Restart Exist Exist.StagedLaw GW2TipSystem GW2TipSystem.RootC24 GW2Rz GW2Rd GW2Rv GW2Sde GW2Sdh GW2Sdx

variable (h13 : Exist.Theorem13Statement.{u}) (h12 : Exist.Theorem12Statement.{u}) (K₀ : PkgFamily.{u})

section Sets

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
  (l : List (EntryIdx c.Θ c.Q))

/-- A version of the alive event of `J32S GW2Sdq.gapFam` in the retained σ-algebra. -/
def aliveVer : Set Ω :=
  (exists_alive_version h13 GW2Sdq.gapFam c (GW2Sdq.measurable_gapFam Ω c) r l).choose

theorem measurableSet_aliveVer : MeasurableSet[c.sigma r l] (aliveVer h13 c r l) :=
  (exists_alive_version h13 GW2Sdq.gapFam c (GW2Sdq.measurable_gapFam Ω c) r l).choose_spec.1

theorem ae_mem_aliveVer_iff : ∀ᵐ ω ∂c.P, (ω ∈ aliveVer h13 c r l ↔
    ω ∈ ((GW2Sdz.J32S GW2Sdq.gapFam Ω c).experiment r).data.alive ((GW2Sdz.J32S GW2Sdq.gapFam Ω c).G r) l) :=
  (exists_alive_version h13 GW2Sdq.gapFam c (GW2Sdq.measurable_gapFam Ω c) r l).choose_spec.2

/-- The selection's bad sets: `Zb` inside the retained alive version. -/
def Zs (n i q b : ℕ) : Set Ω := aliveVer h13 c r l ∩ Zb h13 h12 c r l n i q b

/-- A selection (a pair `Nat.pair q b` per conditioning sample, level, angle index and `m`) whose bad set has
conditional measure at most `1/(m+1)`. -/
def SelOK (ks : Ω → ℕ → ℕ → ℕ → ℕ) : Prop :=
  ∀ᵐ ω₀ ∂c.P, ∀ n i m : ℕ, condExpKernel c.P (c.sigma r l) ω₀
    (Zs h13 h12 c r l n i (Nat.unpair (ks ω₀ n i m)).1 (Nat.unpair (ks ω₀ n i m)).2) ≤ ((m : ℝ≥0∞) + 1)⁻¹

open Classical in
/-- **The cap and buffer selection**: a good selection when one exists. -/
def kSelI : Ω → ℕ → ℕ → ℕ → ℕ :=
  if h : ∃ ks, SelOK h13 h12 c r l ks then h.choose else fun _ _ _ _ => 0

/-- **The cap and buffer selection is good** (good root, time-ordered history). -/
theorem selOK_kSelI (hI : InstInputsX h13 (pkgVerF h13 h12) (pkgCh h13 h12 cwSrc))
    (hlawU : GW2Ni.StageLawUXStatement.{u}) (hg : GoodRoot c r) (hTO : GW2Sdx.HistOrdered c r
        l) : SelOK h13 h12 c r l (kSelI h13 h12 c r l) := by
  classical
  have hex : ∃ ks, SelOK h13 h12 c r l ks := by
    have hZ : ∀ n i q b, MeasurableSet (Zs h13 h12 c r l n i q b) := fun n i q b =>
      (sigma_le_ambient c r l _ (measurableSet_aliveVer h13 c r l)).inter
        (measurableSet_Zb h13 h12 c r l hI hTO n i q b)
    have hgood : ∀ᵐ ξ ∂c.P, ∀ n i : ℕ, ∃ Q : ℝ≥0, ∀ q, Q ≤ (RootJ31.timeEnumeration c r q : ℝ≥0) →
        ∀ᶠ b in atTop, ξ ∉ Zs h13 h12 c r l n i q b := by
      filter_upwards [ae_avoid_Zb h13 h12 hlawU c r l hg hTO, ae_mem_aliveVer_iff h13 c r l] with ξ hav hiff n i
      by_cases hA : ξ ∈ aliveVer h13 c r l
      · obtain ⟨Q, hQ⟩ := hav (hiff.1 hA) n i
        exact ⟨Q, fun q hq => (hQ q hq).mono fun b hb hm => hb hm.2⟩
      · exact ⟨0, fun q _ => Eventually.of_forall fun b hm => hA hm.1⟩
    exact GW2Ni.exists_kSel (sigma_le_ambient c r l) hZ (GW2Ni.exists_capIdx_ge c r) hgood
  unfold kSelI
  rw [dite_eq_left hex]
  exact hex.choose_spec

end Sets

/-- The zero selection. -/
def kZero : NearSelB.{u} := fun _ _ _ _ _ _ _ _ _ _ => 0

/-- **The angle index of the final package's near candidate** (the rightward selection's; it does not read the
cap and buffer selection). -/
def angSel (k : ℕ) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (ω : Ω) (m : ℕ) : ℕ :=
  (Nat.unpair ((pkgF h13 h12 K₀ kZero k Ω c r).nearCandidate l ω 0 m)).1

/-- **BUF's near selection**: NEARIMG2's cap and buffer selection at the selected angle index. -/
def kSelB : NearSelB.{u} := fun k Ω _ _ c r l ω n m =>
  kSelI h13 h12 c r l ω n (angSel h13 h12 K₀ k Ω c r l ω m) m

/-- The final package's near candidate with BUF's selection. -/
theorem nearCandidate_kSelB (k : ℕ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (ω : Ω) (n m : ℕ) :
    (pkgF h13 h12 K₀ (kSelB h13 h12 K₀) k Ω c r).nearCandidate l ω n m =
      Nat.pair (angSel h13 h12 K₀ k Ω c r l ω m) (kSelI h13 h12 c r l ω n (angSel h13 h12 K₀ k Ω c r l ω m) m) := by
  simp only [angSel, kSelB, pkgF, pkgB, withNearSB, Nat.unpair_pair]

/-- **BUF's `hsrc`**: `SrcBoundStatement` for BUF's selection. -/
theorem srcBoundStatement_kSelB (hI : InstInputsX h13 (pkgVerF h13 h12) (pkgCh h13 h12 cwSrc))
    (hlawU : GW2Ni.StageLawUXStatement.{u}) :
    SrcBoundStatement h13 h12 K₀ (kSelB h13 h12 K₀) := by
  intro k Ω _ _ c r l
  by_cases hg : GoodRoot c r
  swap
  · filter_upwards [GW2Sds.ae_goodRoot_of_alive h13 c r l] with ω hω halive
    exact absurd (hω (GW2Sdz.alive_scaled_subset GW2Sdq.gapFam Ω c r l halive)) hg
  by_cases hTO : HistOrdered c r l
  swap
  · exact Eventually.of_forall fun ω halive => absurd
      (RootJ32.timeOrdered_historyProgram_of_alive c r l ω (GW2Sdz.alive_scaled_subset GW2Sdq.gapFam Ω c r l halive))
      hTO
  filter_upwards [selOK_kSelI h13 h12 c r l hI hlawU hg hTO, ae_mem_aliveVer_iff h13 c r l,
    Sec7.Aux122Disint.ae_ae_condExpKernel_mem (sigma_le_ambient c r l) (measurableSet_aliveVer h13 c r l)]
    with ω₀ hsel hiff hker halive n ε hε
  have hA0 : condExpKernel c.P (c.sigma r l) ω₀ (aliveVer h13 c r l)ᶜ = 0 := ae_iff.1 (hker (hiff.2 halive))
  have hev : ∀ᶠ m : ℕ in atTop, ((m : ℝ≥0∞) + 1)⁻¹ ≤ ε := by
    filter_upwards [ENNReal.tendsto_inv_nat_nhds_zero.eventually (gt_mem_nhds hε)] with m hm
    exact le_of_lt (lt_of_le_of_lt (ENNReal.inv_le_inv.2 le_self_add) hm)
  filter_upwards [hev] with m hm
  set i₀ := angSel h13 h12 K₀ k Ω c r l ω₀ m with hi₀
  set kk := kSelI h13 h12 c r l ω₀ n i₀ m with hkk
  have hcand : (pkgF h13 h12 K₀ (kSelB h13 h12 K₀) k Ω c r).nearCandidate l ω₀ n m =
      Nat.pair i₀ (Nat.pair (Nat.unpair kk).1 (Nat.unpair kk).2) := by
    rw [Nat.pair_unpair]
    exact nearCandidate_kSelB h13 h12 K₀ k c r l ω₀ n m
  rw [hcand]
  calc condExpKernel c.P (c.sigma r l) ω₀
        (srcBad h13 h12 K₀ c r l n m (Nat.pair i₀ (Nat.pair (Nat.unpair kk).1 (Nat.unpair kk).2)))
      ≤ condExpKernel c.P (c.sigma r l) ω₀ (Zb h13 h12 c r l n i₀ (Nat.unpair kk).1 (Nat.unpair kk).2) :=
        measure_mono (srcBad_subset_Zb h13 h12 K₀ c r l n m _ _ _)
    _ ≤ condExpKernel c.P (c.sigma r l) ω₀ (Zs h13 h12 c r l n i₀ (Nat.unpair kk).1 (Nat.unpair kk).2) +
          condExpKernel c.P (c.sigma r l) ω₀ (aliveVer h13 c r l)ᶜ := by
        refine le_trans (measure_mono fun ξ hξ => ?_) (measure_union_le _ _)
        by_cases h : ξ ∈ aliveVer h13 c r l
        · exact Or.inl ⟨h, hξ⟩
        · exact Or.inr h
    _ ≤ ((m : ℝ≥0∞) + 1)⁻¹ + 0 := add_le_add (hsel n i₀ m) hA0.le
    _ ≤ ε := by rw [add_zero]; exact hm

end InteractingSLE.Theorem14.GW2Bh
