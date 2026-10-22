import HigherDimLQGContinuity.Core.Interfaces
import HigherDimLQGContinuity.Grid.Version
import HigherDimLQGContinuity.Windows.Exhaustion

/-!
# Gluing the positive-parameter versions

The versions on the rational exhaustion windows agree on one measurable full-measure
event, and hence define a jointly measurable continuous family.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open HigherDimLQGMetric
open HigherDimLFPP (Rd)

namespace HigherDimLQGContinuity

/-- Equality on all interpolation nodes extends across the closed window. -/
private theorem e1b_eq_on_window_of_nodes {d : ℕ} {lo hi : ℝ} (hlohi : lo < hi)
    {F G : ℝ → C(Rd d × Rd d, ℝ)}
    (hF : ContinuousOn F (Icc lo hi)) (hG : ContinuousOn G (Icc lo hi))
    (hnodes : ∀ k i : ℕ, i ≤ 2 ^ posLevel k →
      F (posNode lo hi k i) = G (posNode lo hi k i)) :
    EqOn F G (Icc lo hi) := by
  intro ξ hξ
  choose m hm hnear using fun k : ℕ => exists_posNode_near hlohi hξ k
  let t : ℕ → ℝ := fun k => posNode lo hi k (m k)
  have ht (k : ℕ) : t k ∈ Icc lo hi := posNode_mem hlohi (hm k)
  have htend : Tendsto t atTop (𝓝 ξ) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_)
      (tendsto_posWidth (lo := lo) (hi := hi))
    rw [Real.norm_eq_abs]
    exact hnear k
  have htwithin : Tendsto t atTop (𝓝[Icc lo hi] ξ) :=
    tendsto_nhdsWithin_iff.mpr ⟨htend, Eventually.of_forall ht⟩
  have hft := (hF ξ hξ).tendsto.comp htwithin
  have hgt := (hG ξ hξ).tendsto.comp htwithin
  have heq : (fun k => F (t k)) = (fun k => G (t k)) :=
    funext fun k => hnodes k (m k) (hm k)
  change Tendsto (fun k => F (t k)) atTop (𝓝 (F ξ)) at hft
  rw [heq] at hft
  exact tendsto_nhds_unique hft hgt

/-- Gluing lemma for any nested countable exhaustion by positive subcritical windows. -/
private theorem e1b_glue_of_windows {d : ℕ} (hd : 3 ≤ d) (hP : Prop37Shape d)
    (lo hi : ℕ → ℝ)
    (hdata : ∀ n, 0 < lo n ∧ lo n < hi n ∧ hi n ∈ subcritSet d)
    (hstep : ∀ n, Icc (lo n) (hi n) ⊆ Icc (lo (n + 1)) (hi (n + 1)))
    (hcover : subcritSet d = ⋃ n, Ioo (lo n) (hi n)) :
    ∃ (X : ℝ → DistRd d → C(Rd d × Rd d, ℝ)) (Good : Set (DistRd d)),
      PosVersionStmt d X ∧ MeasurableSet Good ∧ normLGFLaw d Goodᶜ = 0 ∧
      (∀ g ∈ Good, ContinuousOn (fun ξ => X ξ g) (subcritSet d) ∧
        ∀ ξ ∈ subcritSet d, 0 ≤ X ξ g) ∧
      (∀ ξ g, ξ ∉ subcritSet d ∨ g ∉ Good → X ξ g = euclidDistC d) := by
  classical
  let μ := normLGFLaw d
  have hhi (n : ℕ) : 0 < hi n ∧ Real.sqrt (2 * d) < distExp d (hi n) :=
    (hdata n).2.2
  choose V good hgoodMeas hgoodNull hVmeas hVgood hVversion using
    fun n : ℕ => windowVersion_spec hd hP (hdata n).1 (hdata n).2.1 (hhi n)
  have hsub (n : ℕ) : Icc (lo n) (hi n) ⊆ subcritSet d := by
    intro ξ hξ
    have hmargin := gap24 (by omega : 2 ≤ d) (hhi n)
    exact hmargin.choose_spec.2.2.2.1 ⟨(hdata n).1.trans_le hξ.1, hξ.2⟩
  have hinc (n m : ℕ) (hnm : n ≤ m) :
      Icc (lo n) (hi n) ⊆ Icc (lo m) (hi m) := by
    induction m, hnm using Nat.le_induction with
    | base => exact Subset.rfl
    | succ m _ ih => exact ih.trans (hstep m)
  have hAEgoodWin : ∀ᵐ g ∂μ, ∀ n : ℕ, g ∈ good n := by
    apply ae_all_iff.mpr
    intro n
    exact mem_ae_iff.mpr (hgoodNull n)
  have hAEagree : ∀ᵐ g ∂μ, ∀ n k i : ℕ,
      i ≤ 2 ^ posLevel k →
      V n (posNode (lo n) (hi n) k i) g =
        V (n + 1) (posNode (lo n) (hi n) k i) g := by
    apply ae_all_iff.mpr
    intro n
    apply ae_all_iff.mpr
    intro k
    apply ae_all_iff.mpr
    intro i
    by_cases hvalid : i ≤ 2 ^ posLevel k
    · let ξ := posNode (lo n) (hi n) k i
      have hξ : ξ ∈ Icc (lo n) (hi n) := posNode_mem (hdata n).2.1 hvalid
      have hξ' : ξ ∈ Icc (lo (n + 1)) (hi (n + 1)) := hstep n hξ
      have hD := strongAt_spec hd (hsub n hξ)
      filter_upwards [hVversion n ξ hξ (strongAt d ξ) hD,
        hVversion (n + 1) ξ hξ' (strongAt d ξ) hD] with g h₁ h₂
      intro _
      exact h₁.trans h₂.symm
    · exact Filter.Eventually.of_forall (fun _ hv => (hvalid hv).elim)
  have hAEraw : ∀ᵐ g ∂μ,
      (∀ n, g ∈ good n) ∧
      (∀ n k i, i ≤ 2 ^ posLevel k →
        V n (posNode (lo n) (hi n) k i) g =
          V (n + 1) (posNode (lo n) (hi n) k i) g) := by
    filter_upwards [hAEgoodWin, hAEagree] with g hg ha
    exact ⟨hg, ha⟩
  obtain ⟨bad, hbadSub, hbadMeas, hbadNull⟩ :=
    exists_measurable_superset_of_null (ae_iff.mp hAEraw)
  let Good : Set (DistRd d) := badᶜ
  have hGoodMeas : MeasurableSet Good := hbadMeas.compl
  have hGoodNull : μ Goodᶜ = 0 := by simpa only [Good, compl_compl] using hbadNull
  have hGoodAE : ∀ᵐ g ∂μ, g ∈ Good := mem_ae_iff.mpr hGoodNull
  have hGoodProps {g : DistRd d} (hg : g ∈ Good) :
      (∀ n, g ∈ good n) ∧
      (∀ n k i, i ≤ 2 ^ posLevel k →
        V n (posNode (lo n) (hi n) k i) g =
          V (n + 1) (posNode (lo n) (hi n) k i) g) := by
    by_contra hn
    exact hg (hbadSub hn)
  have hEqStep {g : DistRd d} (hg : g ∈ Good) (n : ℕ) :
      EqOn (fun ξ => V n ξ g) (fun ξ => V (n + 1) ξ g) (Icc (lo n) (hi n)) := by
    apply e1b_eq_on_window_of_nodes (hdata n).2.1
      (hVgood n g ((hGoodProps hg).1 n)).1
      ((hVgood (n + 1) g ((hGoodProps hg).1 (n + 1))).1.mono (hstep n))
    intro k i hvalid
    exact (hGoodProps hg).2 n k i hvalid
  have hEqWindows {g : DistRd d} (hg : g ∈ Good) (n m : ℕ) (hnm : n ≤ m) :
      EqOn (fun ξ => V n ξ g) (fun ξ => V m ξ g) (Icc (lo n) (hi n)) := by
    induction m, hnm using Nat.le_induction with
    | base => intro _ _; rfl
    | succ m _ ih =>
      intro ξ hξ
      exact (ih hξ).trans (hEqStep hg m (hinc n m (by omega) hξ))
  have hSmeas : MeasurableSet (subcritSet d) := by
    rw [subcritSet_eq_Ioo (by omega : 2 ≤ d)]
    exact isOpen_Ioo.measurableSet
  let p (n : ℕ) (z : ℝ × DistRd d) : Prop :=
    z.1 ∉ subcritSet d ∨ z.1 ∈ Ioo (lo n) (hi n)
  have hp (z : ℝ × DistRd d) : ∃ n, p n z := by
    by_cases hz : z.1 ∈ subcritSet d
    · rw [hcover] at hz
      obtain ⟨n, hn⟩ := mem_iUnion.mp hz
      exact ⟨n, Or.inr hn⟩
    · exact ⟨0, Or.inl hz⟩
  have hpMeas (n : ℕ) : MeasurableSet {z : ℝ × DistRd d | p n z} := by
    have h₁ : MeasurableSet {z : ℝ × DistRd d | z.1 ∉ subcritSet d} :=
      hSmeas.compl.preimage measurable_fst
    have h₂ : MeasurableSet {z : ℝ × DistRd d | z.1 ∈ Ioo (lo n) (hi n)} :=
      isOpen_Ioo.measurableSet.preimage measurable_fst
    simpa only [p, ofPred_or] using h₁.union h₂
  have hSelectMeas : Measurable (fun z : ℝ × DistRd d =>
      V (Nat.find (hp z)) z.1 z.2) :=
    Measurable.find (fun n => hVmeas n) hpMeas hp
  let X (ξ : ℝ) (g : DistRd d) : C(Rd d × Rd d, ℝ) :=
    if ξ ∈ subcritSet d ∧ g ∈ Good then V (Nat.find (hp (ξ, g))) ξ g
    else euclidDistC d
  have hXMeas : Measurable (Function.uncurry X) := by
    have hset : MeasurableSet
        {z : ℝ × DistRd d | z.1 ∈ subcritSet d ∧ z.2 ∈ Good} :=
      (hSmeas.preimage measurable_fst).inter
        (hGoodMeas.preimage measurable_snd)
    convert (hSelectMeas.ite hset measurable_const) using 1
    funext z
    rcases z with ⟨ξ, g⟩
    rfl
  have hIdxMem {ξ : ℝ} (hξ : ξ ∈ subcritSet d) (g : DistRd d) :
      ξ ∈ Ioo (lo (Nat.find (hp (ξ, g)))) (hi (Nat.find (hp (ξ, g)))) := by
    have h := Nat.find_spec (hp (ξ, g))
    rcases h with hnot | hmem
    · exact (hnot hξ).elim
    · exact hmem
  have hXeq {g : DistRd d} (hg : g ∈ Good) {ξ : ℝ}
      (hξ : ξ ∈ subcritSet d) (n : ℕ) (hn : ξ ∈ Ioo (lo n) (hi n)) :
      X ξ g = V n ξ g := by
    have hidx := hIdxMem hξ g
    have hiClosed : ξ ∈ Icc (lo (Nat.find (hp (ξ, g))))
        (hi (Nat.find (hp (ξ, g)))) := ⟨le_of_lt hidx.1, le_of_lt hidx.2⟩
    have hnClosed : ξ ∈ Icc (lo n) (hi n) := ⟨le_of_lt hn.1, le_of_lt hn.2⟩
    have hEq : V (Nat.find (hp (ξ, g))) ξ g = V n ξ g := by
      rcases le_total (Nat.find (hp (ξ, g))) n with hle | hle
      · exact hEqWindows hg _ _ hle hiClosed
      · exact (hEqWindows hg _ _ hle hnClosed).symm
    simpa only [X, hξ, hg, and_self, ite_true] using hEq
  have hXcont {g : DistRd d} (hg : g ∈ Good) :
      ContinuousOn (fun ξ => X ξ g) (subcritSet d) := by
    intro ξ hξ
    have hξunion : ξ ∈ ⋃ n, Ioo (lo n) (hi n) := hcover ▸ hξ
    obtain ⟨n, hn⟩ := mem_iUnion.mp hξunion
    have hVopen : ContinuousOn (fun t => V n t g) (Ioo (lo n) (hi n)) :=
      (hVgood n g ((hGoodProps hg).1 n)).1.mono Ioo_subset_Icc_self
    have hVat : ContinuousAt (fun t => V n t g) ξ :=
      hVopen.continuousAt (isOpen_Ioo.mem_nhds hn)
    have hlocal : (fun t => X t g) =ᶠ[𝓝 ξ] (fun t => V n t g) := by
      filter_upwards [isOpen_Ioo.mem_nhds hn] with t ht
      exact hXeq hg (hsub n ⟨le_of_lt ht.1, le_of_lt ht.2⟩) n ht
    exact (hVat.congr_of_eventuallyEq hlocal).continuousWithinAt
  have hXnonneg {g : DistRd d} (hg : g ∈ Good) {ξ : ℝ}
      (hξ : ξ ∈ subcritSet d) : 0 ≤ X ξ g := by
    have hidx := hIdxMem hξ g
    have hgn := (hGoodProps hg).1 (Nat.find (hp (ξ, g)))
    rw [hXeq hg hξ (Nat.find (hp (ξ, g))) hidx]
    exact (hVgood _ g hgn).2 ξ
  have hXVersion : ∀ ξ : ℝ, 0 < ξ → Real.sqrt (2 * d) < distExp d ξ →
      ∀ D : DistRd d → ContMetric d,
        IsStrongExpMetric d ξ (distExp d ξ) D →
        ∀ᵐ g ∂μ, X ξ g = (rho D g).1 := by
    intro ξ hξpos hξgap D hD
    have hξ : ξ ∈ subcritSet d := ⟨hξpos, hξgap⟩
    have hξunion : ξ ∈ ⋃ n, Ioo (lo n) (hi n) := hcover ▸ hξ
    obtain ⟨n, hn⟩ := mem_iUnion.mp hξunion
    have hclosed : ξ ∈ Icc (lo n) (hi n) := ⟨le_of_lt hn.1, le_of_lt hn.2⟩
    filter_upwards [hGoodAE, hVversion n ξ hclosed D hD] with g hg hv
    exact (hXeq hg hξ n hn).trans hv
  have hXcontAE : ∀ᵐ g ∂μ, ContinuousOn (fun ξ => X ξ g) (subcritSet d) :=
    hGoodAE.mono fun _ hg => hXcont hg
  refine ⟨X, Good, ⟨hXMeas, hXVersion, hXcontAE⟩, hGoodMeas,
    hGoodNull, ?_, ?_⟩
  · intro g hg
    exact ⟨hXcont hg, fun ξ hξ => hXnonneg hg hξ⟩
  · intro ξ g h
    rcases h with hξ | hg
    · simp [X, hξ]
    · simp [X, hg]

/-- The glued positive version has one measurable full-measure good event,
with continuity, nonnegativity and a deterministic Euclidean fallback. -/
theorem posVersion_with_good (d : ℕ) (hd : 3 ≤ d) (hP : Prop37Shape d) :
    ∃ (X : ℝ → DistRd d → C(Rd d × Rd d, ℝ)) (Good : Set (DistRd d)),
      PosVersionStmt d X ∧ MeasurableSet Good ∧ normLGFLaw d Goodᶜ = 0 ∧
      (∀ g ∈ Good, ContinuousOn (fun ξ => X ξ g) (subcritSet d) ∧
        ∀ ξ ∈ subcritSet d, 0 ≤ X ξ g) ∧
      (∀ ξ g, ξ ∉ subcritSet d ∨ g ∉ Good → X ξ g = euclidDistC d) := by
  obtain ⟨qlo, qhi, hdata, _, _, _, _, _, hstep, hcover⟩ :=
    exists_window_exhaustion (by omega : 2 ≤ d)
  let lo : ℕ → ℝ := fun n => (qlo n : ℝ)
  let hi : ℕ → ℝ := fun n => (qhi n : ℝ)
  have hdata' (n : ℕ) : 0 < lo n ∧ lo n < hi n ∧ hi n ∈ subcritSet d :=
    hdata n
  have hstep' (n : ℕ) :
      Icc (lo n) (hi n) ⊆ Icc (lo (n + 1)) (hi (n + 1)) :=
    hstep n
  have hcover' : subcritSet d = ⋃ n, Ioo (lo n) (hi n) := hcover
  exact e1b_glue_of_windows hd hP lo hi hdata' hstep' hcover'

/-- One jointly measurable family of positive-parameter metric versions is
almost surely continuous throughout the subcritical parameter interval. -/
theorem posVersion_of (d : ℕ) (hd : 3 ≤ d) (hP : Prop37Shape d) :
    ∃ X, PosVersionStmt d X := by
  obtain ⟨X, _, hX, _, _, _, _⟩ := posVersion_with_good d hd hP
  exact ⟨X, hX⟩

end HigherDimLQGContinuity
