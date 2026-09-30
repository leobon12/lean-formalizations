import QuantumZipper.Proofs.Section5.Prop16LocGoodBasic

/-!
# Proposition 1.6, node LOCGOOD: `Prop16LocGoodStmt` from the domain-Markov coupling

`prop16LocGoodStmt_of_coupling`: the local good-sample node `Prop16LocGoodStmt` of
`Prop16Wire.lean` follows from `Prop16MixedFreeLocCouplingStmt`, the domain Markov coupling of
the mixed field on `D` with a free field on `ℍ`:

  on some standard Borel probability space there are a mixed GFF `Y` on `D` (zero on
  `∂D \ [c,d]`, free on `[c,d]`) and a free field mod constants `X` on `ℍ` such that a.s.
  `Y = X + ψ` on the dyadic folded circles inside `D ∪ (a,b)`, with `ψ` continuous on
  `D ∪ (a,b)`.

Mathematically this is Sheffield, *Gaussian free fields for mathematicians*, PTRF 139 (2007),
Thm. 2.17 (PDF p. 14), in its mixed-boundary form: the mixed space `H_mixed(D)` (extended by
zero) is a closed subspace of the free space `H(ℍ)`, whose orthogonal complement consists of
functions harmonic in `D` with Neumann condition on `(c,d)`, so `h_ℍ = h_D^mixed + φ` with `φ`
independent and (by reflection across `(c,d)` and a harmonic version, Werner–Powell,
arXiv:2004.04720, Prop. 4.3) continuous on `D ∪ (c,d)`; `ψ := −φ` plus the additive constant of
the mod-constants normalisation. This is the whole-domain analogue of the half-disc M7 statement
`K3.MixedFreeCouplingHalfDiscStmt` (decision D22); it is **not proved here**, only named.

The reduction (own argument, measure-theoretic):

1. the dyadic folded circles inside `D ∪ (a,b)` form a countable family (`locCircSet`) of
   mixed-admissible measures (`locGood_isAdmissible_circle`), so the laws of these coordinates of
   the given `X` and of the coupled `Y` agree (`locGood_map_eq_of_isMixedGFF`);
2. on the coupling space, a.s. `X` is good (`AreaOffsets.ae_isLQGGood`) and `Y = X + ψ` on the
   circles; the transfer lemma `locGood_ae_exists_of_map_eq` (disintegration) gives, for
   `P`-a.e. `ω`, a coupling point `ω₀` with the same circle coordinates, and `y := X ω₀` is the
   witness of `IsLocallyGoodOn` for the given sample (the open set `W` from `locGood_exists_open`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric

namespace QuantumZipper

namespace Prop16Asm

/-- **Domain Markov coupling of the mixed field on `D` with the free field on `ℍ`** (not proved;
Sheffield (2007) Thm 2.17, mixed form). On a standard Borel probability space: a mixed GFF `Y`
on `D`, a free field mod constants `X` on `ℍ`, and a.s. a function `ψ` continuous on
`D ∪ (a,b)` with `Y = X + ψ` on every dyadic folded circle whose closed half-disc lies in
`D ∪ (a,b)`. -/
def Prop16MixedFreeLocCouplingStmt : Prop :=
  ∀ (D : Set ℂ) (c d a b : ℝ), K3.Prop16Geometry D c d → a < b → c ≤ a → b ≤ d →
    ∃ (Ω₀ : Type) (_ : MeasurableSpace Ω₀) (_ : StandardBorelSpace Ω₀) (P₀ : Measure Ω₀)
      (Y X : Ω₀ → FieldSample),
      IsProbabilityMeasure P₀ ∧ IsMixedGFF D (realSet (Set.Icc c d)) Y P₀ ∧
      IsFreeGFFModConstH X P₀ ∧
      ∀ᵐ ω ∂P₀, ∃ ψ : ℂ → ℝ, ContinuousOn ψ (D ∪ realSet (Set.Ioo a b)) ∧
        Prop16Area.G.CircAgree (D ∪ realSet (Set.Ioo a b)) (Y ω) (X ω + ofFun ψ)

/-- **LOCGOOD from the domain Markov coupling.** -/
theorem prop16LocGoodStmt_of_coupling (hA : Prop16MixedFreeLocCouplingStmt) :
    Prop16LocGoodStmt := by
  intro γ D c d a b h0 Ω _ P X hdat
  obtain ⟨hγ, hγ2, hgeo, hab, hca, hbd, -, hP, hX, -, -⟩ := hdat
  obtain ⟨W, hWo, hWV⟩ := locGood_exists_open hgeo hca hbd
  obtain ⟨Ω₀, _, _, P₀, Y, Xf, hP₀, hY, hXf, hag⟩ := hA D c d a b hgeo hab hca hbd
  set V := D ∪ realSet (Ioo a b) with hVdef
  have hVW : ∀ {s : Set ℂ}, s ⊆ Hbar → (s ⊆ V ↔ s ⊆ W) := fun {s} hs =>
    ⟨fun h u hu => by rw [← hWV] at h; exact (h hu).1,
      fun h u hu => by rw [← hWV]; exact ⟨h hu, hs hu⟩⟩
  have hsubH : ∀ (n k : ℕ) (z : ℂ), closedBall (dyadicRoundC n z) (radius k) ∩ Hbar ⊆ Hbar :=
    fun _ _ _ => inter_subset_right
  let I := {m : Measure ℂ // m ∈ locCircSet V}
  haveI : Countable I := (locCircSet_countable V).to_subtype
  have hadm : ∀ i : I, IsAdmissibleDual D (mixedSpace D (realSet (Icc c d))) i.1 := by
    rintro ⟨_, n, k, z, hz, hsub, rfl⟩
    exact locGood_isAdmissible_circle hgeo hca hbd hWo hWV
      (CircleCont.dyadicRoundC_mem_Hbar hz n) (radius_pos k) ((hVW (hsubH n k z)).1 hsub)
  have hlaw := locGood_map_eq_of_isMixedGFF hX hY (fun i : I => i.1) hadm
  have hS : ∀ᵐ ω₀ ∂P₀, ω₀ ∈ {ω₀ | IsLQGGood γ (Xf ω₀) ∧ ∃ ψ : ℂ → ℝ, ContinuousOn ψ V ∧
      Prop16Area.G.CircAgree V (Y ω₀) (Xf ω₀ + ofFun ψ)} := by
    filter_upwards [AreaOffsets.ae_isLQGGood hXf hγ hγ2, hag] with ω₀ h1 h2 using ⟨h1, h2⟩
  have hmF : Measurable fun ω (i : I) => X ω i.1 :=
    measurable_pi_iff.2 fun i => hX.measurable_coord _
  have hmG : Measurable fun ω (i : I) => Y ω i.1 :=
    measurable_pi_iff.2 fun i => hY.measurable_coord _
  filter_upwards [locGood_ae_exists_of_map_eq hmF.aemeasurable hmG hlaw hS] with ω hω
  obtain ⟨ω₀, ⟨hgood, ψ, hψ, hag'⟩, hFG⟩ := hω
  refine ⟨W, hWo, hWV, Xf ω₀, ψ, hgood, hψ, fun n k z hz hsub => ?_⟩
  have hsubV := (hVW (hsubH n k z)).2 hsub
  have h1 := congrFun hFG ⟨_, n, k, z, hz, hsubV, rfl⟩
  exact h1.trans (hag' n k z hz hsubV)

/-- **Proposition 1.6 from the domain Markov coupling and the weak TV-local node.** -/
theorem theorem1_6_of_coupling_tvw (hA : Prop16MixedFreeLocCouplingStmt)
    (hTVw : Prop16TVWeakStmt) : theorem1_6 :=
  theorem1_6_of_loc_tvw (prop16LocGoodStmt_of_coupling hA) hTVw

end Prop16Asm

end QuantumZipper
