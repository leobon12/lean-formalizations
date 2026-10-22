import HigherDimLQGMetric.Locality.LimitCI
import Mathlib.MeasureTheory.Function.FactorsThrough

/-! The cutoff and full field remain determined by the prescribed field
coordinates after transfer to a second representation with the same mark law. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory ProbabilityTheory
open LQGMetric.GM.Bilip

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l7a_comap_le_aeClosure_of_ae_eq
    {E β : Type*} [MeasurableSpace E] [MeasurableSpace β]
    (Q : Measure E) {M : MeasurableSpace E}
    {X Y : E → β} (hY : Measurable[M] Y) (h : X =ᵐ[Q] Y) :
    MeasurableSpace.comap X inferInstance ≤ aeClosure Q M := by
  rintro s ⟨S, hS, rfl⟩
  refine ⟨Y ⁻¹' S, hY hS, ?_⟩
  filter_upwards [h] with e he
  change (X e ∈ S) = (Y e ∈ S)
  rw [he]

theorem l7a_ae_of_equal_laws
    {Ω E S β : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    [MeasurableSpace S] [MeasurableSpace β] [MeasurableEq β]
    (P : Measure Ω) (Q : Measure E)
    (X : Ω → S) (Y : E → S) (hX : Measurable X) (hY : Measurable Y)
    (hlaw : Q.map Y = P.map X)
    (f g : S → β) (hf : Measurable f) (hg : Measurable g)
    (heq : (f ∘ X) =ᵐ[P] (g ∘ X)) :
    (f ∘ Y) =ᵐ[Q] (g ∘ Y) := by
  have hs : MeasurableSet {s : S | f s = g s} := measurableSet_eq_fun hf hg
  have hp : ∀ᵐ s ∂(P.map X), f s = g s :=
    (ae_map_iff hX.aemeasurable hs).2 heq
  rw [← hlaw] at hp
  exact (ae_map_iff hY.aemeasurable hs).1 hp

theorem l7a_field_from_mark_law
    {d : ℕ} {Ω E S : Type*}
    [mΩ : MeasurableSpace Ω] [mE : MeasurableSpace E]
    [MeasurableSpace S]
    (P : Measure Ω) (Q : Measure E)
    (X : Ω → S) (Y : E → S) (hX : Measurable X) (hY : Measurable Y)
    (hlaw : Q.map Y = P.map X)
    (V : TopologicalSpace.Opens (Rd d))
    (g : Ω → DistRd d) (g' : S → DistRd d)
    (hg' : Measurable g') (hgX : g = g' ∘ X)
    (F : Ω → C(Rd d, ℝ)) (F' : S → C(Rd d, ℝ))
    (hF' : Measurable F') (hFX : F = F' ∘ X)
    (hFm : Measurable[fieldSigmaRd g V] F)
    (R : Ω → DistOn (extOpen V)) (R' : S → DistOn (extOpen V))
    (hR' : Measurable R') (hRX : R = R' ∘ X)
    (raw : Ω → DistOn (extOpen V)) (hRae : raw =ᵐ[P] R)
    (hdet : LQGMetric.AEDeterminedBy g
      (fun ω => (restrictTo V (g ω), raw ω)) P) :
    let G := MeasurableSpace.comap (fun e => restrictTo V (g' (Y e))) inferInstance
    let H := MeasurableSpace.comap (R' ∘ Y) inferInstance
    MeasurableSpace.comap (F' ∘ Y) inferInstance ≤ aeClosure Q G ∧
      MeasurableSpace.comap (g' ∘ Y) inferInstance ≤ aeClosure Q (H ⊔ G) := by
  dsimp only
  let gV : S → DistOn V := fun s => restrictTo V (g' s)
  have hgV : Measurable gV := (measurable_restrictTo V).comp hg'
  have hgp (ω : Ω) : g ω = g' (X ω) := by
    simpa only [Function.comp_def] using congrFun hgX ω
  have hFp (ω : Ω) : F ω = F' (X ω) := by
    simpa only [Function.comp_def] using congrFun hFX ω
  have hRp (ω : Ω) : R ω = R' (X ω) := by
    simpa only [Function.comp_def] using congrFun hRX ω
  obtain ⟨f, hf, hFeq⟩ := hFm.exists_eq_measurable_comp
  have hFae : (F' ∘ Y) =ᵐ[Q] (f ∘ gV ∘ Y) := by
    apply l7a_ae_of_equal_laws P Q X Y hX hY hlaw F' (f ∘ gV)
      hF' (hf.comp hgV)
    apply Filter.Eventually.of_forall
    intro ω
    change F' (X ω) = f (gV (X ω))
    calc
      F' (X ω) = F ω := (hFp ω).symm
      _ = f (restrictTo V (g ω)) := congrFun hFeq ω
      _ = f (gV (X ω)) := by
        change f (restrictTo V (g ω)) = f (restrictTo V (g' (X ω)))
        rw [hgp ω]
  have hFdet : Measurable[MeasurableSpace.comap (gV ∘ Y) inferInstance]
      (f ∘ gV ∘ Y) := hf.comp (comap_measurable _)
  have hFc : MeasurableSpace.comap (F' ∘ Y) inferInstance ≤
      aeClosure Q (MeasurableSpace.comap (gV ∘ Y) inferInstance) :=
    l7a_comap_le_aeClosure_of_ae_eq Q hFdet hFae
  obtain ⟨T, hT, hTae⟩ := hdet
  have hgeq : (g' ∘ Y) =ᵐ[Q]
      ((fun s => T (gV s, R' s)) ∘ Y) := by
    apply l7a_ae_of_equal_laws P Q X Y hX hY hlaw g'
      (fun s => T (gV s, R' s)) hg' (hT.comp (hgV.prodMk hR'))
    filter_upwards [hTae, hRae] with ω hω hrω
    change g' (X ω) = T (gV (X ω), R' (X ω))
    calc
      g' (X ω) = g ω := (hgp ω).symm
      _ = T (restrictTo V (g ω), raw ω) := by simpa only [Function.comp_def] using hω
      _ = T (gV (X ω), R' (X ω)) := by
        have hr : R' (X ω) = R ω := (hRp ω).symm
        rw [show gV (X ω) = restrictTo V (g ω) from by
          change restrictTo V (g' (X ω)) = restrictTo V (g ω)
          rw [← hgp ω], hr, ← hrω]
  have hTdet : Measurable[MeasurableSpace.comap (R' ∘ Y) inferInstance ⊔
      MeasurableSpace.comap (gV ∘ Y) inferInstance]
      ((fun s => T (gV s, R' s)) ∘ Y) := by
    have ha : Measurable[MeasurableSpace.comap (R' ∘ Y) inferInstance ⊔
        MeasurableSpace.comap (gV ∘ Y) inferInstance] (gV ∘ Y) :=
      (comap_measurable _).mono le_sup_right le_rfl
    have hb : Measurable[MeasurableSpace.comap (R' ∘ Y) inferInstance ⊔
        MeasurableSpace.comap (gV ∘ Y) inferInstance] (R' ∘ Y) :=
      (comap_measurable _).mono le_sup_left le_rfl
    exact hT.comp (ha.prodMk hb)
  exact ⟨hFc, l7a_comap_le_aeClosure_of_ae_eq Q hTdet hgeq⟩

end HigherDimLQGMetric
