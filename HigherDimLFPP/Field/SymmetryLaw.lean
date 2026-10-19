import HigherDimLFPP.Field.Symmetry
import HigherDimLFPP.Field.LawTransfer

/-!
# Similarity invariance in law of the band fields (packet P-X2, target T1, consequences)

Source: `source/higher-dimensional-lfpp-limit.pdf`, §3.1 ("`H_{ra,rb} ∘ T` has the law of
`H_{a,b}`"); planning audits HA5 Details D14 (DGZ Lemma 2.2(2), (4), Lemma 2.5), HA2 Details D2
(Lemma D2.2, Corollaries (ii), (iii)) and HA4 Details D2 ("law invariance": the centered Gaussian
field on band triples is invariant in law under `Y ↦ Y ∘ τ_S`, jointly over all bands and points)
and D7.

For the similarity `T z = x₀ + r • O z` (`r > 0`, `O` a linear isometry), `V_T = simL2 O x₀ hr`
is a linear isometry equivalence of `WN d` with `k_{a,b,Tz} = V_T k_{a/r,b/r,z}` (`bandVec_sim`),
and `W ∘ V_T` is a white noise (`IsWhiteNoise.comp_simL2`). With the law transfer of
`HigherDimLFPP/Field/LawTransfer.lean`:

* `IsWhiteNoise.map_bandVec_sim_eq`: for any family of bands `(a i, b i)` (`0 < a i`) and points
  `z i`, `(H_{a_i,b_i}(T z_i))_i` over `W` and `(H_{a_i/r,b_i/r}(z_i))_i` over any white noise `W'`
  have the same joint law; `IsWhiteNoise.map_bandVec_sim_mul_eq` is HA4's form
  `(H_{r a_i, r b_i}(T z_i))_i =ᵈ (H_{a_i,b_i}(z_i))_i`;
* `map_bandVersion_sim_eq` (target T1): the version families `(j, z) ↦ H_j(T z)` (bands
  `(a j, b j)`, white noise `W`) and `(j, z) ↦ H'_j(z)` (bands `(a j / r, b j / r)`, any white noise
  `W'`) have the same joint law on `J × Rd d → ℝ`; `IsBandVersion.map_sim_eq` for one band, and
  its special cases `IsBandVersion.map_isometry_eq` (DGZ Lemma 2.2(2)) and
  `IsBandVersion.map_smul_eq` (DGZ Lemma 2.2(4));
* `IsBandVersion.map_comp_sim_eq_of_measurable`, `IsBandVersion.map_lfppDistance_sim_eq`: the same
  for functionals that are Borel measurable on `C(Rd d, ℝ)` (DGZ Lemma 2.5 with the path transport
  of packet P-X1).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped RealInnerProductSpace

namespace HigherDimLFPP

variable {d : ℕ} {κ : Rd d → ℝ} {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  {P : Measure Ω} {P' : Measure Ω'} {W : WN d → Ω → ℝ} {W' : WN d → Ω' → ℝ}

/-- **Similarity invariance in law of white-noise band families** (target T1): for any family of
bands `(a i, b i)` with `0 < a i` and points `z i` (any index type), the families
`(H_{a_i,b_i}(T z_i))_i` (white noise `W`) and `(H_{a_i/r,b_i/r}(z_i))_i` (any white noise `W'`,
possibly on another probability space) have the same joint law, for `T z = x₀ + r • O z`. -/
theorem IsWhiteNoise.map_bandVec_sim_eq (hW : IsWhiteNoise P W) (hW' : IsWhiteNoise P' W')
    (hκ : IsLFPPKernel κ) (O : Rd d ≃ₗᵢ[ℝ] Rd d) (x₀ : Rd d) {r : ℝ} (hr : 0 < r) {I : Type*}
    {a b : I → ℝ} (ha : ∀ i, 0 < a i) (z : I → Rd d) :
    P.map (fun ω i => W (bandVec κ (a i) (b i) (x₀ + r • O (z i))) ω) =
      P'.map (fun ω i => W' (bandVec κ (a i / r) (b i / r) (z i)) ω) := by
  calc P.map (fun ω i => W (bandVec κ (a i) (b i) (x₀ + r • O (z i))) ω)
      = P.map (fun ω i => W (simL2 O x₀ hr (bandVec κ (a i / r) (b i / r) (z i))) ω) := by
        congr 1
        funext ω i
        rw [bandVec_sim hκ O x₀ hr (ha i)]
    _ = P'.map (fun ω i => W' (bandVec κ (a i / r) (b i / r) (z i)) ω) :=
        (hW.comp_simL2 O x₀ hr).map_eq hW' fun i => bandVec κ (a i / r) (b i / r) (z i)

/-- **Similarity invariance in law**, HA4's form (D2, "law invariance" under
`τ_S(a, b, z) = (r a, r b, S z)`): `(H_{r a_i, r b_i}(T z_i))_i =ᵈ (H_{a_i,b_i}(z_i))_i`, jointly
over all bands and points. -/
theorem IsWhiteNoise.map_bandVec_sim_mul_eq (hW : IsWhiteNoise P W) (hW' : IsWhiteNoise P' W')
    (hκ : IsLFPPKernel κ) (O : Rd d ≃ₗᵢ[ℝ] Rd d) (x₀ : Rd d) {r : ℝ} (hr : 0 < r) {I : Type*}
    {a b : I → ℝ} (ha : ∀ i, 0 < a i) (z : I → Rd d) :
    P.map (fun ω i => W (bandVec κ (r * a i) (r * b i) (x₀ + r • O (z i))) ω) =
      P'.map (fun ω i => W' (bandVec κ (a i) (b i) (z i)) ω) := by
  have h := hW.map_bandVec_sim_eq hW' hκ O x₀ hr (a := fun i => r * a i) (b := fun i => r * b i)
    (fun i => mul_pos hr (ha i)) z
  simp only [mul_div_cancel_left₀ _ hr.ne'] at h
  exact h

/-- **Similarity invariance in law of version families** (target T1): let `T z = x₀ + r • O z`,
`r > 0`. For bands `(a j, b j)` (`0 < a j`, `j ∈ J` any index type), continuous versions `H j` of
`H_{a_j,b_j}` over `W` and `H' j` of `H_{a_j/r,b_j/r}` over any white noise `W'`, the families
`(j, z) ↦ H_j(T z)` and `(j, z) ↦ H'_j(z)` have the same joint law on `J × Rd d → ℝ`. -/
theorem map_bandVersion_sim_eq (hW : IsWhiteNoise P W) (hW' : IsWhiteNoise P' W')
    (hκ : IsLFPPKernel κ) (O : Rd d ≃ₗᵢ[ℝ] Rd d) (x₀ : Rd d) {r : ℝ} (hr : 0 < r) {J : Type*}
    {a b : J → ℝ} (ha : ∀ j, 0 < a j) {H : J → Rd d → Ω → ℝ} {H' : J → Rd d → Ω' → ℝ}
    (hH : ∀ j, IsBandVersion P W κ (a j) (b j) (H j))
    (hH' : ∀ j, IsBandVersion P' W' κ (a j / r) (b j / r) (H' j)) :
    P.map (fun ω (p : J × Rd d) => H p.1 (x₀ + r • O p.2) ω) =
      P'.map (fun ω (p : J × Rd d) => H' p.1 p.2 ω) :=
  map_bandVersion_family_eq (fun j => (hH j).comp_sim hκ O x₀ hr (ha j)) hH'
    (hW.comp_simL2 O x₀ hr) hW'

namespace IsBandVersion

variable {a b r : ℝ} {H : Rd d → Ω → ℝ} {H' : Rd d → Ω' → ℝ}

/-- **Similarity invariance in law of one version** (target T1): `z ↦ H_{a,b}(T z)` and
`z ↦ H'_{a/r,b/r}(z)` (any white noise) have the same law on `Rd d → ℝ`. -/
theorem map_sim_eq (hH : IsBandVersion P W κ a b H) (hH' : IsBandVersion P' W' κ (a / r) (b / r) H')
    (hW : IsWhiteNoise P W) (hW' : IsWhiteNoise P' W') (hκ : IsLFPPKernel κ)
    (O : Rd d ≃ₗᵢ[ℝ] Rd d) (x₀ : Rd d) (hr : 0 < r) (ha : 0 < a) :
    P.map (fun ω z => H (x₀ + r • O z) ω) = P'.map (fun ω z => H' z ω) :=
  (hH.comp_sim hκ O x₀ hr ha).map_eq hH' (hW.comp_simL2 O x₀ hr) hW'

/-- **Isometry invariance in law** (DGZ Lemma 2.2(2)): `z ↦ H(x₀ + O z)` has the law of any
version `H'` of the same band field `H_{a,b}` over any white noise. -/
theorem map_isometry_eq (hH : IsBandVersion P W κ a b H) (hH' : IsBandVersion P' W' κ a b H')
    (hW : IsWhiteNoise P W) (hW' : IsWhiteNoise P' W') (hκ : IsLFPPKernel κ)
    (O : Rd d ≃ₗᵢ[ℝ] Rd d) (x₀ : Rd d) (ha : 0 < a) :
    P.map (fun ω z => H (x₀ + O z) ω) = P'.map (fun ω z => H' z ω) :=
  (hH.comp_isometry hκ O x₀ ha).map_eq hH' (hW.comp_simL2 O x₀ one_pos) hW'

/-- **Scaling in law** (DGZ Lemma 2.2(4)): `z ↦ H_{a,b}(r • z)` has the law of any version of
`H_{a/r,b/r}` over any white noise. -/
theorem map_smul_eq (hH : IsBandVersion P W κ a b H)
    (hH' : IsBandVersion P' W' κ (a / r) (b / r) H') (hW : IsWhiteNoise P W)
    (hW' : IsWhiteNoise P' W') (hκ : IsLFPPKernel κ) (hr : 0 < r) (ha : 0 < a) :
    P.map (fun ω z => H (r • z) ω) = P'.map (fun ω z => H' z ω) :=
  (hH.comp_smul hκ hr ha).map_eq hH' (hW.comp_simL2 _ 0 hr) hW'

/-- **Similarity invariance in law of field functionals**: for every `G : (Rd d → ℝ) → β` that is
Borel measurable on `C(Rd d, ℝ)`, `G(H ∘ T)` and `G(H')` have the same law (HA5 D14: with the
path transport of packet P-X1 this gives DGZ Lemma 2.5). -/
theorem map_comp_sim_eq_of_measurable (hH : IsBandVersion P W κ a b H)
    (hH' : IsBandVersion P' W' κ (a / r) (b / r) H') (hW : IsWhiteNoise P W)
    (hW' : IsWhiteNoise P' W') (hκ : IsLFPPKernel κ) (O : Rd d ≃ₗᵢ[ℝ] Rd d) (x₀ : Rd d)
    (hr : 0 < r) (ha : 0 < a) {β : Type*} [MeasurableSpace β] {G : (Rd d → ℝ) → β}
    (hG : Measurable fun f : C(Rd d, ℝ) => G f) :
    P.map (fun ω => G fun z => H (x₀ + r • O z) ω) = P'.map (fun ω => G fun z => H' z ω) :=
  (hH.comp_sim hκ O x₀ hr ha).map_comp_eq_of_measurable hH' (hW.comp_simL2 O x₀ hr) hW' hG

/-- The LFPP distance of the transported field: `D^ζ(H ∘ T)` has the law of `D^ζ(H')`, once
`f ↦ D^ζ(f)` is Borel measurable on `C(Rd d, ℝ)` (packet P-X1). -/
theorem map_lfppDistance_sim_eq (hH : IsBandVersion P W κ a b H)
    (hH' : IsBandVersion P' W' κ (a / r) (b / r) H') (hW : IsWhiteNoise P W)
    (hW' : IsWhiteNoise P' W') (hκ : IsLFPPKernel κ) (O : Rd d ≃ₗᵢ[ℝ] Rd d) (x₀ : Rd d)
    (hr : 0 < r) (ha : 0 < a) (ζ : ℝ)
    (hmeas : Measurable fun f : C(Rd d, ℝ) => lfppDistance d ζ f) :
    P.map (fun ω => lfppDistance d ζ fun z => H (x₀ + r • O z) ω) =
      P'.map (fun ω => lfppDistance d ζ fun z => H' z ω) :=
  hH.map_comp_sim_eq_of_measurable hH' hW hW' hκ O x₀ hr ha hmeas

end IsBandVersion

end HigherDimLFPP
