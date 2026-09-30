import QuantumZipper.Proofs.Zipper.D3PlusN2RIdx

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# N2-H2 on the restricted window index (Decision D36)

Task D36-IMPL, step (3). The N2-H2 node `N2HLatTVStmt` (`D3PlusN2HeartStmt.lean`) is stated over
the full window index `LocIdx K`, where the model side needs a.s. convergence of the dyadic
regularization at arbitrary local admissible measures — the project gap `F2.EvalRegRawStmt`/D17
(`D3PlusN2H2Obstr`). Here the same statement is restated on the restricted index `WinIdx K`
(`D3PlusN2RIdx.lean`: folded circles and bounded compactly supported densities inside the window,
Decision D36).

* `latWinW K a y`: the lateral window at scale `a` read on the restricted index
  (`latWinW_eq_latWin`: on the index it is the restriction of the full-index `latWin`).
* `latY''W K X''` (`= latFreeW K X''`): the wedge-side lateral window on the restricted index.
* `latWinFreeW K a X` / `latFreeW K X`: the middle term of the reduction (`N2H2Basic`), on the
  restricted index; definitionally the `N2H2Law.latWinFreeI`/`latFreeI` families of
  `D3PlusN2H2Law`.

**Proved here** (the free-field half of H2): `map_latWinFreeW_eq` — for every `a > 0` the law of
the rescaled free-field lateral window on the restricted index equals the law of the plain
lateral window of every free GFF mod const H. It is `N2H2Law.map_latWinFreeI_eq` at the family
`winIdx K` (whose regularity is `winRegFam_winIdx`). Consequence (assembly, own elementary
triangle inequality, copied from `n2HLatTV_of_parts`): `n2HLatTVWin_of_harm` reduces the
restricted H2 node `N2HLatTVWinStmt` to the single named analytic Prop `N2H2HarmWinStmt` — the
model-side harmonic-correction (Cameron–Martin) statement of `N2H2HarmStmt` restricted to the
same index. That is exactly the shape of `N2HLatTVStmt` over `LocIdx K`; on the restricted index
the missing convergence is supplied by `winRegFam_winIdx`, so `N2H2HarmWinStmt` is the D36
counterpart of `N2H2HarmStmt` (`D3PlusN2H2Basic.lean`), whose analytic content (Markov
decomposition `Z = X − h_X`, `C²` cutoff of the harmonic part of Dirichlet energy `O(a²)` on the
window) is unchanged (whether the unrestricted reduction `D3PlusN2Cutoff` transfers to the
restricted family has not been checked).

Sources: Duplantier–Miller–Sheffield, arXiv:1409.7055, proof of Prop. 4.7(ii), pp. 77–78;
Berestycki–Powell, arXiv:2004.04720, Lemmas 3.12, 3.14; see `D3PlusN2H2Basic.lean` and
`D3PlusN2H2Law.lean` for the full attribution.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace D3Plus

/-! ## The window data on the restricted index -/

/-- The lateral window at scale `a` read on the restricted index (the restriction of `latWin`). -/
def latWinW (K : ℕ) (a : ℝ) (y : FieldSample) : WinIdx K → ℝ :=
  fun i => evalReg y ((winIdx K i).map fun z => (a : ℂ) * z)

/-- The free-field lateral window at scale `a` on the restricted index (`N2H2Basic`'s middle
term). -/
def latWinFreeW (K : ℕ) (a : ℝ) {Ω : Type} (X : Ω → FieldSample) : Ω → WinIdx K → ℝ :=
  fun ω i => evalReg (X ω) ((winIdx K i).map fun z => (a : ℂ) * z) -
    ∫ z, radAvgReg (X ω) (a * ‖z‖) ∂(winIdx K i)

/-- The lateral part of the free field on the restricted index. -/
def latFreeW (K : ℕ) {Ω : Type} (X : Ω → FieldSample) : Ω → WinIdx K → ℝ :=
  fun ω i => lateralPart (X ω) (winIdx K i)

/-- The wedge-side window data on the restricted index (definitionally the free-field lateral
part, as `latY''_eq_n2LatFree` on the full index). -/
def latY''W (K : ℕ) {Ω : Type} (X : Ω → FieldSample) : Ω → WinIdx K → ℝ := latFreeW K X

theorem latWinFreeW_eq_latWinFreeI (K : ℕ) (a : ℝ) {Ω : Type} (X : Ω → FieldSample) :
    latWinFreeW K a X = N2H2Law.latWinFreeI (winIdx K) a X := rfl

theorem latFreeW_eq_latFreeI (K : ℕ) {Ω : Type} (X : Ω → FieldSample) :
    latFreeW K X = N2H2Law.latFreeI (winIdx K) X := rfl

theorem measurable_latWinFreeW {Ω : Type} [MeasurableSpace Ω] {X : Ω → FieldSample}
    (hX : ∀ μ : Measure ℂ, Measurable fun ω => X ω μ) (K : ℕ) (a : ℝ) :
    Measurable (latWinFreeW K a X) :=
  N2H2Law.measurable_latWinFreeI (isAdmissibleH_winIdx K) hX a

/-! ## The free half of H2 on the restricted index (proved) -/

/-- **Free-field half of N2-H2 on the restricted index**: for every `a > 0` the rescaled
free-field lateral window on the restricted index has the law of the plain lateral window of
every free GFF mod const H (`N2H2Law.map_latWinFreeI_eq` at `winIdx K`). -/
theorem map_latWinFreeW_eq {K : ℕ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → FieldSample} (hX : IsFreeGFFModConstH X P)
    {Ω'' : Type} [MeasurableSpace Ω''] {P'' : Measure Ω''} [IsProbabilityMeasure P'']
    {X'' : Ω'' → FieldSample} (hX'' : IsFreeGFFModConstH X'' P'') {a : ℝ} (ha : 0 < a) :
    P.map (latWinFreeW K a X) = P''.map (latFreeW K X'') := by
  rw [latWinFreeW_eq_latWinFreeI, latFreeW_eq_latFreeI]
  exact N2H2Law.map_latWinFreeI_eq (ι := winIdx K) (hι := winRegFam_winIdx K)
    (Ω := Ω) (P := P) (X := X) (Ω'' := Ω'') (P'' := P'') (X'' := X'') hX hX'' ha

/-! ## The restricted H2 node and its reduction -/

/-- **N2-H2, model side, restricted index** (D36 counterpart of `N2H2HarmStmt`): the lateral
window of the local field `Z` at scale `a` on the restricted index converges, as `a → 0⁺`, to the
lateral window of the free field in TV. Content unchanged from `N2H2HarmStmt` (Markov
decomposition `Z = X − h_X`, Cameron–Martin for the `C²` cutoff of the harmonic part); the
restricted index is what supplies the a.s. convergence of the regularized evaluation at the
rescaled window measures. -/
def N2H2HarmWinStmt : Prop :=
  ∀ (r : ℝ) (K : ℕ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → FieldSample), 0 < r → IsFreeGFFModConstH X P →
    Tendsto (fun a => TV.tvDist (P.map fun ω => latWinW K a (n2LatY X r ω))
      (P.map (latWinFreeW K a X))) (𝓝[>] 0) (𝓝 0)

/-- **N2-H2 on the restricted index** (D36 form of `N2HLatTVStmt`): the lateral window of the
local field `Z` at deterministic scale `a`, restricted to folded circles and bounded densities
inside the window, converges in TV to the wedge-side lateral window as `a → 0⁺`. -/
def N2HLatTVWinStmt : Prop :=
  ∀ (r : ℝ) (K : ℕ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → FieldSample) {Ω'' : Type} [MeasurableSpace Ω''] (P'' : Measure Ω'')
    [IsProbabilityMeasure P''] (X'' : Ω'' → FieldSample),
    0 < r → IsFreeGFFModConstH X P → IsFreeGFFModConstH X'' P'' →
    Tendsto (fun a => TV.tvDist (P.map fun ω => latWinW K a (n2LatY X r ω))
      (P''.map (latY''W K X''))) (𝓝[>] 0) (𝓝 0)

/-- **N2-H2 on the restricted index from its model half** (own elementary argument: triangle
inequality for `TV.tvDist` and the proved free half `map_latWinFreeW_eq`; copy of
`n2HLatTV_of_parts`). -/
theorem n2HLatTVWin_of_harm (hHarm : N2H2HarmWinStmt) : N2HLatTVWinStmt := by
  intro r K Ω _ P _ X Ω'' _ P'' _ X'' hr hX hX''
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  have hstep := (ENNReal.tendsto_nhds_zero.1 (hHarm r K P X hr hX)) η hη
  filter_upwards [hstep, self_mem_nhdsWithin] with a ha hapos
  have h0 : TV.tvDist (P.map (latWinFreeW K a X)) (P''.map (latY''W K X'')) = 0 := by
    rw [show latY''W K X'' = latFreeW K X'' from rfl, map_latWinFreeW_eq hX hX'' hapos]
    exact TV.tvDist_self
  calc TV.tvDist (P.map fun ω => latWinW K a (n2LatY X r ω)) (P''.map (latY''W K X''))
      ≤ TV.tvDist (P.map fun ω => latWinW K a (n2LatY X r ω)) (P.map (latWinFreeW K a X)) +
        TV.tvDist (P.map (latWinFreeW K a X)) (P''.map (latY''W K X'')) := TV.tvDist_triangle
    _ = TV.tvDist (P.map fun ω => latWinW K a (n2LatY X r ω)) (P.map (latWinFreeW K a X)) := by
        rw [h0, add_zero]
    _ ≤ η := ha

end D3Plus
end QuantumZipper
