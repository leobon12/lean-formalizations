import SupercriticalLQGUniqueness.Uniqueness.Objects.BlockWitness.BlockCircleBorel




 


set_option autoImplicit false
noncomputable section

open Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BlockWitness

abbrev BlockWitness (T : Objects.CorrectedEvent.TubeData) :=
  ((closedBall (Objects.Excursions.cU T) T.blockRadius) ×
    (closedBall (Objects.Excursions.cV T) T.blockRadius)) × Measurability.GeodesicCodes.Path

def BlockRelation (C : Objects.CorrectedEvent.Constants) (T : Objects.CorrectedEvent.TubeData)
    (Ksh : ℕ) (Cmid0 : ℝ)
    (D D' : LQGMetric.DistC → LSCMetric)
    (p : LQGMetric.DistC × BlockWitness T) : Prop :=
  let u : ℂ := p.2.1.1
  let v : ℂ := p.2.1.2
  ‖u‖ = T.alpha * (T.rho * T.r) ∧
  dist u (Objects.Excursions.cU T) < T.blockRadius / 2 ∧
  ‖v‖ = T.rho * T.r ∧
  dist v (Objects.Excursions.cV T) < T.blockRadius / 2 ∧
  D' p.1 (u, v) ≤ ENNReal.ofReal Cmid0 * D p.1 (u, v) ∧
  D' p.1 (u, v) < ⊤ ∧
  Measurability.GeodesicCodes.GeoCode (D' p.1, (p.2.2, (u, v))) ∧
  (∀ t, p.2.2 t ∈ closure (Objects.Excursions.blockShape T)) ∧
  Objects.Shadow.circleOuter (Objects.Excursions.cU T) T.blockRadius.toNNReal 0
      (sphere (Objects.Excursions.cU T) T.blockRadius \
        Objects.Producer.goodSet (D p.1) (Objects.Excursions.cU T) u T.blockRadius
          (C.lamConst * (D' p.1 (u, v)).toReal) p.2.1.1.property) ≤
    ENNReal.ofReal (C.lamConst * T.blockRadius / 2) ∧
  Objects.Shadow.circleOuter (Objects.Excursions.cV T) T.blockRadius.toNNReal 0
      (sphere (Objects.Excursions.cV T) T.blockRadius \
        Objects.Producer.goodSet (D p.1) (Objects.Excursions.cV T) v T.blockRadius
          (C.lamConst * (D' p.1 (u, v)).toReal) p.2.1.2.property) ≤
    ENNReal.ofReal (C.lamConst * T.blockRadius / 2) ∧
  Objects.Excursions.shield C T Ksh (D p.1)

theorem blockRaw_iff_projection (C : Objects.CorrectedEvent.Constants) (T : Objects.CorrectedEvent.TubeData)
    (Ksh : ℕ) (Cmid0 : ℝ)
    (D D' : LQGMetric.DistC → LSCMetric)
    (hn : ‖T.orientation‖ = 1) (hρr : 0 < T.rho * T.r)
    (g : LQGMetric.DistC) :
    Objects.Excursions.blockRaw C T Ksh Cmid0 D D' g ↔
      ∃ w : BlockWitness T, BlockRelation C T Ksh Cmid0 D D' (g, w) := by
  constructor
  · rintro ⟨⟨u, v, huNorm, huClose, hvNorm, hvClose, hratio, hfin,
        hgeo, hF3u, hF3v⟩, hshield⟩
    obtain ⟨huBall, huF3⟩ := hF3u
    obtain ⟨hvBall, hvF3⟩ := hF3v
    obtain ⟨P, a, b, hcurve, hPa, hPb, htrace, hlen⟩ := hgeo
    obtain ⟨Q, hcode, hQtrace⟩ :=
      (block_geodesic_iff_code T hn hρr (D' g) u v).mp
        ⟨⟨P, a, b, hcurve, hPa, hPb, htrace, hlen⟩, hfin⟩
    refine ⟨((⟨u, huBall⟩, ⟨v, hvBall⟩), Q), ?_⟩
    change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _
    refine ⟨huNorm, huClose, hvNorm, hvClose, hratio, hfin, hcode, hQtrace, ?_, ?_, hshield⟩
    · simpa only using huF3
    · simpa only using hvF3
  · rintro ⟨⟨⟨u, v⟩, Q⟩, hcode⟩
    rcases hcode with ⟨huNorm, huClose, hvNorm, hvClose, hratio, hfin,
      hQgeo, hQtrace, hF3u, hF3v, hshield⟩
    obtain ⟨⟨P, a, b, hcurve, hPa, hPb, htrace, hlen⟩, -⟩ :=
      (block_geodesic_iff_code T hn hρr (D' g) u v).mpr
        ⟨Q, hQgeo, hQtrace⟩
    refine ⟨⟨(u : ℂ), (v : ℂ), huNorm, huClose, hvNorm, hvClose,
      hratio, hfin, ⟨P, a, b, hcurve, hPa, hPb, htrace, hlen⟩,
      ⟨u.property, hF3u⟩, ⟨v.property, hF3v⟩⟩, hshield⟩


end SupercriticalLQGUniqueness.Uniqueness.Objects.BlockWitness
