import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.Sub.ConvGeoSub
import UnforcedLeray.Short.PartIIb.Sub.G4_3_org

/-!
# `TrainBand` from `RawJetBound` (`PartIII-b:C/asrc/ra/9/2/2/11`)

Source of record: `the November 2 reference manuscript`, 2419-2423 (jets of `v` and
`H = (1-𝒦)ψ` on `0 < s ≤ Σ/ν`, the content of `PartII-b` `RawJetBound`), 2055-2077, 4371.

`TrainBand` (planar form, `Σ = 11/10`) is the same estimate as `PartII-b` `RawJetBound`
(chart form), which `PartII-b` proves from the Part I statements `TrainTransverseTails`,
`TrainFixedBand` (`rawJetBound_of`).  Proved here: `trainBand_of_charts` (the `ageCut` is
irrelevant to the train, so it is reset to `11/10`; each of the six quantities is dominated by
`2×` the chart sum).  The two chart comparison leaves `TBChartVel`, `TBChartRaised` are Props.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Cons.C03.Concrete (Params)

/-- **Chart comparison for the velocity** (planar `trPl p s = v(s)` versus the chart profile
`trainProf p`, `x = (q, η)`, `Axi.dQ`, `Axi.dEta`, `kAge = 2s ∂_s + η ∂_η`): for `s > 0`,
`‖v‖ ≤ ‖v‖_{ℓ²}` (sup norm ≤ `ℓ²` norm), `‖D_x v‖ ≤ ‖∂_q v‖ + ‖∂_η v‖` (operator norm on `ℝ²` is at
most the sum over the basis), `‖𝒦v‖ ≤ ‖kAge v‖`; hence the sum is `≤ 2×` the chart sum.  Needs
joint differentiability of `v` in `(s, q, η)` for `s > 0` (`IIb.trainVelSmooth_proof`, i.e.
`TrainVelSmooth`, in `Short/PartII-b/Tasks/AffineColumnComparison/Column/RawJet/Leaves/TrainVelSmooth.lean`)
so that the slice derivatives are the partials of the joint derivative. -/
def TBChartVel : Prop :=
  ∀ (p : Params) (d dm dp : ℝ), UnforcedLeray.Short.IIb.BgRegime p d dm dp →
    ∀ (s : ℝ), 0 < s → ∀ x : ℝ × ℝ,
      ‖trPl p s x‖ + ‖fderiv ℝ (trPl p s) x‖ + ‖cK (trPl p) s x‖ ≤
        2 * (‖UnforcedLeray.Short.IIb.trainProf p (s, x)‖ +
          ‖UnforcedLeray.Axi.dQ (UnforcedLeray.Short.IIb.trainProf p) (s, x)‖ +
          ‖UnforcedLeray.Axi.dEta (UnforcedLeray.Short.IIb.trainProf p) (s, x)‖ +
          ‖UnforcedLeray.Short.IIb.kAge (UnforcedLeray.Short.IIb.trainProf p) (s, x)‖)

/-- **Chart comparison for the raised stream** (`trH p s x = raisedStream ψ s x.1 x.2 =
raisedProf p (s, x)` by definition; `Kop (trH p) s x = η ∂_η H + 2 s ∂_s H = kAge (raisedProf p)`):
for `s > 0`, `|H| + ‖D_x H‖ + |𝒦H| ≤ 2 (|H| + |∂_qH| + |∂_ηH| + |kAge H|)`.  Needs joint
differentiability of `raisedProf p` at `(s, x)`, `s > 0`, from `BgRegime.train_stream_smooth`
(`ψ` is `C^∞` on `s > 0`, so `raisedStream` — built from its first partials — is `C^∞` there; cf.
`Short/PartII-b/Tasks/AffineColumnComparison/Column/RawJet/Leaves/RaisedChartBridge.lean`). -/
def TBChartRaised : Prop :=
  ∀ (p : Params) (d dm dp : ℝ), UnforcedLeray.Short.IIb.BgRegime p d dm dp →
    ∀ (s : ℝ), 0 < s → ∀ x : ℝ × ℝ,
      |trH p s x| + ‖fderiv ℝ (trH p s) x‖ + |Kop (trH p) s x| ≤
        2 * (|UnforcedLeray.Short.IIb.raisedProf p (s, x)| +
          |UnforcedLeray.Axi.dQ (UnforcedLeray.Short.IIb.raisedProf p) (s, x)| +
          |UnforcedLeray.Axi.dEta (UnforcedLeray.Short.IIb.raisedProf p) (s, x)| +
          |UnforcedLeray.Short.IIb.kAge (UnforcedLeray.Short.IIb.raisedProf p) (s, x)|)

theorem trainBand_of_charts (hR : UnforcedLeray.Short.IIb.RawJetBound) (h1 : TBChartVel)
    (h2 : TBChartRaised) : TrainBand := by
  intro dm dp hdm
  obtain ⟨C, k, N, ν₀, hC, hν₀, H⟩ := hR (11 / 10) (by norm_num) dm dp hdm
  refine ⟨2 * C, k, N, ν₀, hν₀, fun p d hreg hν s hs hsT x => ?_⟩
  set p' : Params := { p with ageCut := 11 / 10, ageCut_pos := by norm_num } with hp'
  have hreg' : UnforcedLeray.Short.IIb.BgRegime p' d dm dp :=
    ⟨hreg.dm_pos, hreg.dm_le, hreg.le_dp, hreg.eps_eq, hreg.c_eq, hreg.train_buc,
      hreg.train_stream_smooth⟩
  have hHp : p'.H = (11 / 10) / p.ν := rfl
  have hb : ‖UnforcedLeray.Short.IIb.trainProf p (s, x)‖ +
      ‖UnforcedLeray.Axi.dQ (UnforcedLeray.Short.IIb.trainProf p) (s, x)‖ +
      ‖UnforcedLeray.Axi.dEta (UnforcedLeray.Short.IIb.trainProf p) (s, x)‖ +
      ‖UnforcedLeray.Short.IIb.kAge (UnforcedLeray.Short.IIb.trainProf p) (s, x)‖ +
      (|UnforcedLeray.Short.IIb.raisedProf p (s, x)| +
        |UnforcedLeray.Axi.dQ (UnforcedLeray.Short.IIb.raisedProf p) (s, x)| +
        |UnforcedLeray.Axi.dEta (UnforcedLeray.Short.IIb.raisedProf p) (s, x)| +
        |UnforcedLeray.Short.IIb.kAge (UnforcedLeray.Short.IIb.raisedProf p) (s, x)|) ≤
      C * (p.ν ^ k)⁻¹ * (1 + |x.2|) ^ N :=
    H p' d hreg' hν rfl (s, x) hs (by rw [hHp]; exact hsT)
  have hv := h1 p d dm dp hreg s hs x
  have hr := h2 p d dm dp hreg s hs x
  have hbd : (C * (p.ν ^ k)⁻¹ * (1 + |x.2|) ^ N) = C * p.ν⁻¹ ^ k * (1 + |x.2|) ^ N := by
    rw [inv_pow]
  have n1 := norm_nonneg (trPl p s x)
  have n2 := norm_nonneg (fderiv ℝ (trPl p s) x)
  have n3 := norm_nonneg (cK (trPl p) s x)
  have n4 := abs_nonneg (trH p s x)
  have n5 := norm_nonneg (fderiv ℝ (trH p s) x)
  have n6 := abs_nonneg (Kop (trH p) s x)
  have e1 : (2 * C) * p.ν⁻¹ ^ k * (1 + |x.2|) ^ N = 2 * (C * p.ν⁻¹ ^ k * (1 + |x.2|) ^ N) := by ring
  rw [e1, ← hbd]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> nlinarith [hb, hv, hr, n1, n2, n3, n4, n5, n6]

end UnforcedLeray.Short.PartIIIb.Concrete
