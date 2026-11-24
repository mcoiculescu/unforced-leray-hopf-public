import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_3_7

/-!
# Part II-b, task `PartII-b:G4/3/7/7`: the interaction is bilinear in the jets (`BEpsJet`)

Source of record: `the November 2 reference manuscript` (SP) lines 2370-2374.
Pure algebra from `bEps`, `qEps`, `chartJet`: for `0 ≤ ε ≤ 1`,
`‖B_εF‖ ≤ 4 J(b_raw) J(F) ≤ 6 J(b_raw) J(F)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- A coordinate of a meridional vector times a meridional vector. -/
theorem bEpsJet_coord_smul_le (v w : Axi.Merid) (j : Fin 2) :
    ‖v j • w‖ ≤ ‖v‖ * ‖w‖ := by
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_right (PiLp.norm_apply_le v j) (norm_nonneg _)

theorem bEpsJet_norm_le_chartJet (G : Coord → Axi.Merid) (x : Coord) :
    ‖G x‖ ≤ chartJet G x := by
  unfold chartJet
  linarith [norm_nonneg (Axi.dQ G x), norm_nonneg (Axi.dEta G x), norm_nonneg (kAge G x)]

theorem bEpsJet_dEta_le_chartJet (G : Coord → Axi.Merid) (x : Coord) :
    ‖Axi.dEta G x‖ ≤ chartJet G x := by
  unfold chartJet
  linarith [norm_nonneg (Axi.dQ G x), norm_nonneg (G x), norm_nonneg (kAge G x)]

theorem bEpsJet_qEps_le (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (G : Coord → Axi.Merid) (x : Coord) :
    ‖qEps ε G x‖ ≤ chartJet G x := by
  unfold qEps chartJet
  have h2 : ‖ε • (kAge G x + G x)‖ ≤ ‖kAge G x‖ + ‖G x‖ := by
    rw [norm_smul, Real.norm_of_nonneg h0]
    have h3 : ε * ‖kAge G x + G x‖ ≤ ‖kAge G x + G x‖ :=
      mul_le_of_le_one_left (norm_nonneg _) h1
    have h4 : ‖kAge G x + G x‖ ≤ ‖kAge G x‖ + ‖G x‖ := norm_add_le _ _
    linarith
  have h5 := norm_sub_le (Axi.dQ G x) (ε • (kAge G x + G x))
  linarith [norm_nonneg (Axi.dEta G x), norm_nonneg (G x), norm_nonneg (kAge G x),
    norm_nonneg (Axi.dQ G x)]

/-- **The interaction is bilinear in the jets** (SP 2370-2374; pure algebra from `bEps`, `qEps`,
`chartJet`): for `0 ≤ ε ≤ 1`, `‖B_εF‖ ≤ 6 J(b_raw) J(F)`. -/
theorem bEpsJet : UnforcedLeray.Short.IIb.BEpsJet := by
  intro p hε0 hε1 F x
  have hq1 := bEpsJet_qEps_le p.ε hε0 hε1 F x
  have hq2 := bEpsJet_qEps_le p.ε hε0 hε1 (rawProf p) x
  have hR := bEpsJet_norm_le_chartJet (rawProf p) x
  have hRe := bEpsJet_dEta_le_chartJet (rawProf p) x
  have hF := bEpsJet_norm_le_chartJet F x
  have hFe := bEpsJet_dEta_le_chartJet F x
  have hJr : 0 ≤ chartJet (rawProf p) x := le_trans (norm_nonneg _) hR
  have hJF : 0 ≤ chartJet F x := le_trans (norm_nonneg _) hF
  have hT1 : ‖rawProf p x 0 • qEps p.ε F x‖ ≤ chartJet (rawProf p) x * chartJet F x :=
    (bEpsJet_coord_smul_le _ _ 0).trans
      (mul_le_mul hR hq1 (norm_nonneg _) hJr)
  have hT2 : ‖rawProf p x 1 • Axi.dEta F x‖ ≤ chartJet (rawProf p) x * chartJet F x :=
    (bEpsJet_coord_smul_le _ _ 1).trans
      (mul_le_mul hR hFe (norm_nonneg _) hJr)
  have hT3 : ‖F x 0 • qEps p.ε (rawProf p) x‖ ≤ chartJet (rawProf p) x * chartJet F x :=
    (bEpsJet_coord_smul_le _ _ 0).trans
      (by
        have := mul_le_mul hF hq2 (norm_nonneg _) hJF
        linarith [mul_comm (chartJet F x) (chartJet (rawProf p) x)])
  have hT4 : ‖F x 1 • Axi.dEta (rawProf p) x‖ ≤ chartJet (rawProf p) x * chartJet F x :=
    (bEpsJet_coord_smul_le _ _ 1).trans
      (by
        have := mul_le_mul hF hRe (norm_nonneg _) hJF
        linarith [mul_comm (chartJet F x) (chartJet (rawProf p) x)])
  unfold bEps
  have hA : ‖rawProf p x 0 • qEps p.ε F x + rawProf p x 1 • Axi.dEta F x +
      (F x 0 • qEps p.ε (rawProf p) x + F x 1 • Axi.dEta (rawProf p) x)‖ ≤
      ‖rawProf p x 0 • qEps p.ε F x‖ + ‖rawProf p x 1 • Axi.dEta F x‖ +
        (‖F x 0 • qEps p.ε (rawProf p) x‖ + ‖F x 1 • Axi.dEta (rawProf p) x‖) := by
    have e1 := norm_add_le (rawProf p x 0 • qEps p.ε F x + rawProf p x 1 • Axi.dEta F x)
      (F x 0 • qEps p.ε (rawProf p) x + F x 1 • Axi.dEta (rawProf p) x)
    have e2 := norm_add_le (rawProf p x 0 • qEps p.ε F x) (rawProf p x 1 • Axi.dEta F x)
    have e3 := norm_add_le (F x 0 • qEps p.ε (rawProf p) x) (F x 1 • Axi.dEta (rawProf p) x)
    linarith
  have hP : 0 ≤ chartJet (rawProf p) x * chartJet F x := mul_nonneg hJr hJF
  linarith

end UnforcedLeray.Short.IIb

end
