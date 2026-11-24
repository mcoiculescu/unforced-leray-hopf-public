import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Sub.PartIIIb_C_near_delta_8_2_3

/-!
# `cellPtChangeAll` (item `PartIII-b:C/near/delta/8/2/3/2`)

Proves `cellPtChangeAll : CellPtChangeAll`, i.e. for every `c > 0` the three recentring identities
`Masked.CellPtHT c`, `Masked.CellPtInvH c`, `Masked.CellPtH c` (source 1641-1646, 2676-2679).

The proofs are those of `Masked/Proofs/CellPtHT.lean`, `CellPtInvH.lean` and `CellPtH.lean`, copied
here with the auxiliary declarations prefixed `cpc` so that the three duplicated names `ctT ...`
do not clash. Nothing in the `Masked/Proofs` files is edited.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Cons.C03.Concrete
  UnforcedLeray.Blueprint.Planar

/-- The recentring of one `q`-coordinate, as in `cellPt` (copied from `CellPtHT.lean`). -/
def cpcT (c q : ℝ) : ℝ := if q < c / 2 then q else q - c

theorem cpcT_measurable (c : ℝ) : Measurable (cpcT c) :=
  Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_id
    (measurable_id.sub_const c)

theorem cpc_cellPt_eq_prodMap (c : ℝ) : cellPt c = Prod.map id (Prod.map (cpcT c) id) := by
  funext p
  obtain ⟨s, q, η⟩ := p
  rfl

theorem cpc_lintegral_T {c : ℝ} (hc : 0 < c) (f : ℝ → ℝ≥0∞) :
    ∫⁻ q in Ioc (0 : ℝ) c, f (cpcT c q) = ∫⁻ q in Ico (-c / 2) (c / 2), f q := by
  have e0 : volume.restrict (Ioc (0 : ℝ) c) = volume.restrict (Ioo (0 : ℝ) c) :=
    Measure.restrict_congr_set Ioo_ae_eq_Ioc.symm
  have hsplit : Ioo (0 : ℝ) c = Ioo 0 (c / 2) ∪ Ico (c / 2) c :=
    (Ioo_union_Ico_eq_Ioo (show (0 : ℝ) < c / 2 by linarith) (show c / 2 ≤ c by linarith)).symm
  have hdL : Disjoint (Ioo (0 : ℝ) (c / 2)) (Ico (c / 2) c) :=
    Set.disjoint_left.2 fun x hx hx' => not_le.2 hx.2 hx'.1
  have hsplit' : Ico (-c / 2) (c / 2) = Ico (-c / 2) 0 ∪ Ico 0 (c / 2) :=
    (Ico_union_Ico_eq_Ico (show -c / 2 ≤ (0 : ℝ) by linarith) (show (0 : ℝ) ≤ c / 2 by linarith)).symm
  have hdR : Disjoint (Ico (-c / 2) (0 : ℝ)) (Ico (0 : ℝ) (c / 2)) := Set.Ico_disjoint_Ico_same
  have e2 : volume.restrict (Ioo (0 : ℝ) (c / 2)) = volume.restrict (Ico (0 : ℝ) (c / 2)) :=
    Measure.restrict_congr_set Ioo_ae_eq_Ico
  have hI : ∫⁻ q in Ico (c / 2) c, f (q - c) = ∫⁻ q in Ico (-c / 2) 0, f q := by
    have key : ∀ q : ℝ, (Ico (c / 2) c).indicator (fun q => f (q - c)) q =
        (Ico (-c / 2) 0).indicator f (q - c) := by
      intro q
      by_cases h : q ∈ Ico (c / 2) c
      · have h' : q - c ∈ Ico (-c / 2) 0 := ⟨by linarith [h.1], by linarith [h.2]⟩
        rw [indicator_of_mem h, indicator_of_mem h']
      · have h' : q - c ∉ Ico (-c / 2) 0 := fun h'' =>
          h ⟨by linarith [h''.1], by linarith [h''.2]⟩
        rw [indicator_of_notMem h, indicator_of_notMem h']
    calc ∫⁻ q in Ico (c / 2) c, f (q - c)
        = ∫⁻ q, (Ico (c / 2) c).indicator (fun q => f (q - c)) q :=
          (lintegral_indicator measurableSet_Ico _).symm
      _ = ∫⁻ q, (Ico (-c / 2) 0).indicator f (q - c) := lintegral_congr key
      _ = ∫⁻ q, (Ico (-c / 2) 0).indicator f q := lintegral_sub_right_eq_self _ c
      _ = ∫⁻ q in Ico (-c / 2) 0, f q := lintegral_indicator measurableSet_Ico _
  have h1 : ∫⁻ q in Ioo (0 : ℝ) (c / 2), f (cpcT c q) = ∫⁻ q in Ioo (0 : ℝ) (c / 2), f q :=
    setLIntegral_congr_fun measurableSet_Ioo fun q hq => by
      rw [cpcT, if_pos hq.2]
  have h2 : ∫⁻ q in Ico (c / 2) c, f (cpcT c q) = ∫⁻ q in Ico (c / 2) c, f (q - c) :=
    setLIntegral_congr_fun measurableSet_Ico fun q hq => by
      rw [cpcT, if_neg (not_lt.2 hq.1)]
  rw [e0, hsplit, lintegral_union measurableSet_Ico hdL, hsplit',
    lintegral_union measurableSet_Ico hdR, h1, h2, hI, e2]
  exact add_comm _ _

theorem cpc_map_T {c : ℝ} (hc : 0 < c) :
    Measure.map (cpcT c) (volume.restrict (Ioc (0 : ℝ) c)) =
      volume.restrict (Ico (-c / 2) (c / 2)) := by
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  rw [lintegral_map hf (cpcT_measurable c)]
  exact cpc_lintegral_T hc f

theorem cpc_map_cellPt {c a : ℝ} (hc : 0 < c) :
    Measure.map (cellPt c)
        ((UnforcedLeray.B0220.cellMeasure c).withDensity fun p => ENNReal.ofReal (p.1 ^ a)) =
      ENNReal.ofReal c • ageμ c a := by
  have hcell : (UnforcedLeray.B0220.cellMeasure c).withDensity (fun p => ENNReal.ofReal (p.1 ^ a)) =
      ((volume.restrict (Ioi (0 : ℝ))).withDensity fun s => ENNReal.ofReal (s ^ a)).prod
        ((volume.restrict (Ioc (0 : ℝ) c)).prod volume) := by
    rw [prod_withDensity_left (measurable_ofReal_rpow a)]
    congr 1
    rw [UnforcedLeray.B0220.cellMeasure, UnforcedLeray.B0220.cell, Measure.volume_eq_prod,
      Measure.volume_eq_prod, ← Measure.prod_restrict, ← Measure.prod_restrict,
      Measure.restrict_univ]
  have hq2 : (volume.restrict (Ico (-c / 2) (c / 2))).prod (volume : Measure ℝ) =
      volume.restrict (Ico (-c / 2) (c / 2) ×ˢ (univ : Set ℝ)) := by
    have h := Measure.prod_restrict (Ico (-c / 2) (c / 2)) (univ : Set ℝ)
      (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    rw [Measure.restrict_univ, ← Measure.volume_eq_prod] at h
    exact h
  have hmain : Measure.map (cellPt c)
      (((volume.restrict (Ioi (0 : ℝ))).withDensity fun s => ENNReal.ofReal (s ^ a)).prod
        ((volume.restrict (Ioc (0 : ℝ) c)).prod volume)) =
      ((volume.restrict (Ioi (0 : ℝ))).withDensity fun s => ENNReal.ofReal (s ^ a)).prod
        (volume.restrict (Ico (-c / 2) (c / 2) ×ˢ (univ : Set ℝ))) := by
    rw [cpc_cellPt_eq_prodMap, ← Measure.map_prod_map _ _ measurable_id
        ((cpcT_measurable c).prodMap measurable_id), Measure.map_id,
      ← Measure.map_prod_map _ _ (cpcT_measurable c) measurable_id, Measure.map_id,
      cpc_map_T hc, hq2]
  have hR : ENNReal.ofReal c • ageμ c a =
      ((volume.restrict (Ioi (0 : ℝ))).withDensity fun s => ENNReal.ofReal (s ^ a)).prod
        (volume.restrict (Ico (-c / 2) (c / 2) ×ˢ (univ : Set ℝ))) := by
    rw [ageμ, UnforcedLeray.Cyl.avgμ, UnforcedLeray.Cyl.cellμ, UnforcedLeray.Cyl.cell,
      Measure.prod_smul_right, smul_smul, ← ENNReal.ofReal_mul hc.le, mul_inv_cancel₀ hc.ne',
      ENNReal.ofReal_one, one_smul]
  rw [hcell, hmain, hR]

/-- `CellPtHT` at `c` (copied from `CellPtHT.lean`). -/
theorem cpcHT_eq (c : ℝ) (hc : 0 < c) : CellPtHT c := by
  show Measure.map (cellPt c) (UnforcedLeray.Short.PartIIa.measureHT c) =
    ENNReal.ofReal c • ageμ c (-1 / 2)
  have ha : (-1 / 2 : ℝ) = -(1 / 2) := by norm_num
  rw [UnforcedLeray.Short.PartIIa.measureHT, ha]
  exact cpc_map_cellPt hc

/-- The velocity identity `map cellPt (measureH c) = c • ageμ c (-3/2)` (copied from `CellPtH.lean`). -/
theorem cpcH_eq (c : ℝ) (hc : 0 < c) : CellPtH c := by
  show Measure.map (cellPt c) (UnforcedLeray.B0220.measureH c) =
    ENNReal.ofReal c • ageμ c (-3 / 2)
  have ha : (-3 / 2 : ℝ) = -(3 / 2) := by norm_num
  rw [UnforcedLeray.B0220.measureH, ha]
  exact cpc_map_cellPt hc

/-- The velocity identity used for `CellPtInvH` (copied from `CellPtInvH.lean`). -/
theorem cpcH_aux (c : ℝ) (hc : 0 < c) :
    Measure.map (cellPt c) (UnforcedLeray.B0220.measureH c) = ENNReal.ofReal c • ageμ c (-3 / 2) :=
  cpcH_eq c hc

/-- `CellPtInvH` at `c` (copied from `CellPtInvH.lean`). -/
theorem cpcInvH_eq (c : ℝ) (hc : 0 < c) : CellPtInvH c := by
  show Measure.map (cellPtInv c) (ageμ c (-3 / 2)) =
    ENNReal.ofReal c⁻¹ • UnforcedLeray.B0220.measureH c
  have hA : ageμ c (-3 / 2) = ENNReal.ofReal c⁻¹ •
      Measure.map (cellPt c) (UnforcedLeray.B0220.measureH c) := by
    rw [cpcH_aux c hc, smul_smul, ← ENNReal.ofReal_mul (inv_nonneg.2 hc.le),
      inv_mul_cancel₀ hc.ne', ENNReal.ofReal_one, one_smul]
  have hae : (cellPtInv c ∘ cellPt c) =ᵐ[UnforcedLeray.B0220.measureH c] id := by
    filter_upwards [ae_mem_cell_H c] with p hp
    simp only [Function.comp_apply, id]
    exact cellPtInv_cellPt hp.2.1.1 hp.2.1.2
  rw [hA, Measure.map_smul, Measure.map_map (measurable_cellPtInv c) (measurable_cellPt c),
    Measure.map_congr hae, Measure.map_id]

end UnforcedLeray.Short.PartIIIb.NearInst.Masked

namespace UnforcedLeray.Short.PartIIIb.NearInst.Delta

open UnforcedLeray.Short.PartIIIb.NearInst.Masked

/-- **`CellPtChangeAll`**: the three recentring identities hold for every `c > 0`. -/
theorem cellPtChangeAll : CellPtChangeAll := by
  intro c hc
  exact ⟨cpcHT_eq c hc, cpcInvH_eq c hc, cpcH_eq c hc⟩

end UnforcedLeray.Short.PartIIIb.NearInst.Delta
