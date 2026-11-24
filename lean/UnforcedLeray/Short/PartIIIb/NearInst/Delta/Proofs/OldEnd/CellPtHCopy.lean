import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Lemmas

/-!
# `cellPtH_eq`: the recentring carries the velocity measure to `c · ageμ c (-3/2)` (source 2676-2679)

Proves `cellPtH_eq : CellPtH c`, i.e. `map (cellPt c) (measureH c) = c • ageμ c (-3/2)`.

Route. The cell measure is the product `ds ⊗ (dq|_{(0,c]}) ⊗ dη`, and `cellPt` is the product map
`id × (ctT c × id)`, where `ctT c q = q` for `q < c/2` and `ctT c q = q - c` otherwise.  Push-forward
commutes with products (`Measure.map_prod_map`), and `ctT c` pushes `dq|_{(0,c]}` to Lebesgue measure
on `[-c/2, c/2)` (`ct_map_T`, via the `q`-integral split at `c/2`, one translation by `c`, and the
endpoint changes `Ioo ~ Ico`).  The right-hand side is the same product with the normalised cell.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked.OldEndH

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Short.PartIIIb.NearInst.Delta
  UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint.Planar

/-- The recentring of one `q`-coordinate, as in `cellPt`. -/
def ctT (c q : ℝ) : ℝ := if q < c / 2 then q else q - c

theorem ctT_measurable (c : ℝ) : Measurable (ctT c) :=
  Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_id
    (measurable_id.sub_const c)

theorem cellPt_eq_prodMap (c : ℝ) : cellPt c = Prod.map id (Prod.map (ctT c) id) := by
  funext p
  obtain ⟨s, q, η⟩ := p
  rfl

/-- The one-dimensional change of variables: `ctT c` carries `dq` on `(0,c]` to `dq` on `[-c/2,c/2)`
(integral form). -/
theorem ct_lintegral_T {c : ℝ} (hc : 0 < c) (f : ℝ → ℝ≥0∞) :
    ∫⁻ q in Ioc (0 : ℝ) c, f (ctT c q) = ∫⁻ q in Ico (-c / 2) (c / 2), f q := by
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
  have h1 : ∫⁻ q in Ioo (0 : ℝ) (c / 2), f (ctT c q) = ∫⁻ q in Ioo (0 : ℝ) (c / 2), f q :=
    setLIntegral_congr_fun measurableSet_Ioo fun q hq => by
      rw [ctT, if_pos hq.2]
  have h2 : ∫⁻ q in Ico (c / 2) c, f (ctT c q) = ∫⁻ q in Ico (c / 2) c, f (q - c) :=
    setLIntegral_congr_fun measurableSet_Ico fun q hq => by
      rw [ctT, if_neg (not_lt.2 hq.1)]
  rw [e0, hsplit, lintegral_union measurableSet_Ico hdL, hsplit',
    lintegral_union measurableSet_Ico hdR, h1, h2, hI, e2]
  exact add_comm _ _

/-- The push-forward of `dq|_{(0,c]}` under `ctT c` is `dq|_{[-c/2,c/2)}`. -/
theorem ct_map_T {c : ℝ} (hc : 0 < c) :
    Measure.map (ctT c) (volume.restrict (Ioc (0 : ℝ) c)) =
      volume.restrict (Ico (-c / 2) (c / 2)) := by
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  rw [lintegral_map hf (ctT_measurable c)]
  exact ct_lintegral_T hc f

/-- The general form: pushing the cell measure with a weight `s^a` in `s` to `c • ageμ c a`. -/
theorem ct_map_cellPt {c a : ℝ} (hc : 0 < c) :
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
    rw [cellPt_eq_prodMap, ← Measure.map_prod_map _ _ measurable_id
        ((ctT_measurable c).prodMap measurable_id), Measure.map_id,
      ← Measure.map_prod_map _ _ (ctT_measurable c) measurable_id, Measure.map_id,
      ct_map_T hc, hq2]
  have hR : ENNReal.ofReal c • ageμ c a =
      ((volume.restrict (Ioi (0 : ℝ))).withDensity fun s => ENNReal.ofReal (s ^ a)).prod
        (volume.restrict (Ico (-c / 2) (c / 2) ×ˢ (univ : Set ℝ))) := by
    rw [ageμ, UnforcedLeray.Cyl.avgμ, UnforcedLeray.Cyl.cellμ, UnforcedLeray.Cyl.cell,
      Measure.prod_smul_right, smul_smul, ← ENNReal.ofReal_mul hc.le, mul_inv_cancel₀ hc.ne',
      ENNReal.ofReal_one, one_smul]
  rw [hcell, hmain, hR]

/-- **`cellPtH_eq`** (source 2676-2679): the recentring `cellPt` carries the velocity measure
`s^{-3/2} ds dq dη` on the cell to `c · ageμ c (-3/2)`. -/
theorem cellPtH_eq (c : ℝ) (hc : 0 < c) : CellPtH c := by
  show Measure.map (cellPt c) (UnforcedLeray.B0220.measureH c) =
    ENNReal.ofReal c • ageμ c (-3 / 2)
  have ha : (-3 / 2 : ℝ) = -(3 / 2) := by norm_num
  rw [UnforcedLeray.B0220.measureH, ha]
  exact ct_map_cellPt hc

end UnforcedLeray.Short.PartIIIb.NearInst.Masked.OldEndH
