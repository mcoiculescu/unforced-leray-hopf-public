import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_18_3_4
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Proofs.DB.FullOutMeas
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Proofs.DB.FullOutLip

/-!
# `FullOutMemH` (`PartIII-b:C/near/masked/18/3/4/1`, source 3916-3921, 1688-1689)

For a box test `m` the chart field `merC (fullOut ε⁻¹ c ν μ m (cellPt c p))` lies in `H`.
Route: `fullOutLip` with `g = 0` (the zero tensor has `fullOut = 0`) bounds the `L²(s^{-3/2})`
norm of `fullOut m` by `tv4 m` in `L²(s^{-1/2})`, which is finite since `m` is a box tensor
(`skr_memLp_box`); `fullOutMeas` gives measurability; the transport `CellPtH` moves the
`ageμ c (-3/2)` integrability to `measureH c`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Short.PartIIIb.NearInst.Masked

theorem fullOutMemH_nsSym_zero : nsSym (0 : Ten3) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [nsSym, symRZ]

theorem fullOutMemH_fullOut_zero (R c ν μ : ℝ) (x : Chart) :
    fullOut R c ν μ (0 : Chart → Ten3) x = 0 := by
  have hc : cartLift R c (0 : Chart → Ten3) = fun _ _ => (0 : Matrix (Fin 3) (Fin 3) ℝ) := by
    funext τ z
    simp [cartLift, fullOutMemH_nsSym_zero]
  unfold fullOut
  rw [hc]
  simp [UnforcedLeray.Short.IIIa.sepW, merRe]

theorem fullOutMemH_tv4_zero : tv4 (0 : Ten3) = 0 := by
  rw [← tv4L_apply]
  exact map_zero tv4L

theorem fullOutMemH_box_zero : IsBoxTensor (0 : Chart → Ten3) :=
  ⟨measurable_zero, ⟨0, fun p => by simp⟩, ⟨1, 1, 0, one_pos, fun p hp => (hp rfl).elim⟩⟩

theorem fullOutMemH : FullOutMemH := by
  intro ν ε c hν hε hc μ hμ m _ hbox
  have hR : 0 < ε⁻¹ := inv_pos.2 hε
  obtain ⟨-, -, hCH⟩ := UnforcedLeray.Short.PartIIIb.NearInst.Delta.cellPtChangeAll c hc
  have hmap : Measure.map (cellPt c) (UnforcedLeray.B0220.measureH c) =
      ENNReal.ofReal c • ageμ c (-3 / 2) := hCH
  obtain ⟨C, -, hCl⟩ := fullOutLip ε⁻¹ c ν μ hR hc hν hμ
  -- the test is in `L²(s^{-1/2})`
  have hbx : MemLp (fun x => tv4 (m x)) 2 (ageμ c (-1 / 2)) := by
    have h := tv4L.comp_memLp' (skr_memLp_box (c := c) hbox)
    exact h
  -- the bound of `fullOut m` in `L²(s^{-3/2})`, using `fullOut 0 = 0`
  have hbound := hCl m 0 hbox fullOutMemH_box_zero
  simp only [Pi.zero_apply, fullOutMemH_fullOut_zero, sub_zero, fullOutMemH_tv4_zero] at hbound
  have hL : eLpNorm (fun x => fullOut ε⁻¹ c ν μ m x) 2 (ageμ c (-3 / 2)) < ∞ :=
    lt_of_le_of_lt hbound (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hbx.eLpNorm_lt_top)
  -- the lifted chart field in `L²(s^{-3/2})`
  have hmeas : AEStronglyMeasurable (fun x => merC (fullOut ε⁻¹ c ν μ m x))
      (ageμ c (-3 / 2)) :=
    continuous_merC'.comp_aestronglyMeasurable (fullOutMeas ε⁻¹ c ν μ hR hc hν hμ m hbox)
  have he : eLpNorm (fun x => merC (fullOut ε⁻¹ c ν μ m x)) 2 (ageμ c (-3 / 2)) =
      eLpNorm (fun x => fullOut ε⁻¹ c ν μ m x) 2 (ageμ c (-3 / 2)) :=
    eLpNorm_congr_norm_ae (Filter.Eventually.of_forall fun x => norm_merC' _)
  have hmem1 : MemLp (fun x => merC (fullOut ε⁻¹ c ν μ m x)) 2 (ageμ c (-3 / 2)) :=
    ⟨hmeas, by rw [he]; exact hL⟩
  -- transport to `measureH c` through `cellPt`
  have h1 : MemLp (fun x => merC (fullOut ε⁻¹ c ν μ m x)) 2
      (Measure.map (cellPt c) (UnforcedLeray.B0220.measureH c)) := by
    rw [hmap]
    exact hmem1.smul_measure ENNReal.ofReal_ne_top
  have hMem : MemLp (fun p => merC (fullOut ε⁻¹ c ν μ m (cellPt c p))) 2
      (UnforcedLeray.B0220.measureH c) :=
    (memLp_map_measure_iff h1.aestronglyMeasurable
      (measurable_cellPt c).aemeasurable).1 h1
  refine ⟨hMem.toLp _, ?_⟩
  exact hMem.coeFn_toLp

end UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization
