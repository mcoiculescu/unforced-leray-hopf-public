import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_data_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_data_1.GaussProfPtCont
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_data_1.GaussPointBound
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_data_1.GaussMeasurable
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_data_1.PeriodizePointBound
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_data_1.PeriodizeMeas
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_data_1.WeightedL2Gauss
import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Pair.Proofs.ContinuousToLpOfDominated
import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Space

/-!


Source `the November 2 reference manuscript`
lines 4352-4356 and 4565.

Route: for fixed `S`, the family `s ↦ P_{s} := periodizeC c (profile (srcA ν (min s S)))` is
continuous into `L²(cellMeasure)` by `continuousToLpOfDominated`, with the dominating function
`|D| exp(-|x|²/(16 A_S))`, `A_S = srcA ν S`, which is `MemLp 2` by `weightedL2Gauss`; the
domination on the cell comes from `periodizePointBound`, the pointwise continuity in `s` from
`gaussProfPtCont`.  Since `F s =ᵐ P_s` for each `s`, `F (min s S)` equals the `L²` family, and
`F` is continuous near each `t` by taking `S = t + 1`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- The cell is contained in `|x₁| ≤ c/2`. -/
theorem gsc_cell_abs (c : ℝ) (x : ℝ × ℝ) (hx : x ∈ B0579.cell c) : |x.1| ≤ c / 2 := by
  have hx' : x.1 ∈ Ico (-(c / 2)) (c / 2) := (Set.mem_prod.1 hx).1
  exact abs_le.2 ⟨hx'.1, hx'.2.le⟩

/-- Generic form of `GaussSrcContinuous` for one profile family `P` (with `P a = hMode a` or
`rMode a`). -/
theorem gsc_helper (ν m : ℝ) (hν : 0 < ν) (P : ℝ → ℝ × ℝ → ℂ)
    (hPm : ∀ a, Measurable (P a))
    (hPb : ∀ A : ℝ, 1 ≤ A → ∃ C : ℝ, ∀ a ∈ Icc (1 : ℝ) A, ∀ x : ℝ × ℝ,
      ‖P a x‖ ≤ C * (1 + x.1 ^ 2 + x.2 ^ 2) ^ 2 * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (4 * A)))
    (hPc : ∀ x : ℝ × ℝ, Continuous (fun s => IIIa.periodizeC (cOf ν) (P (srcA ν s)) x)) :
    ∀ F : ℝ → XAmb (cOf ν) m,
      (∀ s, (F s : ℝ × ℝ → ℂ) =ᵐ[B0579.cellMeasure (cOf ν) m]
          IIIa.periodizeC (cOf ν) (P (srcA ν s))) → Continuous F := by
  intro F hFae
  have hc : 0 < cOf ν := by unfold cOf; positivity
  have hcm : MeasurableSet (B0579.cell (cOf ν)) := by
    unfold B0579.cell
    exact measurableSet_Ico.prod MeasurableSet.univ
  have hcontS : ∀ S : ℝ, Continuous (fun s => F (min s S)) := by
    intro S
    have hAS : 1 ≤ srcA ν S := srcA_ge_one ν hν S
    have hA0 : 0 < srcA ν S := lt_of_lt_of_le one_pos hAS
    obtain ⟨C, hC⟩ := hPb (srcA ν S) hAS
    obtain ⟨Cl, hCl⟩ := periodizeL2Bound_of periodizePointBound weightedL2Gauss periodizeMeas
      m (srcA ν S) (cOf ν) hA0 hc
    obtain ⟨Cpp, hCpp⟩ := periodizePointBound (srcA ν S) (cOf ν) hA0 hc
    -- the bound for the profile at a time `min s S`
    have hbd : ∀ s : ℝ, ∀ x : ℝ × ℝ,
        ‖P (srcA ν (min s S)) x‖ ≤
          C * (1 + x.1 ^ 2 + x.2 ^ 2) ^ 2 * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (4 * srcA ν S)) :=
      fun s x => hC _ ⟨srcA_ge_one ν hν _, srcA_mono ν hν (min_le_right s S)⟩ x
    have hmemHs : ∀ s : ℝ, MemLp (IIIa.periodizeC (cOf ν) (P (srcA ν (min s S)))) 2
        (B0579.cellMeasure (cOf ν) m) := by
      intro s
      obtain ⟨h1, h2⟩ := hCl (cOf ν) le_rfl (P (srcA ν (min s S))) C (hPm _) (hbd s)
      exact ⟨h1, lt_of_le_of_lt h2 ENNReal.ofReal_lt_top⟩
    -- the dominating function
    set gfun : ℝ × ℝ → ℝ := fun x =>
      |Cpp * C| * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (16 * srcA ν S)) with hgfun
    have hgcont : Continuous gfun := by
      rw [hgfun]; fun_prop
    have hcplx_cont : Continuous (fun x : ℝ × ℝ => ((gfun x : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp hgcont
    have hbdC : ∀ x : ℝ × ℝ, |x.1| ≤ cOf ν / 2 →
        ‖((gfun x : ℝ) : ℂ)‖ ≤ |Cpp * C| * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (16 * srcA ν S)) := by
      intro x _
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by rw [hgfun]; positivity)]
    obtain ⟨Cw, hCw⟩ := weightedL2Gauss m (srcA ν S) hA0
    have hwl := hCw (cOf ν) hc (fun x : ℝ × ℝ => ((gfun x : ℝ) : ℂ)) (|Cpp * C|)
      hcplx_cont.aestronglyMeasurable hbdC
    have hgM : MemLp gfun 2 (B0579.cellMeasure (cOf ν) m) := by
      have hh : MemLp (fun x : ℝ × ℝ => ((gfun x : ℝ) : ℂ)) 2 (B0579.cellMeasure (cOf ν) m) :=
        ⟨hcplx_cont.aestronglyMeasurable, lt_of_le_of_lt hwl ENNReal.ofReal_lt_top⟩
      have := hh.re
      convert this using 1
      funext x
      simp
    -- domination on the cell, transferred to `cellMeasure`
    have hdom : ∀ s : ℝ, ∀ᵐ x ∂(B0579.cellMeasure (cOf ν) m),
        ‖IIIa.periodizeC (cOf ν) (P (srcA ν (min s S))) x‖ ≤ gfun x := by
      intro s
      apply ae_cellMeasure_of_ae_cell
      refine (ae_restrict_mem hcm).mono fun x hx => ?_
      have h1 := hCpp (cOf ν) le_rfl (P (srcA ν (min s S))) C (hbd s) x (gsc_cell_abs _ x hx)
      have h2 : Cpp * C * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (16 * srcA ν S)) ≤
          |Cpp * C| * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (16 * srcA ν S)) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le
      exact le_trans h1 h2
    -- the `L²` family and its continuity
    have hcs : ∀ x : ℝ × ℝ, Continuous fun s => IIIa.periodizeC (cOf ν) (P (srcA ν (min s S))) x :=
      fun x => (hPc x).comp (continuous_id.min continuous_const)
    have hcae : ∀ᵐ x ∂(B0579.cellMeasure (cOf ν) m),
        Continuous fun s => IIIa.periodizeC (cOf ν) (P (srcA ν (min s S))) x :=
      ae_of_all _ hcs
    have hLp := Pair.continuousToLpOfDominated (B0579.cellMeasure (cOf ν) m)
      (fun s => IIIa.periodizeC (cOf ν) (P (srcA ν (min s S))))
      hmemHs gfun hgM hdom hcae
    have hEq : ∀ s : ℝ, (hmemHs s).toLp (IIIa.periodizeC (cOf ν) (P (srcA ν (min s S))))
        = F (min s S) := by
      intro s
      rw [MemLp.toLp_congr (hmemHs s) (Lp.memLp (F (min s S))) (hFae (min s S)).symm]
      exact Lp.toLp_coeFn _ _
    have hfun : (fun s => F (min s S)) =
        fun s => (hmemHs s).toLp (IIIa.periodizeC (cOf ν) (P (srcA ν (min s S)))) :=
      funext fun s => (hEq s).symm
    rw [hfun]
    exact hLp
  rw [continuous_iff_continuousAt]
  intro t
  have h1 := (hcontS (t + 1)).continuousAt (x := t)
  refine h1.congr ?_
  have hev : ∀ᶠ s in 𝓝 t, s < t + 1 := Iio_mem_nhds (by linarith)
  refine hev.mono fun s hs => ?_
  show F (min s (t + 1)) = F s
  rw [min_eq_left hs.le]

theorem gaussSrcContinuous_of : GaussSrcContinuous := by
  intro ν m hν
  have hbdH : ∀ A : ℝ, 1 ≤ A → ∃ C : ℝ, ∀ a ∈ Icc (1 : ℝ) A, ∀ x : ℝ × ℝ,
      ‖hMode a x‖ ≤ C * (1 + x.1 ^ 2 + x.2 ^ 2) ^ 2 * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (4 * A)) := by
    intro A hA
    obtain ⟨C, hC⟩ := gaussPointBound A hA
    exact ⟨C, fun a ha x => (hC a ha x).1⟩
  have hbdR : ∀ A : ℝ, 1 ≤ A → ∃ C : ℝ, ∀ a ∈ Icc (1 : ℝ) A, ∀ x : ℝ × ℝ,
      ‖rMode a x‖ ≤ C * (1 + x.1 ^ 2 + x.2 ^ 2) ^ 2 * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (4 * A)) := by
    intro A hA
    obtain ⟨C, hC⟩ := gaussPointBound A hA
    exact ⟨C, fun a ha x => (hC a ha x).2⟩
  have hcH : ∀ x : ℝ × ℝ, Continuous (fun s => IIIa.periodizeC (cOf ν) (hMode (srcA ν s)) x) :=
    fun x => (gaussProfPtCont ν hν x).1
  have hcR : ∀ x : ℝ × ℝ, Continuous (fun s => IIIa.periodizeC (cOf ν) (rMode (srcA ν s)) x) :=
    fun x => (gaussProfPtCont ν hν x).2
  exact ⟨gsc_helper ν m hν hMode (fun a => (gaussMeasurable a).1) hbdH hcH,
    gsc_helper ν m hν rMode (fun a => (gaussMeasurable a).2) hbdR hcR⟩

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
