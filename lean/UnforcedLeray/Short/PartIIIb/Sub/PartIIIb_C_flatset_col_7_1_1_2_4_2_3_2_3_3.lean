import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_3_2_3_3.DivReIm

/-!
# `PepsC0SliceOrthCell`

Source `the November 2 reference manuscript`
1650-1656, 1676.  The periodic fields `Φs, Ψs` and the periodic extension `w` of `v` are `L²` on the
centred cell; `Re w, Im w ∈ Cyl.divFree c` (`reim_mem_divFree`); the four real pairings
`⟨Re/Im w, Re/Im Φs - 𝒫₀ Re/Im Φs⟩` vanish (`pair_zero`); the strip integral is the cell integral.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal InnerProductSpace

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.Short.IIIa (toL2v reVec imVec P0C cplxOf P0re P0im)

theorem orth_alg (z y : ℂ) (A B : ℝ) :
    (starRingEnd ℂ) (z - ((A : ℂ) + Complex.I * (B : ℂ))) * y =
      (((z.re - A) * y.re + (z.im - B) * y.im : ℝ) : ℂ) +
        Complex.I * (((z.re - A) * y.im - (z.im - B) * y.re : ℝ) : ℂ) := by
  apply Complex.ext <;> simp <;> ring

/-- The `i`-th component of `𝒫₀` applied to the class of a real field. -/
def Pr (c : ℝ) (F : ℝ × ℝ → UnforcedLeray.Cyl.Vec2) (x : ℝ × ℝ) (i : Fin 2) : ℝ :=
  (UnforcedLeray.Cyl.P0 c (toL2v c F) : ℝ × ℝ → UnforcedLeray.Cyl.Vec2) x i

theorem pepsC0SliceOrthCell : PepsC0SliceOrthCell := by
  intro c hc Φs Ψs v hΦp hΨp hΦ hΨ hv hΨP hdiv
  -- periodic extension of `v`
  obtain ⟨w, hwp, hwae, hwL⟩ := periodic_extension_L2 hc v hv
  -- cell integrability of `Φs`
  have cellMem : ∀ F : ℝ × ℝ → Fin 2 → ℂ, (∀ q η, F (q + c, η) = F (q, η)) →
      MemLp (fun x => toMC (F x)) 2 (volume.restrict (stripSet c)) →
      MemLp (fun x => toMC (F x)) 2 (UnforcedLeray.Cyl.cellμ c) := by
    intro F hF hFL
    obtain ⟨wF, hwFp, hwFae, hwFL⟩ := periodic_extension_L2 hc F hFL
    have h1 : F =ᵐ[volume] wF :=
      ae_vol_of_strip hc (fun z => hF z.1 z.2) (fun z => hwFp z.1 z.2)
        (hwFae.mono fun x hx => hx.symm)
    have h2 : (fun x => toMC (F x)) =ᵐ[UnforcedLeray.Cyl.cellμ c] fun x => toMC (wF x) :=
      ae_restrict_of_ae (h1.mono fun x hx => by simp only [hx])
    exact hwFL.ae_eq h2.symm
  have hΦc := cellMem Φs hΦp hΦ
  obtain ⟨hΦre, hΦim⟩ := memLp_reVec_imVec hΦc
  obtain ⟨hwre, hwim⟩ := memLp_reVec_imVec hwL
  -- the weak divergence of `w`
  have hdivw : ∀ ψ : ℝ × ℝ → ℝ, UnforcedLeray.B0579.IsCylTest c ψ →
      ∫ x in stripSet c, (w x 0 * (UnforcedLeray.B0579.pd 0 ψ x : ℂ) +
        w x 1 * (UnforcedLeray.B0579.pd 1 ψ x : ℂ)) = 0 := by
    intro ψ hψ
    rw [← hdiv ψ hψ]
    exact integral_congr_ae (hwae.mono fun x hx => by simp only [hx])
  obtain ⟨hgre, hgim⟩ := reim_mem_divFree hc w hwp hwL hdivw
  -- the four real pairings
  obtain ⟨i1, z1⟩ := pair_zero c (reVec Φs) (reVec w) hΦre hwre hgre
  obtain ⟨i2, z2⟩ := pair_zero c (imVec Φs) (imVec w) hΦim hwim hgim
  obtain ⟨i3, z3⟩ := pair_zero c (reVec Φs) (imVec w) hΦre hwim hgim
  obtain ⟨i4, z4⟩ := pair_zero c (imVec Φs) (reVec w) hΦim hwre hgre
  -- strip to cell
  have hperT : UnforcedLeray.Cyl.IsPeriodic c (fun x : ℝ × ℝ =>
      ∑ i : Fin 2, (starRingEnd ℂ) (Φs x i - Ψs x i) * w x i) := by
    intro z
    show ∑ i : Fin 2, (starRingEnd ℂ) (Φs (z.1 + c, z.2) i - Ψs (z.1 + c, z.2) i) *
      w (z.1 + c, z.2) i = _
    rw [hΦp z.1 z.2, hΨp z.1 z.2, hwp z.1 z.2]
  have hS : ∫ x in stripSet c, ∑ i : Fin 2, (starRingEnd ℂ) (Φs x i - Ψs x i) * v x i =
      ∫ x in stripSet c, ∑ i : Fin 2, (starRingEnd ℂ) (Φs x i - Ψs x i) * w x i :=
    integral_congr_ae (hwae.mono fun x hx => by simp only [hx])
  rw [hS]
  have hcell : ∫ x in stripSet c, ∑ i : Fin 2, (starRingEnd ℂ) (Φs x i - Ψs x i) * w x i =
      ∫ x, ∑ i : Fin 2, (starRingEnd ℂ) (Φs x i - Ψs x i) * w x i
        ∂(UnforcedLeray.Cyl.cellμ c) :=
    UnforcedLeray.B0224.integral_strip_eq_cell hc hperT
  rw [hcell]
  -- replace `Ψs` by `P0C Φs`
  have hae : (fun x : ℝ × ℝ => ∑ i : Fin 2, (starRingEnd ℂ) (Φs x i - Ψs x i) * w x i)
      =ᵐ[UnforcedLeray.Cyl.cellμ c] fun x =>
        ∑ i : Fin 2, (starRingEnd ℂ) (Φs x i - P0C c Φs x i) * w x i :=
    hΨP.mono fun x hx => by simp only [hx]
  rw [integral_congr_ae hae]
  have hpt : ∀ x : ℝ × ℝ, ∑ i : Fin 2, (starRingEnd ℂ) (Φs x i - P0C c Φs x i) * w x i =
      ((∑ i : Fin 2, (reVec Φs x i - Pr c (reVec Φs) x i) * reVec w x i : ℝ) : ℂ) +
      ((∑ i : Fin 2, (imVec Φs x i - Pr c (imVec Φs) x i) * imVec w x i : ℝ) : ℂ) +
      Complex.I * (((∑ i : Fin 2, (reVec Φs x i - Pr c (reVec Φs) x i) * imVec w x i : ℝ) : ℂ) -
        ((∑ i : Fin 2, (imVec Φs x i - Pr c (imVec Φs) x i) * reVec w x i : ℝ) : ℂ)) := by
    intro x
    have e0 := orth_alg (Φs x 0) (w x 0) (Pr c (reVec Φs) x 0) (Pr c (imVec Φs) x 0)
    have e1 := orth_alg (Φs x 1) (w x 1) (Pr c (reVec Φs) x 1) (Pr c (imVec Φs) x 1)
    simp only [Fin.sum_univ_two, P0C, cplxOf, P0re, P0im,
      UnforcedLeray.Short.IIIa.reVec_apply_p0orth, UnforcedLeray.Short.IIIa.imVec_apply_p0orth]
    change (starRingEnd ℂ) (Φs x 0 - (((Pr c (reVec Φs) x 0 : ℝ) : ℂ) + Complex.I *
        ((Pr c (imVec Φs) x 0 : ℝ) : ℂ))) * w x 0 +
      (starRingEnd ℂ) (Φs x 1 - (((Pr c (reVec Φs) x 1 : ℝ) : ℂ) + Complex.I *
        ((Pr c (imVec Φs) x 1 : ℝ) : ℂ))) * w x 1 = _
    rw [e0, e1]
    push_cast
    ring
  rw [integral_congr_ae (Eventually.of_forall hpt)]
  have j1 : Integrable (fun x : ℝ × ℝ => ∑ i : Fin 2, (reVec Φs x i - Pr c (reVec Φs) x i) *
      reVec w x i) (UnforcedLeray.Cyl.cellμ c) := i1
  have j2 : Integrable (fun x : ℝ × ℝ => ∑ i : Fin 2, (imVec Φs x i - Pr c (imVec Φs) x i) *
      imVec w x i) (UnforcedLeray.Cyl.cellμ c) := i2
  have j3 : Integrable (fun x : ℝ × ℝ => ∑ i : Fin 2, (reVec Φs x i - Pr c (reVec Φs) x i) *
      imVec w x i) (UnforcedLeray.Cyl.cellμ c) := i3
  have j4 : Integrable (fun x : ℝ × ℝ => ∑ i : Fin 2, (imVec Φs x i - Pr c (imVec Φs) x i) *
      reVec w x i) (UnforcedLeray.Cyl.cellμ c) := i4
  have y1 : ∫ x, ∑ i : Fin 2, (reVec Φs x i - Pr c (reVec Φs) x i) * reVec w x i
      ∂(UnforcedLeray.Cyl.cellμ c) = 0 := z1
  have y2 : ∫ x, ∑ i : Fin 2, (imVec Φs x i - Pr c (imVec Φs) x i) * imVec w x i
      ∂(UnforcedLeray.Cyl.cellμ c) = 0 := z2
  have y3 : ∫ x, ∑ i : Fin 2, (reVec Φs x i - Pr c (reVec Φs) x i) * imVec w x i
      ∂(UnforcedLeray.Cyl.cellμ c) = 0 := z3
  have y4 : ∫ x, ∑ i : Fin 2, (imVec Φs x i - Pr c (imVec Φs) x i) * reVec w x i
      ∂(UnforcedLeray.Cyl.cellμ c) = 0 := z4
  rw [integral_add (j1.ofReal.add j2.ofReal) ((j3.ofReal.sub j4.ofReal).const_mul _),
    integral_add j1.ofReal j2.ofReal, integral_const_mul, integral_sub j3.ofReal j4.ofReal]
  simp only [integral_complex_ofReal, y1, y2, y3, y4]
  simp

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
