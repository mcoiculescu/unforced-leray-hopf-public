import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_4_1_Fields
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletSourcePtw.Fields.InletJointSmooth
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.AbsPhaseIBP

/-!
# Part II-b, task `PartII-b:G4/4/1/1/5` (`InletSourceIBP`)

Source of record: `the November 2 reference manuscript`, lines 2355-2383.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint UnforcedLeray.PhaseSpace
  UnforcedLeray.B0411 UnforcedLeray.B0412 UnforcedLeray.Axi

private theorem ibp_inlet_periodic (p : Params) (i : Fin 2) (τ : ℝ) (y : Space) :
    p.inlet i (τ + p.period) y = p.inlet i τ y := by
  have hR : p.R ≠ 0 := p.R_pos.ne'
  have hch : Axi.chart p.R (τ + p.period) y =
      (Axi.age p.R y, (Axi.phase p.R τ y + p.c, Axi.trans p.R y)) := by
    simp only [Axi.chart, Axi.phase, p.period_eq]
    refine Prod.ext rfl (Prod.ext ?_ rfl)
    show p.R * (τ + 2 * p.c / p.R) / 2 - p.R / 2 * Real.log (Axi.age p.R y) =
      p.R * τ / 2 - p.R / 2 * Real.log (Axi.age p.R y) + p.c
    field_simp
    ring
  unfold Params.inlet Axi.Nv
  rw [hch, p.inletProfile_periodic i]
  rfl

private theorem ibp_space_sum_single (v : Space) :
    v = ∑ k : Fin 3, v k • EuclideanSpace.single k (1 : ℝ) := by
  ext j
  fin_cases j <;> simp [Fin.sum_univ_three]

private theorem ibp_advT_Efun_Ufun {p : Params}
    (hRaw : ContDiff ℝ ∞ (fun x : ℝ × Space => p.raw x.1 x.2)) (i : Fin 2) (x : ℝ × Space) :
    advT (p.Efun i) (fun w => realC (p.raw w.1 w.2)) x =
      realC (fderiv ℝ (p.raw x.1) x.2 (p.inlet i x.1 x.2)) := by
  have hv : fderiv ℝ (p.raw x.1) x.2 (p.inlet i x.1 x.2) =
      ∑ k : Fin 3, (p.inlet i x.1 x.2 k) •
        fderiv ℝ (p.raw x.1) x.2 (EuclideanSpace.single k 1) := by
    conv_lhs => rw [ibp_space_sum_single (p.inlet i x.1 x.2)]
    rw [map_sum]
    exact Finset.sum_congr rfl fun k _ => map_smul _ _ _
  ext m
  simp only [advT, Params.Efun, dy_realC_comp hRaw, hv, realC_apply,
    Fin.sum_univ_three, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
    Complex.ofReal_add, Complex.ofReal_mul]

/-- **Integration by parts** for the unprojected inlet source (SP 2355-2383). -/
theorem inletSourceIBP_of (hRaw : UnforcedLeray.Short.IIb.RawJointSmooth)
    (hDiv : UnforcedLeray.Short.IIb.RawDivFree) :
    UnforcedLeray.Short.IIb.InletSourceIBP := by
  intro Sig lam q hSig hq dm dp hdm
  obtain ⟨ν₁, h1, H1⟩ := inletJointSmooth Sig lam q hSig hq dm dp hdm
  obtain ⟨ν₂, h2, H2⟩ := hRaw Sig lam q hSig hq dm dp hdm
  obtain ⟨ν₃, h3, H3⟩ := hDiv Sig lam q hSig hq dm dp hdm
  refine ⟨min ν₁ (min ν₂ ν₃), lt_min h1 (lt_min h2 h3), ?_⟩
  intro p d hreg hν hSig' hmode i Φ hΦ
  have e1 : p.ν ≤ ν₁ := hν.trans (min_le_left _ _)
  have e23 : p.ν ≤ min ν₂ ν₃ := hν.trans (min_le_right _ _)
  have e2 : p.ν ≤ ν₂ := e23.trans (min_le_left _ _)
  have e3 : p.ν ≤ ν₃ := e23.trans (min_le_right _ _)
  have hInl : ContDiff ℝ ∞ (fun x : ℝ × Space => p.inlet i x.1 x.2) :=
    H1 p d hreg e1 hSig' hmode i
  have hRaw' : ContDiff ℝ ∞ (fun x : ℝ × Space => p.raw x.1 x.2) :=
    H2 p d hreg e2 hSig' hmode i
  have hDiv' : ∀ τ y, ∑ k : Fin 3, fderiv ℝ (p.raw τ) y (EuclideanSpace.single k 1) k = 0 :=
    H3 p d hreg e3 hSig' hmode i
  have hE : ContDiff ℝ ∞ (p.Efun i) := contDiff_realC_field hInl
  have hEper : ∀ τ y, p.Efun i (τ + p.period, y) = p.Efun i (τ, y) := by
    intro τ y
    simp only [Params.Efun, ibp_inlet_periodic]
  rw [absIBP_core p.period_pos hRaw' hE hEper (fun x _ => hDiv' x.1 x.2) hΦ.1]
  congr 1
  funext x
  rw [ibp_advT_Efun_Ufun hRaw' i x]
  rfl

end UnforcedLeray.Short.IIb
