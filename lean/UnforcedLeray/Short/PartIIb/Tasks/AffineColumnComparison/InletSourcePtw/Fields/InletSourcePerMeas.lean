import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_4_1_Fields
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletSourcePtw.Fields.InletJointSmooth
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletSourcePtw.Fields.InletSourceGradPtw
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawGood

/-!
# Part II-b, task `PartII-b:G4/4/1/1/7` (`InletSourcePerMeas`)

Source of record: `the November 2 reference manuscript`, lines 2355-2383.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint UnforcedLeray.PhaseSpace
  UnforcedLeray.B0411 UnforcedLeray.B0412 UnforcedLeray.Axi

theorem ispm_inlet_periodic (p : Params) (i : Fin 2) (τ : ℝ) (y : Space) :
    p.inlet i (τ + p.period) y = p.inlet i τ y := by
  have hR : p.R ≠ 0 := p.R_pos.ne'
  have hch' : Axi.chart p.R (τ + p.period) y =
      (Axi.age p.R y, (Axi.phase p.R τ y + p.c, Axi.trans p.R y)) := by
    simp only [Axi.chart, Axi.phase, p.period_eq]
    refine Prod.ext rfl (Prod.ext ?_ rfl)
    show p.R * (τ + 2 * p.c / p.R) / 2 - p.R / 2 * Real.log (Axi.age p.R y) =
      p.R * τ / 2 - p.R / 2 * Real.log (Axi.age p.R y) + p.c
    field_simp
    ring
  unfold Params.inlet Axi.Nv
  rw [hch', p.inletProfile_periodic i]
  rfl

theorem ispm_raw_periodic (p : Params) (τ : ℝ) (y : Space) :
    p.raw (τ + p.period) y = p.raw τ y := by
  by_cases hy : y ∈ Axi.axis
  · have hev : (Axi.Nv p.R (UnforcedLeray.Cons.C03.rawProfile p.ε p.train.v p.train.ψ)
        (τ + p.period)) =ᶠ[𝓝[Axi.axisᶜ] y]
        (Axi.Nv p.R (UnforcedLeray.Cons.C03.rawProfile p.ε p.train.v p.train.ψ) τ) := by
      filter_upwards [self_mem_nhdsWithin] with z hz
      have h1 := raw_periodic_off (p := p) τ hz
      rwa [p.raw_eq_off_axis _ z hz, p.raw_eq_off_axis _ z hz] at h1
    show UnforcedLeray.Cons.C03.Concrete.axisExt _ y = UnforcedLeray.Cons.C03.Concrete.axisExt _ y
    unfold UnforcedLeray.Cons.C03.Concrete.axisExt
    simp only [hy, ↓reduceIte, limUnder]
    rw [Filter.map_congr hev]
  · exact raw_periodic_off τ hy

private theorem ispm_fderiv_periodic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : ℝ} {F : ℝ × Space → E} (hF : ∀ x : ℝ × Space, F (x.1 + P, x.2) = F x) (x : ℝ × Space) :
    fderiv ℝ F (x.1 + P, x.2) = fderiv ℝ F x := by
  have hinv : ∀ z : ℝ × Space, F (z + (P, 0)) = F z := by
    intro z
    rw [show z + (P, (0 : Space)) = (z.1 + P, z.2) from Prod.ext rfl (add_zero _)]
    exact hF z
  have hx : (x.1 + P, x.2) = x + (P, (0 : Space)) := Prod.ext rfl (add_zero _).symm
  rw [hx]
  exact fderiv_add_of_invariant hinv x

theorem ispm_dτ_periodic {P : ℝ} {F : ℝ × Space → CVec3}
    (hF : ∀ x : ℝ × Space, F (x.1 + P, x.2) = F x) (x : ℝ × Space) :
    dτ F (x.1 + P, x.2) = dτ F x := by
  simp only [dτ, ispm_fderiv_periodic hF x]

theorem ispm_dy_periodic {P : ℝ} {F : ℝ × Space → CVec3}
    (hF : ∀ x : ℝ × Space, F (x.1 + P, x.2) = F x) (j : Fin 3) (x : ℝ × Space) :
    dy j F (x.1 + P, x.2) = dy j F x := by
  simp only [dy, ispm_fderiv_periodic hF x]

theorem ispm_radialT_periodic {P : ℝ} {F : ℝ × Space → CVec3}
    (hF : ∀ x : ℝ × Space, F (x.1 + P, x.2) = F x) (x : ℝ × Space) :
    radialT F (x.1 + P, x.2) = radialT F x := by
  simp only [radialT, ispm_dy_periodic hF _ x]

theorem ispm_lapT_periodic {P : ℝ} {F : ℝ × Space → CVec3}
    (hF : ∀ x : ℝ × Space, F (x.1 + P, x.2) = F x) (x : ℝ × Space) :
    lapT F (x.1 + P, x.2) = lapT F x := by
  simp only [lapT, ispm_dy_periodic (ispm_dy_periodic hF _) _ x]

theorem ispm_advT_periodic {P : ℝ} {A B : ℝ × Space → CVec3}
    (hA : ∀ x : ℝ × Space, A (x.1 + P, x.2) = A x)
    (hB : ∀ x : ℝ × Space, B (x.1 + P, x.2) = B x) (x : ℝ × Space) :
    advT A B (x.1 + P, x.2) = advT A B x := by
  simp only [advT, hA x, ispm_dy_periodic hB _ x]

theorem inletSourceF_periodic (p : Params) (i : Fin 2) (x : ℝ × Space) :
    inletSourceF p i (x.1 + p.period, x.2) = inletSourceF p i x := by
  have hE : ∀ z : ℝ × Space, p.Efun i (z.1 + p.period, z.2) = p.Efun i z := fun z => by
    simp only [Params.Efun, ispm_inlet_periodic]
  have hU : ∀ z : ℝ × Space, p.Ufun (z.1 + p.period, z.2) = p.Ufun z := fun z => by
    simp only [Params.Ufun, ispm_raw_periodic]
  have hraw : p.raw (x.1 + p.period) = p.raw x.1 := funext (ispm_raw_periodic p x.1)
  simp only [inletSourceF, ispm_dτ_periodic hE x, ispm_radialT_periodic hE x,
    ispm_lapT_periodic hE x, hE x, ispm_advT_periodic hU hE x, hraw,
    ispm_inlet_periodic p i x.1 x.2]

theorem inletSourceG_periodic (p : Params) (i : Fin 2) (j : Fin 3) (x : ℝ × Space) :
    inletSourceG p i j (x.1 + p.period, x.2) = inletSourceG p i j x :=
  ispm_dy_periodic (inletSourceF_periodic p i) j x

/-- **Periodicity and measurability** of the inlet source and its gradients (SP 2355-2383). -/
theorem inletSourcePerMeas_of (hRaw : UnforcedLeray.Short.IIb.RawJointSmooth) :
    UnforcedLeray.Short.IIb.InletSourcePerMeas := by
  intro Sig lam q hSig hq dm dp hdm
  obtain ⟨ν₁, h1, H1⟩ := inletJointSmooth Sig lam q hSig hq dm dp hdm
  obtain ⟨ν₂, h2, H2⟩ := hRaw Sig lam q hSig hq dm dp hdm
  refine ⟨min ν₁ ν₂, lt_min h1 h2, ?_⟩
  intro p d hreg hν hSig' hmode i
  have e1 : p.ν ≤ ν₁ := hν.trans (min_le_left _ _)
  have e2 : p.ν ≤ ν₂ := hν.trans (min_le_right _ _)
  have hInl : ContDiff ℝ ∞ (fun x : ℝ × Space => p.inlet i x.1 x.2) :=
    H1 p d hreg e1 hSig' hmode i
  have hRaw' : ContDiff ℝ ∞ (fun x : ℝ × Space => p.raw x.1 x.2) :=
    H2 p d hreg e2 hSig' hmode i
  have hF : ContDiff ℝ ∞ (inletSourceF p i) := contDiff_inletSourceF hInl hRaw'
  refine ⟨⟨Eventually.of_forall (inletSourceF_periodic p i),
    hF.continuous.aestronglyMeasurable⟩, fun j =>
      ⟨Eventually.of_forall (inletSourceG_periodic p i j),
        (UnforcedLeray.PhaseSpace.contDiff_dy hF j).continuous.aestronglyMeasurable⟩⟩

end UnforcedLeray.Short.IIb
