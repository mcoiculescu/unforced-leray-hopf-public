import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.XAdd.Reg
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.L1_red
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.L1_far
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1.L2

/-!
# Integrability of the outward primitive integrand for old `L²` data
(source 4177-4191, 3604-3621)

For old `L²` data `g` and `r > R√(5ν/6)`, the integrand `ρ ↦ ρ · X₀(ρ, 0, z)_z` of the outward
primitive `Ψ_{X₀}(r, z)` is integrable on `(r, ∞)`: `X₀` is continuous on the young region
(`sepWSmoothOn_of`), and for `ρ ≥ 2R√(5ν/6)` it is `O(ρ^{-3})` (`sepFarDecay`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem xa_outPrim_integrable {c ν μ R : ℝ} (hc : 0 < c) (hν : 0 < ν) (hR : 0 < R)
    (hμ : -(1 / 4) < μ) {g : Chart → Ten3} (hg : IsOldL2 c ν g) (τ z r : ℝ)
    (hr : R * Real.sqrt (5 * ν / 6) < r) :
    IntegrableOn (fun ρ : ℝ => ρ * wardX0 ν μ R c g τ (!₂[ρ, 0, z] : Space) 2) (Ioi r) := by
  obtain ⟨hS, hM, hae⟩ := xa_oldReg hc hν hR hg
  set r0 : ℝ := R * Real.sqrt (5 * ν / 6) with hr0
  have hr0nn : 0 ≤ r0 := by positivity
  have hP : 0 < 2 * c / R := by positivity
  set T' := oldCutSrc R c r0 g with hT'
  have hSW : ∀ (μ' : ℂ) (y : Space) (τ' : ℝ),
      IIIa.sepW ν μ' (oldPhys R c g) y τ' = IIIa.sepW ν μ' T' y τ' :=
    fun μ' y τ' => sepWCongrAE ν μ' _ _ hae y τ'
  have h1 : -(1 / 4 : ℝ) < ((μ : ℝ) : ℂ).re := by simpa using hμ
  have h2 : -(1 / 4 : ℝ) < (((μ : ℝ) : ℂ) + 1).re := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.one_re]; linarith
  have hA : ContDiffOn ℝ 2 (fun y => IIIa.sepW ν (μ : ℂ) T' y τ 2) {y : Space | r0 < ϱ y} :=
    sepWSmoothOn_of IIIa.sepKernelBounds ν _ r0 _ T' hν h1 hr0nn hP hS hM τ 2
  have hB : ContDiffOn ℝ 2 (fun y => IIIa.sepW ν ((μ : ℂ) + 1) T' y τ 2)
      {y : Space | r0 < ϱ y} :=
    sepWSmoothOn_of IIIa.sepKernelBounds ν _ r0 _ T' hν h2 hr0nn hP hS hM τ 2
  obtain ⟨C1, hC1⟩ := sepFarDecay ν (μ : ℂ) r0 _ T' hν h1 hr0nn hP hS hM τ
  obtain ⟨C2, hC2⟩ := sepFarDecay ν ((μ : ℂ) + 1) r0 _ T' hν h2 hr0nn hP hS hM τ
  have hrepr : ∀ ρ : ℝ, wardX0 ν μ R c g τ (!₂[ρ, 0, z] : Space) 2 =
      (IIIa.sepW ν (μ : ℂ) T' (!₂[ρ, 0, z] : Space) τ 2 -
        IIIa.sepW ν ((μ : ℂ) + 1) T' (!₂[ρ, 0, z] : Space) τ 2).re := by
    intro ρ
    simp only [wardX0, PiLp.toLp_apply, hSW]
  set F : ℝ → ℝ := fun ρ => ρ * wardX0 ν μ R c g τ (!₂[ρ, 0, z] : Space) 2 with hF
  have hφ : Continuous (fun ρ : ℝ => (!₂[ρ, 0, z] : Space)) := by fun_prop
  have hmaps : MapsTo (fun ρ : ℝ => (!₂[ρ, 0, z] : Space)) (Ici r) {y : Space | r0 < ϱ y} := by
    intro ρ hρ
    have : r ≤ ρ := hρ
    show r0 < ϱ (!₂[ρ, 0, z] : Space)
    rw [wardFar_varrho ρ z (by linarith)]
    linarith
  have hcont : ContinuousOn F (Ici r) := by
    have hAc : ContinuousOn (fun ρ : ℝ => IIIa.sepW ν (μ : ℂ) T' (!₂[ρ, 0, z] : Space) τ 2)
        (Ici r) := hA.continuousOn.comp hφ.continuousOn hmaps
    have hBc : ContinuousOn (fun ρ : ℝ =>
        IIIa.sepW ν ((μ : ℂ) + 1) T' (!₂[ρ, 0, z] : Space) τ 2) (Ici r) :=
      hB.continuousOn.comp hφ.continuousOn hmaps
    have : ContinuousOn (fun ρ : ℝ => ρ * (IIIa.sepW ν (μ : ℂ) T' (!₂[ρ, 0, z] : Space) τ 2 -
        IIIa.sepW ν ((μ : ℂ) + 1) T' (!₂[ρ, 0, z] : Space) τ 2).re) (Ici r) :=
      continuousOn_id.mul (Complex.continuous_re.comp_continuousOn (hAc.sub hBc))
    refine this.congr fun ρ _ => ?_
    simp only [hF, hrepr]
  set B : ℝ := max r (2 * r0) with hBdef
  have hrB : r ≤ B := le_max_left _ _
  have hBpos : 0 < B := lt_of_lt_of_le (lt_of_le_of_lt hr0nn hr) hrB
  have hI1 : IntegrableOn F (Ioc r B) :=
    ((hcont.mono (Icc_subset_Ici_self)).integrableOn_Icc).mono_set
      Ioc_subset_Icc_self
  have hI2 : IntegrableOn F (Ioi B) := by
    have hrp : IntegrableOn (fun t : ℝ => t ^ (-2 : ℝ)) (Ioi B) :=
      integrableOn_Ioi_rpow_of_lt (by norm_num) hBpos
    refine Integrable.mono' (hrp.const_mul (C1 + C2)) ?_ ?_
    · exact (hcont.mono (Ioi_subset_Ici_self.trans' (Ioi_subset_Ioi hrB))).aestronglyMeasurable
        measurableSet_Ioi
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun ρ hρ => ?_)
      have hρB : B < ρ := hρ
      have hρpos : 0 < ρ := lt_trans hBpos hρB
      have h2r : 2 * r0 ≤ ϱ (!₂[ρ, 0, z] : Space) := by
        rw [wardFar_varrho ρ z hρpos.le]
        exact (le_max_right _ _).trans hρB.le
      have hϱ := wardFar_varrho ρ z hρpos.le
      have a1 := (hC1 2 _ h2r).1
      have a2 := (hC2 2 _ h2r).1
      rw [hϱ] at a1 a2
      have hX : |(IIIa.sepW ν (μ : ℂ) T' (!₂[ρ, 0, z] : Space) τ 2 -
          IIIa.sepW ν ((μ : ℂ) + 1) T' (!₂[ρ, 0, z] : Space) τ 2).re| ≤
          (C1 + C2) * ρ ^ (-3 : ℝ) := by
        have := wardFar_re_sub_le (IIIa.sepW ν (μ : ℂ) T' (!₂[ρ, 0, z] : Space) τ 2)
          (IIIa.sepW ν ((μ : ℂ) + 1) T' (!₂[ρ, 0, z] : Space) τ 2)
        rw [Real.norm_eq_abs] at this
        nlinarith
      have := wardFar_arith ρ (C1 + C2) (C1 + C2) _ hρpos le_rfl hX
      simp only [hF, hrepr]
      exact this
  have hunion : Ioi r = Ioc r B ∪ Ioi B := (Ioc_union_Ioi_eq_Ioi hrB).symm
  rw [hunion]
  exact hI1.union hI2

end UnforcedLeray.Short.PartIIIb.Concrete
