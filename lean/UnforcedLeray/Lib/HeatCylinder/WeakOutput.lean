import UnforcedLeray.Lib.HeatCylinder.SmoothBounds
import UnforcedLeray.Lib.HeatCylinder.CellBridge
import UnforcedLeray.Lib.CylinderB.Tests
import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-!
# Weak cylinder derivatives of Gaussian-tailed heat outputs

The output of heatDiv is not compactly supported axially. Weak integration by parts still holds
against the cylinder test class because the tests and their derivatives have compact axial support.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000

noncomputable section

open MeasureTheory Set
open scoped Topology ContDiff ENNReal

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.GaussianVortex (Plane)

private theorem integrableOn_test_smul_continuous {c : ℝ}
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {φ : Plane → ℝ} (hφ : UnforcedLeray.Sob.IsCylTest c φ)
    {u : Plane → F} (hu : Continuous u) :
    Integrable (fun z => φ z • u z)
      (volume.restrict (UnforcedLeray.Cyl.cell c)) := by
  obtain ⟨R, hR⟩ := hφ.bounded
  have h := UnforcedLeray.Sob.integrableOn_cylCell (c := c)
    (hφ.smooth.continuous.smul hu) (R := R)
      (fun z hz => by
        change φ z • u z = 0
        rw [hR z hz, zero_smul])
  change Integrable (fun z => φ z • u z)
    (volume.restrict (UnforcedLeray.Cyl.cell c))
  rw [UnforcedLeray.Sob.cyl_cell_eq]
  exact h

private theorem IsCylSmooth.fst {c : ℝ} {F G : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {u : Plane → F × G} (hu : UnforcedLeray.Sob.IsCylSmooth c u) :
    UnforcedLeray.Sob.IsCylSmooth c (fun z => (u z).1) := by
  obtain ⟨R, hR⟩ := hu.bounded
  refine ⟨hu.smooth.fst, ?_, ?_⟩
  · intro z
    exact congrArg Prod.fst (hu.periodic z)
  · exact ⟨R, fun z hz => by simp [hR z hz]⟩

private theorem IsCylSmooth.snd {c : ℝ} {F G : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {u : Plane → F × G} (hu : UnforcedLeray.Sob.IsCylSmooth c u) :
    UnforcedLeray.Sob.IsCylSmooth c (fun z => (u z).2) := by
  obtain ⟨R, hR⟩ := hu.bounded
  refine ⟨hu.smooth.snd, ?_, ?_⟩
  · intro z
    exact congrArg Prod.snd (hu.periodic z)
  · exact ⟨R, fun z hz => by simp [hR z hz]⟩

private theorem memLp_scalar_cylSmooth_normalized {c : ℝ} (hc : 0 < c)
    {f : Plane → ℝ} (hf : UnforcedLeray.Sob.IsCylSmooth c f) :
    MemLp f 2 (UnforcedLeray.B0284.cellMeasure c) := by
  have hcenter : MemLp f 2 (UnforcedLeray.Cyl.cellμ c) := by
    have h := hf.memLp (1 : UnforcedLeray.Sob.Weight Plane) 2
    simpa [UnforcedLeray.Sob.wμ_one, UnforcedLeray.Sob.cylinder_μ,
      UnforcedLeray.Sob.cyl_cell_eq, UnforcedLeray.Cyl.cellμ] using h
  have hper : UnforcedLeray.B0284.IsQPeriodic c f := by
    intro z
    have hcoord : (z.1 + c, z.2) = z + (c, 0) := by ext <;> simp
    rw [hcoord]
    exact hf.periodic z
  exact memLp_cellMeasure_of_memLp_cyl hc hf.smooth.continuous.measurable hper hcenter

theorem memLp_tensor_iterD_cylSmooth_normalized {c : ℝ} (hc : 0 < c)
    {T : Plane → Plane × Plane} (hT : UnforcedLeray.Sob.IsCylSmooth c T)
    (vs : List Plane) :
    MemLp (UnforcedLeray.Sob.iterD vs T) 2 (UnforcedLeray.B0284.cellMeasure c) := by
  have hD : UnforcedLeray.Sob.IsCylSmooth c (UnforcedLeray.Sob.iterD vs T) := hT.iterD vs
  have hrow₁smooth := IsCylSmooth.fst hD
  have hrow₂smooth := IsCylSmooth.snd hD
  have h00 := memLp_scalar_cylSmooth_normalized hc (IsCylSmooth.fst hrow₁smooth)
  have h01 := memLp_scalar_cylSmooth_normalized hc (IsCylSmooth.snd hrow₁smooth)
  have h10 := memLp_scalar_cylSmooth_normalized hc (IsCylSmooth.fst hrow₂smooth)
  have h11 := memLp_scalar_cylSmooth_normalized hc (IsCylSmooth.snd hrow₂smooth)
  have hrow₁ : MemLp (fun z => (UnforcedLeray.Sob.iterD vs T z).1) 2
      (UnforcedLeray.B0284.cellMeasure c) := by
    rw [memLp_prod_iff]
    exact ⟨h00, h01⟩
  have hrow₂ : MemLp (fun z => (UnforcedLeray.Sob.iterD vs T z).2) 2
      (UnforcedLeray.B0284.cellMeasure c) := by
    rw [memLp_prod_iff]
    exact ⟨h10, h11⟩
  change MemLp (fun z => ((UnforcedLeray.Sob.iterD vs T z).1,
    (UnforcedLeray.Sob.iterD vs T z).2)) 2 (UnforcedLeray.B0284.cellMeasure c)
  rw [memLp_prod_iff]
  exact ⟨hrow₁, hrow₂⟩

/-- A differentiable periodic field has its classical first derivative as a cylinder weak
 derivative when its two coordinate derivatives are continuous. No axial support assumption is
made on the field; compact support is needed only for the test. -/
theorem hasWeakDeriv_cylinder_dir_of_continuous_fderiv {c : ℝ} (hc : 0 < c)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {u : Plane → F} (hu : Differentiable ℝ u) (huc : Continuous u)
    (hper : UnforcedLeray.Cyl.IsPeriodic c u)
    (hderc : ∀ e : Plane, Continuous (fun z => fderiv ℝ u z e)) (v : Plane) :
    UnforcedLeray.Sob.HasWeakDeriv (UnforcedLeray.Sob.cylinder c) [v] u
      (fun z => fderiv ℝ u z v) := by
  refine ⟨fun φ hφ => ?_, fun φ hφ => ?_, fun φ hφ => ?_⟩
  · have hφ' : UnforcedLeray.Sob.IsCylTest c φ := hφ
    simpa [UnforcedLeray.Sob.cylinder_μ, UnforcedLeray.Sob.cyl_cell_eq] using
      integrableOn_test_smul_continuous (hφ'.dirDeriv v) huc
  · have hφ' : UnforcedLeray.Sob.IsCylTest c φ := hφ
    simpa [UnforcedLeray.Sob.cylinder_μ, UnforcedLeray.Sob.cyl_cell_eq] using
      integrableOn_test_smul_continuous hφ' (hderc v)
  · have hφ : UnforcedLeray.Sob.IsCylTest c φ := hφ
    have hφsmooth : UnforcedLeray.Sob.IsCylSmooth c φ := hφ.isCylSmooth
    let H : Plane → F := fun z => φ z • u z
    have hHdiff : Differentiable ℝ H := hφsmooth.smooth.differentiable (by simp) |>.smul hu
    have hHcont : Continuous H := hφsmooth.smooth.continuous.smul huc
    have hHper : UnforcedLeray.Cyl.IsPeriodic c H := by
      intro z
      change φ (z.1 + c, z.2) • u (z.1 + c, z.2) = φ z • u z
      have hcoord : (z.1 + c, z.2) = z + (c, 0) := by ext <;> simp
      have huper : u (z + (c, 0)) = u z := by
        simpa only [hcoord] using hper z
      rw [hcoord, hφ.periodic z]
      exact congrArg (fun y => φ z • y) huper
    obtain ⟨R, hR⟩ := hφ.bounded
    have hHvanish : ∀ z : Plane, R < |z.2| → H z = 0 := by
      intro z hz
      simp [H, hR z hz]
    have hHderiv (z e : Plane) :
        fderiv ℝ H z e = fderiv ℝ φ z e • u z + φ z • fderiv ℝ u z e := by
      have h1 : DifferentiableAt ℝ φ z := (hφsmooth.smooth.differentiable (by simp)) z
      have h2 : DifferentiableAt ℝ u z := hu z
      change fderiv ℝ (fun y : Plane => φ y • u y) z e = _
      have hfun : (fun y : Plane => φ y • u y) = φ • u := rfl
      rw [hfun, fderiv_smul h1 h2]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.smulRight_apply]
      rw [add_comm]
    have hq : IntegrableOn (fun z => fderiv ℝ H z ((1 : ℝ), (0 : ℝ)))
        (UnforcedLeray.Cyl.cell c) := by
      have hφq : UnforcedLeray.Sob.IsCylSmooth c
          (fun z => fderiv ℝ φ z ((1 : ℝ), (0 : ℝ))) := hφsmooth.dir _
      have hφq' : UnforcedLeray.Sob.IsCylTest c
          (fun z => fderiv ℝ φ z ((1 : ℝ), (0 : ℝ))) :=
        ⟨hφq.smooth, hφq.periodic, hφq.bounded⟩
      have h1 := integrableOn_test_smul_continuous hφq' huc
      have h2 := integrableOn_test_smul_continuous hφ (hderc ((1 : ℝ), (0 : ℝ)))
      have heq : (fun z => fderiv ℝ H z ((1 : ℝ), (0 : ℝ))) =
          fun z => fderiv ℝ φ z ((1 : ℝ), (0 : ℝ)) • u z +
            φ z • fderiv ℝ u z ((1 : ℝ), (0 : ℝ)) := funext fun z => hHderiv z _
      rw [heq]
      exact h1.add h2
    have heta : IntegrableOn (fun z => fderiv ℝ H z ((0 : ℝ), (1 : ℝ)))
        (UnforcedLeray.Cyl.cell c) := by
      have hφη : UnforcedLeray.Sob.IsCylSmooth c
          (fun z => fderiv ℝ φ z ((0 : ℝ), (1 : ℝ))) := hφsmooth.dir _
      have hφη' : UnforcedLeray.Sob.IsCylTest c
          (fun z => fderiv ℝ φ z ((0 : ℝ), (1 : ℝ))) :=
        ⟨hφη.smooth, hφη.periodic, hφη.bounded⟩
      have h1 := integrableOn_test_smul_continuous hφη' huc
      have h2 := integrableOn_test_smul_continuous hφ (hderc ((0 : ℝ), (1 : ℝ)))
      have heq : (fun z => fderiv ℝ H z ((0 : ℝ), (1 : ℝ))) =
          fun z => fderiv ℝ φ z ((0 : ℝ), (1 : ℝ)) • u z +
            φ z • fderiv ℝ u z ((0 : ℝ), (1 : ℝ)) := funext fun z => hHderiv z _
      rw [heq]
      exact h1.add h2
    have hqzero : ∫ z in UnforcedLeray.Cyl.cell c,
        fderiv ℝ H z ((1 : ℝ), (0 : ℝ)) = 0 := by
      have hd : ∀ q η, HasDerivAt (fun q' => H (q', η))
          (fderiv ℝ H (q, η) ((1 : ℝ), (0 : ℝ))) q := by
        intro q η
        have hl : HasDerivAt (fun q' : ℝ => ((q', η) : Plane))
            ((1 : ℝ), (0 : ℝ)) q :=
          (hasDerivAt_id q).prodMk (hasDerivAt_const q η)
        exact (hHdiff (q, η)).hasFDerivAt.comp_hasDerivAt q hl
      exact UnforcedLeray.Cyl.integral_cell_deriv_q_of_periodic hc hHper hd hq
    have hetazero : ∫ z in UnforcedLeray.Cyl.cell c,
        fderiv ℝ H z ((0 : ℝ), (1 : ℝ)) = 0 := by
      have hd : ∀ q η, HasDerivAt (fun η' : ℝ => H (q, η'))
          (fderiv ℝ H (q, η) ((0 : ℝ), (1 : ℝ))) η := by
        intro q η
        have hl : HasDerivAt (fun η' : ℝ => ((q, η') : Plane))
            ((0 : ℝ), (1 : ℝ)) η :=
          (hasDerivAt_const η q).prodMk (hasDerivAt_id η)
        exact (hHdiff (q, η)).hasFDerivAt.comp_hasDerivAt η hl
      have hHint : IntegrableOn H (UnforcedLeray.Cyl.cell c) := by
        have h := UnforcedLeray.Sob.integrableOn_cylCell (c := c) hHcont hHvanish
        rw [← UnforcedLeray.Sob.cyl_cell_eq] at h
        exact h
      exact UnforcedLeray.Cyl.integral_cell_deriv_eta hd hHint heta
    have hvsplit : ∀ z, fderiv ℝ H z v =
        v.1 • fderiv ℝ H z ((1 : ℝ), (0 : ℝ)) +
          v.2 • fderiv ℝ H z ((0 : ℝ), (1 : ℝ)) := by
      intro z
      have hv : v = v.1 • ((1 : ℝ), (0 : ℝ)) + v.2 • ((0 : ℝ), (1 : ℝ)) := by
        ext <;> simp
      calc
        fderiv ℝ H z v = fderiv ℝ H z
            (v.1 • ((1 : ℝ), (0 : ℝ)) + v.2 • ((0 : ℝ), (1 : ℝ))) :=
          congrArg (fderiv ℝ H z) hv
        _ = v.1 • fderiv ℝ H z ((1 : ℝ), (0 : ℝ)) +
            v.2 • fderiv ℝ H z ((0 : ℝ), (1 : ℝ)) := by rw [map_add, map_smul, map_smul]
    have hDzero : ∫ z in UnforcedLeray.Cyl.cell c, fderiv ℝ H z v = 0 := by
      simp_rw [hvsplit]
      rw [integral_add (f := fun z => v.1 • fderiv ℝ H z ((1 : ℝ), (0 : ℝ)))
        (g := fun z => v.2 • fderiv ℝ H z ((0 : ℝ), (1 : ℝ)))
        (hq.smul v.1) (heta.smul v.2), integral_smul, integral_smul, hqzero, hetazero,
        smul_zero, smul_zero, add_zero]
    have hprod (z : Plane) : fderiv ℝ H z v =
        fderiv ℝ φ z v • u z + φ z • fderiv ℝ u z v := hHderiv z v
    have hleft : IntegrableOn (fun z => fderiv ℝ φ z v • u z)
        (UnforcedLeray.Cyl.cell c) := integrableOn_test_smul_continuous (hφ.dirDeriv v) huc
    have hright : IntegrableOn (fun z => φ z • fderiv ℝ u z v)
        (UnforcedLeray.Cyl.cell c) := integrableOn_test_smul_continuous hφ (hderc v)
    have hzero : (∫ z in UnforcedLeray.Cyl.cell c,
        fderiv ℝ φ z v • u z) +
        (∫ z in UnforcedLeray.Cyl.cell c, φ z • fderiv ℝ u z v) = 0 := by
      rw [← integral_add hleft hright]
      calc
        ∫ z in UnforcedLeray.Cyl.cell c,
            (fderiv ℝ φ z v • u z + φ z • fderiv ℝ u z v) =
            ∫ z in UnforcedLeray.Cyl.cell c, fderiv ℝ H z v :=
          integral_congr_ae (Filter.Eventually.of_forall fun z => (hprod z).symm)
        _ = 0 := hDzero
    have hrel := (add_eq_zero_iff_eq_neg.mp hzero)
    simpa [UnforcedLeray.Sob.iterDirDeriv_singleton,
      UnforcedLeray.Sob.cylinder_μ, UnforcedLeray.Sob.cyl_cell_eq,
      UnforcedLeray.Cyl.cellμ, List.length_singleton, pow_one, neg_smul, one_smul,
      IntegrableOn] using hrel


/-- Actual Gaussian heatDiv is differentiable for every smooth periodic compact-axial tensor
input. The global bounds needed by dominated differentiation come from compactness of one period.
-/
theorem differentiable_heatDiv_of_cylSmooth {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    {T : Plane → Plane × Plane} (hT : UnforcedLeray.Sob.IsCylSmooth c T) :
    Differentiable ℝ (UnforcedLeray.B0296.heatDiv θ T) := by
  obtain ⟨M₀, hM₀, hTbound⟩ := exists_global_bound_of_cylSmooth hc hT
  obtain ⟨M₁, hM₁, hderivBound⟩ := exists_global_deriv_bound_of_cylSmooth hc hT
  have hT1 : ContDiff ℝ 1 T := hT.smooth.of_le (by norm_num)
  intro z
  exact (hasFDerivAt_heatDiv hθ hT1 hTbound hderivBound z).differentiableAt

/-- The actual Gaussian heatDiv output of a smooth periodic compact-axial tensor has the expected
first cylinder weak derivative, even though the heat output itself has Gaussian axial tails. -/
theorem hasWeakDeriv_heatDiv_dir_of_cylSmooth {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    {T : Plane → Plane × Plane} (hT : UnforcedLeray.Sob.IsCylSmooth c T) (v : Plane) :
    UnforcedLeray.Sob.HasWeakDeriv (UnforcedLeray.Sob.cylinder c) [v]
      (UnforcedLeray.B0296.heatDiv θ T)
      (fun z => UnforcedLeray.B0296.heatDiv θ (fun x => fderiv ℝ T x v) z) := by
  have hTper : UnforcedLeray.B0284.IsQPeriodic c T := by
    intro z
    have hcoord : (z.1 + c, z.2) = z + (c, 0) := by ext <;> simp
    rw [hcoord]
    exact hT.periodic z
  have hUdiff : Differentiable ℝ (UnforcedLeray.B0296.heatDiv θ T) :=
    differentiable_heatDiv_of_cylSmooth hc hθ hT
  have hUcont : Continuous (UnforcedLeray.B0296.heatDiv θ T) := hUdiff.continuous
  have hUper : UnforcedLeray.B0284.IsQPeriodic c
      (UnforcedLeray.B0296.heatDiv θ T) :=
    UnforcedLeray.B0296.heatDiv_periodic (θ := θ) hTper
  have hderc : ∀ e : Plane, Continuous (fun z =>
      fderiv ℝ (UnforcedLeray.B0296.heatDiv θ T) z e) := by
    intro e
    have hEq : (fun z => fderiv ℝ (UnforcedLeray.B0296.heatDiv θ T) z e) =
        fun z => UnforcedLeray.B0296.heatDiv θ (fun x => fderiv ℝ T x e) z := by
      funext z
      exact fderiv_heatDiv_apply_of_cylSmooth hc hθ hT z e
    rw [hEq]
    exact (differentiable_heatDiv_of_cylSmooth hc hθ (hT.dir e)).continuous
  have hEqv : (fun z => fderiv ℝ (UnforcedLeray.B0296.heatDiv θ T) z v) =
      fun z => UnforcedLeray.B0296.heatDiv θ (fun x => fderiv ℝ T x v) z := by
    funext z
    exact fderiv_heatDiv_apply_of_cylSmooth hc hθ hT z v
  have hweak := hasWeakDeriv_cylinder_dir_of_continuous_fderiv
    hc hUdiff hUcont hUper hderc v
  exact hweak.congr_ae (Filter.Eventually.of_forall fun _ => rfl)
    (Filter.Eventually.of_forall fun z => congrFun hEqv z)


/-- Every iterated weak spatial derivative of the actual Gaussian heatDiv output is the
corresponding Gaussian convolution of the compact-axial tensor derivative. -/
theorem hasWeakDeriv_iterD_heatDiv {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    {T : Plane → Plane × Plane} (hT : UnforcedLeray.Sob.IsCylSmooth c T)
    (vs : List Plane) :
    UnforcedLeray.Sob.HasWeakDeriv (UnforcedLeray.Sob.cylinder c) vs
      (UnforcedLeray.B0296.heatDiv θ T)
      (UnforcedLeray.Sob.iterD vs (UnforcedLeray.B0296.heatDiv θ T)) := by
  induction vs with
  | nil =>
    refine UnforcedLeray.Sob.HasWeakDeriv.nil fun φ hφ => ?_
    have hφ' : UnforcedLeray.Sob.IsCylTest c φ := hφ
    have hcont := (differentiable_heatDiv_of_cylSmooth hc hθ hT).continuous
    rw [UnforcedLeray.Sob.cylinder_μ]
    change Integrable (fun z => φ z • UnforcedLeray.B0296.heatDiv θ T z)
      (volume.restrict (UnforcedLeray.Sob.cylCell c))
    have hInt := integrableOn_test_smul_continuous hφ' hcont
    rw [UnforcedLeray.Sob.cyl_cell_eq] at hInt
    exact hInt
  | cons e vs ih =>
    have hcomm := iterD_heatDiv_commute hc hθ hT vs
    have hweakOne := hasWeakDeriv_heatDiv_dir_of_cylSmooth hc hθ (hT.iterD vs) e
    have hsource : (fun z => UnforcedLeray.B0296.heatDiv θ
        (UnforcedLeray.Sob.iterD vs T) z) =ᵐ[(UnforcedLeray.Sob.cylinder c).μ]
        UnforcedLeray.Sob.iterD vs (UnforcedLeray.B0296.heatDiv θ T) := by
      filter_upwards [] with z
      exact (congrFun hcomm z).symm
    have hout : (fun z => UnforcedLeray.B0296.heatDiv θ
        (UnforcedLeray.Sob.iterD (e :: vs) T) z) =ᵐ[(UnforcedLeray.Sob.cylinder c).μ]
        UnforcedLeray.Sob.iterD (e :: vs) (UnforcedLeray.B0296.heatDiv θ T) := by
      filter_upwards [] with z
      exact (congrFun (iterD_heatDiv_commute hc hθ hT (e :: vs)) z).symm
    have hweakOne' := hweakOne.congr_ae hsource (by
      filter_upwards [] with z
      have h := fderiv_heatDiv_apply_of_cylSmooth hc hθ (hT.iterD vs) z e
      calc
        UnforcedLeray.B0296.heatDiv θ
            (UnforcedLeray.Sob.iterD (e :: vs) T) z =
            UnforcedLeray.B0296.heatDiv θ
              (fun x => fderiv ℝ (UnforcedLeray.Sob.iterD vs T) x e) z := by
                simp [UnforcedLeray.Sob.iterD_cons]
        _ = fderiv ℝ
            (UnforcedLeray.B0296.heatDiv θ (UnforcedLeray.Sob.iterD vs T)) z e := h.symm
        _ = UnforcedLeray.Sob.iterD (e :: vs)
            (UnforcedLeray.B0296.heatDiv θ T) z := by
              have hfdEq := congrArg (fun f : Plane → Plane => fderiv ℝ f z e) hcomm
              calc
                fderiv ℝ (UnforcedLeray.B0296.heatDiv θ
                    (UnforcedLeray.Sob.iterD vs T)) z e =
                    fderiv ℝ (UnforcedLeray.Sob.iterD vs
                      (UnforcedLeray.B0296.heatDiv θ T)) z e := hfdEq.symm
                _ = UnforcedLeray.Sob.iterD (e :: vs)
                    (UnforcedLeray.B0296.heatDiv θ T) z := rfl)
    exact ih.cons hweakOne'

/-- If a classical derivative of the compact-axial input is square integrable on the normalized
cell, then the matching derivative of the actual Gaussian heat output is square integrable too.
The proof applies the concrete B0296 heatDiv estimate to the input derivative and transfers it
through the pointwise derivative-commutation identity. -/
theorem memLp_iterD_heatDiv_of_memLp {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    {T : Plane → Plane × Plane} (hT : UnforcedLeray.Sob.IsCylSmooth c T)
    (vs : List Plane)
    (hmem : MemLp (UnforcedLeray.Sob.iterD vs T) 2
      (UnforcedLeray.B0284.cellMeasure c)) :
    MemLp (UnforcedLeray.Sob.iterD vs (UnforcedLeray.B0296.heatDiv θ T)) 2
      (UnforcedLeray.B0284.cellMeasure c) := by
  have hderiv : UnforcedLeray.Sob.IsCylSmooth c (UnforcedLeray.Sob.iterD vs T) :=
    hT.iterD vs
  have hper : UnforcedLeray.B0284.IsQPeriodic c
      (UnforcedLeray.Sob.iterD vs T) := by
    intro z
    have hcoord : (z.1 + c, z.2) = z + (c, 0) := by ext <;> simp
    rw [hcoord]
    exact hderiv.periodic z
  have hmeas : AEStronglyMeasurable (UnforcedLeray.Sob.iterD vs T) volume :=
    hderiv.smooth.continuous.aestronglyMeasurable
  have hout := UnforcedLeray.B0296.memLp_heatDiv hc hθ hper hmeas
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) ENNReal.ofNat_ne_top hmem.eLpNorm_ne_top
  have hEq : (fun z => UnforcedLeray.B0296.heatDiv θ
      (UnforcedLeray.Sob.iterD vs T) z) =ᵐ[UnforcedLeray.B0284.cellMeasure c]
      UnforcedLeray.Sob.iterD vs (UnforcedLeray.B0296.heatDiv θ T) := by
    filter_upwards [] with z
    exact (congrFun (iterD_heatDiv_commute hc hθ hT vs) z).symm
  exact (memLp_congr_ae hEq).mp hout

/-- Every finite classical derivative of the actual Gaussian heatDiv output of a smooth
periodic compact-axial tensor belongs to normalized-cell `L²`. The input derivative's finite
cell energy follows from compact axial support, with the normalized/centered transfer made
explicit. -/
theorem memLp_iterD_heatDiv_of_cylSmooth {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    {T : Plane → Plane × Plane} (hT : UnforcedLeray.Sob.IsCylSmooth c T)
    (vs : List Plane) :
    MemLp (UnforcedLeray.Sob.iterD vs (UnforcedLeray.B0296.heatDiv θ T)) 2
      (UnforcedLeray.B0284.cellMeasure c) := by
  exact memLp_iterD_heatDiv_of_memLp hc hθ hT vs
    (memLp_tensor_iterD_cylSmooth_normalized hc hT vs)

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.hasWeakDeriv_cylinder_dir_of_continuous_fderiv
#print axioms UnforcedLeray.HeatCylinder.differentiable_heatDiv_of_cylSmooth
#print axioms UnforcedLeray.HeatCylinder.hasWeakDeriv_heatDiv_dir_of_cylSmooth
#print axioms UnforcedLeray.HeatCylinder.hasWeakDeriv_iterD_heatDiv
#print axioms UnforcedLeray.HeatCylinder.memLp_iterD_heatDiv_of_memLp
#print axioms UnforcedLeray.HeatCylinder.memLp_iterD_heatDiv_of_cylSmooth
#print axioms UnforcedLeray.HeatCylinder.memLp_tensor_iterD_cylSmooth_normalized
#print axioms UnforcedLeray.HeatCylinder.differentiable_heatDiv_of_cylSmooth
#print axioms UnforcedLeray.HeatCylinder.hasWeakDeriv_heatDiv_dir_of_cylSmooth
