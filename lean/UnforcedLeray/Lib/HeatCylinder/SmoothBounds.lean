import UnforcedLeray.Lib.SobolevC.CylSmooth
import UnforcedLeray.Lib.HeatCylinder.Derivative

/-!
# Global bounds for smooth periodic cylinder fields

A continuous field that is periodic in the cell direction and vanishes outside a compact axial
strip is bounded on the whole plane. The proof reduces the q coordinate to one compact period.
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped Topology ContDiff

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.GaussianVortex (Plane)

/-- A continuous periodic field with compact axial support is bounded globally by its maximum on
one closed fundamental cell times its axial support interval. -/
theorem exists_global_bound_of_cylSmooth {c : ℝ} (hc : 0 < c)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u : Plane → F} (hu : UnforcedLeray.Sob.IsCylSmooth c u) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z, ‖u z‖ ≤ M := by
  obtain ⟨R, hR⟩ := hu.bounded
  let K : Set Plane := Icc (-c / 2) (c / 2) ×ˢ Icc (-R) R
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  obtain ⟨M₀, hM₀⟩ := hK.exists_bound_of_continuousOn hu.smooth.continuous.continuousOn
  refine ⟨max M₀ (0 : ℝ), le_max_right _ _, fun z => ?_⟩
  by_cases hη : R < |z.2|
  · rw [hR z hη]
    simp
  · have hη' : |z.2| ≤ R := le_of_not_gt hη
    have hηmem : z.2 ∈ Icc (-R) R := abs_le.mp hη'
    let g : ℝ → F := fun q => u (q, z.2)
    have hper : Function.Periodic g c := by
      intro q
      dsimp [g]
      have := hu.periodic (q, z.2)
      simpa using this
    let q' : ℝ := toIcoMod hc (-c / 2) z.1
    have hq'mem : q' ∈ Ico (-c / 2) (-c / 2 + c) := by
      exact toIcoMod_mem_Ico hc (-c / 2) z.1
    have hq'Icc : q' ∈ Icc (-c / 2) (c / 2) := ⟨hq'mem.1, by linarith [hq'mem.2]⟩
    have hreduce : u z = u (q', z.2) := by
      have hgq : g z.1 = g q' := by
        dsimp [q']
        rw [← self_sub_toIcoDiv_zsmul, hper.sub_zsmul_eq]
      exact hgq
    have hKz : (q', z.2) ∈ K := ⟨hq'Icc, hηmem⟩
    calc
      ‖u z‖ = ‖u (q', z.2)‖ := congrArg norm hreduce
      _ ≤ M₀ := hM₀ (q', z.2) hKz
      _ ≤ max M₀ 0 := le_max_left _ _


/-- The first derivative field of a smooth periodic compact-axial field is globally bounded in
operator norm. Periodicity and axial support pass to the derivative, after which the compact-strip
bound applies to the continuous-linear-map-valued field. -/
theorem exists_global_deriv_bound_of_cylSmooth {c : ℝ} (hc : 0 < c)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u : Plane → F} (hu : UnforcedLeray.Sob.IsCylSmooth c u) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z, ‖fderiv ℝ u z‖ ≤ M := by
  let D : Plane → Plane →L[ℝ] F := fun z => fderiv ℝ u z
  have hDsmooth : ContDiff ℝ ∞ D := by
    exact ContDiff.fderiv_right (m := ∞) hu.smooth (by simp)
  have hDperiodic : ∀ z, D (z + (c, 0)) = D z := by
    intro z
    have heq : (fun y : Plane => u (y + (c, 0))) = u := funext hu.periodic
    have h := fderiv_comp_add_right (𝕜 := ℝ) (f := u) (x := z) ((c, 0) : Plane)
    rw [heq] at h
    simpa [D] using h.symm
  obtain ⟨R, hR⟩ := hu.bounded
  have hDbounded : ∀ z : Plane, R < |z.2| → D z = 0 := by
    intro z hz
    have hopen : IsOpen {y : Plane | R < |y.2|} :=
      isOpen_lt continuous_const (continuous_abs.comp continuous_snd)
    have hev : u =ᶠ[𝓝 z] fun _ => (0 : F) :=
      Filter.eventually_of_mem (hopen.mem_nhds hz) fun y hy => hR y hy
    change fderiv ℝ u z = 0
    rw [hev.fderiv_eq]
    simp
  have hD : UnforcedLeray.Sob.IsCylSmooth c D :=
    ⟨hDsmooth, hDperiodic, ⟨R, hDbounded⟩⟩
  exact exists_global_bound_of_cylSmooth hc hD


/-- The classical derivative of heatDiv on a smooth periodic compact-axial tensor field equals
heatDiv applied to the derivative of the tensor. -/
theorem fderiv_heatDiv_apply_of_cylSmooth {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    {T : Plane → Plane × Plane} (hT : UnforcedLeray.Sob.IsCylSmooth c T)
    (z e : Plane) :
    fderiv ℝ (UnforcedLeray.B0296.heatDiv θ T) z e =
      UnforcedLeray.B0296.heatDiv θ (fun x => fderiv ℝ T x e) z := by
  obtain ⟨M₀, hM₀, hTbound⟩ := exists_global_bound_of_cylSmooth hc hT
  obtain ⟨M₁, hM₁, hderivBound⟩ := exists_global_deriv_bound_of_cylSmooth hc hT
  have hT1 : ContDiff ℝ 1 T := hT.smooth.of_le (by norm_num)
  have hfd := UnforcedLeray.HeatCylinder.hasFDerivAt_heatDiv hθ hT1 hTbound
    hderivBound z
  calc
    fderiv ℝ (UnforcedLeray.B0296.heatDiv θ T) z e =
        (∫ w : Plane, (divKernelCLM θ w).comp (fderiv ℝ T (z - w))) e :=
      congrArg (fun L : Plane →L[ℝ] Plane => L e) hfd.fderiv
    _ = UnforcedLeray.B0296.heatDiv θ (fun x => fderiv ℝ T x e) z :=
      heatDivFDeriv_apply hθ hT1 hderivBound z e

/-- Every iterated classical spatial derivative of the actual heatDiv convolution commutes with
the Gaussian integral on smooth periodic compact-axial tensor fields. -/
theorem iterD_heatDiv_commute {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    {T : Plane → Plane × Plane} (hT : UnforcedLeray.Sob.IsCylSmooth c T)
    (vs : List Plane) :
    UnforcedLeray.Sob.iterD vs (UnforcedLeray.B0296.heatDiv θ T) =
      fun z => UnforcedLeray.B0296.heatDiv θ
        (UnforcedLeray.Sob.iterD vs T) z := by
  induction vs with
  | nil => rfl
  | cons e vs ih =>
    funext z
    simp only [UnforcedLeray.Sob.iterD_cons]
    have hder := congrArg (fun f : Plane → Plane => fderiv ℝ f z e) ih
    rw [hder]
    exact fderiv_heatDiv_apply_of_cylSmooth hc hθ (hT.iterD vs) z e

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.exists_global_bound_of_cylSmooth
#print axioms UnforcedLeray.HeatCylinder.exists_global_deriv_bound_of_cylSmooth
#print axioms UnforcedLeray.HeatCylinder.fderiv_heatDiv_apply_of_cylSmooth
#print axioms UnforcedLeray.HeatCylinder.iterD_heatDiv_commute
#print axioms UnforcedLeray.HeatCylinder.exists_global_deriv_bound_of_cylSmooth
