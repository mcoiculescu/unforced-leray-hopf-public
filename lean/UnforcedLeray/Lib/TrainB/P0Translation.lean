import UnforcedLeray.Lib.CylinderB.Leray

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory Set
open UnforcedLeray.Cyl

namespace UnforcedLeray.TrainB

/-- Vertical translations preserve the centered periodic-cylinder measure. -/
theorem measurePreserving_etaShift (c a : ℝ) :
    MeasurePreserving (fun z : Plane => z + ((0 : ℝ), a)) (cellμ c) (cellμ c) := by
  have hmp : MeasurePreserving (fun z : Plane => z + ((0 : ℝ), a)) volume volume :=
    measurePreserving_add_right volume ((0 : ℝ), a)
  have hpre : (fun z : Plane => z + ((0 : ℝ), a)) ⁻¹' cell c = cell c := by
    ext z
    simp [cell, mem_Ico]
  have h := hmp.restrict_preimage (measurableSet_cell c)
  rw [hpre] at h
  simpa [cellμ] using h

/-- Vertical translation as an isometry on the actual cylinder `L²` quotient. -/
def etaShiftL2 (c a : ℝ) : Cyl.L2v c →ₗᵢ[ℝ] Cyl.L2v c :=
  Lp.compMeasurePreservingₗᵢ ℝ (fun z : Plane => z + ((0 : ℝ), a))
    (measurePreserving_etaShift c a)

theorem etaShiftL2_ae {c a : ℝ} (u : Cyl.L2v c) :
    (etaShiftL2 c a u : Plane → Vec2) =ᵐ[cellμ c]
      fun z => u (z + ((0 : ℝ), a)) :=
  Lp.coeFn_compMeasurePreserving u (measurePreserving_etaShift c a)


/-- Translate a cylinder test in the axial direction. -/
def etaShiftTest (a : ℝ) (φ : Plane → ℝ) : Plane → ℝ :=
  fun z => φ (z + ((0 : ℝ), a))

theorem isCylTest_etaShiftTest {c a : ℝ} {φ : Plane → ℝ}
    (hφ : Sob.IsCylTest c φ) : Sob.IsCylTest c (etaShiftTest a φ) := by
  obtain ⟨R, hR⟩ := hφ.bounded
  refine ⟨hφ.smooth.comp (contDiff_id.add contDiff_const), ?_, ⟨R + |a|, ?_⟩⟩
  · intro z
    change φ ((z + ((c, 0) : Plane)) + ((0, a) : Plane)) =
      φ (z + ((0, a) : Plane))
    calc
      φ ((z + ((c, 0) : Plane)) + ((0, a) : Plane)) =
          φ ((z + ((0, a) : Plane)) + ((c, 0) : Plane)) := by
            congr 1 <;> ext <;> simp [add_assoc, add_comm]
      _ = φ (z + ((0, a) : Plane)) := hφ.periodic _
  · intro z hz
    have htriangle : |z.2| ≤ |z.2 + a| + |a| := by
      calc
        |z.2| = |(z.2 + a) + (-a)| := by congr 1 <;> ring
        _ ≤ |z.2 + a| + |-a| := abs_add_le _ _
        _ = |z.2 + a| + |a| := by rw [abs_neg]
    have hz' : R < |z.2 + a| := by linarith
    exact hR (z + ((0 : ℝ), a)) hz'

/-- The two classical partial derivatives of a translated test are the translated derivatives. -/
theorem etaShiftTest_partialQ {c a : ℝ} {φ : Plane → ℝ}
    (hφ : Sob.IsCylTest c φ) (z : Plane) :
    Cyl.partialQ (etaShiftTest a φ) z = Cyl.partialQ φ (z + ((0 : ℝ), a)) := by
  rw [Cyl.partialQ_eq_fderiv (isCylTest_etaShiftTest hφ).differentiable,
    Cyl.partialQ_eq_fderiv hφ.differentiable]
  have hcomp := fderiv_comp_add_right (𝕜 := ℝ) (f := φ) (x := z) ((0 : ℝ), a)
  have h := congrArg (fun D => D ((1 : ℝ), (0 : ℝ))) hcomp
  change fderiv ℝ (fun x => φ (x + ((0 : ℝ), a))) z ((1 : ℝ), (0 : ℝ)) =
    fderiv ℝ φ (z + ((0 : ℝ), a)) ((1 : ℝ), (0 : ℝ))
  exact h

theorem etaShiftTest_partialEta {c a : ℝ} {φ : Plane → ℝ}
    (hφ : Sob.IsCylTest c φ) (z : Plane) :
    Cyl.partialEta (etaShiftTest a φ) z = Cyl.partialEta φ (z + ((0 : ℝ), a)) := by
  rw [Cyl.partialEta_eq_fderiv (isCylTest_etaShiftTest hφ).differentiable,
    Cyl.partialEta_eq_fderiv hφ.differentiable]
  have hcomp := fderiv_comp_add_right (𝕜 := ℝ) (f := φ) (x := z) ((0 : ℝ), a)
  have h := congrArg (fun D => D ((0 : ℝ), (1 : ℝ))) hcomp
  change fderiv ℝ (fun x => φ (x + ((0 : ℝ), a))) z ((0 : ℝ), (1 : ℝ)) =
    fderiv ℝ φ (z + ((0 : ℝ), a)) ((0 : ℝ), (1 : ℝ))
  exact h

/-- Vertical translation commutes with the test-gradient classes. -/
theorem etaShiftL2_gradL {c a : ℝ} {φ : Plane → ℝ} (hφ : Sob.IsCylTest c φ) :
    etaShiftL2 c a (Cyl.gradL hφ) = Cyl.gradL (isCylTest_etaShiftTest (a := a) hφ) := by
  apply Lp.ext
  have hshift := etaShiftL2_ae (c := c) (a := a) (Cyl.gradL hφ)
  have hfrom := (measurePreserving_etaShift c a).quasiMeasurePreserving.ae
    (Cyl.memLp_gradT hφ).coeFn_toLp
  have hto := (Cyl.memLp_gradT (isCylTest_etaShiftTest (a := a) hφ)).coeFn_toLp
  filter_upwards [hshift, hfrom, hto] with z hzshift hfrom hto
  calc
    (etaShiftL2 c a (Cyl.gradL hφ) : Plane → Vec2) z =
        (Cyl.gradL hφ : Plane → Vec2) (z + ((0 : ℝ), a)) := hzshift
    _ = Cyl.gradT φ (z + ((0 : ℝ), a)) := hfrom
    _ = Cyl.gradT (etaShiftTest a φ) z := by
      symm
      ext i
      fin_cases i <;> simp [Cyl.gradT, Cyl.vec, etaShiftTest_partialQ hφ z,
        etaShiftTest_partialEta hφ z]
    _ = (Cyl.gradL (isCylTest_etaShiftTest (a := a) hφ) : Plane → Vec2) z := hto.symm

/-- Opposite vertical translations are inverse maps on the cylinder L² quotient. -/
theorem etaShiftL2_neg_comp {c a : ℝ} (u : Cyl.L2v c) :
    etaShiftL2 c (-a) (etaShiftL2 c a u) = u := by
  apply Lp.ext
  have houter := etaShiftL2_ae (c := c) (a := -a) (etaShiftL2 c a u)
  have hinner := (measurePreserving_etaShift c (-a)).quasiMeasurePreserving.ae
    (etaShiftL2_ae (c := c) (a := a) u)
  filter_upwards [houter, hinner] with z hzouter hzinner
  calc
    (etaShiftL2 c (-a) (etaShiftL2 c a u) : Plane → Vec2) z =
        (etaShiftL2 c a u : Plane → Vec2) (z + ((0 : ℝ), -a)) := hzouter
    _ = u ((z + ((0 : ℝ), -a)) + ((0 : ℝ), a)) := hzinner
    _ = u z := by congr 1 <;> ext <;> simp

/-- Vertical translation is onto, with the opposite shift as its inverse. -/
theorem etaShiftL2_surjective {c a : ℝ} : Function.Surjective (etaShiftL2 c a) := by
  intro u
  refine ⟨etaShiftL2 c (-a) u, ?_⟩
  simpa [neg_neg] using (etaShiftL2_neg_comp (c := c) (a := -a) u)

/-- The vertical L² shift preserves the weakly divergence-free subspace. -/
theorem etaShiftL2_mem_divFree {c a : ℝ} {u : Cyl.L2v c}
    (hu : u ∈ Cyl.divFree c) : etaShiftL2 c a u ∈ Cyl.divFree c := by
  rw [Cyl.mem_divFree] at hu ⊢
  intro φ hφ
  let hψ := isCylTest_etaShiftTest (a := -a) hφ
  calc
    inner ℝ (Cyl.gradL hφ) (etaShiftL2 c a u) =
        inner ℝ (etaShiftL2 c (-a) (Cyl.gradL hφ))
          (etaShiftL2 c (-a) (etaShiftL2 c a u)) := by
            symm
            exact (etaShiftL2 c (-a)).inner_map_map (Cyl.gradL hφ) (etaShiftL2 c a u)
    _ = inner ℝ (Cyl.gradL hψ) u := by
          rw [etaShiftL2_gradL, etaShiftL2_neg_comp]
    _ = 0 := hu _ hψ

/-- The vertical shift maps the solenoidal subspace onto itself. -/
theorem etaShiftL2_map_divFree_eq {c a : ℝ} :
    Submodule.map (etaShiftL2 c a).toLinearMap (Cyl.divFree c) = Cyl.divFree c := by
  apply le_antisymm
  · intro u hu
    rcases Submodule.mem_map.1 hu with ⟨v, hv, hvu⟩
    rw [← hvu]
    exact etaShiftL2_mem_divFree hv
  · intro u hu
    refine Submodule.mem_map.2 ⟨etaShiftL2 c (-a) u,
      etaShiftL2_mem_divFree (a := -a) hu, ?_⟩
    simpa [neg_neg] using (etaShiftL2_neg_comp (c := c) (a := -a) u)

/-- The actual Leray projector commutes with vertical translation on cylinder L². -/
theorem etaShiftL2_P0_comm {c a : ℝ} (u : Cyl.L2v c) :
    etaShiftL2 c a (Cyl.P0 c u) = Cyl.P0 c (etaShiftL2 c a u) := by
  apply (Cyl.P0_eq_of_orthogonal (etaShiftL2_mem_divFree (Cyl.P0_mem u)) ?_).symm
  have hsub : etaShiftL2 c a u - etaShiftL2 c a (Cyl.P0 c u) =
      etaShiftL2 c a (u - Cyl.P0 c u) := (etaShiftL2 c a).map_sub _ _ |>.symm
  rw [hsub]
  intro w hw
  have hshiftw : etaShiftL2 c (-a) w ∈ Cyl.divFree c :=
    etaShiftL2_mem_divFree (a := -a) hw
  have hinv : etaShiftL2 c a (etaShiftL2 c (-a) w) = w := by
    simpa [neg_neg] using (etaShiftL2_neg_comp (c := c) (a := -a) w)
  have horth := Cyl.sub_P0_mem_orthogonal u (etaShiftL2 c (-a) w) hshiftw
  have hinner := (etaShiftL2 c a).inner_map_map (etaShiftL2 c (-a) w)
    (u - Cyl.P0 c u)
  calc
    inner ℝ w (etaShiftL2 c a (u - Cyl.P0 c u)) =
        inner ℝ (etaShiftL2 c a (etaShiftL2 c (-a) w))
          (etaShiftL2 c a (u - Cyl.P0 c u)) := by rw [hinv]
    _ = inner ℝ (etaShiftL2 c (-a) w) (u - Cyl.P0 c u) := hinner
    _ = 0 := horth



#print axioms UnforcedLeray.TrainB.measurePreserving_etaShift
#print axioms UnforcedLeray.TrainB.etaShiftL2
#print axioms UnforcedLeray.TrainB.etaShiftL2_ae
#print axioms UnforcedLeray.TrainB.isCylTest_etaShiftTest
#print axioms UnforcedLeray.TrainB.etaShiftTest_partialQ
#print axioms UnforcedLeray.TrainB.etaShiftTest_partialEta
#print axioms UnforcedLeray.TrainB.etaShiftL2_gradL
#print axioms UnforcedLeray.TrainB.etaShiftL2_mem_divFree
#print axioms UnforcedLeray.TrainB.etaShiftL2_map_divFree_eq
#print axioms UnforcedLeray.TrainB.etaShiftL2_P0_comm
#print axioms UnforcedLeray.TrainB.etaShiftL2_neg_comp
#print axioms UnforcedLeray.TrainB.etaShiftL2_surjective

end UnforcedLeray.TrainB
