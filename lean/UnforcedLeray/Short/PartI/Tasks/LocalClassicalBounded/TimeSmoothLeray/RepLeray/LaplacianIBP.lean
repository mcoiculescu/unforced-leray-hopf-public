import UnforcedLeray.Short.PartI.Sub.T02_1_4_6
import UnforcedLeray.Lib.Cylinder.IBP
import UnforcedLeray.Lib.Train.Ops

/-!
# Part I, task `PartI:T02/1/4/6`, leaf R6: double integration by parts against a periodic test

Source of record: `the November 2 reference manuscript`, lines 261-288.
Target: `laplacianIBP : LaplacianIBP` (`Short/PartI/Sub/T02_1_4_6.lean`, leaf R6).

Proof. Split the vector pairing into its two components. For each scalar component `f = v_i`
and `g = φ_i`, apply `Cyl.integral_cell_partialQ_mul` twice in `q` and
`Cyl.integral_cell_partialEta_mul` twice in `η`. Every product in these identities has a factor
that vanishes for `|η|` large (`g` or one of its partial derivatives), and both factors are
continuous, so each integrability side condition is `leafR6_integrable`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.Cyl (Plane)

/-! ### Smoothness, vanishing and integrability of scalar derivatives -/

theorem leafR6_cd_partialQ {F : Plane → ℝ} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (Cyl.partialQ F) := by
  have h : Cyl.partialQ F = fun w => fderiv ℝ F w (1, 0) :=
    funext fun w => Cyl.partialQ_eq_fderiv (hF.differentiable (by simp)) w
  rw [h]
  exact (hF.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem leafR6_cd_partialEta {F : Plane → ℝ} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (Cyl.partialEta F) := by
  have h : Cyl.partialEta F = fun w => fderiv ℝ F w (0, 1) :=
    funext fun w => Cyl.partialEta_eq_fderiv (hF.differentiable (by simp)) w
  rw [h]
  exact (hF.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem leafR6_cd_lapS {F : Plane → ℝ} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (Train.lapS F) :=
  (leafR6_cd_partialQ (leafR6_cd_partialQ hF)).add
    (leafR6_cd_partialEta (leafR6_cd_partialEta hF))

theorem leafR6_vanish_lapS {R : ℝ} {F : Plane → ℝ} (hF : Cyl.VanishesOutside R F) :
    Cyl.VanishesOutside R (Train.lapS F) := by
  intro z hz
  unfold Train.lapS
  rw [hF.partialQ.partialQ z hz, hF.partialEta.partialEta z hz, add_zero]

/-- A product of two continuous functions, one of which vanishes for `|η|` large, is integrable
on the cell. -/
theorem leafR6_integrable {c R : ℝ} {a b : Plane → ℝ} (ha : Continuous a) (hb : Continuous b)
    (hbR : Cyl.VanishesOutside R b) :
    IntegrableOn (fun z => a z * b z) (Cyl.cell c) :=
  (hbR.mul_left a).integrableOn_cell (ha.mul hb) c

/-! ### Vector pairing and components -/

theorem leafR6_inner (x y : Vec) : inner ℝ x y = x 0 * y 0 + x 1 * y 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two, mul_comm]

theorem leafR6_comp_cd {v : Plane → Vec} (hv : ContDiff ℝ ∞ v) (i : Fin 2) :
    ContDiff ℝ ∞ fun z => v z i := by
  fun_prop

theorem leafR6_comp_periodic {c : ℝ} {v : Plane → Vec} (hv : Cyl.IsPeriodic c v) (i : Fin 2) :
    Cyl.IsPeriodic c fun z => v z i :=
  fun z => congrArg (fun x : Vec => x i) (hv z)

theorem leafR6_comp_vanish {R : ℝ} {φ : Plane → Vec}
    (hφ : ∀ z : Plane, R < |z.2| → φ z = 0) (i : Fin 2) :
    Cyl.VanishesOutside R fun z => φ z i :=
  fun z hz => by simp [hφ z hz]

/-! ### The scalar identity -/

/-- Double integration by parts for one component: `∫ f Δg = ∫ (Δf) g` on the cell, for smooth
periodic `f`, `g` with `g` vanishing for `|η|` large. -/
theorem leafR6_scalar {c R : ℝ} (hc : 0 < c) {f g : Plane → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hfp : Cyl.IsPeriodic c f) (hgp : Cyl.IsPeriodic c g) (hgR : Cyl.VanishesOutside R g) :
    ∫ z in Cyl.cell c, f z * Train.lapS g z = ∫ z in Cyl.cell c, Train.lapS f z * g z := by
  -- differentiability
  have dF : Differentiable ℝ f := hf.differentiable (by simp)
  have dG : Differentiable ℝ g := hg.differentiable (by simp)
  have dQF : Differentiable ℝ (Cyl.partialQ f) := (leafR6_cd_partialQ hf).differentiable (by simp)
  have dQG : Differentiable ℝ (Cyl.partialQ g) := (leafR6_cd_partialQ hg).differentiable (by simp)
  have dEF : Differentiable ℝ (Cyl.partialEta f) :=
    (leafR6_cd_partialEta hf).differentiable (by simp)
  have dEG : Differentiable ℝ (Cyl.partialEta g) :=
    (leafR6_cd_partialEta hg).differentiable (by simp)
  -- continuity
  have cF : Continuous f := hf.continuous
  have cG : Continuous g := hg.continuous
  have cQF : Continuous (Cyl.partialQ f) := (leafR6_cd_partialQ hf).continuous
  have cQG : Continuous (Cyl.partialQ g) := (leafR6_cd_partialQ hg).continuous
  have cEF : Continuous (Cyl.partialEta f) := (leafR6_cd_partialEta hf).continuous
  have cEG : Continuous (Cyl.partialEta g) := (leafR6_cd_partialEta hg).continuous
  have cQQF : Continuous (Cyl.partialQ (Cyl.partialQ f)) :=
    (leafR6_cd_partialQ (leafR6_cd_partialQ hf)).continuous
  have cQQG : Continuous (Cyl.partialQ (Cyl.partialQ g)) :=
    (leafR6_cd_partialQ (leafR6_cd_partialQ hg)).continuous
  have cEEF : Continuous (Cyl.partialEta (Cyl.partialEta f)) :=
    (leafR6_cd_partialEta (leafR6_cd_partialEta hf)).continuous
  have cEEG : Continuous (Cyl.partialEta (Cyl.partialEta g)) :=
    (leafR6_cd_partialEta (leafR6_cd_partialEta hg)).continuous
  -- vanishing for |η| large (the test function `g` has compact η-support)
  have vQG : Cyl.VanishesOutside R (Cyl.partialQ g) := hgR.partialQ
  have vEG : Cyl.VanishesOutside R (Cyl.partialEta g) := hgR.partialEta
  have vQQG : Cyl.VanishesOutside R (Cyl.partialQ (Cyl.partialQ g)) := vQG.partialQ
  have vEEG : Cyl.VanishesOutside R (Cyl.partialEta (Cyl.partialEta g)) := vEG.partialEta
  -- q-direction: ∫ ∂qf ∂qg = -∫ f ∂q²g and ∫ ∂q²f g = -∫ ∂qf ∂qg
  have hA : ∫ z in Cyl.cell c, Cyl.partialQ f z * Cyl.partialQ g z
      = -∫ z in Cyl.cell c, f z * Cyl.partialQ (Cyl.partialQ g) z :=
    Cyl.integral_cell_partialQ_mul hc dF dQG hfp hgp.partialQ
      (leafR6_integrable cQF cQG vQG) (leafR6_integrable cF cQQG vQQG)
  have hB : ∫ z in Cyl.cell c, Cyl.partialQ (Cyl.partialQ f) z * g z
      = -∫ z in Cyl.cell c, Cyl.partialQ f z * Cyl.partialQ g z :=
    Cyl.integral_cell_partialQ_mul hc dQF dG hfp.partialQ hgp
      (leafR6_integrable cQQF cG hgR) (leafR6_integrable cQF cQG vQG)
  have hQ : ∫ z in Cyl.cell c, f z * Cyl.partialQ (Cyl.partialQ g) z
      = ∫ z in Cyl.cell c, Cyl.partialQ (Cyl.partialQ f) z * g z := by
    linarith
  -- η-direction: ∫ ∂ηf ∂ηg = -∫ f ∂η²g and ∫ ∂η²f g = -∫ ∂ηf ∂ηg
  have hE1 : ∫ z in Cyl.cell c, Cyl.partialEta f z * Cyl.partialEta g z
      = -∫ z in Cyl.cell c, f z * Cyl.partialEta (Cyl.partialEta g) z :=
    Cyl.integral_cell_partialEta_mul dF dEG
      (leafR6_integrable cF cEG vEG) (leafR6_integrable cEF cEG vEG)
      (leafR6_integrable cF cEEG vEEG)
  have hE2 : ∫ z in Cyl.cell c, Cyl.partialEta (Cyl.partialEta f) z * g z
      = -∫ z in Cyl.cell c, Cyl.partialEta f z * Cyl.partialEta g z :=
    Cyl.integral_cell_partialEta_mul dEF dG
      (leafR6_integrable cEF cG hgR) (leafR6_integrable cEEF cG hgR)
      (leafR6_integrable cEF cEG vEG)
  have hE : ∫ z in Cyl.cell c, f z * Cyl.partialEta (Cyl.partialEta g) z
      = ∫ z in Cyl.cell c, Cyl.partialEta (Cyl.partialEta f) z * g z := by
    linarith
  -- splitting Δ = ∂q² + ∂η² on both sides
  have IL1 : IntegrableOn (fun z => f z * Cyl.partialQ (Cyl.partialQ g) z) (Cyl.cell c) :=
    leafR6_integrable cF cQQG vQQG
  have IL2 : IntegrableOn (fun z => f z * Cyl.partialEta (Cyl.partialEta g) z) (Cyl.cell c) :=
    leafR6_integrable cF cEEG vEEG
  have IR1 : IntegrableOn (fun z => Cyl.partialQ (Cyl.partialQ f) z * g z) (Cyl.cell c) :=
    leafR6_integrable cQQF cG hgR
  have IR2 : IntegrableOn (fun z => Cyl.partialEta (Cyl.partialEta f) z * g z) (Cyl.cell c) :=
    leafR6_integrable cEEF cG hgR
  simp only [Train.lapS, mul_add, add_mul]
  rw [integral_add IL1 IL2, integral_add IR1 IR2, hQ, hE]

/-! ### The leaf -/

/-- **Leaf R6** (`LaplacianIBP`): double integration by parts against a periodic `η`-compact
test field, componentwise. -/
theorem laplacianIBP : LaplacianIBP := by
  unfold LaplacianIBP
  intro c hc v φ hv hvp hφ
  unfold IsCellTest at hφ
  obtain ⟨hφC, hφp, R, hφR⟩ := hφ
  have key1 : ∀ z : Plane, inner ℝ (v z) (Train.vecLaplacian φ z)
      = v z 0 * Train.lapS (fun w => φ w 0) z + v z 1 * Train.lapS (fun w => φ w 1) z := by
    intro z
    rw [leafR6_inner]
    rfl
  have key2 : ∀ z : Plane, inner ℝ (Train.vecLaplacian v z) (φ z)
      = Train.lapS (fun w => v w 0) z * φ z 0 + Train.lapS (fun w => v w 1) z * φ z 1 := by
    intro z
    rw [leafR6_inner]
    rfl
  simp only [key1, key2]
  -- components
  have hv0 : ContDiff ℝ ∞ fun z => v z 0 := leafR6_comp_cd hv 0
  have hv1 : ContDiff ℝ ∞ fun z => v z 1 := leafR6_comp_cd hv 1
  have hφ0 : ContDiff ℝ ∞ fun z => φ z 0 := leafR6_comp_cd hφC 0
  have hφ1 : ContDiff ℝ ∞ fun z => φ z 1 := leafR6_comp_cd hφC 1
  have hvp0 : Cyl.IsPeriodic c fun z => v z 0 := leafR6_comp_periodic hvp 0
  have hvp1 : Cyl.IsPeriodic c fun z => v z 1 := leafR6_comp_periodic hvp 1
  have hφp0 : Cyl.IsPeriodic c fun z => φ z 0 := leafR6_comp_periodic hφp 0
  have hφp1 : Cyl.IsPeriodic c fun z => φ z 1 := leafR6_comp_periodic hφp 1
  have hR0 : Cyl.VanishesOutside R fun z => φ z 0 := leafR6_comp_vanish hφR 0
  have hR1 : Cyl.VanishesOutside R fun z => φ z 1 := leafR6_comp_vanish hφR 1
  -- scalar identities
  have S0 : ∫ z in Cyl.cell c, v z 0 * Train.lapS (fun w => φ w 0) z
      = ∫ z in Cyl.cell c, Train.lapS (fun w => v w 0) z * φ z 0 :=
    leafR6_scalar hc hv0 hφ0 hvp0 hφp0 hR0
  have S1 : ∫ z in Cyl.cell c, v z 1 * Train.lapS (fun w => φ w 1) z
      = ∫ z in Cyl.cell c, Train.lapS (fun w => v w 1) z * φ z 1 :=
    leafR6_scalar hc hv1 hφ1 hvp1 hφp1 hR1
  -- integrability of the four component products
  have I0 : IntegrableOn (fun z => v z 0 * Train.lapS (fun w => φ w 0) z) (Cyl.cell c) :=
    leafR6_integrable hv0.continuous (leafR6_cd_lapS hφ0).continuous (leafR6_vanish_lapS hR0)
  have I1 : IntegrableOn (fun z => v z 1 * Train.lapS (fun w => φ w 1) z) (Cyl.cell c) :=
    leafR6_integrable hv1.continuous (leafR6_cd_lapS hφ1).continuous (leafR6_vanish_lapS hR1)
  have J0 : IntegrableOn (fun z => Train.lapS (fun w => v w 0) z * φ z 0) (Cyl.cell c) :=
    leafR6_integrable (leafR6_cd_lapS hv0).continuous hφ0.continuous hR0
  have J1 : IntegrableOn (fun z => Train.lapS (fun w => v w 1) z * φ z 1) (Cyl.cell c) :=
    leafR6_integrable (leafR6_cd_lapS hv1).continuous hφ1.continuous hR1
  rw [integral_add I0 I1, integral_add J0 J1, S0, S1]

end UnforcedLeray.Short.PartI
