import UnforcedLeray.Lib.TrainB.Embedding
import UnforcedLeray.Lib.CylinderB.Space
import UnforcedLeray.Lib.SobolevC.CylTransfer
import UnforcedLeray.Lib.SobolevC.CylDensity

/-!
# Weak H²-to-bounded-continuous embedding on the train cylinder

The construction uses smooth density, the centered-cell smooth estimate, and the infinite-measure
Lp subsequence theorem to identify the uniform limit with the Sobolev value.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology ContDiff BoundedContinuousFunction

namespace UnforcedLeray.TrainB

open UnforcedLeray.GaussianVortex (Plane partialX partialY)

abbrev ScalarH2 (c : ℝ) := UnforcedLeray.Cyl.H ℝ ℝ c 0 2

/-- At weight exponent zero, the H² value measure is exactly the unnormalized centered cell. -/
theorem scalarH2_measure_eq_cell (c : ℝ) :
    UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) = UnforcedLeray.Cyl.cellμ c := by
  rw [UnforcedLeray.Cyl.wμ_ρwW]
  simp [UnforcedLeray.Cyl.wμ]

/-- Reinterpret the scalar H² field class on the centered cell. -/
def scalarH2Value {c : ℝ} (x : ScalarH2 c) : Lp ℝ 2 (UnforcedLeray.Cyl.cellμ c) :=
  have htype :
      ↥(Lp ℝ 2 (UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)))) = ↥(Lp ℝ 2 (UnforcedLeray.Cyl.cellμ c)) := by
    rw [scalarH2_measure_eq_cell]
  htype ▸ UnforcedLeray.Cyl.H.val x

/-- Every classical derivative of a smooth compact-axial cylinder field is in the centered-cell
L² space. -/
theorem memLp_iterD_cell {c : ℝ} {f : Plane → ℝ} (hf : UnforcedLeray.Sob.IsCylSmooth c f)
    (vs : List Plane) : MemLp (UnforcedLeray.Sob.iterD vs f) 2 (UnforcedLeray.Cyl.cellμ c) := by
  have hmem := (hf.iterD vs).memLp (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) 2
  simpa only [scalarH2_measure_eq_cell] using hmem

/-- The first classical coordinate derivatives agree with the corresponding Sobolev derivative
words of a smooth field. -/
theorem iterD_q_eq_partialX {c : ℝ} {f : Plane → ℝ}
    (hf : UnforcedLeray.Sob.IsCylSmooth c f) :
    UnforcedLeray.Sob.iterD [(1, 0)] f = partialX f := by
  funext z
  have hd : Differentiable ℝ f := hf.smooth.differentiable (by simp)
  simp [UnforcedLeray.Sob.iterD, UnforcedLeray.B0151.partialX_eq_fderiv hd]

/-- The other first classical coordinate derivative has the same agreement. -/
theorem iterD_eta_eq_partialY {c : ℝ} {f : Plane → ℝ}
    (hf : UnforcedLeray.Sob.IsCylSmooth c f) :
    UnforcedLeray.Sob.iterD [(0, 1)] f = partialY f := by
  funext z
  have hd : Differentiable ℝ f := hf.smooth.differentiable (by simp)
  simp [UnforcedLeray.Sob.iterD, UnforcedLeray.B0151.partialY_eq_fderiv hd]

/-- The mixed derivative word `∂η∂q` agrees with the B0151 partial derivative notation. -/
theorem iterD_eta_q_eq_partialY_partialX {c : ℝ} {f : Plane → ℝ}
    (hf : UnforcedLeray.Sob.IsCylSmooth c f) :
    UnforcedLeray.Sob.iterD [(0, 1), (1, 0)] f = partialY (partialX f) := by
  funext z
  have hdf : Differentiable ℝ f := hf.smooth.differentiable (by simp)
  have hdq : Differentiable ℝ (partialX f) :=
    (UnforcedLeray.B0151.contDiff_partialX_infty hf.smooth).differentiable (by simp)
  have heq : (fun x => fderiv ℝ f x (1, 0)) = partialX f :=
    funext fun x => (UnforcedLeray.B0151.partialX_eq_fderiv hdf x).symm
  simp [UnforcedLeray.Sob.iterD, heq, UnforcedLeray.B0151.partialY_eq_fderiv hdq]

/-- The four L² hypotheses needed by the smooth H² bound follow from the smooth cylinder
representative's derivative-word MemLp facts. -/
theorem smooth_H2_memLp_data {c : ℝ} {f : Plane → ℝ}
    (hf : UnforcedLeray.Sob.IsCylSmooth c f) :
    MemLp f 2 (UnforcedLeray.Cyl.cellμ c) ∧
    MemLp (partialX f) 2 (UnforcedLeray.Cyl.cellμ c) ∧
    MemLp (partialY f) 2 (UnforcedLeray.Cyl.cellμ c) ∧
    MemLp (partialY (partialX f)) 2 (UnforcedLeray.Cyl.cellμ c) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [UnforcedLeray.Sob.iterD] using memLp_iterD_cell hf []
  · simpa only [← iterD_q_eq_partialX hf] using memLp_iterD_cell hf [(1, 0)]
  · simpa only [← iterD_eta_eq_partialY hf] using memLp_iterD_cell hf [(0, 1)]
  · simpa only [← iterD_eta_q_eq_partialY_partialX hf] using
      memLp_iterD_cell hf [(0, 1), (1, 0)]

/-- The smooth B0151 estimate applies to every compact-axial periodic smooth representative. -/
theorem smooth_cyl_H2_bound {c : ℝ} (hc1 : 1 ≤ c) {f : Plane → ℝ}
    (hf : UnforcedLeray.Sob.IsCylSmooth c f) (z : Plane) :
    ‖f z‖ₑ ≤ 3 * (eLpNorm f 2 (UnforcedLeray.Cyl.cellμ c) +
      eLpNorm (partialX f) 2 (UnforcedLeray.Cyl.cellμ c) +
      eLpNorm (partialY f) 2 (UnforcedLeray.Cyl.cellμ c) +
      eLpNorm (partialY (partialX f)) 2 (UnforcedLeray.Cyl.cellμ c)) := by
  have hf2 : ContDiff ℝ 2 f := hf.smooth.of_le (by norm_num)
  have hper : UnforcedLeray.Cyl.IsPeriodic c f := by
    intro z
    rcases z with ⟨x, y⟩
    simpa using hf.periodic (x, y)
  obtain ⟨h0, hq, hη, hqη⟩ := smooth_H2_memLp_data hf
  exact smooth_H2_enorm_le_cell hc1 hf2 hper h0 hq hη hqη z

/-- Every compact-axial smooth periodic field defines a bounded continuous function, with its
global bound supplied by the centered-cell H² estimate. -/
theorem exists_smooth_bcf {c : ℝ} (hc1 : 1 ≤ c) {f : Plane → ℝ}
    (hf : UnforcedLeray.Sob.IsCylSmooth c f) :
    ∃ F : Plane →ᵇ ℝ, ∀ z, F z = f z := by
  obtain ⟨h0, hq, hη, hqη⟩ := smooth_H2_memLp_data hf
  let E : ℝ≥0∞ := 3 * (eLpNorm f 2 (UnforcedLeray.Cyl.cellμ c) +
    eLpNorm (partialX f) 2 (UnforcedLeray.Cyl.cellμ c) +
    eLpNorm (partialY f) 2 (UnforcedLeray.Cyl.cellμ c) +
    eLpNorm (partialY (partialX f)) 2 (UnforcedLeray.Cyl.cellμ c))
  have hsum : (eLpNorm f 2 (UnforcedLeray.Cyl.cellμ c) +
      eLpNorm (partialX f) 2 (UnforcedLeray.Cyl.cellμ c) +
      eLpNorm (partialY f) 2 (UnforcedLeray.Cyl.cellμ c) +
      eLpNorm (partialY (partialX f)) 2 (UnforcedLeray.Cyl.cellμ c)) ≠ ⊤ := by
    have hab : eLpNorm f 2 (UnforcedLeray.Cyl.cellμ c) +
        eLpNorm (partialX f) 2 (UnforcedLeray.Cyl.cellμ c) ≠ ⊤ :=
      ENNReal.add_ne_top.mpr ⟨h0.eLpNorm_ne_top, hq.eLpNorm_ne_top⟩
    have habc : eLpNorm f 2 (UnforcedLeray.Cyl.cellμ c) +
        eLpNorm (partialX f) 2 (UnforcedLeray.Cyl.cellμ c) +
        eLpNorm (partialY f) 2 (UnforcedLeray.Cyl.cellμ c) ≠ ⊤ :=
      ENNReal.add_ne_top.mpr ⟨hab, hη.eLpNorm_ne_top⟩
    apply ENNReal.add_ne_top.mpr
    exact ⟨habc, hqη.eLpNorm_ne_top⟩
  have hE : E ≠ ⊤ := by
    dsimp [E]
    exact ENNReal.mul_ne_top ENNReal.ofNat_ne_top hsum
  refine ⟨BoundedContinuousFunction.ofNormedAddCommGroup f hf.smooth.continuous E.toReal ?_, ?_⟩
  · intro z
    have h := smooth_cyl_H2_bound hc1 hf z
    have hr := ENNReal.toReal_mono hE h
    rwa [toReal_enorm] at hr
  · intro z
    rfl

/-- A smooth derivative word is controlled by the Sobolev norm of the smooth class. -/
theorem smooth_iterD_eLp_le_h2norm {c : ℝ} (hc : 0 < c) {f : Plane → ℝ}
    (hf : UnforcedLeray.Sob.IsCylSmooth c f) (vs : List Plane)
    (α : UnforcedLeray.Sob.Idx 2 2)
    (hword : (UnforcedLeray.Sob.cylinder c).word α = vs) :
    eLpNorm (UnforcedLeray.Sob.iterD vs f) 2 (UnforcedLeray.Cyl.cellμ c) ≤
      ENNReal.ofReal ‖UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := ℝ) (k := 2) (p := 2)
        (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) hc f hf‖ := by
  let x := UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := ℝ) (k := 2) (p := 2)
    (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) hc f hf
  rw [← hword, ← scalarH2_measure_eq_cell]
  rw [eLpNorm_congr_ae (UnforcedLeray.Sob.W.deriv_ofCylSmooth
    (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ) (F := ℝ) (k := 2) (p := 2)
    hc f hf α).symm]
  have hcomp : ‖UnforcedLeray.Sob.W.deriv (UnforcedLeray.Sob.cylinder c)
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ ℝ 2 2 α x‖ ≤ ‖x‖ := by
    change ‖((x : UnforcedLeray.Sob.SobTuple (UnforcedLeray.Sob.cylinder c)
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ 2 2).ofLp α)‖ ≤ ‖x‖
    exact PiLp.norm_apply_le _ _
  have hfin := (Lp.memLp (UnforcedLeray.Sob.W.deriv
    (UnforcedLeray.Sob.cylinder c) (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ ℝ 2 2 α x)).eLpNorm_ne_top
  calc
    eLpNorm (⇑(UnforcedLeray.Sob.W.deriv (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ ℝ 2 2 α x) : Plane → ℝ) 2
        (UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
          (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))) =
      ENNReal.ofReal ‖UnforcedLeray.Sob.W.deriv (UnforcedLeray.Sob.cylinder c)
          (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ ℝ 2 2 α x‖ := by
        rw [← ENNReal.ofReal_toReal hfin, Lp.norm_def]
    _ ≤ ENNReal.ofReal ‖x‖ := ENNReal.ofReal_le_ofReal hcomp

/-- The order-three version of the smooth derivative-component estimate. -/
theorem smooth_iterD_eLp_le_h3norm {c : ℝ} (hc : 0 < c) {f : Plane → ℝ}
    (hf : UnforcedLeray.Sob.IsCylSmooth c f) (vs : List Plane)
    (α : UnforcedLeray.Sob.Idx 2 3)
    (hword : (UnforcedLeray.Sob.cylinder c).word α = vs) :
    eLpNorm (UnforcedLeray.Sob.iterD vs f) 2 (UnforcedLeray.Cyl.cellμ c) ≤
      ENNReal.ofReal ‖UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := ℝ) (k := 3) (p := 2)
        (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) hc f hf‖ := by
  let x := UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := ℝ) (k := 3) (p := 2)
    (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) hc f hf
  rw [← hword, ← scalarH2_measure_eq_cell]
  rw [eLpNorm_congr_ae (UnforcedLeray.Sob.W.deriv_ofCylSmooth
    (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ) (F := ℝ) (k := 3) (p := 2)
    hc f hf α).symm]
  have hcomp : ‖UnforcedLeray.Sob.W.deriv (UnforcedLeray.Sob.cylinder c)
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ ℝ 3 2 α x‖ ≤ ‖x‖ := by
    change ‖((x : UnforcedLeray.Sob.SobTuple (UnforcedLeray.Sob.cylinder c)
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ 3 2).ofLp α)‖ ≤ ‖x‖
    exact PiLp.norm_apply_le _ _
  have hfin := (Lp.memLp (UnforcedLeray.Sob.W.deriv
    (UnforcedLeray.Sob.cylinder c) (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ ℝ 3 2 α x)).eLpNorm_ne_top
  calc
    eLpNorm (⇑(UnforcedLeray.Sob.W.deriv (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ ℝ 3 2 α x) : Plane → ℝ) 2
        (UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
          (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))) =
      ENNReal.ofReal ‖UnforcedLeray.Sob.W.deriv (UnforcedLeray.Sob.cylinder c)
          (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ ℝ 3 2 α x‖ := by
        rw [← ENNReal.ofReal_toReal hfin, Lp.norm_def]
    _ ≤ ENNReal.ofReal ‖x‖ := ENNReal.ofReal_le_ofReal hcomp

/-- The B0151 derivative words viewed as lists of actual cylinder directions. -/
def b0151WordPlane : List Bool → List Plane
  | [] => []
  | true :: w => (1, 0) :: b0151WordPlane w
  | false :: w => (0, 1) :: b0151WordPlane w

def b0151WordFin : List Bool → List (Fin 2)
  | [] => []
  | true :: w => 0 :: b0151WordFin w
  | false :: w => 1 :: b0151WordFin w

/-- B0151's recursive partial notation is exactly the smooth Sobolev derivative word. -/
theorem b0151_derivWord_eq_iterD {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f) (w : List Bool) :
    UnforcedLeray.B0151.derivWord w f =
      UnforcedLeray.Sob.iterD (b0151WordPlane w) f := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    cases b
    · simp only [UnforcedLeray.B0151.derivWord, b0151WordPlane]
      funext z
      rw [ih]
      have hd : Differentiable ℝ (UnforcedLeray.Sob.iterD (b0151WordPlane w) f) :=
        (UnforcedLeray.Sob.contDiff_iterD hf (b0151WordPlane w)).differentiable (by simp)
      exact UnforcedLeray.B0151.partialY_eq_fderiv hd z
    · simp only [UnforcedLeray.B0151.derivWord, b0151WordPlane]
      funext z
      rw [ih]
      have hd : Differentiable ℝ (UnforcedLeray.Sob.iterD (b0151WordPlane w) f) :=
        (UnforcedLeray.Sob.contDiff_iterD hf (b0151WordPlane w)).differentiable (by simp)
      exact UnforcedLeray.B0151.partialX_eq_fderiv hd z

theorem b0151WordFin_length (w : List Bool) : (b0151WordFin w).length = w.length := by
  induction w with
  | nil => rfl
  | cons b w ih => cases b <;> simp [b0151WordFin, ih]

theorem map_cylDir_b0151Word (w : List Bool) :
    (b0151WordFin w).map UnforcedLeray.Sob.cylDir = b0151WordPlane w := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    cases b <;>
      simp only [b0151WordFin, b0151WordPlane, List.map_cons] <;>
      rw [ih] <;> simp [UnforcedLeray.Sob.cylDir]

/-- The Sobolev cylinder index associated to a B0151 word has the matching direction list. -/
theorem cylinder_word_of_b0151Word {c : ℝ} (w : List Bool) (hw : w.length ≤ 3) :
    (UnforcedLeray.Sob.cylinder c).word
      (UnforcedLeray.Sob.Idx.ofList (b0151WordFin w)
        (by simpa only [b0151WordFin_length] using hw)) =
      b0151WordPlane w := by
  rw [UnforcedLeray.Sob.TestDomain.word_eq_map,
    UnforcedLeray.Sob.Idx.toList_ofList, UnforcedLeray.Sob.cylinder_dir]
  exact map_cylDir_b0151Word w

/-- Every B0151 derivative of order at most one is pointwise bounded by the H³ cylinder norm.
The four L² terms in its H² embedding are all controlled by distinct order-at-most-three
components of the same Sobolev class. -/
theorem smooth_h3_lowDerivative_enorm_bound {c : ℝ} (hc1 : 1 ≤ c) {f : Plane → ℝ}
    (hf : UnforcedLeray.Sob.IsCylSmooth c f) (w : List Bool) (hw : w.length ≤ 1)
    (z : Plane) :
    ‖UnforcedLeray.B0151.derivWord w f z‖ₑ ≤
      12 * ENNReal.ofReal ‖UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := ℝ)
        (k := 3) (p := 2) (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))
        (by linarith [hc1]) f hf‖ := by
  let hc : 0 < c := by linarith [hc1]
  let x := UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := ℝ) (k := 3) (p := 2)
    (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) hc f hf
  have hp0 : UnforcedLeray.B0151.IsPeriodicQ c f := by
    intro q η
    simpa [UnforcedLeray.B0151.IsPeriodicQ] using hf.periodic (q, η)
  have hper (v : List Bool) :
      UnforcedLeray.Cyl.IsPeriodic c (UnforcedLeray.B0151.derivWord v f) := by
    intro z
    rcases z with ⟨q, η⟩
    change UnforcedLeray.B0151.derivWord v f (q + c, η) =
      UnforcedLeray.B0151.derivWord v f (q, η)
    exact UnforcedLeray.B0151.periodic_derivWord hp0 v q η
  have hmeas (v : List Bool) :
      Measurable (UnforcedLeray.B0151.derivWord v f) :=
    (UnforcedLeray.B0151.contDiff_derivWord hf.smooth v).continuous.measurable
  have hterm : ∀ v : List Bool, v.length ≤ 3 →
      eLpNorm (UnforcedLeray.B0151.derivWord v f) 2 (UnforcedLeray.B0151.cellMeasure c) ≤
        ENNReal.ofReal ‖x‖ := by
    intro v hv
    let α : UnforcedLeray.Sob.Idx 2 3 := UnforcedLeray.Sob.Idx.ofList (b0151WordFin v)
      (by simpa only [b0151WordFin_length] using hv)
    have hwv : (UnforcedLeray.Sob.cylinder c).word α = b0151WordPlane v := by
      exact cylinder_word_of_b0151Word v hv
    have hcell := smooth_iterD_eLp_le_h3norm hc hf (b0151WordPlane v) α hwv
    rw [← b0151_derivWord_eq_iterD hf.smooth v] at hcell
    have hnormeq := eLpNorm_sq_b0151_eq_cyl hc (hmeas v) (hper v)
    exact hnormeq.trans_le (by simpa [x, hc] using hcell)
  have h0 : MemLp (UnforcedLeray.B0151.derivWord w f) 2
      (UnforcedLeray.B0151.cellMeasure c) := by
    apply memLp_b0151_of_cell hc (hmeas w) (hper w)
    rw [b0151_derivWord_eq_iterD hf.smooth w]
    exact memLp_iterD_cell hf (b0151WordPlane w)
  have hq : MemLp (UnforcedLeray.B0151.derivWord (true :: w) f) 2
      (UnforcedLeray.B0151.cellMeasure c) := by
    apply memLp_b0151_of_cell hc (hmeas (true :: w)) (hper (true :: w))
    rw [b0151_derivWord_eq_iterD hf.smooth (true :: w)]
    exact memLp_iterD_cell hf (b0151WordPlane (true :: w))
  have hη : MemLp (UnforcedLeray.B0151.derivWord (false :: w) f) 2
      (UnforcedLeray.B0151.cellMeasure c) := by
    apply memLp_b0151_of_cell hc (hmeas (false :: w)) (hper (false :: w))
    rw [b0151_derivWord_eq_iterD hf.smooth (false :: w)]
    exact memLp_iterD_cell hf (b0151WordPlane (false :: w))
  have hqη : MemLp (UnforcedLeray.B0151.derivWord (false :: true :: w) f) 2
      (UnforcedLeray.B0151.cellMeasure c) := by
    apply memLp_b0151_of_cell hc (hmeas (false :: true :: w))
      (hper (false :: true :: w))
    rw [b0151_derivWord_eq_iterD hf.smooth (false :: true :: w)]
    exact memLp_iterD_cell hf (b0151WordPlane (false :: true :: w))
  have hB := UnforcedLeray.B0151.enorm_derivWord_le hc1 hf.smooth hp0 w h0 hq hη hqη z
  have hsum :
      eLpNorm (UnforcedLeray.B0151.derivWord w f) 2 (UnforcedLeray.B0151.cellMeasure c) +
      eLpNorm (UnforcedLeray.B0151.derivWord (true :: w) f) 2
        (UnforcedLeray.B0151.cellMeasure c) +
      eLpNorm (UnforcedLeray.B0151.derivWord (false :: w) f) 2
        (UnforcedLeray.B0151.cellMeasure c) +
      eLpNorm (UnforcedLeray.B0151.derivWord (false :: true :: w) f) 2
        (UnforcedLeray.B0151.cellMeasure c) ≤ 4 * ENNReal.ofReal ‖x‖ := by
    calc
      _ ≤ ENNReal.ofReal ‖x‖ + ENNReal.ofReal ‖x‖ + ENNReal.ofReal ‖x‖ +
          ENNReal.ofReal ‖x‖ := by
            exact add_le_add (add_le_add (add_le_add
              (hterm w (by omega)) (hterm (true :: w) (by simp; omega)))
              (hterm (false :: w) (by simp; omega)))
              (hterm (false :: true :: w) (by simp; omega))
      _ = 4 * ENNReal.ofReal ‖x‖ := by ring
  calc
    ‖UnforcedLeray.B0151.derivWord w f z‖ₑ ≤ 3 * (eLpNorm _ 2 _ + eLpNorm _ 2 _ +
        eLpNorm _ 2 _ + eLpNorm _ 2 _) := hB
    _ ≤ 3 * (4 * ENNReal.ofReal ‖x‖) := by gcongr
    _ = 12 * ENNReal.ofReal ‖x‖ := by ring

/-- A smooth H³ derivative of order at most one is an L² multiplier, with its coefficient bounded
by the H³ norm. This is the low/high split estimate used termwise in the H³ Leibniz expansion. -/
theorem smooth_h3_lowDerivative_mul_L2 {c : ℝ} (hc1 : 1 ≤ c) {f g : Plane → ℝ}
    (hf : UnforcedLeray.Sob.IsCylSmooth c f) (w : List Bool) (hw : w.length ≤ 1) :
    eLpNorm (fun z => UnforcedLeray.B0151.derivWord w f z * g z) 2
        (UnforcedLeray.B0151.cellMeasure c) ≤
      ENNReal.ofReal (12 * ‖UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := ℝ)
        (k := 3) (p := 2) (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))
        (by linarith [hc1]) f hf‖) * eLpNorm g 2 (UnforcedLeray.B0151.cellMeasure c) := by
  have hc : 0 < c := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hc1
  let x := UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := ℝ) (k := 3) (p := 2)
    (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) hc f hf
  have hR : 12 * ENNReal.ofReal ‖x‖ ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofNat_ne_top ENNReal.ofReal_ne_top
  have hpoint : ∀ z, ‖UnforcedLeray.B0151.derivWord w f z‖ ≤ 12 * ‖x‖ := by
    intro z
    have h := ENNReal.toReal_mono hR (smooth_h3_lowDerivative_enorm_bound hc1 hf w hw z)
    simpa [x, hc, toReal_enorm, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (norm_nonneg _)] using h
  refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul (Eventually.of_forall fun z => ?_) 2
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hpoint z) (norm_nonneg _)

/-- The four classical terms in B0151's H² estimate are bounded by the norm of the smooth H²
class. -/
theorem smooth_H2_terms_le_norm {c : ℝ} (hc : 0 < c) {f : Plane → ℝ}
    (hf : UnforcedLeray.Sob.IsCylSmooth c f) :
    eLpNorm f 2 (UnforcedLeray.Cyl.cellμ c) ≤ ENNReal.ofReal ‖UnforcedLeray.Sob.W.ofCylSmooth
        (𝕜 := ℝ) (F := ℝ) (k := 2) (p := 2)
        (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) hc f hf‖ ∧
    eLpNorm (partialX f) 2 (UnforcedLeray.Cyl.cellμ c) ≤ ENNReal.ofReal ‖UnforcedLeray.Sob.W.ofCylSmooth
        (𝕜 := ℝ) (F := ℝ) (k := 2) (p := 2)
        (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) hc f hf‖ ∧
    eLpNorm (partialY f) 2 (UnforcedLeray.Cyl.cellμ c) ≤ ENNReal.ofReal ‖UnforcedLeray.Sob.W.ofCylSmooth
        (𝕜 := ℝ) (F := ℝ) (k := 2) (p := 2)
        (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) hc f hf‖ ∧
    eLpNorm (partialY (partialX f)) 2 (UnforcedLeray.Cyl.cellμ c) ≤ ENNReal.ofReal ‖UnforcedLeray.Sob.W.ofCylSmooth
        (𝕜 := ℝ) (F := ℝ) (k := 2) (p := 2)
        (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) hc f hf‖ := by
  let α0 : UnforcedLeray.Sob.Idx 2 2 := UnforcedLeray.Sob.Idx.zero
  let αq : UnforcedLeray.Sob.Idx 2 2 := UnforcedLeray.Sob.Idx.ofList [0] (by norm_num)
  let αη : UnforcedLeray.Sob.Idx 2 2 := UnforcedLeray.Sob.Idx.ofList [1] (by norm_num)
  let αηq : UnforcedLeray.Sob.Idx 2 2 := UnforcedLeray.Sob.Idx.ofList [1, 0] (by norm_num)
  have hw0 : (UnforcedLeray.Sob.cylinder c).word α0 = [] := by
    simp [α0, UnforcedLeray.Sob.TestDomain.word_eq_map]
  have hwq : (UnforcedLeray.Sob.cylinder c).word αq = [(1, 0)] := by
    simp [αq, UnforcedLeray.Sob.TestDomain.word_eq_map,
      UnforcedLeray.Sob.cylinder_dir, UnforcedLeray.Sob.cylDir]
  have hwη : (UnforcedLeray.Sob.cylinder c).word αη = [(0, 1)] := by
    simp [αη, UnforcedLeray.Sob.TestDomain.word_eq_map,
      UnforcedLeray.Sob.cylinder_dir, UnforcedLeray.Sob.cylDir]
  have hwηq : (UnforcedLeray.Sob.cylinder c).word αηq = [(0, 1), (1, 0)] := by
    simp [αηq, UnforcedLeray.Sob.TestDomain.word_eq_map,
      UnforcedLeray.Sob.cylinder_dir, UnforcedLeray.Sob.cylDir]
  have h0 := smooth_iterD_eLp_le_h2norm hc hf [] α0 hw0
  have hq := smooth_iterD_eLp_le_h2norm hc hf [(1, 0)] αq hwq
  have hη := smooth_iterD_eLp_le_h2norm hc hf [(0, 1)] αη hwη
  have hηq := smooth_iterD_eLp_le_h2norm hc hf [(0, 1), (1, 0)] αηq hwηq
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [UnforcedLeray.Sob.iterD] using h0
  · simpa only [← iterD_q_eq_partialX hf] using hq
  · simpa only [← iterD_eta_eq_partialY hf] using hη
  · simpa only [← iterD_eta_q_eq_partialY_partialX hf] using hηq

/-- The smooth periodic representative has a uniform bound by its genuine H² norm. -/
theorem smooth_cyl_sup_le_h2norm {c : ℝ} (hc1 : 1 ≤ c) {f : Plane → ℝ}
    (hf : UnforcedLeray.Sob.IsCylSmooth c f) (z : Plane) :
    ‖f z‖ ≤ 12 * ‖UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := ℝ) (k := 2) (p := 2)
      (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (by linarith [hc1]) f hf‖ := by
  let hc : 0 < c := by linarith [hc1]
  let x := UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := ℝ) (k := 2) (p := 2)
    (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) hc f hf
  let A := eLpNorm f 2 (UnforcedLeray.Cyl.cellμ c)
  let B := eLpNorm (partialX f) 2 (UnforcedLeray.Cyl.cellμ c)
  let C := eLpNorm (partialY f) 2 (UnforcedLeray.Cyl.cellμ c)
  let D := eLpNorm (partialY (partialX f)) 2 (UnforcedLeray.Cyl.cellμ c)
  let E : ℝ≥0∞ := 3 * (A + B + C + D)
  obtain ⟨hA, hB, hC, hD⟩ := smooth_H2_terms_le_norm hc hf
  have hsum : A + B + C + D ≤ 4 * ENNReal.ofReal ‖x‖ := by
    dsimp [A, B, C, D]
    calc
      eLpNorm f 2 (UnforcedLeray.Cyl.cellμ c) + eLpNorm (partialX f) 2
          (UnforcedLeray.Cyl.cellμ c) + eLpNorm (partialY f) 2
          (UnforcedLeray.Cyl.cellμ c) + eLpNorm (partialY (partialX f)) 2
          (UnforcedLeray.Cyl.cellμ c) ≤ ENNReal.ofReal ‖x‖ + ENNReal.ofReal ‖x‖ +
            ENNReal.ofReal ‖x‖ + ENNReal.ofReal ‖x‖ := by
              exact add_le_add (add_le_add (add_le_add hA hB) hC) hD
      _ = 4 * ENNReal.ofReal ‖x‖ := by ring
  have hs : (A + B + C + D) ≠ ⊤ := by
    have ⟨h0, h1, h2, h3⟩ := smooth_H2_memLp_data hf
    simp only [A, B, C, D]
    apply ENNReal.add_ne_top.mpr
    apply And.intro
    · apply ENNReal.add_ne_top.mpr
      apply And.intro
      · exact ENNReal.add_ne_top.mpr ⟨h0.eLpNorm_ne_top, h1.eLpNorm_ne_top⟩
      · exact h2.eLpNorm_ne_top
    · exact h3.eLpNorm_ne_top
  have hE : E ≠ ⊤ := by
    dsimp [E]
    exact ENNReal.mul_ne_top ENNReal.ofNat_ne_top hs
  have hEbound : E ≤ 12 * ENNReal.ofReal ‖x‖ := by
    dsimp [E]
    calc
      3 * (A + B + C + D) ≤ 3 * (4 * ENNReal.ofReal ‖x‖) := by gcongr
      _ = 12 * ENNReal.ofReal ‖x‖ := by ring
  have hpoint : ‖f z‖ ≤ E.toReal := by
    have h := ENNReal.toReal_mono hE (smooth_cyl_H2_bound hc1 hf z)
    simpa [E, A, B, C, D, toReal_enorm] using h
  have hreal : E.toReal ≤ 12 * ‖x‖ := by
    have hR : 12 * ENNReal.ofReal ‖x‖ ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofNat_ne_top (ENNReal.ofReal_ne_top)
    have h := ENNReal.toReal_mono hR hEbound
    simpa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (norm_nonneg x)] using h
  dsimp [x, hc]
  exact hpoint.trans hreal

/-- Multiplication by a smooth H² cylinder field is bounded on cell L², with the coefficient
controlled by the actual Sobolev class. This is the low-order factor estimate used in H³ Leibniz
terms. -/
theorem smooth_multiplier_L2_bound {c : ℝ} (hc1 : 1 ≤ c) {f g : Plane → ℝ}
    (hf : UnforcedLeray.Sob.IsCylSmooth c f) :
    eLpNorm (fun z => f z * g z) 2 (UnforcedLeray.Cyl.cellμ c) ≤
      ENNReal.ofReal (12 * ‖UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := ℝ)
        (k := 2) (p := 2) (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))
        (by linarith [hc1]) f hf‖) * eLpNorm g 2 (UnforcedLeray.Cyl.cellμ c) := by
  have hpoint : ∀ z, ‖f z‖ ≤ 12 * ‖UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ)
      (F := ℝ) (k := 2) (p := 2) (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))
      (by linarith [hc1]) f hf‖ := fun z => smooth_cyl_sup_le_h2norm hc1 hf z
  refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul (Eventually.of_forall fun z => ?_) 2
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hpoint z) (norm_nonneg _)

/-- Smooth periodic compact-axial fields are closed under subtraction. -/
theorem isCylSmooth_sub {c : ℝ} {f g : Plane → ℝ}
    (hf : UnforcedLeray.Sob.IsCylSmooth c f) (hg : UnforcedLeray.Sob.IsCylSmooth c g) :
    UnforcedLeray.Sob.IsCylSmooth c (f - g) := by
  obtain ⟨Rf, hfbd⟩ := hf.bounded
  obtain ⟨Rg, hgbd⟩ := hg.bounded
  refine ⟨hf.smooth.sub hg.smooth, ?_, ?_⟩
  · intro z
    simp only [Pi.sub_apply]
    rw [hf.periodic, hg.periodic]
  · refine ⟨max Rf Rg, ?_⟩
    intro z hz
    have hRf : Rf < |z.2| := lt_of_le_of_lt (le_max_left _ _) hz
    have hRg : Rg < |z.2| := lt_of_le_of_lt (le_max_right _ _) hz
    simp [hfbd z hRf, hgbd z hRg]

/-- The smooth Sobolev representative construction respects subtraction. -/
theorem ofCylSmooth_sub_eq {c : ℝ} (hc : 0 < c) {f g : Plane → ℝ}
    (hf : UnforcedLeray.Sob.IsCylSmooth c f) (hg : UnforcedLeray.Sob.IsCylSmooth c g) :
    UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := ℝ) (k := 2) (p := 2)
      (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) hc (f - g) (isCylSmooth_sub hf hg) =
    UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := ℝ) (k := 2) (p := 2)
      (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) hc f hf -
    UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := ℝ) (k := 2) (p := 2)
      (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) hc g hg := by
  have hmap := map_sub (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
    (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ ℝ 2 2)
    (UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := ℝ) (k := 2) (p := 2)
      (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) hc f hf)
    (UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := ℝ) (k := 2) (p := 2)
      (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) hc g hg)
  apply UnforcedLeray.Sob.W.value_injective
  apply Lp.ext
  filter_upwards [
    UnforcedLeray.Sob.W.value_ofCylSmooth (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))
      (𝕜 := ℝ) (F := ℝ) (k := 2) (p := 2) hc (f - g) (isCylSmooth_sub hf hg),
    UnforcedLeray.Sob.W.value_ofCylSmooth (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))
      (𝕜 := ℝ) (F := ℝ) (k := 2) (p := 2) hc f hf,
    UnforcedLeray.Sob.W.value_ofCylSmooth (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))
      (𝕜 := ℝ) (F := ℝ) (k := 2) (p := 2) hc g hg,
    Lp.coeFn_sub (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ ℝ 2 2
      (UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := ℝ) (k := 2) (p := 2)
        (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) hc f hf))
      (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ ℝ 2 2
        (UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := ℝ) (k := 2) (p := 2)
          (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) hc g hg))] with z hfg hfz hgz hsub
  have hmapz := congrArg (fun u : Lp ℝ 2
    (UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))) => u z) hmap
  simp only [Pi.sub_apply] at hsub
  rw [hmapz, hfg, hsub, hfz, hgz]
  rfl

/-- Smooth density can be chosen so that each approximant is literally the Sobolev element
associated with its smooth representative. -/
theorem exists_smoothH2_sequence {c : ℝ} (hc : 0 < c) (x : ScalarH2 c) :
    ∃ y : ℕ → ScalarH2 c, ∃ f : ℕ → Plane → ℝ,
      ∃ hf : ∀ n, UnforcedLeray.Sob.IsCylSmooth c (f n),
      (∀ n, y n = UnforcedLeray.Sob.W.ofCylSmooth
        (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ) (k := 2) (p := 2)
        hc (f n) (hf n)) ∧
      Tendsto y atTop (𝓝 x) := by
  obtain ⟨y, hy, hlim⟩ := UnforcedLeray.Sob.W.exists_seq_cylSmooth
    (c := c) (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ) (F := ℝ)
    (k := 2) (p := 2) hc (by norm_num) x
  choose f hf hrep using hy
  refine ⟨y, f, hf, ?_, hlim⟩
  intro n
  apply UnforcedLeray.Sob.W.value_injective
  apply Lp.ext
  have hrepW := (UnforcedLeray.Sob.ae_eq_wμ_iff (UnforcedLeray.Sob.cylinder c).μ
    (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))).mpr (hrep n)
  filter_upwards [hrepW,
    UnforcedLeray.Sob.W.value_ofCylSmooth (c := c) (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))
      (𝕜 := ℝ) (F := ℝ) (k := 2) (p := 2) hc (f n) (hf n)] with z hz₁ hz₂
  exact hz₁.trans hz₂.symm

/-- The bounded continuous representatives of a smooth density sequence are Cauchy in the
uniform norm, with the quantitative H² modulus inherited from the smooth estimate. -/
theorem smooth_density_bcf_cauchy {c : ℝ} (hc1 : 1 ≤ c) (hc : 0 < c)
    (x : ScalarH2 c) (y : ℕ → ScalarH2 c) (f : ℕ → Plane → ℝ)
    (hf : ∀ n, UnforcedLeray.Sob.IsCylSmooth c (f n))
    (hy : ∀ n, y n = UnforcedLeray.Sob.W.ofCylSmooth
      (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ) (k := 2) (p := 2)
      hc (f n) (hf n)) (hlim : Tendsto y atTop (𝓝 x)) :
    ∃ F : ℕ → Plane →ᵇ ℝ, (∀ n z, F n z = f n z) ∧ CauchySeq F := by
  choose F hF using fun n => exists_smooth_bcf hc1 (hf n)
  have hycauchy := hlim.cauchySeq
  have hC : CauchySeq F := by
    rw [Metric.cauchySeq_iff] at hycauchy ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hycauchy (ε / 12) (by positivity)
    refine ⟨N, fun m hm n hn => ?_⟩
    rw [dist_eq_norm]
    have hpoint : ∀ z, ‖(F m - F n) z‖ ≤ 12 * ‖y m - y n‖ := by
      intro z
      have h := smooth_cyl_sup_le_h2norm hc1 (isCylSmooth_sub (hf m) (hf n)) z
      rw [ofCylSmooth_sub_eq hc (hf m) (hf n)] at h
      rw [← hy m, ← hy n] at h
      simpa [Pi.sub_apply, hF m z, hF n z] using h
    have hnorm : ‖F m - F n‖ ≤ 12 * ‖y m - y n‖ :=
      (BoundedContinuousFunction.norm_le (by positivity)).2 hpoint
    calc
      ‖F m - F n‖ ≤ 12 * ‖y m - y n‖ := hnorm
      _ < ε := by
        have hdist := hN m hm n hn
        rw [dist_eq_norm] at hdist
        nlinarith
  exact ⟨F, (fun n z => hF n z), hC⟩

/-- Every H² class on a train cylinder with period at least one is the uniform limit of the
bounded continuous representatives of its smooth density sequence. -/
theorem exists_uniform_smooth_H2_limit {c : ℝ} (hc1 : 1 ≤ c) (x : ScalarH2 c) :
    ∃ F : Plane →ᵇ ℝ, ∃ Fseq : ℕ → Plane →ᵇ ℝ, ∃ f : ℕ → Plane → ℝ,
      (∀ n z, Fseq n z = f n z) ∧ Tendsto Fseq atTop (𝓝 F) := by
  have hc : 0 < c := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hc1
  obtain ⟨y, f, hf, hy, hlim⟩ := exists_smoothH2_sequence hc x
  obtain ⟨Fseq, hFseq, hC⟩ := smooth_density_bcf_cauchy hc1 hc x y f hf hy hlim
  obtain ⟨F, hF⟩ := cauchySeq_tendsto_of_complete hC
  exact ⟨F, Fseq, f, hFseq, hF⟩

/-- The uniform limit of smooth cylinder representatives agrees almost everywhere with the
Sobolev value. This uses the L² subsequence theorem and is valid on the infinite-measure cylinder. -/
theorem exists_scalarH2_bcf_representative {c : ℝ} (hc1 : 1 ≤ c) (x : ScalarH2 c) :
    ∃ F : Plane →ᵇ ℝ,
      (F : Plane → ℝ) =ᵐ[UnforcedLeray.Cyl.cellμ c]
        (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
          (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ ℝ 2 2 x) ∧
      (∀ z, F (z + (c, 0)) = F z) ∧ ‖F‖ ≤ 12 * ‖x‖ := by
  have hc : 0 < c := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hc1
  obtain ⟨y, f, hf, hy, hlim⟩ := exists_smoothH2_sequence hc x
  obtain ⟨Fseq, hFseq, hC⟩ := smooth_density_bcf_cauchy hc1 hc x y f hf hy hlim
  obtain ⟨F, hF⟩ := cauchySeq_tendsto_of_complete hC
  let V := UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
    (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ ℝ 2 2
  let μ := UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
    (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))
  have hLp : Tendsto (fun n => V (y n)) atTop (𝓝 (V x)) :=
    (V.continuous.tendsto x).comp hlim
  have hmeasure := MeasureTheory.tendstoInMeasure_of_tendsto_Lp hLp
  obtain ⟨ns, hns, hconv⟩ := hmeasure.exists_seq_tendsto_ae
  have hrep (n : ℕ) : (Fseq n : Plane → ℝ) =ᵐ[μ] (V (y n)) := by
    rw [hy n]
    filter_upwards [UnforcedLeray.Sob.W.value_ofCylSmooth
      (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))
      (𝕜 := ℝ) (F := ℝ) (k := 2) (p := 2) hc (f n) (hf n)] with z hz
    exact (hFseq n z).trans hz.symm
  have hrepAll : ∀ᵐ z ∂μ, ∀ n, Fseq n z = V (y n) z := by
    rw [ae_all_iff]
    intro n
    exact hrep n
  have hFpoint (z : Plane) : Tendsto (fun n => Fseq n z) atTop (𝓝 (F z)) :=
    ((continuous_eval_const z).tendsto F).comp hF
  have hper : ∀ z, F (z + (c, 0)) = F z := by
    intro z
    have hL : Tendsto (fun n => Fseq n (z + (c, 0))) atTop (𝓝 (F (z + (c, 0)))) :=
      hFpoint (z + (c, 0))
    have hR : Tendsto (fun n => Fseq n z) atTop (𝓝 (F z)) := hFpoint z
    have heq : (fun n => Fseq n (z + (c, 0))) =ᶠ[atTop] (fun n => Fseq n z) :=
      Filter.Eventually.of_forall fun n => by
        change Fseq n (z + (c, 0)) = Fseq n z
        rw [hFseq n (z + (c, 0)), hFseq n z, (hf n).periodic z]
    exact tendsto_nhds_unique (hL.congr' heq) hR
  have hnormSeq : ∀ n, ‖Fseq n‖ ≤ 12 * ‖y n‖ := by
    intro n
    have hpointN : ∀ z, ‖Fseq n z‖ ≤ 12 * ‖y n‖ := by
      intro z
      have h := smooth_cyl_sup_le_h2norm hc1 (hf n) z
      rw [← hy n] at h
      simpa [hFseq n z] using h
    exact (BoundedContinuousFunction.norm_le (by positivity)).2 hpointN
  have hnormLimit : Tendsto (fun n => ‖Fseq n‖) atTop (𝓝 ‖F‖) :=
    (continuous_norm.tendsto F).comp hF
  have hmul : Continuous (fun r : ScalarH2 c => (12 : ℝ) * ‖r‖) :=
    continuous_const.mul continuous_norm
  have hyNormLimit : Tendsto (fun n => 12 * ‖y n‖) atTop (𝓝 (12 * ‖x‖)) :=
    (hmul.tendsto x).comp hlim
  have hnormF : ‖F‖ ≤ 12 * ‖x‖ :=
    le_of_tendsto_of_tendsto hnormLimit hyNormLimit (Eventually.of_forall hnormSeq)
  have hlimitAE : (F : Plane → ℝ) =ᵐ[μ] (V x) := by
    filter_upwards [hconv, hrepAll] with z hzconv hzrep
    have hzF : Tendsto (fun k => Fseq (ns k) z) atTop (𝓝 (F z)) :=
      (hFpoint z).comp hns.tendsto_atTop
    have hzF' := hzF.congr' (Filter.Eventually.of_forall fun k => hzrep (ns k))
    exact tendsto_nhds_unique hzF' hzconv
  refine ⟨F, ?_, hper, hnormF⟩
  simpa [μ, scalarH2_measure_eq_cell] using hlimitAE

end UnforcedLeray.TrainB

#print axioms UnforcedLeray.TrainB.exists_scalarH2_bcf_representative
#print axioms UnforcedLeray.TrainB.smooth_multiplier_L2_bound
#print axioms UnforcedLeray.TrainB.smooth_h3_lowDerivative_enorm_bound
#print axioms UnforcedLeray.TrainB.smooth_h3_lowDerivative_mul_L2
