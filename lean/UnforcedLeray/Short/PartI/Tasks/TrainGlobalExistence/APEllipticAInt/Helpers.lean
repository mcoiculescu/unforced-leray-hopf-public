import UnforcedLeray.Short.PartI.Sub.PartI_T04_8_1
import UnforcedLeray.Short.PartI.Tasks.CylinderInterpolation.JetWord
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.ForcingIBP
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.PressureOrth.Word
import UnforcedLeray.Short.PartI.Sub.PartI_T08_1

/-!
# Shared helpers for `APEllipticAInt` and `APEllipticAEq` (task `PartI:T04/8/1`)

Source: `the November 2 reference manuscript` lines 285-287.
Word derivatives of the components of a smooth periodic field `f : Plane → Vec`, their jet
bounds, integrability on the cell (from `APEllipticData`), the pointwise curl identity and the
mixed-partial identity needed for the cell integration by parts.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff

namespace UnforcedLeray.Short.PartI.APEllipticHelp

open UnforcedLeray
open UnforcedLeray.Train (Vec)
open UnforcedLeray.Cyl (Plane)

/-! ### Components, constants and the data of `APEllipticData` -/

/-- The `k`-th component of a vector field as a scalar field. -/
def vcomp (f : Plane → Vec) (k : Fin 2) : Plane → ℝ := fun x => f x k

/-- Sum of the operator norms of the two coordinate projections (a fixed constant). -/
def projSum : ℝ := ∑ k : Fin 2, ‖(EuclideanSpace.proj k : Vec →L[ℝ] ℝ)‖

theorem projSum_nonneg : 0 ≤ projSum :=
  Finset.sum_nonneg (fun k _ => norm_nonneg _)

theorem apData_le {c : ℝ} {f : Plane → Vec} (hf : APEllipticData c f) : 1 ≤ c := by
  unfold APEllipticData at hf
  exact hf.1

theorem apData_smooth {c : ℝ} {f : Plane → Vec} (hf : APEllipticData c f) :
    ContDiff ℝ ∞ f := by
  unfold APEllipticData at hf
  exact hf.2.1

theorem apData_periodic {c : ℝ} {f : Plane → Vec} (hf : APEllipticData c f) :
    Cyl.IsPeriodic c f := by
  unfold APEllipticData at hf
  exact hf.2.2.1

theorem apData_div {c : ℝ} {f : Plane → Vec} (hf : APEllipticData c f) :
    ∀ z, Cyl.divergence f z = 0 := by
  unfold APEllipticData at hf
  exact hf.2.2.2.1

theorem apData_integrable {c : ℝ} {f : Plane → Vec} (hf : APEllipticData c f) (i : ℕ) :
    IntegrableOn (fun z => ‖iteratedFDeriv ℝ i f z‖ ^ 2) (Cyl.cell c) := by
  unfold APEllipticData at hf
  exact hf.2.2.2.2.2 i

theorem vcomp_smooth {f : Plane → Vec} (hf : ContDiff ℝ ∞ f) (k : Fin 2) :
    ContDiff ℝ ∞ (vcomp f k) :=
  (EuclideanSpace.proj k : Vec →L[ℝ] ℝ).contDiff.comp hf

theorem cont_word {f : Plane → Vec} (hf : ContDiff ℝ ∞ f) (k : Fin 2) (u : List Bool) :
    Continuous (B0151.derivWord u (vcomp f k)) :=
  (B0151.contDiff_derivWord (vcomp_smooth hf k) u).continuous

/-! ### Partial derivatives as word derivatives -/

/-- `∂_q` of a word derivative is the word derivative with the letter `true` prepended. -/
theorem rq_word {h : Plane → ℝ} (hh : ContDiff ℝ ∞ h) (u : List Bool) :
    Cyl.partialQ (B0151.derivWord u h) = B0151.derivWord (true :: u) h := by
  have hd : Differentiable ℝ (B0151.derivWord u h) :=
    (B0151.contDiff_derivWord hh u).differentiable (by simp)
  funext z
  rw [Cyl.partialQ_eq_fderiv hd z]
  exact (B0151.partialX_eq_fderiv hd z).symm

/-- `∂_η` of a word derivative is the word derivative with the letter `false` prepended. -/
theorem re_word {h : Plane → ℝ} (hh : ContDiff ℝ ∞ h) (u : List Bool) :
    Cyl.partialEta (B0151.derivWord u h) = B0151.derivWord (false :: u) h := by
  have hd : Differentiable ℝ (B0151.derivWord u h) :=
    (B0151.contDiff_derivWord hh u).differentiable (by simp)
  funext z
  rw [Cyl.partialEta_eq_fderiv hd z]
  exact (B0151.partialY_eq_fderiv hd z).symm

/-- Mixed partial derivatives commute on smooth scalar fields. -/
theorem mixed_partial {G : Plane → ℝ} (hG : ContDiff ℝ ∞ G) :
    Cyl.partialEta (Cyl.partialQ G) = Cyl.partialQ (Cyl.partialEta G) := by
  have h := (ForcingIBP.derivWord_comm [false] G hG).1
  have e1 : Cyl.partialEta (Cyl.partialQ G) = B0151.derivWord [false] (Cyl.partialQ G) :=
    re_word (ForcingIBP.cd_partialQ hG) []
  have e2 : Cyl.partialEta G = B0151.derivWord [false] G := re_word hG []
  rw [e1, h, e2]

/-! ### Bounds and integrability -/

/-- Word derivatives of a component are bounded by the `m`-th jet, for `m` the word length. -/
theorem abs_derivWord_le {f : Plane → Vec} (hf : ContDiff ℝ ∞ f) (k : Fin 2) (u : List Bool)
    (m : ℕ) (hm : u.length = m) (z : Plane) :
    |B0151.derivWord u (vcomp f k) z| ≤ projSum * ‖iteratedFDeriv ℝ m f z‖ := by
  have hk := vcomp_smooth hf k
  have h1 : |B0151.derivWord u (vcomp f k) z| ≤ ‖iteratedFDeriv ℝ m (vcomp f k) z‖ :=
    (cylJetWord_proof (vcomp f k) hk m z).1 u hm
  have h2 : ‖iteratedFDeriv ℝ m (vcomp f k) z‖ ≤
      ‖(EuclideanSpace.proj k : Vec →L[ℝ] ℝ)‖ * ‖iteratedFDeriv ℝ m f z‖ :=
    ContinuousLinearMap.norm_iteratedFDeriv_comp_left (EuclideanSpace.proj k : Vec →L[ℝ] ℝ)
      hf.contDiffAt (by simp)
  have h3 : ‖(EuclideanSpace.proj k : Vec →L[ℝ] ℝ)‖ ≤ projSum :=
    Finset.single_le_sum (f := fun k : Fin 2 => ‖(EuclideanSpace.proj k : Vec →L[ℝ] ℝ)‖)
      (fun i _ => norm_nonneg _) (Finset.mem_univ k)
  calc |B0151.derivWord u (vcomp f k) z| ≤ ‖iteratedFDeriv ℝ m (vcomp f k) z‖ := h1
    _ ≤ ‖(EuclideanSpace.proj k : Vec →L[ℝ] ℝ)‖ * ‖iteratedFDeriv ℝ m f z‖ := h2
    _ ≤ projSum * ‖iteratedFDeriv ℝ m f z‖ := mul_le_mul_of_nonneg_right h3 (norm_nonneg _)

theorem integrableOn_bound_sq {c : ℝ} {f : Plane → Vec} (hf : APEllipticData c f) (K : ℝ)
    (m : ℕ) : IntegrableOn (fun z => (K * ‖iteratedFDeriv ℝ m f z‖) ^ 2) (Cyl.cell c) := by
  have e : (fun z => (K * ‖iteratedFDeriv ℝ m f z‖) ^ 2) =
      fun z => K ^ 2 * ‖iteratedFDeriv ℝ m f z‖ ^ 2 := by
    funext z; ring
  rw [e]
  exact Integrable.const_mul (apData_integrable hf m) (K ^ 2)

/-- Product of two functions dominated by `A` and `B` with square-integrable `A`, `B`. -/
theorem integrable_mul_of_le {S : Set Plane} {a b A B : Plane → ℝ}
    (ha : Continuous a) (hb : Continuous b)
    (hA : Integrable (fun z => A z ^ 2) (volume.restrict S))
    (hB : Integrable (fun z => B z ^ 2) (volume.restrict S))
    (haA : ∀ z, |a z| ≤ A z) (hbB : ∀ z, |b z| ≤ B z) :
    Integrable (fun z => a z * b z) (volume.restrict S) := by
  have hAB : Integrable (fun z => A z ^ 2 + B z ^ 2) (volume.restrict S) := hA.add hB
  refine Integrable.mono' (hAB.const_mul (1 / 2 : ℝ)) (ha.mul hb).aestronglyMeasurable ?_
  refine ae_of_all _ (fun z => ?_)
  have h1 := haA z
  have h2 := hbB z
  have hA0 : 0 ≤ A z := le_trans (abs_nonneg _) h1
  have h3 : |a z| * |b z| ≤ A z * B z := mul_le_mul h1 h2 (abs_nonneg _) hA0
  simp only [Real.norm_eq_abs, abs_mul]
  nlinarith [sq_nonneg (A z - B z), h3]

theorem integrable_sq_of_le {S : Set Plane} {a A : Plane → ℝ} (ha : Continuous a)
    (hA : Integrable (fun z => A z ^ 2) (volume.restrict S))
    (haA : ∀ z, |a z| ≤ A z) :
    Integrable (fun z => a z ^ 2) (volume.restrict S) := by
  have e : (fun z => a z ^ 2) = fun z => a z * a z := funext fun z => sq (a z)
  rw [e]
  exact integrable_mul_of_le ha ha hA hA haA haA

theorem integrableOn_sq_word {c : ℝ} {f : Plane → Vec} (hf : APEllipticData c f) (k : Fin 2)
    (u : List Bool) :
    IntegrableOn (fun z => B0151.derivWord u (vcomp f k) z ^ 2) (Cyl.cell c) :=
  integrable_sq_of_le (S := Cyl.cell c) (cont_word (apData_smooth hf) k u)
    (integrableOn_bound_sq hf projSum u.length) (abs_derivWord_le (apData_smooth hf) k u u.length rfl)

theorem integrableOn_mul_word {c : ℝ} {f : Plane → Vec} (hf : APEllipticData c f) (k l : Fin 2)
    (u v : List Bool) :
    IntegrableOn (fun z => B0151.derivWord u (vcomp f k) z * B0151.derivWord v (vcomp f l) z)
      (Cyl.cell c) :=
  integrable_mul_of_le (S := Cyl.cell c) (cont_word (apData_smooth hf) k u)
    (cont_word (apData_smooth hf) l v)
    (integrableOn_bound_sq hf projSum u.length) (integrableOn_bound_sq hf projSum v.length)
    (abs_derivWord_le (apData_smooth hf) k u u.length rfl)
    (abs_derivWord_le (apData_smooth hf) l v v.length rfl)

/-! ### The curl and the divergence on word derivatives -/

/-- The word derivative of the scalar curl: `∂_w curl f = ∂_q ∂_w f_1 - ∂_η ∂_w f_0`. -/
theorem curl_word_eq {f : Plane → Vec} (hf : ContDiff ℝ ∞ f) (w : List Bool) (z : Plane) :
    B0151.derivWord w (Cyl.curl f) z =
      B0151.derivWord (true :: w) (vcomp f 1) z - B0151.derivWord (false :: w) (vcomp f 0) z := by
  have hcurl : Cyl.curl f = fun x => Cyl.partialQ (vcomp f 1) x - Cyl.partialEta (vcomp f 0) x :=
    rfl
  have s1 : ContDiff ℝ ∞ (Cyl.partialQ (vcomp f 1)) :=
    ForcingIBP.cd_partialQ (vcomp_smooth hf 1)
  have s2 : ContDiff ℝ ∞ (Cyl.partialEta (vcomp f 0)) :=
    ForcingIBP.cd_partialEta (vcomp_smooth hf 0)
  rw [hcurl, derivWord_sub_smooth s1 s2 w z]
  rw [(ForcingIBP.derivWord_comm w (vcomp f 1) (vcomp_smooth hf 1)).1,
    (ForcingIBP.derivWord_comm w (vcomp f 0) (vcomp_smooth hf 0)).2,
    rq_word (vcomp_smooth hf 1) w, re_word (vcomp_smooth hf 0) w]

theorem integrableOn_curl_sq {c : ℝ} {f : Plane → Vec} (hf : APEllipticData c f) (w : List Bool) :
    IntegrableOn (fun z => (B0151.derivWord (true :: w) (vcomp f 1) z
      - B0151.derivWord (false :: w) (vcomp f 0) z) ^ 2) (Cyl.cell c) := by
  have hs := apData_smooth hf
  refine integrable_sq_of_le (S := Cyl.cell c)
    (A := fun z => (2 * projSum) * ‖iteratedFDeriv ℝ (w.length + 1) f z‖) ?_
    (integrableOn_bound_sq hf (2 * projSum) (w.length + 1)) ?_
  · exact (cont_word hs 1 (true :: w)).sub (cont_word hs 0 (false :: w))
  · intro z
    have h1 := abs_derivWord_le hs 1 (true :: w) (w.length + 1) rfl z
    have h2 := abs_derivWord_le hs 0 (false :: w) (w.length + 1) rfl z
    have h3 := abs_sub (B0151.derivWord (true :: w) (vcomp f 1) z)
      (B0151.derivWord (false :: w) (vcomp f 0) z)
    have hp := projSum_nonneg
    have hn : 0 ≤ ‖iteratedFDeriv ℝ (w.length + 1) f z‖ := norm_nonneg _
    nlinarith [h1, h2, h3, mul_nonneg hp hn]

/-- The divergence of the word derivatives vanishes: `∂_q ∂_w f_0 + ∂_η ∂_w f_1 = 0`. -/
theorem div_word_zero {c : ℝ} {f : Plane → Vec} (hf : APEllipticData c f) (w : List Bool)
    (z : Plane) :
    B0151.derivWord (true :: w) (vcomp f 0) z + B0151.derivWord (false :: w) (vcomp f 1) z = 0 := by
  have hs0 := vcomp_smooth (apData_smooth hf) 0
  have hs1 := vcomp_smooth (apData_smooth hf) 1
  have hadd := JetPressureWord.derivWord_add w (ForcingIBP.cd_partialQ hs0)
    (ForcingIBP.cd_partialEta hs1)
  have hfun : (fun x => Cyl.partialQ (vcomp f 0) x + Cyl.partialEta (vcomp f 1) x) =
      fun _ => (0 : ℝ) :=
    funext fun x => apData_div hf x
  have hz : B0151.derivWord w (fun x => Cyl.partialQ (vcomp f 0) x + Cyl.partialEta (vcomp f 1) x) z
      = 0 := by
    rw [hfun, JetPressureWord.derivWord_zero]
  rw [hadd] at hz
  have c0 : B0151.derivWord w (Cyl.partialQ (vcomp f 0)) z =
      B0151.derivWord (true :: w) (vcomp f 0) z := by
    rw [(ForcingIBP.derivWord_comm w (vcomp f 0) hs0).1, rq_word hs0 w]
  have c1 : B0151.derivWord w (Cyl.partialEta (vcomp f 1)) z =
      B0151.derivWord (false :: w) (vcomp f 1) z := by
    rw [(ForcingIBP.derivWord_comm w (vcomp f 1) hs1).2, re_word hs1 w]
  simp only at hz
  linarith [hz, c0, c1]

end UnforcedLeray.Short.PartI.APEllipticHelp
