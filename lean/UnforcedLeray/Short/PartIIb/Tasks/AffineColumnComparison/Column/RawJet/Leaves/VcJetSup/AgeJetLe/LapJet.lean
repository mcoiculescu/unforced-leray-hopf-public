import UnforcedLeray.Lib.Train.Datum
import UnforcedLeray.Lib.Cylinder.IBP

/-!
Helper for task `PartII-b:G4/3/6/1/5/1` (`VcAgeJetLe`, SP line 2205): the vector Laplacian as a
sum of two second derivatives along the unit vectors of `Plane`, and the jet estimate
`‖D^j Δ^ℓ F (z)‖ ≤ 2^ℓ ‖D^{j+2ℓ} F (z)‖` for smooth `F`.
-/

set_option autoImplicit false

open scoped ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Train UnforcedLeray.Cyl

/-- Directional derivative `u ↦ (z ↦ D u(z) v)`. -/
noncomputable def Dv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (v : Plane)
    (u : Plane → E) : Plane → E := fun z => fderiv ℝ u z v

/-- The Laplacian as a sum of two second directional derivatives. -/
noncomputable def lapD (u : Plane → Vec) : Plane → Vec :=
  fun z => Dv ((1 : ℝ), (0 : ℝ)) (Dv ((1 : ℝ), (0 : ℝ)) u) z +
    Dv ((0 : ℝ), (1 : ℝ)) (Dv ((0 : ℝ), (1 : ℝ)) u) z

theorem contDiff_Dv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {u : Plane → E}
    (hu : ContDiff ℝ ∞ u) (v : Plane) : ContDiff ℝ ∞ (Dv v u) :=
  (contDiff_infty_iff_fderiv.1 hu).2.clm_apply contDiff_const

theorem contDiff_lapD {u : Plane → Vec} (hu : ContDiff ℝ ∞ u) : ContDiff ℝ ∞ (lapD u) :=
  ((contDiff_Dv (contDiff_Dv hu _) _).add (contDiff_Dv (contDiff_Dv hu _) _))

theorem Dv_proj {u : Plane → Vec} (hu : Differentiable ℝ u) (v : Plane) (k : Fin 2) :
    Dv v (fun x => u x k) = fun z => Dv v u z k := by
  funext z
  have h := ((EuclideanSpace.proj k : Vec →L[ℝ] ℝ).hasFDerivAt.comp z (hu z).hasFDerivAt)
  show fderiv ℝ (fun x => u x k) z v = _
  have : (fun x => u x k) = (EuclideanSpace.proj k : Vec →L[ℝ] ℝ) ∘ u := rfl
  rw [this, h.fderiv]
  rfl

theorem scalar_lap_eq {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f) (z : Plane) :
    lapS f z = Dv ((1 : ℝ), (0 : ℝ)) (Dv ((1 : ℝ), (0 : ℝ)) f) z +
      Dv ((0 : ℝ), (1 : ℝ)) (Dv ((0 : ℝ), (1 : ℝ)) f) z := by
  have hd : Differentiable ℝ f := hf.differentiable (by simp)
  have hd1 : Differentiable ℝ (Dv ((1 : ℝ), (0 : ℝ)) f) := (contDiff_Dv hf _).differentiable (by simp)
  have hd2 : Differentiable ℝ (Dv ((0 : ℝ), (1 : ℝ)) f) := (contDiff_Dv hf _).differentiable (by simp)
  have hQ : partialQ f = Dv ((1 : ℝ), (0 : ℝ)) f := funext (partialQ_eq_fderiv hd)
  have hE : partialEta f = Dv ((0 : ℝ), (1 : ℝ)) f := funext (partialEta_eq_fderiv hd)
  show partialQ (partialQ f) z + partialEta (partialEta f) z = _
  rw [hQ, hE, partialQ_eq_fderiv hd1, partialEta_eq_fderiv hd2]
  rfl

theorem vecLaplacian_eq_lapD {u : Plane → Vec} (hu : ContDiff ℝ ∞ u) :
    vecLaplacian u = lapD u := by
  funext z
  have hd : Differentiable ℝ u := hu.differentiable (by simp)
  have hd1 : ∀ v, Differentiable ℝ (Dv v u) := fun v => (contDiff_Dv hu v).differentiable (by simp)
  have hk : ∀ k : Fin 2, vecLaplacian u z k =
      Dv ((1 : ℝ), (0 : ℝ)) (Dv ((1 : ℝ), (0 : ℝ)) u) z k +
        Dv ((0 : ℝ), (1 : ℝ)) (Dv ((0 : ℝ), (1 : ℝ)) u) z k := by
    intro k
    have hs : ContDiff ℝ ∞ (fun x => u x k) :=
      (EuclideanSpace.proj k : Vec →L[ℝ] ℝ).contDiff.comp hu
    have h1 := scalar_lap_eq hs z
    rw [Dv_proj hd, Dv_proj hd, Dv_proj (hd1 _), Dv_proj (hd1 _)] at h1
    · fin_cases k
      · exact h1
      · exact h1
  ext k
  rw [hk k]
  rfl

/-- One step of the jet estimate: `‖D^j (D_v u)‖ ≤ ‖v‖ ‖D^{j+1} u‖`. -/
theorem norm_jet_Dv_le {u : Plane → Vec} (hu : ContDiff ℝ ∞ u) (v : Plane) (j : ℕ) (z : Plane) :
    ‖iteratedFDeriv ℝ j (Dv v u) z‖ ≤ ‖v‖ * ‖iteratedFDeriv ℝ (j + 1) u z‖ := by
  have hfd : ContDiff ℝ ∞ (fderiv ℝ u) := (contDiff_infty_iff_fderiv.1 hu).2
  have e : Dv v u = (ContinuousLinearMap.apply ℝ Vec v) ∘ (fderiv ℝ u) := rfl
  rw [e, ← norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := u) (x := z) (n := j)]
  refine ((ContinuousLinearMap.apply ℝ Vec v).norm_iteratedFDeriv_comp_left
    (hfd.contDiffAt) (by exact_mod_cast le_top)).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (fun f => ?_)
  simpa [mul_comm] using f.le_opNorm v

theorem norm_jet_lapD_le {u : Plane → Vec} (hu : ContDiff ℝ ∞ u) (j : ℕ) (z : Plane) :
    ‖iteratedFDeriv ℝ j (lapD u) z‖ ≤ 2 * ‖iteratedFDeriv ℝ (j + 2) u z‖ := by
  have hA : ContDiff ℝ ∞ (Dv ((1 : ℝ), (0 : ℝ)) (Dv ((1 : ℝ), (0 : ℝ)) u)) :=
    contDiff_Dv (contDiff_Dv hu _) _
  have hB : ContDiff ℝ ∞ (Dv ((0 : ℝ), (1 : ℝ)) (Dv ((0 : ℝ), (1 : ℝ)) u)) :=
    contDiff_Dv (contDiff_Dv hu _) _
  have cA : ContDiffAt ℝ j (Dv ((1 : ℝ), (0 : ℝ)) (Dv ((1 : ℝ), (0 : ℝ)) u)) z :=
    (hA.of_le (by exact_mod_cast le_top)).contDiffAt
  have cB : ContDiffAt ℝ j (Dv ((0 : ℝ), (1 : ℝ)) (Dv ((0 : ℝ), (1 : ℝ)) u)) z :=
    (hB.of_le (by exact_mod_cast le_top)).contDiffAt
  have e : lapD u = Dv ((1 : ℝ), (0 : ℝ)) (Dv ((1 : ℝ), (0 : ℝ)) u) +
      Dv ((0 : ℝ), (1 : ℝ)) (Dv ((0 : ℝ), (1 : ℝ)) u) := rfl
  have n1 : ‖((1 : ℝ), (0 : ℝ))‖ = 1 := by simp [Prod.norm_def]
  have n2 : ‖((0 : ℝ), (1 : ℝ))‖ = 1 := by simp [Prod.norm_def]
  have b1 := norm_jet_Dv_le (contDiff_Dv hu ((1 : ℝ), (0 : ℝ))) ((1 : ℝ), (0 : ℝ)) j z
  have b2 := norm_jet_Dv_le hu ((1 : ℝ), (0 : ℝ)) (j + 1) z
  have b3 := norm_jet_Dv_le (contDiff_Dv hu ((0 : ℝ), (1 : ℝ))) ((0 : ℝ), (1 : ℝ)) j z
  have b4 := norm_jet_Dv_le hu ((0 : ℝ), (1 : ℝ)) (j + 1) z
  rw [n1] at b1 b2
  rw [n2] at b3 b4
  rw [e, iteratedFDeriv_add_apply cA cB]
  refine (norm_add_le _ _).trans ?_
  have : j + 1 + 1 = j + 2 := rfl
  rw [this] at b2 b4
  linarith

theorem contDiff_lapD_iterate {u : Plane → Vec} (hu : ContDiff ℝ ∞ u) :
    ∀ ℓ : ℕ, ContDiff ℝ ∞ (lapD^[ℓ] u)
  | 0 => hu
  | ℓ + 1 => by
    rw [Function.iterate_succ_apply']
    exact contDiff_lapD (contDiff_lapD_iterate hu ℓ)

theorem norm_jet_lapD_iterate_le {u : Plane → Vec} (hu : ContDiff ℝ ∞ u) (ℓ : ℕ) :
    ∀ (j : ℕ) (z : Plane),
      ‖iteratedFDeriv ℝ j (lapD^[ℓ] u) z‖ ≤ 2 ^ ℓ * ‖iteratedFDeriv ℝ (j + 2 * ℓ) u z‖ := by
  induction ℓ generalizing u with
  | zero => intro j z; simp
  | succ ℓ ih =>
    intro j z
    rw [Function.iterate_succ_apply]
    have h1 := ih (contDiff_lapD hu) j z
    have h2 := norm_jet_lapD_le hu (j + 2 * ℓ) z
    have e : j + 2 * ℓ + 2 = j + 2 * (ℓ + 1) := by ring
    rw [e] at h2
    calc _ ≤ 2 ^ ℓ * ‖iteratedFDeriv ℝ (j + 2 * ℓ) (lapD u) z‖ := h1
      _ ≤ 2 ^ ℓ * (2 * ‖iteratedFDeriv ℝ (j + 2 * (ℓ + 1)) u z‖) := by gcongr
      _ = _ := by ring

end UnforcedLeray.Short.IIb
