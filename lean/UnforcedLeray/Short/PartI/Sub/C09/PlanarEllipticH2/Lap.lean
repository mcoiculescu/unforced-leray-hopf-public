import UnforcedLeray.Short.PartI.Sub.C09
import UnforcedLeray.Lib.SobolevC.Elliptic
import UnforcedLeray.Lib.SobolevC.CylTransfer

/-!
# Planar Laplacian transfer to `Eucl 2` (helper for `PartI:PlanarEllipticH2`)

* `iterD_post_clm`: post-composition with a continuous real-linear map commutes with iterated
  derivatives.
* `planarH2_symm_ev`: the planar directions `ev i` are sent to the coordinate directions `e i` by
  `toPlane.symm`.
* `weakLap_toPlane`: `WeakLapOn univ u g` on `ℝ × ℝ` gives `IsWeakLaplacian (u ∘ toPlane)
  (g ∘ toPlane)` on `Eucl 2` (real tests).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

/-- Post-composition with a continuous real-linear map commutes with iterated derivatives. -/
theorem iterD_post_clm {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : F →L[ℝ] G) {φ : E → F} (hφ : ContDiff ℝ ∞ φ) (vs : List E) :
    UnforcedLeray.Sob.iterD vs (fun x => L (φ x)) =
      fun x => L (UnforcedLeray.Sob.iterD vs φ x) := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    funext x
    simp only [UnforcedLeray.Sob.iterD_cons]
    rw [ih]
    have hd : DifferentiableAt ℝ (UnforcedLeray.Sob.iterD vs φ) x :=
      ((UnforcedLeray.Sob.contDiff_iterD hφ vs).differentiable (by simp)) x
    rw [show (fun y => L (UnforcedLeray.Sob.iterD vs φ y)) =
        L ∘ (UnforcedLeray.Sob.iterD vs φ) from rfl,
      fderiv_comp x L.differentiableAt hd, L.fderiv]
    rfl

/-- The planar direction `ev i` is the image of the coordinate direction `cylDir i`. -/
theorem planarH2_ev_eq_cylDir (i : Fin 2) :
    UnforcedLeray.Sob.cylDir i = UnforcedLeray.B0121.ev i := by
  fin_cases i <;> rfl

theorem planarH2_symm_ev (i : Fin 2) :
    UnforcedLeray.Sob.toPlane.symm (UnforcedLeray.B0121.ev i) = UnforcedLeray.Sob.e i := by
  rw [← planarH2_ev_eq_cylDir, UnforcedLeray.Sob.toPlane_symm_cylDir]

/-- **Planar Laplacian to `Eucl 2`.** A weak Laplacian identity on `ℝ × ℝ` (complex tests, the
whole plane) gives the weak Laplacian identity on `Eucl 2` (real tests) for `u ∘ toPlane`. -/
theorem weakLap_toPlane {u g : ℝ × ℝ → ℂ} (h : WeakLapOn univ u g) :
    UnforcedLeray.Sob.IsWeakLaplacian
      (fun x : UnforcedLeray.Sob.Eucl 2 => u (UnforcedLeray.Sob.toPlane x))
      (fun x : UnforcedLeray.Sob.Eucl 2 => g (UnforcedLeray.Sob.toPlane x)) := by
  intro φ hφ hφc
  have hcφ : ContDiff ℝ ∞ (fun y => Complex.ofRealCLM (φ y)) :=
    Complex.ofRealCLM.contDiff.comp hφ
  have hsm : ContDiff ℝ ∞ (fun z : ℝ × ℝ => Complex.ofRealCLM (φ (UnforcedLeray.Sob.toPlane.symm z))) :=
    hcφ.comp UnforcedLeray.Sob.toPlane.symm.contDiff
  have hcs : HasCompactSupport
      (fun z : ℝ × ℝ => Complex.ofRealCLM (φ (UnforcedLeray.Sob.toPlane.symm z))) := by
    have h0 : HasCompactSupport (fun z : ℝ × ℝ => φ (UnforcedLeray.Sob.toPlane.symm z)) :=
      hφc.comp_homeomorph UnforcedLeray.Sob.toPlane.symm.toHomeomorph
    exact h0.comp_left (g := Complex.ofRealCLM) (by simp)
  have hT : UnforcedLeray.PlanarBS.Sob.IsTestFn univ (fun z : ℝ × ℝ => Complex.ofRealCLM (φ (UnforcedLeray.Sob.toPlane.symm z))) :=
    ⟨hsm, hcs, subset_univ _⟩
  have key : ∫ z : ℝ × ℝ, u z * (UnforcedLeray.PlanarBS.Sob.iterDirDeriv
        [UnforcedLeray.B0121.ev 0, UnforcedLeray.B0121.ev 0]
          (fun z : ℝ × ℝ => Complex.ofRealCLM (φ (UnforcedLeray.Sob.toPlane.symm z))) z +
      UnforcedLeray.PlanarBS.Sob.iterDirDeriv
        [UnforcedLeray.B0121.ev 1, UnforcedLeray.B0121.ev 1]
          (fun z : ℝ × ℝ => Complex.ofRealCLM (φ (UnforcedLeray.Sob.toPlane.symm z))) z) =
      ∫ z : ℝ × ℝ, g z * Complex.ofRealCLM (φ (UnforcedLeray.Sob.toPlane.symm z)) :=
    h _ hT
  -- the planar second derivatives of the pulled-back test are Euclidean ones, composed
  have hgen : ∀ i : Fin 2, ∀ z : ℝ × ℝ,
      UnforcedLeray.PlanarBS.Sob.iterDirDeriv
          [UnforcedLeray.B0121.ev i, UnforcedLeray.B0121.ev i]
            (fun z : ℝ × ℝ => Complex.ofRealCLM (φ (UnforcedLeray.Sob.toPlane.symm z))) z =
        Complex.ofRealCLM (UnforcedLeray.Sob.iterDirDeriv [UnforcedLeray.Sob.e i, UnforcedLeray.Sob.e i]
          φ (UnforcedLeray.Sob.toPlane.symm z)) := by
    intro i z
    have e1 := UnforcedLeray.Sob.iterD_comp_clm
      (UnforcedLeray.Sob.toPlane.symm : ℝ × ℝ →L[ℝ] UnforcedLeray.Sob.Eucl 2) hcφ
      [UnforcedLeray.B0121.ev i, UnforcedLeray.B0121.ev i]
    have e2 := iterD_post_clm Complex.ofRealCLM hφ [UnforcedLeray.Sob.e i, UnforcedLeray.Sob.e i]
    simp only [List.map_cons, List.map_nil, ContinuousLinearEquiv.coe_coe, planarH2_symm_ev] at e1
    have e3 := congrFun e1 z
    have e4 := congrFun e2 (UnforcedLeray.Sob.toPlane.symm z)
    simp only [Function.comp_apply] at e3 e4
    exact e3.trans e4
  have hlap : ∀ z : ℝ × ℝ,
      UnforcedLeray.PlanarBS.Sob.iterDirDeriv [UnforcedLeray.B0121.ev 0, UnforcedLeray.B0121.ev 0]
          (fun z : ℝ × ℝ => Complex.ofRealCLM (φ (UnforcedLeray.Sob.toPlane.symm z))) z +
        UnforcedLeray.PlanarBS.Sob.iterDirDeriv [UnforcedLeray.B0121.ev 1, UnforcedLeray.B0121.ev 1]
          (fun z : ℝ × ℝ => Complex.ofRealCLM (φ (UnforcedLeray.Sob.toPlane.symm z))) z =
        Complex.ofRealCLM (UnforcedLeray.Sob.lapl φ (UnforcedLeray.Sob.toPlane.symm z)) := by
    intro z
    rw [hgen 0 z, hgen 1 z, ← map_add]
    congr 1
    rw [UnforcedLeray.Sob.lapl, Fin.sum_univ_two]
  simp only [hlap] at key
  -- change of variables along `toPlane`
  have m1 := UnforcedLeray.Sob.measurePreserving_toPlane.integral_comp UnforcedLeray.Sob.measurableEmbedding_toPlane
    (fun z : ℝ × ℝ => u z * Complex.ofRealCLM (UnforcedLeray.Sob.lapl φ
      (UnforcedLeray.Sob.toPlane.symm z)))
  have m2 := UnforcedLeray.Sob.measurePreserving_toPlane.integral_comp UnforcedLeray.Sob.measurableEmbedding_toPlane
    (fun z : ℝ × ℝ => g z * Complex.ofRealCLM (φ (UnforcedLeray.Sob.toPlane.symm z)))
  simp only [UnforcedLeray.Sob.toPlane.symm_apply_apply] at m1 m2
  rw [← m1, ← m2] at key
  simp only [Complex.real_smul]
  simp only [Complex.ofRealCLM_apply] at key
  simpa only [mul_comm] using key

end UnforcedLeray.Short.PartI
