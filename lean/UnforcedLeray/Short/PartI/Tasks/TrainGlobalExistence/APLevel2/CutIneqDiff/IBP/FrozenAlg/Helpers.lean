import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APEnstrophy.HasDeriv

/-!
# Helpers for the frozen-field integration by parts (`APL2FrozenAlg`, `APL2FrozenTransport`,
`APL2FrozenViscous`)

Generic calculus facts on `Plane → ℝ` and `Plane → Vec`: local partial derivatives as
`fderiv`, symmetry of mixed partials, product and linear rules for slices, component rules, and
integrability of `χ_R(η) h(z)` on the cell for continuous `h`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI.FA

open UnforcedLeray
open UnforcedLeray.Train (Vec)
open UnforcedLeray.Cyl (Plane)

lemma fdFDiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) : DifferentiableAt ℝ (fderiv ℝ f) x :=
  (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)

lemma fdFD {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (v w : E) :
    fderiv ℝ (fun y => fderiv ℝ f y v) x w = fderiv ℝ (fderiv ℝ f) x w v := by
  have h2 : HasFDerivAt (fun y => fderiv ℝ f y v)
      ((fderiv ℝ f x).comp (0 : E →L[ℝ] E) + (fderiv ℝ (fderiv ℝ f) x).flip v) x :=
    (fdFDiff hf).hasFDerivAt.clm_apply (hasFDerivAt_const v x)
  rw [h2.fderiv]
  simp

lemma fdSymm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (a b : E) :
    fderiv ℝ (fderiv ℝ f) x a b = fderiv ℝ (fderiv ℝ f) x b a :=
  hf.isSymmSndFDerivAt (by simp) a b

/-- Partial derivative at a point of differentiability, as a directional derivative. -/
lemma pqAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {g : Plane → E} {z : Plane}
    (hg : DifferentiableAt ℝ g z) :
    Cyl.partialQ g z = fderiv ℝ g z ((1 : ℝ), (0 : ℝ)) := by
  have h0 : HasDerivAt (fun q : ℝ => ((q, z.2) : Plane)) ((1 : ℝ), (0 : ℝ)) z.1 :=
    (hasDerivAt_id z.1).prodMk (hasDerivAt_const z.1 z.2)
  unfold Cyl.partialQ
  exact (hg.hasFDerivAt.comp_hasDerivAt z.1 h0).deriv

lemma peAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {g : Plane → E} {z : Plane}
    (hg : DifferentiableAt ℝ g z) :
    Cyl.partialEta g z = fderiv ℝ g z ((0 : ℝ), (1 : ℝ)) := by
  have h0 : HasDerivAt (fun η : ℝ => ((z.1, η) : Plane)) ((0 : ℝ), (1 : ℝ)) z.2 :=
    (hasDerivAt_const z.2 z.1).prodMk (hasDerivAt_id z.2)
  unfold Cyl.partialEta
  exact (hg.hasFDerivAt.comp_hasDerivAt z.2 h0).deriv

/-- Mixed partials of a `C^∞` scalar field commute. -/
theorem pqpe_comm (f : Plane → ℝ) (hf : ContDiff ℝ ∞ f) (z : Plane) :
    Cyl.partialQ (Cyl.partialEta f) z = Cyl.partialEta (Cyl.partialQ f) z := by
  have hdiff : Differentiable ℝ f := hf.differentiable (by simp)
  have hc2 : ContDiffAt ℝ 2 f z := hf.contDiffAt.of_le (by simp)
  have e1 : Cyl.partialEta f = fun y => fderiv ℝ f y ((0 : ℝ), (1 : ℝ)) :=
    funext fun y => Cyl.partialEta_eq_fderiv hdiff y
  have e2 : Cyl.partialQ f = fun y => fderiv ℝ f y ((1 : ℝ), (0 : ℝ)) :=
    funext fun y => Cyl.partialQ_eq_fderiv hdiff y
  have hEd : DifferentiableAt ℝ (Cyl.partialEta f) z := by
    rw [e1]; exact (fdFDiff hc2).clm_apply (differentiableAt_const _)
  have hQd : DifferentiableAt ℝ (Cyl.partialQ f) z := by
    rw [e2]; exact (fdFDiff hc2).clm_apply (differentiableAt_const _)
  have hLHS : Cyl.partialQ (Cyl.partialEta f) z
      = fderiv ℝ (fderiv ℝ f) z ((1 : ℝ), (0 : ℝ)) ((0 : ℝ), (1 : ℝ)) := by
    rw [pqAt hEd, e1, fdFD hc2]
  have hRHS : Cyl.partialEta (Cyl.partialQ f) z
      = fderiv ℝ (fderiv ℝ f) z ((0 : ℝ), (1 : ℝ)) ((1 : ℝ), (0 : ℝ)) := by
    rw [peAt hQd, e2, fdFD hc2]
  rw [hLHS, hRHS]
  exact fdSymm hc2 _ _

theorem pqpe_fun (f : Plane → ℝ) (hf : ContDiff ℝ ∞ f) :
    Cyl.partialQ (Cyl.partialEta f) = Cyl.partialEta (Cyl.partialQ f) :=
  funext (pqpe_comm f hf)

theorem pqAdd (f g : Plane → ℝ) (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (z : Plane) :
    Cyl.partialQ (fun y => f y + g y) z = Cyl.partialQ f z + Cyl.partialQ g z := by
  rcases z with ⟨q, η⟩
  exact ((Cyl.hasDerivAt_sliceQ hf q η).add (Cyl.hasDerivAt_sliceQ hg q η)).deriv

theorem peAdd (f g : Plane → ℝ) (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (z : Plane) :
    Cyl.partialEta (fun y => f y + g y) z = Cyl.partialEta f z + Cyl.partialEta g z := by
  rcases z with ⟨q, η⟩
  exact ((Cyl.hasDerivAt_sliceEta hf q η).add (Cyl.hasDerivAt_sliceEta hg q η)).deriv

/-- `∂_q` of the Laplacian of a smooth scalar field. -/
theorem lapComm_q (om : Plane → ℝ) (hom : ContDiff ℝ ∞ om) :
    Cyl.partialQ (Train.lapS om) = Train.lapS (Cyl.partialQ om) := by
  funext z
  have hQ : ContDiff ℝ ∞ (Cyl.partialQ om) := Cyl.contDiff_partialQ hom
  have hE : ContDiff ℝ ∞ (Cyl.partialEta om) := Cyl.contDiff_partialEta hom
  have hQQ : ContDiff ℝ ∞ (Cyl.partialQ (Cyl.partialQ om)) := Cyl.contDiff_partialQ hQ
  have hEE : ContDiff ℝ ∞ (Cyl.partialEta (Cyl.partialEta om)) := Cyl.contDiff_partialEta hE
  have hEQ : ContDiff ℝ ∞ (Cyl.partialEta (Cyl.partialQ om)) := Cyl.contDiff_partialEta hQ
  have hQE : ContDiff ℝ ∞ (Cyl.partialQ (Cyl.partialEta om)) := Cyl.contDiff_partialQ hE
  have hsplit : Train.lapS om = fun y => Cyl.partialQ (Cyl.partialQ om) y
      + Cyl.partialEta (Cyl.partialEta om) y := rfl
  rw [hsplit, pqAdd _ _ (hQQ.differentiable (by simp)) (hEE.differentiable (by simp)) z]
  unfold Train.lapS
  rw [pqpe_fun (Cyl.partialEta om) hE, pqpe_fun om hom]

/-- `∂_η` of the Laplacian of a smooth scalar field. -/
theorem lapComm_e (om : Plane → ℝ) (hom : ContDiff ℝ ∞ om) :
    Cyl.partialEta (Train.lapS om) = Train.lapS (Cyl.partialEta om) := by
  funext z
  have hQ : ContDiff ℝ ∞ (Cyl.partialQ om) := Cyl.contDiff_partialQ hom
  have hE : ContDiff ℝ ∞ (Cyl.partialEta om) := Cyl.contDiff_partialEta hom
  have hQQ : ContDiff ℝ ∞ (Cyl.partialQ (Cyl.partialQ om)) := Cyl.contDiff_partialQ hQ
  have hEE : ContDiff ℝ ∞ (Cyl.partialEta (Cyl.partialEta om)) := Cyl.contDiff_partialEta hE
  have hsplit : Train.lapS om = fun y => Cyl.partialQ (Cyl.partialQ om) y
      + Cyl.partialEta (Cyl.partialEta om) y := rfl
  rw [hsplit, peAdd _ _ (hQQ.differentiable (by simp)) (hEE.differentiable (by simp)) z]
  unfold Train.lapS
  rw [← pqpe_fun (Cyl.partialQ om) hQ, ← pqpe_fun om hom]

/-- Smoothness of the Laplacian. -/
theorem lapS_contDiff (f : Plane → ℝ) (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (Train.lapS f) :=
  (Cyl.contDiff_partialQ (Cyl.contDiff_partialQ hf)).add
    (Cyl.contDiff_partialEta (Cyl.contDiff_partialEta hf))

/-- Smoothness of the vorticity of a smooth field. -/
theorem curl_contDiff {w : Plane → Vec} (hw : ContDiff ℝ ∞ w) :
    ContDiff ℝ ∞ (Cyl.curl w) := by
  have h1 : ContDiff ℝ ∞ (fun y => w y 1) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).contDiff.comp hw
  have h0 : ContDiff ℝ ∞ (fun y => w y 0) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).contDiff.comp hw
  exact (Cyl.contDiff_partialQ h1).sub (Cyl.contDiff_partialEta h0)

/-- Partial derivative of a component is the component of the partial derivative. -/
theorem pqComp (h : Plane → Vec) (hh : Differentiable ℝ h) (i : Fin 2) (z : Plane) :
    Cyl.partialQ (fun y => h y i) z = Cyl.partialQ h z i := by
  have hA : DifferentiableAt ℝ (fun y => h y i) z :=
    (EuclideanSpace.proj (𝕜 := ℝ) i : Vec →L[ℝ] ℝ).differentiableAt.comp z (hh z)
  have hcomp : fderiv ℝ (fun y => h y i) z
      = (EuclideanSpace.proj (𝕜 := ℝ) i : Vec →L[ℝ] ℝ).comp (fderiv ℝ h z) :=
    ((EuclideanSpace.proj (𝕜 := ℝ) i : Vec →L[ℝ] ℝ).hasFDerivAt.comp z
      (hh z).hasFDerivAt).fderiv
  rw [pqAt hA, pqAt (hh z), hcomp]
  rfl

/-- Partial `η`-derivative of a component is the component of the partial derivative. -/
theorem peComp (h : Plane → Vec) (hh : Differentiable ℝ h) (i : Fin 2) (z : Plane) :
    Cyl.partialEta (fun y => h y i) z = Cyl.partialEta h z i := by
  have hA : DifferentiableAt ℝ (fun y => h y i) z :=
    (EuclideanSpace.proj (𝕜 := ℝ) i : Vec →L[ℝ] ℝ).differentiableAt.comp z (hh z)
  have hcomp : fderiv ℝ (fun y => h y i) z
      = (EuclideanSpace.proj (𝕜 := ℝ) i : Vec →L[ℝ] ℝ).comp (fderiv ℝ h z) :=
    ((EuclideanSpace.proj (𝕜 := ℝ) i : Vec →L[ℝ] ℝ).hasFDerivAt.comp z
      (hh z).hasFDerivAt).fderiv
  rw [peAt hA, peAt (hh z), hcomp]
  rfl

/-- The product rule for `∂_q`. -/
theorem pqF4 {f g h k m : Plane → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (hh : Differentiable ℝ h) (hk : Differentiable ℝ k) (hm : Differentiable ℝ m) (ν : ℝ)
    (z : Plane) :
    Cyl.partialQ (fun y => -(f y * g y + h y * k y) + ν * m y) z
      = -(Cyl.partialQ f z * g z + f z * Cyl.partialQ g z
          + (Cyl.partialQ h z * k z + h z * Cyl.partialQ k z)) + ν * Cyl.partialQ m z := by
  rcases z with ⟨q, η⟩
  have d := ((((Cyl.hasDerivAt_sliceQ hf q η).mul (Cyl.hasDerivAt_sliceQ hg q η)).add
      ((Cyl.hasDerivAt_sliceQ hh q η).mul (Cyl.hasDerivAt_sliceQ hk q η))).neg).add
      ((Cyl.hasDerivAt_sliceQ hm q η).const_mul ν)
  exact d.deriv.trans (by ring)

/-- The product rule for `∂_η`. -/
theorem peF4 {f g h k m : Plane → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (hh : Differentiable ℝ h) (hk : Differentiable ℝ k) (hm : Differentiable ℝ m) (ν : ℝ)
    (z : Plane) :
    Cyl.partialEta (fun y => -(f y * g y + h y * k y) + ν * m y) z
      = -(Cyl.partialEta f z * g z + f z * Cyl.partialEta g z
          + (Cyl.partialEta h z * k z + h z * Cyl.partialEta k z)) + ν * Cyl.partialEta m z := by
  rcases z with ⟨q, η⟩
  have d := ((((Cyl.hasDerivAt_sliceEta hf q η).mul (Cyl.hasDerivAt_sliceEta hg q η)).add
      ((Cyl.hasDerivAt_sliceEta hh q η).mul (Cyl.hasDerivAt_sliceEta hk q η))).neg).add
      ((Cyl.hasDerivAt_sliceEta hm q η).const_mul ν)
  exact d.deriv.trans (by ring)

/-- Integrability of `χ_R(η) h(z)` on the cell for continuous `h`. -/
theorem intg_phi {R c : ℝ} (hR : 0 < R) {h : Plane → ℝ} (hh : Continuous h) :
    IntegrableOn (fun z : Plane => etaCutoff R z.2 * h z) (Cyl.cell c) := by
  have hφ : Continuous (fun z : Plane => etaCutoff R z.2) :=
    (ecContDiff R hR).continuous.comp continuous_snd
  exact apHD_integ (c := c) (R0 := 2 * R) (hφ.mul hh)
    (fun z hz => by simp [apHD_eta_zero hR hz.le])

end UnforcedLeray.Short.PartI.FA
