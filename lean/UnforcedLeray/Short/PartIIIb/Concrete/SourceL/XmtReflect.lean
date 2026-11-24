import UnforcedLeray.Short.PartIIIb.Concrete.SourceL

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace XmtRefl

/-! ## Sign vector and reflection algebra -/

/-- Sign vector of the reflection `reflY`, the diagonal `diag(1,-1,1)`. -/
def sg : Fin 3 → ℝ := ![1, -1, 1]

theorem sg_zero : sg 0 = 1 := by simp [sg]
theorem sg_one : sg 1 = -1 := by simp [sg]
theorem sg_two : sg 2 = 1 := by simp [sg]

theorem sg_pm (k : Fin 3) : sg k = 1 ∨ sg k = -1 := by
  fin_cases k <;> simp [sg]

theorem sg_pm2 (j k : Fin 3) : sg j * sg k = 1 ∨ sg j * sg k = -1 := by
  rcases sg_pm j with h | h <;> rcases sg_pm k with h' | h' <;> simp [h, h']

theorem sg_sq (k : Fin 3) : sg k * sg k = 1 := by
  rcases sg_pm k with h | h <;> simp [h]

theorem reflY_reflY (v : Vec3) : reflY (reflY v) = v := by
  funext i; fin_cases i <;> simp [reflY]

theorem reflY_sub (a b : Vec3) : reflY (a - b) = reflY a - reflY b := by
  funext i; fin_cases i <;> simp [reflY] <;> ring

theorem reflY_add (a b : Vec3) : reflY (a + b) = reflY a + reflY b := by
  funext i; fin_cases i <;> simp [reflY] <;> ring

theorem reflY_smul (t : ℝ) (v : Vec3) : reflY (t • v) = t • reflY v := by
  funext i; fin_cases i <;> simp [reflY]

theorem reflY_ez : reflY (![0, 0, 1] : Vec3) = ![0, 0, 1] := by
  funext i; fin_cases i <;> simp [reflY]

theorem reflY_single (k : Fin 3) : reflY (Pi.single k 1) = sg k • Pi.single k 1 := by
  funext i
  fin_cases k <;> fin_cases i <;> simp [reflY, sg]

theorem reflY_apply_idx (v : Vec3) (i : Fin 3) : reflY v i = sg i * v i := by
  fin_cases i <;> simp [reflY, sg]

/-- The reflection as a continuous linear equivalence. -/
def reflL : Vec3 ≃L[ℝ] Vec3 :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := reflY
      map_add' := fun a b => reflY_add a b
      map_smul' := fun t v => reflY_smul t v
      invFun := reflY
      left_inv := fun v => reflY_reflY v
      right_inv := fun v => reflY_reflY v }

theorem reflL_apply (y : Vec3) : reflL y = reflY y := rfl

/-! ## Derivatives under the reflection -/

theorem fderiv_reflY (f : Vec3 → ℝ) (s : ℝ) (hs : s = 1 ∨ s = -1)
    (hf : ∀ y, f (reflY y) = s * f y) (y v : Vec3) :
    fderiv ℝ f (reflY y) (reflY v) = s * fderiv ℝ f y v := by
  have h1 : fderiv ℝ (f ∘ reflL) y = (fderiv ℝ f (reflL y)).comp (reflL : Vec3 →L[ℝ] Vec3) :=
    ContinuousLinearEquiv.comp_right_fderiv reflL
  have h2 : (f ∘ reflL) = fun z => s * f z := funext fun z => hf z
  have h3 : fderiv ℝ (f ∘ reflL) y = s • fderiv ℝ f y := by
    rw [h2]
    rcases hs with rfl | rfl
    · simp
    · have hneg : (fun z => (-1 : ℝ) * f z) = -f := funext fun z => by simp
      rw [hneg, fderiv_neg]
      exact (neg_one_smul ℝ (fderiv ℝ f y)).symm
  have h4 := congrArg (fun L : Vec3 →L[ℝ] ℝ => L v) (h1.symm.trans h3)
  simpa [reflL_apply] using h4

theorem eig (f : Vec3 → ℝ) (s : ℝ) (hs : s = 1 ∨ s = -1)
    (hf : ∀ y, f (reflY y) = s * f y) (j : Fin 3) (y : Vec3) :
    fderiv ℝ f (reflY y) (Pi.single j 1) = s * sg j * fderiv ℝ f y (Pi.single j 1) := by
  have h := fderiv_reflY f s hs hf y (Pi.single j 1)
  rw [reflY_single j] at h
  simp only [map_smul, smul_eq_mul] at h
  linear_combination (sg j) * h - (fderiv ℝ f (reflY y) (Pi.single j 1)) * sg_sq j

/-! ## The Newton kernel and its third derivatives -/

theorem newtonN_reflY (w : Vec3) : newtonN (reflY w) = newtonN w := by
  unfold newtonN
  simp [reflY, Fin.sum_univ_three]

/-- `G_k(z) = ∂_k N(z)`. -/
def Gk (k : Fin 3) (z : Vec3) : ℝ := fderiv ℝ newtonN z (Pi.single k 1)

/-- `H_jk(y) = ∂_j G_k(y)`. -/
def Hjk (j k : Fin 3) (y : Vec3) : ℝ := fderiv ℝ (Gk k) y (Pi.single j 1)

theorem newtonD3_eq (x : Vec3) (i j k : Fin 3) :
    newtonD3 x i j k = fderiv ℝ (Hjk j k) x (Pi.single i 1) := rfl

theorem Gk_reflY (k : Fin 3) (y : Vec3) : Gk k (reflY y) = sg k * Gk k y := by
  have hN : ∀ z, newtonN (reflY z) = 1 * newtonN z := fun z => by
    rw [newtonN_reflY, one_mul]
  unfold Gk
  rw [eig newtonN 1 (Or.inl rfl) hN k y]
  ring

theorem Hjk_reflY (j k : Fin 3) (y : Vec3) : Hjk j k (reflY y) = (sg j * sg k) * Hjk j k y := by
  unfold Hjk
  rw [eig (Gk k) (sg k) (sg_pm k) (Gk_reflY k) j y]
  ring

theorem newtonD3_reflY (w : Vec3) (i j k : Fin 3) :
    newtonD3 (reflY w) i j k = sg i * sg j * sg k * newtonD3 w i j k := by
  rw [newtonD3_eq, newtonD3_eq, eig (Hjk j k) (sg j * sg k) (sg_pm2 j k) (Hjk_reflY j k) i w]
  ring

/-! ## The swap of the plane coordinates -/

/-- `σ(a,b) = (a,-b)` on the plane, as a measurable equivalence. -/
def sigE : ℝ × ℝ ≃ᵐ ℝ × ℝ :=
  MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) (MeasurableEquiv.neg ℝ)

theorem sigE_apply (x : ℝ × ℝ) : sigE x = (x.1, -x.2) := rfl

theorem sigE_measurePreserving : MeasurePreserving sigE volume volume := by
  have h := (MeasurePreserving.id (volume : Measure ℝ)).prod
    (Measure.measurePreserving_neg (volume : Measure ℝ))
  have hv : (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume := rfl
  rw [← hv] at h
  exact h

theorem embPlane_sigE (y : ℝ × ℝ) : embPlane (sigE y) = reflY (embPlane y) := by
  rw [sigE_apply]
  funext i
  fin_cases i <;> simp [embPlane, reflY]

theorem sigmaM_sigE (c ν : ℝ) (χo : ℝ → ℝ) (M : Chart → Mat3) (y : ℝ × ℝ) (a b : Fin 3) :
    sigmaM c ν χo M (sigE y) a b = sg a * sg b * sigmaM c ν χo M y a b := by
  rw [sigE_apply]
  have hQ : ∀ a i, rotQ (y.1, -y.2) a i = sg a * sg i * rotQ y a i := by
    intro a i
    fin_cases a <;> fin_cases i <;> simp [rotQ, sg, neg_sq] <;> ring
  have hpm : ∀ (u : ℝ) (i j : Fin 3),
      sg i * sg j * phaseMean c ν χo M u i j = phaseMean c ν χo M u i j := by
    intro u i j
    fin_cases i <;> fin_cases j <;> simp [phaseMean, sg]
  simp only [sigmaM, neg_sq, hQ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  linear_combination (sg a * sg b * rotQ y a i * ((Real.sqrt (y.1 ^ 2 + y.2 ^ 2))⁻¹) * rotQ y b j) *
    hpm ((y.1 ^ 2 + y.2 ^ 2)⁻¹) i j

/-! ## Equivariance of the zero-width Newton field and of `X^mt` -/

theorem newtonV_reflY (c ν μ : ℝ) (χo : ℝ → ℝ) (M : Chart → Mat3) (x : Vec3) :
    newtonV c ν μ χo M (reflY x) = reflY (newtonV c ν μ χo M x) := by
  funext i
  have hpt : ∀ (t : ℝ) (y : ℝ × ℝ),
      (∑ j, ∑ k, newtonD3 (reflY x - t • embPlane (sigE y)) i j k * sigmaM c ν χo M (sigE y) j k)
        = sg i * ∑ j, ∑ k, newtonD3 (x - t • embPlane y) i j k * sigmaM c ν χo M y j k := by
    intro t y
    have hw : reflY x - t • embPlane (sigE y) = reflY (x - t • embPlane y) := by
      rw [embPlane_sigE, reflY_sub, reflY_smul]
    rw [hw]
    simp only [newtonD3_reflY, sigmaM_sigE, Fin.sum_univ_three, sg_zero, sg_one, sg_two]
    ring
  have key : ∀ t : ℝ,
      ∫ x' : ℝ × ℝ, (∑ j, ∑ k, newtonD3 (reflY x - t • embPlane x') i j k * sigmaM c ν χo M x' j k)
        = sg i * ∫ x' : ℝ × ℝ, (∑ j, ∑ k, newtonD3 (x - t • embPlane x') i j k * sigmaM c ν χo M x' j k) := by
    intro t
    rw [← integral_const_mul]
    refine ((sigE_measurePreserving.integral_comp' _).symm).trans ?_
    congr 1
    funext y
    exact hpt t y
  have hT : ∀ t : ℝ,
      t ^ (2 * μ + 2) * ∫ x' : ℝ × ℝ,
          (∑ j, ∑ k, newtonD3 (reflY x - t • embPlane x') i j k * sigmaM c ν χo M x' j k)
        = sg i * (t ^ (2 * μ + 2) * ∫ x' : ℝ × ℝ,
          (∑ j, ∑ k, newtonD3 (x - t • embPlane x') i j k * sigmaM c ν χo M x' j k)) := by
    intro t
    rw [key t]
    ring
  simp only [newtonV, reflY_apply_idx]
  simp only [hT, integral_const_mul]
  ring

theorem youngW_reflY (c ν ε μ : ℝ) (χo : ℝ → ℝ) (M : Chart → Mat3) (y : Vec3) :
    youngW c ν ε μ χo M (reflY y) = reflY (youngW c ν ε μ χo M y) := by
  unfold youngW
  rw [← reflY_smul, newtonV_reflY, reflY_smul]

/-- The reflection statement of the source (source 4771-4791, 4178-4186). -/
theorem xmtReflect : XmtReflect := by
  intro c ν ε μ χo χy M y
  unfold Xmt
  set Z : Vec3 → Vec3 := youngW c ν ε μ χo M - youngW c ν ε (μ + 1) χo M with hZdef
  have hZr : ∀ w, Z (reflY w) = reflY (Z w) := by
    intro w
    simp only [hZdef, Pi.sub_apply, youngW_reflY, reflY_sub]
  have hZ2 : ∀ w, Z (reflY w) 2 = Z w 2 := by
    intro w
    rw [hZr]
    simp [reflY]
  have hcyl : cylR (reflY y) = cylR y := by
    simp [cylR, reflY]
  have hray : ∀ ρ, rayPt (reflY y) ρ = reflY (rayPt y ρ) := by
    intro ρ
    funext i
    simp only [rayPt, hcyl]
    fin_cases i <;> simp [reflY] <;> ring
  have hpsi : streamPsi Z (reflY y) = streamPsi Z y := by
    simp only [streamPsi, hcyl, hray, hZ2]
  unfold streamCut
  rw [hcyl, hpsi, hZr, reflY_add, reflY_smul, reflY_smul, reflY_ez]

end XmtRefl

end UnforcedLeray.Short.PartIIIb.Concrete
