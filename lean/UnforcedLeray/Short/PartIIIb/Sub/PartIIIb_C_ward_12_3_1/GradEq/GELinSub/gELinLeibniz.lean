import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.Props
import UnforcedLeray.Lib.PhaseSpace.Leibniz

/-!
# `GELinLeibniz`: `∂_j(convT V Φ) = convT V ∂_jΦ + convT (∂_jV) Φ` (source 2525-2533)

Task `PartIII-b:C/ward/12/3/1/2/6/2`.  Work componentwise.  With `F(τ,y) = raw τ y` jointly smooth,
the `k`-th component of `convT V Φ` is `∑ᵢ Φᵢ ∂ₖFᵢ - ∑ₘ Fₘ ∂ₘΦₖ`, where `∂ₖ` is the spatial
derivative `fderiv (V τ) y eₖ`.  Differentiating in `y` in direction `e_j` uses the product rule,
the symmetry of the second derivatives of `F` (`IsSymmSndFDerivAt`) and of `Φ`
(`PhaseSpace.dy_dy_comm`), and the chain rule `fderiv (fun y => G (τ,y)) y a = fderiv G (τ,y) (0,a)`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace MeasureTheory Set
open scoped ContDiff
open UnforcedLeray.Cons.C03.Concrete (convT gradUT advT)

/-- Slice derivative: the derivative in `y` of `y ↦ G(τ,y)` is the joint derivative in `(0,a)`. -/
theorem gLeib_slice {G : ℝ × UnforcedLeray.Space → UnforcedLeray.Space}
    (hG : Differentiable ℝ G) (x : ℝ × UnforcedLeray.Space) (a : UnforcedLeray.Space) :
    fderiv ℝ (fun y => G (x.1, y)) x.2 a = fderiv ℝ G x (0, a) := by
  have hg : HasFDerivAt (fun y : UnforcedLeray.Space => ((x.1, y) : ℝ × UnforcedLeray.Space))
      (ContinuousLinearMap.inr ℝ ℝ UnforcedLeray.Space) x.2 :=
    hasFDerivAt_prodMk_right x.1 x.2
  have hc := (hG x).hasFDerivAt.comp x.2 hg
  have hfd : fderiv ℝ (fun y => G (x.1, y)) x.2 =
      (fderiv ℝ G x).comp (ContinuousLinearMap.inr ℝ ℝ UnforcedLeray.Space) := hc.fderiv
  rw [hfd]
  rfl

/-- Spatial derivative of a jointly smooth vector field is jointly smooth. -/
theorem gLeib_partial {F : ℝ × UnforcedLeray.Space → UnforcedLeray.Space}
    (hF : ContDiff ℝ ∞ F) (j : Fin 3) :
    ContDiff ℝ ∞ (fun x : ℝ × UnforcedLeray.Space =>
      fderiv ℝ (fun y => F (x.1, y)) x.2 (EuclideanSpace.single j 1)) := by
  have key : ∀ x : ℝ × UnforcedLeray.Space,
      fderiv ℝ (fun y => F (x.1, y)) x.2 (EuclideanSpace.single j 1) =
        fderiv ℝ F x (0, EuclideanSpace.single j 1) :=
    fun x => gLeib_slice (hF.differentiable (by simp)) x (EuclideanSpace.single j 1)
  have hd : ContDiff ℝ ∞ (fderiv ℝ F) := hF.fderiv_right (m := ∞) (by simp)
  have hfun : (fun x : ℝ × UnforcedLeray.Space =>
      fderiv ℝ (fun y => F (x.1, y)) x.2 (EuclideanSpace.single j 1)) =
      fun x => fderiv ℝ F x (0, EuclideanSpace.single j 1) := funext key
  rw [hfun]
  exact hd.clm_apply contDiff_const

/-- Real-valued smooth functions give smooth complex-valued functions. -/
theorem gLeib_ofReal_c {f : ℝ × UnforcedLeray.Space → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun z => ((f z : ℝ) : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp hf

/-- Derivative of a smooth function is smooth. -/
theorem gLeib_dy_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : ℝ × UnforcedLeray.Space → E) (hG : ContDiff ℝ ∞ G) (m : Fin 3) :
    ContDiff ℝ ∞ (dy m G) :=
  (hG.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

/-- Component of the derivative of a `ℂ³`-valued function. -/
theorem gLeib_comp_dy {G : ℝ × UnforcedLeray.Space → CVec3}
    (hG : Differentiable ℝ G) (j k : Fin 3) (x : ℝ × UnforcedLeray.Space) :
    dy j G x k = dy j (fun z => G z k) x := by
  have h0 := ((EuclideanSpace.proj k : CVec3 →L[ℂ] ℂ).restrictScalars ℝ).hasFDerivAt.comp x
    (hG x).hasFDerivAt
  have e : (fun z => G z k) =
      ((EuclideanSpace.proj k : CVec3 →L[ℂ] ℂ).restrictScalars ℝ) ∘ G := by
    funext z
    simp
  have h : HasFDerivAt (fun z => G z k)
      (((EuclideanSpace.proj k : CVec3 →L[ℂ] ℂ).restrictScalars ℝ).comp (fderiv ℝ G x)) x := by
    rw [e]
    exact h0
  simp only [dy, UnforcedLeray.coordinateVector]
  rw [h.fderiv]
  simp

/-- Component of the derivative of a real-space-valued function. -/
theorem gLeib_comp_dyR {G : ℝ × UnforcedLeray.Space → UnforcedLeray.Space}
    (hG : Differentiable ℝ G) (j m : Fin 3) (x : ℝ × UnforcedLeray.Space) :
    dy j G x m = dy j (fun z => G z m) x := by
  have h0 := ((EuclideanSpace.proj m : UnforcedLeray.Space →L[ℝ] ℝ)).hasFDerivAt.comp x
    (hG x).hasFDerivAt
  have e : (fun z => G z m) = (EuclideanSpace.proj m : UnforcedLeray.Space →L[ℝ] ℝ) ∘ G := by
    funext z
    simp
  have h : HasFDerivAt (fun z => G z m)
      ((EuclideanSpace.proj m : UnforcedLeray.Space →L[ℝ] ℝ).comp (fderiv ℝ G x)) x := by
    rw [e]
    exact h0
  simp only [dy, UnforcedLeray.coordinateVector]
  rw [h.fderiv]
  simp

/-- The derivative of the complex cast of a real function. -/
theorem gLeib_ofReal_dy {f : ℝ × UnforcedLeray.Space → ℝ} (hf : ContDiff ℝ ∞ f)
    (j : Fin 3) (x : ℝ × UnforcedLeray.Space) :
    dy j (fun z => ((f z : ℝ) : ℂ)) x = ((dy j f x : ℝ) : ℂ) := by
  have h : HasFDerivAt (fun z => ((f z : ℝ) : ℂ)) (Complex.ofRealCLM.comp (fderiv ℝ f x)) x :=
    Complex.ofRealCLM.hasFDerivAt.comp x ((hf.differentiable (by simp)) x).hasFDerivAt
  simp only [dy, UnforcedLeray.coordinateVector]
  rw [h.fderiv]
  rfl

/-- Product rule for `dy` on complex-valued smooth functions. -/
theorem gLeib_mul_dy {a b : ℝ × UnforcedLeray.Space → ℂ} (ha : ContDiff ℝ ∞ a)
    (hb : ContDiff ℝ ∞ b) (j : Fin 3) (x : ℝ × UnforcedLeray.Space) :
    dy j (fun z => a z * b z) x = dy j a x * b x + a x * dy j b x := by
  have h : HasFDerivAt (fun z => a z * b z) (a x • fderiv ℝ b x + b x • fderiv ℝ a x) x :=
    ((ha.differentiable (by simp)) x).hasFDerivAt.mul
      ((hb.differentiable (by simp)) x).hasFDerivAt
  simp only [dy, UnforcedLeray.coordinateVector]
  rw [h.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

/-- Difference rule for `dy`. -/
theorem gLeib_sub_dy {f g : ℝ × UnforcedLeray.Space → ℂ} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (j : Fin 3) (x : ℝ × UnforcedLeray.Space) :
    dy j (fun z => f z - g z) x = dy j f x - dy j g x := by
  have h : HasFDerivAt (fun z => f z - g z) (fderiv ℝ f x - fderiv ℝ g x) x :=
    ((hf.differentiable (by simp)) x).hasFDerivAt.sub ((hg.differentiable (by simp)) x).hasFDerivAt
  simp only [dy, UnforcedLeray.coordinateVector]
  rw [h.fderiv]
  simp

/-- Finite-sum rule for `dy`. -/
theorem gLeib_sum_dy {ι : Type*} (s : Finset ι) {f : ι → ℝ × UnforcedLeray.Space → ℂ}
    (hf : ∀ i ∈ s, ContDiff ℝ ∞ (f i)) (j : Fin 3) (x : ℝ × UnforcedLeray.Space) :
    dy j (fun z => ∑ i ∈ s, f i z) x = ∑ i ∈ s, dy j (f i) x := by
  have h : HasFDerivAt (fun z => ∑ i ∈ s, f i z) (∑ i ∈ s, fderiv ℝ (f i) x) x :=
    HasFDerivAt.fun_sum (fun i hi => ((hf i hi).differentiable (by simp) x).hasFDerivAt)
  simp only [dy, UnforcedLeray.coordinateVector]
  rw [h.fderiv]
  simp

/-- Symmetry of the mixed second derivatives of a jointly smooth field in two directions
`(0,a)`, `(0,b)`. -/
theorem gLeib_sym {F : ℝ × UnforcedLeray.Space → UnforcedLeray.Space}
    (hF : ContDiff ℝ ∞ F) (x : ℝ × UnforcedLeray.Space) (a b : UnforcedLeray.Space) :
    fderiv ℝ (fun z => fderiv ℝ F z (0, a)) x (0, b) =
      fderiv ℝ (fun z => fderiv ℝ F z (0, b)) x (0, a) := by
  have hd : Differentiable ℝ (fderiv ℝ F) :=
    (hF.fderiv_right (m := ∞) (by simp)).differentiable (by simp)
  have formula : ∀ (w v z : ℝ × UnforcedLeray.Space),
      fderiv ℝ (fun p => fderiv ℝ F p w) z v = fderiv ℝ (fderiv ℝ F) z v w := by
    intro w v z
    have hx : HasFDerivAt (fun p => fderiv ℝ F p w)
        ((fderiv ℝ (fderiv ℝ F) z).flip w) z := by
      simpa using (hd z).hasFDerivAt.clm_apply (hasFDerivAt_const w z)
    rw [hx.fderiv]
    rfl
  rw [formula, formula]
  exact (hF.contDiffAt.isSymmSndFDerivAt (by simp)).eq _ _

/-- Smoothness of `convT U Ψ` for jointly smooth `U` and smooth `Ψ`. -/
theorem gLeib_convT_smooth {U : ℝ → UnforcedLeray.SpatialField}
    (hU : ContDiff ℝ ∞ (fun x : ℝ × UnforcedLeray.Space => U x.1 x.2))
    {Ψ : ℝ × UnforcedLeray.Space → CVec3} (hΨ : ContDiff ℝ ∞ Ψ) :
    ContDiff ℝ ∞ (convT U Ψ) := by
  refine (contDiff_piLp 2).2 (fun i => ?_)
  show ContDiff ℝ ∞ (fun x : ℝ × UnforcedLeray.Space => convT U Ψ x i)
  have hcomp : (fun x : ℝ × UnforcedLeray.Space => convT U Ψ x i) =
      fun x => (∑ l : Fin 3, Ψ x l *
          ((fderiv ℝ (U x.1) x.2 (EuclideanSpace.single i 1) l : ℝ) : ℂ)) -
        ∑ k : Fin 3, ((U x.1 x.2 k : ℝ) : ℂ) * dy k Ψ x i := by
    funext x
    simp [convT, gradUT, advT, UnforcedLeray.B0412.realC_apply]
  rw [hcomp]
  refine ContDiff.sub ?_ ?_
  · refine ContDiff.sum (fun l _ => ?_)
    exact ((contDiff_piLp 2).1 hΨ l).mul
      (gLeib_ofReal_c ((contDiff_piLp 2).1 (gLeib_partial hU i) l))
  · refine ContDiff.sum (fun k _ => ?_)
    exact (gLeib_ofReal_c ((contDiff_piLp 2).1 hU k)).mul
      ((contDiff_piLp 2).1 (gLeib_dy_smooth Ψ hΨ k) i)

/-- Component formula for `convT`. -/
theorem gLeib_hconvK (U : ℝ → UnforcedLeray.SpatialField)
    (Ψ : ℝ × UnforcedLeray.Space → CVec3) (z : ℝ × UnforcedLeray.Space) (k : Fin 3) :
    convT U Ψ z k =
      (∑ i : Fin 3, Ψ z i * ((fderiv ℝ (U z.1) z.2 (EuclideanSpace.single k 1) i : ℝ) : ℂ)) -
        ∑ m : Fin 3, ((U z.1 z.2 m : ℝ) : ℂ) * dy m Ψ z k := by
  simp [convT, gradUT, advT, UnforcedLeray.B0412.realC_apply]

theorem gELinLeibniz : GELinLeibniz := by
  intro p hp j Φ hΦ
  obtain ⟨hC, -⟩ := hp
  have hF : ContDiff ℝ ∞ (fun x : ℝ × UnforcedLeray.Space => p.raw x.1 x.2) := hC
  have hFd : Differentiable ℝ (fun x : ℝ × UnforcedLeray.Space => p.raw x.1 x.2) :=
    hF.differentiable (by simp)
  have hΦd : Differentiable ℝ Φ := hΦ.differentiable (by simp)
  have hΦi : ∀ i : Fin 3, ContDiff ℝ ∞ (fun z : ℝ × UnforcedLeray.Space => Φ z i) :=
    fun i => (contDiff_piLp 2).1 hΦ i
  have hdyΦ : ∀ m : Fin 3, ContDiff ℝ ∞ (dy m Φ) := fun m => gLeib_dy_smooth Φ hΦ m
  have hdyΦd : ∀ m : Fin 3, Differentiable ℝ (dy m Φ) := fun m => (hdyΦ m).differentiable (by simp)
  have hdyΦc : ∀ m k : Fin 3,
      ContDiff ℝ ∞ (fun z : ℝ × UnforcedLeray.Space => dy m Φ z k) :=
    fun m k => (contDiff_piLp 2).1 (hdyΦ m) k
  have hVc : ∀ m : Fin 3,
      ContDiff ℝ ∞ (fun z : ℝ × UnforcedLeray.Space => ((p.raw z.1 z.2 m : ℝ) : ℂ)) :=
    fun m => gLeib_ofReal_c ((contDiff_piLp 2).1 hF m)
  have hVr : ∀ m : Fin 3,
      ContDiff ℝ ∞ (fun z : ℝ × UnforcedLeray.Space => p.raw z.1 z.2 m) :=
    fun m => (contDiff_piLp 2).1 hF m
  have hPk : ∀ k : Fin 3, ContDiff ℝ ∞
      (fun z : ℝ × UnforcedLeray.Space => fderiv ℝ (p.raw z.1) z.2 (EuclideanSpace.single k 1)) :=
    fun k => gLeib_partial hF k
  have hDr : ∀ k i : Fin 3, ContDiff ℝ ∞
      (fun z : ℝ × UnforcedLeray.Space => fderiv ℝ (p.raw z.1) z.2 (EuclideanSpace.single k 1) i) :=
    fun k i => (contDiff_piLp 2).1 (hPk k) i
  have hDc : ∀ k i : Fin 3, ContDiff ℝ ∞
      (fun z : ℝ × UnforcedLeray.Space =>
        ((fderiv ℝ (p.raw z.1) z.2 (EuclideanSpace.single k 1) i : ℝ) : ℂ)) :=
    fun k i => gLeib_ofReal_c (hDr k i)
  have hG1 : ContDiff ℝ ∞ (convT p.raw Φ) := gLeib_convT_smooth hF hΦ
  have hGj : ContDiff ℝ ∞ (fun z : ℝ × UnforcedLeray.Space => fderiv ℝ
      (fun w : ℝ × UnforcedLeray.Space => p.raw w.1 w.2) z (0, EuclideanSpace.single j 1)) :=
    (hF.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  funext x
  ext k
  simp only [Pi.add_apply, PiLp.add_apply]
  rw [gLeib_comp_dy (hG1.differentiable (by simp)) j k x]
  have e1 : (fun z : ℝ × UnforcedLeray.Space => convT p.raw Φ z k) = fun z =>
      (∑ i : Fin 3, Φ z i * ((fderiv ℝ (p.raw z.1) z.2 (EuclideanSpace.single k 1) i : ℝ) : ℂ)) -
        ∑ m : Fin 3, ((p.raw z.1 z.2 m : ℝ) : ℂ) * dy m Φ z k :=
    funext fun z => gLeib_hconvK p.raw Φ z k
  rw [e1]
  have hS1 : ContDiff ℝ ∞ (fun z : ℝ × UnforcedLeray.Space =>
      ∑ i : Fin 3, Φ z i * ((fderiv ℝ (p.raw z.1) z.2 (EuclideanSpace.single k 1) i : ℝ) : ℂ)) :=
    ContDiff.sum (fun i _ => (hΦi i).mul (hDc k i))
  have hS2 : ContDiff ℝ ∞ (fun z : ℝ × UnforcedLeray.Space =>
      ∑ m : Fin 3, ((p.raw z.1 z.2 m : ℝ) : ℂ) * dy m Φ z k) :=
    ContDiff.sum (fun m _ => (hVc m).mul (hdyΦc m k))
  rw [gLeib_sub_dy hS1 hS2 j x]
  rw [gLeib_sum_dy _ (fun i _ => (hΦi i).mul (hDc k i)) j x]
  rw [gLeib_sum_dy _ (fun m _ => (hVc m).mul (hdyΦc m k)) j x]
  -- the derivative of the rawDV-part
  have hGeq : (fun z : ℝ × UnforcedLeray.Space => fderiv ℝ (p.raw z.1) z.2 (EuclideanSpace.single k 1)) =
      fun z => fderiv ℝ (fun w : ℝ × UnforcedLeray.Space => p.raw w.1 w.2) z
        (0, EuclideanSpace.single k 1) :=
    funext fun z => gLeib_slice hFd z (EuclideanSpace.single k 1)
  have hA : ∀ i : Fin 3,
      dy j (fun z : ℝ × UnforcedLeray.Space => ((fderiv ℝ (p.raw z.1) z.2
        (EuclideanSpace.single k 1) i : ℝ) : ℂ)) x =
        ((fderiv ℝ (rawDV p j x.1) x.2 (EuclideanSpace.single k 1) i : ℝ) : ℂ) := by
    intro i
    rw [gLeib_ofReal_dy (hDr k i) j x]
    congr 1
    rw [← gLeib_comp_dyR ((hPk k).differentiable (by simp)) j i x, hGeq]
    have hsym := gLeib_sym hF x (EuclideanSpace.single k 1) (EuclideanSpace.single j 1)
    have hfun2 : rawDV p j x.1 = fun y => fderiv ℝ (fun w : ℝ × UnforcedLeray.Space => p.raw w.1 w.2)
        (x.1, y) (0, EuclideanSpace.single j 1) :=
      funext fun y => gLeib_slice hFd (x.1, y) (EuclideanSpace.single j 1)
    have hsl : fderiv ℝ (rawDV p j x.1) x.2 (EuclideanSpace.single k 1) =
        fderiv ℝ (fun z => fderiv ℝ (fun w : ℝ × UnforcedLeray.Space => p.raw w.1 w.2) z
          (0, EuclideanSpace.single j 1)) x (0, EuclideanSpace.single k 1) := by
      rw [hfun2, gLeib_slice (hGj.differentiable (by simp)) x (EuclideanSpace.single k 1)]
    simp only [dy, UnforcedLeray.coordinateVector]
    rw [hsym, hsl]
  have hB : ∀ m : Fin 3,
      dy j (fun z : ℝ × UnforcedLeray.Space => ((p.raw z.1 z.2 m : ℝ) : ℂ)) x =
        ((rawDV p j x.1 x.2 m : ℝ) : ℂ) := by
    intro m
    rw [gLeib_ofReal_dy (hVr m) j x]
    congr 1
    rw [← gLeib_comp_dyR hFd j m x]
    simp only [dy, UnforcedLeray.coordinateVector]
    rw [← gLeib_slice hFd x (EuclideanSpace.single j 1)]
    rfl
  have hCm : ∀ m : Fin 3, dy j (fun z : ℝ × UnforcedLeray.Space => dy m Φ z k) x =
      dy m (dy j Φ) x k := by
    intro m
    rw [← gLeib_comp_dy (hdyΦd m) j k x, PhaseSpace.dy_dy_comm hΦ j m]
  have hsumA : ∑ i : Fin 3, dy j (fun z : ℝ × UnforcedLeray.Space =>
      Φ z i * ((fderiv ℝ (p.raw z.1) z.2 (EuclideanSpace.single k 1) i : ℝ) : ℂ)) x =
      ∑ i : Fin 3, (dy j Φ x i * ((fderiv ℝ (p.raw x.1) x.2 (EuclideanSpace.single k 1) i : ℝ) : ℂ) +
        Φ x i * ((fderiv ℝ (rawDV p j x.1) x.2 (EuclideanSpace.single k 1) i : ℝ) : ℂ)) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [gLeib_mul_dy (hΦi i) (hDc k i) j x, ← gLeib_comp_dy hΦd j i x, hA i]
  have hsumB : ∑ m : Fin 3, dy j (fun z : ℝ × UnforcedLeray.Space =>
      ((p.raw z.1 z.2 m : ℝ) : ℂ) * dy m Φ z k) x =
      ∑ m : Fin 3, (((rawDV p j x.1 x.2 m : ℝ) : ℂ) * dy m Φ x k +
        ((p.raw x.1 x.2 m : ℝ) : ℂ) * dy m (dy j Φ) x k) := by
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [gLeib_mul_dy (hVc m) (hdyΦc m k) j x, hB m, hCm m]
  rw [hsumA, hsumB, gLeib_hconvK p.raw (dy j Φ) x k, gLeib_hconvK (rawDV p j) Φ x k]
  simp only [Finset.sum_add_distrib]
  ring

end UnforcedLeray.Short.PartIIIb.Concrete
