import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.Energy.Static.Comm
import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.KT.Defs

/-!
# `PartIII-a:T21/2/7/2/1/1/5/18/2`: the derivation rule of the Friedrichs commutator

Source of record: `the November 2 reference manuscript` lines 3060-3071 (the
regularized adjoint is differentiated in `x`).  `StFriedDeriv` from the shared mollifier leaves
`CellConvDeriv`, `CellMollSmooth`, `CellMollWeakDeriv`, `CellPeriodicLocInt` (`HkStep/Shared.lean`),
the weak Leibniz rule `KTWeakLeibniz` (`HkStep/KT/Defs.lean`) and `StAdjComm`:
`(∂_lρ_n) ⋆ h = ∂_l(ρ_n ⋆ h)`, `∂_j∂_l(ρ_n ⋆ h) = ∂_l(ρ_n ⋆ ∂_jh)`, `∂_j(a_l f) = a_l g + (∂_ja_l) f`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- Convolution with a continuous compactly supported kernel is additive on periodic fields of
`X_{-m,c}` (they are locally integrable on the plane, `CellPeriodicLocInt`). -/
theorem st_cellConv_add (hL : CellPeriodicLocInt) {c m : ℝ} (hc : 0 < c) {K : ℝ × ℝ → ℝ}
    (hK : Continuous K) (hKc : HasCompactSupport K) {f g : ℝ × ℝ → ℂ}
    (hfp : ∀ x : ℝ × ℝ, f (x.1 + c, x.2) = f x) (hgp : ∀ x : ℝ × ℝ, g (x.1 + c, x.2) = g x)
    (hfm : MemLp f 2 (B0579.cellMeasure c (-m))) (hgm : MemLp g 2 (B0579.cellMeasure c (-m))) :
    cellConv K (fun y => f y + g y) = fun x => cellConv K f x + cellConv K g x := by
  have ef := hKc.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ) hK (hL c m f hc hfp hfm).2
  have eg := hKc.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ) hK (hL c m g hc hgp hgm).2
  funext x
  have ef' : Integrable (fun y => K y • f (x - y)) := by
    simpa [ConvolutionExistsAt] using ef x
  have eg' : Integrable (fun y => K y • g (x - y)) := by
    simpa [ConvolutionExistsAt] using eg x
  unfold cellConv
  rw [← integral_add ef' eg']
  congr 1
  funext y
  rw [smul_add]

/-- `(∂_lρ_n) ⋆ h = ∂_l(ρ_n ⋆ h)`. -/
theorem st_convPd_eq (hCD : CellConvDeriv) {c m : ℝ} (hc : 0 < c) (n : ℕ) (l : Fin 2)
    {h : ℝ × ℝ → ℂ} (hp : ∀ x : ℝ × ℝ, h (x.1 + c, x.2) = h x)
    (hm : MemLp h 2 (B0579.cellMeasure c (-m))) :
    cellConv (B0579.pd l (molKer n)) h = pdCx l (cellMoll n h) :=
  ((hCD c m (molKer n) h hc (st_molKer_contDiff n) (st_molKer_hasCompactSupport n) hp
    hm).2.2 [l]).symm

theorem st_rmul_memLp {c m : ℝ} {b : ℝ × ℝ → ℝ} {A : ℝ} (hbc : Continuous b)
    (hb : ∀ x : ℝ × ℝ, |b x| ≤ A) {f : ℝ × ℝ → ℂ} (hf : MemLp f 2 (B0579.cellMeasure c (-m))) :
    MemLp (fun y => ((b y : ℝ) : ℂ) * f y) 2 (B0579.cellMeasure c (-m)) := by
  refine hf.of_le_mul (c := A)
    ((Complex.continuous_ofReal.comp hbc).aestronglyMeasurable.mul hf.1) (ae_of_all _ fun y => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hb y) (norm_nonneg _)

theorem st_rmul_periodic {c : ℝ} {b : ℝ × ℝ → ℝ} (hb : ∀ x : ℝ × ℝ, b (x.1 + c, x.2) = b x)
    {f : ℝ × ℝ → ℂ} (hf : ∀ x : ℝ × ℝ, f (x.1 + c, x.2) = f x) (x : ℝ × ℝ) :
    (fun y => ((b y : ℝ) : ℂ) * f y) (x.1 + c, x.2) = (fun y => ((b y : ℝ) : ℂ) * f y) x := by
  simp only
  rw [hb x, hf x]

theorem st_pd_periodic {c : ℝ} {b : ℝ × ℝ → ℝ} (hb : ∀ x : ℝ × ℝ, b (x.1 + c, x.2) = b x)
    (j : Fin 2) (x : ℝ × ℝ) : B0579.pd j b (x.1 + c, x.2) = B0579.pd j b x := by
  have hfun : (fun y : ℝ × ℝ => b (y + ((c, 0) : ℝ × ℝ))) = b := by
    funext y
    have hy : y + ((c, 0) : ℝ × ℝ) = (y.1 + c, y.2) := by ext <;> simp
    rw [hy]
    exact hb y
  have h := fderiv_comp_add_right (𝕜 := ℝ) (f := b) (x := x) ((c, 0) : ℝ × ℝ)
  rw [hfun] at h
  have hx : x + ((c, 0) : ℝ × ℝ) = (x.1 + c, x.2) := by ext <;> simp
  unfold B0579.pd
  rw [h, hx]

theorem st_pd_contDiff {b : ℝ × ℝ → ℝ} (hb : ContDiff ℝ ∞ b) (j : Fin 2) :
    ContDiff ℝ ∞ (B0579.pd j b) := by
  unfold B0579.pd
  exact (hb.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

/-- `stFried` through the derivatives of the mollification. -/
theorem st_fried_form (hCD : CellConvDeriv) {c m : ℝ} (hc : 0 < c) (n : ℕ)
    (b : Fin 2 → ℝ × ℝ → ℝ) (h : ℝ × ℝ → ℂ)
    (hbp : ∀ l (x : ℝ × ℝ), (fun y => ((b l y : ℝ) : ℂ) * h y) (x.1 + c, x.2) =
      (fun y => ((b l y : ℝ) : ℂ) * h y) x)
    (hbm : ∀ l, MemLp (fun y => ((b l y : ℝ) : ℂ) * h y) 2 (B0579.cellMeasure c (-m)))
    (hp : ∀ x : ℝ × ℝ, h (x.1 + c, x.2) = h x) (hm : MemLp h 2 (B0579.cellMeasure c (-m))) :
    stFried n b h = fun x => ∑ l : Fin 2,
      (pdCx l (cellMoll n (fun y => ((b l y : ℝ) : ℂ) * h y)) x -
        ((b l x : ℝ) : ℂ) * pdCx l (cellMoll n h) x) := by
  funext x
  unfold stFried
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [st_convPd_eq hCD hc n l (hbp l) (hbm l), st_convPd_eq hCD hc n l hp hm]

/-- **`StFriedDeriv` from the shared leaves.** -/
theorem stFriedDeriv_of (hCD : CellConvDeriv) (hS : CellMollSmooth) (hW : CellMollWeakDeriv)
    (hL : CellPeriodicLocInt) (hComm : StAdjComm) (hKW : KTWeakLeibniz) : StFriedDeriv := by
  intro c m n a f hc ha hap hA hfp hfm
  obtain ⟨A, hA⟩ := hA
  have hafp : ∀ l (x : ℝ × ℝ), (fun y => ((a l y : ℝ) : ℂ) * f y) (x.1 + c, x.2) =
      (fun y => ((a l y : ℝ) : ℂ) * f y) x := fun l => st_rmul_periodic (hap l) hfp
  have hafm : ∀ l, MemLp (fun y => ((a l y : ℝ) : ℂ) * f y) 2 (B0579.cellMeasure c (-m)) :=
    fun l => st_rmul_memLp (ha l).continuous (fun x => (hA l x).1) hfm
  have hf1 : ContDiff ℝ ∞ (cellMoll n f) := (hS c m n f hc hfp hfm).1
  refine ⟨?_, ?_⟩
  · rw [st_fried_form hCD hc n a f hafp hafm hfp hfm]
    have h1 : ∀ l : Fin 2,
        ContDiff ℝ ∞ (pdCx l (cellMoll n (fun y => ((a l y : ℝ) : ℂ) * f y))) :=
      fun l => st_contDiff_pdCx (hS c m n _ hc (hafp l) (hafm l)).1 l
    have h3 : ∀ l : Fin 2,
        ContDiff ℝ ∞ (fun x => ((a l x : ℝ) : ℂ) * pdCx l (cellMoll n f) x) :=
      fun l => (Complex.ofRealCLM.contDiff.comp (ha l)).mul (st_contDiff_pdCx hf1 l)
    simp only [Fin.sum_univ_two]
    exact ((h1 0).sub (h3 0)).add ((h1 1).sub (h3 1))
  · intro j g hgp hgm hfg
    have hg1 : ContDiff ℝ ∞ (cellMoll n g) := (hS c m n g hc hgp hgm).1
    -- the fields `a_l g` and `(∂_j a_l) f`
    have hagp : ∀ l (x : ℝ × ℝ), (fun y => ((a l y : ℝ) : ℂ) * g y) (x.1 + c, x.2) =
        (fun y => ((a l y : ℝ) : ℂ) * g y) x := fun l => st_rmul_periodic (hap l) hgp
    have hagm : ∀ l, MemLp (fun y => ((a l y : ℝ) : ℂ) * g y) 2 (B0579.cellMeasure c (-m)) :=
      fun l => st_rmul_memLp (ha l).continuous (fun x => (hA l x).1) hgm
    have hdfp : ∀ l (x : ℝ × ℝ),
        (fun y => ((B0579.pd j (a l) y : ℝ) : ℂ) * f y) (x.1 + c, x.2) =
          (fun y => ((B0579.pd j (a l) y : ℝ) : ℂ) * f y) x :=
      fun l => st_rmul_periodic (st_pd_periodic (hap l) j) hfp
    have hdfm : ∀ l, MemLp (fun y => ((B0579.pd j (a l) y : ℝ) : ℂ) * f y) 2
        (B0579.cellMeasure c (-m)) :=
      fun l => st_rmul_memLp (st_pd_contDiff (ha l) j).continuous (fun x => (hA l x).2 j) hfm
    -- the derivative of the first summand
    have hP : ∀ l : Fin 2, pdCx j (pdCx l (cellMoll n (fun y => ((a l y : ℝ) : ℂ) * f y))) =
        fun x => pdCx l (cellMoll n (fun y => ((a l y : ℝ) : ℂ) * g y)) x +
          pdCx l (cellMoll n (fun y => ((B0579.pd j (a l) y : ℝ) : ℂ) * f y)) x := by
      intro l
      have hsm := (hS c m n _ hc (hafp l) (hafm l)).1
      have hLb : HasWeakCellDerivC c j (fun y => ((a l y : ℝ) : ℂ) * f y)
          (fun y => ((a l y : ℝ) : ℂ) * g y + ((B0579.pd j (a l) y : ℝ) : ℂ) * f y) := by
        have h := hKW m c hc j f g (a l) (ha l) (hap l) ⟨A, fun x => ⟨(hA l x).1, (hA l x).2 j⟩⟩
          hfg hfm hgm
        have e1 : (fun x => f x * ((a l x : ℝ) : ℂ)) = fun y => ((a l y : ℝ) : ℂ) * f y := by
          funext x; ring
        have e2 : (fun x => g x * ((a l x : ℝ) : ℂ) + f x * ((B0579.pd j (a l) x : ℝ) : ℂ)) =
            fun y => ((a l y : ℝ) : ℂ) * g y + ((B0579.pd j (a l) y : ℝ) : ℂ) * f y := by
          funext x; ring
        rwa [e1, e2] at h
      have hsump : ∀ x : ℝ × ℝ,
          (fun y => ((a l y : ℝ) : ℂ) * g y + ((B0579.pd j (a l) y : ℝ) : ℂ) * f y)
            (x.1 + c, x.2) =
          (fun y => ((a l y : ℝ) : ℂ) * g y + ((B0579.pd j (a l) y : ℝ) : ℂ) * f y) x := by
        intro x
        simp only
        rw [hap l x, hgp x, st_pd_periodic (hap l) j x, hfp x]
      have hsumm : MemLp (fun y => ((a l y : ℝ) : ℂ) * g y + ((B0579.pd j (a l) y : ℝ) : ℂ) * f y)
          2 (B0579.cellMeasure c (-m)) := (hagm l).add (hdfm l)
      have hd : pdCx j (cellMoll n (fun y => ((a l y : ℝ) : ℂ) * f y)) =
          cellMoll n (fun y => ((a l y : ℝ) : ℂ) * g y + ((B0579.pd j (a l) y : ℝ) : ℂ) * f y) :=
        hW c m j _ _ hc (hafp l) hsump (hafm l) hsumm hLb n
      have hadd : cellMoll n (fun y => ((a l y : ℝ) : ℂ) * g y +
          ((B0579.pd j (a l) y : ℝ) : ℂ) * f y) = fun x =>
            cellMoll n (fun y => ((a l y : ℝ) : ℂ) * g y) x +
              cellMoll n (fun y => ((B0579.pd j (a l) y : ℝ) : ℂ) * f y) x :=
        st_cellConv_add hL hc (st_molKer_contDiff n).continuous (st_molKer_hasCompactSupport n)
          (hagp l) (hdfp l) (hagm l) (hdfm l)
      have hsym : pdCx j (pdCx l (cellMoll n (fun y => ((a l y : ℝ) : ℂ) * f y))) =
          pdCx l (pdCx j (cellMoll n (fun y => ((a l y : ℝ) : ℂ) * f y))) :=
        hComm _ hsm [j] l
      rw [hsym, hd, hadd]
      exact st_pdCx_add (st_differentiable (hS c m n _ hc (hagp l) (hagm l)).1)
        (st_differentiable (hS c m n _ hc (hdfp l) (hdfm l)).1) l
    -- the derivative of the second summand
    have hQ : ∀ l : Fin 2, pdCx j (fun x => ((a l x : ℝ) : ℂ) * pdCx l (cellMoll n f) x) =
        fun x => ((B0579.pd j (a l) x : ℝ) : ℂ) * pdCx l (cellMoll n f) x +
          ((a l x : ℝ) : ℂ) * pdCx l (cellMoll n g) x := by
      intro l
      rw [st_pdCx_ofReal_mul ((ha l).differentiable (by simp))
        (st_differentiable (st_contDiff_pdCx hf1 l)) j]
      have hsym : pdCx j (pdCx l (cellMoll n f)) = pdCx l (pdCx j (cellMoll n f)) :=
        hComm _ hf1 [j] l
      rw [hsym, hW c m j f g hc hfp hgp hfm hgm hfg n]
    -- assemble
    rw [st_fried_form hCD hc n a f hafp hafm hfp hfm,
      st_fried_form hCD hc n (fun l => B0579.pd j (a l)) f hdfp hdfm hfp hfm,
      st_fried_form hCD hc n a g hagp hagm hgp hgm]
    have hd1 : ∀ l : Fin 2,
        Differentiable ℝ (pdCx l (cellMoll n (fun y => ((a l y : ℝ) : ℂ) * f y))) :=
      fun l => st_differentiable (st_contDiff_pdCx (hS c m n _ hc (hafp l) (hafm l)).1 l)
    have hd2 : ∀ l : Fin 2,
        Differentiable ℝ (fun x => ((a l x : ℝ) : ℂ) * pdCx l (cellMoll n f) x) :=
      fun l => st_differentiable
        ((Complex.ofRealCLM.contDiff.comp (ha l)).mul (st_contDiff_pdCx hf1 l))
    have hD : ∀ l : Fin 2, Differentiable ℝ (fun x =>
        pdCx l (cellMoll n (fun y => ((a l y : ℝ) : ℂ) * f y)) x -
          ((a l x : ℝ) : ℂ) * pdCx l (cellMoll n f) x) := fun l => (hd1 l).sub (hd2 l)
    simp only [Fin.sum_univ_two]
    rw [st_pdCx_add (hD 0) (hD 1), st_pdCx_sub (hd1 0) (hd2 0),
      st_pdCx_sub (hd1 1) (hd2 1), hP 0, hP 1, hQ 0, hQ 1]
    funext x
    ring

end UnforcedLeray.Short.IIIa
