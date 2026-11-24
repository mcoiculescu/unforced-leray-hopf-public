import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_3_2_1_org
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_1.ProdHom.Calc

/-!
# `realCOpsBridge` (`PartIII-b:C/rep/8/2/pres/3/2/1/2`)

Source of record: `the November 2 reference manuscript`
1263, 4140-4141 (`D₀U + U·∇U + ∇p = 0`).

Data-free calculus: for `W = realC ∘ X`, the complexified operators `L₀`, `advT`, `gradT` of the
real fields are `realC` of the physical operators `physDmu`, `fderiv X (X)` and `physGrad`.
Derivatives of `realC ∘ H` are `realC` of derivatives (`realCLI` is a real linear isometry), and
the slice identities `fderiv (X t) y v = fderiv X̂ (t,y) (0,v)` and its second-order analogue
identify the `y`-derivatives of `X̂` with those of the slice `X t`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `realC` commutes with the Fréchet derivative: `D(realC ∘ H) = realC ∘ DH`. -/
theorem rcb_fderiv_realC (H : ℝ × Space → Space) (x : ℝ × Space) (hH : DifferentiableAt ℝ H x)
    (v : ℝ × Space) :
    fderiv ℝ (fun q => UnforcedLeray.B0412.realC (H q)) x v =
      UnforcedLeray.B0412.realC (fderiv ℝ H x v) := by
  have h := (realCLI.toContinuousLinearMap.hasFDerivAt.comp x hH.hasFDerivAt).fderiv
  have e : (fun q => UnforcedLeray.B0412.realC (H q)) = realCLI.toContinuousLinearMap ∘ H := rfl
  rw [e, h]
  rfl

/-- The same for a real-valued function composed with `ℝ ↪ ℂ`. -/
theorem rcb_fderiv_ofReal (P : ℝ × Space → ℝ) (x : ℝ × Space) (hP : DifferentiableAt ℝ P x)
    (v : ℝ × Space) :
    fderiv ℝ (fun q => ((P q : ℝ) : ℂ)) x v = ((fderiv ℝ P x v : ℝ) : ℂ) := by
  have h := (Complex.ofRealCLM.hasFDerivAt.comp x hP.hasFDerivAt).fderiv
  have e : (fun q => ((P q : ℝ) : ℂ)) = Complex.ofRealCLM ∘ P := rfl
  rw [e, h]
  rfl

theorem rcb_add (a b : Space) :
    UnforcedLeray.B0412.realC (a + b) = UnforcedLeray.B0412.realC a + UnforcedLeray.B0412.realC b :=
  realCLI.map_add a b

theorem rcb_sub (a b : Space) :
    UnforcedLeray.B0412.realC (a - b) = UnforcedLeray.B0412.realC a - UnforcedLeray.B0412.realC b :=
  map_sub realCLI a b

theorem rcb_smul (c : ℝ) (a : Space) :
    UnforcedLeray.B0412.realC (c • a) = c • UnforcedLeray.B0412.realC a :=
  realCLI.map_smul c a

theorem rcb_cs (c : ℝ) (v : Space) :
    ((c : ℂ)) • UnforcedLeray.B0412.realC v = UnforcedLeray.B0412.realC (c • v) := by
  ext i
  simp [UnforcedLeray.B0412.realC_apply]

theorem rcb_sum_coord (y : Space) : ∑ j : Fin 3, y j • (coordinateVector j) = y := by
  ext k
  simp [coordinateVector, Pi.single_apply]

/-- The slice identity at a point of differentiability:
`∂_y (X t) v = ∂X̂ (t,y) (0,v)`. -/
theorem rcb_slice1 (X : ℝ → Space → Space) (t : ℝ) (y v : Space)
    (hF : DifferentiableAt ℝ (fun q : ℝ × Space => X q.1 q.2) (t, y)) :
    fderiv ℝ (X t) y v = fderiv ℝ (fun q : ℝ × Space => X q.1 q.2) (t, y) (0, v) := by
  have h1 : HasFDerivAt (fun z : Space => ((t, z) : ℝ × Space))
      (ContinuousLinearMap.inr ℝ ℝ Space) y :=
    hasFDerivAt_prodMk_right t y
  have h2 := hF.hasFDerivAt.comp y h1
  have h3 : fderiv ℝ (X t) y = (fderiv ℝ (fun q : ℝ × Space => X q.1 q.2) (t, y)).comp
      (ContinuousLinearMap.inr ℝ ℝ Space) := h2.fderiv
  rw [h3]
  simp

/-- The real-valued slice identity at a point of differentiability. -/
theorem rcb_slice1R (P : ℝ × Space → ℝ) (t : ℝ) (y v : Space)
    (hP : DifferentiableAt ℝ P (t, y)) :
    fderiv ℝ (fun z : Space => P (t, z)) y v = fderiv ℝ P (t, y) (0, v) := by
  have h1 : HasFDerivAt (fun z : Space => ((t, z) : ℝ × Space))
      (ContinuousLinearMap.inr ℝ ℝ Space) y :=
    hasFDerivAt_prodMk_right t y
  have h2 := hP.hasFDerivAt.comp y h1
  have h3 : fderiv ℝ (fun z : Space => P (t, z)) y = (fderiv ℝ P (t, y)).comp
      (ContinuousLinearMap.inr ℝ ℝ Space) := h2.fderiv
  rw [h3]
  simp

/-- The second-order slice identity: `∂_{y}∂_{y} (X t)` is the `y`-slice of `∂X̂`. -/
theorem rcb_slice2 (X : ℝ → Space → Space) (t : ℝ) (y v w : Space)
    (hC : ContDiffAt ℝ 2 (fun q : ℝ × Space => X q.1 q.2) (t, y)) :
    fderiv ℝ (fun p : ℝ × Space => fderiv ℝ (fun q : ℝ × Space => X q.1 q.2) p (0, v)) (t, y)
        (0, w) =
      fderiv ℝ (fun y' : Space => fderiv ℝ (X t) y' v) y w := by
  have hDF : DifferentiableAt ℝ (fderiv ℝ (fun q : ℝ × Space => X q.1 q.2)) (t, y) :=
    (hC.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hG : DifferentiableAt ℝ
      (fun p : ℝ × Space => fderiv ℝ (fun q : ℝ × Space => X q.1 q.2) p (0, v)) (t, y) :=
    hDF.clm_apply (differentiableAt_const _)
  have hev : (fun y' : Space => fderiv ℝ (X t) y' v) =ᶠ[𝓝 y]
      (fun y' : Space => fderiv ℝ (fun q : ℝ × Space => X q.1 q.2) (t, y') (0, v)) := by
    have hc : ∀ᶠ p in 𝓝 (t, y), ContDiffAt ℝ 2 (fun q : ℝ × Space => X q.1 q.2) p :=
      hC.eventually (by simp)
    have ht : Tendsto (fun y' : Space => ((t, y') : ℝ × Space)) (𝓝 y) (𝓝 (t, y)) :=
      (continuous_const.prodMk continuous_id).tendsto y
    filter_upwards [ht.eventually hc] with y' hy'
    exact rcb_slice1 X t y' v (hy'.differentiableAt (by norm_num))
  rw [hev.fderiv_eq]
  rw [show (fun y' : Space => fderiv ℝ (fun q : ℝ × Space => X q.1 q.2) (t, y') (0, v)) =
      (fun p : ℝ × Space => fderiv ℝ (fun q : ℝ × Space => X q.1 q.2) p (0, v)) ∘
        (fun z : Space => ((t, z) : ℝ × Space)) from rfl]
  rw [(hG.hasFDerivAt.comp y (hasFDerivAt_prodMk_right t y)).fderiv]
  simp

/-- `∂_τ` of a jointly differentiable field is the time derivative of the slice. -/
theorem rcb_dtau_eq (X : ℝ → Space → Space) (t : ℝ) (y : Space)
    (hF : DifferentiableAt ℝ (fun q : ℝ × Space => X q.1 q.2) (t, y)) :
    fderiv ℝ (fun q : ℝ × Space => X q.1 q.2) (t, y) (1, 0) = deriv (fun s => X s y) t := by
  have hs : HasFDerivAt (fun s : ℝ => ((s, y) : ℝ × Space)) (ContinuousLinearMap.inl ℝ ℝ Space) t :=
    hasFDerivAt_prodMk_left t y
  have h := hF.hasFDerivAt.comp t hs
  have hd := h.hasDerivAt.deriv
  have e : deriv (fun s => X s y) t =
      deriv ((fun q : ℝ × Space => X q.1 q.2) ∘ (fun s : ℝ => ((s, y) : ℝ × Space))) t := rfl
  rw [e, hd]
  simp

/-- **`realCOpsBridge`** (source 1263, 4140-4141): the complexified operators of the realified
repair field are the realification of the physical operators. -/
theorem realCOpsBridge : RealCOpsBridge := by
  intro ν X Pr z hX hPr
  obtain ⟨t, y⟩ := z
  have hF : DifferentiableAt ℝ (fun q : ℝ × Space => X q.1 q.2) (t, y) :=
    hX.differentiableAt (by norm_num)
  have hev : ∀ᶠ p in 𝓝 (t, y), DifferentiableAt ℝ (fun q : ℝ × Space => X q.1 q.2) p :=
    (hX.eventually (by simp)).mono fun p hp => hp.differentiableAt (by norm_num)
  have hDF : DifferentiableAt ℝ
      (fderiv ℝ (fun q : ℝ × Space => X q.1 q.2)) (t, y) :=
    (hX.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  -- the spatial derivatives of `W = realC ∘ X̂` near the point
  have hdy : ∀ j : Fin 3,
      PhaseSpace.dy j (fun q : ℝ × Space => UnforcedLeray.B0412.realC (X q.1 q.2))
        =ᶠ[𝓝 (t, y)] (fun q : ℝ × Space => UnforcedLeray.B0412.realC
          (fderiv ℝ (fun q' : ℝ × Space => X q'.1 q'.2) q (0, coordinateVector j))) := by
    intro j
    filter_upwards [hev] with q hq
    simp only [PhaseSpace.dy]
    exact rcb_fderiv_realC _ q hq _
  -- the second spatial derivatives
  have hlap1 : ∀ j : Fin 3,
      PhaseSpace.dy j (PhaseSpace.dy j (fun q : ℝ × Space => UnforcedLeray.B0412.realC (X q.1 q.2)))
        (t, y) = UnforcedLeray.B0412.realC (physPd2 (X t) j j y) := by
    intro j
    have hDj : DifferentiableAt ℝ
        (fun q : ℝ × Space => fderiv ℝ (fun q' : ℝ × Space => X q'.1 q'.2) q (0, coordinateVector j))
        (t, y) :=
      hDF.clm_apply (differentiableAt_const _)
    have e1 : PhaseSpace.dy j (PhaseSpace.dy j (fun q : ℝ × Space => UnforcedLeray.B0412.realC (X q.1 q.2)))
        (t, y) = fderiv ℝ (PhaseSpace.dy j (fun q : ℝ × Space => UnforcedLeray.B0412.realC (X q.1 q.2)))
          (t, y) (0, coordinateVector j) := rfl
    rw [e1, (hdy j).fderiv_eq, rcb_fderiv_realC _ _ hDj]
    congr 1
    rw [show physPd2 (X t) j j y = fderiv ℝ (fun y' : Space => fderiv ℝ (X t) y' (coordinateVector j))
        y (coordinateVector j) from rfl]
    exact rcb_slice2 X t y _ _ hX
  have hLap : PhaseSpace.lapT (fun q : ℝ × Space => UnforcedLeray.B0412.realC (X q.1 q.2)) (t, y) =
      UnforcedLeray.B0412.realC (physLap (X t) y) := by
    unfold PhaseSpace.lapT physLap
    simp only [hlap1]
    exact (map_sum realCLI (fun j : Fin 3 => physPd2 (X t) j j y) Finset.univ).symm
  have hdyW : ∀ j : Fin 3,
      PhaseSpace.dy j (fun q : ℝ × Space => UnforcedLeray.B0412.realC (X q.1 q.2)) (t, y) =
        UnforcedLeray.B0412.realC (fderiv ℝ (X t) y (coordinateVector j)) := by
    intro j
    unfold PhaseSpace.dy
    rw [rcb_fderiv_realC _ _ hF, rcb_slice1 X t y _ hF]
  have hsum : ∀ f : Fin 3 → Space,
      ∑ j : Fin 3, UnforcedLeray.B0412.realC (f j) = UnforcedLeray.B0412.realC (∑ j : Fin 3, f j) :=
    fun f => (map_sum realCLI f Finset.univ).symm
  have hRad : PhaseSpace.radialT (fun q : ℝ × Space => UnforcedLeray.B0412.realC (X q.1 q.2))
      (t, y) = UnforcedLeray.B0412.realC (fderiv ℝ (X t) y y) := by
    unfold PhaseSpace.radialT
    simp only [hdyW]
    have h2 : fderiv ℝ (X t) y y = ∑ j : Fin 3, (y j) • fderiv ℝ (X t) y (coordinateVector j) := by
      calc fderiv ℝ (X t) y y
          = fderiv ℝ (X t) y (∑ j : Fin 3, (y j) • coordinateVector j) := by
            rw [rcb_sum_coord]
        _ = ∑ j : Fin 3, (y j) • fderiv ℝ (X t) y (coordinateVector j) := by
            rw [map_sum]
            simp [map_smul]
    rw [h2]
    have h3 : ∑ j : Fin 3, (y j) • UnforcedLeray.B0412.realC (fderiv ℝ (X t) y (coordinateVector j))
        = ∑ j : Fin 3, UnforcedLeray.B0412.realC ((y j) • fderiv ℝ (X t) y (coordinateVector j)) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      exact (rcb_smul _ _).symm
    rw [h3, hsum]
  have hAdv : UnforcedLeray.Cons.C03.Concrete.advT
      (fun q : ℝ × Space => UnforcedLeray.B0412.realC (X q.1 q.2))
      (fun q : ℝ × Space => UnforcedLeray.B0412.realC (X q.1 q.2)) (t, y) =
      UnforcedLeray.B0412.realC (fderiv ℝ (X t) y (X t y)) := by
    unfold UnforcedLeray.Cons.C03.Concrete.advT
    simp only [hdyW, UnforcedLeray.B0412.realC_apply]
    have h3 : ∑ k : Fin 3, ((X t y k : ℝ) : ℂ) • UnforcedLeray.B0412.realC
        (fderiv ℝ (X t) y (coordinateVector k)) =
        ∑ k : Fin 3, UnforcedLeray.B0412.realC ((X t y k) • fderiv ℝ (X t) y (coordinateVector k)) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      exact rcb_cs _ _
    rw [h3, hsum]
    congr 1
    calc ∑ k : Fin 3, (X t y k) • fderiv ℝ (X t) y (coordinateVector k)
        = fderiv ℝ (X t) y (∑ k : Fin 3, (X t y k) • coordinateVector k) := by
          rw [map_sum]
          simp [map_smul]
      _ = fderiv ℝ (X t) y (X t y) := by
          rw [rcb_sum_coord]
  have hG1 : ∀ j : Fin 3,
      PhaseSpace.dy j (fun q : ℝ × Space => ((Pr q.1 q.2 : ℝ) : ℂ)) (t, y) =
        (((fderiv ℝ (Pr t) y (coordinateVector j)) : ℝ) : ℂ) := by
    intro j
    unfold PhaseSpace.dy
    rw [rcb_fderiv_ofReal (fun q => Pr q.1 q.2) (t, y) hPr]
    congr 1
    exact (rcb_slice1R (fun q => Pr q.1 q.2) t y _ hPr).symm
  have hGrad : PhaseSpace.gradT (fun q : ℝ × Space => ((Pr q.1 q.2 : ℝ) : ℂ)) (t, y) =
      UnforcedLeray.B0412.realC (physGrad (Pr t) y) := by
    unfold PhaseSpace.gradT
    simp only [hG1]
    ext i
    simp [UnforcedLeray.B0412.realC_apply, physGrad, coordinateVector, Pi.single_apply,
      Finset.sum_ite_eq', Finset.mem_univ]
  have hdt : PhaseSpace.dτ (fun q : ℝ × Space => UnforcedLeray.B0412.realC (X q.1 q.2)) (t, y) =
      UnforcedLeray.B0412.realC (deriv (fun s => X s y) t) := by
    unfold PhaseSpace.dτ
    rw [rcb_fderiv_realC _ _ hF, rcb_dtau_eq X t y hF]
  simp only [UnforcedLeray.B0411.L0, UnforcedLeray.B0411.T0]
  rw [hdt, hRad, hLap, hGrad, hAdv]
  simp only [physDmu, rcb_add, rcb_sub, rcb_smul]
  module

end UnforcedLeray.Short.PartIIIb.Concrete
