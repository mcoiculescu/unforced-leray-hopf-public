import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Sub.IIIb_D2_3_2_8
import UnforcedLeray.Short.PartIIb.Tasks.RawResidualFamily.SmoothResidualWeakForm

/-!
# `IBPDiv`: `⟨Φ, div(a⊗b + b⊗a)⟩ = -stressPair` (source 4268-4270)

For a solenoidal-free phase test `Φ` (compact `y`-support), `realCf (physDivSym (U τ) (W τ))`
has `i`-th coordinate `∑ⱼ ∂ⱼ T_{ji}` with `T = symProd U W` symmetric.  Pointwise,
`∑ᵢ Φᵢ ∑ⱼ ∂ⱼT_{ji} = ∑ⱼ ∂ⱼ(∑ᵢ Φᵢ T_{ji}) - ∑ᵢⱼ T_{ij} ∂ⱼΦᵢ`; the `y_j`-derivative terms
integrate to zero by `srwf_slab_dy` (compact `y`-support), which leaves `-stressPair`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)
open UnforcedLeray.Short.IIb

/-- `∂_{y_i}` of a complexified real function, pointwise. -/
theorem id_dy_ofReal {G : ℝ × Space → ℝ} (hG : ContDiff ℝ ∞ G) (i : Fin 3) (x : ℝ × Space) :
    dy i (fun w : ℝ × Space => ((G w : ℝ) : ℂ)) x =
      ((fderiv ℝ (fun y => G (x.1, y)) x.2 (coordinateVector i) : ℝ) : ℂ) := by
  have hd : DifferentiableAt ℝ G x := (hG.differentiable (by simp)) x
  have h : HasFDerivAt (fun w : ℝ × Space => ((G w : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (fderiv ℝ G x)) x :=
    Complex.ofRealCLM.hasFDerivAt.comp x hd.hasFDerivAt
  have hs : fderiv ℝ (fun y => G (x.1, y)) x.2 =
      (fderiv ℝ G x).comp (ContinuousLinearMap.inr ℝ ℝ Space) :=
    UnforcedLeray.B0005.fderiv_slice_space hd
  simp only [dy]
  rw [h.fderiv, hs]
  simp [coordinateVector]

/-- `∂_j` of a finite sum of complex-valued differentiable functions. -/
theorem id_dy_finsetSum {ι : Type*} (s : Finset ι) (f : ι → ℝ × Space → ℂ)
    (hf : ∀ i ∈ s, Differentiable ℝ (f i)) (j : Fin 3) (x : ℝ × Space) :
    dy j (fun w => ∑ i ∈ s, f i w) x = ∑ i ∈ s, dy j (f i) x := by
  unfold dy
  rw [fderiv_fun_sum (fun i hi => hf i hi x), ContinuousLinearMap.sum_apply]

/-- The `j`-th complexified term `∑ᵢ Φᵢ · T_{ji}`. -/
def ibpDivK (U W : ℝ → Space → Space) (Φ : ℝ × Space → CVec3) (j : Fin 3) :
    ℝ × Space → ℂ :=
  fun w => ∑ i : Fin 3, Φ w i * ((symProd (U w.1 w.2) (W w.1 w.2) j i : ℝ) : ℂ)

/-- The stress integrand of `stressPair P (symProd U W) Φ`. -/
def ibpDivStress (U W : ℝ → Space → Space) (Φ : ℝ × Space → CVec3) : ℝ × Space → ℂ :=
  fun x => ∑ i : Fin 3, ∑ j : Fin 3,
    ((symProd (U x.1 x.2) (W x.1 x.2) i j : ℝ) : ℂ) * dy j Φ x i

theorem ibpDiv_proved : IBPDiv := by
  intro P U W hU hW Φ hΦ
  obtain ⟨R, hR⟩ := hΦ.bounded_support
  have hΦc : ContDiff ℝ ∞ Φ := hΦ.smooth
  have hΦd : Differentiable ℝ Φ := hΦc.differentiable (by simp)
  -- coordinates and the symmetric product
  have hUc : ∀ k : Fin 3, ContDiff ℝ ∞ (fun x : ℝ × Space => U x.1 x.2 k) := fun k =>
    (EuclideanSpace.proj k : Space →L[ℝ] ℝ).contDiff.comp hU
  have hWc : ∀ k : Fin 3, ContDiff ℝ ∞ (fun x : ℝ × Space => W x.1 x.2 k) := fun k =>
    (EuclideanSpace.proj k : Space →L[ℝ] ℝ).contDiff.comp hW
  have hMc : ∀ i j : Fin 3, ContDiff ℝ ∞
      (fun x : ℝ × Space => symProd (U x.1 x.2) (W x.1 x.2) i j) := fun i j =>
    ((hUc i).mul (hWc j)).add ((hWc i).mul (hUc j))
  have hMsym : ∀ (x : ℝ × Space) (i j : Fin 3),
      ((symProd (U x.1 x.2) (W x.1 x.2) j i : ℝ) : ℂ) =
        ((symProd (U x.1 x.2) (W x.1 x.2) i j : ℝ) : ℂ) := fun x i j => by
    unfold symProd; ring_nf
  have hMC : ∀ i j : Fin 3, ContDiff ℝ ∞
      (fun w : ℝ × Space => ((symProd (U w.1 w.2) (W w.1 w.2) i j : ℝ) : ℂ)) := fun i j =>
    Complex.ofRealCLM.contDiff.comp (hMc i j)
  -- the `j`-th terms are smooth with compact `y`-support
  have hKc : ∀ j, ContDiff ℝ ∞ (ibpDivK U W Φ j) := fun j => by
    unfold ibpDivK
    exact ContDiff.sum fun i _ => (srwf_coord_contDiff hΦc i).mul (hMC j i)
  have hK_bdd : ∀ j, ∀ τ y, R < ‖y‖ → ibpDivK U W Φ j (τ, y) = 0 := fun j τ y hy => by
    simp [ibpDivK, hR τ y hy]
  have hK_int : ∀ j, Integrable (fun z => dy j (ibpDivK U W Φ j) z) (srwfSlab P) ∧
      ∫ z, dy j (ibpDivK U W Φ j) z ∂(srwfSlab P) = 0 := fun j =>
    srwf_slab_dy (R := R) (hKc j) (hK_bdd j) j
  -- pointwise derivative of `K_j`
  have hdy : ∀ (j : Fin 3) (x : ℝ × Space), dy j (ibpDivK U W Φ j) x =
      ∑ i : Fin 3, (dy j Φ x i * ((symProd (U x.1 x.2) (W x.1 x.2) j i : ℝ) : ℂ) +
        Φ x i * ((fderiv ℝ (fun y => symProd (U x.1 y) (W x.1 y) j i) x.2
          (coordinateVector j) : ℝ) : ℂ)) := by
    intro j x
    unfold ibpDivK
    rw [id_dy_finsetSum Finset.univ (fun i w => Φ w i * ((symProd (U w.1 w.2) (W w.1 w.2) j i : ℝ) : ℂ))
      (fun i _ => ((srwf_coord_contDiff hΦc i).mul (hMC j i)).differentiable (by simp)) j x]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h3 := id_dy_ofReal (G := fun x : ℝ × Space => symProd (U x.1 x.2) (W x.1 x.2) j i)
      (hMc j i) j x
    rw [srwf_dy_mul ((srwf_coord_contDiff hΦc i).differentiable (by simp))
      ((hMC j i).differentiable (by simp)) j x, srwf_dy_coord hΦd i j x, h3]
    try rfl
  -- the stress integrand
  have hstress_c : Continuous (ibpDivStress U W Φ) := by
    unfold ibpDivStress
    refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
    exact (hMC i j).continuous.mul (srwf_coord_contDiff (UnforcedLeray.PhaseSpace.contDiff_dy hΦc j)
      i).continuous
  have hstress_bdd : ∀ τ y, R < ‖y‖ → ibpDivStress U W Φ (τ, y) = 0 := fun τ y hy => by
    have hz : ∀ j, dy j Φ (τ, y) = 0 := fun j => srwf_dy_bdd hR j τ y hy
    simp [ibpDivStress, hz]
  have hstress_int : Integrable (ibpDivStress U W Φ) (srwfSlab P) :=
    UnforcedLeray.B0005.integrable_slab (𝒯 := P) hstress_c (R := R) hstress_bdd
  -- the transposed-index identity for the stress integrand
  have hstress_eq : ∀ x : ℝ × Space,
      ibpDivStress U W Φ x = ∑ j : Fin 3, ∑ i : Fin 3,
        dy j Φ x i * ((symProd (U x.1 x.2) (W x.1 x.2) j i : ℝ) : ℂ) := by
    intro x
    unfold ibpDivStress
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    rw [hMsym x j i]
    ring
  -- pointwise identity
  have hpt : ∀ x : ℝ × Space,
      dotL (Φ x) (realCf (fun τ y => physDivSym (U τ) (W τ) y) x) =
        ∑ j : Fin 3, dy j (ibpDivK U W Φ j) x - ibpDivStress U W Φ x := by
    intro x
    have hc : ∀ i : Fin 3, realCf (fun τ y => physDivSym (U τ) (W τ) y) x i =
        ((∑ j : Fin 3, fderiv ℝ (fun y => symProd (U x.1 y) (W x.1 y) j i) x.2
          (coordinateVector j) : ℝ) : ℂ) := by
      intro i
      simp [realCf, B0412.realC_apply, physDivSym, symProd]
    rw [dotL_apply]
    simp only [hc, Complex.ofReal_sum]
    rw [Finset.sum_congr rfl fun j _ => hdy j x, hstress_eq x]
    simp only [Finset.mul_sum, Finset.sum_add_distrib]
    conv_lhs => rw [Finset.sum_comm]
    ring
  unfold pairF
  show phaseInt P (fun x => dotL (Φ x) (realCf (fun τ y => physDivSym (U τ) (W τ) y) x)) =
    -phaseInt P (fun x => ∑ i : Fin 3, ∑ j : Fin 3,
      ((symProd (U x.1 x.2) (W x.1 x.2) i j : ℝ) : ℂ) * dy j Φ x i)
  have hRHS : phaseInt P (fun x => ∑ i : Fin 3, ∑ j : Fin 3,
      ((symProd (U x.1 x.2) (W x.1 x.2) i j : ℝ) : ℂ) * dy j Φ x i) =
      P⁻¹ • ∫ z, ibpDivStress U W Φ z ∂(srwfSlab P) := srwf_phaseInt_eq hstress_int
  rw [show (fun x => dotL (Φ x) (realCf (fun τ y => physDivSym (U τ) (W τ) y) x)) =
      fun x => ∑ j : Fin 3, dy j (ibpDivK U W Φ j) x - ibpDivStress U W Φ x from funext hpt]
  have hsumI : Integrable (fun z => ∑ j : Fin 3, dy j (ibpDivK U W Φ j) z) (srwfSlab P) :=
    integrable_finsetSum _ fun j _ => (hK_int j).1
  have hI : Integrable (fun z => ∑ j : Fin 3, dy j (ibpDivK U W Φ j) z - ibpDivStress U W Φ z)
      (srwfSlab P) := hsumI.sub hstress_int
  rw [srwf_phaseInt_eq hI, integral_sub hsumI hstress_int,
    integral_finsetSum _ fun j _ => (hK_int j).1, Finset.sum_eq_zero fun j _ => (hK_int j).2,
    zero_sub, smul_neg, hRHS]

end UnforcedLeray.Short.PartIIIb.Concrete
