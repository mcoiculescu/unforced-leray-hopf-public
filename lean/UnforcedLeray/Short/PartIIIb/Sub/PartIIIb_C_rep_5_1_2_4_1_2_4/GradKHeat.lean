import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_2_4_1_2_4
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2.L2

/-!
# Heat equation for the contracted kernel gradient (`PartIII-b:C/rep/5/1/2/4/1/2/4`, `GradKHeat`)

Source `the November 2 reference manuscript` 3600-3610.  Componentwise,
`(gradKCon t x M)_i = ∑_{a,b} (∂_b K_{t,ia})(x) M_{ab}`, so `∂_t` of it is the sum of the partial heat
equations `KernelPartialHeat`, which is `physLap` of the same field.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Component of a finite sum of `Space`-vectors. -/
lemma sum_apply_space {ι : Type*} (s : Finset ι) (f : ι → Space) (i : Fin 3) :
    (∑ j ∈ s, f j) i = ∑ j ∈ s, f j i := by
  have := map_sum (EuclideanSpace.proj i : Space →L[ℝ] ℝ) f s
  simpa using this

/-- Component of a derivative: the `i`-th coordinate of `fderiv` of a `Space`-valued `C²` field is the
`fderiv` of its `i`-th coordinate. -/
lemma proj_fderiv_comm (F : Space → Space) (hF : ContDiff ℝ 2 F) (i : Fin 3) (v w x : Space) :
    (fderiv ℝ (fun y => fderiv ℝ F y v) x w) i
      = fderiv ℝ (fun y => fderiv ℝ (fun z => F z i) y v) x w := by
  set P : Space →L[ℝ] ℝ := EuclideanSpace.proj i with hP
  have hFd : ∀ y, DifferentiableAt ℝ F y := fun y => (hF.differentiable (by norm_num)) y
  have hcomp : ∀ y, fderiv ℝ (fun z => F z i) y = P.comp (fderiv ℝ F y) := fun y =>
    ((P.hasFDerivAt).comp y (hFd y).hasFDerivAt).fderiv
  have hfun : (fun y => fderiv ℝ (fun z => F z i) y v) = fun y => P (fderiv ℝ F y v) := by
    funext y
    rw [hcomp y]
    rfl
  have hG : Differentiable ℝ (fun y => fderiv ℝ F y v) := by
    have h1 : ContDiff ℝ 1 (fun y => fderiv ℝ F y) := hF.fderiv_right (m := 1) (by norm_num)
    exact ((h1.clm_apply contDiff_const).differentiable (by norm_num))
  have h2 : HasFDerivAt (fun y => P (fderiv ℝ F y v))
      (P.comp (fderiv ℝ (fun y => fderiv ℝ F y v) x)) x :=
    (P.hasFDerivAt).comp x (hG x).hasFDerivAt
  rw [hfun, h2.fderiv]
  rfl

/-- Derivative of a double sum of scalar fields times constants. -/
lemma fderiv_double_sum (φ : Fin 3 → Fin 3 → Space → ℝ) (c : Fin 3 → Fin 3 → ℝ)
    (hφ : ∀ a b, Differentiable ℝ (φ a b)) (y v : Space) :
    fderiv ℝ (fun y => ∑ a, ∑ b, φ a b y * c a b) y v
      = ∑ a, ∑ b, fderiv ℝ (φ a b) y v * c a b := by
  have h : HasFDerivAt (fun y => ∑ a, ∑ b, φ a b y * c a b)
      (∑ a, ∑ b, c a b • fderiv ℝ (φ a b) y) y := by
    refine HasFDerivAt.fun_sum (fun a _ => HasFDerivAt.fun_sum (fun b _ => ?_))
    exact (hφ a b y).hasFDerivAt.mul_const (c a b)
  rw [h.fderiv]
  simp only [ContinuousLinearMap.sum_apply, smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => mul_comm _ _

/-- **Heat equation for the contracted kernel gradient** (source 3600-3610): from the partial heat
equations `KernelPartialHeat`, `∂_t (∇K_t(x) : M) = Δ_x (∇K_t : M)(x)`. -/
theorem gradKHeat_of_partial (h : KernelPartialHeat) : GradKHeat := by
  intro t ht x M
  have hK : ∀ i j : Fin 3, ContDiff ℝ 3 (fun y => IIIa.heatLerayK t i j y) :=
    fun i j => heatLerayKSmooth t ht i j
  -- the partial derivatives `y ↦ ∂_b K_{t,ia}(y)` are `C²`
  have hgd : ∀ i a b : Fin 3, ContDiff ℝ 2
      (fun y => fderiv ℝ (fun z => IIIa.heatLerayK t i a z) y (coordinateVector b)) :=
    fun i a b => ((hK i a).fderiv_right (m := 2) (by norm_num)).clm_apply contDiff_const
  have hgd1 : ∀ i a b : Fin 3, Differentiable ℝ
      (fun y => fderiv ℝ (fun z => IIIa.heatLerayK t i a z) y (coordinateVector b)) :=
    fun i a b => (hgd i a b).differentiable (by norm_num)
  have hgg : ∀ i a b j : Fin 3, Differentiable ℝ (fun y =>
      fderiv ℝ (fun y' => fderiv ℝ (fun z => IIIa.heatLerayK t i a z) y' (coordinateVector b))
        y (coordinateVector j)) := by
    intro i a b j
    have h1 : ContDiff ℝ 1 (fun y =>
        fderiv ℝ (fun y' => fderiv ℝ (fun z => IIIa.heatLerayK t i a z) y' (coordinateVector b)) y) :=
      (hgd i a b).fderiv_right (m := 1) (by norm_num)
    exact (h1.clm_apply contDiff_const).differentiable (by norm_num)
  -- the field `y ↦ ∇K_t(y) : M` is `C²`
  have hF : ContDiff ℝ 2 (fun y => gradKCon t y M) := by
    unfold gradKCon
    refine PiLp.contDiff_toLp.comp ?_
    refine contDiff_pi.2 fun i => ?_
    refine ContDiff.sum fun a _ => ContDiff.sum fun b _ => ?_
    exact (hgd i a b).mul contDiff_const
  -- time derivative, componentwise
  have hT : HasDerivAt (fun t' => gradKCon t' x M)
      (WithLp.toLp 2 (fun i => ∑ a, ∑ b,
        (∑ l, fderiv ℝ (fun y => fderiv ℝ (fun y' =>
          fderiv ℝ (fun z => IIIa.heatLerayK t i a z) y' (coordinateVector b)) y
            (coordinateVector l)) x (coordinateVector l)) * M a b)) t := by
    have hc : HasDerivAt (fun t' : ℝ => fun i => ∑ a, ∑ b,
        fderiv ℝ (fun z => IIIa.heatLerayK t' i a z) x (coordinateVector b) * M a b)
        (fun i => ∑ a, ∑ b,
          (∑ l, fderiv ℝ (fun y => fderiv ℝ (fun y' =>
            fderiv ℝ (fun z => IIIa.heatLerayK t i a z) y' (coordinateVector b)) y
              (coordinateVector l)) x (coordinateVector l)) * M a b) t := by
      rw [hasDerivAt_pi]
      intro i
      refine HasDerivAt.fun_sum (fun a _ => HasDerivAt.fun_sum (fun b _ => ?_))
      exact (h t ht i a b x).mul_const (M a b)
    exact HasFDerivAt.comp_hasDerivAt t
      (PiLp.hasFDerivAt_toLp (2 : ENNReal) (fun i : Fin 3 => ∑ a, ∑ b,
        fderiv ℝ (fun z => IIIa.heatLerayK t i a z) x (coordinateVector b) * M a b)) hc
  -- the Laplacian of the field, componentwise
  have hP : physLap (fun y => gradKCon t y M) x
      = WithLp.toLp 2 (fun i => ∑ a, ∑ b,
        (∑ l, fderiv ℝ (fun y => fderiv ℝ (fun y' =>
          fderiv ℝ (fun z => IIIa.heatLerayK t i a z) y' (coordinateVector b)) y
            (coordinateVector l)) x (coordinateVector l)) * M a b) := by
    ext i
    have hsum : (physLap (fun y => gradKCon t y M) x) i
        = ∑ j : Fin 3, fderiv ℝ (fun y => fderiv ℝ (fun z => gradKCon t z M) y (coordinateVector j))
            x (coordinateVector j) i := by
      unfold physLap physPd2 physPd
      exact sum_apply_space _ _ i
    rw [hsum]
    simp only [PiLp.toLp_apply]
    have hj : ∀ j : Fin 3,
        fderiv ℝ (fun y => fderiv ℝ (fun z => gradKCon t z M) y (coordinateVector j)) x
          (coordinateVector j) i
        = ∑ a, ∑ b, fderiv ℝ (fun y => fderiv ℝ (fun y' =>
            fderiv ℝ (fun z => IIIa.heatLerayK t i a z) y' (coordinateVector b)) y
              (coordinateVector j)) x (coordinateVector j) * M a b := by
      intro j
      rw [proj_fderiv_comm _ hF i _ _ _]
      beta_reduce
      have e1 : ∀ y : Space, fderiv ℝ (fun z => gradKCon t z M i) y (coordinateVector j)
          = ∑ a, ∑ b, fderiv ℝ (fun y' => fderiv ℝ (fun z => IIIa.heatLerayK t i a z) y'
              (coordinateVector b)) y (coordinateVector j) * M a b := fun y =>
        fderiv_double_sum (fun a b y' => fderiv ℝ (fun z => IIIa.heatLerayK t i a z) y'
          (coordinateVector b)) M (fun a b => hgd1 i a b) y (coordinateVector j)
      have e2 : (fun y => fderiv ℝ (fun z => gradKCon t z M i) y (coordinateVector j))
          = fun y => ∑ a, ∑ b, fderiv ℝ (fun y' => fderiv ℝ (fun z => IIIa.heatLerayK t i a z) y'
              (coordinateVector b)) y (coordinateVector j) * M a b := funext e1
      rw [e2]
      exact fderiv_double_sum (fun a b y => fderiv ℝ (fun y' =>
          fderiv ℝ (fun z => IIIa.heatLerayK t i a z) y' (coordinateVector b)) y
            (coordinateVector j)) M (fun a b => hgg i a b j) x (coordinateVector j)
    refine (Finset.sum_congr rfl (fun j _ => hj j)).trans ?_
    simp only [Finset.sum_mul]
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
  rw [hP]
  exact hT
