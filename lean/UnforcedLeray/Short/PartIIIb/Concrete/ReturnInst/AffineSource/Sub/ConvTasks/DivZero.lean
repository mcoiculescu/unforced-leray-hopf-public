import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.Sub.ConvGeoSub
import UnforcedLeray.Short.PartIIIb.Concrete.HpJGradProof
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.PsipADiff
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_2.HpADiffX
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_2.PsipAXSecond

/-!
# `convDivZero` (`PartIII-b:C/asrc/ra/9/2/2/8`), helper lemmas

Source 4993 (`h^p_A = J∇ψ^p_A`), 5022 (planar train solenoidal).

* Part 1, `cDiv (trPl p) s x = 0` for `s > 0`: proved below from `IsTrain.solenoidal`.
* Part 2, `cDiv (hpA ν χf A) s x = 0`: `HpIsJGrad` (`hpIsJGrad_proof`) gives
  `hpA = J∇ψ^p_A` pointwise for `s > 0`, and the divergence of `J∇ψ` vanishes by symmetry of the
  second derivative (`second_derivative_symmetric_of_eventually`).  The symmetry needs the
  Fréchet differentiability in `x` of `y ↦ fderiv (psipA s) y` at the point, which is not yet
  proved anywhere in the library (see the conditional lemma `cDiv_hpA_zero_of`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest Params)

/-- The partial derivative in `q` of a planar function is its `fderiv` along `e_0`. -/
theorem fderiv_ei0_eq (f : ℝ × ℝ → ℝ) (x : ℝ × ℝ) (hf : DifferentiableAt ℝ f x) :
    fderiv ℝ f x (ei 0) = deriv (fun q : ℝ => f (q, x.2)) x.1 := by
  have hg : HasDerivAt (fun q : ℝ => (q, x.2)) (ei 0) x.1 := by
    have := (hasDerivAt_id x.1).prodMk (hasDerivAt_const x.1 x.2)
    simpa [ei] using this
  have h := hf.hasFDerivAt.comp_hasDerivAt x.1 hg
  exact h.deriv.symm

/-- The partial derivative in `η` of a planar function is its `fderiv` along `e_1`. -/
theorem fderiv_ei1_eq (f : ℝ × ℝ → ℝ) (x : ℝ × ℝ) (hf : DifferentiableAt ℝ f x) :
    fderiv ℝ f x (ei 1) = deriv (fun η : ℝ => f (x.1, η)) x.2 := by
  have hg : HasDerivAt (fun η : ℝ => (x.1, η)) (ei 1) x.2 := by
    have := (hasDerivAt_const x.2 x.1).prodMk (hasDerivAt_id x.2)
    simpa [ei] using this
  have h := hf.hasFDerivAt.comp_hasDerivAt x.2 hg
  exact h.deriv.symm

/-- The train velocity is differentiable in `x` at `s > 0` (`smooth_v` on the open set `s > 0`). -/
theorem trainV_diffAt {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (s : ℝ) (hs : 0 < s)
    (x : ℝ × ℝ) : DifferentiableAt ℝ (tr.v s) x := by
  have hopen : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := isOpen_Ioi.prod isOpen_univ
  have hmem : (Ici (0 : ℝ)) ×ˢ (univ : Set (ℝ × ℝ)) ∈ 𝓝 (s, x) :=
    Filter.mem_of_superset (hopen.mem_nhds (show (s, x) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)) from
      ⟨hs, mem_univ _⟩))
      (prod_mono Ioi_subset_Ici_self (subset_refl _))
  have hc := tr.isTrain.smooth_v.contDiffAt hmem
  have h2 := hc.comp (x := x) (contDiffAt_const.prodMk contDiffAt_id)
  exact h2.differentiableAt (by simp)

/-- Part 1: the planar train has zero planar divergence for `s > 0`. -/
theorem cDiv_trPl_zero (p : Params) (s : ℝ) (hs : 0 < s) (x : ℝ × ℝ) :
    cDiv (trPl p) s x = 0 := by
  have hu := trainV_diffAt p.train s hs x
  have h0 : DifferentiableAt ℝ (fun y => p.train.v s y 0) x :=
    ((EuclideanSpace.proj (0 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).differentiableAt).comp x hu
  have h1 : DifferentiableAt ℝ (fun y => p.train.v s y 1) x :=
    ((EuclideanSpace.proj (1 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).differentiableAt).comp x hu
  have hL : fderiv ℝ (trPl p s) x =
      (fderiv ℝ (fun y => p.train.v s y 0) x).prod (fderiv ℝ (fun y => p.train.v s y 1) x) :=
    (h0.hasFDerivAt.prodMk h1.hasFDerivAt).fderiv
  have hsol := p.train.isTrain.solenoidal s hs.le x
  unfold cDiv
  rw [hL]
  simp only [ContinuousLinearMap.prod_apply]
  rw [fderiv_ei0_eq _ x h0, fderiv_ei1_eq _ x h1]
  unfold UnforcedLeray.Cyl.divergence UnforcedLeray.Cyl.partialQ UnforcedLeray.Cyl.partialEta at hsol
  exact hsol

/-- The derivative of a pair of scalar functions, componentwise. -/
theorem pair_fderiv_apply (a b : ℝ × ℝ → ℝ) (x w : ℝ × ℝ) (ha : DifferentiableAt ℝ a x)
    (hb : DifferentiableAt ℝ b x) :
    fderiv ℝ (fun y => (a y, b y)) x w = (fderiv ℝ a x w, fderiv ℝ b x w) := by
  rw [(ha.hasFDerivAt.prodMk hb.hasFDerivAt).fderiv]
  rfl

/-- Part 2, conditional: the divergence of `hpA = J∇ψ^p_A` vanishes at `s > 0` once the
gradient of `ψ^p_A(s, ·)` is differentiable at the point (symmetry of the second derivative). -/
theorem cDiv_hpA_zero_of (ν : ℝ) (hν : 0 < ν) (χf : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (hs : 0 < s)
    (x : ℝ × ℝ) (hd : ∀ y, DifferentiableAt ℝ (psipA ν χf A s) y)
    (hC2 : DifferentiableAt ℝ (fun y => fderiv ℝ (psipA ν χf A s) y) x) :
    cDiv (hpA ν χf A) s x = 0 := by
  have hJ : hpA ν χf A s = fun y =>
      (-(fderiv ℝ (psipA ν χf A s) y (ei 1)), fderiv ℝ (psipA ν χf A s) y (ei 0)) := by
    funext y
    exact (hpIsJGrad_proof ν hν χf A).2 s hs y
  have hG0 : DifferentiableAt ℝ (fun y => fderiv ℝ (psipA ν χf A s) y (ei 0)) x :=
    hC2.clm_apply (differentiableAt_const _)
  have hG1 : DifferentiableAt ℝ (fun y => fderiv ℝ (psipA ν χf A s) y (ei 1)) x :=
    hC2.clm_apply (differentiableAt_const _)
  have hD : ∀ (b w : ℝ × ℝ), fderiv ℝ (fun y => fderiv ℝ (psipA ν χf A s) y b) x w =
      fderiv ℝ (fun y => fderiv ℝ (psipA ν χf A s) y) x w b := by
    intro b w
    rw [fderiv_clm_apply hC2 (differentiableAt_const b)]
    simp
  have hsym := second_derivative_symmetric_of_eventually
    (f := psipA ν χf A s) (f' := fun y => fderiv ℝ (psipA ν χf A s) y)
    (f'' := fderiv ℝ (fun y => fderiv ℝ (psipA ν χf A s) y) x)
    (Filter.Eventually.of_forall (fun y => (hd y).hasFDerivAt)) hC2.hasFDerivAt (ei 0) (ei 1)
  unfold cDiv
  rw [hJ]
  have hna : DifferentiableAt ℝ (fun y => -(fderiv ℝ (psipA ν χf A s) y (ei 1))) x := hG1.neg
  rw [pair_fderiv_apply _ _ x (ei 0) hna hG0, pair_fderiv_apply _ _ x (ei 1) hna hG0]
  rw [fderiv_fun_neg, ContinuousLinearMap.neg_apply, hD (ei 1) (ei 0), hD (ei 0) (ei 1), hsym]
  ring

/-- Missing analytic leaf (not proved anywhere in the library): the gradient of `ψ^p_A(s, ·)` is
differentiable in `x` at `s > 0` (`C²` in `x`; source 4973-4980, 4991). -/
def PsipAC2X (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  ∀ (ν : ℝ), 0 < ν → ∀ (A : ℝ → Mat3), IsAffElem as A → ∀ s : ℝ, 0 < s → ∀ x : ℝ × ℝ,
    DifferentiableAt ℝ (fun y => fderiv ℝ (psipA ν χf A s) y) x

/-- `ConvDivZero` from the missing leaf `PsipAC2X` (the reduction; not the unconditional target). -/
theorem convDivZero_of (as : ℝ) (χf : ℝ → ℝ) (hC2 : PsipAC2X as χf) : ConvDivZero as χf := by
  intro hχ p A hA s hs x
  refine ⟨cDiv_trPl_zero p s hs x, ?_⟩
  exact cDiv_hpA_zero_of p.ν p.ν_pos χf A s hs x
    (fun y => (psipADiff as χf hχ p.ν p.ν_pos A hA s hs y).1) (hC2 p.ν p.ν_pos A hA s hs x)

/-- The leaf `PsipAC2X`: `∂_q ψ` is a component of `hpA`, `∂_η ψ` is `PsipAXSecond`. -/
theorem psipA_C2X (as : ℝ) (χf : ℝ → ℝ) (hχ : IsSourceCutoffC χf) : PsipAC2X as χf := by
  intro ν hν A hA s hs x
  have h1 := hpADiffX as χf hχ ν hν A hA s hs x
  have h2 := psipAXSecond as χf hχ ν hν A hA s hs x
  have hJ : hpA ν χf A s = fun y =>
      (-(fderiv ℝ (psipA ν χf A s) y (ei 1)), fderiv ℝ (psipA ν χf A s) y (ei 0)) := by
    funext y
    exact (hpIsJGrad_proof ν hν χf A).2 s hs y
  have h0 : DifferentiableAt ℝ (fun y => fderiv ℝ (psipA ν χf A s) y (ei 0)) x := by
    rw [hJ] at h1
    exact (differentiableAt_snd).comp x h1
  have hdec : (fun y => fderiv ℝ (psipA ν χf A s) y) = fun y =>
      (fderiv ℝ (psipA ν χf A s) y (ei 0)) • (ContinuousLinearMap.fst ℝ ℝ ℝ) +
      (fderiv ℝ (psipA ν χf A s) y (ei 1)) • (ContinuousLinearMap.snd ℝ ℝ ℝ) := by
    funext y
    ext v <;> simp [ei]
  rw [hdec]
  exact (h0.smul_const _).add (h2.smul_const _)

theorem convDivZero (as : ℝ) (χf : ℝ → ℝ) : ConvDivZero as χf := by
  intro hχ
  exact convDivZero_of as χf (psipA_C2X as χf hχ) hχ

end UnforcedLeray.Short.PartIIIb.Concrete
