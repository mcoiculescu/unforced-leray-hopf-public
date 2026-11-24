import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_2_3.K1
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2.Int
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2.L2

/-!
# `sepW` equivariance (`PartIII-b:IIIb-D2/3/1/2/3/2`)

Source of record: `the November 2 reference manuscript`
lines 4171-4178 (rotation of `X₀`) and 3611-3621 (`sep:resolvent`).

Route. (1) The chain rule through `actM M`, applied to the differentiated kernel identity
`kernelEquivariance`, gives `∂_k K_{ij}(Mw) = ∑_a M_{ia} (M D^a Mᵀ)_{jk}` with
`D^a_{bk} = ∂_k K_{ab}(w)`.  (2) The contraction with `T(Mz) = M T(z) Mᵀ` collapses by
`∑_{jk} A_{jk} B_{jk} = tr(Aᵀ B)` and `Mᵀ M = 1`, giving the pointwise identity
`sepPhi_i(l, Mz; My) = ∑_a M_{ia} sepPhi_a(l, z; y)` wherever `y - l z ≠ 0`.  (3) The map
`(l,z) ↦ (l, Mz)` preserves `sepRho`, and `y - l z = 0` is `sepRho`-null, so the componentwise
integrals at `My` are the mixed integrals of `sepW` at `y`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- `actM` is additive in the point and linear in the scalar. -/
lemma actM_sub_smul (M : Matrix (Fin 3) (Fin 3) ℝ) (y z : Space) (l : ℝ) :
    actM M (y - l • z) = actM M y - l • actM M z := by
  ext i
  simp [actM, Matrix.mulVec_sub, Matrix.mulVec_smul]

/-- The linear equivalence of an orthogonal `M`, as a `LinearIsometryEquiv`. -/
def lieOf {M : Matrix (Fin 3) (Fin 3) ℝ} (hM : M * M.transpose = 1) : Space ≃ₗᵢ[ℝ] Space where
  toLinearEquiv := (cleOf hM).toLinearEquiv
  norm_map' x := norm_actM hM x

/-- Chain rule for `f ∘ actM M`, with no regularity of `f`. -/
lemma fderiv_comp_actM {M : Matrix (Fin 3) (Fin 3) ℝ} (hM : M * M.transpose = 1)
    (f : Space → ℝ) (w v : Space) :
    fderiv ℝ (fun x => f (actM M x)) w v = fderiv ℝ f (actM M w) (actM M v) := by
  have h := (cleOf hM).comp_right_fderiv (f := f) (x := w)
  rw [show (fun x => f (actM M x)) = f ∘ (cleOf hM) from rfl, h]
  rfl

/-- Chain rule for the kernel: `∂_v K_{ij}(Mw; Mv) = ∑_{ab} M_{ia} M_{jb} ∂_v K_{ab}(w)`. -/
lemma chain_K {M : Matrix (Fin 3) (Fin 3) ℝ} (hM : M * M.transpose = 1) (t : ℝ) (i j : Fin 3)
    (w v : Space)
    (hd : ∀ a b : Fin 3, DifferentiableAt ℝ (fun x => IIIa.heatLerayK t a b x) w) :
    fderiv ℝ (fun x => IIIa.heatLerayK t i j x) (actM M w) (actM M v) =
      ∑ a : Fin 3, ∑ b : Fin 3,
        M i a * M j b * fderiv ℝ (fun x => IIIa.heatLerayK t a b x) w v := by
  have h1 : fderiv ℝ (fun x => IIIa.heatLerayK t i j (actM M x)) w v =
      fderiv ℝ (fun x => IIIa.heatLerayK t i j x) (actM M w) (actM M v) :=
    fderiv_comp_actM hM (fun x => IIIa.heatLerayK t i j x) w v
  have hfun : (fun x => IIIa.heatLerayK t i j (actM M x)) =
      fun x => ∑ a : Fin 3, ∑ b : Fin 3, M i a * M j b * IIIa.heatLerayK t a b x := by
    funext x
    exact kernelEquivariance M hM t i j x
  have hS : HasFDerivAt
      (fun x => ∑ a : Fin 3, ∑ b : Fin 3, M i a * M j b * IIIa.heatLerayK t a b x)
      (∑ a : Fin 3, ∑ b : Fin 3,
        (M i a * M j b) • fderiv ℝ (fun x => IIIa.heatLerayK t a b x) w) w := by
    apply HasFDerivAt.fun_sum
    intro a _
    apply HasFDerivAt.fun_sum
    intro b _
    exact (hd a b).hasFDerivAt.const_mul (M i a * M j b)
  rw [← h1, hfun, hS.fderiv]
  simp [smul_eq_mul]

/-- The directional derivative along a standard basis vector, expressed through `Mᵀ`. -/
lemma dK_eq {M : Matrix (Fin 3) (Fin 3) ℝ} (hM : M * M.transpose = 1) (t : ℝ) (i j k : Fin 3)
    (w : Space)
    (hd : ∀ a b : Fin 3, DifferentiableAt ℝ (fun x => IIIa.heatLerayK t a b x) w) :
    fderiv ℝ (fun x => IIIa.heatLerayK t i j x) (actM M w) (coordinateVector k) =
      ∑ a : Fin 3, ∑ b : Fin 3, M i a * M j b *
        ∑ k' : Fin 3, M k k' * fderiv ℝ (fun x => IIIa.heatLerayK t a b x) w (coordinateVector k') := by
  have h := chain_K hM t i j w (actM M.transpose (coordinateVector k)) hd
  rw [actM_actM' hM, actM_transpose_coord] at h
  simp only [map_sum, map_smul, smul_eq_mul] at h
  exact h

/-- The matrix of first `x`-derivatives of `K_{a·}` at `w`: entry `(b, k)` is `∂_k K_{ab}(w)`. -/
def Dmat (t : ℝ) (w : Space) (a : Fin 3) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun b k => fderiv ℝ (fun x => IIIa.heatLerayK t a b x) w (coordinateVector k)

lemma dK_matrix {M : Matrix (Fin 3) (Fin 3) ℝ} (hM : M * M.transpose = 1) (t : ℝ) (i j k : Fin 3)
    (w : Space)
    (hd : ∀ a b : Fin 3, DifferentiableAt ℝ (fun x => IIIa.heatLerayK t a b x) w) :
    fderiv ℝ (fun x => IIIa.heatLerayK t i j x) (actM M w) (coordinateVector k) =
      ∑ a : Fin 3, M i a * (M * Dmat t w a * M.transpose) j k := by
  rw [dK_eq hM t i j k w hd]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Dmat, Matrix.of_apply, Fin.sum_univ_three]
  ring

lemma sum_eq_trace (A B : Matrix (Fin 3) (Fin 3) ℝ) :
    ∑ j : Fin 3, ∑ k : Fin 3, A j k * B j k = Matrix.trace (A.transpose * B) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
  exact Finset.sum_comm

/-- Orthogonal invariance of the contraction `∑_{jk} A_{jk} B_{jk}` under `A ↦ M A Mᵀ`. -/
lemma contract_trace {M D T : Matrix (Fin 3) (Fin 3) ℝ} (hMt : M.transpose * M = 1) :
    ∑ j : Fin 3, ∑ k : Fin 3, (M * D * M.transpose) j k * (M * T * M.transpose) j k =
      ∑ j : Fin 3, ∑ k : Fin 3, D j k * T j k := by
  rw [sum_eq_trace, sum_eq_trace]
  have e : (M * D * M.transpose).transpose * (M * T * M.transpose) =
      M * (D.transpose * T) * M.transpose := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc M.transpose M, hMt, Matrix.one_mul]
  rw [e, Matrix.trace_mul_comm (M * (D.transpose * T)) M.transpose,
    ← Matrix.mul_assoc M.transpose M, hMt, Matrix.one_mul]

/-- The contraction identity at a point `w` where the kernel is differentiable. -/
lemma contr_identity {M : Matrix (Fin 3) (Fin 3) ℝ} (hM : M * M.transpose = 1) (t : ℝ) (w : Space)
    (hd : ∀ a b : Fin 3, DifferentiableAt ℝ (fun x => IIIa.heatLerayK t a b x) w)
    (T : Matrix (Fin 3) (Fin 3) ℝ) (i : Fin 3) :
    ∑ j : Fin 3, ∑ k : Fin 3,
        fderiv ℝ (fun x => IIIa.heatLerayK t i j x) (actM M w) (coordinateVector k) *
          (M * T * M.transpose) j k =
      ∑ a : Fin 3, M i a * ∑ j : Fin 3, ∑ k : Fin 3,
        fderiv ℝ (fun x => IIIa.heatLerayK t a j x) w (coordinateVector k) * T j k := by
  have hMt : M.transpose * M = 1 := mul_transpose_comm hM
  have h1 : ∀ j k : Fin 3,
      fderiv ℝ (fun x => IIIa.heatLerayK t i j x) (actM M w) (coordinateVector k) *
          (M * T * M.transpose) j k =
        ∑ a : Fin 3, M i a * ((M * Dmat t w a * M.transpose) j k * (M * T * M.transpose) j k) := by
    intro j k
    rw [dK_matrix hM t i j k w hd, Finset.sum_mul]
    exact Finset.sum_congr rfl fun a _ => by ring
  calc _ = ∑ j : Fin 3, ∑ k : Fin 3, ∑ a : Fin 3,
        M i a * ((M * Dmat t w a * M.transpose) j k * (M * T * M.transpose) j k) :=
        Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => h1 j k
    _ = ∑ j : Fin 3, ∑ a : Fin 3, ∑ k : Fin 3,
        M i a * ((M * Dmat t w a * M.transpose) j k * (M * T * M.transpose) j k) :=
        Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = ∑ a : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
        M i a * ((M * Dmat t w a * M.transpose) j k * (M * T * M.transpose) j k) :=
        Finset.sum_comm
    _ = ∑ a : Fin 3, M i a * ∑ j : Fin 3, ∑ k : Fin 3,
        (M * Dmat t w a * M.transpose) j k * (M * T * M.transpose) j k := by
        refine Finset.sum_congr rfl fun a _ => ?_
        simp only [Finset.mul_sum]
    _ = _ := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [contract_trace hMt]
        rfl

/-- Differentiability of the heat-Leray kernel at a point off the origin, for every real `t`. -/
lemma diffAt_heatLerayK (t : ℝ) (w : Space) (hw : w ≠ 0) (a b : Fin 3) :
    DifferentiableAt ℝ (fun x => IIIa.heatLerayK t a b x) w := by
  rcases lt_or_ge 0 t with ht | ht
  · exact ((heatLerayKSmooth t ht a b).differentiable (by norm_num)) w
  · set g : Space → ℝ := fun y => (4 * Real.pi * ‖y‖)⁻¹ with hg_def
    have hEqN : ∀ z : Space, z ≠ 0 → IIIa.heatTail t =ᶠ[𝓝 z] g := fun z hz =>
      Filter.eventually_of_mem (isOpen_ne.mem_nhds hz) (fun u hu => heatTail_nonpos_eq ht hu)
    have hpart : ∀ y : Space, y ≠ 0 → IIIa.part2 (IIIa.heatTail t) a b y = IIIa.part2 g a b y := by
      intro y hy
      unfold IIIa.part2
      have hfun : (fun z => fderiv ℝ (IIIa.heatTail t) z (coordinateVector b)) =ᶠ[𝓝 y]
          (fun z => fderiv ℝ g z (coordinateVector b)) := by
        filter_upwards [isOpen_ne.mem_nhds hy] with z hz
        rw [(hEqN z hz).fderiv_eq]
      rw [hfun.fderiv_eq]
    have hKeq : (fun x => IIIa.heatLerayK t a b x) =ᶠ[𝓝 w] IIIa.part2 g a b := by
      filter_upwards [isOpen_ne.mem_nhds hw] with y hy
      simp only [IIIa.heatLerayK, heatG_of_nonpos ht y, hpart y hy]
      simp
    have hg : ContDiffAt ℝ 3 g w := by
      have hn : ContDiffAt ℝ 3 (fun z : Space => ‖z‖) w := contDiffAt_norm ℝ hw
      have hne : (4 * Real.pi * ‖w‖) ≠ 0 := by
        have := norm_pos_iff.2 hw
        positivity
      exact (contDiffAt_const.mul hn).inv hne
    have h1 : ContDiffAt ℝ 2 (fderiv ℝ g) w := hg.fderiv_right (m := 2) (by norm_num)
    have h2 : ContDiffAt ℝ 2 (fun y => fderiv ℝ g y (coordinateVector b)) w :=
      h1.clm_apply contDiffAt_const
    have h3 : ContDiffAt ℝ 1 (fderiv ℝ (fun y => fderiv ℝ g y (coordinateVector b))) w :=
      h2.fderiv_right (m := 1) (by norm_num)
    have h4 : DifferentiableAt ℝ (IIIa.part2 g a b) w := by
      unfold IIIa.part2
      exact (h3.differentiableAt (by norm_num)).clm_apply (differentiableAt_const _)
    exact h4.congr_of_eventuallyEq hKeq

/-- The pointwise identity of the integrand: `Φ_i(l, Mz; My) = ∑_a M_{ia} Φ_a(l, z; y)`. -/
lemma sepPhi_equiv {M : Matrix (Fin 3) (Fin 3) ℝ} (hM : M * M.transpose = 1)
    (ν : ℝ) (μ : ℂ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ)
    (hT : ∀ τ z, T τ (actM M z) = M * T τ z * M.transpose) (τ : ℝ) (i : Fin 3)
    (l : ℝ) (z y : Space) (hw : y - l • z ≠ 0) :
    sepPhi ν μ T τ i (l, actM M z) (actM M y) =
      ∑ a : Fin 3, ((M i a : ℝ) : ℂ) * sepPhi ν μ T τ a (l, z) y := by
  have hd : ∀ a b : Fin 3,
      DifferentiableAt ℝ (fun x => IIIa.heatLerayK (ν * (1 - l ^ 2)) a b x) (y - l • z) :=
    fun a b => diffAt_heatLerayK (ν * (1 - l ^ 2)) (y - l • z) hw a b
  have R := contr_identity hM (ν * (1 - l ^ 2)) (y - l • z) hd (T (τ + 2 * Real.log l) z) i
  have Rc := congrArg (fun r : ℝ => (r : ℂ)) R
  push_cast at Rc
  unfold sepPhi
  dsimp only
  rw [← actM_sub_smul M y z l]
  simp only [hT]
  rw [Rc, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

/-- The exceptional set `{y = l z}` is `sepRho`-null. -/
lemma ae_ne_zero_sepRho (y : Space) : ∀ᵐ p ∂sepRho, y - p.1 • p.2 ≠ 0 := by
  have hSm : MeasurableSet {p : ℝ × Space | y - p.1 • p.2 = 0} :=
    (isClosed_eq (by fun_prop) continuous_const).measurableSet
  have hnull : sepRho {p : ℝ × Space | y - p.1 • p.2 = 0} = 0 := by
    unfold sepRho
    rw [Measure.measure_prod_null hSm]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with l hl
    simp only [Pi.zero_apply]
    refine Set.Subsingleton.measure_zero ?_ volume
    intro a ha b hb
    have ha' : y - l • a = 0 := ha
    have hb' : y - l • b = 0 := hb
    have hl0 : l ≠ 0 := ne_of_gt hl.1
    have h : l • a = l • b := by
      rw [sub_eq_zero] at ha' hb'
      exact ha'.symm.trans hb'
    exact smul_right_injective Space hl0 h
  exact (measure_eq_zero_iff_ae_notMem.mp hnull).mono fun p hp h => hp h

/-- The substitution `(l, z) ↦ (l, Mz)` preserves `sepRho`. -/
lemma mp_phi {M : Matrix (Fin 3) (Fin 3) ℝ} (hM : M * M.transpose = 1) :
    MeasurePreserving (fun p : ℝ × Space => (p.1, actM M p.2)) sepRho sepRho := by
  unfold sepRho
  exact (MeasurePreserving.id (volume.restrict (Ioo (0 : ℝ) 1))).prod (lieOf hM).measurePreserving

/-- The substitution `(l, z) ↦ (l, Mz)` is a measurable embedding. -/
lemma me_phi {M : Matrix (Fin 3) (Fin 3) ℝ} (hM : M * M.transpose = 1) :
    MeasurableEmbedding (fun p : ℝ × Space => (p.1, actM M p.2)) :=
  (Homeomorph.prodCongr (Homeomorph.refl ℝ) (cleOf hM).toHomeomorph).measurableEmbedding

/-- **`sepW` equivariance** (`PartIII-b:IIIb-D2/3/1/2/3/2`). -/
theorem sepWEquivariance : SepWEquivariance := by
  intro M hM ν μ T hT y τ hI
  funext i
  have hae := ae_ne_zero_sepRho y
  have hpt : ∀ᵐ p ∂sepRho, sepPhi ν μ T τ i (p.1, actM M p.2) (actM M y) =
      ∑ a : Fin 3, ((M i a : ℝ) : ℂ) * sepPhi ν μ T τ a p y := by
    filter_upwards [hae] with p hp
    exact sepPhi_equiv hM ν μ T hT τ i p.1 p.2 y hp
  have hsum : Integrable (fun p => ∑ a : Fin 3, ((M i a : ℝ) : ℂ) * sepPhi ν μ T τ a p y) sepRho :=
    integrable_finsetSum _ fun a _ => (hI a).const_mul _
  have hcomp : Integrable (fun p => sepPhi ν μ T τ i (p.1, actM M p.2) (actM M y)) sepRho :=
    hsum.congr (hpt.mono fun p hp => hp.symm)
  have hG : Integrable (fun p => sepPhi ν μ T τ i p (actM M y)) sepRho :=
    ((mp_phi hM).integrable_comp_emb (me_phi hM)).1 hcomp
  have hc := (mp_phi hM).integral_comp (me_phi hM) (fun p => sepPhi ν μ T τ i p (actM M y))
  show IIIa.sepW ν μ T (actM M y) τ i = ∑ a : Fin 3, ((M i a : ℝ) : ℂ) * IIIa.sepW ν μ T y τ a
  rw [sepW_eq_integral ν μ T τ i (actM M y) hG, ← hc, integral_congr_ae hpt]
  rw [integral_finsetSum (f := fun a p => ((M i a : ℝ) : ℂ) * sepPhi ν μ T τ a p y) _
    (fun a _ => (hI a).const_mul _)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [integral_const_mul, sepW_eq_integral ν μ T τ a y (hI a)]

end UnforcedLeray.Short.PartIIIb.Concrete
