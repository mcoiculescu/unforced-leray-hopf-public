import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.FullKerReg.PrimY

/-!
# `PDYKerBound` helpers (1): the joint derivative of the phase-lag kernel

Source `the November 2 reference manuscript` 4198-4205, 3700-3713.

`ykJ (h, x) = xKer ν μ h x M` is `C²` on `{h > 0}` (`xKer_jointC2`).  Its derivative `DJ` splits
into the partials `DJ (1, v) = ∂_h xKer + D_x xKer · v`; the `h`-derivative of the transported
kernel `h ↦ xKer(h, a - λ(h) z)` is `DJ (1, (λ/2) z)` (`λ' = -λ/2`), and the bound
`‖DJ (1, v)‖ ≤ C λ^{2μ+3} (|x|^{-4} + ν|x|^{-6} + |x|^{-5}|v|)|M|` comes from `PDKerBounds`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The body of `PDKerBounds` for a fixed constant. -/
def YKB (C : ℝ) : Prop :=
  0 ≤ C ∧ ∀ (ν μ h : ℝ), 0 < ν → -(1 / 4) < μ → μ ≤ 1 → 0 < h →
    ∀ (M : Matrix (Fin 3) (Fin 3) ℝ),
      ContDiff ℝ 2 (fun x' => xKer ν μ h x' M) ∧
      (∀ x : Space, DifferentiableAt ℝ (fun h' => xKer ν μ h' x M) h) ∧
      ∀ x : Space, x ≠ 0 →
        ‖xKer ν μ h x M‖ ≤ C * pdLam h ^ (2 * μ + 3) * (‖x‖ ^ 4)⁻¹ * IIIa.tensorNorm M ∧
        ‖fderiv ℝ (fun x' => xKer ν μ h x' M) x‖ ≤
          C * pdLam h ^ (2 * μ + 3) * (‖x‖ ^ 5)⁻¹ * IIIa.tensorNorm M ∧
        ‖iteratedFDeriv ℝ 2 (fun x' => xKer ν μ h x' M) x‖ ≤
          C * pdLam h ^ (2 * μ + 3) * (‖x‖ ^ 6)⁻¹ * IIIa.tensorNorm M ∧
        ‖deriv (fun h' => xKer ν μ h' x M) h‖ ≤
          C * pdLam h ^ (2 * μ + 3) * ((‖x‖ ^ 4)⁻¹ + ν * (‖x‖ ^ 6)⁻¹) * IIIa.tensorNorm M ∧
        ‖wKer ν μ h x M‖ ≤ C * pdLam h ^ (2 * μ + 3) * (‖x‖ ^ 4)⁻¹ * IIIa.tensorNorm M

theorem ykb_exists : ∃ C : ℝ, YKB C := pdKerBounds

/-- A joint derivative gives the two partial derivatives. -/
theorem ykb_partials {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : ℝ × E → F} {a : ℝ} {x : E}
    {L : ℝ × E →L[ℝ] F} (hf : HasFDerivAt f L (a, x)) :
    HasDerivAt (fun t => f (t, x)) (L (1, 0)) a ∧
      HasFDerivAt (fun x' => f (a, x')) (L.comp (ContinuousLinearMap.inr ℝ ℝ E)) x := by
  refine ⟨?_, ?_⟩
  · have hp : HasDerivAt (fun t : ℝ => (t, x)) ((1 : ℝ), (0 : E)) a :=
      (hasDerivAt_id' a).prodMk (hasDerivAt_const a x)
    exact hf.comp_hasDerivAt a hp
  · exact hf.comp x (hasFDerivAt_prodMk_right a x)

/-- The joint kernel `(h, x) ↦ xKer ν μ h x M`. -/
def ykJ (ν μ : ℝ) (M : Matrix (Fin 3) (Fin 3) ℝ) (p : ℝ × Space) : Space := xKer ν μ p.1 p.2 M

theorem ykJ_open : IsOpen {p : ℝ × Space | 0 < p.1} := isOpen_lt continuous_const continuous_fst

theorem ykJ_hasFDerivAt (ν μ : ℝ) (hν : 0 < ν) (M : Matrix (Fin 3) (Fin 3) ℝ) {h : ℝ}
    (hh : 0 < h) (x : Space) :
    HasFDerivAt (ykJ ν μ M) (fderiv ℝ (ykJ ν μ M) (h, x)) (h, x) := by
  have hd := (xKer_jointC2 ν μ hν M).differentiableOn (by norm_num)
  exact (hd.differentiableAt (ykJ_open.mem_nhds (show (0 : ℝ) < (h, x).1 from hh))).hasFDerivAt

theorem ykJ_contDiffOn (ν μ : ℝ) (hν : 0 < ν) (M : Matrix (Fin 3) (Fin 3) ℝ) :
    ContDiffOn ℝ 2 (ykJ ν μ M) {p : ℝ × Space | 0 < p.1} := xKer_jointC2 ν μ hν M

theorem ykJ_continuousOn_fderiv (ν μ : ℝ) (hν : 0 < ν) (M : Matrix (Fin 3) (Fin 3) ℝ) :
    ContinuousOn (fderiv ℝ (ykJ ν μ M)) {p : ℝ × Space | 0 < p.1} :=
  (ykJ_contDiffOn ν μ hν M).continuousOn_fderiv_of_isOpen ykJ_open (by norm_num)

/-- The partial derivatives of `xKer` through the joint derivative. -/
theorem ykJ_deriv_eq (ν μ : ℝ) (hν : 0 < ν) (M : Matrix (Fin 3) (Fin 3) ℝ) {h : ℝ}
    (hh : 0 < h) (x : Space) :
    deriv (fun t => xKer ν μ t x M) h = fderiv ℝ (ykJ ν μ M) (h, x) (1, 0) :=
  (ykb_partials (ykJ_hasFDerivAt ν μ hν M hh x)).1.deriv

theorem ykJ_fderiv_eq (ν μ : ℝ) (hν : 0 < ν) (M : Matrix (Fin 3) (Fin 3) ℝ) {h : ℝ}
    (hh : 0 < h) (x v : Space) :
    fderiv ℝ (fun x' => xKer ν μ h x' M) x v = fderiv ℝ (ykJ ν μ M) (h, x) (0, v) := by
  have e : fderiv ℝ (fun x' => xKer ν μ h x' M) x =
      (fderiv ℝ (ykJ ν μ M) (h, x)).comp (ContinuousLinearMap.inr ℝ ℝ Space) :=
    (ykb_partials (ykJ_hasFDerivAt ν μ hν M hh x)).2.fderiv
  rw [e]
  rfl

theorem ykJ_split (L : ℝ × Space →L[ℝ] Space) (a : ℝ) (v : Space) :
    L (a, v) = a • L (1, 0) + L (0, v) := by
  rw [← map_smul, ← map_add]
  congr 1
  ext <;> simp

/-- `λ' = -λ/2`. -/
theorem ykb_pdLam_hasDerivAt (h : ℝ) : HasDerivAt pdLam (-(pdLam h) / 2) h := by
  unfold pdLam
  have h1 : HasDerivAt (fun t : ℝ => -(t / 2)) (-(1 / 2)) h :=
    ((hasDerivAt_id' h).div_const 2).neg
  have h2 := h1.exp
  convert h2 using 1
  ring

theorem ykb_path (a z : Space) (h : ℝ) :
    HasDerivAt (fun t : ℝ => (t, a - pdLam t • z)) ((1 : ℝ), (pdLam h / 2) • z) h := by
  refine (hasDerivAt_id' h).prodMk ?_
  have := ((ykb_pdLam_hasDerivAt h).smul_const z).const_sub a
  refine this.congr_deriv ?_
  rw [neg_div, neg_smul, neg_neg]

/-- **Part 1 `h`-derivative**: the transported kernel `t ↦ xKer(t, a - λ(t) z)`. -/
theorem ykb_partB (ν μ : ℝ) (hν : 0 < ν) (M : Matrix (Fin 3) (Fin 3) ℝ) {h : ℝ} (hh : 0 < h)
    (a z : Space) :
    HasDerivAt (fun t => xKer ν μ t (a - pdLam t • z) M)
      (fderiv ℝ (ykJ ν μ M) (h, a - pdLam h • z) (1, (pdLam h / 2) • z)) h := by
  have hJ := ykJ_hasFDerivAt ν μ hν M hh (a - pdLam h • z)
  exact hJ.comp_hasDerivAt h (ykb_path a z h)

theorem ykb_pdLam_rpow_le_one (μ h : ℝ) (hμ : -(1 / 4) < μ) (hh : 0 ≤ h) :
    pdLam h ^ (2 * μ + 3) ≤ 1 := by
  have h0 : 0 ≤ pdLam h := (pdLam_pos h).le
  have h1 : pdLam h ≤ 1 := by
    unfold pdLam
    rw [Real.exp_le_one_iff]
    linarith
  exact Real.rpow_le_one h0 h1 (by linarith)

theorem ykb_rpow_nonneg (μ h : ℝ) : 0 ≤ pdLam h ^ (2 * μ + 3) :=
  Real.rpow_nonneg (pdLam_pos h).le _

/-- `‖DJ (1, v)‖ ≤ C λ^{2μ+3} (|x|^{-4} + ν|x|^{-6} + |x|^{-5}|v|) |M|`. -/
theorem ykb_DJ_bound {C : ℝ} (hC : YKB C) (ν μ : ℝ) (hν : 0 < ν) (hμ0 : -(1 / 4) < μ)
    (hμ1 : μ ≤ 1) (M : Matrix (Fin 3) (Fin 3) ℝ) {h : ℝ} (hh : 0 < h) {x : Space} (hx : x ≠ 0)
    (v : Space) :
    ‖fderiv ℝ (ykJ ν μ M) (h, x) (1, v)‖ ≤
      C * pdLam h ^ (2 * μ + 3) * IIIa.tensorNorm M *
        ((‖x‖ ^ 4)⁻¹ + ν * (‖x‖ ^ 6)⁻¹ + (‖x‖ ^ 5)⁻¹ * ‖v‖) := by
  obtain ⟨-, -, hb⟩ := hC.2 ν μ h hν hμ0 hμ1 hh M
  obtain ⟨-, b1, -, b3, -⟩ := hb x hx
  rw [ykJ_split, one_smul, ← ykJ_deriv_eq ν μ hν M hh, ← ykJ_fderiv_eq ν μ hν M hh]
  have e1 : ‖fderiv ℝ (fun x' => xKer ν μ h x' M) x v‖ ≤
      C * pdLam h ^ (2 * μ + 3) * (‖x‖ ^ 5)⁻¹ * IIIa.tensorNorm M * ‖v‖ :=
    ((fderiv ℝ (fun x' => xKer ν μ h x' M) x).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right b1 (norm_nonneg v))
  refine (norm_add_le _ _).trans ?_
  have : C * pdLam h ^ (2 * μ + 3) * ((‖x‖ ^ 4)⁻¹ + ν * (‖x‖ ^ 6)⁻¹) * IIIa.tensorNorm M +
      C * pdLam h ^ (2 * μ + 3) * (‖x‖ ^ 5)⁻¹ * IIIa.tensorNorm M * ‖v‖ =
      C * pdLam h ^ (2 * μ + 3) * IIIa.tensorNorm M *
        ((‖x‖ ^ 4)⁻¹ + ν * (‖x‖ ^ 6)⁻¹ + (‖x‖ ^ 5)⁻¹ * ‖v‖) := by ring
  linarith

/-- Inverse powers for `κ ≤ v ≤ X`. -/
theorem ykb_pow_inv {κ v X : ℝ} (hκ : 0 < κ) (hv : κ ≤ v) (hX : v ≤ X) :
    (X ^ 4)⁻¹ ≤ (v ^ 4)⁻¹ ∧ (X ^ 5)⁻¹ ≤ κ⁻¹ * (v ^ 4)⁻¹ ∧ (X ^ 6)⁻¹ ≤ (κ ^ 2)⁻¹ * (v ^ 4)⁻¹ := by
  have hv0 : 0 < v := lt_of_lt_of_le hκ hv
  have hX0 : 0 < X := lt_of_lt_of_le hv0 hX
  have h4 : v ^ 4 ≤ X ^ 4 := pow_le_pow_left₀ hv0.le hX 4
  refine ⟨inv_anti₀ (by positivity) h4, ?_, ?_⟩
  · rw [← mul_inv]
    refine inv_anti₀ (by positivity) ?_
    calc κ * v ^ 4 ≤ X * X ^ 4 := mul_le_mul (hv.trans hX) h4 (by positivity) hX0.le
      _ = X ^ 5 := by ring
  · rw [← mul_inv]
    refine inv_anti₀ (by positivity) ?_
    have hk2 : κ ^ 2 ≤ X ^ 2 := pow_le_pow_left₀ hκ.le (hv.trans hX) 2
    calc κ ^ 2 * v ^ 4 ≤ X ^ 2 * X ^ 4 := mul_le_mul hk2 h4 (by positivity) (by positivity)
      _ = X ^ 6 := by ring

/-- The specialized combination bound `‖DJ (1, v)‖ ≤ C λ^p |M| (1 + ν κ^{-2} + |v| κ^{-1}) v₀^{-4}`
for `κ ≤ v₀ ≤ |x|`. -/
theorem ykb_DJ_bound' {C : ℝ} (hC : YKB C) (ν μ : ℝ) (hν : 0 < ν) (hμ0 : -(1 / 4) < μ)
    (hμ1 : μ ≤ 1) (M : Matrix (Fin 3) (Fin 3) ℝ) {h : ℝ} (hh : 0 < h) {x : Space}
    {κ v₀ : ℝ} (hκ : 0 < κ) (hv : κ ≤ v₀) (hX : v₀ ≤ ‖x‖) (v : Space) :
    ‖fderiv ℝ (ykJ ν μ M) (h, x) (1, v)‖ ≤
      C * pdLam h ^ (2 * μ + 3) * IIIa.tensorNorm M *
        ((1 + ν * (κ ^ 2)⁻¹ + ‖v‖ * κ⁻¹) * (v₀ ^ 4)⁻¹) := by
  have hx : x ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hX; linarith
  refine (ykb_DJ_bound hC ν μ hν hμ0 hμ1 M hh hx v).trans ?_
  have hK : 0 ≤ C * pdLam h ^ (2 * μ + 3) * IIIa.tensorNorm M :=
    mul_nonneg (mul_nonneg hC.1 (ykb_rpow_nonneg μ h)) (kb_tensor_nonneg M)
  refine mul_le_mul_of_nonneg_left ?_ hK
  obtain ⟨p4, p5, p6⟩ := ykb_pow_inv hκ hv hX
  have hv4 : 0 ≤ (v₀ ^ 4)⁻¹ := by have := lt_of_lt_of_le hκ hv; positivity
  have a1 : ν * (‖x‖ ^ 6)⁻¹ ≤ ν * ((κ ^ 2)⁻¹ * (v₀ ^ 4)⁻¹) := mul_le_mul_of_nonneg_left p6 hν.le
  have a2 : (‖x‖ ^ 5)⁻¹ * ‖v‖ ≤ (κ⁻¹ * (v₀ ^ 4)⁻¹) * ‖v‖ :=
    mul_le_mul_of_nonneg_right p5 (norm_nonneg v)
  nlinarith

end UnforcedLeray.Short.PartIIIb.Concrete

end
