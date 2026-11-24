import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_proj2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_3_6
import UnforcedLeray.Short.PartIIIa.Sub.T18_2_4_2
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.NiceForceSolution.LerayProjectSlices.P0CommWeakC
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.NiceForceSolution.LerayProjectSlices.SmoothSliceWeak
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.NiceForceSolution.LerayProjectSlices.LerayClassEnergy

/-!
# Gradient contraction of `P₀` on a smooth representative (organize task
`PartIII-b:C/flatset/col/7/1/1/2/4/2/3/4`, proves `P0GradContract`)

Source `the November 2 reference manuscript`
1650-1656, 1676. Route: the complexified `φ` and its `j`-derivatives are weak cell derivatives
(`ssw_weak_of_smooth`); `P0CommWeakC` transports them through `P₀`; `ψ = P0C φ` a.e. and the smooth
`ψ` has classical derivative equal to its weak one (`ssw_weak_of_smooth`), which is a.e. unique
(`weakCellDerivUnique`); the `L²` contraction `‖P₀‖ ≤ 1` (`ce_contract`) gives the inequality column
by column.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.Short.IIIa (vnorm2 tnorm2 P0C HasWeakCellDerivC)

/-- The complexified `φ` (`ℝ`-valued components, `ℂ`-valued). -/
def p0gC (φ : ℝ × ℝ → Fin 2 → ℝ) : ℝ × ℝ → Fin 2 → ℂ :=
  fun y i => ((φ y i : ℝ) : ℂ)

/-- The `j`-derivative of the complexified `φ`, componentwise: `∂_j φ_i`. -/
def p0gG (φ : ℝ × ℝ → Fin 2 → ℝ) (j : Fin 2) (y : ℝ × ℝ) : Fin 2 → ℂ :=
  fun i => ((fderiv ℝ (fun z => φ z i) y (B0579.dir j) : ℝ) : ℂ)

theorem p0g_vanish (φ : ℝ × ℝ → Fin 2 → ℝ) (L : ℝ) (hL : ∀ y : ℝ × ℝ, φ y ≠ 0 → |y.2| ≤ L) :
    ∀ y : ℝ × ℝ, L < |y.2| → ∀ i, φ y i = 0 := by
  intro y hy i
  by_contra h
  exact absurd (hL y (fun h0 => h (congrFun h0 i))) (not_le.2 hy)

theorem p0gG_cont (φ : ℝ × ℝ → Fin 2 → ℝ) (hφ : ∀ i, ContDiff ℝ ∞ fun y => φ y i) (j i : Fin 2) :
    Continuous fun y => p0gG φ j y i := by
  have h1 : Continuous (fun y => fderiv ℝ (fun z => φ z i) y) :=
    (hφ i).continuous_fderiv (by simp)
  exact Complex.continuous_ofReal.comp (h1.clm_apply continuous_const)

theorem p0gG_zero (φ : ℝ × ℝ → Fin 2 → ℝ) (L : ℝ)
    (hv : ∀ y : ℝ × ℝ, L < |y.2| → ∀ i, φ y i = 0) (j : Fin 2) (y : ℝ × ℝ) (hy : L < |y.2|)
    (i : Fin 2) : p0gG φ j y i = 0 := by
  have h0 : B0579.pd j (fun z => φ z i) y = 0 :=
    IIIa.ssw_pd_eq_zero (fun x hx => hv x hx i) j hy
  have e : p0gG φ j y i = ((B0579.pd j (fun z => φ z i) y : ℝ) : ℂ) := rfl
  rw [e, h0]
  simp

theorem p0g_fderiv_ofReal (f : ℝ × ℝ → ℝ) (hf : Differentiable ℝ f) (x v : ℝ × ℝ) :
    fderiv ℝ (fun y => ((f y : ℝ) : ℂ)) x v = ((fderiv ℝ f x v : ℝ) : ℂ) := by
  have h1 : HasFDerivAt (fun y => ((f y : ℝ) : ℂ)) (Complex.ofRealCLM.comp (fderiv ℝ f x)) x :=
    Complex.ofRealCLM.hasFDerivAt.comp x (hf x).hasFDerivAt
  rw [h1.fderiv]
  simp

theorem p0g_reVec_cont {F : ℝ × ℝ → Fin 2 → ℂ} (hF : ∀ i, Continuous fun y => F y i) :
    Continuous (IIIa.reVec F) :=
  IIIa.ce_cont_vec2 (fun y => (F y 0).re) (fun y => (F y 1).re)
    (Complex.continuous_re.comp (hF 0)) (Complex.continuous_re.comp (hF 1))

theorem p0g_imVec_cont {F : ℝ × ℝ → Fin 2 → ℂ} (hF : ∀ i, Continuous fun y => F y i) :
    Continuous (IIIa.imVec F) :=
  IIIa.ce_cont_vec2 (fun y => (F y 0).im) (fun y => (F y 1).im)
    (Complex.continuous_im.comp (hF 0)) (Complex.continuous_im.comp (hF 1))

theorem p0g_reVec_zero {F : ℝ × ℝ → Fin 2 → ℂ} {L : ℝ}
    (hv : ∀ y : ℝ × ℝ, L < |y.2| → ∀ i, F y i = 0) :
    ∀ z : ℝ × ℝ, L < |z.2| → IIIa.reVec F z = 0 := by
  intro z hz
  have h0 := hv z hz 0
  have h1 := hv z hz 1
  unfold IIIa.reVec
  rw [h0, h1]
  ext i
  fin_cases i <;> simp

theorem p0g_imVec_zero {F : ℝ × ℝ → Fin 2 → ℂ} {L : ℝ}
    (hv : ∀ y : ℝ × ℝ, L < |y.2| → ∀ i, F y i = 0) :
    ∀ z : ℝ × ℝ, L < |z.2| → IIIa.imVec F z = 0 := by
  intro z hz
  have h0 := hv z hz 0
  have h1 := hv z hz 1
  unfold IIIa.imVec
  rw [h0, h1]
  ext i
  fin_cases i <;> simp

theorem p0g_memLp_re {c L : ℝ} {F : ℝ × ℝ → Fin 2 → ℂ} (hF : ∀ i, Continuous fun y => F y i)
    (hv : ∀ y : ℝ × ℝ, L < |y.2| → ∀ i, F y i = 0) :
    MemLp (IIIa.reVec F) 2 (UnforcedLeray.Cyl.cellμ c) :=
  UnforcedLeray.Cyl.memLp_of_vanishes (p0g_reVec_cont hF) (R := L) (p0g_reVec_zero hv) 2

theorem p0g_memLp_im {c L : ℝ} {F : ℝ × ℝ → Fin 2 → ℂ} (hF : ∀ i, Continuous fun y => F y i)
    (hv : ∀ y : ℝ × ℝ, L < |y.2| → ∀ i, F y i = 0) :
    MemLp (IIIa.imVec F) 2 (UnforcedLeray.Cyl.cellμ c) :=
  UnforcedLeray.Cyl.memLp_of_vanishes (p0g_imVec_cont hF) (R := L) (p0g_imVec_zero hv) 2

/-- The `L²` contraction of `P₀` applied to one real `L²` class. -/
theorem p0g_contract_part {c : ℝ} (H : ℝ × ℝ → UnforcedLeray.Cyl.Vec2)
    (hH : MemLp H 2 (UnforcedLeray.Cyl.cellμ c)) :
    ∫⁻ x, ENNReal.ofReal (‖UnforcedLeray.Cyl.P0 c (IIIa.toL2v c H) x‖ ^ 2)
        ∂(UnforcedLeray.Cyl.cellμ c) ≤
      ∫⁻ x, ENNReal.ofReal (‖H x‖ ^ 2) ∂(UnforcedLeray.Cyl.cellμ c) := by
  have eF : IIIa.toL2v c H = hH.toLp H := by
    unfold IIIa.toL2v
    rw [dif_pos hH]
  have hae : (IIIa.toL2v c H : ℝ × ℝ → UnforcedLeray.Cyl.Vec2) =ᵐ[UnforcedLeray.Cyl.cellμ c] H := by
    rw [eF]
    exact MemLp.coeFn_toLp hH
  refine (IIIa.ce_contract c (IIIa.toL2v c H)).trans (le_of_eq ?_)
  refine lintegral_congr_ae ?_
  filter_upwards [hae] with x hx
  rw [hx]

theorem p0g_aemeas (c : ℝ) (G : ℝ × ℝ → Fin 2 → ℂ) :
    AEMeasurable (fun x => ENNReal.ofReal (vnorm2 (IIIa.P0C c G x) ^ 2))
      (UnforcedLeray.Cyl.cellμ c) := by
  have e : (fun x => ENNReal.ofReal (vnorm2 (IIIa.P0C c G x) ^ 2)) =
      fun x => ENNReal.ofReal (‖IIIa.P0re c G x‖ ^ 2) + ENNReal.ofReal (‖IIIa.P0im c G x‖ ^ 2) := by
    funext x
    rw [IIIa.ce_vnorm_P0C, ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
  rw [e]
  exact (IIIa.ce_aemeas (IIIa.P0re c G)).add (IIIa.ce_aemeas (IIIa.P0im c G))

theorem p0g_vn_meas {G : ℝ × ℝ → Fin 2 → ℂ} (hGc : ∀ i, Continuous fun y => G y i) :
    Measurable fun x => ENNReal.ofReal (vnorm2 (G x) ^ 2) := by
  have hc : Continuous fun x => ∑ i, ‖G x i‖ ^ 2 :=
    continuous_finsetSum _ fun i _ => ((hGc i).norm).pow 2
  have e : (fun x => ENNReal.ofReal (vnorm2 (G x) ^ 2)) =
      fun x => ENNReal.ofReal (∑ i, ‖G x i‖ ^ 2) := by
    funext x
    rw [IIIa.ce_vnorm2_sq']
  rw [e]
  exact hc.measurable.ennreal_ofReal

/-- Per column: `∫ |P₀ G|² ≤ ∫ |G|²` for a continuous `G` vanishing for large `|η|`. -/
theorem p0g_per_j {c : ℝ} (G : ℝ × ℝ → Fin 2 → ℂ) (hGc : ∀ i, Continuous fun y => G y i)
    {L : ℝ} (hGv : ∀ y : ℝ × ℝ, L < |y.2| → ∀ i, G y i = 0) :
    ∫⁻ x, ENNReal.ofReal (vnorm2 (IIIa.P0C c G x) ^ 2) ∂(UnforcedLeray.Cyl.cellμ c) ≤
      ∫⁻ x, ENNReal.ofReal (vnorm2 (G x) ^ 2) ∂(UnforcedLeray.Cyl.cellμ c) := by
  have hRm : MemLp (IIIa.reVec G) 2 (UnforcedLeray.Cyl.cellμ c) := p0g_memLp_re hGc hGv
  have hIm : MemLp (IIIa.imVec G) 2 (UnforcedLeray.Cyl.cellμ c) := p0g_memLp_im hGc hGv
  have key2 : ∀ x, vnorm2 (G x) ^ 2 = ‖IIIa.reVec G x‖ ^ 2 + ‖IIIa.imVec G x‖ ^ 2 := by
    intro x
    have e : G x = fun i => ((IIIa.reVec G x i : ℝ) : ℂ) + Complex.I * ((IIIa.imVec G x i : ℝ) : ℂ) := by
      funext i
      rw [IIIa.reVec_apply_pc, IIIa.imVec_apply_pc, mul_comm]
      exact (Complex.re_add_im (G x i)).symm
    rw [e]
    exact IIIa.ce_vnorm_cplx _ _
  have hBm : Measurable (fun x => ENNReal.ofReal (‖IIIa.reVec G x‖ ^ 2)) :=
    ((p0g_reVec_cont hGc).norm.pow 2).measurable.ennreal_ofReal
  have hsplit : ∫⁻ x, ENNReal.ofReal (vnorm2 (IIIa.P0C c G x) ^ 2) ∂(UnforcedLeray.Cyl.cellμ c) =
      ∫⁻ x, ENNReal.ofReal (‖IIIa.P0re c G x‖ ^ 2) ∂(UnforcedLeray.Cyl.cellμ c) +
        ∫⁻ x, ENNReal.ofReal (‖IIIa.P0im c G x‖ ^ 2) ∂(UnforcedLeray.Cyl.cellμ c) := by
    rw [← lintegral_add_left' (IIIa.ce_aemeas (IIIa.P0re c G))
      (fun x => ENNReal.ofReal (‖IIIa.P0im c G x‖ ^ 2))]
    refine lintegral_congr fun x => ?_
    rw [IIIa.ce_vnorm_P0C, ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
  have h1 : ∫⁻ x, ENNReal.ofReal (‖IIIa.P0re c G x‖ ^ 2) ∂(UnforcedLeray.Cyl.cellμ c) ≤
      ∫⁻ x, ENNReal.ofReal (‖IIIa.reVec G x‖ ^ 2) ∂(UnforcedLeray.Cyl.cellμ c) :=
    p0g_contract_part (IIIa.reVec G) hRm
  have h2 : ∫⁻ x, ENNReal.ofReal (‖IIIa.P0im c G x‖ ^ 2) ∂(UnforcedLeray.Cyl.cellμ c) ≤
      ∫⁻ x, ENNReal.ofReal (‖IIIa.imVec G x‖ ^ 2) ∂(UnforcedLeray.Cyl.cellμ c) :=
    p0g_contract_part (IIIa.imVec G) hIm
  rw [hsplit]
  refine (add_le_add h1 h2).trans (le_of_eq ?_)
  rw [← lintegral_add_left hBm (fun x => ENNReal.ofReal (‖IIIa.imVec G x‖ ^ 2))]
  refine lintegral_congr fun x => ?_
  rw [key2 x, ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]

/-- **Gradient contraction of `P₀` on a smooth representative** (`P0GradContract`). -/
theorem p0GradContract : P0GradContract := by
  intro c hc φ ψ hφ hφp hφsupp hψ hψp hae
  obtain ⟨L, hL⟩ := hφsupp
  have hv : ∀ y : ℝ × ℝ, L < |y.2| → ∀ i, φ y i = 0 := p0g_vanish φ L hL
  have hΦc : ∀ i, Continuous fun y => p0gC φ y i :=
    fun i => Complex.continuous_ofReal.comp (hφ i).continuous
  have hΦv : ∀ y : ℝ × ℝ, L < |y.2| → ∀ i, p0gC φ y i = 0 := fun y hy i => by
    show ((φ y i : ℝ) : ℂ) = 0
    rw [hv y hy i]
    simp
  have hΦsmooth : ∀ i, ContDiff ℝ ∞ fun y => p0gC φ y i :=
    fun i => Complex.ofRealCLM.contDiff.comp (hφ i)
  have hRΦ : MemLp (IIIa.reVec (p0gC φ)) 2 (UnforcedLeray.Cyl.cellμ c) :=
    p0g_memLp_re hΦc hΦv
  have hIΦ : MemLp (IIIa.imVec (p0gC φ)) 2 (UnforcedLeray.Cyl.cellμ c) :=
    p0g_memLp_im hΦc hΦv
  have hRG : ∀ j, MemLp (IIIa.reVec (p0gG φ j)) 2 (UnforcedLeray.Cyl.cellμ c) :=
    fun j => p0g_memLp_re (fun i => p0gG_cont φ hφ j i) (fun y hy i => p0gG_zero φ L hv j y hy i)
  have hIG : ∀ j, MemLp (IIIa.imVec (p0gG φ j)) 2 (UnforcedLeray.Cyl.cellμ c) :=
    fun j => p0g_memLp_im (fun i => p0gG_cont φ hφ j i) (fun y hy i => p0gG_zero φ L hv j y hy i)
  -- weak derivatives of the complexified components
  have hwG : ∀ i j, HasWeakCellDerivC c j (fun x => p0gC φ x i) (fun x => p0gG φ j x i) := by
    intro i j
    have hper : ∀ x : ℝ × ℝ,
        (fun y : ℝ × ℝ => ((φ y i : ℝ) : ℂ)) (x.1 + c, x.2) = (fun y : ℝ × ℝ => ((φ y i : ℝ) : ℂ)) x := by
      intro x
      show ((φ (x.1 + c, x.2) i : ℝ) : ℂ) = ((φ x i : ℝ) : ℂ)
      rw [hφp x.1 x.2]
    have h := IIIa.ssw_weak_of_smooth (c := c) (a := fun y => ((φ y i : ℝ) : ℂ))
      (Complex.ofRealCLM.contDiff.comp (hφ i)) hper j
    have hd : ∀ x, IIIa.pdC j (fun y => ((φ y i : ℝ) : ℂ)) x = p0gG φ j x i := fun x =>
      p0g_fderiv_ofReal (fun z => φ z i) ((hφ i).differentiable (by simp)) x (B0579.dir j)
    have e : (fun x => IIIa.pdC j (fun y => ((φ y i : ℝ) : ℂ)) x) = fun x => p0gG φ j x i :=
      funext hd
    rw [e] at h
    exact h
  -- `P₀` transports them
  have hP := IIIa.p0CommWeakC c hc (p0gC φ) (p0gG φ) hRΦ hIΦ hRG hIG hwG
  -- `ψ = P₀ φ` a.e., componentwise on the cell
  have hψi : ∀ i, (fun y => ψ y i) =ᵐ[UnforcedLeray.Cyl.cellμ c]
      (fun x => IIIa.P0C c (p0gC φ) x i) := fun i => by
    filter_upwards [hae] with x hx
    exact congrFun hx i
  have hψi' : ∀ i j, HasWeakCellDerivC c j (fun y => ψ y i)
      (fun x => IIIa.P0C c (p0gG φ j) x i) := fun i j => by
    have hcell := hψi i
    rw [IIIa.cellμ_eq c] at hcell
    exact HasWeakCellDerivC.congr_ae hcell (Filter.EventuallyEq.refl _ _) (hP i j)
  -- the smooth `ψ` has classical derivative = weak derivative
  have hψw : ∀ i j, HasWeakCellDerivC c j (fun y => ψ y i)
      (fun x => IIIa.pdC j (fun y => ψ y i) x) := fun i j =>
    IIIa.ssw_weak_of_smooth (hψ i)
      (fun x => by
        show ψ (x.1 + c, x.2) i = ψ x i
        rw [hψp x.1 x.2]) j
  have hu : ∀ i j, (fun x => IIIa.pdC j (fun y => ψ y i) x) =ᵐ[UnforcedLeray.Cyl.cellμ c]
      (fun x => IIIa.P0C c (p0gG φ j) x i) := fun i j =>
    weakCellDerivUnique c hc j (fun y => ψ y i) (fun x => IIIa.pdC j (fun y => ψ y i) x)
      (fun x => IIIa.P0C c (p0gG φ j) x i) (hψw i j) (hψi' i j)
  have hall : ∀ᵐ x ∂(UnforcedLeray.Cyl.cellμ c), ∀ i j,
      IIIa.pdC j (fun y => ψ y i) x = IIIa.P0C c (p0gG φ j) x i := by
    rw [ae_all_iff]
    intro i
    rw [ae_all_iff]
    intro j
    exact hu i j
  -- pointwise identities
  have hLHS : ∀ᵐ x ∂(UnforcedLeray.Cyl.cellμ c),
      ENNReal.ofReal (tnorm2 (fun i j => fderiv ℝ (fun y => ψ y i) x (B0579.dir j)) ^ 2) =
        ENNReal.ofReal (vnorm2 (IIIa.P0C c (p0gG φ 0) x) ^ 2) +
          ENNReal.ofReal (vnorm2 (IIIa.P0C c (p0gG φ 1) x) ^ 2) := by
    filter_upwards [hall] with x hx
    have e : (fun i j => fderiv ℝ (fun y => ψ y i) x (B0579.dir j)) =
        (fun i j => IIIa.P0C c (p0gG φ j) x i) := by
      funext i j
      exact hx i j
    have key := IIIa.ce_tn_split (fun j => IIIa.P0C c (p0gG φ j)) x
    beta_reduce at key
    rw [e, key, ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
  have hR : ∀ x, ENNReal.ofReal (tnorm2 (fun i j =>
        ((fderiv ℝ (fun y => φ y i) x (B0579.dir j) : ℝ) : ℂ)) ^ 2) =
      ENNReal.ofReal (vnorm2 (p0gG φ 0 x) ^ 2) + ENNReal.ofReal (vnorm2 (p0gG φ 1 x) ^ 2) := by
    intro x
    have key := IIIa.ce_tn_split (p0gG φ) x
    rw [show (fun i j => ((fderiv ℝ (fun y => φ y i) x (B0579.dir j) : ℝ) : ℂ)) =
      (fun i j => p0gG φ j x i) from rfl, key, ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
  -- assemble
  have hm : (volume.restrict (Ico (-(c / 2)) (c / 2) ×ˢ (univ : Set ℝ))) =
      UnforcedLeray.Cyl.cellμ c := (IIIa.cellμ_eq c).symm
  rw [hm]
  calc ∫⁻ x, ENNReal.ofReal (tnorm2 (fun i j => fderiv ℝ (fun y => ψ y i) x (B0579.dir j)) ^ 2)
        ∂(UnforcedLeray.Cyl.cellμ c)
      = ∫⁻ x, (ENNReal.ofReal (vnorm2 (IIIa.P0C c (p0gG φ 0) x) ^ 2) +
          ENNReal.ofReal (vnorm2 (IIIa.P0C c (p0gG φ 1) x) ^ 2)) ∂(UnforcedLeray.Cyl.cellμ c) :=
        lintegral_congr_ae hLHS
    _ = ∫⁻ x, ENNReal.ofReal (vnorm2 (IIIa.P0C c (p0gG φ 0) x) ^ 2) ∂(UnforcedLeray.Cyl.cellμ c) +
          ∫⁻ x, ENNReal.ofReal (vnorm2 (IIIa.P0C c (p0gG φ 1) x) ^ 2) ∂(UnforcedLeray.Cyl.cellμ c) :=
        lintegral_add_left' (p0g_aemeas c (p0gG φ 0))
          (fun x => ENNReal.ofReal (vnorm2 (IIIa.P0C c (p0gG φ 1) x) ^ 2))
    _ ≤ ∫⁻ x, ENNReal.ofReal (vnorm2 (p0gG φ 0 x) ^ 2) ∂(UnforcedLeray.Cyl.cellμ c) +
          ∫⁻ x, ENNReal.ofReal (vnorm2 (p0gG φ 1 x) ^ 2) ∂(UnforcedLeray.Cyl.cellμ c) :=
        add_le_add (p0g_per_j (p0gG φ 0) (fun i => p0gG_cont φ hφ 0 i)
          (fun y hy i => p0gG_zero φ L hv 0 y hy i))
          (p0g_per_j (p0gG φ 1) (fun i => p0gG_cont φ hφ 1 i)
          (fun y hy i => p0gG_zero φ L hv 1 y hy i))
    _ = ∫⁻ x, ENNReal.ofReal (tnorm2 (fun i j =>
          ((fderiv ℝ (fun y => φ y i) x (B0579.dir j) : ℝ) : ℂ)) ^ 2) ∂(UnforcedLeray.Cyl.cellμ c) :=
        ((lintegral_add_left' (p0g_vn_meas (fun i => p0gG_cont φ hφ 0 i)).aemeasurable
          (fun x => ENNReal.ofReal (vnorm2 (p0gG φ 1 x) ^ 2))).symm).trans
          (lintegral_congr fun x => (hR x).symm)

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
