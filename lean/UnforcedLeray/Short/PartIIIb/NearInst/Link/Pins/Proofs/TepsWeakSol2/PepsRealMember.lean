import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Sub.PartIIIb_C_near_pins_3_2
import UnforcedLeray.Short.PartIIIb.NearInst.Body.Defs

/-!
# `PepsRealMember` (task `PartIII-b:C/near/pins/3/2/1`)

Source `the November 2 reference manuscript` 1675-1677.

`g := P_ε z` lies in `solenoidalHC` (the orthogonal complement of the complexified profile
gradients). Its real part `b := merReL g` is orthogonal to every real profile gradient, hence lies in
`B0226.solenoidalH`; and `b = wk ∘ cellPt` a.e. because `g = merC (wk ∘ cellPt)` a.e.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal InnerProductSpace ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.NearInst

open UnforcedLeray.Short.PartIIIb.Concrete UnforcedLeray.Cons.C03.Concrete
  UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.B0220 (HSpace measureH Profile)
open UnforcedLeray.B0223 (MeridC)

/-- The complexified gradient is the complex image of the real profile gradient. -/
theorem pepsRealMember_cgrad_eq (ε : ℝ) (Φ : Profile → ℝ) :
    UnforcedLeray.Short.PartIIa.cgrad ε Φ =
      fun p => merC (UnforcedLeray.B0226.profileGrad ε Φ p) := by
  funext p
  ext i
  fin_cases i <;> simp [UnforcedLeray.Short.PartIIa.cgrad, UnforcedLeray.B0226.profileGrad, merC,
    UnforcedLeray.B0226.Deps]

theorem pepsRealMember_merC_lip : LipschitzWith 1 merC := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [EuclideanSpace.dist_eq, EuclideanSpace.dist_eq]
  simp only [merC, NNReal.coe_one, one_mul, Complex.dist_eq, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs, Real.dist_eq]
  exact le_rfl

theorem pepsRealMember_memLp_cgrad {c : ℝ} (ε : ℝ) (Φ : UnforcedLeray.B0226.ProfileTest c) :
    MemLp (UnforcedLeray.Short.PartIIa.cgrad ε Φ.1) 2 (measureH c) := by
  have h := UnforcedLeray.B0226.memLp_profileGrad ε Φ.2
  rw [pepsRealMember_cgrad_eq]
  have h0 : merC 0 = 0 := by ext i; simp [merC]
  exact LipschitzWith.comp_memLp (g := merC) pepsRealMember_merC_lip h0 h

theorem pepsRealMember_merReL_merC (x : Merid) :
    Body.merReL (merC x) = x := by
  ext i
  simp [Body.merReL, Body.merReLin, merC]

theorem pepsRealMember : PepsRealMember := by
  intro p z wk hwk
  have hwk' : (UnforcedLeray.Short.PartIIa.PepsC p.ε p.c z : Profile → MeridC) =ᵐ[measureH p.c]
      fun q => merC (wk (cellPt p.c q)) := hwk
  have hG : UnforcedLeray.Short.PartIIa.PepsC p.ε p.c z ∈
      UnforcedLeray.Short.PartIIa.solenoidalHC p.ε p.c :=
    Submodule.starProjection_apply_mem _ _
  obtain ⟨b, hbdef⟩ : ∃ b : HSpace p.c Merid,
      b = Body.merReL.compLp (UnforcedLeray.Short.PartIIa.PepsC p.ε p.c z) := ⟨_, rfl⟩
  have hb_coe : ∀ᵐ q ∂(measureH p.c), b q =
      Body.merReL (UnforcedLeray.Short.PartIIa.PepsC p.ε p.c z q) := by
    rw [hbdef]
    exact ContinuousLinearMap.coeFn_compLp _ _
  have hb_ae : (b : Profile → Merid) =ᵐ[measureH p.c] fun q => wk (cellPt p.c q) := by
    filter_upwards [hb_coe, hwk'] with q h1 h2
    rw [h1, h2, pepsRealMember_merReL_merC]
  have hGb : (UnforcedLeray.Short.PartIIa.PepsC p.ε p.c z : Profile → MeridC) =ᵐ[measureH p.c]
      fun q => merC (b q) := by
    filter_upwards [hb_ae, hwk'] with q h1 h2
    rw [h2, h1]
  refine ⟨b, ?_, hb_ae⟩
  rw [UnforcedLeray.B0226.mem_solenoidalH_iff]
  intro Φ
  have hO := (Submodule.mem_orthogonal _ _).1 hG
  have hgen := hO _ (Submodule.subset_span ⟨Φ, pepsRealMember_memLp_cgrad p.ε Φ, rfl⟩)
  rw [L2.inner_def] at hgen
  have hint : (∫ q, ((b q 0 * UnforcedLeray.B0226.Deps p.ε Φ.1 q +
      b q 1 * Axi.dEta Φ.1 q : ℝ) : ℂ) ∂measureH p.c) = 0 := by
    rw [← hgen]
    apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp (pepsRealMember_memLp_cgrad p.ε Φ), hGb] with q hq1 hq2
    rw [hq1, hq2]
    simp [PiLp.inner_apply, UnforcedLeray.Short.PartIIa.cgrad, merC, Fin.sum_univ_two]
  rw [integral_complex_ofReal] at hint
  exact Complex.ofReal_eq_zero.mp hint

end UnforcedLeray.Short.PartIIIb.NearInst
