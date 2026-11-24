import UnforcedLeray.Short.PartIIIa.Sub.T18_2_4_2
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.NiceForceSolution.LerayProjectSlices.TestBridge

/-!
# Part III-a, leaf `PartIII-a:T18/2/4/2/5`: `𝒫₀ f - f` is orthogonal to divergence-free fields

Target (`Sub/T18_2_4_2.lean`): `P0OrthC`. Source of record:
`the November 2 reference manuscript`, lines 3442-3465.

Proof: for a divergence-free test field `Ψ` (`IsDivFreeTestField`), the class `Ψc` of
`Ψ' x = (Ψ x 0, Ψ x 1)` is in `divFree c` (integration by parts, `B0579.integral_mul_pd`, and
the pointwise divergence-free identity). Since `g - 𝒫₀ g ∈ (divFree c)ᗮ` (`Cyl.sub_P0_mem_orthogonal`),
the real pairing `∫ ⟪Ψc, g - 𝒫₀ g⟫` vanishes. The complex integrand is the real part plus `i` times
the imaginary part, and each part is the real pairing above.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.IIIa

/-- `⟪vec (Ψ p₀) (Ψ p₁), w⟫ = w₀ Ψ p₀ + w₁ Ψ p₁`. -/
theorem inner_psi_aux_p0orth (Ψ : ℝ × ℝ → Fin 2 → ℝ) (p : ℝ × ℝ) (w : UnforcedLeray.Cyl.Vec2) :
    ⟪UnforcedLeray.Cyl.vec (Ψ p 0) (Ψ p 1), w⟫_ℝ = w 0 * Ψ p 0 + w 1 * Ψ p 1 := by
  rw [real_inner_comm _ _, UnforcedLeray.Cyl.inner_vec]

/-- `⟪gradT ψ z, w⟫ = w₀ ∂_q ψ + w₁ ∂_η ψ` (same as in `P0DivFreeC`). -/
theorem inner_gradT_aux_p0orth (ψ : ℝ × ℝ → ℝ) (z : ℝ × ℝ) (w : UnforcedLeray.Cyl.Vec2) :
    ⟪UnforcedLeray.Cyl.gradT ψ z, w⟫_ℝ =
      w 0 * UnforcedLeray.Cyl.partialQ ψ z + w 1 * UnforcedLeray.Cyl.partialEta ψ z := by
  rw [real_inner_comm _ _]
  unfold UnforcedLeray.Cyl.gradT
  rw [UnforcedLeray.Cyl.inner_vec]

/-- The integral of `Ψ · ∇φ` over the cell vanishes for a divergence-free test field `Ψ`. -/
theorem div_zero_aux_p0orth (c : ℝ) (Ψ : ℝ × ℝ → Fin 2 → ℝ) (hΨ : IsDivFreeTestField c Ψ)
    (φ : ℝ × ℝ → ℝ) (hφ : B0579.IsCylTest c φ) :
    ∫ x in B0579.cell c, (Ψ x 0 * B0579.pd 0 φ x + Ψ x 1 * B0579.pd 1 φ x) = 0 := by
  have hΨ0 : B0579.IsCylTest c (fun x => Ψ x 0) := hΨ.1 0
  have hΨ1 : B0579.IsCylTest c (fun x => Ψ x 1) := hΨ.1 1
  have e0 : ∫ x in B0579.cell c, Ψ x 0 * B0579.pd 0 φ x =
      -∫ x in B0579.cell c, B0579.pd 0 (fun y => Ψ y 0) x * φ x :=
    B0579.integral_mul_pd hΨ0 hφ 0
  have e1 : ∫ x in B0579.cell c, Ψ x 1 * B0579.pd 1 φ x =
      -∫ x in B0579.cell c, B0579.pd 1 (fun y => Ψ y 1) x * φ x :=
    B0579.integral_mul_pd hΨ1 hφ 1
  have hdiv : ∀ x, B0579.pd 0 (fun y => Ψ y 0) x * φ x +
      B0579.pd 1 (fun y => Ψ y 1) x * φ x = 0 := fun x => by
    rw [← add_mul, hΨ.2 x, zero_mul]
  have hsum : ∫ x in B0579.cell c, (B0579.pd 0 (fun y => Ψ y 0) x * φ x +
      B0579.pd 1 (fun y => Ψ y 1) x * φ x) = 0 := by
    simp only [hdiv, integral_zero]
  have i2 : IntegrableOn (fun x => B0579.pd 0 (fun y => Ψ y 0) x * φ x) (B0579.cell c) :=
    ((hΨ0.pd 0).mul hφ).integrableOn
  have i3 : IntegrableOn (fun x => B0579.pd 1 (fun y => Ψ y 1) x * φ x) (B0579.cell c) :=
    ((hΨ1.pd 1).mul hφ).integrableOn
  have i0 : IntegrableOn (fun x => Ψ x 0 * B0579.pd 0 φ x) (B0579.cell c) :=
    (hΨ0.mul (hφ.pd 0)).integrableOn
  have i1 : IntegrableOn (fun x => Ψ x 1 * B0579.pd 1 φ x) (B0579.cell c) :=
    (hΨ1.mul (hφ.pd 1)).integrableOn
  have hs := integral_add i0 i1
  have hs2 := integral_add i2 i3
  linarith [e0, e1, hsum, hs, hs2]

/-- The class of `Ψ' = (Ψ₀, Ψ₁)` lies in `divFree c` (given that it is in `L²(cell)`). -/
theorem psi_mem_divFree_aux_p0orth (c : ℝ) (Ψ : ℝ × ℝ → Fin 2 → ℝ) (hΨ : IsDivFreeTestField c Ψ)
    (hL : MemLp (fun z : ℝ × ℝ => UnforcedLeray.Cyl.vec (Ψ z 0) (Ψ z 1)) 2
      (UnforcedLeray.Cyl.cellμ c)) :
    hL.toLp (fun z : ℝ × ℝ => UnforcedLeray.Cyl.vec (Ψ z 0) (Ψ z 1)) ∈
      UnforcedLeray.Cyl.divFree c := by
  rw [UnforcedLeray.Cyl.mem_divFree]
  intro φ hφ
  have hB : B0579.IsCylTest c φ := (testBridge c φ).1.mpr hφ
  have hpd := (testBridge c φ).2 hB
  rw [L2.inner_def]
  have hae : (fun a => ⟪UnforcedLeray.Cyl.gradL hφ a,
        hL.toLp (fun z : ℝ × ℝ => UnforcedLeray.Cyl.vec (Ψ z 0) (Ψ z 1)) a⟫_ℝ) =ᵐ[
        UnforcedLeray.Cyl.cellμ c]
      fun a => Ψ a 0 * B0579.pd 0 φ a + Ψ a 1 * B0579.pd 1 φ a := by
    filter_upwards [(UnforcedLeray.Cyl.memLp_gradT hφ).coeFn_toLp, hL.coeFn_toLp] with a hx hy
    have hx' : UnforcedLeray.Cyl.gradL hφ a = UnforcedLeray.Cyl.gradT φ a := hx
    rw [hx', hy]
    simp only [inner_gradT_aux_p0orth, (hpd a).1, (hpd a).2, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons]
  refine (integral_congr_ae hae).trans ?_
  rw [cellμ_eq c]
  exact div_zero_aux_p0orth c Ψ hΨ φ hB

/-- The real pairing `∫ Σ_i (𝒫₀ F_i - F_i) Ψ_i` vanishes, and it is integrable. -/
theorem orth_real_aux_p0orth (c : ℝ) (F : ℝ × ℝ → UnforcedLeray.Cyl.Vec2)
    (hF : MemLp F 2 (UnforcedLeray.Cyl.cellμ c)) (Ψ : ℝ × ℝ → Fin 2 → ℝ)
    (hΨ : IsDivFreeTestField c Ψ) :
    Integrable (fun x : ℝ × ℝ => ∑ i : Fin 2,
        ((UnforcedLeray.Cyl.P0 c (toL2v c F) : ℝ × ℝ → UnforcedLeray.Cyl.Vec2) x i - F x i) *
          Ψ x i) (UnforcedLeray.Cyl.cellμ c) ∧
      ∫ x, ∑ i : Fin 2,
        ((UnforcedLeray.Cyl.P0 c (toL2v c F) : ℝ × ℝ → UnforcedLeray.Cyl.Vec2) x i - F x i) *
          Ψ x i ∂(UnforcedLeray.Cyl.cellμ c) = 0 := by
  have hcont : Continuous fun z : ℝ × ℝ => UnforcedLeray.Cyl.vec (Ψ z 0) (Ψ z 1) :=
    (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => by
      fin_cases i
      · exact (hΨ.1 0).continuous
      · exact (hΨ.1 1).continuous)
  have hvan : ∃ R : ℝ, UnforcedLeray.Cyl.VanishesOutside R
      (fun z : ℝ × ℝ => UnforcedLeray.Cyl.vec (Ψ z 0) (Ψ z 1)) := by
    obtain ⟨R0, h0⟩ := (hΨ.1 0).band
    obtain ⟨R1, h1⟩ := (hΨ.1 1).band
    refine ⟨max R0 R1, fun z hz => ?_⟩
    have e0 : Ψ z 0 = 0 := h0 z (lt_of_le_of_lt (le_max_left _ _) hz)
    have e1 : Ψ z 1 = 0 := h1 z (lt_of_le_of_lt (le_max_right _ _) hz)
    simp only [e0, e1]
    ext i
    fin_cases i <;> rfl
  obtain ⟨R, hR⟩ := hvan
  have hL : MemLp (fun z : ℝ × ℝ => UnforcedLeray.Cyl.vec (Ψ z 0) (Ψ z 1)) 2
      (UnforcedLeray.Cyl.cellμ c) :=
    UnforcedLeray.Cyl.memLp_of_vanishes hcont hR 2
  have hΨc := psi_mem_divFree_aux_p0orth c Ψ hΨ hL
  set Ψc := hL.toLp (fun z : ℝ × ℝ => UnforcedLeray.Cyl.vec (Ψ z 0) (Ψ z 1)) with hΨc_def
  have hO : ⟪Ψc, toL2v c F - UnforcedLeray.Cyl.P0 c (toL2v c F)⟫_ℝ = 0 :=
    (Submodule.mem_orthogonal _ _).1 (UnforcedLeray.Cyl.sub_P0_mem_orthogonal (toL2v c F)) Ψc hΨc
  have hg : (toL2v c F : ℝ × ℝ → UnforcedLeray.Cyl.Vec2) =ᵐ[UnforcedLeray.Cyl.cellμ c] F := by
    unfold toL2v
    rw [dif_pos hF]
    exact hF.coeFn_toLp
  have hpt : ∀ᵐ a ∂(UnforcedLeray.Cyl.cellμ c),
      ⟪Ψc a, (toL2v c F - UnforcedLeray.Cyl.P0 c (toL2v c F)) a⟫_ℝ =
        -∑ i : Fin 2, ((UnforcedLeray.Cyl.P0 c (toL2v c F) : ℝ × ℝ → UnforcedLeray.Cyl.Vec2) a i -
          F a i) * Ψ a i := by
    filter_upwards [hL.coeFn_toLp, Lp.coeFn_sub (toL2v c F) (UnforcedLeray.Cyl.P0 c (toL2v c F)),
      hg] with a h1 h2 h3
    have h1' : Ψc a = UnforcedLeray.Cyl.vec (Ψ a 0) (Ψ a 1) := h1
    rw [h1', h2, Pi.sub_apply, inner_psi_aux_p0orth, h3, Fin.sum_univ_two]
    simp only [PiLp.sub_apply]
    ring
  have hInt : Integrable (fun a => ⟪Ψc a, (toL2v c F - UnforcedLeray.Cyl.P0 c (toL2v c F)) a⟫_ℝ)
      (UnforcedLeray.Cyl.cellμ c) := L2.integrable_inner Ψc _
  have hInt2 := (hInt.congr hpt).neg
  have hI0 : ∫ a, ⟪Ψc a, (toL2v c F - UnforcedLeray.Cyl.P0 c (toL2v c F)) a⟫_ℝ
      ∂(UnforcedLeray.Cyl.cellμ c) = 0 := ((L2.inner_def _ _).symm).trans hO
  have hR2 : ∫ a, ∑ i : Fin 2,
        ((UnforcedLeray.Cyl.P0 c (toL2v c F) : ℝ × ℝ → UnforcedLeray.Cyl.Vec2) a i - F a i) *
          Ψ a i ∂(UnforcedLeray.Cyl.cellμ c) = 0 := by
    have h1 := integral_congr_ae hpt
    rw [integral_neg, hI0] at h1
    linarith
  refine ⟨?_, hR2⟩
  exact (hInt2.congr (Filter.Eventually.of_forall fun a => neg_neg _))

theorem reVec_apply_p0orth (f : ℝ × ℝ → Fin 2 → ℂ) (x : ℝ × ℝ) (i : Fin 2) :
    reVec f x i = (f x i).re := by
  fin_cases i <;> rfl

theorem imVec_apply_p0orth (f : ℝ × ℝ → Fin 2 → ℂ) (x : ℝ × ℝ) (i : Fin 2) :
    imVec f x i = (f x i).im := by
  fin_cases i <;> rfl

/-- The `ℂ²`-valued orthogonality of `𝒫₀ f - f` against divergence-free test fields. -/
theorem p0OrthC : UnforcedLeray.Short.IIIa.P0OrthC := by
  unfold UnforcedLeray.Short.IIIa.P0OrthC
  intro c _hc f hre him Ψ hΨ
  rw [← cellμ_eq c]
  obtain ⟨hI1, hZ1⟩ := orth_real_aux_p0orth c (reVec f) hre Ψ hΨ
  obtain ⟨hI2, hZ2⟩ := orth_real_aux_p0orth c (imVec f) him Ψ hΨ
  have hpt : ∀ x : ℝ × ℝ,
      ∑ i : Fin 2, (UnforcedLeray.Short.IIIa.P0C c f x i - f x i) * ((Ψ x i : ℝ) : ℂ) =
        ((∑ i : Fin 2, ((UnforcedLeray.Cyl.P0 c (toL2v c (reVec f)) :
            ℝ × ℝ → UnforcedLeray.Cyl.Vec2) x i - reVec f x i) * Ψ x i : ℝ) : ℂ) +
          Complex.I * ((∑ i : Fin 2, ((UnforcedLeray.Cyl.P0 c (toL2v c (imVec f)) :
            ℝ × ℝ → UnforcedLeray.Cyl.Vec2) x i - imVec f x i) * Ψ x i : ℝ) : ℂ) := by
    intro x
    have hf0 : f x 0 = ((f x 0).re : ℂ) + Complex.I * ((f x 0).im : ℂ) := by
      apply Complex.ext <;> simp
    have hf1 : f x 1 = ((f x 1).re : ℂ) + Complex.I * ((f x 1).im : ℂ) := by
      apply Complex.ext <;> simp
    simp only [Fin.sum_univ_two, UnforcedLeray.Short.IIIa.P0C, UnforcedLeray.Short.IIIa.cplxOf,
      UnforcedLeray.Short.IIIa.P0re, UnforcedLeray.Short.IIIa.P0im, reVec_apply_p0orth,
      imVec_apply_p0orth]
    push_cast
    linear_combination (-(Ψ x 0 : ℂ)) * hf0 + (-(Ψ x 1 : ℂ)) * hf1
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_add, integral_const_mul]
  · simp only [integral_complex_ofReal, hZ1, hZ2]
    simp
  all_goals first
    | exact Integrable.ofReal hI1
    | exact (Integrable.ofReal hI2).const_mul _

end UnforcedLeray.Short.IIIa
