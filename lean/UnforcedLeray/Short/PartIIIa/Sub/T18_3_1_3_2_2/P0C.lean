import UnforcedLeray.Short.PartIIIa.Sub.T18_3_1_3_2_2.Props
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.NiceForceSolution.LerayProjectSlices.TestBridge
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.LionsMagenesCyl.MollLimit.SmoothWeak
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-!
# Part III-a, `PartIII-a:T18/3/1/3/2/2/org`: `𝒫₀` on `L²(cell; ℂ²)`

Source of record: `the November 2 reference manuscript` lines 3427-3440.
The pairing `LMIp` is written through the real `L²(cell; ℝ²)` inner products (`lmIp_cplxOf`), and
`lmP0CAdj`, `lmP0CFix`, `lmP0CContr` follow from `Cyl.inner_P0_comm`, `Cyl.P0_eq_self`,
`Cyl.norm_P0_le`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.IIIa

open UnforcedLeray.Cyl (L2v Vec2 cellμ)

theorem lm_reVec_memLp {c : ℝ} {f : LMSpField} (hf : LMCellL2 c f) :
    MemLp (reVec f) 2 (cellμ c) := by
  rw [cellμ_eq, memLp_piLp_iff]
  intro i
  fin_cases i
  · exact (hf 0).re
  · exact (hf 1).re

theorem lm_imVec_memLp {c : ℝ} {f : LMSpField} (hf : LMCellL2 c f) :
    MemLp (imVec f) 2 (cellμ c) := by
  rw [cellμ_eq, memLp_piLp_iff]
  intro i
  fin_cases i
  · exact (hf 0).im
  · exact (hf 1).im

/-- The class of `reVec f` represents it. -/
theorem lm_toL2v_ae {c : ℝ} {g : ℝ × ℝ → Vec2} (hg : MemLp g 2 (cellμ c)) :
    (toL2v c g : ℝ × ℝ → Vec2) =ᵐ[cellμ c] g := by
  unfold toL2v
  rw [dif_pos hg]
  exact hg.coeFn_toLp

/-- An `L²` field is a.e. `cplxOf` of the classes of its real and imaginary parts. -/
theorem lm_cplxOf_ae {c : ℝ} {f : LMSpField} (hf : LMCellL2 c f) :
    ∀ᵐ x ∂(volume.restrict (B0579.cell c)), ∀ i : Fin 2,
      f x i = cplxOf c (toL2v c (reVec f)) (toL2v c (imVec f)) x i := by
  rw [← cellμ_eq c]
  filter_upwards [lm_toL2v_ae (lm_reVec_memLp hf), lm_toL2v_ae (lm_imVec_memLp hf)] with x h1 h2 i
  simp only [cplxOf, h1, h2]
  have hr : reVec f x i = (f x i).re := by fin_cases i <;> rfl
  have him : imVec f x i = (f x i).im := by fin_cases i <;> rfl
  rw [hr, him]
  apply Complex.ext <;> simp

/-- **The pairing through the real inner products.** -/
theorem lmIp_cplxOf (c : ℝ) (a₁ a₂ b₁ b₂ : L2v c) :
    LMIp c (cplxOf c a₁ a₂) (cplxOf c b₁ b₂) =
      ((⟪a₁, b₁⟫_ℝ + ⟪a₂, b₂⟫_ℝ : ℝ) : ℂ) + Complex.I * ((⟪a₁, b₂⟫_ℝ - ⟪a₂, b₁⟫_ℝ : ℝ) : ℂ) := by
  have hpt : ∀ x : ℝ × ℝ, ∑ i : Fin 2, starRingEnd ℂ (cplxOf c a₁ a₂ x i) * cplxOf c b₁ b₂ x i =
      ((⟪(a₁ : ℝ × ℝ → Vec2) x, (b₁ : ℝ × ℝ → Vec2) x⟫_ℝ +
          ⟪(a₂ : ℝ × ℝ → Vec2) x, (b₂ : ℝ × ℝ → Vec2) x⟫_ℝ : ℝ) : ℂ) +
        Complex.I * ((⟪(a₁ : ℝ × ℝ → Vec2) x, (b₂ : ℝ × ℝ → Vec2) x⟫_ℝ -
          ⟪(a₂ : ℝ × ℝ → Vec2) x, (b₁ : ℝ × ℝ → Vec2) x⟫_ℝ : ℝ) : ℂ) := by
    intro x
    simp only [PiLp.inner_apply, Fin.sum_univ_two, cplxOf, RCLike.inner_apply, conj_trivial, map_add,
      map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring_nf
    simp only [Complex.I_sq]
    ring
  have h11 := L2.integrable_inner (𝕜 := ℝ) a₁ b₁
  have h22 := L2.integrable_inner (𝕜 := ℝ) a₂ b₂
  have h12 := L2.integrable_inner (𝕜 := ℝ) a₁ b₂
  have h21 := L2.integrable_inner (𝕜 := ℝ) a₂ b₁
  unfold LMIp
  rw [← cellμ_eq c, integral_congr_ae (ae_of_all _ hpt), integral_add, integral_const_mul,
    integral_complex_ofReal, integral_complex_ofReal, integral_add h11 h22, integral_sub h12 h21,
    ← L2.inner_def, ← L2.inner_def, ← L2.inner_def, ← L2.inner_def]
  · exact (h11.add h22).ofReal
  · exact ((h12.sub h21).ofReal).const_mul _

/-- **`𝒫₀` is self-adjoint on `L²(cell; ℂ²)`.** -/
theorem lmP0CAdj : LMP0CAdj := by
  intro c _hc f g hf hg
  have e1 : LMIp c (P0C c f) g = LMIp c (P0C c f)
      (cplxOf c (toL2v c (reVec g)) (toL2v c (imVec g))) := lmIp_congr_right (lm_cplxOf_ae hg)
  have e2 : LMIp c f (P0C c g) = LMIp c (cplxOf c (toL2v c (reVec f)) (toL2v c (imVec f)))
      (P0C c g) := lmIp_congr_left (lm_cplxOf_ae hf)
  rw [e1, e2]
  simp only [P0C, P0re, P0im]
  rw [lmIp_cplxOf, lmIp_cplxOf]
  simp only [UnforcedLeray.Cyl.inner_P0_comm]

/-- **`𝒫₀ g = g` for weakly divergence-free `g`.** -/
theorem lmP0CFix : LMP0CFix := by
  intro c hc g hg hd
  have hRe : toL2v c (reVec g) ∈ UnforcedLeray.Cyl.divFree c ∧
      toL2v c (imVec g) ∈ UnforcedLeray.Cyl.divFree c := by
    have key : ∀ (φ : ℝ × ℝ → ℝ) (_ : UnforcedLeray.Sob.IsCylTest c φ),
        ⟪UnforcedLeray.Cyl.gradL ‹_›, toL2v c (reVec g)⟫_ℝ = 0 ∧
          ⟪UnforcedLeray.Cyl.gradL ‹_›, toL2v c (imVec g)⟫_ℝ = 0 := by
      intro φ hφ
      have hB : B0579.IsCylTest c φ := (testBridge c φ).1.mpr hφ
      have hpd := (testBridge c φ).2 hB
      have hint : ∀ j : Fin 2, Integrable (fun x => g x j * (B0579.pd j φ x : ℂ))
          (volume.restrict (B0579.cell c)) := fun j => by
        obtain ⟨R', hR'⟩ := (hB.pd j).band
        exact lmSW_integrableOn (R := R') (hg j)
          (Complex.continuous_ofReal.comp (hB.pd j).continuous) (fun x hx => by simp [hR' x hx])
      have h0 := hd φ hB
      rw [integral_add (hint 0) (hint 1)] at h0
      have hrep : ∀ a : ℝ × ℝ → Vec2, MemLp a 2 (cellμ c) →
          ⟪UnforcedLeray.Cyl.gradL hφ, toL2v c a⟫_ℝ =
            ∫ x in B0579.cell c, (a x 0 * B0579.pd 0 φ x + a x 1 * B0579.pd 1 φ x) := by
        intro a ha
        rw [L2.inner_def, ← cellμ_eq c]
        refine integral_congr_ae ?_
        filter_upwards [(UnforcedLeray.Cyl.memLp_gradT hφ).coeFn_toLp, lm_toL2v_ae ha] with x h1 h2
        have h1' : UnforcedLeray.Cyl.gradL hφ x = UnforcedLeray.Cyl.gradT φ x := h1
        rw [h1', h2, real_inner_comm, UnforcedLeray.Cyl.gradT, UnforcedLeray.Cyl.inner_vec,
          (hpd x).1, (hpd x).2]
      have hre : ∀ j : Fin 2, Integrable (fun x => (g x j).re * B0579.pd j φ x)
          (volume.restrict (B0579.cell c)) := fun j => by
        have := (hint j).re
        simpa using this
      have him : ∀ j : Fin 2, Integrable (fun x => (g x j).im * B0579.pd j φ x)
          (volume.restrict (B0579.cell c)) := fun j => by
        have := (hint j).im
        simpa using this
      have hr : ∀ j : Fin 2, ∫ x in B0579.cell c, (g x j).re * B0579.pd j φ x =
          (∫ x in B0579.cell c, g x j * (B0579.pd j φ x : ℂ)).re := fun j => by
        have := integral_re (hint j)
        simpa using this
      have hi : ∀ j : Fin 2, ∫ x in B0579.cell c, (g x j).im * B0579.pd j φ x =
          (∫ x in B0579.cell c, g x j * (B0579.pd j φ x : ℂ)).im := fun j => by
        have := integral_im (hint j)
        simpa using this
      constructor
      · rw [hrep _ (lm_reVec_memLp hg)]
        show ∫ x in B0579.cell c, ((g x 0).re * B0579.pd 0 φ x + (g x 1).re * B0579.pd 1 φ x) = 0
        rw [integral_add (hre 0) (hre 1), hr 0, hr 1, ← Complex.add_re, h0, Complex.zero_re]
      · rw [hrep _ (lm_imVec_memLp hg)]
        show ∫ x in B0579.cell c, ((g x 0).im * B0579.pd 0 φ x + (g x 1).im * B0579.pd 1 φ x) = 0
        rw [integral_add (him 0) (him 1), hi 0, hi 1, ← Complex.add_im, h0, Complex.zero_im]
    exact ⟨UnforcedLeray.Cyl.mem_divFree.2 fun φ hφ => (key φ hφ).1,
      UnforcedLeray.Cyl.mem_divFree.2 fun φ hφ => (key φ hφ).2⟩
  filter_upwards [lm_cplxOf_ae hg] with x hx i
  rw [hx i]
  simp only [P0C, P0re, P0im, UnforcedLeray.Cyl.P0_eq_self hRe.1, UnforcedLeray.Cyl.P0_eq_self hRe.2]

/-- The cell norm of `cplxOf` through the `L²` norms. -/
theorem lm_cplxOf_norm (c : ℝ) (a₁ a₂ : L2v c) :
    ∫ x in B0579.cell c, ∑ i : Fin 2, ‖cplxOf c a₁ a₂ x i‖ ^ 2 = ‖a₁‖ ^ 2 + ‖a₂‖ ^ 2 := by
  have h := lmIp_cplxOf c a₁ a₂ a₁ a₂
  rw [lmIp_self, real_inner_comm a₁ a₂, sub_self, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq] at h
  have h2 : ∫ x in B0579.cell c, vnorm2 (cplxOf c a₁ a₂ x) ^ 2 = ‖a₁‖ ^ 2 + ‖a₂‖ ^ 2 := by
    have h' : ((∫ x in B0579.cell c, vnorm2 (cplxOf c a₁ a₂ x) ^ 2 : ℝ) : ℂ) =
        ((‖a₁‖ ^ 2 + ‖a₂‖ ^ 2 : ℝ) : ℂ) := by
      rw [h]
      simp
    exact Complex.ofReal_inj.1 h'
  rw [← h2]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  exact (Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)).symm

/-- **`𝒫₀` is an `L²` contraction.** -/
theorem lmP0CContr : LMP0CContr := by
  intro c _hc f hf
  have e : ∫ x in B0579.cell c, ∑ i : Fin 2, ‖f x i‖ ^ 2 =
      ‖toL2v c (reVec f)‖ ^ 2 + ‖toL2v c (imVec f)‖ ^ 2 := by
    rw [← lm_cplxOf_norm]
    refine integral_congr_ae ?_
    filter_upwards [lm_cplxOf_ae hf] with x hx
    exact Finset.sum_congr rfl fun i _ => by rw [hx i]
  rw [e]
  show ∫ x in B0579.cell c, ∑ i : Fin 2, ‖cplxOf c (P0re c f) (P0im c f) x i‖ ^ 2 ≤ _
  rw [lm_cplxOf_norm]
  have hle : ∀ a : L2v c, ‖UnforcedLeray.Cyl.P0 c a‖ ≤ ‖a‖ := fun a =>
    ((UnforcedLeray.Cyl.P0 c).le_opNorm a).trans
      (by nlinarith [UnforcedLeray.Cyl.norm_P0_le (c := c), norm_nonneg a])
  have h1 := pow_le_pow_left₀ (norm_nonneg _) (hle (toL2v c (reVec f))) 2
  have h2 := pow_le_pow_left₀ (norm_nonneg _) (hle (toL2v c (imVec f))) 2
  exact add_le_add h1 h2

end UnforcedLeray.Short.IIIa
