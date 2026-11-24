import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Lemmas
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2.L3
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2.L4
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2.L5
import UnforcedLeray.Short.PartIIIa.T15_SepKernelBounds
import UnforcedLeray.Short.PartIIIa.Compose

/-!
# `PartIII-b:C/near/masked/15`: `farKernelLinear` from two source leaves

Source `the November 2 reference manuscript`
3905-3912 (masked `sep:resolvent`), 3604-3646.

For a box tensor `f` the masked lift `T_f(τ',z) = 1_{e^δ s < R²/|z'|²} 𝒩_T f` is a periodic
(period `2c/R`) measurable separated source supported in `|z'| ≤ R e^{-δ/2}/√s`, bounded with
bounded `z`-support (so with finite `L²_τL²_z` moment).  Given the two leaves
`MaskedLiftSource`, `MaskedLiftMoment`, the proved `sepPhiMeasurable`, `sepGapPointwise`,
`sepGapMajorantIntegrable` give integrability of the integrand `sepPhi`, and linearity of
`sepW` in the source follows termwise.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Short.PartIIIb.NearInst.Delta
  UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint.Planar

/-- The masked lift of a chart tensor at output age `s` (the source in `sepWfar`). -/
def maskedLift (R c δ s : ℝ) (f : Chart → Ten3) : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ :=
  fun τ' z => if Real.exp δ * s < R ^ 2 / (z 0 ^ 2 + z 1 ^ 2) then cartLift R c f τ' z else 0

/-- Leaf 1 (source 3905-3912, 3604-3610): for a box tensor `f` the masked lift is a measurable
`2c/R`-periodic separated source supported in `|z'| ≤ R e^{-δ/2}/√s` (the mask keeps only
`R²/|z'|² > e^δ s`; `chartOf` shifts `τ` by `2c/R` exactly when `q` shifts by `c`;
`f` measurable, `chartOf`, `cylFrame`, `nsSym` measurable). -/
def MaskedLiftSource : Prop :=
  ∀ (R c δ s : ℝ), 0 < R → 0 < c → 0 < δ → 0 < s → ∀ f : Chart → Ten3, IsBoxTensor f →
    UnforcedLeray.Short.IIIa.IsSepSource (2 * c / R) (R * Real.exp (-δ / 2) / Real.sqrt s)
      (maskedLift R c δ s f)

/-- Leaf 2 (source 3905-3912, 4155-4156): finite `L²_τL²_z` moment of the masked lift of a box
tensor (`‖T_f‖ ≤ B·s₂·C`, `f ≠ 0` only for age in `[s₁,s₂]`, `|η| ≤ L`, so `T_f(τ',z) = 0` unless
`R/√s₂ ≤ |z'| ≤ R/√s₁`, `|z₃| ≤ L|z'|/R`: bounded with bounded `z`-support). -/
def MaskedLiftMoment : Prop :=
  ∀ (R c δ s : ℝ), 0 < R → 0 < c → 0 < δ → 0 < s → ∀ f : Chart → Ten3, IsBoxTensor f →
    SepMoment (2 * c / R) (maskedLift R c δ s f)

theorem maskedSepPhi_integrable (h1 : MaskedLiftSource) (h2 : MaskedLiftMoment)
    (R c δ s ν μ : ℝ) (hR : 0 < R) (hc : 0 < c) (hδ : 0 < δ) (hs : 0 < s) (hν : 0 < ν)
    (hμ : -(1 / 4) < μ) (f : Chart → Ten3) (hf : IsBoxTensor f) (y : Space)
    (hy : R * Real.exp (-δ / 2) / Real.sqrt s < hRad y) (τ : ℝ) (i : Fin 3) :
    Integrable (fun p => sepPhi ν (μ : ℂ) (maskedLift R c δ s f) τ i p y) sepRho := by
  have hP : 0 < 2 * c / R := by positivity
  have hr : 0 ≤ R * Real.exp (-δ / 2) / Real.sqrt s := by positivity
  have hS := h1 R c δ s hR hc hδ hs f hf
  have hM := h2 R c δ s hR hc hδ hs f hf
  have hμ' : -(1 / 4) < (μ : ℂ).re := by simpa using hμ
  obtain ⟨ε, hε, C, hC0, hb⟩ := sepGapPointwise UnforcedLeray.Short.IIIa.sepKernelBounds ν
    (μ : ℂ) _ _ _ hν hμ' hr hP hS τ i y hy
  have hint := (sepGapMajorantIntegrable (μ : ℂ) _ _ _ hμ' hP hS hM τ 0 (by norm_num)).const_mul C
  have hmeas := sepPhiMeasurable ν (μ : ℂ) _ _ _ hν hS τ i 0 (by norm_num) y
  have hmeas' : AEStronglyMeasurable (fun p => sepPhi ν (μ : ℂ) (maskedLift R c δ s f) τ i p y)
      sepRho := by
    have := (continuousMultilinearCurryFin0 ℝ Space ℂ).continuous.comp_aestronglyMeasurable hmeas
    refine this.congr (Filter.Eventually.of_forall fun p => ?_)
    simp [iteratedFDeriv_zero_eq_comp]
  refine hint.mono' hmeas' ?_
  filter_upwards [ae_mem_Ioo_sepRho] with p hp
  have := hb y (Metric.mem_ball_self hε) p.1 hp p.2 0 (by norm_num)
  simpa [norm_iteratedFDeriv_zero] using this

theorem sepPhi_add_smul (ν : ℝ) (μ : ℂ) (T1 T2 : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (a : ℝ)
    (τ : ℝ) (i : Fin 3) (p : ℝ × Space) (y : Space) :
    sepPhi ν μ (fun τ' z => T1 τ' z + a • T2 τ' z) τ i p y =
      sepPhi ν μ T1 τ i p y + a • sepPhi ν μ T2 τ i p y := by
  unfold sepPhi
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Complex.real_smul]
  push_cast
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  refine congrArg₂ _ rfl ?_
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem nsSym_add_smul (a : ℝ) (T1 T2 : Ten3) :
    nsSym (T1 + a • T2) = nsSym T1 + a • nsSym T2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [nsSym, symRZ] <;> ring

theorem maskedLift_add_smul (R c δ s a : ℝ) (f g : Chart → Ten3) :
    maskedLift R c δ s (f + a • g) =
      fun τ' z => maskedLift R c δ s f τ' z + a • maskedLift R c δ s g τ' z := by
  funext τ' z
  unfold maskedLift cartLift
  split_ifs
  · have : (f + a • g) (chartOf R c z τ') = f (chartOf R c z τ') + a • g (chartOf R c z τ') := rfl
    rw [this, nsSym_add_smul, smul_add, smul_comm (chartOf R c z τ').1 a, Matrix.mul_add,
      Matrix.add_mul]
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_comm a]
  · simp

theorem hRad_chartY (R : ℝ) (hR : 0 < R) (x : Chart) (hs : 0 < x.1) :
    hRad (chartY R x) = R / Real.sqrt x.1 := by
  have : 0 < Real.sqrt x.1 := Real.sqrt_pos.2 hs
  unfold hRad chartY
  simp only [PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  rw [show (R / Real.sqrt x.1) ^ 2 + 0 ^ 2 = (R / Real.sqrt x.1) ^ 2 by ring]
  exact Real.sqrt_sq (by positivity)

theorem sepWfar_add_smul (h1 : MaskedLiftSource) (h2 : MaskedLiftMoment)
    (R c δ s ν μ : ℝ) (hR : 0 < R) (hc : 0 < c) (hδ : 0 < δ) (hs : 0 < s) (hν : 0 < ν)
    (hμ : -(1 / 4) < μ) (f g : Chart → Ten3) (hf : IsBoxTensor f) (hg : IsBoxTensor g) (a : ℝ)
    (y : Space) (hy : R * Real.exp (-δ / 2) / Real.sqrt s < hRad y) (τ : ℝ) :
    sepWfar ν (μ : ℂ) R δ s (cartLift R c (f + a • g)) y τ =
      sepWfar ν (μ : ℂ) R δ s (cartLift R c f) y τ +
        a • sepWfar ν (μ : ℂ) R δ s (cartLift R c g) y τ := by
  funext i
  have e : ∀ F : Chart → Ten3, sepWfar ν (μ : ℂ) R δ s (cartLift R c F) y τ =
      UnforcedLeray.Short.IIIa.sepW ν (μ : ℂ) (maskedLift R c δ s F) y τ := fun F => rfl
  have i1 := maskedSepPhi_integrable h1 h2 R c δ s ν μ hR hc hδ hs hν hμ f hf y hy τ i
  have i2 := maskedSepPhi_integrable h1 h2 R c δ s ν μ hR hc hδ hs hν hμ g hg y hy τ i
  have hsum : (fun p => sepPhi ν (μ : ℂ) (maskedLift R c δ s (f + a • g)) τ i p y) =
      fun p => sepPhi ν (μ : ℂ) (maskedLift R c δ s f) τ i p y +
        a • sepPhi ν (μ : ℂ) (maskedLift R c δ s g) τ i p y := by
    funext p
    rw [maskedLift_add_smul, sepPhi_add_smul]
  have i3 : Integrable (fun p => sepPhi ν (μ : ℂ) (maskedLift R c δ s (f + a • g)) τ i p y)
      sepRho := by
    rw [hsum]; exact i1.add (i2.smul a)
  simp only [Pi.add_apply, Pi.smul_apply, e]
  rw [sepW_eq_integral ν _ _ τ i y i3, sepW_eq_integral ν _ _ τ i y i1,
    sepW_eq_integral ν _ _ τ i y i2, hsum]
  refine (integral_add i1 (i2.smul a)).trans ?_
  congr 1
  exact integral_smul a (fun p => sepPhi ν (μ : ℂ) (maskedLift R c δ s g) τ i p y)

theorem merRe_neg_add_smul (u v : Fin 3 → ℂ) (a : ℝ) :
    merRe (-(u + a • v)) = merRe (-u) + a • merRe (-v) := by
  ext i
  fin_cases i <;> simp [merRe] <;> ring

theorem farKernelLinear_of (h1 : MaskedLiftSource) (h2 : MaskedLiftMoment) : FarKernelLinear := by
  intro R c ν δ S μ hR hc hν hδ hS hμ f g hf hg a
  filter_upwards [UnforcedLeray.Short.IIIa.ae_pos_ageμ c (-3 / 2)] with x hx
  by_cases hxS : x.1 < S
  · have hgap : R * Real.exp (-δ / 2) / Real.sqrt x.1 < hRad (chartY R x) := by
      rw [hRad_chartY R hR x hx]
      have hq : 0 < Real.sqrt x.1 := Real.sqrt_pos.2 hx
      have he : Real.exp (-δ / 2) < 1 := by rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 (by linarith)
      exact div_lt_div_of_pos_right (by nlinarith) hq
    simp only [farOut, hxS, ite_true, Pi.add_apply, Pi.smul_apply]
    rw [sepWfar_add_smul h1 h2 R c δ x.1 ν μ hR hc hδ hx hν hμ f g hf hg a _ hgap,
      merRe_neg_add_smul, smul_add, smul_comm (Real.sqrt x.1)⁻¹ a]
  · simp [farOut, hxS]

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
