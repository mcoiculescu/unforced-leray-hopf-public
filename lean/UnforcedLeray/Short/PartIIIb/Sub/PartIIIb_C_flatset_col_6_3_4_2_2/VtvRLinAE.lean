import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6_3_4_2_2
import UnforcedLeray.Short.PartIIIa.Clock.Existence.StripBookkeeping.LinFlowComb

/-!
# `VtvRLinAE`: a.e. linearity of `φ ↦ R(r,φ)` (source 4610)

Source of record: `the November 2 reference manuscript`
(line 4610, the integrated Duhamel identity `Y(s,φ) = ∫₀^s R(r,φ) dr`).

* `slice_ae`: Fubini on the age bands `[1/(n+1), n+1]`: for a.e. `r > 0`, `f(r,·) ∈ L²(cell)`.
* `gLin`: with `f(r,·) ∈ L²(cell)`, `φ ↦ ∫ (f₀ ∂_η φ - f₁ ∂_q φ)` is linear on cylinder tests.
* `fLin`: `φ ↦ ∫ flowIntegrand` is linear: `ω ψ_φ` is integrable (last clause, `ψ_φ = νΔφ + v·∇φ` is
  a cylinder test since `v` is smooth periodic), and `(u·∇E)φ` is integrable (`u ∈ L²`, `∇E φ` a
  cylinder test since `E = curl v` is smooth periodic).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.Short.IIIa (flowIntegrand lapP)

section CylAlg

variable {c : ℝ}

theorem cyl_add {φ ψ : ℝ × ℝ → ℝ} (hφ : B0579.IsCylTest c φ) (hψ : B0579.IsCylTest c ψ) :
    B0579.IsCylTest c (φ + ψ) where
  smooth := hφ.smooth.add hψ.smooth
  periodic x := by simp [hφ.periodic, hψ.periodic]
  band := by
    obtain ⟨R1, h1⟩ := hφ.band
    obtain ⟨R2, h2⟩ := hψ.band
    refine ⟨max R1 R2, fun x hx => ?_⟩
    simp [h1 x (lt_of_le_of_lt (le_max_left _ _) hx), h2 x (lt_of_le_of_lt (le_max_right _ _) hx)]

theorem cyl_smul (a : ℝ) {φ : ℝ × ℝ → ℝ} (hφ : B0579.IsCylTest c φ) :
    B0579.IsCylTest c (a • φ) where
  smooth := hφ.smooth.const_smul a
  periodic x := by simp [hφ.periodic]
  band := by
    obtain ⟨R1, h1⟩ := hφ.band
    exact ⟨R1, fun x hx => by simp [h1 x hx]⟩

theorem cyl_mul_sp {χ φ : ℝ × ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχp : ∀ x : ℝ × ℝ, χ (x.1 + c, x.2) = χ x) (hφ : B0579.IsCylTest c φ) :
    B0579.IsCylTest c (fun x => χ x * φ x) where
  smooth := hχ.mul hφ.smooth
  periodic x := by simp only [hχp, hφ.periodic]
  band := by
    obtain ⟨R1, h1⟩ := hφ.band
    exact ⟨R1, fun x hx => by simp [h1 x hx]⟩

theorem pd_add' (j : Fin 2) {φ ψ : ℝ × ℝ → ℝ} (hφ : Differentiable ℝ φ) (hψ : Differentiable ℝ ψ) :
    B0579.pd j (φ + ψ) = B0579.pd j φ + B0579.pd j ψ := by
  funext x
  have h : fderiv ℝ (φ + ψ) x = fderiv ℝ φ x + fderiv ℝ ψ x := fderiv_add (hφ x) (hψ x)
  simp [B0579.pd, h]

theorem pd_smul' (j : Fin 2) (a : ℝ) {φ : ℝ × ℝ → ℝ} (hφ : Differentiable ℝ φ) :
    B0579.pd j (a • φ) = a • B0579.pd j φ := by
  funext x
  have h : fderiv ℝ (a • φ) x = a • fderiv ℝ φ x := fderiv_const_smul (hφ x) a
  simp [B0579.pd, h]

theorem pd_add2 (i j : Fin 2) {φ ψ : ℝ × ℝ → ℝ} (hφ : B0579.IsCylTest c φ)
    (hψ : B0579.IsCylTest c ψ) :
    B0579.pd i (B0579.pd j (φ + ψ)) = B0579.pd i (B0579.pd j φ) + B0579.pd i (B0579.pd j ψ) := by
  rw [pd_add' j hφ.differentiable hψ.differentiable,
    pd_add' i (hφ.pd j).differentiable (hψ.pd j).differentiable]

theorem pd_smul2 (i j : Fin 2) (a : ℝ) {φ : ℝ × ℝ → ℝ} (hφ : B0579.IsCylTest c φ) :
    B0579.pd i (B0579.pd j (a • φ)) = a • B0579.pd i (B0579.pd j φ) := by
  rw [pd_smul' j a hφ.differentiable, pd_smul' i a (hφ.pd j).differentiable]

end CylAlg

/-! ### Fubini: a.e. slice of the force is in `L²(cell)` -/

theorem slice_band_ae {s₁ s₂ c : ℝ} {f : ℝ × (ℝ × ℝ) → Fin 2 → ℂ}
    (hf : ∀ i, MemLp (fun p => f p i) 2 (volume.restrict (Icc s₁ s₂ ×ˢ B0579.cell c))) :
    ∀ᵐ r ∂(volume.restrict (Icc s₁ s₂)),
      ∀ i, MemLp (fun x => f (r, x) i) 2 (volume.restrict (B0579.cell c)) := by
  rw [ae_all_iff]
  intro i
  have h := hf i
  have e : (volume : Measure (ℝ × (ℝ × ℝ))).restrict (Icc s₁ s₂ ×ˢ B0579.cell c) =
      (volume.restrict (Icc s₁ s₂)).prod (volume.restrict (B0579.cell c)) := by
    rw [Measure.volume_eq_prod, Measure.prod_restrict]
  rw [e] at h
  have hm := h.aestronglyMeasurable
  have hint := (memLp_two_iff_integrable_sq_norm hm).1 h
  have h1 := hint.prod_right_ae
  have h2 := hm.prodMk_left
  filter_upwards [h1, h2] with r a b
  exact (memLp_two_iff_integrable_sq_norm b).2 a

theorem slice_ae {c : ℝ} {f : ℝ × (ℝ × ℝ) → Fin 2 → ℂ}
    (hf : ∀ s₁ s₂ : ℝ, 0 < s₁ → ∀ i,
      MemLp (fun p => f p i) 2 (volume.restrict (Icc s₁ s₂ ×ˢ B0579.cell c))) :
    ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))),
      ∀ i, MemLp (fun x => f (r, x) i) 2 (volume.restrict (B0579.cell c)) := by
  have hU : Ioi (0 : ℝ) = ⋃ n : ℕ, Icc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1) := by
    ext x
    simp only [mem_Ioi, mem_iUnion, mem_Icc]
    constructor
    · intro hx
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt hx
      obtain ⟨k, hk⟩ := exists_nat_ge x
      refine ⟨max m k, ?_, ?_⟩
      · refine le_trans ?_ hm.le
        apply one_div_le_one_div_of_le (by positivity)
        have : (m : ℝ) ≤ ((max m k : ℕ) : ℝ) := by exact_mod_cast le_max_left m k
        linarith
      · have : (k : ℝ) ≤ ((max m k : ℕ) : ℝ) := by exact_mod_cast le_max_right m k
        linarith
    · rintro ⟨n, hn, -⟩
      exact lt_of_lt_of_le (by positivity) hn
  rw [hU, ae_restrict_iUnion_iff]
  intro n
  exact slice_band_ae (fun i => hf _ _ (by positivity) i)

/-! ### Linearity of the `g`-part -/

theorem gLin {c : ℝ} (F : ℝ × ℝ → Fin 2 → ℂ)
    (hF : ∀ i, MemLp (fun x => F x i) 2 (volume.restrict (B0579.cell c)))
    {φ ψ : ℝ × ℝ → ℝ} (hφ : B0579.IsCylTest c φ) (hψ : B0579.IsCylTest c ψ) (a : ℝ) :
    (∫ x in B0579.cell c, (F x 0 * (B0579.pd 1 (φ + ψ) x : ℂ) -
        F x 1 * (B0579.pd 0 (φ + ψ) x : ℂ))) =
      (∫ x in B0579.cell c, (F x 0 * (B0579.pd 1 φ x : ℂ) - F x 1 * (B0579.pd 0 φ x : ℂ))) +
      ∫ x in B0579.cell c, (F x 0 * (B0579.pd 1 ψ x : ℂ) - F x 1 * (B0579.pd 0 ψ x : ℂ)) ∧
    (∫ x in B0579.cell c, (F x 0 * (B0579.pd 1 (a • φ) x : ℂ) -
        F x 1 * (B0579.pd 0 (a • φ) x : ℂ))) =
      (a : ℂ) * ∫ x in B0579.cell c, (F x 0 * (B0579.pd 1 φ x : ℂ) -
        F x 1 * (B0579.pd 0 φ x : ℂ)) := by
  have hI : ∀ {χ : ℝ × ℝ → ℝ}, B0579.IsCylTest c χ →
      IntegrableOn (fun x => F x 0 * (B0579.pd 1 χ x : ℂ) - F x 1 * (B0579.pd 0 χ x : ℂ))
        (B0579.cell c) := fun hχ =>
    (UnforcedLeray.Short.IIIa.Exist.lfc_integrableOn_vol_test (hF 0) (hχ.pd 1)).sub
      (UnforcedLeray.Short.IIIa.Exist.lfc_integrableOn_vol_test (hF 1) (hχ.pd 0))
  constructor
  · rw [← integral_add (hI hφ) (hI hψ)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [pd_add' _ hφ.differentiable hψ.differentiable, Pi.add_apply]
    push_cast
    ring
  · rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [pd_smul' _ a hφ.differentiable, Pi.smul_apply, smul_eq_mul]
    push_cast
    ring

/-! ### Linearity of the flow part -/

theorem cd_pQ {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (Cyl.partialQ F) := by
  have h : Cyl.partialQ F = fun w => fderiv ℝ F w (1, 0) :=
    funext fun w => Cyl.partialQ_eq_fderiv (hF.differentiable (by simp)) w
  rw [h]
  exact (hF.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem cd_pEta {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (Cyl.partialEta F) := by
  have h : Cyl.partialEta F = fun w => fderiv ℝ F w (0, 1) :=
    funext fun w => Cyl.partialEta_eq_fderiv (hF.differentiable (by simp)) w
  rw [h]
  exact (hF.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

section Flow

variable {ν c : ℝ}

theorem v_comp_smooth (tr : UnforcedLeray.B0140.TrainSol ν c) {r : ℝ} (hr : 0 ≤ r) (k : Fin 2) :
    ContDiff ℝ ∞ (fun x : ℝ × ℝ => tr.v r x k) :=
  (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp
    (UnforcedLeray.B0238.contDiff_Vc tr hr)

theorem v_comp_periodic (tr : UnforcedLeray.B0140.TrainSol ν c) {r : ℝ} (hr : 0 ≤ r) (k : Fin 2) :
    Cyl.IsPeriodic c (fun x : ℝ × ℝ => tr.v r x k) := fun x => by
  show tr.v r (x.1 + c, x.2) k = tr.v r x k
  rw [tr.isTrain.periodic_v r hr x]

theorem Ec_smooth (tr : UnforcedLeray.B0140.TrainSol ν c) {r : ℝ} (hr : 0 ≤ r) :
    ContDiff ℝ ∞ (UnforcedLeray.B0238.Ec tr r) := by
  have e : UnforcedLeray.B0238.Ec tr r = fun z =>
      Cyl.partialQ (fun w : ℝ × ℝ => tr.v r w 1) z - Cyl.partialEta (fun w : ℝ × ℝ => tr.v r w 0) z :=
    rfl
  rw [e]
  exact (cd_pQ (v_comp_smooth tr hr 1)).sub (cd_pEta (v_comp_smooth tr hr 0))

theorem Ec_periodic (tr : UnforcedLeray.B0140.TrainSol ν c) {r : ℝ} (hr : 0 ≤ r) :
    ∀ x : ℝ × ℝ, UnforcedLeray.B0238.Ec tr r (x.1 + c, x.2) = UnforcedLeray.B0238.Ec tr r x := by
  intro x
  have h1 := (v_comp_periodic tr hr 1).partialQ x
  have h0 := (v_comp_periodic tr hr 0).partialEta x
  show Cyl.partialQ (fun w : ℝ × ℝ => tr.v r w 1) (x.1 + c, x.2) -
      Cyl.partialEta (fun w : ℝ × ℝ => tr.v r w 0) (x.1 + c, x.2) =
      Cyl.partialQ (fun w : ℝ × ℝ => tr.v r w 1) x - Cyl.partialEta (fun w : ℝ × ℝ => tr.v r w 0) x
  rw [h1, h0]

theorem pd_sp {χ : ℝ × ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hp : ∀ x : ℝ × ℝ, χ (x.1 + c, x.2) = χ x) (j : Fin 2) :
    ContDiff ℝ ∞ (B0579.pd j χ) ∧ ∀ x : ℝ × ℝ, B0579.pd j χ (x.1 + c, x.2) = B0579.pd j χ x := by
  refine ⟨((contDiff_infty_iff_fderiv.1 hχ).2).clm_apply contDiff_const, fun x => ?_⟩
  have hfun : (fun y : ℝ × ℝ => χ (y + ((c, 0) : ℝ × ℝ))) = χ := by
    funext y
    have hy : y + ((c, 0) : ℝ × ℝ) = (y.1 + c, y.2) := by ext <;> simp
    rw [hy]
    exact hp y
  have h := fderiv_comp_add_right (𝕜 := ℝ) (f := χ) (x := x) ((c, 0) : ℝ × ℝ)
  rw [hfun] at h
  have hx : x + ((c, 0) : ℝ × ℝ) = (x.1 + c, x.2) := by ext <;> simp
  rw [hx] at h
  simp only [B0579.pd]
  rw [← h]

theorem psi_test (tr : UnforcedLeray.B0140.TrainSol ν c) {r : ℝ} (hr : 0 ≤ r)
    {φ : ℝ × ℝ → ℝ} (hφ : B0579.IsCylTest c φ) :
    B0579.IsCylTest c (fun x => ν * lapP φ x +
      (tr.v r x 0 * B0579.pd 0 φ x + tr.v r x 1 * B0579.pd 1 φ x)) := by
  have e : (fun x => ν * lapP φ x +
      (tr.v r x 0 * B0579.pd 0 φ x + tr.v r x 1 * B0579.pd 1 φ x)) =
      (ν • (B0579.pd 0 (B0579.pd 0 φ) + B0579.pd 1 (B0579.pd 1 φ))) +
        ((fun x => tr.v r x 0 * B0579.pd 0 φ x) + (fun x => tr.v r x 1 * B0579.pd 1 φ x)) := by
    funext x
    simp [lapP, mul_add]
  rw [e]
  exact cyl_add (cyl_smul ν (cyl_add ((hφ.pd 0).pd 0) ((hφ.pd 1).pd 1)))
    (cyl_add (cyl_mul_sp (v_comp_smooth tr hr 0) (v_comp_periodic tr hr 0) (hφ.pd 0))
      (cyl_mul_sp (v_comp_smooth tr hr 1) (v_comp_periodic tr hr 1) (hφ.pd 1)))

theorem theta_test (tr : UnforcedLeray.B0140.TrainSol ν c) {r : ℝ} (hr : 0 ≤ r) (j : Fin 2)
    {φ : ℝ × ℝ → ℝ} (hφ : B0579.IsCylTest c φ) :
    B0579.IsCylTest c (fun x => B0579.pd j (UnforcedLeray.B0238.Ec tr r) x * φ x) :=
  cyl_mul_sp (pd_sp (Ec_smooth tr hr) (Ec_periodic tr hr) j).1
    (pd_sp (Ec_smooth tr hr) (Ec_periodic tr hr) j).2 hφ

theorem flow_eq (tr : UnforcedLeray.B0140.TrainSol ν c) (om : ℝ × ℝ → ℂ) (u : ℝ × ℝ → Fin 2 → ℂ)
    (r : ℝ) (φ : ℝ × ℝ → ℝ) (x : ℝ × ℝ) :
    flowIntegrand tr om u r φ x =
      om x * ((ν * lapP φ x + (tr.v r x 0 * B0579.pd 0 φ x + tr.v r x 1 * B0579.pd 1 φ x) : ℝ) : ℂ) -
        (u x 0 * ((B0579.pd 0 (UnforcedLeray.B0238.Ec tr r) x * φ x : ℝ) : ℂ) +
          u x 1 * ((B0579.pd 1 (UnforcedLeray.B0238.Ec tr r) x * φ x : ℝ) : ℂ)) := by
  unfold flowIntegrand
  push_cast
  ring

theorem flow_int (tr : UnforcedLeray.B0140.TrainSol ν c) {r : ℝ} (hr : 0 ≤ r)
    (om : ℝ × ℝ → ℂ) (u : ℝ × ℝ → Fin 2 → ℂ)
    (hom : ∀ ψ : ℝ × ℝ → ℝ, B0579.IsCylTest c ψ → IntegrableOn (fun x => om x * (ψ x : ℂ)) (B0579.cell c))
    (hu : ∀ j, MemLp (fun x => u x j) 2 (volume.restrict (B0579.cell c)))
    {φ : ℝ × ℝ → ℝ} (hφ : B0579.IsCylTest c φ) :
    IntegrableOn (flowIntegrand tr om u r φ) (B0579.cell c) := by
  have h1 := hom _ (psi_test tr hr hφ)
  have h2 := UnforcedLeray.Short.IIIa.Exist.lfc_integrableOn_vol_test (hu 0) (theta_test tr hr 0 hφ)
  have h3 := UnforcedLeray.Short.IIIa.Exist.lfc_integrableOn_vol_test (hu 1) (theta_test tr hr 1 hφ)
  exact (h1.sub (h2.add h3)).congr (Eventually.of_forall fun x => (flow_eq tr om u r φ x).symm)

theorem flow_lin (tr : UnforcedLeray.B0140.TrainSol ν c) {r : ℝ} (hr : 0 ≤ r)
    (om : ℝ × ℝ → ℂ) (u : ℝ × ℝ → Fin 2 → ℂ)
    (hom : ∀ ψ : ℝ × ℝ → ℝ, B0579.IsCylTest c ψ → IntegrableOn (fun x => om x * (ψ x : ℂ)) (B0579.cell c))
    (hu : ∀ j, MemLp (fun x => u x j) 2 (volume.restrict (B0579.cell c)))
    {φ ψ : ℝ × ℝ → ℝ} (hφ : B0579.IsCylTest c φ) (hψ : B0579.IsCylTest c ψ) (a : ℝ) :
    (∫ x in B0579.cell c, flowIntegrand tr om u r (φ + ψ) x) =
      (∫ x in B0579.cell c, flowIntegrand tr om u r φ x) +
        ∫ x in B0579.cell c, flowIntegrand tr om u r ψ x ∧
    (∫ x in B0579.cell c, flowIntegrand tr om u r (a • φ) x) =
      (a : ℂ) * ∫ x in B0579.cell c, flowIntegrand tr om u r φ x := by
  constructor
  · rw [← integral_add (flow_int tr hr om u hom hu hφ) (flow_int tr hr om u hom hu hψ)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [flowIntegrand, lapP]
    rw [pd_add2 0 0 hφ hψ, pd_add2 1 1 hφ hψ, pd_add' 0 hφ.differentiable hψ.differentiable,
      pd_add' 1 hφ.differentiable hψ.differentiable]
    simp only [Pi.add_apply]
    push_cast
    ring
  · rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [flowIntegrand, lapP]
    rw [pd_smul2 0 0 a hφ, pd_smul2 1 1 a hφ, pd_smul' 0 a hφ.differentiable,
      pd_smul' 1 a hφ.differentiable]
    simp only [Pi.smul_apply, smul_eq_mul]
    push_cast
    ring

end Flow

theorem vtvRLinAE : VtvRLinAE := by
  intro ν c μ tr om g b G f H
  obtain ⟨hν, hc, hBUC, hE, hBS, hf, hcurl, hid, hOm⟩ := H
  have hsl := slice_ae (c := c) hf
  have hpos : ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), r ∈ Ioi (0 : ℝ) :=
    ae_restrict_mem measurableSet_Ioi
  filter_upwards [hsl, hpos] with r hr hr0
  intro φ ψ hφ hψ a
  have hr0' : (0 : ℝ) < r := hr0
  obtain ⟨g1, g2⟩ := gLin (fun x => f (r, x)) hr hφ hψ a
  obtain ⟨f1, f2⟩ := flow_lin tr hr0'.le (om r) (fun x => b (r, x)) (hOm r hr0')
    (fun j => (hBS r hr0').1 j) hφ hψ a
  constructor
  · unfold vtvR
    rw [hcurl r hr0' (φ + ψ) (cyl_add hφ hψ), hcurl r hr0' φ hφ, hcurl r hr0' ψ hψ, g1, f1]
    ring
  · unfold vtvR
    rw [hcurl r hr0' (a • φ) (cyl_smul a hφ), hcurl r hr0' φ hφ, g2, f2]
    ring

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
