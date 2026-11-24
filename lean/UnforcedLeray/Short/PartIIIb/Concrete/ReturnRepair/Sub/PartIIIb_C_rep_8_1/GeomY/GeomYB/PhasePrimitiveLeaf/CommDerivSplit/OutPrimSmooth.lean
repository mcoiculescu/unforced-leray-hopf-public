import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.GeomYB.PhasePrimitiveLeaf.CommDerivSplit.SpatialReg
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2_11_2.B4a
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2_11_2.B4b

/-!
# Spatial smoothness and integrability of outward primitives (`CommDerivSplit/OutPrimSmooth`)

From `ContDiffOn ℝ ∞ (Z τ) {y' | r₀ < ϱ y'}` and the far-field decay
`‖iteratedFDeriv ℝ j (Z τ) y'‖ ≤ C_j * (ϱ y') ^ (-4 - j)`, proves via `paramIntSmooth_proved`
(`B4a.lean:314`) and `b4b_comp_norm` (`B4b.lean:65`):
1. Integrability `i1`, `i3`, `i4` on `Ioi r` for all `r > r₀` and `z : ℝ`.
2. `ContDiffOn ℝ ∞` on `{y' | r₀ < ϱ y'}` for `psiFld Z τ`, `outPrim Z τ (ϱ y') (y' 2)`,
   `outPrim (fun t y'' => fderiv ℝ (Z t) y'' y'') τ (ϱ y') (y' 2)`, and
   `outPrim (fun t y'' => physLap (Z t) y'') τ (ϱ y') (y' 2)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.YBPhase

open YBComm UnforcedLeray.PhaseSpace

/-- Multiplying a smooth function `h : ℝ × ℝ × ℝ → ℝ` with `(ρ ^ (k + 1))⁻¹` decay by `x.2.1 = ρ`
yields a smooth function with `(ρ ^ k)⁻¹` decay. -/
theorem iter_mul_rho_step {r₀ : ℝ} (hr₀ : 0 ≤ r₀) (k : ℕ) {h : ℝ × ℝ × ℝ → ℝ}
    (hh : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h {x : ℝ × ℝ × ℝ | r₀ < x.2.1})
    (hb : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ × ℝ × ℝ, 2 * r₀ + 2 ≤ x.2.1 →
      ‖iteratedFDeriv ℝ j h x‖ ≤ C * (x.2.1 ^ (k + 1))⁻¹) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × ℝ × ℝ => x.2.1 * h x)
      {x : ℝ × ℝ × ℝ | r₀ < x.2.1} ∧
    ∀ n : ℕ, ∃ C' : ℝ, 0 ≤ C' ∧ ∀ x : ℝ × ℝ × ℝ, 2 * r₀ + 2 ≤ x.2.1 →
      ‖iteratedFDeriv ℝ n (fun x : ℝ × ℝ × ℝ => x.2.1 * h x) x‖ ≤ C' * (x.2.1 ^ k)⁻¹ := by
  have hft : IsOpen {x : ℝ × ℝ × ℝ | r₀ < x.2.1} := isOpen_lt continuous_const (by fun_prop)
  have hfs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : ℝ × ℝ × ℝ => y.2.1) :=
    contDiff_fst.comp contDiff_snd
  refine ⟨hfs.contDiffOn.mul hh, fun n => ?_⟩
  choose C hC0 hC using hb
  refine ⟨∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (2 * C (n - i)),
    Finset.sum_nonneg fun i _ => by have := hC0 (n - i); positivity, fun x hx => ?_⟩
  set ρ : ℝ := x.2.1
  have hρ1 : 1 ≤ ρ := by show 1 ≤ x.2.1; linarith
  have hρ0 : 0 < ρ := by linarith
  have hxt : x ∈ {x : ℝ × ℝ × ℝ | r₀ < x.2.1} := by show r₀ < x.2.1; linarith
  have hn : (n : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast le_top
  have hL := norm_iteratedFDerivWithin_mul_le hfs.contDiffOn hh hft.uniqueDiffOn hxt hn
  rw [iteratedFDerivWithin_of_isOpen n hft hxt] at hL
  refine hL.trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [iteratedFDerivWithin_of_isOpen i hft hxt, iteratedFDerivWithin_of_isOpen (n - i) hft hxt]
  have hi : ‖iteratedFDeriv ℝ i (fun y : ℝ × ℝ × ℝ => y.2.1) x‖ ≤ 2 * ρ := by
    have hbi := b4b_lin_iter i x
    change ‖iteratedFDeriv ℝ i (fun y : ℝ × ℝ × ℝ => y.2.1) x‖ ≤ |ρ| + 1 at hbi
    rw [abs_of_pos hρ0] at hbi
    linarith
  have hj := hC (n - i) x hx
  have hpow : ρ * (ρ ^ (k + 1))⁻¹ = (ρ ^ k)⁻¹ := by
    rw [pow_succ, mul_inv, mul_comm (ρ ^ k)⁻¹, ← mul_assoc, mul_inv_cancel₀ hρ0.ne', one_mul]
  calc (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun y : ℝ × ℝ × ℝ => y.2.1) x‖ *
          ‖iteratedFDeriv ℝ (n - i) h x‖
      ≤ (n.choose i : ℝ) * (2 * ρ) * (C (n - i) * (ρ ^ (k + 1))⁻¹) := by
        gcongr
    _ = (n.choose i : ℝ) * (2 * C (n - i)) * (ρ * (ρ ^ (k + 1))⁻¹) := by ring
    _ = (n.choose i : ℝ) * (2 * C (n - i)) * (ρ ^ k)⁻¹ := by rw [hpow]

/-- A smooth function `G : ℝ × ℝ × ℝ → ℝ` on `{x | r₀ < x.2.1}` with `(ρ ^ 3)⁻¹` far-field decay
satisfies `PIS_Bnd G r₀`, is integrable on `Ioi r` for `r > r₀`, and has `C^∞` outward primitive
on `{y' : Space | r₀ < ϱ y'}`. -/
theorem pis_of_k3 {r₀ : ℝ} (hr₀ : 0 ≤ r₀) {G : ℝ × ℝ × ℝ → ℝ}
    (hG : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G {x : ℝ × ℝ × ℝ | r₀ < x.2.1})
    (hb : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ × ℝ × ℝ, 2 * r₀ + 2 ≤ x.2.1 →
      ‖iteratedFDeriv ℝ n G x‖ ≤ C * (x.2.1 ^ 3)⁻¹) :
    PIS_Bnd G r₀ ∧
    (∀ (τ z r : ℝ), r₀ < r → IntegrableOn (fun ρ : ℝ => G (τ, ρ, z)) (Ioi r)) ∧
    (∀ τ : ℝ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y' : Space => -∫ ρ in Ioi (ϱ y'), G (τ, ρ, y' 2)) {y' : Space | r₀ < ϱ y'}) := by
  have hpis : PIS_Bnd G r₀ := by
    intro n K _
    obtain ⟨C, hC0, hC⟩ := hb n
    refine ⟨2 * r₀ + 2, C, by linarith, by linarith, fun τ z _ ρ hρ => ?_⟩
    have hρ1 : 1 ≤ ρ := by linarith
    have h1 := hC (τ, ρ, z) hρ
    have h2 : (ρ ^ 3)⁻¹ ≤ (ρ ^ 2)⁻¹ :=
      inv_anti₀ (by positivity) (pow_le_pow_right₀ hρ1 (by norm_num))
    calc ‖iteratedFDeriv ℝ n G (τ, ρ, z)‖ ≤ C * (ρ ^ 3)⁻¹ := h1
      _ ≤ C * (ρ ^ 2)⁻¹ := mul_le_mul_of_nonneg_left h2 hC0
      _ = C / ρ ^ 2 := by rw [div_eq_mul_inv]
  refine ⟨hpis, ?_, ?_⟩
  · intro τ z r hr
    obtain ⟨M, hM0, hMb⟩ := pis_bound G r₀ r 0 hG {(τ, z)} isCompact_singleton
      (hpis 0 {(τ, z)} isCompact_singleton) hr
    have hmaj : Integrable (fun ρ : ℝ => M * (1 + ‖ρ‖) ^ (-(2 : ℝ)))
        (volume.restrict (Ioi r)) :=
      ((integrable_one_add_norm (μ := (volume : Measure ℝ)) (r := 2) (by norm_num)).const_mul M).restrict
    have hcont : ContinuousOn (fun ρ : ℝ => G (τ, ρ, z)) (Ioi r) := by
      have hc : ContinuousOn (fun ρ : ℝ => (τ, ρ, z)) (Ioi r) := by fun_prop
      exact hG.continuousOn.comp hc fun ρ (hρ : r < ρ) => show r₀ < ρ by linarith
    refine Integrable.mono' hmaj (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with ρ (hρ : r < ρ)
    have h0 := hMb τ z (mem_singleton _) ρ hρ.le
    rw [norm_iteratedFDeriv_zero] at h0
    refine h0.trans (le_of_eq ?_)
    rw [Real.norm_eq_abs, Real.rpow_neg (by positivity), Real.rpow_two, div_eq_mul_inv]
  · intro τ
    have hP := paramIntSmooth_proved G r₀ hG hpis
    set φ : Space → ℝ × ℝ × ℝ := fun y' => (τ, ϱ y', y' 2)
    have hU : IsOpen {y' : Space | r₀ < ϱ y'} := isOpen_lt continuous_const continuous_ϱ
    have hφ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ {y' : Space | r₀ < ϱ y'} := by
      refine contDiffOn_const.prodMk (ContDiffOn.prodMk ?_ ?_)
      · exact contDiffOn_ϱ.mono fun y' (hy' : r₀ < ϱ y') =>
          Sub8_1_1_2_3.not_axis_of_pos (lt_of_le_of_lt hr₀ hy')
      · exact (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).contDiff.contDiffOn
    exact hP.comp hφ fun y' (hy' : r₀ < ϱ y') => hy'

/-- Embedding `w : Space → ℝ` via `(τ, ρ, z) ↦ w !₂[ρ, 0, z]` preserves `C^∞` and `(ρ ^ m)⁻¹` decay. -/
theorem embed_space_decay {r₀ : ℝ} (hr₀ : 0 ≤ r₀) (m : ℕ) {w : Space → ℝ}
    (hw : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w {y' : Space | r₀ < ϱ y'})
    (hb : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ y' : Space, 2 * r₀ + 2 ≤ ϱ y' →
      ‖iteratedFDeriv ℝ j w y'‖ ≤ C * (ϱ y' ^ m)⁻¹) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × ℝ × ℝ => w !₂[x.2.1, 0, x.2.2])
      {x : ℝ × ℝ × ℝ | r₀ < x.2.1} ∧
    ∀ j : ℕ, ∃ C' : ℝ, 0 ≤ C' ∧ ∀ x : ℝ × ℝ × ℝ, 2 * r₀ + 2 ≤ x.2.1 →
      ‖iteratedFDeriv ℝ j (fun x : ℝ × ℝ × ℝ => w !₂[x.2.1, 0, x.2.2]) x‖ ≤
        C' * (x.2.1 ^ m)⁻¹ := by
  set S : Set (ℝ × Space) := {q | r₀ < ϱ q.2}
  have hUo : IsOpen {y' : Space | r₀ < ϱ y'} := isOpen_lt continuous_const continuous_ϱ
  have hSo : IsOpen S := isOpen_lt continuous_const (continuous_ϱ.comp continuous_snd)
  set P2 : ℝ × Space →L[ℝ] Space := ContinuousLinearMap.snd ℝ ℝ Space
  set W : ℝ × Space → ℝ := w ∘ P2
  have hWs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W S :=
    hw.comp P2.contDiff.contDiffOn fun q hq => hq
  have hmaps : MapsTo b4bE {x : ℝ × ℝ × ℝ | r₀ < x.2.1} S := by
    intro x (hx : r₀ < x.2.1)
    rw [b4bE_apply]
    show r₀ < ϱ (!₂[x.2.1, 0, x.2.2] : Space)
    rw [b4b_rho x.2.1 x.2.2 (hr₀.trans hx.le)]
    exact hx
  have hWe : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (W ∘ b4bE) {x : ℝ × ℝ × ℝ | r₀ < x.2.1} :=
    hWs.comp b4bE.contDiff.contDiffOn hmaps
  have hfun : (fun x : ℝ × ℝ × ℝ => w !₂[x.2.1, 0, x.2.2]) = W ∘ b4bE := by
    funext x; simp [W, P2, b4bE_apply]
  rw [hfun]
  refine ⟨hWe, fun j => ?_⟩
  obtain ⟨C, hC0, hC⟩ := hb j
  refine ⟨C * ‖P2‖ ^ j * ‖b4bE‖ ^ j, by positivity, fun x hx => ?_⟩
  have hx0 : 0 ≤ x.2.1 := by linarith
  have hexS : b4bE x ∈ S := hmaps (by show r₀ < x.2.1; linarith)
  refine (b4b_comp_norm W S hSo hWs j x hexS).trans ?_
  have hy'S : P2 (b4bE x) ∈ {y' : Space | r₀ < ϱ y'} := hexS
  have hj : (j : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast le_top
  have hP := ContinuousLinearMap.iteratedFDerivWithin_comp_right P2 hw hUo.uniqueDiffOn
    hSo.uniqueDiffOn hy'S hj
  change iteratedFDerivWithin ℝ j W S (b4bE x) =
    (iteratedFDerivWithin ℝ j w {y' | r₀ < ϱ y'} (P2 (b4bE x))).compContinuousLinearMap
      fun _ => P2 at hP
  rw [iteratedFDerivWithin_of_isOpen j hSo hexS, iteratedFDerivWithin_of_isOpen j hUo hy'S] at hP
  have hW_le : ‖iteratedFDeriv ℝ j W (b4bE x)‖ ≤
      ‖iteratedFDeriv ℝ j w (b4bE x).2‖ * ‖P2‖ ^ j := by
    rw [hP]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact le_rfl
  have hϱ : ϱ (b4bE x).2 = x.2.1 := by
    rw [b4bE_apply]; exact b4b_rho x.2.1 x.2.2 hx0
  have hwy := hC (b4bE x).2 (by rw [hϱ]; exact hx)
  rw [hϱ] at hwy
  calc ‖iteratedFDeriv ℝ j W (b4bE x)‖ * ‖b4bE‖ ^ j
      ≤ (C * (x.2.1 ^ m)⁻¹ * ‖P2‖ ^ j) * ‖b4bE‖ ^ j := by
        gcongr
        exact hW_le.trans (mul_le_mul_of_nonneg_right hwy (by positivity))
    _ = C * ‖P2‖ ^ j * ‖b4bE‖ ^ j * (x.2.1 ^ m)⁻¹ := by ring

/-- Outward integral smoothness and integrability for `ρ * w !₂[ρ, 0, z]` when `w` has `(ϱ ^ 4)⁻¹` decay. -/
theorem outPrim_scalar_mul1 {r₀ : ℝ} (hr₀ : 0 ≤ r₀) {w : Space → ℝ}
    (hw : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w {y' : Space | r₀ < ϱ y'})
    (hb : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ y' : Space, 2 * r₀ + 2 ≤ ϱ y' →
      ‖iteratedFDeriv ℝ j w y'‖ ≤ C * (ϱ y' ^ 4)⁻¹) :
    (∀ (r z : ℝ), r₀ < r → IntegrableOn (fun ρ : ℝ => ρ * w !₂[ρ, 0, z]) (Ioi r)) ∧
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y' : Space => -∫ ρ in Ioi (ϱ y'), ρ * w !₂[ρ, 0, y' 2]) {y' : Space | r₀ < ϱ y'} := by
  obtain ⟨he_sm, he_bd⟩ := embed_space_decay hr₀ 4 hw hb
  obtain ⟨hG_sm, hG_bd⟩ := iter_mul_rho_step hr₀ 3 he_sm he_bd
  obtain ⟨_, hint, hsm⟩ := pis_of_k3 hr₀ hG_sm hG_bd
  exact ⟨fun r z hr => hint 0 z r hr, hsm 0⟩

/-- Outward integral smoothness and integrability for `ρ * (ρ * w !₂[ρ, 0, z])` when `w` has
`(ϱ ^ 5)⁻¹` decay. -/
theorem outPrim_scalar_mul2 {r₀ : ℝ} (hr₀ : 0 ≤ r₀) {w : Space → ℝ}
    (hw : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w {y' : Space | r₀ < ϱ y'})
    (hb : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ y' : Space, 2 * r₀ + 2 ≤ ϱ y' →
      ‖iteratedFDeriv ℝ j w y'‖ ≤ C * (ϱ y' ^ 5)⁻¹) :
    (∀ (r z : ℝ), r₀ < r → IntegrableOn (fun ρ : ℝ => ρ * (ρ * w !₂[ρ, 0, z])) (Ioi r)) ∧
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y' : Space => -∫ ρ in Ioi (ϱ y'), ρ * (ρ * w !₂[ρ, 0, y' 2]))
      {y' : Space | r₀ < ϱ y'} := by
  obtain ⟨he_sm, he_bd⟩ := embed_space_decay hr₀ 5 hw hb
  obtain ⟨hG1_sm, hG1_bd⟩ := iter_mul_rho_step hr₀ 4 he_sm he_bd
  obtain ⟨hG2_sm, hG2_bd⟩ := iter_mul_rho_step hr₀ 3 hG1_sm hG1_bd
  obtain ⟨_, hint, hsm⟩ := pis_of_k3 hr₀ hG2_sm hG2_bd
  exact ⟨fun r z hr => hint 0 z r hr, hsm 0⟩

/-- Iterated derivative bound for `physPd f k` on an open set. -/
theorem norm_iteratedFDeriv_physPd_le {f : Space → Space} {U : Set Space} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f U) (k : Fin 3) (j : ℕ) {y' : Space}
    (hy' : y' ∈ U) :
    ‖iteratedFDeriv ℝ j (physPd f k) y'‖ ≤ ‖iteratedFDeriv ℝ (j + 1) f y'‖ := by
  set L : (Space →L[ℝ] Space) →L[ℝ] Space :=
    ContinuousLinearMap.apply ℝ Space (UnforcedLeray.coordinateVector k)
  have hLn : ‖L‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun A => ?_
    calc ‖A (UnforcedLeray.coordinateVector k)‖
        ≤ ‖A‖ * ‖UnforcedLeray.coordinateVector k‖ := A.le_opNorm _
      _ = ‖A‖ * 1 := by simp [UnforcedLeray.coordinateVector]
      _ = 1 * ‖A‖ := by ring
  have hfd : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fderiv ℝ f) y' :=
    (hf.fderiv_of_isOpen hU (by simp)).contDiffAt (hU.mem_nhds hy')
  have hj : (j : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast le_top
  have hfun : physPd f k = L ∘ fderiv ℝ f := rfl
  rw [hfun]
  calc ‖iteratedFDeriv ℝ j (L ∘ fderiv ℝ f) y'‖
      ≤ ‖L‖ * ‖iteratedFDeriv ℝ j (fderiv ℝ f) y'‖ :=
        L.norm_iteratedFDeriv_comp_left hfd hj
    _ ≤ 1 * ‖iteratedFDeriv ℝ (j + 1) f y'‖ := by
        rw [norm_iteratedFDeriv_fderiv]
        exact mul_le_mul_of_nonneg_right hLn (norm_nonneg _)
    _ = ‖iteratedFDeriv ℝ (j + 1) f y'‖ := one_mul _

/-- Iterated derivative bound for `physLap f` on an open set. -/
theorem norm_iteratedFDeriv_physLap_le {f : Space → Space} {U : Set Space} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f U) (j : ℕ) {y' : Space} (hy' : y' ∈ U) :
    ‖iteratedFDeriv ℝ j (physLap f) y'‖ ≤ 3 * ‖iteratedFDeriv ℝ (j + 2) f y'‖ := by
  have hj : (j : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast le_top
  have hterm : ∀ k : Fin 3, ContDiffAt ℝ j (physPd (physPd f k) k) y' := fun k =>
    ((xd_physPd_top hU (xd_physPd_top hU hf k) k).contDiffAt (hU.mem_nhds hy')).of_le hj
  unfold physLap physPd2
  rw [iteratedFDeriv_fun_sum_apply fun k _ => hterm k]
  refine (norm_sum_le _ _).trans ?_
  have hb : ∀ k : Fin 3, ‖iteratedFDeriv ℝ j (physPd (physPd f k) k) y'‖ ≤
      ‖iteratedFDeriv ℝ (j + 2) f y'‖ := fun k =>
    (norm_iteratedFDeriv_physPd_le hU (xd_physPd_top hU hf k) k j hy').trans
      (norm_iteratedFDeriv_physPd_le hU hf k (j + 1) hy')
  refine (Finset.sum_le_sum fun k _ => hb k).trans ?_
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat,
    le_rfl]

/-- Helper converting `(ϱ y') ^ (-4 - (j + d))` into `(ϱ y' ^ m)⁻¹` for `ϱ y' ≥ 1` and `m ≤ 4 + d`. -/
private lemma rpow_decay_le_inv_pow {ρ : ℝ} (hρ : 1 ≤ ρ) (j : ℕ) {m : ℕ} {e : ℝ}
    (he : e ≤ -(m : ℝ)) :
    ρ ^ (e - (j : ℝ)) ≤ (ρ ^ m)⁻¹ := by
  have h1 : ρ ^ (e - (j : ℝ)) ≤ ρ ^ (-(m : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hρ (by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)])
  rw [Real.rpow_neg (by linarith), Real.rpow_natCast] at h1
  exact h1

/-- Spatial outward primitives of `Z τ`, `fderiv ℝ (Z τ) y'' y''`, and `physLap (Z τ)` are
integrable (`i1`, `i3`, `i4`) and `C^∞` on `{y' | r₀ < ϱ y'}`. -/
theorem spatial_outPrim_reg {r₀ : ℝ} (hr₀ : 0 ≤ r₀) (Z : ℝ → Space → Space) (τ : ℝ)
    (hZ_sm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Z τ) {y' : Space | r₀ < ϱ y'})
    (hZ_bd : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ y' : Space, 2 * r₀ + 2 ≤ ϱ y' →
      ‖iteratedFDeriv ℝ j (Z τ) y'‖ ≤ C * (ϱ y') ^ (-4 - (j : ℝ))) :
    (∀ (r z : ℝ), r₀ < r → IntegrableOn (fun ρ : ℝ => ρ * Z τ !₂[ρ, 0, z] 2) (Ioi r)) ∧
    (∀ (r z : ℝ), r₀ < r →
      IntegrableOn (fun ρ : ℝ => ρ * (fderiv ℝ (Z τ) !₂[ρ, 0, z] !₂[ρ, 0, z]) 2) (Ioi r)) ∧
    (∀ (r z : ℝ), r₀ < r →
      IntegrableOn (fun ρ : ℝ => ρ * (physLap (Z τ) !₂[ρ, 0, z]) 2) (Ioi r)) ∧
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y' : Space => outPrim Z τ (ϱ y') (y' 2)) {y' : Space | r₀ < ϱ y'} ∧
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (psiFld Z τ) {y' : Space | r₀ < ϱ y'} ∧
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y' : Space => outPrim (fun t y'' => fderiv ℝ (Z t) y'' y'') τ (ϱ y') (y' 2))
      {y' : Space | r₀ < ϱ y'} ∧
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y' : Space => outPrim (fun t y'' => physLap (Z t) y'') τ (ϱ y') (y' 2))
      {y' : Space | r₀ < ϱ y'} := by
  have hU : IsOpen {y' : Space | r₀ < ϱ y'} := isOpen_lt continuous_const continuous_ϱ
  set Pz : Space →L[ℝ] ℝ := EuclideanSpace.proj (2 : Fin 3)
  have hPz_le : ‖Pz‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
    rw [one_mul]
    exact PiLp.norm_apply_le v (2 : Fin 3)
  have hcomp_Pz : ∀ {f : Space → Space},
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f {y' : Space | r₀ < ϱ y'} →
      ∀ (j : ℕ) {y' : Space}, r₀ < ϱ y' →
      ‖iteratedFDeriv ℝ j (fun y'' => f y'' 2) y'‖ ≤ ‖iteratedFDeriv ℝ j f y'‖ := by
    intro f hf j y' hy'
    have hj : (j : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast le_top
    have hfa : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f y' := hf.contDiffAt (hU.mem_nhds hy')
    calc ‖iteratedFDeriv ℝ j (Pz ∘ f) y'‖
        ≤ ‖Pz‖ * ‖iteratedFDeriv ℝ j f y'‖ := Pz.norm_iteratedFDeriv_comp_left hfa hj
      _ ≤ 1 * ‖iteratedFDeriv ℝ j f y'‖ := mul_le_mul_of_nonneg_right hPz_le (norm_nonneg _)
      _ = ‖iteratedFDeriv ℝ j f y'‖ := one_mul _
  -- 1. w₁ = fun y' => Z τ y' 2
  have hw1_sm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y' : Space => Z τ y' 2)
      {y' : Space | r₀ < ϱ y'} := Pz.contDiff.comp_contDiffOn hZ_sm
  have hw1_bd : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ y' : Space, 2 * r₀ + 2 ≤ ϱ y' →
      ‖iteratedFDeriv ℝ j (fun y'' : Space => Z τ y'' 2) y'‖ ≤ C * (ϱ y' ^ 4)⁻¹ := by
    intro j
    obtain ⟨C, hC0, hC⟩ := hZ_bd j
    refine ⟨C, hC0, fun y' hy' => ?_⟩
    have hy'0 : r₀ < ϱ y' := by linarith
    have hy'1 : 1 ≤ ϱ y' := by linarith
    exact (hcomp_Pz hZ_sm j hy'0).trans
      ((hC y' hy').trans (mul_le_mul_of_nonneg_left
        (rpow_decay_le_inv_pow hy'1 j (by norm_num)) hC0))
  obtain ⟨hi1, hsm1⟩ := outPrim_scalar_mul1 hr₀ hw1_sm hw1_bd
  -- 2. w₄ = fun y' => physLap (Z τ) y' 2
  have hLap_sm := xd_physLap_top hU hZ_sm
  have hw4_sm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y' : Space => physLap (Z τ) y' 2)
      {y' : Space | r₀ < ϱ y'} := Pz.contDiff.comp_contDiffOn hLap_sm
  have hw4_bd : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ y' : Space, 2 * r₀ + 2 ≤ ϱ y' →
      ‖iteratedFDeriv ℝ j (fun y'' : Space => physLap (Z τ) y'' 2) y'‖ ≤ C * (ϱ y' ^ 4)⁻¹ := by
    intro j
    obtain ⟨C, hC0, hC⟩ := hZ_bd (j + 2)
    refine ⟨3 * C, by positivity, fun y' hy' => ?_⟩
    have hy'0 : r₀ < ϱ y' := by linarith
    have hy'1 : 1 ≤ ϱ y' := by linarith
    have h1 := (hcomp_Pz hLap_sm j hy'0).trans (norm_iteratedFDeriv_physLap_le hU hZ_sm j hy'0)
    have h2 := hC y' hy'
    have h3 : (ϱ y') ^ (-4 - ((j + 2 : ℕ) : ℝ)) ≤ (ϱ y' ^ 4)⁻¹ := by
      rw [show -4 - ((j + 2 : ℕ) : ℝ) = (-6 : ℝ) - (j : ℝ) by push_cast; ring]
      exact rpow_decay_le_inv_pow hy'1 j (by norm_num)
    calc ‖iteratedFDeriv ℝ j (fun y'' : Space => physLap (Z τ) y'' 2) y'‖
        ≤ 3 * (C * (ϱ y') ^ (-4 - ((j + 2 : ℕ) : ℝ))) :=
          h1.trans (mul_le_mul_of_nonneg_left h2 (by norm_num))
      _ ≤ 3 * (C * (ϱ y' ^ 4)⁻¹) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 hC0) (by norm_num)
      _ = 3 * C * (ϱ y' ^ 4)⁻¹ := by ring
  obtain ⟨hi4, hsm4⟩ := outPrim_scalar_mul1 hr₀ hw4_sm hw4_bd
  -- 3. w₂ = fun y' => physPd (Z τ) 2 y' 2 and w₃ = fun y' => physPd (Z τ) 0 y' 2
  have hPd2_sm := xd_physPd_top hU hZ_sm 2
  have hPd0_sm := xd_physPd_top hU hZ_sm 0
  have hw2_sm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y' : Space => physPd (Z τ) 2 y' 2)
      {y' : Space | r₀ < ϱ y'} := Pz.contDiff.comp_contDiffOn hPd2_sm
  have hw3_sm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y' : Space => physPd (Z τ) 0 y' 2)
      {y' : Space | r₀ < ϱ y'} := Pz.contDiff.comp_contDiffOn hPd0_sm
  have hw2_bd : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ y' : Space, 2 * r₀ + 2 ≤ ϱ y' →
      ‖iteratedFDeriv ℝ j (fun y'' : Space => physPd (Z τ) 2 y'' 2) y'‖ ≤ C * (ϱ y' ^ 4)⁻¹ := by
    intro j
    obtain ⟨C, hC0, hC⟩ := hZ_bd (j + 1)
    refine ⟨C, hC0, fun y' hy' => ?_⟩
    have hy'0 : r₀ < ϱ y' := by linarith
    have hy'1 : 1 ≤ ϱ y' := by linarith
    have h1 := (hcomp_Pz hPd2_sm j hy'0).trans (norm_iteratedFDeriv_physPd_le hU hZ_sm 2 j hy'0)
    have h3 : (ϱ y') ^ (-4 - ((j + 1 : ℕ) : ℝ)) ≤ (ϱ y' ^ 4)⁻¹ := by
      rw [show -4 - ((j + 1 : ℕ) : ℝ) = (-5 : ℝ) - (j : ℝ) by push_cast; ring]
      exact rpow_decay_le_inv_pow hy'1 j (by norm_num)
    exact h1.trans ((hC y' hy').trans (mul_le_mul_of_nonneg_left h3 hC0))
  have hw3_bd : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ y' : Space, 2 * r₀ + 2 ≤ ϱ y' →
      ‖iteratedFDeriv ℝ j (fun y'' : Space => physPd (Z τ) 0 y'' 2) y'‖ ≤ C * (ϱ y' ^ 5)⁻¹ := by
    intro j
    obtain ⟨C, hC0, hC⟩ := hZ_bd (j + 1)
    refine ⟨C, hC0, fun y' hy' => ?_⟩
    have hy'0 : r₀ < ϱ y' := by linarith
    have hy'1 : 1 ≤ ϱ y' := by linarith
    have h1 := (hcomp_Pz hPd0_sm j hy'0).trans (norm_iteratedFDeriv_physPd_le hU hZ_sm 0 j hy'0)
    have h3 : (ϱ y') ^ (-4 - ((j + 1 : ℕ) : ℝ)) ≤ (ϱ y' ^ 5)⁻¹ := by
      rw [show -4 - ((j + 1 : ℕ) : ℝ) = (-5 : ℝ) - (j : ℝ) by push_cast; ring]
      exact rpow_decay_le_inv_pow hy'1 j (by norm_num)
    exact h1.trans ((hC y' hy').trans (mul_le_mul_of_nonneg_left h3 hC0))
  obtain ⟨hi2_pd, hsm2_pd⟩ := outPrim_scalar_mul1 hr₀ hw2_sm hw2_bd
  obtain ⟨hi3_pd, hsm3_pd⟩ := outPrim_scalar_mul2 hr₀ hw3_sm hw3_bd
  have h_euler : ∀ (ρ z : ℝ),
      ρ * (fderiv ℝ (Z τ) !₂[ρ, 0, z] !₂[ρ, 0, z]) 2 =
        ρ * (ρ * physPd (Z τ) 0 !₂[ρ, 0, z] 2) + z * (ρ * physPd (Z τ) 2 !₂[ρ, 0, z] 2) := by
    intro ρ z
    have hvec : (!₂[ρ, 0, z] : Space) =
        ρ • UnforcedLeray.coordinateVector 0 + z • UnforcedLeray.coordinateVector 2 := by
      ext i; fin_cases i <;> simp [UnforcedLeray.coordinateVector]
    conv_lhs => rw [
      show fderiv ℝ (Z τ) !₂[ρ, 0, z] !₂[ρ, 0, z] =
          fderiv ℝ (Z τ) !₂[ρ, 0, z]
            (ρ • UnforcedLeray.coordinateVector 0 + z • UnforcedLeray.coordinateVector 2) by
        rw [← hvec]]
    rw [map_add, map_smul, map_smul]
    simp only [physPd, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  have hi3 : ∀ (r z : ℝ), r₀ < r →
      IntegrableOn (fun ρ : ℝ => ρ * (fderiv ℝ (Z τ) !₂[ρ, 0, z] !₂[ρ, 0, z]) 2) (Ioi r) := by
    intro r z hr
    simp only [h_euler]
    exact (hi3_pd r z hr).add ((hi2_pd r z hr).const_mul z)
  have hsm3 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y' : Space => outPrim (fun t y'' => fderiv ℝ (Z t) y'' y'') τ (ϱ y') (y' 2))
      {y' : Space | r₀ < ϱ y'} := by
    have hz_sm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y' : Space => y' 2)
        {y' : Space | r₀ < ϱ y'} := Pz.contDiff.contDiffOn
    refine (hsm3_pd.add (hz_sm.mul hsm2_pd)).congr fun y' (hy' : r₀ < ϱ y') => ?_
    unfold outPrim
    simp only [h_euler]
    rw [integral_add (hi3_pd (ϱ y') (y' 2) hy') ((hi2_pd (ϱ y') (y' 2) hy').const_mul (y' 2)),
      integral_const_mul]
    ring
  have hpsi_sm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (psiFld Z τ) {y' : Space | r₀ < ϱ y'} :=
    hsm1.smul contDiffOn_const
  exact ⟨hi1, hi3, hi4, hsm1, hpsi_sm, hsm3, hsm4⟩

end UnforcedLeray.Short.PartIIIb.Concrete.YBPhase
