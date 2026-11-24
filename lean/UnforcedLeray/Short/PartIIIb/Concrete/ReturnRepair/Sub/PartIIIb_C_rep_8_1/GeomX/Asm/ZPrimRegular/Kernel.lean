import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.Asm.ZPrimRegular.RayPrimW
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.ZRegular
import Mathlib.Analysis.Complex.OperatorNorm

/-!
# `PartIII-b:C/rep/8/1/1/1/asm/4`: ray decay of `zAct` and `zMt` (the kernel half of `ZPrimRegular`)

Source `the November 2 reference manuscript`
lines 4178-4186 (the separated-kernel estimates give convergence of the outward primitive and of
its differentiated versions), 5400-5406 (the receivers of the clear region are radially separated
from the old source), 3604-3621 (`sep:kernel`, `sep:resolvent`), 4776-4791 (the zero-width Newton
fields).

* (`rayDecayW_of`) a field that is `C¹` on an open set containing the half-plane rays
  `ρ ≥ r₀`, and whose value and gradient are `O(ρ⁻³)` for `ρ ≥ R₁`, has `RayDecayW` on
  `[r₀, ∞) × (z - 1, z + 1)`: on the compact piece `[r₀, max R₁ r₀] × [z - 1, z + 1]` the value
  and the gradient are bounded by continuity.
* (`sep_far`) the separated response `W_μ - W_{μ+1}` of a separated source supported in
  `|z'| ≤ r_o` is `O(ϱ⁻³)` with its gradient on `ϱ ≥ 2r_o` (`sepFarDecay`, 4177-4179); the source
  is a cylinder of infinite height, so `ρ⁻³` (not `ρ⁻⁴`) is the decay along the ray.
* (`newton_far`) the zero-width Newton field `W^mt_μ - W^mt_{μ+1}` has `|D^kZ| ≤ C(1+|w|)^{-4-k}`
  (`xsZDecay`), hence is `O(ρ⁻³)` with its gradient.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi Metric

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace GeomXAsm

namespace ZPrimKernel

open RayFTCAux RayPrimAux RayPrimW

theorem ϱ_hpt {ρ : ℝ} (hρ : 0 < ρ) (z : ℝ) : ϱ (hpt ρ z) = ρ := by
  unfold ϱ
  have h0 : (hpt ρ z) 0 = ρ := rfl
  have h1 : (hpt ρ z) 1 = 0 := rfl
  rw [h0, h1]
  simp [Real.sqrt_sq hρ.le]

/-- The Euclidean norm is at most the sum of the coordinate norms. -/
theorem norm_le_sum_coords (x : Space) : ‖x‖ ≤ ∑ i, ‖x i‖ := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_three, Fin.sum_univ_three]
  have h0 := norm_nonneg (x 0)
  have h1 := norm_nonneg (x 1)
  have h2 := norm_nonneg (x 2)
  calc √(‖x 0‖ ^ 2 + ‖x 1‖ ^ 2 + ‖x 2‖ ^ 2) ≤ √((‖x 0‖ + ‖x 1‖ + ‖x 2‖) ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith)
    _ = ‖x 0‖ + ‖x 1‖ + ‖x 2‖ := Real.sqrt_sq (by positivity)

/-- The derivative of a field is bounded by the sum of the derivatives of its components. -/
theorem norm_fderiv_le_of_comp {F : Space → Space} {y : Space} {L : Fin 3 → (Space →L[ℝ] ℝ)}
    (h : ∀ i, HasFDerivAt (fun x => F x i) (L i) y) : ‖fderiv ℝ F y‖ ≤ ∑ i, ‖L i‖ := by
  have hF : DifferentiableAt ℝ F y := (differentiableAt_piLp 2).2 fun i => (h i).differentiableAt
  have hc : ∀ i, HasFDerivAt (fun x => F x i)
      ((PiLp.proj 2 (fun _ : Fin 3 => ℝ) i).comp (fderiv ℝ F y)) y := fun i =>
    (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 (F y) i).comp y hF.hasFDerivAt
  have heq : ∀ i, (PiLp.proj 2 (fun _ : Fin 3 => ℝ) i).comp (fderiv ℝ F y) = L i :=
    fun i => (hc i).unique (h i)
  refine ContinuousLinearMap.opNorm_le_bound _
    (Finset.sum_nonneg fun i _ => norm_nonneg _) fun v => ?_
  calc ‖fderiv ℝ F y v‖ ≤ ∑ i, ‖fderiv ℝ F y v i‖ := norm_le_sum_coords _
    _ = ∑ i, ‖L i v‖ := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← heq i]
        rfl
    _ ≤ ∑ i, ‖L i‖ * ‖v‖ := Finset.sum_le_sum fun i _ => (L i).le_opNorm v
    _ = (∑ i, ‖L i‖) * ‖v‖ := (Finset.sum_mul _ _ _).symm

theorem one_le_mul_rpow {ρ R : ℝ} (hρ : 0 < ρ) (h : ρ ≤ R) : 1 ≤ R ^ 3 * ρ ^ (-3 : ℝ) := by
  rw [Real.rpow_neg hρ.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
    ← div_eq_mul_inv, le_div_iff₀ (pow_pos hρ 3), one_mul]
  exact pow_le_pow_left₀ hρ.le h 3

theorem le_of_split {v M C R ρ : ℝ} (hρ : 0 < ρ) (hM : 0 ≤ M) (hnear : ρ ≤ R → v ≤ M)
    (hfar : R < ρ → v ≤ C * ρ ^ (-3 : ℝ)) : v ≤ max C (M * R ^ 3) * ρ ^ (-3 : ℝ) := by
  have hp : 0 ≤ ρ ^ (-3 : ℝ) := Real.rpow_nonneg hρ.le _
  rcases le_or_gt ρ R with h | h
  · calc v ≤ M := hnear h
      _ ≤ M * (R ^ 3 * ρ ^ (-3 : ℝ)) := le_mul_of_one_le_right hM (one_le_mul_rpow hρ h)
      _ = (M * R ^ 3) * ρ ^ (-3 : ℝ) := by ring
      _ ≤ max C (M * R ^ 3) * ρ ^ (-3 : ℝ) := mul_le_mul_of_nonneg_right (le_max_right _ _) hp
  · calc v ≤ C * ρ ^ (-3 : ℝ) := hfar h
      _ ≤ max C (M * R ^ 3) * ρ ^ (-3 : ℝ) := mul_le_mul_of_nonneg_right (le_max_left _ _) hp

/-- **Ray decay from regularity and far decay.**  If `Z τ` is `C¹` on an open set `U` containing
the half-plane points `(ρ, 0, z')`, `ρ ≥ r₀`, and the value and the gradient are `≤ C ρ⁻³` for
`ρ ≥ R₁`, then `RayDecayW Z τ r₀ z 1 K` for some `K` (the compact piece `ρ ≤ max R₁ r₀` by
continuity). -/
theorem rayDecayW_of {Z : ℝ → Space → Space} {τ : ℝ} {U : Set Space} (hU : IsOpen U)
    (hZ : ContDiffOn ℝ 1 (Z τ) U) {r₀ R₁ C : ℝ} (hr₀ : 0 < r₀)
    (hmem : ∀ ρ : ℝ, r₀ ≤ ρ → ∀ z' : ℝ, hpt ρ z' ∈ U)
    (hfar : ∀ ρ : ℝ, R₁ ≤ ρ → r₀ ≤ ρ → ∀ z' : ℝ,
      ‖Z τ (hpt ρ z')‖ ≤ C * ρ ^ (-3 : ℝ) ∧ ‖fderiv ℝ (Z τ) (hpt ρ z')‖ ≤ C * ρ ^ (-3 : ℝ))
    (z : ℝ) : ∃ K : ℝ, RayDecayW Z τ r₀ z 1 K := by
  set R₂ := max R₁ r₀ with hR₂
  set S : Set Space := (fun p : ℝ × ℝ => hpt p.1 p.2) '' (Icc r₀ R₂ ×ˢ Icc (z - 1) (z + 1))
    with hSdef
  have hS : IsCompact S := (isCompact_Icc.prod isCompact_Icc).image continuous_hpt_pair
  have hSU : S ⊆ U := by
    rintro _ ⟨p, hp, rfl⟩
    exact hmem p.1 hp.1.1 p.2
  obtain ⟨M₁, hM₁⟩ := hS.exists_bound_of_continuousOn (hZ.continuousOn.mono hSU)
  obtain ⟨M₂, hM₂⟩ := hS.exists_bound_of_continuousOn
    ((hZ.continuousOn_fderiv_of_isOpen hU le_rfl).mono hSU)
  set M := max (max M₁ M₂) 0 with hM
  have hM0 : 0 ≤ M := le_max_right _ _
  have hinS : ∀ ρ : ℝ, r₀ ≤ ρ → ρ ≤ R₂ → ∀ z' : ℝ, |z' - z| < 1 → hpt ρ z' ∈ S := by
    intro ρ h1 h2 z' hz'
    have := abs_lt.1 hz'
    exact ⟨(ρ, z'), ⟨⟨h1, h2⟩, ⟨by linarith, by linarith⟩⟩, rfl⟩
  refine ⟨max C (M * R₂ ^ 3), ?_, ?_, ?_⟩
  · intro ρ hρ z' _
    exact (hZ.differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds (hmem ρ hρ z'))
  · intro ρ hρ z' hz'
    have hρ0 : 0 < ρ := lt_of_lt_of_le hr₀ hρ
    refine le_of_split hρ0 hM0 (fun h => ?_) (fun h => ?_)
    · exact (hM₁ _ (hinS ρ hρ h z' hz')).trans ((le_max_left _ _).trans (le_max_left _ _))
    · exact (hfar ρ ((le_max_left _ _).trans h.le) hρ z').1
  · intro ρ hρ z' hz'
    have hρ0 : 0 < ρ := lt_of_lt_of_le hr₀ hρ
    refine le_of_split hρ0 hM0 (fun h => ?_) (fun h => ?_)
    · exact (hM₂ _ (hinS ρ hρ h z' hz')).trans ((le_max_right _ _).trans (le_max_left _ _))
    · exact (hfar ρ ((le_max_left _ _).trans h.le) hρ z').2

/-! ## The separated response (`zAct`) -/

/-- The real separated response `W_μ - W_{μ+1}` of a source `T'` (the form of `wardX0`). -/
def sepField (ν μ : ℝ) (T' : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ) (y : Space) : Space :=
  WithLp.toLp 2 fun i =>
    (UnforcedLeray.Short.IIIa.sepW ν (μ : ℂ) T' y τ i -
      UnforcedLeray.Short.IIIa.sepW ν ((μ : ℂ) + 1) T' y τ i).re

/-- **Far decay of the separated response** (source 4177-4179, 3604-3621; `sepFarDecay`): for a
separated source supported in `|z'| ≤ r_o`, at `ρ ≥ 2r_o` the value and the gradient of
`W_μ - W_{μ+1}` at `(ρ, 0, z')` are `≤ C ρ⁻³`. -/
theorem sep_far {ν μ ro P : ℝ} {T' : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ} (hν : 0 < ν)
    (hμ : -(1 / 4) < μ) (hro : 0 < ro) (hP : 0 < P)
    (hS : UnforcedLeray.Short.IIIa.IsSepSource P ro T') (hM : SepMoment P T') (τ : ℝ) :
    ∃ C : ℝ, ∀ ρ : ℝ, 2 * ro ≤ ρ → ∀ z' : ℝ,
      ‖sepField ν μ T' τ (hpt ρ z')‖ ≤ C * ρ ^ (-3 : ℝ) ∧
      ‖fderiv ℝ (sepField ν μ T' τ) (hpt ρ z')‖ ≤ C * ρ ^ (-3 : ℝ) := by
  have hμa : -(1 / 4) < (μ : ℂ).re := by simpa using hμ
  have hμb : -(1 / 4) < ((μ : ℂ) + 1).re := by simp; linarith
  obtain ⟨C1, h1⟩ := sepFarDecay ν (μ : ℂ) ro P T' hν hμa hro.le hP hS hM τ
  obtain ⟨C2, h2⟩ := sepFarDecay ν ((μ : ℂ) + 1) ro P T' hν hμb hro.le hP hS hM τ
  have hsm := sepWSmoothOn_of UnforcedLeray.Short.IIIa.sepKernelBounds
  refine ⟨3 * (C1 + C2), fun ρ hρ z' => ?_⟩
  have hρ0 : 0 < ρ := by linarith
  set y := hpt ρ z' with hy
  have hϱ : ϱ y = ρ := ϱ_hpt hρ0 z'
  have hy2 : 2 * ro ≤ ϱ y := by rw [hϱ]; exact hρ
  have hyU : y ∈ {y : Space | ro < ϱ y} := by
    show ro < ϱ y
    linarith
  have hUo : IsOpen {y : Space | ro < ϱ y} :=
    isOpen_lt continuous_const UnforcedLeray.Axi.continuous_ϱ
  have hda : ∀ i, DifferentiableAt ℝ (fun x => UnforcedLeray.Short.IIIa.sepW ν (μ : ℂ) T' x τ i) y :=
    fun i => ((hsm ν (μ : ℂ) ro P T' hν hμa hro.le hP hS hM τ i).differentiableOn
      (by norm_num)).differentiableAt (hUo.mem_nhds hyU)
  have hdb : ∀ i, DifferentiableAt ℝ
      (fun x => UnforcedLeray.Short.IIIa.sepW ν ((μ : ℂ) + 1) T' x τ i) y :=
    fun i => ((hsm ν ((μ : ℂ) + 1) ro P T' hν hμb hro.le hP hS hM τ i).differentiableOn
      (by norm_num)).differentiableAt (hUo.mem_nhds hyU)
  have hp : 0 ≤ ρ ^ (-3 : ℝ) := Real.rpow_nonneg hρ0.le _
  constructor
  · refine (norm_le_sum_coords _).trans ?_
    have hi : ∀ i : Fin 3, ‖sepField ν μ T' τ y i‖ ≤ (C1 + C2) * ρ ^ (-3 : ℝ) := by
      intro i
      have ha := (h1 i y hy2).1
      have hb := (h2 i y hy2).1
      rw [hϱ] at ha hb
      calc ‖sepField ν μ T' τ y i‖
          = ‖(UnforcedLeray.Short.IIIa.sepW ν (μ : ℂ) T' y τ i -
              UnforcedLeray.Short.IIIa.sepW ν ((μ : ℂ) + 1) T' y τ i).re‖ := rfl
        _ ≤ ‖UnforcedLeray.Short.IIIa.sepW ν (μ : ℂ) T' y τ i -
              UnforcedLeray.Short.IIIa.sepW ν ((μ : ℂ) + 1) T' y τ i‖ := by
            rw [Real.norm_eq_abs]; exact Complex.abs_re_le_norm _
        _ ≤ _ := norm_sub_le _ _
        _ ≤ C1 * ρ ^ (-3 : ℝ) + C2 * ρ ^ (-3 : ℝ) := add_le_add ha hb
        _ = (C1 + C2) * ρ ^ (-3 : ℝ) := by ring
    calc ∑ i, ‖sepField ν μ T' τ y i‖ ≤ ∑ _i : Fin 3, (C1 + C2) * ρ ^ (-3 : ℝ) :=
          Finset.sum_le_sum fun i _ => hi i
      _ = 3 * (C1 + C2) * ρ ^ (-3 : ℝ) := by simp [Finset.sum_const]; ring
  · have hcomp : ∀ i, HasFDerivAt (fun x => sepField ν μ T' τ x i)
        (Complex.reCLM.comp (fderiv ℝ (fun x => UnforcedLeray.Short.IIIa.sepW ν (μ : ℂ) T' x τ i) y -
          fderiv ℝ (fun x => UnforcedLeray.Short.IIIa.sepW ν ((μ : ℂ) + 1) T' x τ i) y)) y :=
      fun i => Complex.reCLM.hasFDerivAt.comp y ((hda i).hasFDerivAt.sub (hdb i).hasFDerivAt)
    refine (norm_fderiv_le_of_comp hcomp).trans ?_
    have hi : ∀ i : Fin 3,
        ‖Complex.reCLM.comp (fderiv ℝ (fun x => UnforcedLeray.Short.IIIa.sepW ν (μ : ℂ) T' x τ i) y -
          fderiv ℝ (fun x => UnforcedLeray.Short.IIIa.sepW ν ((μ : ℂ) + 1) T' x τ i) y)‖ ≤
          (C1 + C2) * ρ ^ (-3 : ℝ) := by
      intro i
      have ha := (h1 i y hy2).2
      have hb := (h2 i y hy2).2
      rw [hϱ] at ha hb
      calc _ ≤ ‖Complex.reCLM‖ * ‖fderiv ℝ (fun x => UnforcedLeray.Short.IIIa.sepW ν (μ : ℂ) T' x τ i) y -
              fderiv ℝ (fun x => UnforcedLeray.Short.IIIa.sepW ν ((μ : ℂ) + 1) T' x τ i) y‖ :=
            ContinuousLinearMap.opNorm_comp_le _ _
        _ = ‖fderiv ℝ (fun x => UnforcedLeray.Short.IIIa.sepW ν (μ : ℂ) T' x τ i) y -
              fderiv ℝ (fun x => UnforcedLeray.Short.IIIa.sepW ν ((μ : ℂ) + 1) T' x τ i) y‖ := by
            rw [Complex.reCLM_norm, one_mul]
        _ ≤ _ := norm_sub_le _ _
        _ ≤ C1 * ρ ^ (-3 : ℝ) + C2 * ρ ^ (-3 : ℝ) := add_le_add ha hb
        _ = (C1 + C2) * ρ ^ (-3 : ℝ) := by ring
    calc _ ≤ ∑ _i : Fin 3, (C1 + C2) * ρ ^ (-3 : ℝ) := Finset.sum_le_sum fun i _ => hi i
      _ = 3 * (C1 + C2) * ρ ^ (-3 : ℝ) := by simp [Finset.sum_const]; ring

/-! ## The zero-width Newton field (`zMt`) -/

/-- The zero-width Newton field `W^mt_μ - W^mt_{μ+1}` on `Space`. -/
def newtonField (c ν ε μ : ℝ) (χo : ℝ → ℝ) (M : Chart → Mat3) (y : Space) : Space :=
  WithLp.toLp 2 ((youngW c ν ε μ χo M - youngW c ν ε (μ + 1) χo M) (WithLp.ofLp y))

theorem ofLp_hpt_norm {ρ : ℝ} (hρ : 0 < ρ) (z : ℝ) : ρ ≤ ‖WithLp.ofLp (hpt ρ z)‖ := by
  have h := norm_le_pi_norm (WithLp.ofLp (hpt ρ z)) 0
  have h0 : (WithLp.ofLp (hpt ρ z)) 0 = ρ := rfl
  rw [h0, Real.norm_eq_abs, abs_of_pos hρ] at h
  exact h

theorem cylR_ofLp_hpt {ρ : ℝ} (hρ : 0 < ρ) (z : ℝ) : cylR (WithLp.ofLp (hpt ρ z)) = ρ := by
  unfold cylR
  have h0 : (WithLp.ofLp (hpt ρ z)) 0 = ρ := rfl
  have h1 : (WithLp.ofLp (hpt ρ z)) 1 = 0 := rfl
  rw [h0, h1]
  simp [Real.sqrt_sq hρ.le]

/-- `(1 + |w|)^{-(4+k)} ≤ ρ⁻³` when `ρ ≤ |w|`. -/
theorem decay_le {ρ x : ℝ} (hρ : 0 < ρ) (hx : ρ ≤ x) (k : ℕ) :
    (1 + x) ^ (-(4 + (k : ℝ))) ≤ ρ ^ (-3 : ℝ) := by
  have h1 : (1 : ℝ) ≤ 1 + x := by linarith
  calc (1 + x) ^ (-(4 + (k : ℝ))) ≤ (1 + x) ^ (-3 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le h1 (by have := k.cast_nonneg (α := ℝ); linarith)
    _ ≤ ρ ^ (-3 : ℝ) := Real.rpow_le_rpow_of_nonpos hρ (by linarith) (by norm_num)

/-- **Far decay of the zero-width Newton field** (source 4776-4791; `xsZDecay`, `xsZSmooth`):
at `ρ ≥ r₀`, `r₀² > 5ν/(6ε²)`, the value and the gradient of `W^mt_μ - W^mt_{μ+1}` at
`(ρ, 0, z')` are `≤ C ρ⁻³`. -/
theorem newton_far {c ν ε μ : ℝ} {χo : ℝ → ℝ} {M : Chart → Mat3} (hc : 0 < c) (hν : 0 < ν)
    (hε : 0 < ε) (hμ : 0 < μ) (hχ : IsOutwardCutoff χo) (hfin : OldThinFinite c ν M)
    {r₀ : ℝ} (hr₀ : 0 < r₀) (hr₀b : 5 * ν / (6 * ε ^ 2) < r₀ ^ 2) :
    ∃ C : ℝ, ∀ ρ : ℝ, r₀ ≤ ρ → ∀ z' : ℝ,
      ‖newtonField c ν ε μ χo M (hpt ρ z')‖ ≤ C * ρ ^ (-3 : ℝ) ∧
      ‖fderiv ℝ (newtonField c ν ε μ χo M) (hpt ρ z')‖ ≤ C * ρ ^ (-3 : ℝ) := by
  set Zc : Vec3 → Vec3 := youngW c ν ε μ χo M - youngW c ν ε (μ + 1) χo M with hZc
  obtain ⟨C0, hC0⟩ := xsZDecay c ν ε μ χo M hc hν hε hμ hχ hfin (r₀ ^ 2) hr₀b 0
  obtain ⟨C1, hC1⟩ := xsZDecay c ν ε μ χo M hc hν hε hμ hχ hfin (r₀ ^ 2) hr₀b 1
  have hsm := xsZSmooth c ν ε μ χo M hc hν hε hμ hχ hfin
  refine ⟨3 * (|C0| + |C1|), fun ρ hρ z' => ?_⟩
  have hρ0 : 0 < ρ := lt_of_lt_of_le hr₀ hρ
  set w := WithLp.ofLp (hpt ρ z') with hw
  have hcyl : cylR w = ρ := cylR_ofLp_hpt hρ0 z'
  have ha : r₀ ^ 2 ≤ cylR w ^ 2 := by rw [hcyl]; exact pow_le_pow_left₀ hr₀.le hρ 2
  have hwn : ρ ≤ ‖w‖ := ofLp_hpt_norm hρ0 z'
  have hp : 0 ≤ ρ ^ (-3 : ℝ) := Real.rpow_nonneg hρ0.le _
  have hpos : ∀ k : ℕ, 0 ≤ (1 + ‖w‖) ^ (-(4 + (k : ℝ))) := fun k =>
    Real.rpow_nonneg (by positivity) _
  have hb0 : ‖Zc w‖ ≤ |C0| * ρ ^ (-3 : ℝ) := by
    have := hC0 w ha
    rw [norm_iteratedFDeriv_zero] at this
    calc ‖Zc w‖ ≤ C0 * (1 + ‖w‖) ^ (-(4 + ((0 : ℕ) : ℝ))) := this
      _ ≤ |C0| * (1 + ‖w‖) ^ (-(4 + ((0 : ℕ) : ℝ))) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (hpos 0)
      _ ≤ |C0| * ρ ^ (-3 : ℝ) := mul_le_mul_of_nonneg_left (decay_le hρ0 hwn 0) (abs_nonneg _)
  have hb1 : ‖fderiv ℝ Zc w‖ ≤ |C1| * ρ ^ (-3 : ℝ) := by
    have := hC1 w ha
    rw [norm_iteratedFDeriv_one] at this
    calc ‖fderiv ℝ Zc w‖ ≤ C1 * (1 + ‖w‖) ^ (-(4 + ((1 : ℕ) : ℝ))) := this
      _ ≤ |C1| * (1 + ‖w‖) ^ (-(4 + ((1 : ℕ) : ℝ))) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (hpos 1)
      _ ≤ |C1| * ρ ^ (-3 : ℝ) := mul_le_mul_of_nonneg_left (decay_le hρ0 hwn 1) (abs_nonneg _)
  constructor
  · refine (norm_le_sum_coords _).trans ?_
    have hi : ∀ i : Fin 3, ‖newtonField c ν ε μ χo M (hpt ρ z') i‖ ≤
        (|C0| + |C1|) * ρ ^ (-3 : ℝ) := by
      intro i
      have : ‖newtonField c ν ε μ χo M (hpt ρ z') i‖ = ‖Zc w i‖ := rfl
      rw [this]
      refine (norm_le_pi_norm (Zc w) i).trans (hb0.trans ?_)
      exact mul_le_mul_of_nonneg_right (by linarith [abs_nonneg C1]) hp
    calc _ ≤ ∑ _i : Fin 3, (|C0| + |C1|) * ρ ^ (-3 : ℝ) := Finset.sum_le_sum fun i _ => hi i
      _ = 3 * (|C0| + |C1|) * ρ ^ (-3 : ℝ) := by simp [Finset.sum_const]; ring
  · have hwU : w ∈ outReg ν ε := by
      show 5 * ν / (6 * ε ^ 2) < cylR w ^ 2
      exact lt_of_lt_of_le hr₀b ha
    have hZd : HasFDerivAt Zc (fderiv ℝ Zc w) w :=
      ((hsm.differentiableOn (by simp)).differentiableAt
        ((isOpen_outReg ν ε).mem_nhds hwU)).hasFDerivAt
    have hcomp : ∀ i, HasFDerivAt (fun x => newtonField c ν ε μ χo M x i)
        ((ContinuousLinearMap.proj i).comp ((fderiv ℝ Zc w).comp
          (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).toContinuousLinearMap))
        (hpt ρ z') := fun i => by
      have h1 := hZd.comp (hpt ρ z') (PiLp.hasFDerivAt_ofLp (𝕜 := ℝ) 2 (hpt ρ z'))
      have h2 := (hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 3 => ℝ) i (Zc w)).comp
        (hpt ρ z') h1
      exact h2
    refine (norm_fderiv_le_of_comp hcomp).trans ?_
    have hi : ∀ i : Fin 3, ‖(ContinuousLinearMap.proj i).comp ((fderiv ℝ Zc w).comp
          (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).toContinuousLinearMap)‖ ≤
        (|C0| + |C1|) * ρ ^ (-3 : ℝ) := by
      intro i
      have hle : ‖(ContinuousLinearMap.proj i).comp ((fderiv ℝ Zc w).comp
          (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).toContinuousLinearMap)‖ ≤
          ‖fderiv ℝ Zc w‖ := by
        refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => ?_
        have hv : ‖WithLp.ofLp v‖ ≤ ‖v‖ :=
          (pi_norm_le_iff_of_nonneg (norm_nonneg v)).2 fun j => PiLp.norm_apply_le v j
        calc ‖(fderiv ℝ Zc w (WithLp.ofLp v)) i‖ ≤ ‖fderiv ℝ Zc w (WithLp.ofLp v)‖ :=
              norm_le_pi_norm _ i
          _ ≤ ‖fderiv ℝ Zc w‖ * ‖WithLp.ofLp v‖ := (fderiv ℝ Zc w).le_opNorm _
          _ ≤ ‖fderiv ℝ Zc w‖ * ‖v‖ := mul_le_mul_of_nonneg_left hv (norm_nonneg _)
      refine hle.trans (hb1.trans ?_)
      exact mul_le_mul_of_nonneg_right (by linarith [abs_nonneg C0]) hp
    calc _ ≤ ∑ _i : Fin 3, (|C0| + |C1|) * ρ ^ (-3 : ℝ) := Finset.sum_le_sum fun i _ => hi i
      _ = 3 * (|C0| + |C1|) * ρ ^ (-3 : ℝ) := by simp [Finset.sum_const]; ring

end ZPrimKernel

end GeomXAsm

end UnforcedLeray.Short.PartIIIb.Concrete
