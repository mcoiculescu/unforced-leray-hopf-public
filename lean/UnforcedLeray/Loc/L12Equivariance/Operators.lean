import UnforcedLeray.Loc.L12Equivariance.Rotation
import UnforcedLeray.Loc.L08Green.Algebra

/-!
# L12 helper: operators commuting with `E` commute with `P₊`, `Π₊` and `𝓡_β`

`paper/main.tex` lines 563–567 (step L12, blueprint unit B1025): the action "commutes with …
`𝓑_*`, its evolution, the monodromy and its spectral projections, and `𝓡_β`". Here `A` is any
bounded operator on `X` commuting with `E(τ,s)` (`CommutesWithE`), and `A_Z` a bounded
operator on `Z` with `ι_Z A_Z = A ι_Z`. From the clauses of the linear steps only:

* `A` commutes with `𝓜`, with `P₊` (the commutant clause of `IsSpectralSplitting`), with
  `N = 𝓜₊⁻¹P₊` (`comm_MplusInv`, pure algebra) and with `Π₊(τ) = E(θ,0) N E(𝒯,θ)`;
* uniqueness in `𝒵_β` (lines 410–417): a weighted `Z`-curve `d` that is a mild solution of
  the homogeneous equation on `(-∞, τ₀]` with `Π₊(τ₀) d(τ₀) = 0` vanishes
  (`eq_zero_of_homogeneous_green`). The stable part is killed by `loc:eq:past-bound` and
  `β₋ < β`, the exterior part by the left inverse `E₊(τ,τ₀)Π₊(τ₀) E(τ₀,τ) Π₊(τ) = Π₊(τ)`
  (`backwardExterior_mul_E_mul_proj`,

* hence `𝓡_β(τ₀)` commutes with the pointwise actions on `𝒳_β(τ₀)`, `𝒵_β(τ₀)`
  (`green_comm`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal Topology BoundedContinuousFunction

namespace UnforcedLeray.Blueprint.L12

open SobolevGraph
open UnforcedLeray.Blueprint.L08Green (phaseOf_nonneg phaseOf_le N_mul_M
  backwardExterior_mul_E_mul_proj backwardExterior_self)

/-! ## Pointwise actions on `𝒳_β`, `𝒵_β` -/

/-- The pointwise action of `A` on `𝒳_β(τ₀)`. -/
def liftX (τ₀ : ℝ) (A : X →L[ℝ] X) : WeightedX τ₀ →L[ℝ] WeightedX τ₀ :=
  A.compLeftContinuousBounded (Iic τ₀)

/-- The pointwise action of `A` on `𝒵_β(τ₀)`. -/
def liftZ (τ₀ : ℝ) (A : Z →L[ℝ] Z) : WeightedZ τ₀ →L[ℝ] WeightedZ τ₀ :=
  A.compLeftContinuousBounded (Iic τ₀)

theorem liftX_apply (τ₀ : ℝ) (A : X →L[ℝ] X) (F : WeightedX τ₀) (τ : Iic τ₀) :
    liftX τ₀ A F τ = A (F τ) := rfl

theorem liftZ_apply (τ₀ : ℝ) (A : Z →L[ℝ] Z) (w : WeightedZ τ₀) (τ : Iic τ₀) :
    liftZ τ₀ A w τ = A (w τ) := rfl

theorem unweightX_liftX {τ₀ : ℝ} (β : ℝ) (A : X →L[ℝ] X) (F : WeightedX τ₀) (r : ℝ) :
    unweightX β (liftX τ₀ A F) r = A (unweightX β F r) := by
  unfold unweightX
  split_ifs
  · rw [liftX_apply, map_smul]
  · rw [map_zero]

theorem unweight_liftZ {τ₀ : ℝ} (β : ℝ) (A : Z →L[ℝ] Z) (w : WeightedZ τ₀) (r : ℝ) :
    unweight β (liftZ τ₀ A w) r = A (unweight β w r) := by
  unfold unweight
  split_ifs
  · rw [liftZ_apply, map_smul]
  · rw [map_zero]

theorem unweight_sub {τ₀ : ℝ} (β : ℝ) (w₁ w₂ : WeightedZ τ₀) (r : ℝ) :
    unweight β (w₁ - w₂) r = unweight β w₁ r - unweight β w₂ r := by
  unfold unweight
  split_ifs
  · rw [← smul_sub]
    rfl
  · rw [sub_zero]

theorem norm_liftZ {τ₀ : ℝ} (A : Z →L[ℝ] Z) (hA : ∀ z, ‖A z‖ = ‖z‖) (w : WeightedZ τ₀) :
    ‖liftZ τ₀ A w‖ = ‖w‖ := by
  let w' : Iic τ₀ →ᵇ Z := w
  let v' : Iic τ₀ →ᵇ Z := liftZ τ₀ A w
  have hv : ∀ τ, v' τ = A (w' τ) := fun τ => rfl
  show ‖v'‖ = ‖w'‖
  apply le_antisymm
  · refine (BoundedContinuousFunction.norm_le (norm_nonneg _)).mpr (fun τ => ?_)
    rw [hv, hA]
    exact BoundedContinuousFunction.norm_coe_le_norm w' τ
  · refine (BoundedContinuousFunction.norm_le (norm_nonneg _)).mpr (fun τ => ?_)
    rw [← hA, ← hv]
    exact BoundedContinuousFunction.norm_coe_le_norm v' τ

theorem ιZ_inj : Function.Injective ιZ := fun a b h =>
  Zclass_injective (by rw [← Xclass_ιZ, ← Xclass_ιZ, h])

/-! ## Commuting with the monodromy and its projections -/

/-- `A` commutes with every `E(τ,s)`, `s ≤ τ`. -/
def CommutesWithE (ev : Evolution) (A : X →L[ℝ] X) : Prop :=
  ∀ s τ, s ≤ τ → ∀ f, ev.E τ s (A f) = A (ev.E τ s f)

variable {D : BackgroundData} {c : Coefficients} {S : FreeEvolution} {ev : Evolution}
  {sp : SpectralSplitting X}

theorem comm_monodromy (hP : 0 < D.period) {A : X →L[ℝ] X} (hA : CommutesWithE ev A) :
    A * monodromy D ev = monodromy D ev * A := by
  ext f
  exact (hA 0 D.period hP.le f).symm

/-- `A 𝓜₊⁻¹P₊ = 𝓜₊⁻¹P₊ A` for `A` in the commutant of `𝓜`. -/
theorem comm_MplusInv (hsp : IsSpectralSplitting (monodromy D ev) D.period D.σ sp)
    {A : X →L[ℝ] X} (hAM : A * monodromy D ev = monodromy D ev * A) :
    A * sp.MplusInv = sp.MplusInv * A := by
  have hAP : A * sp.Pplus = sp.Pplus * A := hsp.commutant A hAM
  have hNP : sp.MplusInv * sp.Pplus = sp.MplusInv := hsp.inverse_kernel
  have hPN : sp.Pplus * sp.MplusInv = sp.MplusInv := hsp.inverse_range
  have hMN : monodromy D ev * sp.MplusInv = sp.Pplus := hsp.inverse_right
  have hNM : sp.MplusInv * monodromy D ev = sp.Pplus := N_mul_M hsp
  symm
  calc sp.MplusInv * A = sp.MplusInv * sp.Pplus * A := by rw [hNP]
    _ = sp.MplusInv * (A * sp.Pplus) := by rw [mul_assoc, hAP]
    _ = sp.MplusInv * A * (monodromy D ev * sp.MplusInv) := by rw [hMN, mul_assoc]
    _ = sp.MplusInv * monodromy D ev * A * sp.MplusInv := by
        rw [← mul_assoc, mul_assoc sp.MplusInv A, hAM, ← mul_assoc]
    _ = sp.Pplus * A * sp.MplusInv := by rw [hNM]
    _ = A * (sp.Pplus * sp.MplusInv) := by rw [← hAP, mul_assoc]
    _ = A * sp.MplusInv := by rw [hPN]

theorem comm_exteriorProjection (hP : 0 < D.period) {A N : X →L[ℝ] X}
    (hA : CommutesWithE ev A) (hN : A * N = N * A) (τ : ℝ) (f : X) :
    exteriorProjection D.period ev N τ (A f) = A (exteriorProjection D.period ev N τ f) := by
  have hNf : ∀ y, N (A y) = A (N y) := fun y => by
    have h := congrArg (fun T : X →L[ℝ] X => T y) hN
    exact h.symm
  simp only [exteriorProjection, ContinuousLinearMap.comp_apply]
  rw [hA _ _ (phaseOf_le hP τ) f, hNf, hA _ _ (phaseOf_nonneg hP τ)]

/-! ## Uniqueness of the Green solution in `𝒵_β` -/

variable {EplusZ : BackwardLift}

/-- A weighted `Z`-curve on `(-∞, τ₀]` that is a mild solution of `∂_τ z = 𝓛_* z` with
`Π₊(τ₀) z(τ₀) = 0` vanishes (lines 410–417). -/
theorem eq_zero_of_homogeneous_green (hP : 0 < D.period) (hev : IsEvolution D c S ev)
    (hsp : IsSpectralSplitting (monodromy D ev) D.period D.σ sp)
    (hpp : IsPhaseProjections D ev sp EplusZ) {τ₀ : ℝ} (d : WeightedZ τ₀)
    (hmild : ∀ s τ, s ≤ τ → τ ≤ τ₀ →
      ιZ (unweight sp.β d τ) = ev.E τ s (ιZ (unweight sp.β d s)))
    (hterm : exteriorProjection D.period ev sp.MplusInv τ₀ (ιZ (unweight sp.β d τ₀)) = 0) :
    d = 0 := by
  refine BoundedContinuousFunction.ext (fun τ' => ?_)
  obtain ⟨τ, hτ⟩ := τ'
  have hτ' : τ ≤ τ₀ := hτ
  -- the exterior part
  have hext : exteriorProjection D.period ev sp.MplusInv τ (ιZ (unweight sp.β d τ)) = 0 := by
    have h1 := backwardExterior_mul_E_mul_proj hev hsp hP (r := τ) (s := τ) (s₁ := τ₀) le_rfl hτ'
    rw [backwardExterior_self] at h1
    have h2 : exteriorProjection D.period ev sp.MplusInv τ (ιZ (unweight sp.β d τ)) =
        backwardExterior D.period ev sp.MplusInv τ τ₀ (ev.E τ₀ τ
          (exteriorProjection D.period ev sp.MplusInv τ (ιZ (unweight sp.β d τ)))) := by
      have := congrArg (fun T : X →L[ℝ] X => T (ιZ (unweight sp.β d τ))) h1
      exact this.symm
    have h3 : ev.E τ₀ τ (exteriorProjection D.period ev sp.MplusInv τ (ιZ (unweight sp.β d τ)))
        = exteriorProjection D.period ev sp.MplusInv τ₀ (ev.E τ₀ τ (ιZ (unweight sp.β d τ))) :=
      congrArg (fun T : X →L[ℝ] X => T (ιZ (unweight sp.β d τ))) (hpp.intertwine τ τ₀ hτ')
    rw [h2, h3, ← hmild τ τ₀ hτ' le_rfl, hterm, map_zero]
  -- the stable part
  have hstab : ιZ (unweight sp.β d τ) -
      exteriorProjection D.period ev sp.MplusInv τ (ιZ (unweight sp.β d τ)) = 0 := by
    obtain ⟨C, hC⟩ := hpp.past_bound
    have hbound : ∀ s, s ≤ τ - 1 → ‖ιZ (unweight sp.β d τ) -
        exteriorProjection D.period ev sp.MplusInv τ (ιZ (unweight sp.β d τ))‖ ≤
        (max C 0 * 2 * ‖ιZ‖ * ‖ιZ‖ * ‖d‖ * Real.exp (sp.βminus * τ)) *
          Real.exp ((sp.β - sp.βminus) * s) := by
      intro s hs
      have hsτ : s < τ := by linarith
      have hsτ₀ : s ≤ τ₀ := by linarith
      have hx : ιZ (unweight sp.β d τ) -
          exteriorProjection D.period ev sp.MplusInv τ (ιZ (unweight sp.β d τ)) =
          ιZ (ev.EZ τ s ((1 - exteriorProjection D.period ev sp.MplusInv s)
            (ιZ (unweight sp.β d s)))) := by
        have e1 : ιZ (ev.EZ τ s ((1 - exteriorProjection D.period ev sp.MplusInv s)
            (ιZ (unweight sp.β d s)))) = ev.E τ s ((1 - exteriorProjection D.period ev
              sp.MplusInv s) (ιZ (unweight sp.β d s))) := by
          rw [← hev.EZ_compat s τ hsτ]
          rfl
        have e2 : ev.E τ s (exteriorProjection D.period ev sp.MplusInv s
            (ιZ (unweight sp.β d s))) = exteriorProjection D.period ev sp.MplusInv τ
              (ev.E τ s (ιZ (unweight sp.β d s))) :=
          congrArg (fun T : X →L[ℝ] X => T (ιZ (unweight sp.β d s))) (hpp.intertwine s τ hsτ.le)
        rw [e1, ContinuousLinearMap.sub_apply, map_sub, e2, ContinuousLinearMap.one_apply,
          ← hmild s τ hsτ.le hτ']
      have hus : ‖ιZ (unweight sp.β d s)‖ ≤ ‖ιZ‖ * (Real.exp (sp.β * s) * ‖d‖) :=
        (ιZ.le_opNorm _).trans
          (mul_le_mul_of_nonneg_left (norm_unweight_le sp.β d hsτ₀) (norm_nonneg _))
      have hsq : 1 / Real.sqrt (τ - s) ≤ 1 := by
        rw [div_le_one (Real.sqrt_pos.mpr (by linarith))]
        exact Real.one_le_sqrt.mpr (by linarith)
      have hP0 : 0 ≤ (1 + 1 / Real.sqrt (τ - s)) * Real.exp (sp.βminus * (τ - s)) := by
        positivity
      have hEZ : ‖(ev.EZ τ s).comp (1 - exteriorProjection D.period ev sp.MplusInv s)‖ ≤
          max C 0 * 2 * Real.exp (sp.βminus * (τ - s)) := by
        refine (hC s τ hsτ).trans ?_
        calc C * (1 + 1 / Real.sqrt (τ - s)) * Real.exp (sp.βminus * (τ - s))
            = C * ((1 + 1 / Real.sqrt (τ - s)) * Real.exp (sp.βminus * (τ - s))) := by ring
          _ ≤ max C 0 * ((1 + 1 / Real.sqrt (τ - s)) * Real.exp (sp.βminus * (τ - s))) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) hP0
          _ ≤ max C 0 * (2 * Real.exp (sp.βminus * (τ - s))) := by
            refine mul_le_mul_of_nonneg_left ?_ (le_max_right _ _)
            exact mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
          _ = max C 0 * 2 * Real.exp (sp.βminus * (τ - s)) := by ring
      have hexp : Real.exp (sp.βminus * (τ - s)) * Real.exp (sp.β * s) =
          Real.exp (sp.βminus * τ) * Real.exp ((sp.β - sp.βminus) * s) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      rw [hx]
      calc ‖ιZ (ev.EZ τ s ((1 - exteriorProjection D.period ev sp.MplusInv s)
              (ιZ (unweight sp.β d s))))‖
          ≤ ‖ιZ‖ * (‖(ev.EZ τ s).comp (1 - exteriorProjection D.period ev sp.MplusInv s)‖ *
              ‖ιZ (unweight sp.β d s)‖) := by
            refine (ιZ.le_opNorm _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
            exact ((ev.EZ τ s).comp (1 - exteriorProjection D.period ev sp.MplusInv s)).le_opNorm
              (ιZ (unweight sp.β d s))
        _ ≤ ‖ιZ‖ * ((max C 0 * 2 * Real.exp (sp.βminus * (τ - s))) *
              (‖ιZ‖ * (Real.exp (sp.β * s) * ‖d‖))) := by
            refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
            exact mul_le_mul hEZ hus (norm_nonneg _) (by positivity)
        _ = (max C 0 * 2 * ‖ιZ‖ * ‖ιZ‖ * ‖d‖) *
              (Real.exp (sp.βminus * (τ - s)) * Real.exp (sp.β * s)) := by ring
        _ = _ := by rw [hexp]; ring
    have hlim : Tendsto (fun s => (max C 0 * 2 * ‖ιZ‖ * ‖ιZ‖ * ‖d‖ *
        Real.exp (sp.βminus * τ)) * Real.exp ((sp.β - sp.βminus) * s)) atBot (𝓝 0) := by
      have h1 : Tendsto (fun s : ℝ => (sp.β - sp.βminus) * s) atBot atBot :=
        Tendsto.const_mul_atBot (by linarith [hsp.rate_lower]) tendsto_id
      have h2 := (Real.tendsto_exp_atBot.comp h1).const_mul
        (max C 0 * 2 * ‖ιZ‖ * ‖ιZ‖ * ‖d‖ * Real.exp (sp.βminus * τ))
      simpa using h2
    have h0 := ge_of_tendsto hlim ((eventually_le_atBot (τ - 1)).mono fun s hs => hbound s hs)
    exact norm_le_zero_iff.mp h0
  have hu0 : ιZ (unweight sp.β d τ) = 0 := by
    have := hstab
    rwa [hext, sub_zero] at this
  have hw : unweight sp.β d τ = 0 := ιZ_inj (by rw [map_zero]; exact hu0)
  rw [unweight_of_le sp.β d hτ'] at hw
  rcases smul_eq_zero.mp hw with h | h
  · exact absurd h (Real.exp_pos _).ne'
  · exact h

/-- `𝓡_β(τ₀)` commutes with the pointwise actions of `A` and `A_Z`. -/
theorem green_comm (hP : 0 < D.period) (hev : IsEvolution D c S ev)
    (hsp : IsSpectralSplitting (monodromy D ev) D.period D.σ sp)
    (hpp : IsPhaseProjections D ev sp EplusZ) {R : GreenFamily} (hR : IsGreenOperator D ev sp R)
    (A : X →L[ℝ] X) (AZ : Z →L[ℝ] Z) (hι : ∀ z, ιZ (AZ z) = A (ιZ z))
    (hA : CommutesWithE ev A) {τ₀ : ℝ} (hτ₀ : τ₀ ≤ 0) (F : WeightedX τ₀) :
    R τ₀ (liftX τ₀ A F) = liftZ τ₀ AZ (R τ₀ F) := by
  have hN : A * sp.MplusInv = sp.MplusInv * A := comm_MplusInv hsp (comm_monodromy hP hA)
  have hz₁ : ∀ r, ιZ (unweight sp.β (liftZ τ₀ AZ (R τ₀ F)) r) =
      A (ιZ (unweight sp.β (R τ₀ F) r)) := by
    intro r
    rw [unweight_liftZ, hι]
  have hmild : ∀ s τ, s ≤ τ → τ ≤ τ₀ →
      ιZ (unweight sp.β (liftZ τ₀ AZ (R τ₀ F) - R τ₀ (liftX τ₀ A F)) τ) =
        ev.E τ s (ιZ (unweight sp.β (liftZ τ₀ AZ (R τ₀ F) - R τ₀ (liftX τ₀ A F)) s)) := by
    intro s τ hsτ hτ
    have i1 := hR.mild_integrable τ₀ hτ₀ F s τ hsτ hτ
    have e1 : A (∫ r in Ioo s τ, ev.E τ r (unweightX sp.β F r)) =
        ∫ r in Ioo s τ, ev.E τ r (unweightX sp.β (liftX τ₀ A F) r) := by
      rw [← A.integral_comp_comm i1]
      refine setIntegral_congr_fun measurableSet_Ioo (fun r hr => ?_)
      rw [unweightX_liftX, hA r τ hr.2.le]
    rw [unweight_sub, unweight_sub, map_sub, map_sub, hz₁, hz₁,
      hR.mild τ₀ hτ₀ F s τ hsτ hτ, hR.mild τ₀ hτ₀ (liftX τ₀ A F) s τ hsτ hτ, map_add,
      ← hA s τ hsτ, e1, map_sub]
    abel
  have hterm : exteriorProjection D.period ev sp.MplusInv τ₀
      (ιZ (unweight sp.β (liftZ τ₀ AZ (R τ₀ F) - R τ₀ (liftX τ₀ A F)) τ₀)) = 0 := by
    rw [unweight_sub, map_sub, map_sub, hz₁, comm_exteriorProjection hP hA hN,
      hR.terminal τ₀ hτ₀ F, hR.terminal τ₀ hτ₀ (liftX τ₀ A F), map_zero, sub_zero]
  have h0 := eq_zero_of_homogeneous_green hP hev hsp hpp _ hmild hterm
  exact (sub_eq_zero.mp h0).symm

end UnforcedLeray.Blueprint.L12
