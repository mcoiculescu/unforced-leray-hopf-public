import UnforcedLeray.Short.Spine.PartII
import UnforcedLeray.Short.PartI.Sub.T01

/-!
# Part II output from the Part II-b statements (task `Spine:SP-PII`)

Source of record: `the November 2 reference manuscript` (73 pages), Section
`short-bg:section` (lines 2026-2645).

`Spine.PartIIOutput` (`Short/Spine/PartII.lean`) asks, at the fixed inlet of slow age `Σ`, for the
contraction-ball background of `short-bg:result` with the regularity of `short-bg:strong` and the
datum, heat remainder and pressure. The Part II-b statements (`Short/PartII-b/StatementsNonlinear.lean`)
give:
* `IIb.BackgroundResult` (lines 2505-2524): for the growing eigenpair `q = P.mode`, every `m > 0`
  and window, a threshold `Σ₀`; at `Σ = Σ₀` a state `z` solving the projected equation with
  `‖z‖_Z ≤ C₁ν^{-k₁}e^{m/ν}ε^{3/11}` (the contraction ball, lines 2507-2520);
* `IIb.StrongRegularity` (lines 2525-2562), on that ball when `2m < 3d₋/11` (lines 2510-2512):
  `U = bgField p z` jointly smooth, `‖w‖_{W^{1,∞}}` and `sup_τ‖w(τ)‖_{11/4}` bounded by
  `C₂ν^{-k₂}e^{m/ν}ε^{3/11}`.
The two remaining inputs are stated here, at the ball state, over the same concrete objects:
* `BallB3Output` (lines 2563-2645): the datum `a_α = p.datum (p.coord z)`, the heat remainder
  `Q = U - H_ν[a] ∈ C_per H²` and the global pressure `p_U = Σ R_iR_j(U_iU_j) ∈ L²` with the
  equation, i.e. Theorem B3's output (`Blueprint.IsB3Output`) for the ball state (task
  `Spine:SP-PII/1`; this is the assembly of `PartII-b:B4` at the given state, plus the pressure);
* `BallRepairRegularity` (lines 2524-2562, 1219, 2556): the repair `w = p.corr z` is jointly smooth
  through the axis and `‖D^jw‖_{𝒴_{11/4}} ≤ P_νe^{m/ν}ε^{3/11}`, `j = 1, 2` (task `Spine:SP-PII/2`).

`partIIOutput_of` composes them with the threshold `m₀ = d₋/10` (so `2m < 3d₋/11`), `Σ = Σ₀` of
`BackgroundResult` at `m`, `P_ν = Cν^{-N}` with `C`, `N` the maxima (sums) of the constants and
`ν₀ ≤ 1`. The parameter record of the level is `levelParams P ν ε Σ T`; its regime
`IIb.BgRegime` holds with `d = -ν log ε` (`ε = e^{-d/ν}`, `c = Train.per ν = ν^{-2}`, the BUC
train, its smooth stream `PartI.TrainStreamSmooth`). The unconditional `partIIOutput` is the task
`Spine:SP-PII` (`Short/Spine/Proofs/PartIIOutput.lean`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Short.Spine.SPPII

open UnforcedLeray UnforcedLeray.Blueprint UnforcedLeray.Blueprint.Planar
open UnforcedLeray.Cons.C03.Concrete (Params)

/-- **Theorem B3's output at the contraction-ball state** (lines 2563-2645: the datum
`a_r = (R/ϱ)(-ψ_{in,η})`, `a_z = (R/ϱ)[ψ_{in,q} + ε(ψ_in - ηψ_{in,η})]`, lines 2563-2583; the heat
remainder `Q = U - H_ν[a] ∈ C_per H²`, `short-bg:raw-heat` at 2601, lines 2584-2640; the global
pressure `p_U = Σ_{i,j}R_iR_j(U_iU_j) ∈ C_per L²` recovering the gradient part of the projected
equation, lines 2641-2642; the background of the ball, lines 2505-2524). At the fixed slow age
`Σ` and growing eigenpair `q = p.mode`, for `2m < 3d₋/11` (the contraction condition, lines
2510-2512) and every ball constant `C₁ν^{-k₁}`, for small `ν`: every solution `z` of the projected
equation in the ball has the B3 output with the datum `a_α = p.datum (p.coord z)`. -/
def BallB3Output : Prop :=
  ∀ (Sig : ℝ) (lam : ℂ) (q : Profile), 0 < Sig → IsGrowingEigenpair lam q →
  ∀ m : ℝ, 0 < m → ∀ dm dp : ℝ, 0 < dm → 2 * m < 3 * dm / 11 → ∀ (C₁ : ℝ) (k₁ : ℕ), 0 < C₁ →
    ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), IIb.BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig → p.mode = q →
      ∀ z : p.Z, IIb.ProjectedEquation p z →
      ‖z‖ ≤ C₁ * (p.ν ^ k₁)⁻¹ * Real.exp (m / p.ν) * p.ε ^ (3 / 11 : ℝ) →
      ∃ (Q : ℝ → SobolevGraph.H2) (pres : ℝ → Space → ℝ),
        IsB3Output p.ν p.period (p.datum (p.coord z)) (IIb.bgField p z) Q pres

/-- **The regularity of the repair at the contraction-ball state** (`short-bg:strong` and all
spatial orders, lines 2524-2562: "`D^jw` in `Y_p`", "This proves all spatial orders", "so `U` is
jointly smooth through the axis"; `U_raw` smooth through the axis, line 1219; the inlet cutoff
vanishes near the axis, line 2556; the norms `‖D^jr_b‖_{𝒴_{11/4}}`, `j = 1, 2`, of lines 5131-5134,
phase-normalized, hence the factor `P^{4/11}` on the slab). At the fixed slow age `Σ` and growing
eigenpair `q = p.mode`, for `2m < 3d₋/11` and every ball constant, for small `ν`: the repair
`w = p.corr z` of every solution in the ball is jointly smooth in `(τ, y)` and its first and second
spatial derivatives are in `L^{11/4}` of the period slab with norm
`≤ P^{4/11}C₂ν^{-k₂}e^{m/ν}ε^{3/11}`. -/
def BallRepairRegularity : Prop :=
  ∀ (Sig : ℝ) (lam : ℂ) (q : Profile), 0 < Sig → IsGrowingEigenpair lam q →
  ∀ m : ℝ, 0 < m → ∀ dm dp : ℝ, 0 < dm → 2 * m < 3 * dm / 11 → ∀ (C₁ : ℝ) (k₁ : ℕ), 0 < C₁ →
    ∃ (C₂ : ℝ) (k₂ : ℕ) (ν₀ : ℝ), 0 < C₂ ∧ 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), IIb.BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig → p.mode = q →
      ∀ z : p.Z, IIb.ProjectedEquation p z →
      ‖z‖ ≤ C₁ * (p.ν ^ k₁)⁻¹ * Real.exp (m / p.ν) * p.ε ^ (3 / 11 : ℝ) →
      ContDiff ℝ ∞ (fun x : SpaceTime => p.corr z x.1 x.2) ∧
      ∀ j : ℕ, 1 ≤ j → j ≤ 2 →
        MemLp (fun x : SpaceTime => iteratedFDeriv ℝ j (p.corr z x.1) x.2) (11 / 4 : ℝ≥0∞)
            (volume.restrict (periodSlab p.period)) ∧
          (eLpNorm (fun x : SpaceTime => iteratedFDeriv ℝ j (p.corr z x.1) x.2) (11 / 4 : ℝ≥0∞)
            (volume.restrict (periodSlab p.period))).toReal ≤
            p.period ^ ((4 : ℝ) / 11) *
              (C₂ * (p.ν ^ k₂)⁻¹ * Real.exp (m / p.ν) * p.ε ^ (3 / 11 : ℝ))

/-- A loss with smaller constant and degree is below `lossRadius` for `0 < ν ≤ 1`. -/
private theorem le_lossRadius {C' C ν ε m : ℝ} {k N : ℕ} (hC : C' ≤ C) (hC' : 0 ≤ C')
    (hν : 0 < ν) (hν1 : ν ≤ 1) (hε : 0 ≤ ε) (hk : k ≤ N) :
    C' * (ν ^ k)⁻¹ * Real.exp (m / ν) * ε ^ (3 / 11 : ℝ) ≤ lossRadius ν ε m C N := by
  unfold lossRadius
  have h1 : (ν ^ k)⁻¹ ≤ (ν ^ N)⁻¹ :=
    inv_anti₀ (pow_pos hν N) (pow_le_pow_of_le_one hν.le hν1 hk)
  have h2 : 0 ≤ Real.exp (m / ν) * ε ^ (3 / 11 : ℝ) :=
    mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hε _)
  have h3 : C' * (ν ^ k)⁻¹ ≤ C * (ν ^ N)⁻¹ :=
    mul_le_mul hC h1 (inv_nonneg.2 (pow_pos hν k).le) (le_trans hC' hC)
  calc C' * (ν ^ k)⁻¹ * Real.exp (m / ν) * ε ^ (3 / 11 : ℝ)
      = C' * (ν ^ k)⁻¹ * (Real.exp (m / ν) * ε ^ (3 / 11 : ℝ)) := by ring
    _ ≤ C * (ν ^ N)⁻¹ * (Real.exp (m / ν) * ε ^ (3 / 11 : ℝ)) :=
        mul_le_mul_of_nonneg_right h3 h2
    _ = C * (ν ^ N)⁻¹ * Real.exp (m / ν) * ε ^ (3 / 11 : ℝ) := by ring

/-- The phase slices of a jointly smooth field are smooth. -/
private theorem slice_contDiff {f : ℝ → SpatialField}
    (hf : ContDiff ℝ ∞ (fun x : SpaceTime => f x.1 x.2)) (τ : ℝ) : ContDiff ℝ ∞ (f τ) := by
  have h1 : ContDiff ℝ ∞
      ((fun x : SpaceTime => f x.1 x.2) ∘ fun y : Space => ((τ, y) : SpaceTime)) :=
    hf.comp (contDiff_const.prodMk contDiff_id)
  exact h1

/-- `(11/4 : ℝ≥0∞)` is `ENNReal.ofReal bgp`. -/
private theorem bgp_eq : ENNReal.ofReal IIb.bgp = (11 / 4 : ℝ≥0∞) := by
  rw [IIb.bgp, ENNReal.ofReal_div_of_pos (by norm_num)]
  norm_num

/-- **`Spine.PartIIOutput` from the Part II-b statements** (lines 2026-2645). -/
theorem partIIOutput_of (hR : IIb.BackgroundResult) (hS : IIb.StrongRegularity)
    (hB3 : BallB3Output) (hReg : BallRepairRegularity) (hTS : PartI.TrainStreamSmooth) :
    PartIIOutput := by
  intro P hP dLo dHi hdLo hdle
  have hq := hP.eigenpair
  refine ⟨dLo / 10, by positivity, fun m hm hmle => ?_⟩
  have h2m : 2 * m < 3 * dLo / 11 := by linarith
  obtain ⟨Sig, hSig, hRS⟩ := hR P.eigenvalue P.mode hq m hm dLo dHi hdLo
  obtain ⟨C₁, k₁, ν₁, hC₁, hν₁, hball⟩ := hRS Sig le_rfl
  obtain ⟨C₂, k₂, ν₂, hC₂, hν₂, hstrong⟩ :=
    hS Sig P.eigenvalue P.mode hSig hq m hm dLo dHi hdLo h2m C₁ k₁ hC₁
  obtain ⟨ν₃, hν₃, hb3⟩ := hB3 Sig P.eigenvalue P.mode hSig hq m hm dLo dHi hdLo h2m C₁ k₁ hC₁
  obtain ⟨C₄, k₄, ν₄, hC₄, hν₄, hreg4⟩ :=
    hReg Sig P.eigenvalue P.mode hSig hq m hm dLo dHi hdLo h2m C₁ k₁ hC₁
  refine ⟨Sig, hSig, min (min ν₁ ν₂) (min (min ν₃ ν₄) 1), max C₁ (max C₂ C₄), k₁ + k₂ + k₄,
    lt_min (lt_min hν₁ hν₂) (lt_min (lt_min hν₃ hν₄) one_pos),
    lt_of_lt_of_le hC₁ (le_max_left _ _), ?_⟩
  intro ν hν ε hε hd T hT
  have hν0 : 0 < ν := hν.1
  have hνa : ν ≤ min ν₁ ν₂ := le_trans hν.2 (min_le_left _ _)
  have hνb : ν ≤ min (min ν₃ ν₄) 1 := le_trans hν.2 (min_le_right _ _)
  have hν1' : ν ≤ ν₁ := le_trans hνa (min_le_left _ _)
  have hν2' : ν ≤ ν₂ := le_trans hνa (min_le_right _ _)
  have hν3' : ν ≤ ν₃ := le_trans hνb (le_trans (min_le_left _ _) (min_le_left _ _))
  have hν4' : ν ≤ ν₄ := le_trans hνb (le_trans (min_le_left _ _) (min_le_right _ _))
  have hνone : ν ≤ 1 := le_trans hνb (min_le_right _ _)
  have hc : 0 < Train.per ν := by unfold Train.per; positivity
  have hCC₁ : C₁ ≤ max C₁ (max C₂ C₄) := le_max_left _ _
  have hCC₂ : C₂ ≤ max C₁ (max C₂ C₄) := le_trans (le_max_left _ _) (le_max_right _ _)
  have hCC₄ : C₄ ≤ max C₁ (max C₂ C₄) := le_trans (le_max_right _ _) (le_max_right _ _)
  have hk₁ : k₁ ≤ k₁ + k₂ + k₄ := by omega
  have hk₂ : k₂ ≤ k₁ + k₂ + k₄ := by omega
  have hk₄ : k₄ ≤ k₁ + k₂ + k₄ := by omega
  -- the parameter record of the level and its regime (lines 2031-2040)
  let p : Params := levelParams P hν0 hε hSig T
  have hreg : IIb.BgRegime p (-ν * Real.log ε) dLo dHi :=
    { dm_pos := hdLo
      dm_le := hd.1
      le_dp := hd.2
      eps_eq := by
        show ε = Real.exp (-(-ν * Real.log ε) / ν)
        rw [show -(-ν * Real.log ε) / ν = Real.log ε by field_simp, Real.exp_log hε]
      c_eq := by
        show Train.per ν = (ν ^ 2)⁻¹
        simp [Train.per, inv_pow]
      train_buc := hT
      train_stream_smooth := hTS ν (Train.per ν) hν0 hc T hT }
  -- the contraction-ball state (lines 2505-2524) and its regularity (lines 2525-2645)
  obtain ⟨z, hz, hzn⟩ := hball p _ hreg hν1' rfl rfl
  obtain ⟨Q, pres, hB3z⟩ := hb3 p _ hreg hν3' rfl rfl z hz hzn
  obtain ⟨hsm, -, -, -, hsup, hLp, -⟩ := hstrong p _ hreg hν2' rfl rfl z hz hzn
  obtain ⟨hrbsm, hder⟩ := hreg4 p _ hreg hν4' rfl rfl z hz hzn
  refine ⟨⟨p, z, p.datum (p.coord z), Q, pres⟩, rfl, ?_⟩
  have hL : ∀ {C' : ℝ} {k : ℕ}, C' ≤ max C₁ (max C₂ C₄) → 0 ≤ C' → k ≤ k₁ + k₂ + k₄ →
      C' * (ν ^ k)⁻¹ * Real.exp (m / ν) * ε ^ (3 / 11 : ℝ) ≤
        lossRadius ν ε m (max C₁ (max C₂ C₄)) (k₁ + k₂ + k₄) :=
    fun hC hC' hk => le_lossRadius hC hC' hν0 hνone hε.le hk
  exact
    { nu_eq := rfl
      eps_eq := rfl
      c_eq := rfl
      ageCut_eq := rfl
      mode_eq := rfl
      train_buc := hT
      equation := hz
      ball := le_trans hzn (hL hCC₁ hC₁.le hk₁)
      b3 := hB3z
      smooth := hsm
      rb_smooth := hrbsm
      rb_sup := fun τ y =>
        ⟨le_trans (hsup τ y).1 (hL hCC₂ hC₂.le hk₂), le_trans (hsup τ y).2 (hL hCC₂ hC₂.le hk₂)⟩
      rb_Lp := fun τ => by
        have hle := hLp τ
        rw [bgp_eq] at hle
        have hX : 0 ≤ C₂ * (ν ^ k₂)⁻¹ * Real.exp (m / ν) * ε ^ (3 / 11 : ℝ) := by
          have := Real.rpow_nonneg hε.le (3 / 11 : ℝ)
          have := (Real.exp_pos (m / ν)).le
          have := inv_nonneg.2 (pow_pos hν0 k₂).le
          positivity
        refine ⟨⟨((slice_contDiff hrbsm τ).continuous).aestronglyMeasurable,
          lt_of_le_of_lt hle ENNReal.ofReal_lt_top⟩, ?_⟩
        exact le_trans (ENNReal.toReal_le_of_le_ofReal hX hle) (hL hCC₂ hC₂.le hk₂)
      rb_derivatives := fun j hj1 hj2 => by
        obtain ⟨hmem, hbd⟩ := hder j hj1 hj2
        refine ⟨hmem, le_trans hbd ?_⟩
        exact mul_le_mul_of_nonneg_left (hL hCC₄ hC₄.le hk₄)
          (Real.rpow_nonneg (Cons.C03.Concrete.Params.period_pos p).le _) }

end UnforcedLeray.Short.Spine.SPPII
