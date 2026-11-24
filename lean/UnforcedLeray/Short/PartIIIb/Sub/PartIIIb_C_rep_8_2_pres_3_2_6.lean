import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_3_2_6.Phys
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_3_2_6.Inlet

/-!
# The entrance source bound (`PartIII-b:C/rep/8/2/pres/3/2/6`)

Source `the November 2 reference manuscript`
2346-2347 ("Its complete equation source is in `Y_p`"), 2370-2392 (`short-bg:affine`: the inlet
source has the bound `𝒫_ν R^{2/p}|α|`, the quadratic inlet source the same bound with `|α|²`,
"these assertions compare sources, never the nonintegrable inlet states"), 2513-2520
(`‖z‖_Z = ‖w‖ + R^{8/11}|α| ≤ 𝒫_ν e^{m/ν}ε^{3/11}`, so `|α| ≤ 𝒫_ν e^{m₀/ν}ε`), 5277-5279.

On an actual level `V = U_raw + E_εα`, `E_εα = Σᵢ αᵢ E_i` (`IsBallSplit`), so off the axis

  `entSrc = [D₀E_εα + E_εα·∇U_raw + U_raw·∇E_εα] + E_εα·∇E_εα`

(`ES326.esG_eq_of`), the linear inlet source `inletLinSrc` plus the quadratic one
`inletQuadSrc`.

* **Proved here:** `entSrcReg` (the regularity leaf `EntSrcRegLeaf`: `|entSrc|` is measurable off the
  axis, `P`-periodic and axisymmetric; from the joint smoothness of `U_raw` off the axis and of the
  inlets, the periodicity of the ring lifts, and their equivariance), and `entSrcLp_of` (the bound
  leaf `EntSrcLpLeaf` from `InletSrcPhys`, the algebra above, the triangle inequality and
  `R^{8/11}|α| ≤ ρ_b = C₀ν^{-k₀}ρ`, `|α| ≤ ρ_b ≤ C₀ν^{-k₀}`).
* **Remaining leaf:** `InletSrcPhys`, the physical phase-uniform `L^{11/4}(ℝ³)` form of the inlet
  source bound of `short-bg:affine` (source 2370-2392).  The compiled `IIb.InletSourceBound`
  (`Short/PartII-b/Sub/G4.lean:92`) is the weak `Y`-norm statement (phase-averaged, tested against
  solenoidal phase tests, about a representative `g` of the projected source), from which the
  pointwise-in-phase physical bound of the unprojected source does not follow.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

/-! ## The two leaves of `EntSrcAt` -/

/-- Regularity part of `EntSrcAt` along the sequence. -/
def EntSrcRegLeaf (D : SeqData) {dm dp : ℝ} (_hst : D.RepairStanding dm dp) : Prop :=
  ∀ᶠ n : ℕ in atTop,
    Measurable (axisZero fun τ y => ‖entSrc D.Pl (D.level n) τ y‖) ∧
    (∀ τ y, ‖entSrc D.Pl (D.level n) (τ + 2 * (D.level n).ε * cOf (D.level n).ν) y‖ =
      ‖entSrc D.Pl (D.level n) τ y‖) ∧
    IsAxiScalar (fun τ y => ‖entSrc D.Pl (D.level n) τ y‖)

/-- Bound part of `EntSrcAt` along the sequence. -/
def EntSrcLpLeaf (D : SeqData) {dm dp : ℝ} (_hst : D.RepairStanding dm dp) : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ τ,
    eLpNorm (entSrc D.Pl (D.level n) τ) (11 / 4) volume ≤
      ENNReal.ofReal (C * (D.level n).ν⁻¹ ^ k * rhoRep D.K (D.level n))

theorem entSrc_of (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp)
    (h1 : EntSrcRegLeaf D hst) (h2 : EntSrcLpLeaf D hst) : D.EntSrc := by
  obtain ⟨C, k, h⟩ := h2
  exact ⟨C, k, by filter_upwards [h1, h] with n a b
                  exact ⟨a.1, a.2.1, a.2.2, b⟩⟩

/-! ## The regularity leaf (proved) -/

namespace ES326

/-- The regularity of `|entSrc|` at one level, from the split `V = U_raw + Σ αᵢE_i` and the
smoothness of `U_raw` (off the axis) and of the inlets. -/
theorem reg_of (p : UnforcedLeray.Cons.C03.Concrete.Params) (α : Fin 2 → ℝ)
    (V : ℝ → Space → Space)
    (hInl : ∀ i : Fin 2, ContDiff ℝ ∞ (fun x : ℝ × Space => p.inlet i x.1 x.2))
    (hRaw : ContDiffOn ℝ 2 (fun x : ℝ × Space => p.raw x.1 x.2) offAxis)
    (hV : ∀ τ y, V τ y = p.raw τ y + ∑ i : Fin 2, α i • p.inlet i τ y) :
    Measurable (axisZero fun τ y => ‖esG p.ν V p.raw τ y‖) ∧
    (∀ τ y, ‖esG p.ν V p.raw (τ + p.period) y‖ = ‖esG p.ν V p.raw τ y‖) ∧
    IsAxiScalar (fun τ y => ‖esG p.ν V p.raw τ y‖) := by
  set E : ℝ → Space → Space := fun t y => ∑ i : Fin 2, α i • p.inlet i t y with hEdef
  have hVE : ∀ t y, V t y = p.raw t y + E t y := hV
  have hEj : ContDiff ℝ ∞ (fun x : ℝ × Space => E x.1 x.2) :=
    ContDiff.sum fun i _ => (hInl i).const_smul (α i)
  have hE2 : ContDiffOn ℝ 2 (fun x : ℝ × Space => E x.1 x.2) offAxis :=
    (hEj.of_le (by norm_num)).contDiffOn
  refine ⟨?_, ?_, ?_⟩
  · exact pf4_axisZero_measurable (f := fun τ y => ‖esG p.ν V p.raw τ y‖)
      (esG_continuousOn hVE hRaw hE2).norm
  · intro τ y
    have hrp : Function.Periodic p.raw p.period := raw_add_period p
    have hEp : Function.Periodic E p.period := by
      intro t
      funext y'
      simp only [hEdef, inlet_add_period p _ t]
    have hVp : Function.Periodic V p.period := by
      intro t
      funext y'
      rw [hVE, hVE, hrp t, hEp t]
    rw [esG_add_period hVp hrp τ y]
  · intro τ y
    exact esG_norm_merPt (r' := fun t => Nv p.R
        (UnforcedLeray.Cons.C03.rawProfile p.ε p.train.v p.train.ψ) t) hVE hEj
      (fun t => axi_E p α t) (fun t => axi_Nv _ _ t)
      (fun t y' hy' => UnforcedLeray.Cons.C03.Concrete.Params.raw_eq_off_axis p t y' hy') τ y

end ES326

/-- **The regularity leaf** (source 1205-1225, 2031, 2347-2369, 4139-4141): for large `n`,
`|entSrc|` is measurable off the axis, `P`-periodic and axisymmetric. -/
theorem entSrcReg (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) :
    EntSrcRegLeaf D hst := by
  obtain ⟨ν₀, hν₀, hS⟩ := UnforcedLeray.Short.IIb.inletJointSmooth D.Sig D.Pl.eigenvalue D.Pl.mode
    D.Sig_pos hst.planar.eigenpair dm dp hst.dm_pos
  have hν : ∀ᶠ n : ℕ in atTop, retNu D.Pl D.σ₀ n < ν₀ :=
    (retNu_tendsto D.σ₀ hst.omega_ne).eventually (gt_mem_nhds hν₀)
  filter_upwards [hst.actual, hν] with n hn hνn
  obtain ⟨z, -, hVz, -, -⟩ := hn.ball
  have hInl : ∀ i : Fin 2, ContDiff ℝ ∞
      (fun x : ℝ × Space => ((D.level n).params D.Pl).inlet i x.1 x.2) :=
    fun i => hS ((D.level n).params D.Pl) _ hn.regime hνn.le rfl rfl i
  have hRaw : ContDiffOn ℝ 2
      (fun x : ℝ × Space => ((D.level n).params D.Pl).raw x.1 x.2) offAxis :=
    rawU_contDiffOn_offAxis_of ((D.level n).params D.Pl) (D.level n).ε_pos
      ((D.level n).train_stream_smooth.of_le (by norm_num))
  exact ES326.reg_of ((D.level n).params D.Pl) (fun i => ((D.level n).params D.Pl).coord z i)
    (D.V n) hInl hRaw hVz


/-! ## The bound leaf: reduction to the physical inlet source bound -/

namespace ES326

theorem aesm_slice {G : ℝ × Space → Space} (hG : ContinuousOn G offAxis) (τ : ℝ) :
    AEStronglyMeasurable (fun y => G (τ, y)) volume := by
  have hc : ContinuousOn (fun y : Space => G (τ, y)) axisᶜ :=
    hG.comp (continuous_const.prodMk continuous_id).continuousOn fun y hy => hy
  have h1 := hc.aestronglyMeasurable (μ := volume) isClosed_axis.isOpen_compl.measurableSet
  have hae : ∀ᵐ y : Space ∂volume, y ∈ axisᶜ := ae_not_mem_axis
  rwa [Measure.restrict_eq_self_of_ae_mem hae] at h1

theorem slice_diffAt {F : ℝ → Space → Space} {O : Set (ℝ × Space)} (hO : IsOpen O)
    (hF : ContDiffOn ℝ 2 (fun x : ℝ × Space => F x.1 x.2) O) {τ : ℝ} {y : Space}
    (hx : (τ, y) ∈ O) : DifferentiableAt ℝ (F τ) y := by
  have hd : DifferentiableAt ℝ (fun x : ℝ × Space => F x.1 x.2) (τ, y) :=
    (hF.differentiableOn (by norm_num)).differentiableAt (hO.mem_nhds hx)
  exact hd.comp y ((differentiableAt_const τ).prodMk differentiableAt_id)

/-- The entrance source splits a.e. into the linear and quadratic inlet sources, so its
`L^{11/4}` norm is at most the sum of theirs. -/
theorem lp_split (p : UnforcedLeray.Cons.C03.Concrete.Params) (α : Fin 2 → ℝ)
    (V : ℝ → Space → Space)
    (hInl : ∀ i : Fin 2, ContDiff ℝ ∞ (fun x : ℝ × Space => p.inlet i x.1 x.2))
    (hRaw : ContDiffOn ℝ 2 (fun x : ℝ × Space => p.raw x.1 x.2) offAxis)
    (hV : ∀ τ y, V τ y = p.raw τ y + ∑ i : Fin 2, α i • p.inlet i τ y) (τ : ℝ) :
    eLpNorm (esG p.ν V p.raw τ) (11 / 4) volume ≤
      eLpNorm (inletLinSrc p α τ) (11 / 4) volume +
        eLpNorm (inletQuadSrc p α τ) (11 / 4) volume := by
  set E : ℝ → Space → Space := fun t y => ∑ i : Fin 2, α i • p.inlet i t y with hEdef
  have hVE : ∀ t y, V t y = p.raw t y + E t y := hV
  have hEj : ContDiff ℝ ∞ (fun x : ℝ × Space => E x.1 x.2) :=
    ContDiff.sum fun i _ => (hInl i).const_smul (α i)
  have hE2 : ContDiffOn ℝ 2 (fun x : ℝ × Space => E x.1 x.2) offAxis :=
    (hEj.of_le (by norm_num)).contDiffOn
  have hlinC : ContinuousOn (fun x : ℝ × Space => inletLinSrc p α x.1 x.2) offAxis := by
    have h1 := physDmu_continuousOn isOpen_offAxis hE2 p.ν 0
    have h2 : ContinuousOn (fun x : ℝ × Space => fderiv ℝ (E x.1) x.2 (p.raw x.1 x.2))
        offAxis :=
      (fderiv_slice_continuousOn isOpen_offAxis hE2).clm_apply hRaw.continuousOn
    have h3 : ContinuousOn (fun x : ℝ × Space => fderiv ℝ (p.raw x.1) x.2 (E x.1 x.2))
        offAxis :=
      (fderiv_slice_continuousOn isOpen_offAxis hRaw).clm_apply hE2.continuousOn
    exact (h1.add (h2.add h3)).congr fun x _ => rfl
  have hquadC : ContinuousOn (fun x : ℝ × Space => inletQuadSrc p α x.1 x.2) offAxis :=
    ((fderiv_slice_continuousOn isOpen_offAxis hE2).clm_apply hE2.continuousOn).congr
      fun x _ => rfl
  have hae : esG p.ν V p.raw τ =ᵐ[volume] inletLinSrc p α τ + inletQuadSrc p α τ := by
    filter_upwards [ae_not_mem_axis] with y hy
    have hx : (τ, y) ∈ offAxis := hy
    rw [esG_eq_of hVE (slice_diffAt isOpen_offAxis hRaw hx) (slice_diffAt isOpen_offAxis hE2 hx)]
    rfl
  rw [eLpNorm_congr_ae hae]
  exact eLpNorm_add_le (aesm_slice hlinC τ) (aesm_slice hquadC τ) one_lt_elevenFourths.le

/-- `|α| ≤ ε^{8/11}‖z‖_Z` (`α = ε^{8/11}A`, source 2513-2520, `Params.coord`). -/
theorem norm_coord_le (p : UnforcedLeray.Cons.C03.Concrete.Params) (z : p.Z) :
    ‖(fun i => p.coord z i : Fin 2 → ℝ)‖ ≤ p.ε ^ (8 / 11 : ℝ) * ‖z‖ := by
  have he : 0 ≤ p.ε ^ (8 / 11 : ℝ) := Real.rpow_nonneg p.ε_pos.le _
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg he (norm_nonneg _))).2 fun i => ?_
  have hA := UnforcedLeray.Cons.C03.Concrete.norm_amb p.period
    (z : UnforcedLeray.Cons.C03.Concrete.Amb p.period)
  have h1 : ‖UnforcedLeray.Cons.C03.Concrete.cA p.period
      (z : UnforcedLeray.Cons.C03.Concrete.Amb p.period)‖ ≤ ‖z‖ := by
    have := norm_nonneg (UnforcedLeray.Cons.C03.Concrete.cw p.period
      (z : UnforcedLeray.Cons.C03.Concrete.Amb p.period))
    have := norm_nonneg (UnforcedLeray.Cons.C03.Concrete.cΔ p.period
      (z : UnforcedLeray.Cons.C03.Concrete.Amb p.period))
    have := norm_nonneg (UnforcedLeray.Cons.C03.Concrete.cT p.period
      (z : UnforcedLeray.Cons.C03.Concrete.Amb p.period))
    have hz : ‖z‖ = ‖(z : UnforcedLeray.Cons.C03.Concrete.Amb p.period)‖ := rfl
    rw [hz]
    linarith
  show ‖p.ε ^ (8 / 11 : ℝ) * (UnforcedLeray.Cons.C03.Concrete.cA p.period
      (z : UnforcedLeray.Cons.C03.Concrete.Amb p.period)) i‖ ≤ _
  rw [norm_mul, Real.norm_of_nonneg he]
  exact mul_le_mul_of_nonneg_left ((PiLp.norm_apply_le _ i).trans h1) he

/-- The numerical step: `CwᵏR^{8/11}|α|(1 + |α|) ≤ C C₀(1 + C₀)w^{k+2k₀}ρ`, `w = ν⁻¹`, from
`|α| ≤ ε^{8/11}ρ_b`, `ρ_b = C₀w^{k₀}ρ`, `R^{8/11}ε^{8/11} = 1`, `ε, ρ ≤ 1 ≤ w`. -/
theorem num_bound {C a w ρ A R e : ℝ} {k k0 : ℕ} (hC : 0 ≤ C) (ha : 0 ≤ a) (hw : 1 ≤ w)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hA0 : 0 ≤ A) (hR : 0 ≤ R) (he1 : e ≤ 1)
    (hRe : R * e = 1) (hA : A ≤ e * (a * w ^ k0 * ρ)) :
    C * w ^ k * R * A + C * w ^ k * R * A ^ 2 ≤ C * a * (1 + a) * w ^ (k + 2 * k0) * ρ := by
  have hwk : 0 ≤ w ^ k := pow_nonneg (by linarith) k
  have hwk0 : 1 ≤ w ^ k0 := one_le_pow₀ hw
  set Y := a * w ^ k0 * ρ with hYdef
  have hY0 : 0 ≤ Y := mul_nonneg (mul_nonneg ha (by linarith)) hρ0
  have hYle : Y ≤ a * w ^ k0 := mul_le_of_le_one_right (mul_nonneg ha (by linarith)) hρ1
  have h1 : R * A ≤ Y := by
    calc R * A ≤ R * (e * Y) := mul_le_mul_of_nonneg_left hA hR
      _ = (R * e) * Y := by ring
      _ = Y := by rw [hRe, one_mul]
  have hAY : A ≤ Y := hA.trans (mul_le_of_le_one_left hY0 he1)
  have h2 : 1 + A ≤ (1 + a) * w ^ k0 := by nlinarith
  have hCw : 0 ≤ C * w ^ k := mul_nonneg hC hwk
  calc C * w ^ k * R * A + C * w ^ k * R * A ^ 2 = C * w ^ k * (R * A) * (1 + A) := by ring
    _ ≤ C * w ^ k * Y * ((1 + a) * w ^ k0) :=
        mul_le_mul (mul_le_mul_of_nonneg_left h1 hCw) h2 (by linarith) (mul_nonneg hCw hY0)
    _ = C * a * (1 + a) * w ^ (k + 2 * k0) * ρ := by
        rw [hYdef, pow_add, two_mul, pow_add]
        ring

theorem eps_le_one' {ε ν d dm : ℝ} (hν : 0 < ν) (hε : ε = Real.exp (-d / ν)) (hdm : 0 < dm)
    (hd : dm ≤ d) : ε ≤ 1 := by
  rw [hε, Real.exp_le_one_iff]
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) hν.le

theorem rho_le_one' {ε ν d dm m0 : ℝ} (hν : 0 < ν) (hε : ε = Real.exp (-d / ν)) (hd : dm ≤ d)
    (hm : m0 ≤ 3 * dm / 11) : ε ^ (3 / 11 : ℝ) * Real.exp (m0 / ν) ≤ 1 := by
  rw [hε, ← Real.exp_mul, ← Real.exp_add, Real.exp_le_one_iff]
  have : -d / ν * (3 / 11) + m0 / ν = (m0 - 3 * d / 11) / ν := by
    field_simp
    ring
  rw [this]
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) hν.le

end ES326

namespace ES326

/-- The bound at one level: `‖entSrc(τ)‖_{L^{11/4}} ≤ ‖lin‖ + ‖quad‖ ≤ Cν^{-k}R^{8/11}|α|(1 + |α|)`
with `R^{8/11}|α| ≤ ρ_b = C₀ν^{-k₀}ρ`, `|α| ≤ C₀ν^{-k₀}` (source 2370-2392, 2513-2520). -/
theorem lp_level (p : UnforcedLeray.Cons.C03.Concrete.Params) (z : p.Z) (V : ℝ → Space → Space)
    {C a m0 ρb : ℝ} {k k0 : ℕ} (hC : 0 < C) (ha : 0 ≤ a)
    (hInl : ∀ i : Fin 2, ContDiff ℝ ∞ (fun x : ℝ × Space => p.inlet i x.1 x.2))
    (hRaw : ContDiffOn ℝ 2 (fun x : ℝ × Space => p.raw x.1 x.2) offAxis)
    (hV : ∀ τ y, V τ y = p.raw τ y + ∑ i : Fin 2, p.coord z i • p.inlet i τ y)
    (hz : ‖z‖ ≤ ρb)
    (hρb : ρb = a * (p.ν ^ k0)⁻¹ * Real.exp (m0 / p.ν) * p.ε ^ (3 / 11 : ℝ))
    (hν1 : p.ν ≤ 1) (hε1 : p.ε ≤ 1)
    (hρ1 : p.ε ^ (3 / 11 : ℝ) * Real.exp (m0 / p.ν) ≤ 1)
    (hB : ∀ (α : Fin 2 → ℝ) (τ : ℝ),
        eLpNorm (inletLinSrc p α τ) (11 / 4) volume ≤
            ENNReal.ofReal (C * (p.ν ^ k)⁻¹ * p.R ^ (8 / 11 : ℝ) * ‖α‖) ∧
          eLpNorm (inletQuadSrc p α τ) (11 / 4) volume ≤
            ENNReal.ofReal (C * (p.ν ^ k)⁻¹ * p.R ^ (8 / 11 : ℝ) * ‖α‖ ^ 2))
    (τ : ℝ) :
    eLpNorm (esG p.ν V p.raw τ) (11 / 4) volume ≤
      ENNReal.ofReal (C * a * (1 + a) * p.ν⁻¹ ^ (k + 2 * k0) *
        (p.ε ^ (3 / 11 : ℝ) * Real.exp (m0 / p.ν))) := by
  set α : Fin 2 → ℝ := fun i => p.coord z i with hα
  have hνpos : 0 < p.ν := p.ν_pos
  have hεpos : 0 < p.ε := p.ε_pos
  obtain ⟨hlin, hquad⟩ := hB α τ
  have hsplit := lp_split p α V hInl hRaw hV τ
  have hρ0 : 0 ≤ p.ε ^ (3 / 11 : ℝ) * Real.exp (m0 / p.ν) :=
    mul_nonneg (Real.rpow_nonneg hεpos.le _) (Real.exp_pos _).le
  have hRpos : 0 < p.R := p.R_pos
  have hRe : p.R ^ (8 / 11 : ℝ) * p.ε ^ (8 / 11 : ℝ) = 1 := by
    rw [← Real.mul_rpow hRpos.le hεpos.le]
    have : p.R * p.ε = 1 := inv_mul_cancel₀ hεpos.ne'
    rw [this, Real.one_rpow]
  have hρb' : ρb = a * p.ν⁻¹ ^ k0 * (p.ε ^ (3 / 11 : ℝ) * Real.exp (m0 / p.ν)) := by
    rw [hρb, inv_pow]
    ring
  have hA : ‖α‖ ≤ p.ε ^ (8 / 11 : ℝ) *
      (a * p.ν⁻¹ ^ k0 * (p.ε ^ (3 / 11 : ℝ) * Real.exp (m0 / p.ν))) := by
    rw [← hρb']
    exact (norm_coord_le p z).trans
      (mul_le_mul_of_nonneg_left hz (Real.rpow_nonneg hεpos.le _))
  have hnum := num_bound (C := C) (k := k) hC.le ha ((one_le_inv₀ hνpos).2 hν1) hρ0 hρ1
    (norm_nonneg α) (Real.rpow_nonneg hRpos.le _)
    (Real.rpow_le_one hεpos.le hε1 (by norm_num)) hRe hA
  have hX : 0 ≤ C * (p.ν ^ k)⁻¹ * p.R ^ (8 / 11 : ℝ) * ‖α‖ := by
    have := Real.rpow_nonneg hRpos.le (8 / 11 : ℝ)
    have := norm_nonneg α
    positivity
  have hY : 0 ≤ C * (p.ν ^ k)⁻¹ * p.R ^ (8 / 11 : ℝ) * ‖α‖ ^ 2 := by
    have := Real.rpow_nonneg hRpos.le (8 / 11 : ℝ)
    positivity
  have hinv : (p.ν ^ k)⁻¹ = p.ν⁻¹ ^ k := (inv_pow _ _).symm
  calc eLpNorm (esG p.ν V p.raw τ) (11 / 4) volume
      ≤ eLpNorm (inletLinSrc p α τ) (11 / 4) volume +
          eLpNorm (inletQuadSrc p α τ) (11 / 4) volume := hsplit
    _ ≤ ENNReal.ofReal (C * (p.ν ^ k)⁻¹ * p.R ^ (8 / 11 : ℝ) * ‖α‖) +
          ENNReal.ofReal (C * (p.ν ^ k)⁻¹ * p.R ^ (8 / 11 : ℝ) * ‖α‖ ^ 2) :=
        add_le_add hlin hquad
    _ = ENNReal.ofReal (C * (p.ν ^ k)⁻¹ * p.R ^ (8 / 11 : ℝ) * ‖α‖ +
          C * (p.ν ^ k)⁻¹ * p.R ^ (8 / 11 : ℝ) * ‖α‖ ^ 2) := (ENNReal.ofReal_add hX hY).symm
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hinv]
        exact hnum

end ES326

/-- **The bound leaf from the physical inlet source bound** (source 2370-2392, 2513-2520,
5277-5279): `‖entSrc(τ)‖_{L^{11/4}} ≤ ‖lin‖ + ‖quad‖ ≤ Cν^{-k}R^{8/11}|α|(1 + |α|)` and
`R^{8/11}|α| ≤ ρ_b = C₀ν^{-k₀}ρ`, `|α| ≤ C₀ν^{-k₀}`. -/
theorem entSrcLp_of (hI : InletSrcPhys) (D : SeqData) {dm dp : ℝ}
    (hst : D.RepairStanding dm dp) : EntSrcLpLeaf D hst := by
  obtain ⟨C, k, ν₀, hC, hν₀, hB⟩ := hI D.Sig D.Pl.eigenvalue D.Pl.mode D.Sig_pos
    hst.planar.eigenpair dm dp hst.dm_pos
  obtain ⟨ν₁, hν₁, hS⟩ := UnforcedLeray.Short.IIb.inletJointSmooth D.Sig D.Pl.eigenvalue
    D.Pl.mode D.Sig_pos hst.planar.eigenpair dm dp hst.dm_pos
  have hν : ∀ᶠ n : ℕ in atTop, retNu D.Pl D.σ₀ n < min (min ν₀ ν₁) 1 :=
    (retNu_tendsto D.σ₀ hst.omega_ne).eventually
      (gt_mem_nhds (lt_min (lt_min hν₀ hν₁) one_pos))
  refine ⟨C * D.K.C0 * (1 + D.K.C0), k + 2 * D.K.k0, ?_⟩
  filter_upwards [hst.actual, hν] with n hn hνn τ
  obtain ⟨z, -, hVz, -, hz⟩ := hn.ball
  have hν0 : ((D.level n).params D.Pl).ν < ν₀ :=
    lt_of_lt_of_le hνn ((min_le_left _ _).trans (min_le_left _ _))
  have hν1 : ((D.level n).params D.Pl).ν < ν₁ :=
    lt_of_lt_of_le hνn ((min_le_left _ _).trans (min_le_right _ _))
  have hνle1 : ((D.level n).params D.Pl).ν ≤ 1 := (lt_of_lt_of_le hνn (min_le_right _ _)).le
  have hInl : ∀ i : Fin 2, ContDiff ℝ ∞
      (fun x : ℝ × Space => ((D.level n).params D.Pl).inlet i x.1 x.2) :=
    fun i => hS ((D.level n).params D.Pl) _ hn.regime hν1.le rfl rfl i
  have hRaw : ContDiffOn ℝ 2
      (fun x : ℝ × Space => ((D.level n).params D.Pl).raw x.1 x.2) offAxis :=
    rawU_contDiffOn_offAxis_of ((D.level n).params D.Pl) (D.level n).ε_pos
      ((D.level n).train_stream_smooth.of_le (by norm_num))
  have hreg := hn.regime
  have hε1 : ((D.level n).params D.Pl).ε ≤ 1 :=
    ES326.eps_le_one' (D.level n).ν_pos hreg.eps_eq hreg.dm_pos hreg.dm_le
  have hρ1 : ((D.level n).params D.Pl).ε ^ (3 / 11 : ℝ) *
      Real.exp (D.K.m0 / ((D.level n).params D.Pl).ν) ≤ 1 :=
    ES326.rho_le_one' (D.level n).ν_pos hreg.eps_eq hreg.dm_le (by linarith [hst.m0_lt])
  have key := ES326.lp_level ((D.level n).params D.Pl) z (D.V n) (C := C) (k := k)
    (a := D.K.C0) (m0 := D.K.m0) (k0 := D.K.k0) hC hst.C0_pos.le hInl hRaw hVz hz rfl hνle1
    hε1 hρ1 (fun α τ => hB _ _ hn.regime hν0.le rfl rfl α τ) τ
  exact key

/-- **`PartIII-b:C/rep/8/2/pres/3/2/6`, conditional on the physical inlet source bound**
(source 2346-2347, 2370-2392, 2513-2520, 5277-5279): `EntSrcAt` holds along the sequence. -/
theorem entSrc_of_inletSrcPhys (hI : InletSrcPhys) (D : SeqData) {dm dp : ℝ}
    (hst : D.RepairStanding dm dp) : D.EntSrc :=
  entSrc_of D hst (entSrcReg D hst) (entSrcLp_of hI D hst)

/-- **`PartIII-b:C/rep/8/2/pres/3/2/6`** (source 2346-2347, 2370-2392, 2513-2520, 5277-5279):
`EntSrcAt` holds along the sequence. -/
theorem SeqData.entSrc (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) : D.EntSrc :=
  entSrc_of_inletSrcPhys inletSrcPhys D hst

end UnforcedLeray.Short.PartIIIb.Concrete
