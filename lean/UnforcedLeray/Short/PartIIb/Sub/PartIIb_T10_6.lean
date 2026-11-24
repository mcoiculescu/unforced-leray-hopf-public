import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10
import UnforcedLeray.Short.PartIIb.Sub.T08
import UnforcedLeray.Short.PartIIb.Tasks.BodyLift.Norm

/-!
# `PartII-b:T10/6` (`DriftRecovery`): decomposition

Source of record: `the November 2 reference manuscript`, lines 1912-1915
(`𝒯(√s b) = √s (S + 1/2) b`), converse of `hasPtwOp_driftT_NvC`.

Three leaves: the drift of a lift is a no-swirl field (`DriftNoSwirl`); a no-swirl `Y_r` field is a
ring lift of an `H_r` profile (`ProfileOfNoSwirl`, the `L^r` version of `Axi.range_Jv`, also what
`ResponseProfile` (T10/5) needs); the chart identity (`ChartDrift`).  The target follows
(`driftRecovery_of`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.PhaseSpace UnforcedLeray.Cons.C03.Concrete

/-- A complex phase field is axisymmetric without swirl: for every linear isometry `g` of `ℝ³` fixing
`e₃` (the group `𝒪`, with reflections in planes through the axis), `g d(τ, g⁻¹ y) = d(τ, y)` a.e.,
`g` acting complex-linearly on values (`B0412.gC`). -/
def PhaseNoSwirl (d : ℝ × Space → CVec3) : Prop :=
  ∀ g : Space ≃ₗᵢ[ℝ] Space, g (EuclideanSpace.single 2 1) = EuclideanSpace.single 2 1 →
    (fun x : ℝ × Space => B0412.gC g (d (x.1, g.symm x.2))) =ᵐ[volume] d

/-- **`T10/6/1`** (SP 1912-1915): the phase drift of the lift of `b₀ ∈ H_r`, if it lies in `Y_r`,
is axisymmetric without swirl.  Proof: for `g ∈ 𝒪` the action `Φ ↦ gΦ(τ, g⁻¹·)` preserves phase tests,
commutes with `driftT` (`y·∇` and `∂_τ` are rotation invariant) and preserves `pairF`; `NvC ε⁻¹ b₀`
is `g`-invariant (`Axi.Jv_mem_axisymmetric` on real and imaginary parts, `B0412.gC_realC`); so
`d₀` and `g·d₀` satisfy the same `HasPtwOp` relation, and their difference pairs to zero with every
phase test, hence vanishes a.e. (`B0411.eq_zero_of_forall_phasePair` or the fundamental lemma). -/
def DriftNoSwirl : Prop :=
  ∀ (c ε r : ℝ) (b₀ : CProf) (d₀ : ℝ × Space → CVec3),
    0 < c → 0 < ε → 1 < r → InHr c r b₀ → IsInYr (2 * ε * c) r d₀ →
    HasPtwOp (2 * ε * c) driftT (NvC ε⁻¹ b₀) d₀ → PhaseNoSwirl d₀

/-- **`T10/6/2`** (SP 1902-1906; `L^r` version of `Axi.mem_range_Jv`, `Lib/AxisymmetricB/Unitary.lean`
203): a `P`-periodic no-swirl field of `Y_r` (`P = 2εc`) is a.e. the lift of a `c`-periodic profile,
measurable for `H_r`: take `p = invLift R P (avgMer d)`, `R = ε⁻¹` (angular averages, `Average.ae_eq_avgLift`,
`liftFun_invLift`); the library proof uses only measurability, periodicity and no-swirl, not `L²`. -/
def ProfileOfNoSwirl : Prop :=
  ∀ (c ε r : ℝ) (d : ℝ × Space → CVec3), 0 < c → 0 < ε → 1 < r → IsInYr (2 * ε * c) r d →
    PhaseNoSwirl d →
    ∃ p : CProf, QPeriodic c p ∧ AEStronglyMeasurable p (hMeas c r) ∧ NvC ε⁻¹ p =ᵐ[volume] d

/-- **`T10/6/3`** (SP 1912-1915, converse of `hasPtwOp_driftT_NvC_of`, `Sub/T08.lean:119`): if the
drift of the lift of `b₀ ∈ H_r` is the lift of `p ∈ H_r`, then `S b₀ = p - b₀/2` weakly.  Proof: for a
`c`-periodized coordinate test `φ` the chart change of variables turns `pairF (driftT Φ_φ) (NvC b₀)`
into `∫ b₀ · (Sᵗ + 1/2)φ` and `pairF Φ_φ (NvC p)` into `∫ p · φ` (as in `DriftSmooth`, T08/1, which
holds for any `H_r` profile when tested against such Φ: the integrals converge by Hölder and
`phaseLpNorm_NvC`); equate and read off `HasWeakFO` componentwise (test with real and imaginary
parts of the two components). -/
def ChartDrift : Prop :=
  ∀ (c ε r : ℝ) (b₀ p : CProf) (d : ℝ × Space → CVec3), 0 < c → 0 < ε → 1 < r → InHr c r b₀ →
    InHr c r p → NvC ε⁻¹ p =ᵐ[volume] d → HasPtwOp (2 * ε * c) driftT (NvC ε⁻¹ b₀) d →
    HasWeakVec vS dZero b₀ (fun x => p x - (1 / 2 : ℂ) • b₀ x)

theorem elp_sub_half_le {μ : Measure Coord} {p : ℝ≥0∞} (hp : 1 ≤ p) {f g : CProf}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    eLpNorm (f - (1 / 2 : ℂ) • g) p μ ≤ eLpNorm f p μ + eLpNorm g p μ := by
  refine (eLpNorm_sub_le hf (hg.const_smul (1 / 2 : ℂ)) hp).trans ?_
  gcongr
  refine (eLpNorm_const_smul_le (μ := μ) (p := p) (c := (1 / 2 : ℂ)) (f := g)).trans ?_
  have h1 : ‖(1 / 2 : ℂ)‖ₑ ≤ 1 := by
    rw [enorm_eq_nnnorm]; norm_num
  calc _ ≤ 1 * eLpNorm g p μ := by gcongr
    _ = _ := one_mul _

theorem hNorm_sub_half_le {c r : ℝ} (hr : 1 < r) {f g : CProf} (hf : InHr c r f)
    (hg : InHr c r g) :
    hNorm c r (fun x => f x - (1 / 2 : ℂ) • g x) ≤ hNorm c r f + hNorm c r g := by
  have hr1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal r := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hr.le
  exact elp_sub_half_le hr1 hf.meas hg.meas

theorem driftRecovery_of (h1 : DriftNoSwirl) (h2 : ProfileOfNoSwirl) (h3 : ChartDrift) :
    DriftRecovery := by
  intro c ε r b₀ d₀ hc hε hr hb hd hop
  have hr0 : 0 < r := by linarith
  obtain ⟨p, hpper, hpmeas, hpd⟩ := h2 c ε r d₀ hc hε hr hd (h1 c ε r b₀ d₀ hc hε hr hb hd hop)
  set κ : ℝ≥0∞ := ENNReal.ofReal ((Real.pi * (ε⁻¹) ^ 2) ^ (1 / r)) with hκ
  have hκ0 : κ ≠ 0 := by
    rw [hκ, Ne, ENNReal.ofReal_eq_zero, not_le]
    positivity
  have hNp : phaseLpNorm (2 * ε * c) r (NvC ε⁻¹ p) = κ * hNorm c r p :=
    phaseLpNorm_NvC hc hr0 hε p hpper hpmeas
  have hNb : phaseLpNorm (2 * ε * c) r (NvC ε⁻¹ b₀) = κ * hNorm c r b₀ :=
    phaseLpNorm_NvC hc hr0 hε b₀ hb.periodic hb.meas
  have hNpd : phaseLpNorm (2 * ε * c) r (NvC ε⁻¹ p) = phaseLpNorm (2 * ε * c) r d₀ :=
    phaseLpNorm_congr_ae' hpd
  have hpfin : hNorm c r p < ⊤ := by
    by_contra hcon
    have htop : hNorm c r p = ⊤ := not_lt_top_iff.mp hcon
    have := hd.finite
    rw [← hNpd, hNp, htop, ENNReal.mul_top hκ0] at this
    exact lt_irrefl _ this
  have hp : InHr c r p := ⟨hpper, hpmeas, hpfin⟩
  have hSn : hNorm c r (fun x => p x - (1 / 2 : ℂ) • b₀ x) ≤ hNorm c r p + hNorm c r b₀ :=
    hNorm_sub_half_le hr hp hb
  refine ⟨fun x => p x - (1 / 2 : ℂ) • b₀ x, h3 c ε r b₀ p d₀ hc hε hr hb hp hpd hop, ?_, ?_⟩
  · refine ⟨?_, hp.meas.sub (hb.meas.const_smul (1 / 2 : ℂ)), ?_⟩
    · filter_upwards [hp.periodic, hb.periodic] with x h1 h2
      simp only [h1, h2]
    · exact lt_of_le_of_lt hSn (ENNReal.add_lt_top.2 ⟨hp.finite, hb.finite⟩)
  · calc κ * hNorm c r (fun x => p x - (1 / 2 : ℂ) • b₀ x)
        ≤ κ * (hNorm c r p + hNorm c r b₀) := by gcongr
      _ = phaseLpNorm (2 * ε * c) r d₀ + phaseLpNorm (2 * ε * c) r (NvC ε⁻¹ b₀) := by
        rw [mul_add, ← hNp, ← hNb, hNpd]

end UnforcedLeray.Short.IIb

#print axioms UnforcedLeray.Short.IIb.driftRecovery_of
