import UnforcedLeray.Short.PartIIIa.Sub.T21_c2
import UnforcedLeray.Short.PartIIb.Sub.T22

/-!
# Part III-a, task `PartIII-a:T21/c2/2` (`FmeRate`): decomposition

Source of record: `the November 2 reference manuscript`, lines 2937-2958
(`eq:short-causal-free-moving`) and 2085-2093 (train comparison), 295-305 (`sct:comparison`).

With `a = clockA ν σ`, `p_σ(x) = (1 + |x|²/a)^m` and `𝓔 = a³ ∫ ω² p_σ`:
`𝓔' = 3ν a² ∫ω²p + a³∫ω²∂_σp + 2a³∫ω(νΔω - v·∇ω)p` (`FmrDeriv`); integration by parts
(`FmrIBP`: diffusion seam term nonpositive, transport seam terms cancel) bounds the last term by
`a³∫ω²(νΔp + v·∇p)`; the weight bracket is `≤ (ν/a)(m²+3m+3) p` (`FmrBracket`, SP 2947-2954);
the central Gaussian transports the radial weight exactly (`FmrIsoRadial`) and the actual-base
velocity error is small (`FmrVelGap`, SP 2955); `ν/a = 1/(θ a²) ≤ 1/(b a²)` on `θ ≥ b`.

The weak-to-regular step uses `CylClassicalExists`, `CylWeakEqClassical` (PartII-b `T22/1`, `T22/2`)
and `FmrTransfer`. `fmeRate_of` assembles `FmeRate`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Short.IIb
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

/-- The dilating weight `p_a(x) = (1 + |x|²/a)^m` on the plane. -/
def movWeight (m a : ℝ) (x : B0579.Plane) : ℝ := (1 + (x.1 ^ 2 + x.2 ^ 2) / a) ^ m

/-- The `σ`-derivative of the weight `p_{a(σ)}`, `a = 1 + νσ`: `∂_σ p = -(ν m/a²)|x|²(1+|x|²/a)^{m-1}`. -/
def movWeightDt (ν m a : ℝ) (x : B0579.Plane) : ℝ :=
  -(ν * m / a ^ 2) * (x.1 ^ 2 + x.2 ^ 2) * (1 + (x.1 ^ 2 + x.2 ^ 2) / a) ^ (m - 1)

/-- The candidate right derivative of `movFlowEnergy` along a flow with velocity `v`
(`d/dσ[a³∫ω²p] = 3νa²∫ω²p + a³∫ω²∂_σp + 2a³∫ω(νΔω - v·∇ω)p`). -/
def movRate (ν c m : ℝ) (v : ℝ → B0579.Plane → UnforcedLeray.Train.Vec)
    (ω : ℝ → B0579.Plane → ℝ) (σ : ℝ) : ℝ :=
  3 * ν * clockA ν σ ^ 2 * (∫ x in B0579.cell c, ω σ x ^ 2 * movWeight m (clockA ν σ) x) +
    clockA ν σ ^ 3 * (∫ x in B0579.cell c, ω σ x ^ 2 * movWeightDt ν m (clockA ν σ) x) +
    2 * clockA ν σ ^ 3 * ∫ x in B0579.cell c,
      ω σ x * (ν * lapP (ω σ) x - (v σ x 0 * B0579.pd 0 (ω σ) x + v σ x 1 * B0579.pd 1 (ω σ) x)) *
        movWeight m (clockA ν σ) x

/-- The conclusion of `FmeRate` that concerns a flow on `[t, s]` (everything but the datum term). -/
def FmeRegConc (ν m ε b t s : ℝ) (ω : ℝ → B0579.Plane → ℝ) : Prop :=
  (∀ σ ∈ Icc t s, IntegrableOn
      (fun x : ℝ × ℝ => ω σ x ^ 2 * (1 + (x.1 ^ 2 + x.2 ^ 2) / clockA ν σ) ^ m)
      (B0579.cell (ν ^ (-2 : ℝ)))) ∧
    ContinuousOn (movFlowEnergy ν (ν ^ (-2 : ℝ)) m ω) (Icc t s) ∧
    ∃ E' : ℝ → ℝ, ∀ τ ∈ Ico t s,
      HasDerivWithinAt (movFlowEnergy ν (ν ^ (-2 : ℝ)) m ω) (E' τ) (Ici τ) τ ∧
        E' τ ≤ 2 * ((normGrowthConst m / b + ε) / clockA ν τ ^ 2) *
          movFlowEnergy ν (ν ^ (-2 : ℝ)) m ω τ

/-- The full conclusion of `FmeRate`: the datum term and `FmeRegConc`. -/
def FmeConc (ν m ε b t s : ℝ) (f : B0579.Plane → ℝ) (ω : ℝ → B0579.Plane → ℝ) : Prop :=
  IntegrableOn (fun x : ℝ × ℝ => f x ^ 2 * (1 + (x.1 ^ 2 + x.2 ^ 2) / clockA ν t) ^ m)
      (B0579.cell (ν ^ (-2 : ℝ))) ∧ FmeRegConc ν m ε b t s ω

/-- **Leaf `FmrTrainClose`** (SP 2085-2089 and `sct:comparison`, SP 295-305): for fixed `b > 0` and
`ν` small the actual train (period `c = ν⁻²`) is `δ = 1`-close to the periodized Gaussian in the
weighted budget on all ages `s ≤ Σ/ν` with `Σ = (ν b)⁻¹` (these cover every age with
`θ(s) = (ν a(s))⁻¹ ≥ b`, since then `ν² s ≤ b⁻¹`).  For the trains of the BUC class
`PartI.IsBUCTrain` (SP 270-288): the comparison is a property of the source train, not of an
arbitrary `B0140.TrainSol` (`Short/PartI/TrainClass.lean`). -/
def FmrTrainClose : Prop :=
  ∀ b : ℝ, 0 < b → ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν ∈ Ioc 0 ν₀,
    ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)), UnforcedLeray.Short.PartI.IsBUCTrain tr →
      TrainClose tr (ν * b)⁻¹ 1

/-- **Leaf `FmrVelBdd`** (SP 283, `sup_{[0,t]}‖v‖_∞ < ∞`): the velocity of a BUC train
(`PartI.IsBUCTrain`, SP 270-288) is bounded on `[0, T]`.  `B0140.IsTrain` alone gives no bound in
the unbounded direction `η` (`Short/PartI/TrainClass.lean`); the statement is `FmrVelBddBUC`
(`Sub/PartIIIa_T21_c2_2_8.lean`, proved there as `fmrVelBddBUC`). -/
def FmrVelBdd : Prop :=
  ∀ ν c : ℝ, 0 < ν → 0 < c → ∀ tr : UnforcedLeray.B0140.TrainSol ν c,
    UnforcedLeray.Short.PartI.IsBUCTrain tr → ∀ T : ℝ,
    ∃ M : ℝ, ∀ σ ∈ Icc (0 : ℝ) T, ∀ x : B0579.Plane, |tr.v σ x 0| + |tr.v σ x 1| ≤ M

/-- **Leaf `FmrVelGap`** (SP 2955 "actual-base velocity errors", `sct:comparison` for
`1 ≤ a ≤ c²`, and the image vortices at distance `≥ c/2`): on the ages `θ(s) ≥ b` and `ν` small,
the velocity of a BUC train (`PartI.IsBUCTrain`, SP 270-288) is within `ε a^{-3/2}` of the central
Gaussian vortex on the cell.  The same statement as `FmrVelGapBUC` (`Sub/PartIIIa_T21_c2_2_7.lean`,
proved there by `fmrVelGapBUC_of` from `FmrVelImage`, `FmrVelCompSup`, `PartI.TrainComparison`). -/
def FmrVelGap : Prop :=
  ∀ b : ℝ, 0 < b → ∀ ε : ℝ, 0 < ε → ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν ∈ Ioc 0 ν₀,
    ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)), UnforcedLeray.Short.PartI.IsBUCTrain tr →
      ∀ s : ℝ, 0 ≤ s → b ≤ clockTheta ν s →
      ∀ x ∈ B0579.cell (ν ^ (-2 : ℝ)),
        |tr.v s x 0 - (UnforcedLeray.B0146.isoVelocity ν s x).1| +
            |tr.v s x 1 - (UnforcedLeray.B0146.isoVelocity ν s x).2|
          ≤ ε * clockA ν s ^ (-(3 / 2) : ℝ)

/-- **Leaf `FmrBracket`** (SP 2947-2954): the weight bracket
`νΔp + (3ν/a)p + ∂_σp ≤ (ν/a)(m²+3m+3)p` (that is `2 C_m ν/a · p`), pointwise, for `m ≥ 1`, `a > 0`,
`ν ≥ 0`. In `y = x/√a`, `P = (1+|y|²)^m`: `ΔP/P + 3 - ½ y·∇log P ≤ m²+3m+3`
(with `u = |y|²/(1+|y|²)`: `4m(1-u) + 4m(m-1)u(1-u) - mu + 3 ≤ 4m + m(m-1) + 3`).  The source uses
it only for large `m` (`FmrRegular` has `8 < m`); for `0 < m < 1` it is false at `x = 0`
(`not_fmrBracketOld`, `Sub/T21_c2_2_3.lean`). -/
def FmrBracket : Prop :=
  ∀ m : ℝ, 1 ≤ m → ∀ ν a : ℝ, 0 ≤ ν → 0 < a → ∀ x : B0579.Plane,
    ν * lapP (movWeight m a) x + (3 * ν / a) * movWeight m a x + movWeightDt ν m a x ≤
      (ν / a) * (m ^ 2 + 3 * m + 3) * movWeight m a x

/-- **Leaf `FmrIsoRadial`** (SP 2952-2953 "Radial Euler transport preserves the weight"): the central
Gaussian vortex `isoVelocity ν σ` (a perpendicular gradient of a radial stream) is tangent to the
level sets of the radial weight, and `|∂_j p| ≤ (m/√a) p` for `j = 0, 1`. -/
def FmrIsoRadial : Prop :=
  ∀ m : ℝ, 0 ≤ m → ∀ ν σ : ℝ, 0 < clockA ν σ → ∀ x : B0579.Plane,
    (UnforcedLeray.B0146.isoVelocity ν σ x).1 * B0579.pd 0 (movWeight m (clockA ν σ)) x +
        (UnforcedLeray.B0146.isoVelocity ν σ x).2 * B0579.pd 1 (movWeight m (clockA ν σ)) x = 0 ∧
      |B0579.pd 0 (movWeight m (clockA ν σ)) x| ≤ m / Real.sqrt (clockA ν σ) *
        movWeight m (clockA ν σ) x ∧
      |B0579.pd 1 (movWeight m (clockA ν σ)) x| ≤ m / Real.sqrt (clockA ν σ) *
        movWeight m (clockA ν σ) x

/-- **Leaf `FmrIBP`** (SP 2950-2954; cf. `CylDiffusionBound`, `CylTransportIBP` for the fixed
weight): for `g` of class `CylSmoothDecay c`, a train velocity at an age `σ ≥ 0` and the weight
`p = movWeight m a`,
`2∫_cell g(νΔg - v·∇g)p ≤ ∫_cell g²(νΔp + v·∇p)`, all integrands integrable. (Diffusion: the
seam term `-[g² p_q]` is nonpositive; transport: `div v = 0`, `v` and `g` periodic and `p` even in
`q`, so the seam terms cancel.) -/
def FmrIBP : Prop :=
  ∀ (ν c : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (σ : ℝ), 0 ≤ σ → 0 < c → 0 < ν →
    (∃ M : ℝ, ∀ x : B0579.Plane, |tr.v σ x 0| + |tr.v σ x 1| ≤ M) →
    ∀ (m a : ℝ), 0 ≤ m → 0 < a → ∀ g : B0579.Plane → ℝ, CylSmoothDecay c g →
      IntegrableOn (fun x => g x ^ 2 * (ν * lapP (movWeight m a) x +
          (tr.v σ x 0 * B0579.pd 0 (movWeight m a) x + tr.v σ x 1 * B0579.pd 1 (movWeight m a) x)))
        (B0579.cell c) ∧
      IntegrableOn (fun x => g x * (ν * lapP g x -
          (tr.v σ x 0 * B0579.pd 0 g x + tr.v σ x 1 * B0579.pd 1 g x)) * movWeight m a x)
        (B0579.cell c) ∧
      2 * ∫ x in B0579.cell c, g x * (ν * lapP g x -
          (tr.v σ x 0 * B0579.pd 0 g x + tr.v σ x 1 * B0579.pd 1 g x)) * movWeight m a x ≤
        ∫ x in B0579.cell c, g x ^ 2 * (ν * lapP (movWeight m a) x +
          (tr.v σ x 0 * B0579.pd 0 (movWeight m a) x + tr.v σ x 1 * B0579.pd 1 (movWeight m a) x))

/-- **Leaf `FmrDeriv`** (SP 2937-2946, differentiation under the integral sign; cf.
`RegularEnergyDeriv` for the fixed weight): for a regular flow on `[t, T]` with bounded velocity,
the dilated-weight integrands are integrable, `movFlowEnergy` is continuous on `[t, T]` and has
right derivative `movRate` on `[t, T)`. -/
def FmrDeriv : Prop :=
  ∀ (c ν m t T : ℝ) (v : ℝ → B0579.Plane → UnforcedLeray.Train.Vec) (ω : ℝ → B0579.Plane → ℝ),
    0 < c → 0 < ν → 0 ≤ t → 0 ≤ m → IsRegularCylFlow c ν v t T ω →
    (∃ M : ℝ, ∀ σ ∈ Icc t T, ∀ x : B0579.Plane, |v σ x 0| + |v σ x 1| ≤ M) →
    (∀ σ ∈ Icc t T, IntegrableOn
        (fun x : ℝ × ℝ => ω σ x ^ 2 * (1 + (x.1 ^ 2 + x.2 ^ 2) / clockA ν σ) ^ m)
        (B0579.cell c)) ∧
      ContinuousOn (movFlowEnergy ν c m ω) (Icc t T) ∧
      ∀ τ ∈ Ico t T, HasDerivWithinAt (movFlowEnergy ν c m ω) (movRate ν c m v ω τ) (Ici τ) τ

/-- **Leaf `FmrRegular`** (SP 2937-2958): the dilated-weight energy rate for a *regular* free
cylinder flow. Follows from `FmrDeriv`, `FmrIBP`, `FmrBracket`, `FmrIsoRadial`, `FmrVelGap`,
`FmrVelBdd`: `movRate ≤ a³∫ω²[(ν/a)(m²+3m+3)p + |v - v_iso|(m/√a)p·2]`, and
`ν/a = 1/(θ a²) ≤ 1/(b a²)` on `θ ≥ b`, the velocity error `≤ ε a^{-3/2}`.  For BUC trains
(`PartI.IsBUCTrain`, SP 270-288; `FmrVelGap` and `FmrVelBdd` hold only for them). -/
def FmrRegular : Prop :=
  ∀ m : ℝ, 8 < m → ∀ ε : ℝ, 0 < ε → ∀ b : ℝ, 0 < b → ∃ ν₁ : ℝ, 0 < ν₁ ∧ ∀ ν ∈ Ioc 0 ν₁,
    ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)), UnforcedLeray.Short.PartI.IsBUCTrain tr →
      ∀ t s T : ℝ, 0 ≤ t → t ≤ s → s ≤ T →
      b ≤ clockTheta ν s → ∀ ω : ℝ → B0579.Plane → ℝ,
        IsRegularCylFlow (ν ^ (-2 : ℝ)) ν tr.v t T ω → FmeRegConc ν m ε b t s ω

/-- **Leaf `FmrTransfer`**: a regular flow `ω'` with datum `f` that agrees a.e. on the cell with the
weak flow `ω` for all ages in `[t, T]` (`T ≥ s`) transfers `FmeRegConc` to `ω`, and gives the datum
integrability. (`movEnergy` depends only on the a.e. class; `HasDerivWithinAt` on `Ici τ` only on
`[τ, s]`, a neighbourhood of `τ` in `Ici τ` for `τ < s`.) -/
def FmrTransfer : Prop :=
  ∀ (ν m ε b t s T : ℝ) (f : B0579.Plane → ℝ) (ω ω' : ℝ → B0579.Plane → ℝ), t ≤ s → s ≤ T →
    ω' t = f →
    (∀ σ ∈ Icc t T, ω' σ =ᵐ[volume.restrict (B0579.cell (ν ^ (-2 : ℝ)))] ω σ) →
    FmeRegConc ν m ε b t s ω' → FmeConc ν m ε b t s f ω

theorem fmeRate_of (hTC : FmrTrainClose) (hEx : CylClassicalExists) (hUq : CylWeakEqClassical)
    (hR : FmrRegular) (hTr : FmrTransfer) : FmeRate := by
  intro m hm ε hε
  refine ⟨1, fun b hb => ?_⟩
  have hb0 : 0 < b := by linarith
  obtain ⟨ν₁, hν₁, H1⟩ := hR m hm ε hε b hb0
  obtain ⟨ν₂, hν₂, H2⟩ := hTC b hb0
  refine ⟨min ν₁ (min ν₂ 1), lt_min hν₁ (lt_min hν₂ one_pos),
    fun ν hν tr htr t s ht hts hθ f hf ω hω => ?_⟩
  have hνpos : 0 < ν := hν.1
  have hν1 : ν ≤ ν₁ := hν.2.trans (min_le_left _ _)
  have hν2 : ν ≤ ν₂ := hν.2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hν3 : ν ≤ 1 := hν.2.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hc0 : 0 < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hνpos _
  have hc1 : 1 ≤ ν ^ (-2 : ℝ) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hνpos hν3 (by norm_num)
  have hSg : 0 < (ν * b)⁻¹ := inv_pos.2 (mul_pos hνpos hb0)
  have ha : 0 < clockA ν s := by
    unfold clockA; have := mul_nonneg hνpos.le (ht.trans hts); linarith
  have hs : s ≤ (ν * b)⁻¹ / ν := by
    have hθ' : b ≤ (ν * clockA ν s)⁻¹ := hθ
    have h1 : ν * (1 + ν * s) ≤ b⁻¹ := (le_inv_comm₀ (mul_pos hνpos ha) hb0).2 hθ'
    rw [le_div_iff₀ hνpos, ← one_div, le_div_iff₀ (mul_pos hνpos hb0)]
    have h2 : b * (ν * (1 + ν * s)) ≤ 1 := by
      have := mul_le_mul_of_nonneg_left h1 hb0.le
      rwa [mul_inv_cancel₀ hb0.ne'] at this
    nlinarith [mul_pos hνpos hb0, mul_nonneg hνpos.le (ht.trans hts)]
  have hts' : t ≤ (ν * b)⁻¹ / ν := hts.trans hs
  have hTCl : TrainClose tr (ν * b)⁻¹ 1 := H2 ν ⟨hνpos, hν2⟩ tr htr
  obtain ⟨ω', hreg, hω's⟩ := hEx (ν * b)⁻¹ hSg ν (ν ^ (-2 : ℝ)) 1 hνpos hc1 zero_le_one tr hTCl
    t ht hts' f hf
  have hae := hUq m hm (ν * b)⁻¹ hSg ν (ν ^ (-2 : ℝ)) 1 hνpos hc0 zero_le_one tr hTCl t ht f hf
    ω' hreg hω's ω hω
  exact hTr ν m ε b t s _ f ω ω' hts hs hω's hae
    (H1 ν ⟨hνpos, hν1⟩ tr htr t s _ ht hts hs hθ ω' hreg)

end UnforcedLeray.Short.IIIa
