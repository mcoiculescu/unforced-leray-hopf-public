import UnforcedLeray.Cons.L2.CanonicalBranch.Limit
import UnforcedLeray.Lib.BudgetsGronwall.RunningSup
import UnforcedLeray.Lib.Semigroups.Dunford.Defs

/-!
# G3b, part 4: the amplitude–complement inequalities and Gronwall (B0116, B0117)

`paper/main.tex`, proof of G3b, lines 1750–1803 (`eq:st18-t00089`–`eq:st18-t00094`); blueprint
units B0116 (`eq:st18-t00093`: uniform relative growth) and B0117 (`eq:st18-t00094`:
arbitrary-data inequalities and propagation of differences).

Generic data: `λ, κ ∈ ℂ`, `q, q† ∈ X_G` with `ℓ = ⟨·, q†⟩_{X_G}` (`ℓ f = ⟪q†, f⟫` in Mathlib's
convention, conjugate-linear in the first slot), `Q f = f - ℓ(f)q` (`eq:st18-t00012`).
For a datum `f` at `R` and `t ≥ 0` with `θ = R - t`:
* `normState λ κ R f t = N(R - t, R)f`, the normalized state `A(t)q + r(t)` of the solution
  with `W(0) = f` (`eq:st18-t00089`: `W(t) = e^{λt}(R/θ)^κ(A(t)q + r(t))`);
* `amp = A(t) = ℓ(normState)`, `compl = r(t) = Q(normState)`,
  `ampSup = M(t) = sup_{0 ≤ s ≤ t}|A(s)|` (the library's `runningSup`, INF30);
* `ArbitraryDataBounds`: the two inequalities of `eq:st18-t00094` with `β(t) = 1/(R - t)`, for
  every `R`, `f` and `t` with `θ = R - t ≥ b₀`.

## Results (Gronwall, as in the manuscript)

* `ampSup_le`: `M(t) ≤ (|ℓf| + Cb₀⁻¹‖Qf‖)e^{C/b₀}` (`∫₀^t β² = θ⁻¹ - R⁻¹ ≤ b₀⁻¹`,
  `integral_inv_sq`);
* **`uniformPropagation_of_bounds`** (B0117: "uniform propagation of differences in the normalized
  state `Aq + r`, on every interval `θ ≥ b₀`"): `‖N(θ, θ')‖ ≤ K` for `b₀ ≤ θ ≤ θ'`;
* **`relativeGrowth_of_bounds`** (B0116, `eq:st18-t00093`, the case `f = q`, `ℓq = 1`,
  `Qq = 0`): `‖Y_R(θ) - q‖ ≤ K/θ` for `b₀ ≤ θ ≤ R`.

`A` is continuous (`continuousOn_amp`), so `M` is continuous and the integral in
`eq:st18-t00094` is the integral of a continuous function on a compact interval: no junk value.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped Topology InnerProductSpace

namespace UnforcedLeray.Cons.G3b

open UnforcedLeray.B0010 UnforcedLeray.B0123 UnforcedLeray.Evolution UnforcedLeray.Gronwall

variable (lam κ : ℂ) (q qd : XG)

/-- `Q f = f - ℓ(f)q`, `ℓ = ⟨·, q†⟩_{X_G}` (`eq:st18-t00012`). -/
def projQ (f : XG) : XG := f - ⟪qd, f⟫_ℂ • q

/-- The bounded operator realizing the complementary projection `Q = I - q ℓ` in the mild
formulation (`eq:st18-t00012`). Keeping this as a continuous linear map lets us pass `Q` through
Bochner integrals without a pointwise domain assumption on the integrand. -/
def projQCLM : XG →L[ℂ] XG :=
  1 - UnforcedLeray.Infra.Dunford.rankOneProj (innerSL ℂ qd) q

theorem projQCLM_apply (f : XG) : projQCLM q qd f = projQ q qd f := by
  simp [projQCLM, projQ, UnforcedLeray.Infra.Dunford.rankOneProj_apply,
    innerSL_apply_apply]

/-- The normalized rank-one projection kills the reference vector. -/
theorem projQ_q (hℓq : ⟪qd, q⟫_ℂ = 1) : projQ q qd q = 0 := by
  simp [projQ, hℓq]

/-- Every value of the complementary projection lies in the kernel of the amplitude. -/
theorem inner_qd_projQ_eq_zero (hℓq : ⟪qd, q⟫_ℂ = 1) (f : XG) :
    ⟪qd, projQ q qd f⟫_ℂ = 0 := by
  simp only [projQ, inner_sub_right, inner_smul_right, hℓq]
  ring

/-- The complementary projection is idempotent once the reference amplitude is normalized. -/
theorem projQ_idem (hℓq : ⟪qd, q⟫_ℂ = 1) (f : XG) :
    projQ q qd (projQ q qd f) = projQ q qd f := by
  rw [projQ, inner_qd_projQ_eq_zero q qd hℓq f, zero_smul, sub_zero]

/-- The amplitude functional is represented by the continuous linear map `innerSL`. -/
theorem inner_qd_intervalIntegral {a b : ℝ} {f : ℝ → XG}
    (hf : IntervalIntegrable f volume a b) :
    ⟪qd, ∫ t in a..b, f t⟫_ℂ = ∫ t in a..b, ⟪qd, f t⟫_ℂ := by
  simpa only [innerSL_apply_apply] using
    ((innerSL ℂ qd).intervalIntegral_comp_comm hf).symm

/-- `Q` commutes with the Bochner interval integral, the step needed to project the Dyson mild
equation onto `Q X_G` (B0115, `eq:st18-t00090`). -/
theorem projQ_intervalIntegral {a b : ℝ} {f : ℝ → XG}
    (hf : IntervalIntegrable f volume a b) :
    projQ q qd (∫ t in a..b, f t) = ∫ t in a..b, projQ q qd (f t) := by
  have h := (projQCLM q qd).intervalIntegral_comp_comm hf
  rw [projQCLM_apply] at h
  exact h.symm

/-- The integrand in the concrete Dyson mild equation is interval integrable. This follows from
the bounded perturbation theorem for the free Gaussian family; no regularity of the input `x` is
needed. -/
theorem intervalIntegrable_S_mild_integrand {θ θ' : ℝ} (hθ : 0 < θ)
    (hθθ' : θ ≤ θ') (x : XG) :
    IntervalIntegrable
      (fun u => freeU (-θ) u (B0012.L0 (S (-u) θ' x))) volume (-θ') (-θ) := by
  have hb : -θ < 0 := by linarith
  let E : EvolutionFamily XG (-θ') (-θ) := freeFam (-θ') (-θ) hb
  let A : BoundedPert XG (-θ') (-θ) := pertL0 (-θ') (-θ)
  let U := UnforcedLeray.Evolution.dyson E A
  have hU : ContinuousOn (fun u => U.U u (-θ') x) (Icc (-θ') (-θ)) :=
    U.continuousOn_fst le_rfl x
  have hi := E.intervalIntegrable_integrand A le_rfl (by linarith) le_rfl hU
  apply hi.congr
  intro u hu
  rw [uIoc_of_le (by linarith : -θ' ≤ -θ)] at hu
  have hpos : 0 < -u := by linarith [hu.2]
  have hle : -u ≤ θ' := by linarith [hu.1]
  have hS : S (-u) θ' = U.U u (-θ') := by
    calc S (-u) θ' =
          (UnforcedLeray.Evolution.dyson (freeFam (-θ') (-θ) hb)
            (pertL0 (-θ') (-θ))).U (-(-u)) (-θ') :=
          S_eq_dyson (a := -θ') (b := -θ) hb hpos hle le_rfl (by simpa using hu.2)
      _ = U.U u (-θ') := by simp [U, E, A]
  change E.U (-θ) u (A.A u (U.U u (-θ') x)) =
    freeU (-θ) u (B0012.L0 (S (-u) θ' x))
  rw [show E.U (-θ) u = freeU (-θ) u by rfl,
    show A.A u = B0012.L0 by rfl, hS.symm]

/-- The complementary part of the concrete Dyson evolution satisfies the projected mild
equation. The integrability premise is the standard Dyson integrand condition; the concrete
evolution supplies it from its interval continuity bound. -/
theorem projQ_S_mild_of_integrable {θ θ' : ℝ} (hθ : 0 < θ) (hθθ' : θ ≤ θ') (x : XG)
    (hI : IntervalIntegrable
      (fun u => freeU (-θ) u (B0012.L0 (S (-u) θ' x))) volume (-θ') (-θ)) :
    projQ q qd (S θ θ' x) =
      projQ q qd (expD (Real.log θ' - Real.log θ) x) +
        ∫ u in (-θ')..(-θ), projQ q qd (freeU (-θ) u (B0012.L0 (S (-u) θ' x))) := by
  let T := projQCLM q qd
  let g : ℝ → XG := fun u => freeU (-θ) u (B0012.L0 (S (-u) θ' x))
  have hmap : T (∫ u in (-θ')..(-θ), g u) =
      ∫ u in (-θ')..(-θ), projQ q qd (g u) := by
    calc T (∫ u in (-θ')..(-θ), g u)
        = ∫ u in (-θ')..(-θ), T (g u) := (T.intervalIntegral_comp_comm hI).symm
      _ = ∫ u in (-θ')..(-θ), projQ q qd (g u) := by
        apply intervalIntegral.integral_congr
        intro u hu
        exact projQCLM_apply q qd (g u)
  calc projQ q qd (S θ θ' x) = T (S θ θ' x) := (projQCLM_apply q qd _).symm
    _ = T (expD (Real.log θ' - Real.log θ) x + ∫ u in (-θ')..(-θ), g u) := by
      rw [S_mild hθ hθθ' x]
    _ = T (expD (Real.log θ' - Real.log θ) x) + T (∫ u in (-θ')..(-θ), g u) := map_add T _ _
    _ = T (expD (Real.log θ' - Real.log θ) x) + ∫ u in (-θ')..(-θ), projQ q qd (g u) := by
      exact congrArg (fun z => T (expD (Real.log θ' - Real.log θ) x) + z) hmap
    _ = projQ q qd (expD (Real.log θ' - Real.log θ) x) +
        ∫ u in (-θ')..(-θ), projQ q qd (g u) := by
      exact congrArg (fun z => z + ∫ u in (-θ')..(-θ), projQ q qd (g u))
        (projQCLM_apply q qd _)

/-- The amplitude part of the concrete Dyson evolution satisfies the projected mild equation.
This is the weak scalar identity used before deriving the amplitude ODE in B0115. -/
theorem inner_qd_S_mild_of_integrable {θ θ' : ℝ} (hθ : 0 < θ) (hθθ' : θ ≤ θ') (x : XG)
    (hI : IntervalIntegrable
      (fun u => freeU (-θ) u (B0012.L0 (S (-u) θ' x))) volume (-θ') (-θ)) :
    ⟪qd, S θ θ' x⟫_ℂ =
      ⟪qd, expD (Real.log θ' - Real.log θ) x⟫_ℂ +
        ∫ u in (-θ')..(-θ), ⟪qd, freeU (-θ) u (B0012.L0 (S (-u) θ' x))⟫_ℂ := by
  rw [S_mild hθ hθθ' x, inner_add_right]
  rw [inner_qd_intervalIntegral qd hI]

/-- The complementary mild equation for the concrete Gaussian evolution, with the Dyson
integrability condition discharged from its construction. -/
theorem projQ_S_mild {θ θ' : ℝ} (hθ : 0 < θ) (hθθ' : θ ≤ θ') (x : XG) :
    projQ q qd (S θ θ' x) =
      projQ q qd (expD (Real.log θ' - Real.log θ) x) +
        ∫ u in (-θ')..(-θ), projQ q qd (freeU (-θ) u (B0012.L0 (S (-u) θ' x))) :=
  projQ_S_mild_of_integrable q qd hθ hθθ' x
    (intervalIntegrable_S_mild_integrand hθ hθθ' x)

/-- The scalar amplitude mild equation for the concrete Gaussian evolution. -/
theorem inner_qd_S_mild {θ θ' : ℝ} (hθ : 0 < θ) (hθθ' : θ ≤ θ') (x : XG) :
    ⟪qd, S θ θ' x⟫_ℂ =
      ⟪qd, expD (Real.log θ' - Real.log θ) x⟫_ℂ +
        ∫ u in (-θ')..(-θ), ⟪qd, freeU (-θ) u (B0012.L0 (S (-u) θ' x))⟫_ℂ :=
  inner_qd_S_mild_of_integrable qd hθ hθθ' x
    (intervalIntegrable_S_mild_integrand hθ hθθ' x)

/-- The normalized state `A(t)q + r(t) = N(R - t, R)f` (`eq:st18-t00089`). -/
def normState (R : ℝ) (f : XG) (t : ℝ) : XG := normProp lam κ (R - t) R f

/-- The amplitude `A(t) = ℓ(A(t)q + r(t))`. -/
def amp (R : ℝ) (f : XG) (t : ℝ) : ℂ := ⟪qd, normState lam κ R f t⟫_ℂ

/-- The complement `r(t) = Q(A(t)q + r(t))`. -/
def compl (R : ℝ) (f : XG) (t : ℝ) : XG := projQ q qd (normState lam κ R f t)

/-- `M(t) = sup_{0 ≤ s ≤ t}|A(s)|`. -/
def ampSup (R : ℝ) (f : XG) (t : ℝ) : ℝ := runningSup (fun s => ‖amp lam κ qd R f s‖) 0 t

/-- **The arbitrary-data inequalities `eq:st18-t00094`** (lines 1792–1803, B0117) with constants
`b₀, C, g`, `β(t) = 1/(R - t)`: for every datum `f ∈ X_G` at `R` and `0 ≤ t` with
`θ = R - t ≥ b₀`,
`‖r(t)‖ ≤ Ce^{-gt}‖Qf‖ + Cβ(t)M(t)` and
`|A(t) - ℓf| ≤ Cβ(t)‖Qf‖ + C∫₀^t β(s)²M(s)ds`. -/
def ArbitraryDataBounds (b₀ C g : ℝ) : Prop :=
  ∀ (R t : ℝ) (f : XG), 0 ≤ t → b₀ ≤ R - t →
    ‖compl lam κ q qd R f t‖ ≤
        C * Real.exp (-(g * t)) * ‖projQ q qd f‖ + C * (R - t)⁻¹ * ampSup lam κ qd R f t ∧
      ‖amp lam κ qd R f t - ⟪qd, f⟫_ℂ‖ ≤
        C * (R - t)⁻¹ * ‖projQ q qd f‖ +
          C * ∫ s in (0 : ℝ)..t, ((R - s)⁻¹) ^ 2 * ampSup lam κ qd R f s

variable {lam κ q qd}

theorem normState_eq (R : ℝ) (f : XG) (t : ℝ) :
    normState lam κ R f t = amp lam κ qd R f t • q + compl lam κ q qd R f t := by
  rw [compl, projQ, amp]
  abel

/-- The normalized evolution starts from the prescribed datum at turnover time zero. -/
theorem normState_zero {R : ℝ} (hR : 0 < R) (f : XG) :
    normState lam κ R f 0 = f := by
  rw [normState, normProp_apply]
  simp only [sub_zero]
  rw [S_self hR]
  simp [gauge_mul_gaugeInv hR]

theorem amp_zero {R : ℝ} (hR : 0 < R) (f : XG) :
    amp lam κ qd R f 0 = ⟪qd, f⟫_ℂ := by
  rw [amp, normState_zero hR]

theorem compl_zero {R : ℝ} (hR : 0 < R) (f : XG) :
    compl lam κ q qd R f 0 = projQ q qd f := by
  rw [compl, normState_zero hR]

/-- The normalized amplitude is the scalar gauge times the concrete amplitude mild equation.
This is the initial-data form used to obtain the B0115 amplitude variation identity. -/
theorem amp_mild {R t : ℝ} (hθ : 0 < R - t) (hθR : R - t ≤ R) (f : XG) :
    amp lam κ qd R f t =
      (gauge lam κ (R - t) * gaugeInv lam κ R) *
        (⟪qd, expD (Real.log R - Real.log (R - t)) f⟫_ℂ +
          ∫ u in (-R)..(-(R - t)),
            ⟪qd, freeU (-(R - t)) u (B0012.L0 (S (-u) R f))⟫_ℂ) := by
  rw [amp, normState, normProp_apply, inner_smul_right]
  rw [inner_qd_S_mild qd hθ hθR f]

/-- The normalized complementary state is the gauge times the concrete projected mild equation.
This is the initial-data complement formula before passing to the L₀-based stable evolution. -/
theorem compl_mild {R t : ℝ} (hθ : 0 < R - t) (hθR : R - t ≤ R) (f : XG) :
    compl lam κ q qd R f t =
      (gauge lam κ (R - t) * gaugeInv lam κ R) •
        (projQ q qd (expD (Real.log R - Real.log (R - t)) f) +
          ∫ u in (-R)..(-(R - t)),
            projQ q qd (freeU (-(R - t)) u (B0012.L0 (S (-u) R f)))) := by
  let α := gauge lam κ (R - t) * gaugeInv lam κ R
  let T := projQCLM q qd
  calc compl lam κ q qd R f t = projQ q qd (α • S (R - t) R f) := by
        simp [compl, normState, normProp_apply, α]
    _ = T (α • S (R - t) R f) := (projQCLM_apply q qd _).symm
    _ = α • T (S (R - t) R f) := map_smul T α _
    _ = α • (projQ q qd (expD (Real.log R - Real.log (R - t)) f) +
          ∫ u in (-R)..(-(R - t)),
            projQ q qd (freeU (-(R - t)) u (B0012.L0 (S (-u) R f)))) := by
        exact congrArg (fun z => α • z) (projQ_S_mild q qd hθ hθR f)

/-! ## Continuity -/

variable (lam κ) in
theorem continuousOn_gauge : ContinuousOn (gauge lam κ) (Ioi 0) := by
  unfold gauge
  refine ContinuousOn.mul ?_ ?_
  · exact (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).continuousOn
  · exact ContinuousOn.cpow Complex.continuous_ofReal.continuousOn continuousOn_const
      fun θ hθ => Complex.ofReal_mem_slitPlane.2 hθ

theorem continuousOn_normState {b₀ R : ℝ} (hb₀ : 0 < b₀) (f : XG) :
    ContinuousOn (normState lam κ R f) (Icc 0 (R - b₀)) := by
  have hmaps : MapsTo (fun t : ℝ => R - t) (Icc 0 (R - b₀)) (Icc b₀ R) := fun t ht =>
    ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hsub : ContinuousOn (fun t : ℝ => R - t) (Icc 0 (R - b₀)) :=
    (continuous_const.sub continuous_id).continuousOn
  have hS : ContinuousOn (fun t => S (R - t) R f) (Icc 0 (R - b₀)) :=
    (continuousOn_S_left hb₀ f).comp hsub hmaps
  have hg : ContinuousOn (fun t => gauge lam κ (R - t) * gaugeInv lam κ R) (Icc 0 (R - b₀)) :=
    ((continuousOn_gauge lam κ).comp hsub fun t ht => hb₀.trans_le (hmaps ht).1).mul
      continuousOn_const
  exact hg.smul hS

theorem continuousOn_amp {b₀ R : ℝ} (hb₀ : 0 < b₀) (f : XG) :
    ContinuousOn (fun s => ‖amp lam κ qd R f s‖) (Icc 0 (R - b₀)) :=
  (continuousOn_const.inner (continuousOn_normState hb₀ f)).norm

/-! ## The integral `∫₀^t β² = θ⁻¹ - R⁻¹` -/

theorem continuousOn_inv_sq {R t : ℝ} (ht : t < R) :
    ContinuousOn (fun s : ℝ => ((R - s)⁻¹) ^ 2) (Icc 0 t) :=
  ((continuous_sub_left R).continuousOn.inv₀ fun s hs =>
    sub_ne_zero.2 (ne_of_gt (by linarith [hs.2]))).pow 2

theorem integral_inv_sq {R t : ℝ} (ht0 : 0 ≤ t) (ht : t < R) :
    ∫ s in (0 : ℝ)..t, ((R - s)⁻¹) ^ 2 = (R - t)⁻¹ - R⁻¹ := by
  have hderiv : ∀ s ∈ uIcc 0 t, HasDerivAt (fun s : ℝ => (R - s)⁻¹) (((R - s)⁻¹) ^ 2) s := by
    intro s hs
    rw [uIcc_of_le ht0] at hs
    have hne : R - s ≠ 0 := by linarith [hs.2]
    have h := ((hasDerivAt_id' s).const_sub R).inv hne
    rw [neg_neg, one_div, ← inv_pow] at h
    exact h
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((continuousOn_inv_sq ht).intervalIntegrable_of_Icc ht0)]
  simp

/-! ## Gronwall on the running maximum -/

section Bounds

variable {b₀ C g : ℝ} (hb₀ : 0 < b₀) (hC : 0 ≤ C) (hg : 0 ≤ g)
  (hB : ArbitraryDataBounds lam κ q qd b₀ C g)
include hb₀ hC hB

/-- **Gronwall** (`eq:st18-t00093`, `eq:st18-t00094`): `M(t) ≤ (|ℓf| + Cb₀⁻¹‖Qf‖)e^{C/b₀}` for
`0 ≤ t ≤ R - b₀`. -/
theorem ampSup_le {R t : ℝ} (f : XG) (ht0 : 0 ≤ t) (ht : t ≤ R - b₀) :
    ampSup lam κ qd R f t ≤
      (‖⟪qd, f⟫_ℂ‖ + C * b₀⁻¹ * ‖projQ q qd f‖) * Real.exp (C * b₀⁻¹) := by
  set T := R - b₀
  have hA := continuousOn_amp (lam := lam) (κ := κ) (qd := qd) (R := R) hb₀ f
  have hβ : ContinuousOn (fun s : ℝ => C * ((R - s)⁻¹) ^ 2) (Icc 0 T) :=
    continuousOn_const.mul (continuousOn_inv_sq (by linarith))
  have hβ0 : ∀ s ∈ Icc (0 : ℝ) T, 0 ≤ C * ((R - s)⁻¹) ^ 2 := fun s _ => by positivity
  have hstep : ∀ u ∈ Icc (0 : ℝ) T, ‖amp lam κ qd R f u‖ ≤
      (‖⟪qd, f⟫_ℂ‖ + C * b₀⁻¹ * ‖projQ q qd f‖) +
        ∫ s in (0 : ℝ)..u, C * ((R - s)⁻¹) ^ 2 * runningSup (fun s => ‖amp lam κ qd R f s‖) 0 s := by
    intro u hu
    have h2 := (hB R u f hu.1 (by linarith [hu.2])).2
    have hinv : (R - u)⁻¹ ≤ b₀⁻¹ := inv_anti₀ hb₀ (by linarith [hu.2])
    have h3 : C * (R - u)⁻¹ * ‖projQ q qd f‖ ≤ C * b₀⁻¹ * ‖projQ q qd f‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hinv hC) (norm_nonneg _)
    have h4 : C * ∫ s in (0 : ℝ)..u, ((R - s)⁻¹) ^ 2 * ampSup lam κ qd R f s =
        ∫ s in (0 : ℝ)..u, C * ((R - s)⁻¹) ^ 2 * runningSup (fun s => ‖amp lam κ qd R f s‖) 0 s := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun s _ => ?_
      simp only [ampSup]
      ring
    have h5 := norm_sub_norm_le (amp lam κ qd R f u) ⟪qd, f⟫_ℂ
    linarith
  have hG := runningSup_le_exp_of_le_integral hA (fun _ _ => norm_nonneg _) hβ hβ0 hstep t
    ⟨ht0, ht⟩
  have hint : ∫ s in (0 : ℝ)..t, C * ((R - s)⁻¹) ^ 2 = C * ((R - t)⁻¹ - R⁻¹) := by
    rw [intervalIntegral.integral_const_mul, integral_inv_sq ht0 (by linarith)]
  rw [hint] at hG
  refine hG.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity))
  have hR : 0 ≤ R⁻¹ := inv_nonneg.2 (by linarith)
  have hinv : (R - t)⁻¹ ≤ b₀⁻¹ := inv_anti₀ hb₀ (by linarith)
  nlinarith

include hg in
/-- **Uniform propagation** (B0117, line 1803): the normalized evolution is uniformly bounded on
`θ ≥ b₀`. -/
theorem uniformPropagation_of_bounds :
    ∃ K : ℝ, ∀ θ θ' : ℝ, b₀ ≤ θ → θ ≤ θ' → ‖normProp lam κ θ θ'‖ ≤ K := by
  set E := Real.exp (C * b₀⁻¹)
  set P := 1 + ‖qd‖ * ‖q‖
  set K₀ := (‖qd‖ + C * b₀⁻¹ * P) * E
  have hb₀' : 0 ≤ b₀⁻¹ := inv_nonneg.2 hb₀.le
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have hP : 0 ≤ P := by positivity
  have hK₀ : 0 ≤ K₀ := by positivity
  refine ⟨K₀ * ‖q‖ + C * P + C * b₀⁻¹ * K₀, fun θ θ' hθ hθθ' => ?_⟩
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun f => ?_
  set t := θ' - θ
  have ht0 : 0 ≤ t := by simp only [t]; linarith
  have htT : t ≤ θ' - b₀ := by simp only [t]; linarith
  have hθt : θ' - t = θ := by simp only [t]; ring
  have hQf : ‖projQ q qd f‖ ≤ P * ‖f‖ := by
    unfold projQ
    refine (norm_sub_le _ _).trans ?_
    rw [norm_smul]
    have := norm_inner_le_norm (𝕜 := ℂ) qd f
    have hq := norm_nonneg q
    nlinarith
  have hlf : ‖⟪qd, f⟫_ℂ‖ ≤ ‖qd‖ * ‖f‖ := norm_inner_le_norm _ _
  have hM : ampSup lam κ qd θ' f t ≤ K₀ * ‖f‖ := by
    refine (ampSup_le hb₀ hC hB f ht0 htT).trans ?_
    have h1 : ‖⟪qd, f⟫_ℂ‖ + C * b₀⁻¹ * ‖projQ q qd f‖ ≤ (‖qd‖ + C * b₀⁻¹ * P) * ‖f‖ := by
      have := mul_le_mul_of_nonneg_left hQf (mul_nonneg hC hb₀')
      nlinarith
    calc (‖⟪qd, f⟫_ℂ‖ + C * b₀⁻¹ * ‖projQ q qd f‖) * E ≤ (‖qd‖ + C * b₀⁻¹ * P) * ‖f‖ * E :=
          mul_le_mul_of_nonneg_right h1 hE
      _ = K₀ * ‖f‖ := by simp only [K₀]; ring
  have hamp : ‖amp lam κ qd θ' f t‖ ≤ ampSup lam κ qd θ' f t :=
    le_runningSup (continuousOn_amp (lam := lam) (κ := κ) (qd := qd) (R := θ') hb₀ f)
      ⟨ht0, le_rfl⟩ htT
  obtain ⟨hr, -⟩ := hB θ' t f ht0 (by linarith)
  have hexp : Real.exp (-(g * t)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  have hinv : (θ' - t)⁻¹ ≤ b₀⁻¹ := inv_anti₀ hb₀ (by linarith)
  have hr' : ‖compl lam κ q qd θ' f t‖ ≤ C * P * ‖f‖ + C * b₀⁻¹ * (K₀ * ‖f‖) := by
    refine hr.trans (add_le_add ?_ ?_)
    · calc C * Real.exp (-(g * t)) * ‖projQ q qd f‖ ≤ C * 1 * (P * ‖f‖) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hexp hC) hQf (norm_nonneg _) (by positivity)
        _ = C * P * ‖f‖ := by ring
    · have hM0 : 0 ≤ ampSup lam κ qd θ' f t := (norm_nonneg _).trans hamp
      exact mul_le_mul (mul_le_mul_of_nonneg_left hinv hC) hM hM0 (by positivity)
  have hN : normProp lam κ θ θ' f = normState lam κ θ' f t := by
    rw [normState, hθt]
  rw [hN, normState_eq (q := q) (qd := qd)]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul]
  calc ‖amp lam κ qd θ' f t‖ * ‖q‖ + ‖compl lam κ q qd θ' f t‖
      ≤ K₀ * ‖f‖ * ‖q‖ + (C * P * ‖f‖ + C * b₀⁻¹ * (K₀ * ‖f‖)) :=
        add_le_add (mul_le_mul_of_nonneg_right (hamp.trans hM) (norm_nonneg _)) hr'
    _ = (K₀ * ‖q‖ + C * P + C * b₀⁻¹ * K₀) * ‖f‖ := by ring

/-- **Relative growth** (B0116, `eq:st18-t00093`): with `ℓq = 1`, `‖Y_R(θ) - q‖ ≤ K/θ` for
`b₀ ≤ θ ≤ R`. -/
theorem relativeGrowth_of_bounds (hnorm : ⟪qd, q⟫_ℂ = 1) :
    ∃ K : ℝ, ∀ θ R : ℝ, b₀ ≤ θ → θ ≤ R → ‖stateY lam κ q R θ - q‖ ≤ K / θ := by
  set E := Real.exp (C * b₀⁻¹)
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have hQq : projQ q qd q = 0 := by rw [projQ, hnorm, one_smul, sub_self]
  refine ⟨C * E * (‖q‖ + 1), fun θ R hθ hθR => ?_⟩
  set t := R - θ
  have ht0 : 0 ≤ t := by simp only [t]; linarith
  have htT : t ≤ R - b₀ := by simp only [t]; linarith
  have hθt : R - t = θ := by simp only [t]; ring
  have hθ0 : 0 < θ := hb₀.trans_le hθ
  have hMle : ∀ s ∈ Icc (0 : ℝ) t, ampSup lam κ qd R q s ≤ E := by
    intro s hs
    have h := ampSup_le hb₀ hC hB (R := R) q hs.1 (hs.2.trans htT)
    rwa [hnorm, hQq, norm_zero, mul_zero, add_zero, norm_one, one_mul] at h
  obtain ⟨hr, ha⟩ := hB R t q ht0 (by linarith)
  rw [hQq, norm_zero, mul_zero, zero_add] at hr
  rw [hQq, norm_zero, mul_zero, zero_add, hnorm] at ha
  have hA := continuousOn_amp (lam := lam) (κ := κ) (qd := qd) (R := R) (f := q) hb₀
  have hint : ∫ s in (0 : ℝ)..t, ((R - s)⁻¹) ^ 2 * ampSup lam κ qd R q s ≤
      ∫ s in (0 : ℝ)..t, ((R - s)⁻¹) ^ 2 * E := by
    refine intervalIntegral.integral_mono_on ht0 ?_ ?_ fun s hs =>
      mul_le_mul_of_nonneg_left (hMle s hs) (by positivity)
    · exact ((continuousOn_inv_sq (by linarith)).mul
        ((continuousOn_runningSup hA).mono (Icc_subset_Icc le_rfl htT))).intervalIntegrable_of_Icc
          ht0
    · exact ((continuousOn_inv_sq (by linarith)).mul continuousOn_const).intervalIntegrable_of_Icc
        ht0
  rw [intervalIntegral.integral_mul_const, integral_inv_sq ht0 (by linarith), hθt] at hint
  have hR : 0 ≤ R⁻¹ := inv_nonneg.2 (by linarith)
  have hθinv : 0 ≤ θ⁻¹ := inv_nonneg.2 hθ0.le
  have ha' : ‖amp lam κ qd R q t - 1‖ ≤ C * E * θ⁻¹ := by
    refine ha.trans ?_
    have : C * ((θ⁻¹ - R⁻¹) * E) ≤ C * (θ⁻¹ * E) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by linarith) hE) hC
    calc C * ∫ s in (0 : ℝ)..t, ((R - s)⁻¹) ^ 2 * ampSup lam κ qd R q s
        ≤ C * ((θ⁻¹ - R⁻¹) * E) := mul_le_mul_of_nonneg_left hint hC
      _ ≤ C * (θ⁻¹ * E) := this
      _ = C * E * θ⁻¹ := by ring
  have hr' : ‖compl lam κ q qd R q t‖ ≤ C * E * θ⁻¹ := by
    refine hr.trans ?_
    rw [hθt]
    have hM := hMle t ⟨ht0, le_rfl⟩
    calc C * θ⁻¹ * ampSup lam κ qd R q t ≤ C * θ⁻¹ * E :=
          mul_le_mul_of_nonneg_left hM (mul_nonneg hC hθinv)
      _ = C * E * θ⁻¹ := by ring
  have hY : stateY lam κ q R θ = normState lam κ R q t := by
    rw [normState, hθt, normProp_q]
  have hdiff : normState lam κ R q t - q = (amp lam κ qd R q t - 1) • q + compl lam κ q qd R q t := by
    rw [sub_smul, one_smul, normState_eq (q := q) (qd := qd)]
    abel
  rw [hY, hdiff, div_eq_mul_inv]
  calc ‖(amp lam κ qd R q t - 1) • q + compl lam κ q qd R q t‖
      ≤ ‖amp lam κ qd R q t - 1‖ * ‖q‖ + ‖compl lam κ q qd R q t‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul]
    _ ≤ C * E * θ⁻¹ * ‖q‖ + C * E * θ⁻¹ :=
        add_le_add (mul_le_mul_of_nonneg_right ha' (norm_nonneg _)) hr'
    _ = C * E * (‖q‖ + 1) * θ⁻¹ := by ring

end Bounds

end UnforcedLeray.Cons.G3b
