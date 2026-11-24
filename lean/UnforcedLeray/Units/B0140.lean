import UnforcedLeray.Lib.Train.Ops
import UnforcedLeray.Lib.Gaussian.Periodization
import UnforcedLeray.Analysis.GaussianVortex.PlanarEuler
import UnforcedLeray.Analysis.GaussianVortex.PlanarIntegrals

/-!
# B0140 — Gaussian datum and the train initial-value problem (`eq:st18-t00140`)

Blueprint unit **B0140**, label `eq:st18-t00140` (with `eq:m3-train`, `eq:st18-t00139`),
`paper/main.tex` lines 2045–2057 and 2131–2151 (section `sec:train`); infrastructure INF16,
INF27. Split as the blueprint critic asks (`blueprint/critic.md`, §6 and the B0140 row): the
datum definitions and their stated properties are proved; the existence of the train is stated
conditionally on a named hypothesis, `TrainIVPSolvable` (fixed `ν, c`) or `TrainExistence`
(the `c = ν⁻²` family), matching INF16 T15 `TrainData` / `trainData_exists`
(`scoping/INF16-Cylinder2DNS.md`, §5 T15; decision D8 of `scoping/README.md`).

**Statement (tex lines 2131–2151).**
`ψ₀(q,η) = -2e^{-(q²+η²)/4}`, `v₀ = ∇^⊥ψ₀ = e^{-(q²+η²)/4}(-η, q)` with
`∇^⊥ = (-∂_η, ∂_q)`; its vorticity is `ω₀ = (2 - |x|²/2)e^{-|x|²/4}`, a Gaussian stream vortex
with zero circulation; no compact-support replacement is made. Let `v` be the global smooth
finite-energy solution on `C_c` of `v_s + v·∇v - νΔv + ∇p = 0`, `∇·v = 0`,
`v(q,η,0) = ∑_{n∈ℤ} v₀(q - nc, η)`.
**Lines 2045–2057.** The same system (`eq:m3-train`) with `v(0) = P_c v₀`; the decaying stream
is `v = ∇^⊥ψ` with `ψ(0) = -2∑ₙ e^{-|z-(nc,0)|²/4}`; the field is `c`-periodic and centrally
odd; spatial energy norms use one unnormalized cell. (The parameters `a(s) = 1 + νs`,
`s_c = (c²-1)/ν`, the overlap variable and `e_c` of lines 2052–2057 are unit B0139,
`Lib/Train/Params.lean`: `Train.width`, `Train.sOv`, `Train.ovT`, `Train.ec`.)

**Conventions.** `Plane = ℝ × ℝ`, `(q, η) = (z.1, z.2)`. The planar datum objects are the
compiled library ones (`GaussianVortex.streamfunction`, `velocity`, `vorticity`,
`perpendicularGradient`, `curl`; `lean/UnforcedLeray/Analysis/GaussianVortex/PlanarDefs.lean`),
reused, not redefined. `P_c f(q,η) = ∑ₙ f(q - nc, η)` is `Gaussian.periodize` (INF22 G7,
`Lib/Gaussian/Periodization.lean`). Cylinder fields follow decision D1: `c`-periodic
functions on `Plane` with vector values in `Train.Vec = EuclideanSpace ℝ (Fin 2)`; the cell is
`Cyl.cell c = [-c/2, c/2) × ℝ` with Lebesgue measure (the unnormalized cell of line 2051).
Partial derivatives are the classical `deriv`-based partials; every one that enters a
statement is accompanied by a `HasDerivAt` fact (`hasDerivAt_trainStream_q`, …), so no junk
value of `deriv` enters. Series over `ℤ` are `tsum`s, proved absolutely summable for `c ≠ 0`
(`hasSum_trainVelocity`, `hasSum_trainStream`). The period obeys `c = ν^{-ρ} ≥ 1`
(tex 2043–2044, `0 < ν ≤ 1`); the only place a lower bound on `c` is used is the decay of the
stream datum, stated for `1 ≤ c`.

**The solution object (the part needing INF16).** `IsTrain ν c v p ψ` is the classical
meaning of line 2141: `v, p` smooth on `[0,∞) × ℝ²` (one-sided at `s = 0`, D8), `c`-periodic,
divergence free, the momentum equation for `s > 0`, `v(0) = P_c v₀`, finite cell energy, the
pressure fixed by decay (tex 2160–2161), a differentiable decaying stream `v = ∇^⊥ψ`
(line 2049), and central oddness (line 2051). `TrainSol ν c` bundles a solution
(INF16 T15 `TrainData`). The existence (Gallay–Slijepčević 2015, Thm 1.1 and Rem. 1.3(2),
cited at tex 2152–2155, unit B0141; INF16 T1–T15) is not built: it is the hypothesis
`TrainIVPSolvable ν c := Nonempty (TrainSol ν c)`, resp. `TrainExistence`.
From it the unit derives the stated identification `ψ(0) = -2∑ₙ e^{-|z-(nc,0)|²/4}`
(`IsTrain.stream_zero`: the two streams have the same perpendicular gradient and both decay).

**Main declarations.** Datum: `streamfunction_apply`, `velocity_apply`,
`perpendicularGradient_streamfunction'`, `curl_velocity_apply`, `zero_circulation`,
`not_hasCompactSupport_velocity`. Train datum: `trainVelocity` (`P_c v₀`), `trainStream`
(`ψ(0)`), `trainDatum`, `hasSum_trainVelocity`, `trainStream_apply`,
`perpendicularGradient_trainStream`, `trainDatum_periodic`, `trainDatum_neg`,
`divergence_trainDatum`, `curl_trainDatum`, `tendsto_trainStream`,
`trainVelocity_eq_periodicVelocity` (link to unit B0146). IVP: `IsTrain`, `TrainSol`,
`TrainIVPSolvable`, `TrainExistence`, `train`, `IsTrain.stream_zero`, `train_ivp`,
`train_ivp_per`. Whole unit: `unit_B0140`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.B0140

open UnforcedLeray.GaussianVortex
open UnforcedLeray.Train (Vec toVec)

/-! ### 1. The Gaussian datum (`eq:st18-t00139`, tex lines 2131–2140) -/

/-- `ψ₀(q,η) = -2 e^{-(q²+η²)/4}` (tex line 2133). -/
theorem streamfunction_apply (q η : ℝ) :
    streamfunction (q, η) = -2 * Real.exp (-(q ^ 2 + η ^ 2) / 4) := by
  simp only [streamfunction, planarGaussian, radiusSq, neg_div]

/-- `v₀ = e^{-(q²+η²)/4} (-η, q)` (tex line 2134). -/
theorem velocity_apply (q η : ℝ) :
    velocity (q, η) = Real.exp (-(q ^ 2 + η ^ 2) / 4) • (-η, q) := by
  ext <;> simp only [velocity, planarGaussian, radiusSq, neg_div, Prod.smul_mk, smul_eq_mul] <;>
    ring

/-- `v₀ = ∇^⊥ψ₀` with `∇^⊥ = (-∂_η, ∂_q)` (tex lines 2134–2136); the library identity
`perpendicularGradient_streamfunction`, as an equality of fields. -/
theorem perpendicularGradient_streamfunction' : perpendicularGradient streamfunction = velocity :=
  funext perpendicularGradient_streamfunction

/-- The `q`-partial of `ψ₀` is a genuine derivative: `∂_q ψ₀ = v₀²`. -/
theorem hasDerivAt_streamfunction_q (w : Plane) :
    HasDerivAt (fun t => streamfunction (t, w.2)) (velocity w).2 w.1 := by
  obtain ⟨q, η⟩ := w
  refine ((hasDerivAt_planarGaussian_x q η).const_mul (-2)).congr_deriv ?_
  show -2 * (-q / 2 * planarGaussian (q, η)) = q * planarGaussian (q, η)
  ring

/-- The `η`-partial of `ψ₀` is a genuine derivative: `∂_η ψ₀ = -v₀¹`. -/
theorem hasDerivAt_streamfunction_η (w : Plane) :
    HasDerivAt (fun t => streamfunction (w.1, t)) (-(velocity w).1) w.2 := by
  obtain ⟨q, η⟩ := w
  refine ((hasDerivAt_planarGaussian_y q η).const_mul (-2)).congr_deriv ?_
  show -2 * (-η / 2 * planarGaussian (q, η)) = -(-η * planarGaussian (q, η))
  ring

/-- `ω₀ = curl v₀ = (2 - |x|²/2) e^{-|x|²/4}` (tex lines 2137–2139). -/
theorem curl_velocity_apply (z : Plane) :
    curl velocity z = (2 - radiusSq z / 2) * Real.exp (-(radiusSq z / 4)) := by
  rw [curl_velocity]; rfl

/-- Zero circulation (tex line 2140): `ω₀` is integrable on `ℝ²` (so the integral is not a
junk value) and `∫_{ℝ²} ω₀ = 0`. -/
theorem zero_circulation : Integrable (curl velocity) ∧ ∫ z, curl velocity z = 0 := by
  have h : curl velocity = vorticity := funext curl_velocity
  rw [h]
  exact ⟨integrable_vorticity, integral_vorticity_eq_zero⟩

/-- `v₀(z) ≠ 0` for `z ≠ 0`. -/
theorem velocity_ne_zero {z : Plane} (hz : z ≠ 0) : velocity z ≠ 0 := by
  intro h
  have hg : planarGaussian z ≠ 0 := (Real.exp_pos _).ne'
  have h1 : -z.2 * planarGaussian z = 0 := congrArg Prod.fst h
  have h2 : z.1 * planarGaussian z = 0 := congrArg Prod.snd h
  apply hz
  refine Prod.ext ?_ ?_
  · exact (mul_eq_zero.mp h2).resolve_right hg
  · have := (mul_eq_zero.mp h1).resolve_right hg
    simpa using this

/-- "No compact-support replacement is made" (tex line 2140): the datum `v₀` is the actual
Gaussian field, which does not have compact support. -/
theorem not_hasCompactSupport_velocity : ¬ HasCompactSupport velocity := by
  intro h
  obtain ⟨R, hR⟩ :=
    (Metric.isBounded_iff_subset_closedBall (0 : Plane)).mp h.isCompact.isBounded
  have hpos : 0 < |R| + 1 := by positivity
  have hz : ((|R| + 1, 0) : Plane) ≠ 0 := by
    intro h0
    have : |R| + 1 = 0 := congrArg Prod.fst h0
    linarith
  have hmem : ((|R| + 1, 0) : Plane) ∈ tsupport velocity :=
    subset_tsupport _ (Function.mem_support.mpr (velocity_ne_zero hz))
  have hb := hR hmem
  rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def] at hb
  simp only [norm_zero, Real.norm_eq_abs] at hb
  rw [max_eq_left (abs_nonneg _), abs_of_pos hpos] at hb
  linarith [le_abs_self R]

/-! ### 2. The train datum `P_c v₀` and its stream `ψ(0)` (tex lines 2047–2050, 2141–2147) -/

/-- The train datum `P_c v₀(q,η) = ∑_{n∈ℤ} v₀(q - nc, η)` (tex lines 2047, 2146). -/
def trainVelocity (c : ℝ) : Plane → Plane := Gaussian.periodize c velocity

/-- The datum stream `ψ(0) = P_c ψ₀ = -2 ∑ₙ e^{-|z-(nc,0)|²/4}` (tex line 2050). -/
def trainStream (c : ℝ) : Plane → ℝ := Gaussian.periodize c streamfunction

/-- The train datum as a cylinder field with values in `Vec = EuclideanSpace ℝ (Fin 2)`
(decision D1): the initial value of `eq:st18-t00140`. -/
def trainDatum (c : ℝ) (z : Plane) : Vec := toVec (trainVelocity c z)

theorem trainVelocity_apply (c : ℝ) (z : Plane) :
    trainVelocity c z = ∑' n : ℤ, velocity (z.1 - n * c, z.2) := rfl

theorem trainDatum_apply (c : ℝ) (z : Plane) :
    trainDatum c z = toVec (∑' n : ℤ, velocity (z.1 - n * c, z.2)) := rfl

/-- `ψ(0)(q,η) = -2 ∑ₙ e^{-((q-nc)² + η²)/4}` (tex line 2050). -/
theorem trainStream_apply (c q η : ℝ) :
    trainStream c (q, η) = -2 * ∑' n : ℤ, Real.exp (-((q - n * c) ^ 2 + η ^ 2) / 4) := by
  simp only [trainStream, Gaussian.periodize, streamfunction_apply]
  rw [tsum_mul_left]

/-! #### Gaussian decay of the summands (unit B0146 lattice-sum calculus) -/

theorem velocity_fst_eq : (fun w => (velocity w).1) = B0146.u1 1 := by
  funext w
  simp only [velocity, B0146.u1, B0113.gw, planarGaussian, inv_one, one_pow, one_mul]
  ring

theorem velocity_snd_eq : (fun w => (velocity w).2) = B0146.u2 1 := by
  funext w
  simp only [velocity, B0146.u2, B0113.gw, planarGaussian, inv_one, one_pow, one_mul]

theorem velocity_eq_vExp : velocity = B0113.vExp 1 := by
  funext w
  refine Prod.ext ?_ ?_
  · exact congrFun velocity_fst_eq w
  · exact congrFun velocity_snd_eq w

theorem xdecay_velocity_fst : B0146.XDecay (fun w => (velocity w).1) := by
  rw [velocity_fst_eq]; exact B0146.xd (B0146.gf_u1 one_pos)

theorem xdecay_velocity_snd : B0146.XDecay (fun w => (velocity w).2) := by
  rw [velocity_snd_eq]; exact B0146.xd (B0146.gf_u2 one_pos)

theorem xdecay_streamfunction : B0146.XDecay streamfunction := by
  refine ⟨2, 1 / 4, by norm_num, by norm_num, fun w => ?_⟩
  simp only [streamfunction, planarGaussian, abs_mul, abs_neg, abs_two, Real.abs_exp]
  gcongr
  simp only [radiusSq]
  nlinarith [sq_nonneg w.2]

theorem xdecay_neg {g : Plane → ℝ} (hg : B0146.XDecay g) : B0146.XDecay (fun w => -g w) := by
  obtain ⟨K, β, hK, hβ, hb⟩ := hg
  exact ⟨K, β, hK, hβ, fun w => by rw [abs_neg]; exact hb w⟩

/-- Componentwise form of the datum (lattice sums of unit B0146). -/
theorem trainVelocity_eq_latticeSum {c : ℝ} (hc : c ≠ 0) (z : Plane) :
    trainVelocity c z = (B0146.latticeSum c (fun w => (velocity w).1) z,
      B0146.latticeSum c (fun w => (velocity w).2) z) :=
  ((xdecay_velocity_fst.hasSum hc z).prodMk (xdecay_velocity_snd.hasSum hc z)).tsum_eq

/-- The series `∑ₙ v₀(q - nc, η)` converges (absolutely) to `P_c v₀(q,η)` for every `c ≠ 0`;
so the `tsum` in `trainVelocity` is a genuine sum. -/
theorem hasSum_trainVelocity {c : ℝ} (hc : c ≠ 0) (z : Plane) :
    HasSum (fun n : ℤ => velocity (z.1 - n * c, z.2)) (trainVelocity c z) := by
  have h := (xdecay_velocity_fst.hasSum hc z).prodMk (xdecay_velocity_snd.hasSum hc z)
  have hs : Summable (fun n : ℤ => velocity (z.1 - n * c, z.2)) := h.summable
  exact hs.hasSum

/-- The series `∑ₙ ψ₀(q - nc, η)` converges (absolutely) to `ψ(0)(q,η)` for every `c ≠ 0`. -/
theorem hasSum_trainStream {c : ℝ} (hc : c ≠ 0) (z : Plane) :
    HasSum (fun n : ℤ => streamfunction (z.1 - n * c, z.2)) (trainStream c z) :=
  xdecay_streamfunction.hasSum hc z

/-- `∂_q ψ(0) = (P_c v₀)²`, a genuine derivative (termwise differentiation). -/
theorem hasDerivAt_trainStream_q {c : ℝ} (hc : c ≠ 0) (z : Plane) :
    HasDerivAt (fun t => trainStream c (t, z.2)) (trainVelocity c z).2 z.1 := by
  rw [trainVelocity_eq_latticeSum hc]
  exact B0146.hasDerivAt_latticeSum_x (g := streamfunction) (g' := fun w => (velocity w).2) hc
    hasDerivAt_streamfunction_q xdecay_streamfunction xdecay_velocity_snd z

/-- `∂_η ψ(0) = -(P_c v₀)¹`, a genuine derivative (termwise differentiation). -/
theorem hasDerivAt_trainStream_η {c : ℝ} (hc : c ≠ 0) (z : Plane) :
    HasDerivAt (fun t => trainStream c (z.1, t)) (-(trainVelocity c z).1) z.2 := by
  have h := B0146.hasDerivAt_latticeSum_y (g := streamfunction)
    (g' := fun w => -(velocity w).1) hc hasDerivAt_streamfunction_η xdecay_streamfunction
    (xdecay_neg xdecay_velocity_fst) z
  rw [trainVelocity_eq_latticeSum hc]
  refine h.congr_deriv ?_
  show B0146.latticeSum c (fun w => -(velocity w).1) z =
    -B0146.latticeSum c (fun w => (velocity w).1) z
  simp only [B0146.latticeSum, tsum_neg]

/-- `v(0) = ∇^⊥ψ(0)`: the datum is the perpendicular gradient of the datum stream
(tex lines 2049–2050), for every `c ≠ 0`. -/
theorem perpendicularGradient_trainStream {c : ℝ} (hc : c ≠ 0) :
    perpendicularGradient (trainStream c) = trainVelocity c := by
  funext z
  simp only [perpendicularGradient, partialX, partialY]
  rw [(hasDerivAt_trainStream_q hc z).deriv, (hasDerivAt_trainStream_η hc z).deriv, neg_neg]

/-! #### Periodicity and central symmetry (tex line 2051) -/

/-- `P_c v₀` is `c`-periodic. -/
theorem trainVelocity_periodic (c : ℝ) : Cyl.IsPeriodic c (trainVelocity c) :=
  fun z => Gaussian.periodize_add_period c velocity z.1 z.2

/-- `ψ(0)` is `c`-periodic. -/
theorem trainStream_periodic (c : ℝ) : Cyl.IsPeriodic c (trainStream c) :=
  fun z => Gaussian.periodize_add_period c streamfunction z.1 z.2

/-- The train datum is `c`-periodic (tex line 2051). -/
theorem trainDatum_periodic (c : ℝ) : Cyl.IsPeriodic c (trainDatum c) :=
  fun z => congrArg toVec (trainVelocity_periodic c z)

theorem velocity_neg (w : Plane) : velocity (-w) = -velocity w := by
  have hg : planarGaussian (-w) = planarGaussian w := by
    simp only [planarGaussian, radiusSq, Prod.fst_neg, Prod.snd_neg, neg_sq]
  refine Prod.ext ?_ ?_ <;> simp only [velocity, hg, Prod.fst_neg, Prod.snd_neg] <;> ring

theorem streamfunction_neg (w : Plane) : streamfunction (-w) = streamfunction w := by
  simp only [streamfunction, planarGaussian, radiusSq, Prod.fst_neg, Prod.snd_neg, neg_sq]

/-- Reflection through the origin commutes with periodization: `P_c f(-z) = P_c(f ∘ (-·))(z)`. -/
theorem periodize_neg_arg {E : Type*} [NormedAddCommGroup E] (c : ℝ) (f : Plane → E)
    (z : Plane) : Gaussian.periodize c f (-z) = Gaussian.periodize c (fun w => f (-w)) z := by
  have h := (Equiv.neg ℤ).tsum_eq (fun n : ℤ => f (-(z.1 - (n : ℝ) * c, z.2)))
  simp only [Gaussian.periodize]
  rw [← h]
  refine tsum_congr fun n => ?_
  congr 1
  refine Prod.ext ?_ ?_ <;> simp only [Equiv.neg_apply, Int.cast_neg, Prod.fst_neg, Prod.snd_neg]
  ring

/-- `P_c v₀` is centrally odd. -/
theorem trainVelocity_neg (c : ℝ) (z : Plane) : trainVelocity c (-z) = -trainVelocity c z := by
  rw [trainVelocity, periodize_neg_arg]
  simp only [velocity_neg, Gaussian.periodize, tsum_neg]

/-- `ψ(0)` is centrally even. -/
theorem trainStream_neg (c : ℝ) (z : Plane) : trainStream c (-z) = trainStream c z := by
  rw [trainStream, periodize_neg_arg]
  simp only [streamfunction_neg]

/-- The train datum is centrally odd (tex line 2051). -/
theorem trainDatum_neg (c : ℝ) (z : Plane) : trainDatum c (-z) = -trainDatum c z := by
  rw [trainDatum, trainVelocity_neg, Train.toVec_neg]; rfl

/-! #### Divergence, vorticity and decay of the datum -/

theorem trainDatum_comp_zero {c : ℝ} (hc : c ≠ 0) :
    (fun w => trainDatum c w 0) = B0146.latticeSum c (B0146.u1 1) := by
  funext w
  rw [trainDatum, Train.toVec_zero, trainVelocity_eq_latticeSum hc, velocity_fst_eq]

theorem trainDatum_comp_one {c : ℝ} (hc : c ≠ 0) :
    (fun w => trainDatum c w 1) = B0146.latticeSum c (B0146.u2 1) := by
  funext w
  rw [trainDatum, Train.toVec_one, trainVelocity_eq_latticeSum hc, velocity_snd_eq]

/-- The datum is divergence free, `∇·(P_c v₀) = 0` (compatibility with `∇·v = 0`,
tex line 2146), with genuine partials (`B0146.dX_u1`, `B0146.dY_u2`). -/
theorem divergence_trainDatum {c : ℝ} (hc : c ≠ 0) (z : Plane) :
    Cyl.divergence (trainDatum c) z = 0 := by
  rw [Cyl.divergence, trainDatum_comp_zero hc, trainDatum_comp_one hc]
  change deriv (fun t => B0146.latticeSum c (B0146.u1 1) (t, z.2)) z.1 +
    deriv (fun t => B0146.latticeSum c (B0146.u2 1) (z.1, t)) z.2 = 0
  rw [(B0146.dX_u1 hc one_pos z).deriv, (B0146.dY_u2 hc one_pos z).deriv]
  have h := ((B0146.xd (B0146.gf_u1x one_pos)).hasSum hc z).add
    ((B0146.xd (B0146.gf_u2y one_pos)).hasSum hc z)
  have h0 : HasSum (fun n : ℤ => B0146.u1x 1 (B0146.shift c n z) +
      B0146.u2y 1 (B0146.shift c n z)) 0 := by
    simp only [B0146.div_u]
    exact hasSum_zero
  exact h.unique h0

/-- The datum vorticity is the periodized Gaussian vorticity, `curl(P_c v₀) = P_c ω₀`. -/
theorem curl_trainDatum {c : ℝ} (hc : c ≠ 0) (z : Plane) :
    Cyl.curl (trainDatum c) z = Gaussian.periodize c vorticity z := by
  rw [Cyl.curl, trainDatum_comp_zero hc, trainDatum_comp_one hc]
  change deriv (fun t => B0146.latticeSum c (B0146.u2 1) (t, z.2)) z.1 -
    deriv (fun t => B0146.latticeSum c (B0146.u1 1) (z.1, t)) z.2 = _
  rw [(B0146.dX_u2 hc one_pos z).deriv, (B0146.dY_u1 hc one_pos z).deriv]
  have h := ((B0146.xd (B0146.gf_u2x one_pos)).hasSum hc z).sub
    ((B0146.xd (B0146.gf_u1y one_pos)).hasSum hc z)
  have hv : ∀ w : Plane, B0146.u2x 1 w - B0146.u1y 1 w = vorticity w := by
    intro w
    simp only [B0146.u2x, B0146.u1y, vorticity, B0113.gw, planarGaussian, radiusSq, inv_one,
      one_pow, one_mul]
    ring
  simp only [hv] at h
  exact h.tsum_eq.symm

/-- Gaussian bound on the datum stream, uniform in `q`: `|ψ(0)(q,η)| ≤ 20 e^{-η²/4}` for
`c ≥ 1` (`Gaussian.norm_periodize_le_of_gauss`, INF22 G7). -/
theorem abs_trainStream_le {c : ℝ} (hc : 1 ≤ c) (z : Plane) :
    |trainStream c z| ≤ 20 * Real.exp (-(z.2 ^ 2 / 4)) := by
  have hf : ∀ w : Plane, ‖streamfunction w‖ ≤
      2 * Real.exp (-(w.1 ^ 2 + w.2 ^ 2) / (4 * 1)) := by
    intro w
    rw [Real.norm_eq_abs, streamfunction, planarGaussian, abs_mul, abs_neg, abs_two,
      Real.abs_exp]
    apply le_of_eq
    congr 2
    simp only [radiusSq]
    ring
  have h := Gaussian.norm_periodize_le_of_gauss (c := c) one_pos (by nlinarith) hf z
  rw [Real.norm_eq_abs] at h
  calc |trainStream c z| ≤ 10 * 2 * Real.exp (-z.2 ^ 2 / (4 * 1)) := h
    _ = 20 * Real.exp (-(z.2 ^ 2 / 4)) := by
      congr 1
      · norm_num
      · congr 1; ring

/-- The filter `|η| → ∞` on the plane is nontrivial. -/
theorem neBot_comap_abs_snd : NeBot (comap (fun z : Plane => |z.2|) atTop) := by
  refine NeBot.comap_of_range_mem inferInstance ?_
  refine mem_of_superset (Ici_mem_atTop 0) ?_
  intro x hx
  exact ⟨(0, x), abs_of_nonneg hx⟩

/-- The datum stream decays as `|η| → ∞`, uniformly in `q` (the "decaying stream" of
tex line 2049 at `s = 0`), for `c ≥ 1`. -/
theorem tendsto_trainStream {c : ℝ} (hc : 1 ≤ c) :
    Tendsto (trainStream c) (comap (fun z : Plane => |z.2|) atTop) (𝓝 0) := by
  have hsq : Tendsto (fun t : ℝ => t ^ 2 / 4) atTop atTop :=
    (tendsto_pow_atTop two_ne_zero).atTop_div_const (by norm_num)
  have hlim : Tendsto (fun t : ℝ => 20 * Real.exp (-(t ^ 2 / 4))) atTop (𝓝 0) := by
    have := (Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hsq)).const_mul 20
    simpa only [mul_zero, Function.comp_def] using this
  refine squeeze_zero_norm (fun z => ?_) (hlim.comp tendsto_comap)
  rw [Real.norm_eq_abs, Function.comp_apply, sq_abs]
  exact abs_trainStream_le hc z

/-- Link to unit B0146: the datum is the periodized heat vortex at age `0`,
`P_c v₀ = V_c(·, 0)` for every viscosity `ν` (`a(0) = 1`). -/
theorem trainVelocity_eq_periodicVelocity (ν c : ℝ) :
    trainVelocity c = B0146.periodicVelocity ν c 0 := by
  funext z
  have ha : B0113.heatWidth ν 0 = 1 := by simp [B0113.heatWidth]
  simp only [trainVelocity, Gaussian.periodize, B0146.periodicVelocity, B0146.imageVelocity,
    B0146.isoVelocity_eq, B0146.shift, ha, ← velocity_eq_vExp]

/-! ### 3. The train initial-value problem (`eq:m3-train`, `eq:st18-t00140`) -/

/-- **The train (tex lines 2045–2051, 2141–2147, 2158–2161).** `(v, p)` is a global smooth
finite-energy solution on `C_c` of `v_s + v·∇v - νΔv + ∇p = 0`, `∇·v = 0`,
`v(q,η,0) = ∑ₙ v₀(q - nc, η)`, with decaying stream `ψ`:
* `smooth_v`, `smooth_p`: smooth on `[0,∞) × ℝ²`, one-sided at `s = 0` (INF16 O1, decision D8);
  in particular every `deriv` in `momentum` is a genuine derivative;
* `periodic_v`, `periodic_p`: fields on the cylinder `C_c` (decision D1);
* `solenoidal`, `momentum` (for `s > 0`), `initial`: the system `eq:st18-t00140`;
* `finite_energy`: finite energy on one unnormalized cell (tex lines 2051, 2141);
* `pressure_decay`: the additive constant of the pressure fixed by decay (tex line 2161);
* `stream_differentiable`, `stream`, `stream_decay`: the decaying stream `v = ∇^⊥ψ`
  (tex line 2049);
* `odd`: the field is centrally odd (tex line 2051).
This is the content of INF16 T5 `CylSol` together with the stream and symmetry fields of T15
`TrainData` (scoping note `INF16-Cylinder2DNS.md`, §5); the `memH` field of `CylSol` (bypass
B1) is weakened to the manuscript's finite energy. -/
structure IsTrain (ν c : ℝ) (v : ℝ → Plane → Vec) (p : ℝ → Plane → ℝ) (ψ : ℝ → Plane → ℝ) :
    Prop where
  smooth_v : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => v x.1 x.2) (Ici 0 ×ˢ univ)
  smooth_p : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => p x.1 x.2) (Ici 0 ×ˢ univ)
  periodic_v : ∀ s, 0 ≤ s → Cyl.IsPeriodic c (v s)
  periodic_p : ∀ s, 0 ≤ s → Cyl.IsPeriodic c (p s)
  solenoidal : ∀ s, 0 ≤ s → ∀ z, Cyl.divergence (v s) z = 0
  momentum : ∀ s, 0 < s → ∀ z, Train.momentumResidual ν v p s z = 0
  initial : v 0 = trainDatum c
  finite_energy : ∀ s, 0 ≤ s → IntegrableOn (fun z => ‖v s z‖ ^ 2) (Cyl.cell c)
  pressure_decay : ∀ s, 0 ≤ s → Tendsto (p s) (comap (fun z : Plane => |z.2|) atTop) (𝓝 0)
  stream_differentiable : ∀ s, 0 ≤ s → Differentiable ℝ (ψ s)
  stream : ∀ s, 0 ≤ s → ∀ z, v s z = toVec (perpendicularGradient (ψ s) z)
  stream_decay : ∀ s, 0 ≤ s → Tendsto (ψ s) (comap (fun z : Plane => |z.2|) atTop) (𝓝 0)
  odd : ∀ s, 0 ≤ s → ∀ z, v s (-z) = -v s z

/-- A train solution with its pressure and stream (INF16 T15 `TrainData`, at period `c`). -/
structure TrainSol (ν c : ℝ) where
  /-- The velocity `v(s, z)`. -/
  v : ℝ → Plane → Vec
  /-- The pressure `p(s, z)`, fixed by decay. -/
  p : ℝ → Plane → ℝ
  /-- The decaying stream `ψ(s, z)`. -/
  ψ : ℝ → Plane → ℝ
  isTrain : IsTrain ν c v p ψ

/-- **Named hypothesis (not built): solvability of the train IVP at fixed `ν, c`.**
Existence of the global smooth finite-energy train is cited from Gallay–Slijepčević 2015,
Theorem 1.1 and Remark 1.3(2), for each fixed `c, ν > 0` (tex lines 2152–2161, unit B0141),
and is to be supplied by INF16 (T1–T15, `Lib/Train`, scoping note `INF16-Cylinder2DNS.md`;
bypasses B1–B3 build it at `c = ν⁻²`, see `TrainExistence`). -/
def TrainIVPSolvable (ν c : ℝ) : Prop := Nonempty (TrainSol ν c)

/-- **Named hypothesis (not built): INF16 T15 `trainData_exists`.** For all small `ν`, the
train with period `c = ν⁻²` (`Train.per`, the instance `ρ = 2` used by the construction,
tex lines 2044, 13718; bypass B3) exists. This is weaker than the manuscript's citation
(all `c, ν > 0`), and it is what INF16 builds. -/
def TrainExistence : Prop := ∃ ν₀ > 0, ∀ ν ∈ Ioc 0 ν₀, TrainIVPSolvable ν (Train.per ν)

/-- "Let `v` be the global smooth finite-energy solution" (tex line 2141): a chosen train,
given the solvability hypothesis. -/
def train {ν c : ℝ} (h : TrainIVPSolvable ν c) : TrainSol ν c := Classical.choice h

/-- **The stream at `s = 0` (tex line 2050).** For any train with period `c ≥ 1`,
`ψ(0) = -2 ∑ₙ e^{-|z-(nc,0)|²/4}`: `ψ(0)` and `P_c ψ₀` have the same perpendicular gradient
`P_c v₀`, so they differ by a constant, and both decay as `|η| → ∞`. -/
theorem IsTrain.stream_zero {ν c : ℝ} {v : ℝ → Plane → Vec} {p ψ : ℝ → Plane → ℝ}
    (h : IsTrain ν c v p ψ) (hc : 1 ≤ c) : ψ 0 = trainStream c := by
  have hc0 : c ≠ 0 := (lt_of_lt_of_le one_pos hc).ne'
  have hψd := h.stream_differentiable 0 le_rfl
  have hv : ∀ z, perpendicularGradient (ψ 0) z = trainVelocity c z := by
    intro z
    have e1 := h.stream 0 le_rfl z
    rw [h.initial] at e1
    exact Train.toVec_injective e1.symm
  have hq : ∀ z : Plane, HasDerivAt (fun t => ψ 0 (t, z.2) - trainStream c (t, z.2)) 0 z.1 := by
    intro z
    have hd : DifferentiableAt ℝ (fun t => ψ 0 (t, z.2)) z.1 :=
      (hψd _).comp z.1 (differentiableAt_id.prodMk (differentiableAt_const _))
    have heq : partialX (ψ 0) z = (trainVelocity c z).2 := congrArg Prod.snd (hv z)
    have h1 : HasDerivAt (fun t => ψ 0 (t, z.2)) (partialX (ψ 0) z) z.1 := hd.hasDerivAt
    rw [heq] at h1
    simpa only [sub_self] using h1.fun_sub (hasDerivAt_trainStream_q hc0 z)
  have hη : ∀ z : Plane, HasDerivAt (fun t => ψ 0 (z.1, t) - trainStream c (z.1, t)) 0 z.2 := by
    intro z
    have hd : DifferentiableAt ℝ (fun t => ψ 0 (z.1, t)) z.2 :=
      (hψd _).comp z.2 ((differentiableAt_const _).prodMk differentiableAt_id)
    have heq' : -partialY (ψ 0) z = (trainVelocity c z).1 := congrArg Prod.fst (hv z)
    have heq : partialY (ψ 0) z = -(trainVelocity c z).1 := by rw [← heq', neg_neg]
    have h1 : HasDerivAt (fun t => ψ 0 (z.1, t)) (partialY (ψ 0) z) z.2 := hd.hasDerivAt
    rw [heq] at h1
    simpa only [sub_self] using h1.fun_sub (hasDerivAt_trainStream_η hc0 z)
  have hconst : ∀ z : Plane, ψ 0 z - trainStream c z = ψ 0 (0, 0) - trainStream c (0, 0) := by
    intro z
    have hq' : ψ 0 (z.1, z.2) - trainStream c (z.1, z.2) =
        ψ 0 (0, z.2) - trainStream c (0, z.2) :=
      is_const_of_deriv_eq_zero (f := fun t => ψ 0 (t, z.2) - trainStream c (t, z.2))
        (fun t => (hq (t, z.2)).differentiableAt)
        (fun t => (hq (t, z.2)).deriv) z.1 0
    have hη' : ψ 0 (0, z.2) - trainStream c (0, z.2) = ψ 0 (0, 0) - trainStream c (0, 0) :=
      is_const_of_deriv_eq_zero (f := fun t => ψ 0 (0, t) - trainStream c (0, t))
        (fun t => (hη (0, t)).differentiableAt)
        (fun t => (hη (0, t)).deriv) z.2 0
    exact hq'.trans hη'
  have hlim : Tendsto (fun z => ψ 0 z - trainStream c z)
      (comap (fun z : Plane => |z.2|) atTop) (𝓝 0) := by
    simpa only [sub_zero] using (h.stream_decay 0 le_rfl).sub (tendsto_trainStream hc)
  have hK : ψ 0 (0, 0) - trainStream c (0, 0) = 0 := by
    have := neBot_comap_abs_snd
    have h2 : Tendsto (fun z => ψ 0 z - trainStream c z) (comap (fun z : Plane => |z.2|) atTop)
        (𝓝 (ψ 0 (0, 0) - trainStream c (0, 0))) := by
      rw [show (fun z => ψ 0 z - trainStream c z) =
        fun _ => ψ 0 (0, 0) - trainStream c (0, 0) from funext hconst]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique h2 hlim
  funext z
  have := hconst z
  rw [hK] at this
  linarith

/-- **The train IVP (`eq:st18-t00140`, tex lines 2141–2147), conditional on
`TrainIVPSolvable ν c`.** There is a train `(v, p, ψ)` (`IsTrain`: global smooth finite-energy
`c`-periodic centrally odd solution with decaying stream); its initial value is the literal
lattice sum `v(q,η,0) = ∑ₙ v₀(q - nc, η)`, it equals `∇^⊥ψ(0)`, and
`ψ(0) = -2 ∑ₙ e^{-|z-(nc,0)|²/4}` (tex line 2050). The period obeys `c ≥ 1`
(`c = ν^{-ρ}`, `0 < ν ≤ 1`, tex lines 2043–2044). -/
theorem train_ivp {ν c : ℝ} (hc : 1 ≤ c) (h : TrainIVPSolvable ν c) :
    ∃ tr : TrainSol ν c,
      (∀ z, tr.v 0 z = toVec (∑' n : ℤ, velocity (z.1 - n * c, z.2))) ∧
      (∀ z, tr.v 0 z = toVec (perpendicularGradient (trainStream c) z)) ∧
      (∀ q η, tr.ψ 0 (q, η) = -2 * ∑' n : ℤ, Real.exp (-((q - n * c) ^ 2 + η ^ 2) / 4)) := by
  obtain ⟨tr⟩ := h
  have hc0 : c ≠ 0 := (lt_of_lt_of_le one_pos hc).ne'
  refine ⟨tr, fun z => ?_, fun z => ?_, fun q η => ?_⟩
  · rw [tr.isTrain.initial]; rfl
  · rw [tr.isTrain.initial, perpendicularGradient_trainStream hc0]; rfl
  · rw [tr.isTrain.stream_zero hc, trainStream_apply]

/-- **The train IVP at `c = ν⁻²` (INF16 T15), conditional on `TrainExistence`.** For all
small `ν` there is a train with period `c = ν⁻² ≥ 1`, with the initial value and initial
stream of tex lines 2047–2050 and 2146. -/
theorem train_ivp_per (h : TrainExistence) :
    ∃ ν₀ > 0, ∀ ν ∈ Ioc 0 ν₀, ∃ tr : TrainSol ν (Train.per ν),
      (∀ z, tr.v 0 z = toVec (∑' n : ℤ, velocity (z.1 - n * Train.per ν, z.2))) ∧
      (∀ z, tr.v 0 z = toVec (perpendicularGradient (trainStream (Train.per ν)) z)) ∧
      (∀ q η, tr.ψ 0 (q, η) =
        -2 * ∑' n : ℤ, Real.exp (-((q - n * Train.per ν) ^ 2 + η ^ 2) / 4)) := by
  obtain ⟨ν₀, hν₀, hT⟩ := h
  refine ⟨min ν₀ 1, lt_min hν₀ one_pos, fun ν hν => ?_⟩
  have h1 : 1 ≤ Train.per ν := Train.one_le_per hν.1 (hν.2.trans (min_le_right _ _))
  exact train_ivp h1 (hT ν ⟨hν.1, hν.2.trans (min_le_left _ _)⟩)

/-! ### 4. The whole unit -/

/-- **Unit B0140** (tex lines 2045–2057, 2131–2151). The Gaussian datum and its stated
properties (proved), the train datum `P_c v₀` with its stream `ψ(0)` and their stated
properties (proved), and the train IVP (conditional on the named hypothesis
`TrainIVPSolvable`, INF16 T15). -/
theorem unit_B0140 :
    -- `ψ₀`, `v₀ = ∇^⊥ψ₀ = e^{-(q²+η²)/4}(-η, q)` (eq:st18-t00139)
    (∀ q η : ℝ, streamfunction (q, η) = -2 * Real.exp (-(q ^ 2 + η ^ 2) / 4)) ∧
    perpendicularGradient streamfunction = velocity ∧
    (∀ q η : ℝ, velocity (q, η) = Real.exp (-(q ^ 2 + η ^ 2) / 4) • (-η, q)) ∧
    -- `ω₀ = (2 - |x|²/2) e^{-|x|²/4}`, zero circulation, no compact support
    (∀ z, curl velocity z = (2 - radiusSq z / 2) * Real.exp (-(radiusSq z / 4))) ∧
    (Integrable (curl velocity) ∧ ∫ z, curl velocity z = 0) ∧
    ¬ HasCompactSupport velocity ∧
    -- `P_c v₀ = ∑ₙ v₀(q - nc, η)` converges, `= ∇^⊥ψ(0)`, `ψ(0) = -2∑ₙ e^{-|z-(nc,0)|²/4}`
    (∀ c : ℝ, c ≠ 0 → ∀ z, HasSum (fun n : ℤ => velocity (z.1 - n * c, z.2))
      (trainVelocity c z)) ∧
    (∀ c : ℝ, c ≠ 0 → ∀ z, HasSum (fun n : ℤ => streamfunction (z.1 - n * c, z.2))
      (trainStream c z)) ∧
    (∀ c : ℝ, c ≠ 0 → perpendicularGradient (trainStream c) = trainVelocity c) ∧
    (∀ c : ℝ, c ≠ 0 → ∀ z, HasDerivAt (fun t => trainStream c (t, z.2)) (trainVelocity c z).2 z.1
      ∧ HasDerivAt (fun t => trainStream c (z.1, t)) (-(trainVelocity c z).1) z.2) ∧
    (∀ c q η : ℝ, trainStream c (q, η) =
      -2 * ∑' n : ℤ, Real.exp (-((q - n * c) ^ 2 + η ^ 2) / 4)) ∧
    -- `c`-periodic and centrally odd; divergence free; decaying stream
    (∀ c : ℝ, Cyl.IsPeriodic c (trainDatum c)) ∧
    (∀ c : ℝ, ∀ z, trainDatum c (-z) = -trainDatum c z) ∧
    (∀ c : ℝ, c ≠ 0 → ∀ z, Cyl.divergence (trainDatum c) z = 0) ∧
    (∀ c : ℝ, 1 ≤ c → Tendsto (trainStream c) (comap (fun z : Plane => |z.2|) atTop) (𝓝 0)) ∧
    -- the train IVP (eq:st18-t00140), conditional on the named hypothesis
    (∀ ν c : ℝ, 1 ≤ c → TrainIVPSolvable ν c → ∃ tr : TrainSol ν c,
      (∀ z, tr.v 0 z = toVec (∑' n : ℤ, velocity (z.1 - n * c, z.2))) ∧
      (∀ z, tr.v 0 z = toVec (perpendicularGradient (trainStream c) z)) ∧
      (∀ q η, tr.ψ 0 (q, η) = -2 * ∑' n : ℤ, Real.exp (-((q - n * c) ^ 2 + η ^ 2) / 4))) :=
  ⟨streamfunction_apply, perpendicularGradient_streamfunction', velocity_apply,
    curl_velocity_apply, zero_circulation, not_hasCompactSupport_velocity,
    fun _ hc => hasSum_trainVelocity hc, fun _ hc => hasSum_trainStream hc,
    fun _ hc => perpendicularGradient_trainStream hc,
    fun _ hc z => ⟨hasDerivAt_trainStream_q hc z, hasDerivAt_trainStream_η hc z⟩,
    trainStream_apply, trainDatum_periodic, trainDatum_neg, fun _ hc => divergence_trainDatum hc,
    fun _ hc => tendsto_trainStream hc, fun _ _ hc h => train_ivp hc h⟩

end UnforcedLeray.B0140
