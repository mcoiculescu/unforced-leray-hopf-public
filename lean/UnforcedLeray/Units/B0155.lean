import UnforcedLeray.Units.B0140

/-!
# B0155 — Overlap variables and the period-one equation (`eq:st18-t00153`, `eq:st18-t00154`)

Blueprint unit **B0155**, label `eq:st18-t00153` (with `eq:st18-t00154`), `paper/main.tex`
lines 2357–2369 (subsection `sec:st18-3582`, "The overlap cylinder and integrable strain");
infrastructure INF23 (chain rule under an affine space-time dilation of periodic fields);
dependency B0140 (the train, `Units/B0140.lean`).

**Statement (tex lines 2357–2369).** At `s_c` introduce the exact variables
`X = q/c`, `Y = η/c`, `T = ν(s - s_c)/c²`, `U(X,Y,T) = c³ v(q,η,s)`, `Ψ = c²ψ`
(`eq:st18-t00153`). The equation becomes, on the period-one cylinder,
`U_T + e_c U·∇U + ∇Π = ΔU`, `∇·U = 0` (`eq:st18-t00154`).
Here `c = ν^{-ρ}`, `0 < ν ≤ 1`, `e_c = (νc²)⁻¹` (tex lines 2042–2044, 2105–2108) and
`s_c = (c² - 1)/ν` (tex line 2199). The rescaled pressure `Π` is not displayed in the text; as
the blueprint notes ask, it is fixed here by the computation: `Π = c⁴ p/ν` (`ovPi`).

**Formalization.**
* The overlap variables are stated for a general period `c` (the manuscript's
  `c = ν^{-ρ}`, `ρ > 1/2`): `coeff ν c = (ν c²)⁻¹` (`e_c`), `age ν c = (c² - 1)/ν` (`s_c`),
  `ovTime ν c s = ν(s - s_c)/c²` (`T`), its inverse `ageOf ν c T = s_c + c²T/ν`,
  `ovPoint c (q,η) = (q/c, η/c)` and its inverse `dil c (X,Y) = (cX, cY)`. At `c = ν⁻²` they
  are the library parameters of unit B0139 (`Train.ec`, `Train.sOv`, `Train.ovT`):
  `coeff_per`, `age_per`, `ovTime_per`.
* `ovU ν c v T Z = c³ v(s_c + c²T/ν, cZ)`, `ovPsi = c²ψ(…)`, `ovPi = (c⁴/ν) p(…)`; the
  defining relations of `eq:st18-t00153` in the manuscript's direction are `ovU_ovTime`,
  `ovPsi_ovTime`, `ovPi_ovTime` (`U(q/c, η/c, T(s)) = c³ v(q,η,s)`, …).
* `periodOneResidual e U Π = U_T + e U·∇U + ∇Π - ΔU`, with the classical partials of the
  train layer (`Train.advection`, `Train.vecLaplacian`, `Train.gradS`).
* **The exact chain rule** `periodOneResidual_ovU`: for `ν ≠ 0`, `c ≠ 0` and **every**
  `v, p`, `periodOneResidual e_c U Π (T, Z) = (c⁵/ν) · momentumResidual ν v p (s, cZ)`.
  Mathlib's `deriv` commutes with affine changes of variable without differentiability
  hypotheses (`deriv_comp_mul_left`, `deriv_comp_const_add`, `deriv_const_mul_field`), so the
  identity holds for all fields and no junk value of `deriv` can make it misleading.
* `IsOverlapSol e T₀ U Π Ψ` is the meaning of `eq:st18-t00154` for the rescaled train: smooth
  on `[T₀,∞) × ℝ²`, period one in `X`, divergence free, the momentum equation for `T > T₀`,
  finite energy on the unit cell, the pressure and stream normalized by decay, `U = ∇^⊥Ψ`,
  centrally odd (the fields of `B0140.IsTrain`, transported; finite energy by the change of
  variables `integrableOn_cell_one_dil`). `IsOverlapSol.mono` restricts to later `T₀`;
  `ovU_initial` is the transported initial value `U(T₀) = c³(P_c v₀)(cZ)`. `isOverlapSol_of_isTrain`: if `(v, p, ψ)` is a train
  (`B0140.IsTrain ν c v p ψ`) with `0 < ν`, `0 < c`, then `(U, Π, Ψ)` is an overlap solution
  with `e = e_c` and `T₀ = ovTime ν c 0 = -(c² - 1)/c²` (the image of `s = 0`), and
  `T₀ ≤ 0` when `1 ≤ c` (`ovTime_zero_nonpos`), so everything holds on `T ≥ 0`
  (momentum on `T > 0`; on `T ≥ 0` if `1 < c`); `isOverlapSol_zero_of_isTrain` is the
  restriction to the manuscript's range `T ≥ 0` for `c ≥ 1`.
* Whole unit: `unit_B0155`; the `c = ν⁻²` family conditional on `B0140.TrainExistence`:
  `overlap_per`.

The existence of the train is the named hypothesis of unit B0140 (`TrainIVPSolvable`,
`TrainExistence`, INF16 T15); this unit adds no hypothesis of its own.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.B0155

open UnforcedLeray.GaussianVortex (Plane perpendicularGradient)
open UnforcedLeray.Train (Vec toVec toVec_smul advection vecLaplacian gradS lapS
  momentumResidual)
open UnforcedLeray.Cyl (partialQ partialEta)

/-! ### 1. The overlap parameters and variables (`eq:st18-t00153`, tex lines 2357–2363) -/

/-- The overlap coefficient `e_c = (ν c²)⁻¹` (tex lines 2057, 2107), for a general period `c`
(the manuscript's `c = ν^{-ρ}`). At `c = ν⁻²` it is `Train.ec` (`coeff_per`). -/
def coeff (ν c : ℝ) : ℝ := (ν * c ^ 2)⁻¹

/-- The overlap age `s_c = (c² - 1)/ν` (tex lines 2054, 2199). At `c = ν⁻²` it is
`Train.sOv` (`age_per`). -/
def age (ν c : ℝ) : ℝ := (c ^ 2 - 1) / ν

/-- The overlap time `T = ν(s - s_c)/c²` (tex lines 2055–2056, 2360). At `c = ν⁻²` it is
`Train.ovT` (`ovTime_per`). -/
def ovTime (ν c s : ℝ) : ℝ := ν * (s - age ν c) / c ^ 2

/-- The original age of the overlap time `T`: `s = s_c + c²T/ν` (inverse of `ovTime`). -/
def ageOf (ν c T : ℝ) : ℝ := age ν c + c ^ 2 / ν * T

/-- The overlap point `(X, Y) = (q/c, η/c)` (tex line 2359). -/
def ovPoint (c : ℝ) (z : Plane) : Plane := (z.1 / c, z.2 / c)

/-- The original point `(q, η) = (cX, cY)` (inverse of `ovPoint`). -/
def dil (c : ℝ) (Z : Plane) : Plane := (c * Z.1, c * Z.2)

/-- **The overlap velocity** `U(X,Y,T) = c³ v(q,η,s)` with `q = cX`, `η = cY`,
`s = s_c + c²T/ν` (tex line 2361; the period-one overlap velocity `c³v` of tex line 2057). -/
def ovU (ν c : ℝ) (v : ℝ → Plane → Vec) (T : ℝ) (Z : Plane) : Vec :=
  c ^ 3 • v (ageOf ν c T) (dil c Z)

/-- **The overlap stream** `Ψ = c²ψ` (tex line 2361), in the overlap variables. -/
def ovPsi (ν c : ℝ) (ψ : ℝ → Plane → ℝ) (T : ℝ) (Z : Plane) : ℝ :=
  c ^ 2 * ψ (ageOf ν c T) (dil c Z)

/-- **The overlap pressure** `Π = c⁴ p/ν` (tex line 2366, where `Π` is not displayed; the
normalization is the one the substitution forces, blueprint unit B0155 notes). -/
def ovPi (ν c : ℝ) (p : ℝ → Plane → ℝ) (T : ℝ) (Z : Plane) : ℝ :=
  c ^ 4 / ν * p (ageOf ν c T) (dil c Z)

/-- **The period-one residual** `U_T + e U·∇U + ∇Π - ΔU` (tex line 2366, `eq:st18-t00154`),
with the classical partials of the train layer (`Lib/Train/Ops.lean`). -/
def periodOneResidual (e : ℝ) (U : ℝ → Plane → Vec) (P : ℝ → Plane → ℝ) (T : ℝ) (Z : Plane) :
    Vec :=
  deriv (fun t => U t Z) T + e • advection (U T) Z + gradS (P T) Z - vecLaplacian (U T) Z

theorem periodOneResidual_eq_zero_iff (e : ℝ) (U : ℝ → Plane → Vec) (P : ℝ → Plane → ℝ)
    (T : ℝ) (Z : Plane) :
    periodOneResidual e U P T Z = 0 ↔
      deriv (fun t => U t Z) T + e • advection (U T) Z + gradS (P T) Z =
        vecLaplacian (U T) Z :=
  sub_eq_zero

/-! #### Parameters -/

theorem coeff_per {ν : ℝ} (hν : ν ≠ 0) : coeff ν (Train.per ν) = Train.ec ν :=
  (Train.ec_eq hν).symm

theorem age_per (ν : ℝ) : age ν (Train.per ν) = Train.sOv ν := rfl

theorem ovTime_per (ν s : ℝ) : ovTime ν (Train.per ν) s = Train.ovT ν s := rfl

theorem coeff_pos {ν c : ℝ} (hν : 0 < ν) (hc : c ≠ 0) : 0 < coeff ν c := by
  unfold coeff; positivity

theorem ovTime_age (ν c : ℝ) : ovTime ν c (age ν c) = 0 := by simp [ovTime]

theorem ageOf_ovTime {ν c : ℝ} (hν : ν ≠ 0) (hc : c ≠ 0) (s : ℝ) :
    ageOf ν c (ovTime ν c s) = s := by
  unfold ageOf ovTime
  field_simp
  ring

theorem ovTime_ageOf {ν c : ℝ} (hν : ν ≠ 0) (hc : c ≠ 0) (T : ℝ) :
    ovTime ν c (ageOf ν c T) = T := by
  unfold ageOf ovTime
  field_simp
  ring

theorem dil_ovPoint {c : ℝ} (hc : c ≠ 0) (z : Plane) : dil c (ovPoint c z) = z := by
  simp [dil, ovPoint, mul_div_cancel₀ _ hc]

theorem ovPoint_dil {c : ℝ} (hc : c ≠ 0) (Z : Plane) : ovPoint c (dil c Z) = Z := by
  simp [dil, ovPoint, mul_div_cancel_left₀ _ hc]

/-- The image of the initial age: `ovTime ν c 0 = -(c² - 1)/c²`. -/
theorem ovTime_zero {ν c : ℝ} (hν : ν ≠ 0) : ovTime ν c 0 = -(c ^ 2 - 1) / c ^ 2 := by
  unfold ovTime age
  rw [zero_sub, mul_neg, mul_div_cancel₀ _ hν]

theorem ovTime_zero_nonpos {ν c : ℝ} (hν : ν ≠ 0) (hc : 1 ≤ c) : ovTime ν c 0 ≤ 0 := by
  rw [ovTime_zero hν]
  apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
  nlinarith

theorem ovTime_zero_neg {ν c : ℝ} (hν : ν ≠ 0) (hc : 1 < c) : ovTime ν c 0 < 0 := by
  rw [ovTime_zero hν]
  apply div_neg_of_neg_of_pos _ (by positivity)
  nlinarith

/-- For `ν > 0` the original age is nonnegative exactly from the image of `s = 0` on. -/
theorem nonneg_ageOf_iff {ν c : ℝ} (hν : 0 < ν) (hc : c ≠ 0) (T : ℝ) :
    0 ≤ ageOf ν c T ↔ ovTime ν c 0 ≤ T := by
  have hc2 : 0 < c ^ 2 / ν := by positivity
  constructor
  · intro h
    have := ovTime_ageOf hν.ne' hc T
    rw [← this]
    unfold ovTime
    gcongr
  · intro h
    have h' : ovTime ν c 0 ≤ ovTime ν c (ageOf ν c T) := by rwa [ovTime_ageOf hν.ne' hc]
    unfold ovTime at h'
    have h'' : ν * (0 - age ν c) ≤ ν * (ageOf ν c T - age ν c) :=
      (div_le_div_iff_of_pos_right (by positivity)).1 h'
    nlinarith

theorem pos_ageOf_iff {ν c : ℝ} (hν : 0 < ν) (hc : c ≠ 0) (T : ℝ) :
    0 < ageOf ν c T ↔ ovTime ν c 0 < T := by
  have hc2 : 0 < c ^ 2 / ν := by positivity
  constructor
  · intro h
    have := ovTime_ageOf hν.ne' hc T
    rw [← this]
    unfold ovTime
    gcongr
  · intro h
    have h' : ovTime ν c 0 < ovTime ν c (ageOf ν c T) := by rwa [ovTime_ageOf hν.ne' hc]
    unfold ovTime at h'
    have h'' : ν * (0 - age ν c) < ν * (ageOf ν c T - age ν c) :=
      (div_lt_div_iff_of_pos_right (by positivity)).1 h'
    nlinarith

/-! #### The defining relations of `eq:st18-t00153` in the manuscript's direction -/

/-- `U(q/c, η/c, ν(s - s_c)/c²) = c³ v(q, η, s)` (tex line 2361). -/
theorem ovU_ovTime {ν c : ℝ} (hν : ν ≠ 0) (hc : c ≠ 0) (v : ℝ → Plane → Vec) (s : ℝ)
    (z : Plane) : ovU ν c v (ovTime ν c s) (ovPoint c z) = c ^ 3 • v s z := by
  rw [ovU, ageOf_ovTime hν hc, dil_ovPoint hc]

/-- `Ψ(q/c, η/c, ν(s - s_c)/c²) = c² ψ(q, η, s)` (tex line 2361). -/
theorem ovPsi_ovTime {ν c : ℝ} (hν : ν ≠ 0) (hc : c ≠ 0) (ψ : ℝ → Plane → ℝ) (s : ℝ)
    (z : Plane) : ovPsi ν c ψ (ovTime ν c s) (ovPoint c z) = c ^ 2 * ψ s z := by
  rw [ovPsi, ageOf_ovTime hν hc, dil_ovPoint hc]

/-- `Π(q/c, η/c, ν(s - s_c)/c²) = c⁴ p(q, η, s)/ν`. -/
theorem ovPi_ovTime {ν c : ℝ} (hν : ν ≠ 0) (hc : c ≠ 0) (p : ℝ → Plane → ℝ) (s : ℝ)
    (z : Plane) : ovPi ν c p (ovTime ν c s) (ovPoint c z) = c ^ 4 / ν * p s z := by
  rw [ovPi, ageOf_ovTime hν hc, dil_ovPoint hc]

/-! ### 2. The chain rule under the dilation (INF23) -/

theorem partialQ_dil (K c : ℝ) (f : Plane → ℝ) :
    partialQ (fun Z => K * f (dil c Z)) = fun Z => K * c * partialQ f (dil c Z) := by
  funext Z
  show deriv (fun x => K * f (c * x, c * Z.2)) Z.1 =
    K * c * deriv (fun x => f (x, c * Z.2)) (c * Z.1)
  rw [deriv_const_mul_field]
  have h := deriv_comp_mul_left c (fun u => f (u, c * Z.2)) Z.1
  simp only [smul_eq_mul] at h
  rw [h]
  ring

theorem partialEta_dil (K c : ℝ) (f : Plane → ℝ) :
    partialEta (fun Z => K * f (dil c Z)) = fun Z => K * c * partialEta f (dil c Z) := by
  funext Z
  show deriv (fun y => K * f (c * Z.1, c * y)) Z.2 =
    K * c * deriv (fun y => f (c * Z.1, y)) (c * Z.2)
  rw [deriv_const_mul_field]
  have h := deriv_comp_mul_left c (fun u => f (c * Z.1, u)) Z.2
  simp only [smul_eq_mul] at h
  rw [h]
  ring

theorem lapS_dil (K c : ℝ) (f : Plane → ℝ) (Z : Plane) :
    lapS (fun Z => K * f (dil c Z)) Z = K * c ^ 2 * lapS f (dil c Z) := by
  unfold lapS
  rw [partialQ_dil, partialQ_dil, partialEta_dil, partialEta_dil]
  ring

theorem ovU_apply (ν c : ℝ) (v : ℝ → Plane → Vec) (T : ℝ) (Z : Plane) (k : Fin 2) :
    ovU ν c v T Z k = c ^ 3 * v (ageOf ν c T) (dil c Z) k := by
  simp [ovU, PiLp.smul_apply]

theorem ovU_comp (ν c : ℝ) (v : ℝ → Plane → Vec) (T : ℝ) (k : Fin 2) :
    (fun w => ovU ν c v T w k) = fun w => c ^ 3 * v (ageOf ν c T) (dil c w) k := by
  funext w
  exact ovU_apply ν c v T w k

/-- `U·∇U = c⁷ (v·∇v)(cZ)`. -/
theorem advection_ovU (ν c : ℝ) (v : ℝ → Plane → Vec) (T : ℝ) (Z : Plane) :
    advection (ovU ν c v T) Z = c ^ 7 • advection (v (ageOf ν c T)) (dil c Z) := by
  unfold Train.advection
  rw [ovU_comp, ovU_comp, partialQ_dil (c ^ 3) c (fun z => v (ageOf ν c T) z 0),
    partialQ_dil (c ^ 3) c (fun z => v (ageOf ν c T) z 1),
    partialEta_dil (c ^ 3) c (fun z => v (ageOf ν c T) z 0),
    partialEta_dil (c ^ 3) c (fun z => v (ageOf ν c T) z 1)]
  apply Train.Vec.ext
  · simp only [Train.toVec_zero, PiLp.smul_apply, smul_eq_mul, ovU_apply]; ring
  · simp only [Train.toVec_one, PiLp.smul_apply, smul_eq_mul, ovU_apply]; ring

/-- `ΔU = c⁵ (Δv)(cZ)`. -/
theorem vecLaplacian_ovU (ν c : ℝ) (v : ℝ → Plane → Vec) (T : ℝ) (Z : Plane) :
    vecLaplacian (ovU ν c v T) Z = c ^ 5 • vecLaplacian (v (ageOf ν c T)) (dil c Z) := by
  unfold vecLaplacian
  rw [ovU_comp, ovU_comp, lapS_dil (c ^ 3) c (fun z => v (ageOf ν c T) z 0),
    lapS_dil (c ^ 3) c (fun z => v (ageOf ν c T) z 1)]
  apply Train.Vec.ext
  · simp only [Train.toVec_zero, PiLp.smul_apply, smul_eq_mul]; ring
  · simp only [Train.toVec_one, PiLp.smul_apply, smul_eq_mul]; ring

/-- `∇Π = (c⁵/ν) (∇p)(cZ)`. -/
theorem gradS_ovPi (ν c : ℝ) (p : ℝ → Plane → ℝ) (T : ℝ) (Z : Plane) :
    gradS (ovPi ν c p T) Z = (c ^ 5 / ν) • gradS (p (ageOf ν c T)) (dil c Z) := by
  have h : ovPi ν c p T = fun w => c ^ 4 / ν * p (ageOf ν c T) (dil c w) := rfl
  unfold gradS
  rw [h, partialQ_dil, partialEta_dil]
  apply Train.Vec.ext
  · simp only [Train.toVec_zero, PiLp.smul_apply, smul_eq_mul]; ring
  · simp only [Train.toVec_one, PiLp.smul_apply, smul_eq_mul]; ring

/-- `U_T = (c⁵/ν) v_s` at `s = s_c + c²T/ν`, `q = cX`, `η = cY` (no differentiability
hypothesis: `deriv` commutes with affine changes of variable). -/
theorem deriv_ovU (ν c : ℝ) (v : ℝ → Plane → Vec) (T : ℝ) (Z : Plane) :
    deriv (fun t => ovU ν c v t Z) T =
      (c ^ 5 / ν) • deriv (fun s => v s (dil c Z)) (ageOf ν c T) := by
  have h1 : (fun t => ovU ν c v t Z) =
      fun t => c ^ 3 • (fun u => v (age ν c + u) (dil c Z)) (c ^ 2 / ν * t) := rfl
  rw [h1, deriv_fun_const_smul_field]
  have h2 := deriv_comp_mul_left (c ^ 2 / ν) (fun u => v (age ν c + u) (dil c Z)) T
  have h3 := deriv_comp_const_add (fun s => v s (dil c Z)) (age ν c) (c ^ 2 / ν * T)
  rw [h2, h3, smul_smul, ageOf]
  congr 1
  ring

/-- **The exact chain rule (`eq:st18-t00153` ⇒ `eq:st18-t00154`, proof outline of the
blueprint).** For `ν ≠ 0`, `c ≠ 0` and all fields `v, p`,
`U_T + e_c U·∇U + ∇Π - ΔU = (c⁵/ν)(v_s + v·∇v - νΔv + ∇p)` at
`(q, η, s) = (cX, cY, s_c + c²T/ν)`. -/
theorem periodOneResidual_ovU {ν c : ℝ} (hν : ν ≠ 0) (hc : c ≠ 0) (v : ℝ → Plane → Vec)
    (p : ℝ → Plane → ℝ) (T : ℝ) (Z : Plane) :
    periodOneResidual (coeff ν c) (ovU ν c v) (ovPi ν c p) T Z =
      (c ^ 5 / ν) • momentumResidual ν v p (ageOf ν c T) (dil c Z) := by
  unfold periodOneResidual momentumResidual
  rw [deriv_ovU, advection_ovU, gradS_ovPi, vecLaplacian_ovU, smul_smul]
  have he : coeff ν c * c ^ 7 = c ^ 5 / ν := by
    unfold coeff; field_simp
  have hl : c ^ 5 • vecLaplacian (v (ageOf ν c T)) (dil c Z) =
      (c ^ 5 / ν) • ν • vecLaplacian (v (ageOf ν c T)) (dil c Z) := by
    rw [smul_smul, div_mul_cancel₀ _ hν]
  rw [he, hl]
  simp only [smul_add, smul_sub]
  abel

/-- Divergence: `∇·U = c⁴ (∇·v)(cZ)`. -/
theorem divergence_ovU (ν c : ℝ) (v : ℝ → Plane → Vec) (T : ℝ) (Z : Plane) :
    Cyl.divergence (ovU ν c v T) Z = c ^ 4 * Cyl.divergence (v (ageOf ν c T)) (dil c Z) := by
  unfold Cyl.divergence
  rw [ovU_comp, ovU_comp, partialQ_dil (c ^ 3) c (fun z => v (ageOf ν c T) z 0),
    partialEta_dil (c ^ 3) c (fun z => v (ageOf ν c T) z 1)]
  ring

/-- Stream: `∇^⊥Ψ = c³ (∇^⊥ψ)(cZ)`. -/
theorem perpendicularGradient_ovPsi (ν c : ℝ) (ψ : ℝ → Plane → ℝ) (T : ℝ) (Z : Plane) :
    perpendicularGradient (ovPsi ν c ψ T) Z =
      c ^ 3 • perpendicularGradient (ψ (ageOf ν c T)) (dil c Z) := by
  have h : ovPsi ν c ψ T = fun w => c ^ 2 * ψ (ageOf ν c T) (dil c w) := rfl
  unfold perpendicularGradient
  rw [h, ← Cyl.partialQ_eq_partialX, ← Cyl.partialEta_eq_partialY, partialQ_dil,
    partialEta_dil, Cyl.partialQ_eq_partialX, Cyl.partialEta_eq_partialY]
  simp only [Prod.smul_mk, smul_eq_mul]
  ext <;> ring

/-! ### 3. The rescaled train solves the period-one equation (`eq:st18-t00154`) -/

/-- **A solution of the period-one equation `eq:st18-t00154` on `[T₀, ∞)`** (tex lines
2364–2369), with the fields of `B0140.IsTrain` transported to the overlap variables:
* `smooth_U`, `smooth_P`: smooth on `[T₀,∞) × ℝ²` (one-sided at `T₀`), so every `deriv` in
  `momentum` is a genuine derivative;
* `periodic_U`, `periodic_P`: fields on the period-one cylinder `(ℝ/ℤ) × ℝ`;
* `solenoidal`: `∇·U = 0`; `momentum`: `U_T + e U·∇U + ∇Π = ΔU` for `T > T₀`;
* `finite_energy`: finite energy on the unit cell `[-1/2, 1/2) × ℝ` of the period-one cylinder;
* `pressure_decay`, `stream_differentiable`, `stream`, `stream_decay`: the pressure fixed by
  decay and the decaying stream `U = ∇^⊥Ψ`;
* `odd`: central oddness. -/
structure IsOverlapSol (e T₀ : ℝ) (U : ℝ → Plane → Vec) (P : ℝ → Plane → ℝ)
    (Ψ : ℝ → Plane → ℝ) : Prop where
  smooth_U : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => U x.1 x.2) (Ici T₀ ×ˢ univ)
  smooth_P : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => P x.1 x.2) (Ici T₀ ×ˢ univ)
  periodic_U : ∀ T, T₀ ≤ T → Cyl.IsPeriodic 1 (U T)
  periodic_P : ∀ T, T₀ ≤ T → Cyl.IsPeriodic 1 (P T)
  solenoidal : ∀ T, T₀ ≤ T → ∀ Z, Cyl.divergence (U T) Z = 0
  momentum : ∀ T, T₀ < T → ∀ Z, periodOneResidual e U P T Z = 0
  finite_energy : ∀ T, T₀ ≤ T → IntegrableOn (fun Z => ‖U T Z‖ ^ 2) (Cyl.cell 1)
  pressure_decay : ∀ T, T₀ ≤ T → Tendsto (P T) (comap (fun Z : Plane => |Z.2|) atTop) (𝓝 0)
  stream_differentiable : ∀ T, T₀ ≤ T → Differentiable ℝ (Ψ T)
  stream : ∀ T, T₀ ≤ T → ∀ Z, U T Z = toVec (perpendicularGradient (Ψ T) Z)
  stream_decay : ∀ T, T₀ ≤ T → Tendsto (Ψ T) (comap (fun Z : Plane => |Z.2|) atTop) (𝓝 0)
  odd : ∀ T, T₀ ≤ T → ∀ Z, U T (-Z) = -U T Z

/-- An overlap solution from `T₀` on is one from any later `T₁` on (used to restrict to the
manuscript's range `T ≥ 0`). -/
theorem IsOverlapSol.mono {e T₀ T₁ : ℝ} {U : ℝ → Plane → Vec} {P Ψ : ℝ → Plane → ℝ}
    (h : IsOverlapSol e T₀ U P Ψ) (hT : T₀ ≤ T₁) : IsOverlapSol e T₁ U P Ψ where
  smooth_U := h.smooth_U.mono (prod_mono (Ici_subset_Ici.2 hT) subset_rfl)
  smooth_P := h.smooth_P.mono (prod_mono (Ici_subset_Ici.2 hT) subset_rfl)
  periodic_U T hT' := h.periodic_U T (hT.trans hT')
  periodic_P T hT' := h.periodic_P T (hT.trans hT')
  solenoidal T hT' := h.solenoidal T (hT.trans hT')
  momentum T hT' := h.momentum T (hT.trans_lt hT')
  finite_energy T hT' := h.finite_energy T (hT.trans hT')
  pressure_decay T hT' := h.pressure_decay T (hT.trans hT')
  stream_differentiable T hT' := h.stream_differentiable T (hT.trans hT')
  stream T hT' := h.stream T (hT.trans hT')
  stream_decay T hT' := h.stream_decay T (hT.trans hT')
  odd T hT' := h.odd T (hT.trans hT')

/-- The affine change of variables `(T, X, Y) ↦ (s_c + c²T/ν, cX, cY)` is smooth. -/
theorem contDiff_ovMap (ν c : ℝ) :
    ContDiff ℝ ∞ (fun x : ℝ × Plane => (ageOf ν c x.1, dil c x.2)) := by
  unfold ageOf dil
  fun_prop

theorem mapsTo_ovMap {ν c : ℝ} (hν : 0 < ν) (hc : c ≠ 0) :
    MapsTo (fun x : ℝ × Plane => (ageOf ν c x.1, dil c x.2)) (Ici (ovTime ν c 0) ×ˢ univ)
      (Ici 0 ×ˢ univ) := by
  intro x hx
  exact ⟨(nonneg_ageOf_iff hν hc x.1).2 hx.1, mem_univ _⟩

theorem tendsto_dil {c : ℝ} (hc : c ≠ 0) :
    Tendsto (dil c) (comap (fun Z : Plane => |Z.2|) atTop)
      (comap (fun Z : Plane => |Z.2|) atTop) := by
  rw [tendsto_comap_iff]
  have h : (fun Z : Plane => |Z.2|) ∘ dil c = fun Z => |c| * |Z.2| := by
    funext Z; simp [dil, abs_mul]
  rw [h]
  exact Tendsto.const_mul_atTop (abs_pos.2 hc) tendsto_comap

theorem dil_eq_smul (c : ℝ) (Z : Plane) : dil c Z = c • Z := rfl

/-- For `c > 0`, the dilation maps the unit cell onto the cell of period `c`:
`cZ ∈ [-c/2, c/2) × ℝ ↔ Z ∈ [-1/2, 1/2) × ℝ`. -/
theorem dil_mem_cell_iff {c : ℝ} (hc : 0 < c) (Z : Plane) :
    dil c Z ∈ Cyl.cell c ↔ Z ∈ Cyl.cell 1 := by
  rw [Cyl.mem_cell, Cyl.mem_cell]
  simp only [dil]
  constructor
  · rintro ⟨h1, h2⟩
    constructor
    · by_contra h
      have : c * Z.1 < c * (-1 / 2) := mul_lt_mul_of_pos_left (not_le.mp h) hc
      linarith
    · by_contra h
      have : c * (1 / 2) ≤ c * Z.1 := mul_le_mul_of_nonneg_left (not_lt.mp h) hc.le
      linarith
  · rintro ⟨h1, h2⟩
    constructor
    · have : c * (-1 / 2) ≤ c * Z.1 := mul_le_mul_of_nonneg_left h1 hc.le
      linarith
    · have : c * Z.1 < c * (1 / 2) := mul_lt_mul_of_pos_left h2 hc
      linarith

/-- Change of variables for integrability: if `g` is integrable on the cell of period `c > 0`,
then `K · g(cZ)` is integrable on the unit cell. -/
theorem integrableOn_cell_one_dil {c : ℝ} (hc : 0 < c) {g : Plane → ℝ}
    (hg : IntegrableOn g (Cyl.cell c)) (K : ℝ) :
    IntegrableOn (fun Z => K * g (dil c Z)) (Cyl.cell 1) := by
  rw [← integrable_indicator_iff (Cyl.measurableSet_cell c)] at hg
  rw [← integrable_indicator_iff (Cyl.measurableSet_cell 1)]
  have h := (hg.comp_smul hc.ne').const_mul K
  refine h.congr (Eventually.of_forall fun Z => ?_)
  by_cases hZ : Z ∈ Cyl.cell 1
  · have hZ' : c • Z ∈ Cyl.cell c := (dil_mem_cell_iff hc Z).2 hZ
    simp only [indicator_of_mem hZ, indicator_of_mem hZ', dil_eq_smul]
  · have hZ' : c • Z ∉ Cyl.cell c := fun h' => hZ ((dil_mem_cell_iff hc Z).1 h')
    simp only [indicator_of_notMem hZ, indicator_of_notMem hZ', mul_zero]

/-- The initial value in overlap variables: `U(T₀) = c³ (P_c v₀)(cZ)` at the image
`T₀ = ovTime ν c 0` of `s = 0`. -/
theorem ovU_initial {ν c : ℝ} (hν : ν ≠ 0) (hc : c ≠ 0) {v : ℝ → Plane → Vec}
    {p ψ : ℝ → Plane → ℝ} (htr : B0140.IsTrain ν c v p ψ) (Z : Plane) :
    ovU ν c v (ovTime ν c 0) Z = c ^ 3 • B0140.trainDatum c (dil c Z) := by
  rw [ovU, ageOf_ovTime hν hc, htr.initial]

/-- **The rescaled train solves the period-one equation (`eq:st18-t00154`).** If `(v, p, ψ)`
is the train of unit B0140 (`IsTrain ν c v p ψ`), `0 < ν`, `0 < c`, then
`(U, Π, Ψ) = (c³v, c⁴p/ν, c²ψ)` in the overlap variables solves
`U_T + e_c U·∇U + ∇Π = ΔU`, `∇·U = 0` on the period-one cylinder for
`T > T₀ = ovTime ν c 0` (the image of `s = 0`), with all transported properties. -/
theorem isOverlapSol_of_isTrain {ν c : ℝ} (hν : 0 < ν) (hc : 0 < c) {v : ℝ → Plane → Vec}
    {p ψ : ℝ → Plane → ℝ} (htr : B0140.IsTrain ν c v p ψ) :
    IsOverlapSol (coeff ν c) (ovTime ν c 0) (ovU ν c v) (ovPi ν c p) (ovPsi ν c ψ) := by
  have hc0 : c ≠ 0 := hc.ne'
  have hν0 : ν ≠ 0 := hν.ne'
  have hage : ∀ T, ovTime ν c 0 ≤ T → 0 ≤ ageOf ν c T := fun T hT =>
    (nonneg_ageOf_iff hν hc0 T).2 hT
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := (htr.smooth_v.comp (contDiff_ovMap ν c).contDiffOn (mapsTo_ovMap hν hc0)).const_smul
      (c ^ 3)
    exact this
  · have := (htr.smooth_p.comp (contDiff_ovMap ν c).contDiffOn (mapsTo_ovMap hν hc0)).const_smul
      (c ^ 4 / ν)
    exact this
  · intro T hT Z
    have h := htr.periodic_v (ageOf ν c T) (hage T hT) (dil c Z)
    simp only [ovU, dil] at h ⊢
    rw [mul_add, mul_one, h]
  · intro T hT Z
    have h := htr.periodic_p (ageOf ν c T) (hage T hT) (dil c Z)
    simp only [ovPi, dil] at h ⊢
    rw [mul_add, mul_one, h]
  · intro T hT Z
    rw [divergence_ovU, htr.solenoidal _ (hage T hT), mul_zero]
  · intro T hT Z
    rw [periodOneResidual_ovU hν0 hc0,
      htr.momentum _ ((pos_ageOf_iff hν hc0 T).2 hT), smul_zero]
  · intro T hT
    have h := integrableOn_cell_one_dil hc (htr.finite_energy _ (hage T hT)) ((c ^ 3) ^ 2)
    have he : (fun Z => ‖ovU ν c v T Z‖ ^ 2) =
        fun Z => (c ^ 3) ^ 2 * ‖v (ageOf ν c T) (dil c Z)‖ ^ 2 := by
      funext Z
      rw [ovU, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    rw [he]
    exact h
  · intro T hT
    have h := ((htr.pressure_decay _ (hage T hT)).comp (tendsto_dil hc0)).const_mul (c ^ 4 / ν)
    rw [mul_zero] at h
    exact h
  · intro T hT
    have h := htr.stream_differentiable _ (hage T hT)
    have hd : Differentiable ℝ (dil c) := by unfold dil; fun_prop
    exact (h.comp hd).const_mul (c ^ 2)
  · intro T hT Z
    rw [perpendicularGradient_ovPsi, toVec_smul, ← htr.stream _ (hage T hT)]
    rfl
  · intro T hT
    have h := ((htr.stream_decay _ (hage T hT)).comp (tendsto_dil hc0)).const_mul (c ^ 2)
    rw [mul_zero] at h
    exact h
  · intro T hT Z
    have h := htr.odd _ (hage T hT) (dil c Z)
    have hn : dil c (-Z) = -dil c Z := by simp [dil]
    simp only [ovU, hn, h, smul_neg]

/-- **The period-one equation on the manuscript's range `T ≥ 0`** (tex lines 2357–2369): for
`c ≥ 1` (the manuscript's `c = ν^{-ρ}`, `0 < ν ≤ 1`) the image `T₀` of `s = 0` is `≤ 0`, so
the rescaled train is an overlap solution from `T = 0` (the age `s_c`) on. -/
theorem isOverlapSol_zero_of_isTrain {ν c : ℝ} (hν : 0 < ν) (hc : 1 ≤ c)
    {v : ℝ → Plane → Vec} {p ψ : ℝ → Plane → ℝ} (htr : B0140.IsTrain ν c v p ψ) :
    IsOverlapSol (coeff ν c) 0 (ovU ν c v) (ovPi ν c p) (ovPsi ν c ψ) :=
  (isOverlapSol_of_isTrain hν (lt_of_lt_of_le one_pos hc) htr).mono
    (ovTime_zero_nonpos hν.ne' hc)

/-! ### 4. The whole unit -/

/-- **Unit B0155** (tex lines 2357–2369). For every `0 < ν` and period `0 < c` (the
manuscript's `c = ν^{-ρ}`, `0 < ν ≤ 1`): the overlap variables `X = q/c`, `Y = η/c`,
`T = ν(s - s_c)/c²` invert the dilation; `U = c³v`, `Ψ = c²ψ`, `Π = c⁴p/ν` in these
variables; the chain rule turns the train residual into `(ν/c⁵)⁻¹` times the period-one
residual for all fields; and every train (unit B0140) gives a solution of the period-one
equation `U_T + e_c U·∇U + ∇Π = ΔU`, `∇·U = 0` from `T₀ = ovTime ν c 0` on, with
`T₀ ≤ 0` when `1 ≤ c`, hence on the manuscript's range `T ≥ 0` when `c ≥ 1`. -/
theorem unit_B0155 {ν c : ℝ} (hν : 0 < ν) (hc : 0 < c) :
    -- the exact variables `eq:st18-t00153`
    (∀ s, ageOf ν c (ovTime ν c s) = s) ∧ (∀ T, ovTime ν c (ageOf ν c T) = T) ∧
    ovTime ν c (age ν c) = 0 ∧
    (∀ z, dil c (ovPoint c z) = z) ∧ (∀ Z, ovPoint c (dil c Z) = Z) ∧
    (∀ (v : ℝ → Plane → Vec) s z, ovU ν c v (ovTime ν c s) (ovPoint c z) = c ^ 3 • v s z) ∧
    (∀ (ψ : ℝ → Plane → ℝ) s z, ovPsi ν c ψ (ovTime ν c s) (ovPoint c z) = c ^ 2 * ψ s z) ∧
    (∀ (p : ℝ → Plane → ℝ) s z, ovPi ν c p (ovTime ν c s) (ovPoint c z) = c ^ 4 / ν * p s z) ∧
    -- the substitution (exact for all fields)
    (∀ (v : ℝ → Plane → Vec) (p : ℝ → Plane → ℝ) T Z,
      periodOneResidual (coeff ν c) (ovU ν c v) (ovPi ν c p) T Z =
        (c ^ 5 / ν) • momentumResidual ν v p (ageOf ν c T) (dil c Z)) ∧
    -- the period-one equation `eq:st18-t00154` for the train
    (∀ (v : ℝ → Plane → Vec) (p ψ : ℝ → Plane → ℝ), B0140.IsTrain ν c v p ψ →
      IsOverlapSol (coeff ν c) (ovTime ν c 0) (ovU ν c v) (ovPi ν c p) (ovPsi ν c ψ)) ∧
    (1 ≤ c → ovTime ν c 0 ≤ 0) ∧ (1 < c → ovTime ν c 0 < 0) ∧
    -- on the manuscript's range `T ≥ 0` (from the age `s_c` on), for `c ≥ 1`
    (1 ≤ c → ∀ (v : ℝ → Plane → Vec) (p ψ : ℝ → Plane → ℝ), B0140.IsTrain ν c v p ψ →
      IsOverlapSol (coeff ν c) 0 (ovU ν c v) (ovPi ν c p) (ovPsi ν c ψ)) :=
  ⟨ageOf_ovTime hν.ne' hc.ne', ovTime_ageOf hν.ne' hc.ne', ovTime_age ν c,
    dil_ovPoint hc.ne', ovPoint_dil hc.ne', ovU_ovTime hν.ne' hc.ne',
    ovPsi_ovTime hν.ne' hc.ne', ovPi_ovTime hν.ne' hc.ne',
    periodOneResidual_ovU hν.ne' hc.ne', fun _ _ _ h => isOverlapSol_of_isTrain hν hc h,
    ovTime_zero_nonpos hν.ne', ovTime_zero_neg hν.ne',
    fun h1 _ _ _ h => isOverlapSol_zero_of_isTrain hν h1 h⟩

/-- **The `c = ν⁻²` family (tex line 13718, bypass B3), conditional on the named hypothesis
`B0140.TrainExistence` (INF16 T15).** For all small `ν` there is a train with period
`c = ν⁻²` whose overlap fields solve the period-one equation with `e_c = Train.ec ν = ν³` on
`T > ovTime ν c 0`, where `ovTime ν c 0 ≤ 0`, at overlap time `Train.ovT`. -/
theorem overlap_per (h : B0140.TrainExistence) :
    ∃ ν₀ > 0, ∀ ν ∈ Ioc 0 ν₀, ∃ tr : B0140.TrainSol ν (Train.per ν),
      IsOverlapSol (Train.ec ν) (Train.ovT ν 0) (ovU ν (Train.per ν) tr.v)
        (ovPi ν (Train.per ν) tr.p) (ovPsi ν (Train.per ν) tr.ψ) ∧
      Train.ovT ν 0 ≤ 0 := by
  obtain ⟨ν₀, hν₀, hT⟩ := h
  refine ⟨min ν₀ 1, lt_min hν₀ one_pos, fun ν hν => ?_⟩
  have hν1 : ν ≤ 1 := hν.2.trans (min_le_right _ _)
  have h1 : 1 ≤ Train.per ν := Train.one_le_per hν.1 hν1
  obtain ⟨tr⟩ := hT ν ⟨hν.1, hν.2.trans (min_le_left _ _)⟩
  refine ⟨tr, ?_, ?_⟩
  · have := isOverlapSol_of_isTrain hν.1 (Train.per_pos hν.1) tr.isTrain
    rwa [coeff_per hν.1.ne', ovTime_per] at this
  · rw [← ovTime_per]
    exact ovTime_zero_nonpos hν.1.ne' h1

end UnforcedLeray.B0155
