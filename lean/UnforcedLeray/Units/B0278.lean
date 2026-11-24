import UnforcedLeray.Units.B0277
import UnforcedLeray.Lib.Train.Params

/-!
# B0278 `mixed-background:C.6`: the late strain integral `A_late`

Unit B0278 of `paper/main.tex`, label `mixed-background:C.6`, tex lines 4819–4825
(§ "mixed background", source range 4092–5062; the late age interval starts at tex line 4734,
`H = Σ/ν < S`). The train strain estimate it quotes is `eq:st18-t00164` (tex lines 2469–2478,
blueprint unit B0165, §`sec:st18-3582`, the train section `sec:train`, tex lines 2038–3243),
with `e_c = (νc²)⁻¹` (tex lines 2057, 2107). Consumers: B0667 (`mixed-background:C.7`, the
Gronwall bound `sup ‖z_m‖_{H¹} ≤ e^{A_late}(M_e + ∫_H^S ‖g_m‖_{H¹})`) and B0675 (tex lines
4987–5009: choose `Σ` first to make the late exponential coefficient small, then `ν` small).

**Statement (tex lines 4819–4825).**
`A_late := C ∫_H^S (‖Dv(s)‖_∞ + ‖D²v(s)‖_∞) ds ≤ C/(ν(1+Σ)) + C/(νc²)`, `H = Σ/ν`.
It is `eq:st18-t00164` at `k = 1`, `σ₀ = Σ` (`s₀ = Σ/ν = H`, valid for `1 + Σ ≤ c²`), truncated
at `S` and multiplied by the energy constant `C` of the pairing at tex lines 4810–4815. The
constant on the right is independent of `ν`, `c`, `Σ` and `S`; `C/(νc²) = C ν^{2ρ-1}` is bounded
for `c = ν^{-ρ}`, `ρ > 1/2`, `ν ≤ 1`.

**Lean conventions.** Spatial fields are maps `E → F` between real normed spaces (for the
train, the periodic lift `Plane → Plane` of the cylinder field), as in unit B0277, whose
`‖D^j f‖_∞ = supNormD j f := ⨆ x, ‖iteratedFDeriv ℝ j f x‖ₑ ∈ [0, ∞]` is reused. The strain
integral is the lower Lebesgue integral `∫⁻` in `[0, ∞]` over `Ioc H S`, so no junk value of a
Bochner integral of a non-integrable function enters; `Alate` is the `[0, ∞]` value and
`AlateReal` its real value, which is the true value because `Alate_ne_top` proves finiteness
(no junk `toReal ∞ = 0`). The train strain estimate `eq:st18-t00164` is the explicit hypothesis
`TrainStrainEstimate k C_k ν c σ₀ v` at one order and one starting age (the weakest form the
unit uses), and `TrainStrainFamily ρ v` is the manuscript's form: one constant for all small
`ν` and every `σ₀ ≥ 0` with `1 + σ₀ ≤ c²`, at `c = ν^{-ρ}`. The cutoff `S` is arbitrary (for
`S ≤ H` the integral is `0`); the manuscript has `S > H`.

**What is proved here.**
* `strainIntegral_le`, `Alate_le`: the bound (`mixed-background:C.6`) from the hypothesis
  `TrainStrainEstimate 1 C₁ ν c Σ v`, with right-hand constant `C_A C₁`.
* `Alate_ne_top`, `ofReal_AlateReal`, `AlateReal_le`, `exp_AlateReal_le`: the real form used
  by the Gronwall step B0667.
* `exists_Alate_bound`: one constant `C ≥ 0`, depending only on `C_A` and `C₁`, serves every
  `ν`, `c`, `Σ`, `S` and every field satisfying the strain estimate with constant `C₁`.
* `Alate_family`: the unit in the manuscript's regime, from `TrainStrainFamily ρ v`; and
  `Alate_family_fixedSigma`: for each fixed `Σ ≥ 0` the side condition `1 + Σ ≤ c²` holds for
  small `ν`, the constant `C` being chosen before `Σ`, and `C/(νc²) = C ν^{2ρ-1} ≤ C`.
* `ec_rho_eq`, `ec_rho_le_one`, `one_add_le_sq_of_small`, `ec_per`: the elementary facts about
  `e_c = (νc²)⁻¹` at `c = ν^{-ρ}` and at the Lean train period `c = per ν = ν^{-2}` (bypass B3).

**Missing.** The train strain estimate `eq:st18-t00164` itself (unit B0165, INF16 T10
`integratedStrain`, built on T8 `preOverlap` and T9 `postOverlap_strain`) is not formalized; it
enters as the hypothesis `TrainStrainEstimate` / `TrainStrainFamily`.
-/

set_option autoImplicit false

noncomputable section

open Real Finset MeasureTheory Set
open scoped ENNReal

namespace UnforcedLeray.B0278

open UnforcedLeray.B0277 (supNormD)

section General

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ### Definitions -/

/-- The strain integral `∫_H^S (‖Dv(s)‖_∞ + ‖D²v(s)‖_∞) ds` of tex line 4821, as a lower
Lebesgue integral in `[0, ∞]` over `Ioc H S` (`‖D^j v(s)‖_∞ = supNormD j (v s)`, unit B0277). -/
def strainIntegral (v : ℝ → E → F) (H S : ℝ) : ℝ≥0∞ :=
  ∫⁻ s in Ioc H S, (supNormD 1 (v s) + supNormD 2 (v s))

/-- **The late strain integral** `A_late := C ∫_H^S (‖Dv(s)‖_∞ + ‖D²v(s)‖_∞) ds`, `H = Σ/ν`
(`mixed-background:C.6`, tex lines 4820–4821), valued in `[0, ∞]`. Here `C = CA ≥ 0` is the
constant of the pairing estimate of tex lines 4810–4815 (the theorems assume `0 ≤ CA`). -/
def Alate (CA ν Sig S : ℝ) (v : ℝ → E → F) : ℝ≥0∞ :=
  ENNReal.ofReal CA * strainIntegral v (Sig / ν) S

/-- The real value of `A_late`, as it enters the exponential `e^{A_late}` of
`mixed-background:C.7` (tex line 4829). It is the true value under the hypotheses of
`ofReal_AlateReal` (finiteness from `Alate_ne_top`). -/
def AlateReal (CA ν Sig S : ℝ) (v : ℝ → E → F) : ℝ :=
  CA * (strainIntegral v (Sig / ν) S).toReal

/-- **The train strain estimate `eq:st18-t00164`** (tex lines 2469–2478, unit B0165, train
section `sec:train`), at one order `k` and one starting age `s₀ = σ₀/ν`:
`∫_{s₀}^∞ ∑_{j=1}^{k+1} ‖D^j v(s)‖_∞ ds ≤ C_k/(ν(1+σ₀)) + C_k e_c`, `e_c = (νc²)⁻¹`
(tex line 2107). The manuscript asserts it for every `σ₀ ≥ 0` with `1 + σ₀ ≤ c²`, with `C_k`
independent of `ν`, `c` and `σ₀` (see `TrainStrainFamily`); this single instance is the weakest
form B0278 uses (`k = 1`, `σ₀ = Σ`). Not yet formalized (INF16 T10 `integratedStrain`). -/
def TrainStrainEstimate (k : ℕ) (Ck ν c σ₀ : ℝ) (v : ℝ → E → F) : Prop :=
  ∫⁻ s in Ioi (σ₀ / ν), ∑ j ∈ Icc 1 (k + 1), supNormD j (v s) ≤
    ENNReal.ofReal (Ck / (ν * (1 + σ₀)) + Ck / (ν * c ^ 2))

/-- **The train strain estimate `eq:st18-t00164` at `k = 1`, as the manuscript states it**
(tex lines 2469–2478, unit B0165), for a family of trains `v ν` at `c = ν^{-ρ}`
(tex line 2044): there are `ν₀ > 0` and one constant `C₁` such that for all `0 < ν ≤ ν₀` and
all `σ₀ ≥ 0` with `1 + σ₀ ≤ c²`, `TrainStrainEstimate 1 C₁ ν c σ₀ (v ν)`. -/
def TrainStrainFamily (ρ : ℝ) (v : ℝ → ℝ → E → F) : Prop :=
  ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∃ C₁ : ℝ, ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ → ∀ σ₀ : ℝ, 0 ≤ σ₀ →
    1 + σ₀ ≤ (ν ^ (-ρ)) ^ 2 → TrainStrainEstimate 1 C₁ ν (ν ^ (-ρ)) σ₀ (v ν)

/-! ### The bound `mixed-background:C.6` -/

/-- At `k = 1` the sum `∑_{j=1}^{k+1}` of `eq:st18-t00164` is `‖Dv‖_∞ + ‖D²v‖_∞`. -/
theorem sum_Icc_one_two (f : ℕ → ℝ≥0∞) : ∑ j ∈ Icc 1 (1 + 1), f j = f 1 + f 2 := by
  have h : Finset.Icc 1 (1 + 1) = ({1, 2} : Finset ℕ) := by decide
  rw [h, Finset.sum_pair (by norm_num)]

/-- The truncated strain integral is at most the integral over `(H, ∞)`. -/
theorem strainIntegral_le_Ioi (v : ℝ → E → F) (H S : ℝ) :
    strainIntegral v H S ≤ ∫⁻ s in Ioi H, (supNormD 1 (v s) + supNormD 2 (v s)) :=
  lintegral_mono_set Ioc_subset_Ioi_self

/-- **The strain integral bound** (tex lines 4819–4825, without the factor `C`): the train
strain estimate at `k = 1`, `σ₀ = Σ` gives
`∫_H^S (‖Dv‖_∞ + ‖D²v‖_∞) ds ≤ C₁/(ν(1+Σ)) + C₁/(νc²)` for `H = Σ/ν` and every `S`. -/
theorem strainIntegral_le {C₁ ν c Sig S : ℝ} {v : ℝ → E → F}
    (hT : TrainStrainEstimate 1 C₁ ν c Sig v) :
    strainIntegral v (Sig / ν) S ≤
      ENNReal.ofReal (C₁ / (ν * (1 + Sig)) + C₁ / (ν * c ^ 2)) := by
  refine (strainIntegral_le_Ioi v _ S).trans (le_of_eq_of_le ?_ hT)
  simp only [sum_Icc_one_two]

/-- **`mixed-background:C.6` (tex lines 4819–4825).** For `C_A ≥ 0`, if the train strain
estimate `eq:st18-t00164` holds at `k = 1`, `σ₀ = Σ` with constant `C₁`, then
`A_late = C_A ∫_H^S (‖Dv‖_∞ + ‖D²v‖_∞) ds ≤ C/(ν(1+Σ)) + C/(νc²)` with `C = C_A C₁`. -/
theorem Alate_le {CA C₁ ν c Sig S : ℝ} {v : ℝ → E → F} (hCA : 0 ≤ CA)
    (hT : TrainStrainEstimate 1 C₁ ν c Sig v) :
    Alate CA ν Sig S v ≤
      ENNReal.ofReal (CA * C₁ / (ν * (1 + Sig)) + CA * C₁ / (ν * c ^ 2)) := by
  unfold Alate
  calc ENNReal.ofReal CA * strainIntegral v (Sig / ν) S
      ≤ ENNReal.ofReal CA * ENNReal.ofReal (C₁ / (ν * (1 + Sig)) + C₁ / (ν * c ^ 2)) := by
        gcongr; exact strainIntegral_le hT
    _ = ENNReal.ofReal (CA * (C₁ / (ν * (1 + Sig)) + C₁ / (ν * c ^ 2))) :=
        (ENNReal.ofReal_mul hCA).symm
    _ = ENNReal.ofReal (CA * C₁ / (ν * (1 + Sig)) + CA * C₁ / (ν * c ^ 2)) := by
        congr 1; ring

/-! ### The real form of `A_late` -/

/-- Under the train strain estimate the strain integral is finite. -/
theorem strainIntegral_ne_top {C₁ ν c Sig S : ℝ} {v : ℝ → E → F}
    (hT : TrainStrainEstimate 1 C₁ ν c Sig v) : strainIntegral v (Sig / ν) S ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (strainIntegral_le hT)

/-- `A_late` is finite. -/
theorem Alate_ne_top {CA C₁ ν c Sig S : ℝ} {v : ℝ → E → F}
    (hT : TrainStrainEstimate 1 C₁ ν c Sig v) : Alate CA ν Sig S v ≠ ⊤ :=
  ENNReal.mul_ne_top ENNReal.ofReal_ne_top (strainIntegral_ne_top hT)

/-- The real value `AlateReal` is the true value of `A_late` (no junk `toReal ∞`). -/
theorem ofReal_AlateReal {CA C₁ ν c Sig S : ℝ} {v : ℝ → E → F} (hCA : 0 ≤ CA)
    (hT : TrainStrainEstimate 1 C₁ ν c Sig v) :
    ENNReal.ofReal (AlateReal CA ν Sig S v) = Alate CA ν Sig S v := by
  unfold AlateReal Alate
  rw [ENNReal.ofReal_mul hCA, ENNReal.ofReal_toReal (strainIntegral_ne_top hT)]

theorem AlateReal_nonneg {CA ν Sig S : ℝ} {v : ℝ → E → F} (hCA : 0 ≤ CA) :
    0 ≤ AlateReal CA ν Sig S v :=
  mul_nonneg hCA ENNReal.toReal_nonneg

/-- A strain estimate with constant `C_k` also holds with `max C_k 0` (for `ν > 0`,
`1 + σ₀ > 0`), so the constant may be taken nonnegative. -/
theorem TrainStrainEstimate.max_zero {k : ℕ} {Ck ν c σ₀ : ℝ} {v : ℝ → E → F} (hν : 0 < ν)
    (hσ : 0 < 1 + σ₀) (hT : TrainStrainEstimate k Ck ν c σ₀ v) :
    TrainStrainEstimate k (max Ck 0) ν c σ₀ v := by
  unfold TrainStrainEstimate at hT ⊢
  refine hT.trans (ENNReal.ofReal_le_ofReal ?_)
  have h1 : 0 ≤ ν * (1 + σ₀) := by positivity
  have h2 : 0 ≤ ν * c ^ 2 := by positivity
  have hm := le_max_left Ck 0
  gcongr

/-- **`mixed-background:C.6`, real form** (as used in `e^{A_late}`, tex line 4829): for
`C_A, C₁ ≥ 0`, `ν > 0`, `Σ ≥ 0`, `A_late ≤ C_A C₁/(ν(1+Σ)) + C_A C₁/(νc²)` in `ℝ`. -/
theorem AlateReal_le {CA C₁ ν c Sig S : ℝ} {v : ℝ → E → F} (hCA : 0 ≤ CA) (hC₁ : 0 ≤ C₁)
    (hν : 0 < ν) (hSig : 0 ≤ Sig) (hT : TrainStrainEstimate 1 C₁ ν c Sig v) :
    AlateReal CA ν Sig S v ≤ CA * C₁ / (ν * (1 + Sig)) + CA * C₁ / (ν * c ^ 2) := by
  have h := Alate_le (S := S) hCA hT
  rw [← ofReal_AlateReal hCA hT] at h
  have h0 : 0 ≤ CA * C₁ / (ν * (1 + Sig)) + CA * C₁ / (ν * c ^ 2) := by
    have : 0 ≤ CA * C₁ := mul_nonneg hCA hC₁
    positivity
  exact (ENNReal.ofReal_le_ofReal_iff h0).1 h

/-- The exponential factor of `mixed-background:C.7`: `e^{A_late} ≤ e^{C/(ν(1+Σ)) + C/(νc²)}`. -/
theorem exp_AlateReal_le {CA C₁ ν c Sig S : ℝ} {v : ℝ → E → F} (hCA : 0 ≤ CA) (hC₁ : 0 ≤ C₁)
    (hν : 0 < ν) (hSig : 0 ≤ Sig) (hT : TrainStrainEstimate 1 C₁ ν c Sig v) :
    Real.exp (AlateReal CA ν Sig S v) ≤
      Real.exp (CA * C₁ / (ν * (1 + Sig)) + CA * C₁ / (ν * c ^ 2)) :=
  Real.exp_le_exp.2 (AlateReal_le hCA hC₁ hν hSig hT)

/-- **Uniformity of the constant in `mixed-background:C.6`.** Given the pairing constant
`C_A ≥ 0` and the strain constant `C₁`, one `C ≥ 0` (namely `C_A max(C₁, 0)`) serves every
`ν > 0`, `c`, `Σ ≥ 0`, `S` and every field `v` satisfying the train strain estimate at
`k = 1`, `σ₀ = Σ` with constant `C₁`: `A_late` is finite and
`A_late ≤ C/(ν(1+Σ)) + C/(νc²)`. -/
theorem exists_Alate_bound (CA C₁ : ℝ) (hCA : 0 ≤ CA) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ν c Sig S : ℝ) (v : ℝ → E → F), 0 < ν → 0 ≤ Sig →
      TrainStrainEstimate 1 C₁ ν c Sig v →
      Alate CA ν Sig S v ≠ ⊤ ∧
      Alate CA ν Sig S v ≤ ENNReal.ofReal (C / (ν * (1 + Sig)) + C / (ν * c ^ 2)) ∧
      AlateReal CA ν Sig S v ≤ C / (ν * (1 + Sig)) + C / (ν * c ^ 2) := by
  refine ⟨CA * max C₁ 0, mul_nonneg hCA (le_max_right _ _), ?_⟩
  intro ν c Sig S v hν hSig hT
  have hT' := hT.max_zero hν (by linarith)
  exact ⟨Alate_ne_top hT, Alate_le hCA hT',
    AlateReal_le hCA (le_max_right _ _) hν hSig hT'⟩

end General

/-! ### `e_c` at `c = ν^{-ρ}` and the regime `1 + Σ ≤ c²` -/

/-- `c² = ν^{-2ρ}` for `c = ν^{-ρ}`. -/
theorem rpow_neg_sq {ν ρ : ℝ} (hν : 0 < ν) : (ν ^ (-ρ)) ^ 2 = ν ^ (-(2 * ρ)) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hν.le]
  congr 1; push_cast; ring

/-- `C/(νc²) = C ν^{2ρ-1}` for `c = ν^{-ρ}` (blueprint note of B0278). -/
theorem ec_rho_eq {ν ρ : ℝ} (C : ℝ) (hν : 0 < ν) :
    C / (ν * (ν ^ (-ρ)) ^ 2) = C * ν ^ (2 * ρ - 1) := by
  rw [rpow_neg_sq hν]
  have h : ν * ν ^ (-(2 * ρ)) = ν ^ (1 - 2 * ρ) := by
    rw [Real.rpow_sub hν, Real.rpow_one, Real.rpow_neg hν.le, div_eq_mul_inv]
  rw [h, div_eq_mul_inv, ← Real.rpow_neg hν.le]
  congr 2; ring

/-- `e_c = (νc²)⁻¹ = ν^{2ρ-1} ≤ 1` for `c = ν^{-ρ}`, `ρ > 1/2`, `0 < ν ≤ 1`; so
`C/(νc²) ≤ C` is bounded (blueprint note of B0278; tex lines 4987–4989). -/
theorem ec_rho_le_one {ν ρ : ℝ} (hν0 : 0 < ν) (hν1 : ν ≤ 1) (hρ : 1 / 2 < ρ) :
    1 / (ν * (ν ^ (-ρ)) ^ 2) ≤ 1 := by
  rw [ec_rho_eq 1 hν0, one_mul]
  exact Real.rpow_le_one hν0.le hν1 (by linarith)

/-- **For fixed `Σ ≥ 0` the side condition `1 + Σ ≤ c²` of `eq:st18-t00164` holds for small
`ν`** (`c = ν^{-ρ}`, `ρ > 0`): there is `0 < ν₁ ≤ 1` with `1 + Σ ≤ (ν^{-ρ})²` for `0 < ν ≤ ν₁`. -/
theorem one_add_le_sq_of_small {ρ Sig : ℝ} (hρ : 0 < ρ) (hSig : 0 ≤ Sig) :
    ∃ ν₁ : ℝ, 0 < ν₁ ∧ ν₁ ≤ 1 ∧ ∀ ν : ℝ, 0 < ν → ν ≤ ν₁ → 1 + Sig ≤ (ν ^ (-ρ)) ^ 2 := by
  have h1 : 0 < 1 + Sig := by linarith
  have h1' : 1 ≤ 1 + Sig := by linarith
  refine ⟨(1 + Sig) ^ (-(1 / (2 * ρ))), Real.rpow_pos_of_pos h1 _,
    Real.rpow_le_one_of_one_le_of_nonpos h1' (by
      have : 0 < 1 / (2 * ρ) := by positivity
      linarith), ?_⟩
  intro ν hν hν1
  rw [rpow_neg_sq hν]
  have hmono : ((1 + Sig) ^ (-(1 / (2 * ρ)))) ^ (-(2 * ρ)) ≤ ν ^ (-(2 * ρ)) :=
    Real.rpow_le_rpow_of_nonpos hν hν1 (by linarith)
  have hid : ((1 + Sig) ^ (-(1 / (2 * ρ)))) ^ (-(2 * ρ)) = 1 + Sig := by
    rw [← Real.rpow_mul h1.le]
    have : -(1 / (2 * ρ)) * -(2 * ρ) = 1 := by field_simp
    rw [this, Real.rpow_one]
  rw [hid] at hmono
  exact hmono

/-- At the Lean train period `c = per ν = ν^{-2}` (scoping bypass B3, D8),
`C/(νc²) = C e_c` with `e_c = Train.ec ν = ν³`. -/
theorem ec_per {ν : ℝ} (C : ℝ) (hν : 0 < ν) :
    C / (ν * UnforcedLeray.Train.per ν ^ 2) = C * UnforcedLeray.Train.ec ν := by
  rw [UnforcedLeray.Train.ec_eq hν.ne', div_eq_mul_inv]

/-! ### The unit in the manuscript's regime -/

section Family

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **`mixed-background:C.6` in the manuscript's form** (tex lines 4819–4825 with
`eq:st18-t00164`): for a family of trains `v ν` at `c = ν^{-ρ}` satisfying the train strain
estimate `TrainStrainFamily ρ v` and a pairing constant `C_A ≥ 0`, there are `ν₀ > 0` and one
constant `C ≥ 0` such that for every `0 < ν ≤ ν₀`, every `Σ ≥ 0` with `1 + Σ ≤ c²` and every
cutoff `S`, `A_late` is finite and `A_late ≤ C/(ν(1+Σ)) + C/(νc²)`. The constant is independent
of `ν`, `c`, `Σ` and `S`. -/
theorem Alate_family {ρ CA : ℝ} {v : ℝ → ℝ → E → F} (hCA : 0 ≤ CA)
    (hT : TrainStrainFamily ρ v) :
    ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ → ∀ Sig : ℝ, 0 ≤ Sig →
      1 + Sig ≤ (ν ^ (-ρ)) ^ 2 → ∀ S : ℝ,
      Alate CA ν Sig S (v ν) ≠ ⊤ ∧
      Alate CA ν Sig S (v ν) ≤
        ENNReal.ofReal (C / (ν * (1 + Sig)) + C / (ν * (ν ^ (-ρ)) ^ 2)) ∧
      AlateReal CA ν Sig S (v ν) ≤ C / (ν * (1 + Sig)) + C / (ν * (ν ^ (-ρ)) ^ 2) := by
  obtain ⟨ν₀, hν₀, C₁, hC₁⟩ := hT
  obtain ⟨C, hC0, hC⟩ := exists_Alate_bound (E := E) (F := F) CA C₁ hCA
  exact ⟨ν₀, hν₀, C, hC0, fun ν hν hνν₀ Sig hSig hSigc S =>
    hC ν _ Sig S (v ν) hν hSig (hC₁ ν hν hνν₀ Sig hSig hSigc)⟩

/-- **`mixed-background:C.6` for fixed `Σ`, in the order used at tex lines 4987–4989.** For
`ρ > 1/2`, `C_A ≥ 0` and a train family satisfying `TrainStrainFamily ρ v`, there is one
`C ≥ 0` such that for every `Σ ≥ 0` there is `ν₁ > 0` with, for all `0 < ν ≤ ν₁` and every `S`,
`A_late ≤ C/(ν(1+Σ)) + C ν^{2ρ-1} ≤ C/(ν(1+Σ)) + C`. The constant `C` is chosen before `Σ`, so
choosing `Σ` large makes the late exponential coefficient `C/(1+Σ)` (relative to `1/ν`) small. -/
theorem Alate_family_fixedSigma {ρ CA : ℝ} {v : ℝ → ℝ → E → F} (hρ : 1 / 2 < ρ)
    (hCA : 0 ≤ CA) (hT : TrainStrainFamily ρ v) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Sig : ℝ, 0 ≤ Sig → ∃ ν₁ : ℝ, 0 < ν₁ ∧ ∀ ν : ℝ, 0 < ν → ν ≤ ν₁ →
      ∀ S : ℝ, Alate CA ν Sig S (v ν) ≠ ⊤ ∧
        AlateReal CA ν Sig S (v ν) ≤ C / (ν * (1 + Sig)) + C * ν ^ (2 * ρ - 1) ∧
        AlateReal CA ν Sig S (v ν) ≤ C / (ν * (1 + Sig)) + C := by
  obtain ⟨ν₀, hν₀, C, hC0, hC⟩ := Alate_family hCA hT
  refine ⟨C, hC0, fun Sig hSig => ?_⟩
  obtain ⟨ν₂, hν₂, hν₂1, hsmall⟩ := one_add_le_sq_of_small (by linarith : (0 : ℝ) < ρ) hSig
  refine ⟨min ν₀ ν₂, lt_min hν₀ hν₂, fun ν hν hνm S => ?_⟩
  have hνν₀ : ν ≤ ν₀ := hνm.trans (min_le_left _ _)
  have hνν₂ : ν ≤ ν₂ := hνm.trans (min_le_right _ _)
  obtain ⟨hne, -, hle⟩ := hC ν hν hνν₀ Sig hSig (hsmall ν hν hνν₂) S
  rw [ec_rho_eq C hν] at hle
  refine ⟨hne, hle, hle.trans ?_⟩
  have h1 : ν ^ (2 * ρ - 1) ≤ 1 :=
    Real.rpow_le_one hν.le (hνν₂.trans hν₂1) (by linarith)
  have : C * ν ^ (2 * ρ - 1) ≤ C := by
    calc C * ν ^ (2 * ρ - 1) ≤ C * 1 := by gcongr
      _ = C := mul_one C
  linarith

end Family

end UnforcedLeray.B0278
