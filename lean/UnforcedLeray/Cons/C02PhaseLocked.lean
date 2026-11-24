import UnforcedLeray.Blueprint.Construction.Steps
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Step C2: the phase-locked viscosity sequence (`eq:st18-t00763`)

`paper/main.tex`, lines 13618–13626; blueprint unit B0997 (depending on B0085, B0882, B0883,
B0996). The manuscript: "The phase derivative is `-ω/ν² - Im κ/ν`, so `ω ≠ 0` gives
`ν_n ↓ 0` with `ω/ν_n - Im κ log ν_n + arg C₀ = 2π sign(ω) n`, `ν_n ~ |ω|/(2πn)`."

`StepPhaseLocked F` (`Blueprint/Construction/Steps.lean`, line 264) is a property of the
field `F.ν` of a `ConstructionData`. That field is free in the record (its only constraint is
C2 itself), so C2 cannot hold for every record: it holds for the record whose `ν` is the
phase-locked sequence. This file constructs that sequence and proves C2 for it.

* `PhaseLock`: the scalar statement. For real `ω ≠ 0`, `b`, `c`, the sequence
  `lockedNu ω b c n` is positive, tends to `0`, is strictly decreasing for large `n`, satisfies
  `n ν_n → |ω|/(2π)` (that is, `ν_n ~ |ω|/(2πn)`), and
  `ω/ν_n - b log ν_n + c = 2π sign(ω) n` for all large `n`. The proof writes `x = 1/ν` and
  multiplies the phase by `sign ω`: `G(x) = |ω|x + sign(ω) b log x + sign(ω) c`. On
  `x ≥ M = 1 + |b|/|ω|` one has `x (G(y) - G(x)) ≥ |ω|(y - x)` for `y ≥ x` (this is the
  manuscript's "phase derivative" remark), so `G` is strictly increasing there and tends to
  `+∞`; the intermediate value theorem gives the root `x_n ≥ M` of `G = 2πn` for large `n`,
  and `G(x) ≤ (|ω| + |b|)x + |c|` forces `x_n → ∞`.
* `ConstructionData.phaseLockedNu F`: that sequence with `ω = F.frequency`, `b = Im κ`,
  `c = arg C₀`. It depends only on `F.planar` and `F.σ₀`, never on `F.ν`.
* `ConstructionData.stepPhaseLocked_of_eq`: `StepPhaseLocked F` whenever `ω ≠ 0` and
  `F.ν = F.phaseLockedNu`; `stepPhaseLocked_withPhaseLocked`: C2 for the record
  `F.withPhaseLocked` (that is, `F` with its `ν` replaced by the phase-locked sequence), and
  `F.withPhaseLocked` satisfies C1 exactly when `F` does. The only hypothesis is the
  manuscript's `ω ≠ 0` (line 13620); it follows from C1 (`-2 < ω < 0`).

File location: the wave assigned `Con/C02PhaseLocked.lean`, but Lean 4.34 rejects the module
name `UnforcedLeray.Con.C02PhaseLocked` (`'Con' is a reserved file name on some operating
systems`, `Lean/Elab/Import.lean`), so the file is `Cons/C02PhaseLocked.lean`.
`#print axioms` of the main theorems gives `[propext, Classical.choice, Quot.sound]`.

No hypothesis on `C₀` is needed: the identity is an identity of real numbers whatever
`arg C₀` is. (Compare the earlier draft

`exists_small_phase_locked`, which gives one locked viscosity below each threshold but not a
locked viscosity for every large index.)
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology

namespace UnforcedLeray.Blueprint

namespace PhaseLock

/-! ## The scalar phase -/

/-- The phase of `eq:st18-t00763` (line 13623), `ω/ν - b log ν + c`, with `b = Im κ` and
`c = arg C₀`. -/
def phase (ω b c ν : ℝ) : ℝ := ω / ν - b * Real.log ν + c

/-- The phase in the reciprocal variable `x = 1/ν`, multiplied by `sign ω`:
`G(x) = |ω|x + sign(ω) b log x + sign(ω) c`. -/
def recipPhase (ω b c x : ℝ) : ℝ :=
  |ω| * x + Real.sign ω * b * Real.log x + Real.sign ω * c

/-- The threshold `M = 1 + |b|/|ω|` beyond which `G` is increasing (the manuscript's remark
that the phase derivative `-ω/ν² - Im κ/ν` has the sign of `-ω` for small `ν`, line 13619). -/
def threshold (ω b : ℝ) : ℝ := 1 + |b| / |ω|

theorem one_le_threshold (ω b : ℝ) : 1 ≤ threshold ω b := by
  unfold threshold
  have : 0 ≤ |b| / |ω| := div_nonneg (abs_nonneg _) (abs_nonneg _)
  linarith

theorem threshold_pos (ω b : ℝ) : 0 < threshold ω b :=
  lt_of_lt_of_le one_pos (one_le_threshold ω b)

theorem sign_mul_sign {ω : ℝ} (hω : ω ≠ 0) : Real.sign ω * Real.sign ω = 1 := by
  rcases lt_or_gt_of_ne hω with h | h
  · rw [Real.sign_of_neg h]; norm_num
  · rw [Real.sign_of_pos h]; norm_num

theorem sign_mul_self (ω : ℝ) : Real.sign ω * ω = |ω| := by
  rcases lt_trichotomy ω 0 with h | h | h
  · rw [Real.sign_of_neg h, abs_of_neg h]; ring
  · subst h; simp
  · rw [Real.sign_of_pos h, abs_of_pos h]; ring

theorem abs_sign_le (ω : ℝ) : |Real.sign ω| ≤ 1 := by
  rcases Real.sign_apply_eq ω with h | h | h <;> rw [h] <;> norm_num

/-- `phase(1/x) = sign(ω) G(x)` for `ω ≠ 0`. -/
theorem phase_inv {ω : ℝ} (hω : ω ≠ 0) (b c x : ℝ) :
    phase ω b c x⁻¹ = Real.sign ω * recipPhase ω b c x := by
  have hs := sign_mul_sign hω
  have ha : |ω| = Real.sign ω * ω := (sign_mul_self ω).symm
  simp only [phase, recipPhase, div_inv_eq_mul, Real.log_inv, ha]
  linear_combination (-(ω * x) - b * Real.log x - c) * hs

/-- The increment bound: for `M ≤ x ≤ y`, `|ω|(y - x) ≤ x (G(y) - G(x))`. This is the
discrete form of the derivative remark of line 13619. -/
theorem increment_bound {ω : ℝ} (hω : ω ≠ 0) (b c : ℝ) {x y : ℝ}
    (hx : threshold ω b ≤ x) (hxy : x ≤ y) :
    |ω| * (y - x) ≤ x * (recipPhase ω b c y - recipPhase ω b c x) := by
  have hω' : 0 < |ω| := abs_pos.mpr hω
  have hx0 : 0 < x := lt_of_lt_of_le (threshold_pos ω b) hx
  have hy0 : 0 < y := lt_of_lt_of_le hx0 hxy
  -- `|ω| x ≥ |ω| + |b|`
  have hωx : |ω| + |b| ≤ |ω| * x := by
    have h1 : |ω| * threshold ω b = |ω| + |b| := by
      unfold threshold; field_simp
    rw [← h1]
    exact mul_le_mul_of_nonneg_left hx hω'.le
  -- `0 ≤ L = log y - log x` and `x L ≤ y - x`
  set L := Real.log y - Real.log x with hL
  have hL0 : 0 ≤ L := by
    have := Real.log_le_log hx0 hxy
    linarith
  have hxL : x * L ≤ y - x := by
    have h := Real.log_le_sub_one_of_pos (div_pos hy0 hx0)
    rw [Real.log_div hy0.ne' hx0.ne'] at h
    have h' : x * L ≤ x * (y / x - 1) := mul_le_mul_of_nonneg_left h hx0.le
    have h'' : x * (y / x - 1) = y - x := by field_simp
    linarith
  -- `sign(ω) b L ≥ -|b| L`
  have hsb : -(|b| * L) ≤ Real.sign ω * b * L := by
    have h1 : |Real.sign ω * b * L| ≤ |b| * L := by
      rw [abs_mul, abs_mul, abs_of_nonneg hL0]
      calc |Real.sign ω| * |b| * L = |Real.sign ω| * (|b| * L) := by ring
        _ ≤ 1 * (|b| * L) :=
          mul_le_mul_of_nonneg_right (abs_sign_le ω) (mul_nonneg (abs_nonneg b) hL0)
        _ = |b| * L := one_mul _
    linarith [neg_abs_le (Real.sign ω * b * L)]
  have hdiff : recipPhase ω b c y - recipPhase ω b c x = |ω| * (y - x) + Real.sign ω * b * L := by
    simp only [recipPhase, hL]; ring
  rw [hdiff]
  have hd : 0 ≤ y - x := by linarith
  have hb : |b| * (x * L) ≤ |b| * (y - x) := mul_le_mul_of_nonneg_left hxL (abs_nonneg b)
  have hx1 : (y - x) * (|ω| + |b|) ≤ (y - x) * (|ω| * x) := mul_le_mul_of_nonneg_left hωx hd
  nlinarith

/-- `G` is strictly increasing on `[M, ∞)`. -/
theorem strictMonoOn_recipPhase {ω : ℝ} (hω : ω ≠ 0) (b c : ℝ) :
    StrictMonoOn (recipPhase ω b c) (Ici (threshold ω b)) := by
  intro x hx y _ hxy
  have h := increment_bound hω b c (mem_Ici.mp hx) hxy.le
  have hx0 : 0 < x := lt_of_lt_of_le (threshold_pos ω b) (mem_Ici.mp hx)
  have hpos : 0 < |ω| * (y - x) := mul_pos (abs_pos.mpr hω) (by linarith)
  have : 0 < x * (recipPhase ω b c y - recipPhase ω b c x) := lt_of_lt_of_le hpos h
  have := (pos_iff_pos_of_mul_pos this).mp hx0
  linarith

theorem continuousOn_recipPhase (ω b c : ℝ) :
    ContinuousOn (recipPhase ω b c) (Ici (threshold ω b)) := by
  intro x hx
  have hx0 : x ≠ 0 := (lt_of_lt_of_le (threshold_pos ω b) hx).ne'
  exact (((continuousAt_id.const_mul |ω|).add
    ((Real.continuousAt_log hx0).const_mul (Real.sign ω * b))).add_const
      (Real.sign ω * c)).continuousWithinAt

/-- `G(x) → +∞` as `x → ∞`: from the increment bound at `x = M`, `G` grows at least linearly. -/
theorem tendsto_recipPhase {ω : ℝ} (hω : ω ≠ 0) (b c : ℝ) :
    Tendsto (recipPhase ω b c) atTop atTop := by
  set M := threshold ω b
  have hM : 0 < M := threshold_pos ω b
  have hlin : Tendsto (fun y : ℝ => |ω| / M * y + (recipPhase ω b c M - |ω| / M * M)) atTop
      atTop :=
    tendsto_atTop_add_const_right _ _
      (tendsto_id.const_mul_atTop (div_pos (abs_pos.mpr hω) hM))
  refine tendsto_atTop_mono' _ ?_ hlin
  filter_upwards [eventually_ge_atTop M] with y hy
  have h := increment_bound hω b c (le_refl M) hy
  have : |ω| / M * (y - M) ≤ recipPhase ω b c y - recipPhase ω b c M := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hM]
    linarith
  linarith

/-- The upper bound `G(x) ≤ (|ω| + |b|)x + |c|` for `x ≥ 1`. -/
theorem recipPhase_le (ω b c : ℝ) {x : ℝ} (hx : 1 ≤ x) :
    recipPhase ω b c x ≤ (|ω| + |b|) * x + |c| := by
  have hx0 : 0 < x := lt_of_lt_of_le one_pos hx
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have hlogx : Real.log x ≤ x := by linarith [Real.log_le_sub_one_of_pos hx0]
  have hs := abs_sign_le ω
  have h1 : Real.sign ω * b * Real.log x ≤ |b| * x := by
    have : |Real.sign ω * b * Real.log x| ≤ |b| * x := by
      rw [abs_mul, abs_mul, abs_of_nonneg hlog0]
      have := abs_nonneg b
      have := abs_nonneg (Real.sign ω)
      calc |Real.sign ω| * |b| * Real.log x ≤ 1 * |b| * x := by gcongr
        _ = |b| * x := by ring
    exact le_trans (le_abs_self _) this
  have h2 : Real.sign ω * c ≤ |c| := by
    have : |Real.sign ω * c| ≤ |c| := by
      rw [abs_mul]
      calc |Real.sign ω| * |c| ≤ 1 * |c| := by gcongr
        _ = |c| := one_mul _
    exact le_trans (le_abs_self _) this
  unfold recipPhase
  nlinarith

/-! ## The sequence -/

open Classical in
/-- The root `x_n ≥ M` of `G(x) = 2πn` when one exists, and `M` otherwise. -/
def lockedRecip (ω b c : ℝ) (n : ℕ) : ℝ :=
  if h : ∃ x, threshold ω b ≤ x ∧ recipPhase ω b c x = 2 * Real.pi * n then
    Classical.choose h
  else threshold ω b

/-- The phase-locked viscosity `ν_n = 1/x_n` (`eq:st18-t00763`). -/
def lockedNu (ω b c : ℝ) (n : ℕ) : ℝ := (lockedRecip ω b c n)⁻¹

theorem threshold_le_lockedRecip (ω b c : ℝ) (n : ℕ) : threshold ω b ≤ lockedRecip ω b c n := by
  unfold lockedRecip
  split_ifs with h
  · exact (Classical.choose_spec h).1
  · exact le_refl _

theorem lockedRecip_pos (ω b c : ℝ) (n : ℕ) : 0 < lockedRecip ω b c n :=
  lt_of_lt_of_le (threshold_pos ω b) (threshold_le_lockedRecip ω b c n)

theorem lockedNu_pos (ω b c : ℝ) (n : ℕ) : 0 < lockedNu ω b c n :=
  inv_pos.mpr (lockedRecip_pos ω b c n)

/-- For all large `n`, `G(M) ≤ 2πn`. -/
theorem eventually_threshold_le (ω b c : ℝ) :
    ∀ᶠ n : ℕ in atTop, recipPhase ω b c (threshold ω b) ≤ 2 * Real.pi * n :=
  (tendsto_natCast_atTop_atTop.const_mul_atTop (mul_pos two_pos Real.pi_pos)).eventually_ge_atTop
    _

/-- For all large `n`, `G(x_n) = 2πn` (intermediate value theorem on `[M, ∞)`). -/
theorem eventually_recipPhase_lockedRecip {ω : ℝ} (hω : ω ≠ 0) (b c : ℝ) :
    ∀ᶠ n : ℕ in atTop, recipPhase ω b c (lockedRecip ω b c n) = 2 * Real.pi * n := by
  filter_upwards [eventually_threshold_le ω b c] with n hn
  have hex : ∃ x, threshold ω b ≤ x ∧ recipPhase ω b c x = 2 * Real.pi * n := by
    obtain ⟨x, hx, hGx⟩ := intermediate_value_Ici (continuousOn_recipPhase ω b c)
      (tendsto_recipPhase hω b c) (mem_Ici.mpr hn)
    exact ⟨x, mem_Ici.mp hx, hGx⟩
  unfold lockedRecip
  split_ifs with h
  · exact (Classical.choose_spec h).2
  · exact absurd hex h

/-- `x_n → ∞`, from `2πn = G(x_n) ≤ (|ω| + |b|)x_n + |c|`. -/
theorem tendsto_lockedRecip {ω : ℝ} (hω : ω ≠ 0) (b c : ℝ) :
    Tendsto (lockedRecip ω b c) atTop atTop := by
  have hK : 0 < |ω| + |b| := add_pos_of_pos_of_nonneg (abs_pos.mpr hω) (abs_nonneg b)
  have hlow : Tendsto (fun n : ℕ => (2 * Real.pi) / (|ω| + |b|) * (n : ℝ) + (-|c| / (|ω| + |b|)))
      atTop atTop :=
    tendsto_atTop_add_const_right _ _
      (tendsto_natCast_atTop_atTop.const_mul_atTop (div_pos (mul_pos two_pos Real.pi_pos) hK))
  refine tendsto_atTop_mono' _ ?_ hlow
  filter_upwards [eventually_recipPhase_lockedRecip hω b c] with n hn
  have h1 := recipPhase_le ω b c
    (le_trans (one_le_threshold ω b) (threshold_le_lockedRecip ω b c n))
  rw [hn] at h1
  have : (2 * Real.pi) / (|ω| + |b|) * (n : ℝ) + (-|c| / (|ω| + |b|)) =
      (2 * Real.pi * n - |c|) / (|ω| + |b|) := by
    field_simp; ring
  rw [this, div_le_iff₀ hK]
  linarith

/-- `ν_n → 0`. -/
theorem tendsto_lockedNu {ω : ℝ} (hω : ω ≠ 0) (b c : ℝ) :
    Tendsto (lockedNu ω b c) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp (tendsto_lockedRecip hω b c)

/-- The phase identity `ω/ν_n - b log ν_n + c = 2π sign(ω) n` for all large `n`
(`eq:st18-t00763`). -/
theorem eventually_phase_lockedNu {ω : ℝ} (hω : ω ≠ 0) (b c : ℝ) :
    ∀ᶠ n : ℕ in atTop, ω / lockedNu ω b c n - b * Real.log (lockedNu ω b c n) + c =
      2 * Real.pi * Real.sign ω * n := by
  filter_upwards [eventually_recipPhase_lockedRecip hω b c] with n hn
  have h := phase_inv hω b c (lockedRecip ω b c n)
  simp only [phase] at h
  unfold lockedNu
  rw [h, hn]
  ring

/-- `ν_n ↓ 0` (line 13621): the sequence is strictly decreasing from some index on. -/
theorem eventually_strictAnti_lockedNu {ω : ℝ} (hω : ω ≠ 0) (b c : ℝ) :
    ∃ N : ℕ, StrictAntiOn (lockedNu ω b c) (Ici N) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_recipPhase_lockedRecip hω b c)
  refine ⟨N, ?_⟩
  intro m hm n hn hmn
  have hmono := strictMonoOn_recipPhase hω b c
  have hxm := threshold_le_lockedRecip ω b c m
  have hxn := threshold_le_lockedRecip ω b c n
  have hlt : lockedRecip ω b c m < lockedRecip ω b c n := by
    rw [← hmono.lt_iff_lt (mem_Ici.mpr hxm) (mem_Ici.mpr hxn), hN m (mem_Ici.mp hm),
      hN n (mem_Ici.mp hn)]
    have : (m : ℝ) < n := by exact_mod_cast hmn
    nlinarith [Real.pi_pos]
  exact inv_strictAnti₀ (lockedRecip_pos ω b c m) hlt

/-- `ν_n ~ |ω|/(2πn)` (line 13624), in the form `n ν_n → |ω|/(2π)`. -/
theorem tendsto_mul_lockedNu {ω : ℝ} (hω : ω ≠ 0) (b c : ℝ) :
    Tendsto (fun n : ℕ => (n : ℝ) * lockedNu ω b c n) atTop (𝓝 (|ω| / (2 * Real.pi))) := by
  have hx := tendsto_lockedRecip hω b c
  have hlog : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    simpa only [id_eq] using Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hinv : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hlim : Tendsto (fun x : ℝ => (|ω| + Real.sign ω * b * (Real.log x / x) +
      Real.sign ω * c * x⁻¹) / (2 * Real.pi)) atTop (𝓝 (|ω| / (2 * Real.pi))) := by
    have := ((tendsto_const_nhds (x := |ω|)).add (hlog.const_mul (Real.sign ω * b))).add
      (hinv.const_mul (Real.sign ω * c))
    simp only [mul_zero, add_zero] at this
    exact this.div_const _
  refine (hlim.comp hx).congr' ?_
  filter_upwards [eventually_recipPhase_lockedRecip hω b c] with n hn
  have hx0 := lockedRecip_pos ω b c n
  simp only [Function.comp, lockedNu]
  have hpi : (2 * Real.pi) ≠ 0 := (mul_pos two_pos Real.pi_pos).ne'
  have hG : |ω| * lockedRecip ω b c n + Real.sign ω * b * Real.log (lockedRecip ω b c n) +
      Real.sign ω * c = 2 * Real.pi * n := hn
  field_simp
  linear_combination hG

/-- The scalar content of `eq:st18-t00763`: for `ω ≠ 0` the sequence `ν_n = lockedNu ω b c n`
is positive, tends to `0`, and is phase-locked for all large `n`. -/
theorem lockedNu_spec {ω : ℝ} (hω : ω ≠ 0) (b c : ℝ) :
    (∀ n, 0 < lockedNu ω b c n) ∧ Tendsto (lockedNu ω b c) atTop (𝓝 0) ∧
      ∀ᶠ n : ℕ in atTop, ω / lockedNu ω b c n - b * Real.log (lockedNu ω b c n) + c =
        2 * Real.pi * Real.sign ω * n :=
  ⟨lockedNu_pos ω b c, tendsto_lockedNu hω b c, eventually_phase_lockedNu hω b c⟩

end PhaseLock

/-! ## Step C2 for the construction data -/

namespace ConstructionData

variable (F : ConstructionData)

/-- The phase-locked viscosity sequence of the data (`eq:st18-t00763`, lines 13618–13626,
unit B0997): `ν_n` with `ω/ν_n - Im κ log ν_n + arg C₀ = 2π sign(ω) n`, `ω = Im λ`. It is built
from `F.planar` and `F.σ₀` only (through `ω`, `κ` and `C₀ = 𝒞(σ₀)`), never from `F.ν`. -/
def phaseLockedNu : ℕ → ℝ :=
  PhaseLock.lockedNu F.frequency F.κ.im (Complex.arg F.C₀)

/-- The record `F` with its viscosities replaced by the phase-locked sequence. All other
fields are those of `F`. -/
def withPhaseLocked : ConstructionData := { F with ν := F.phaseLockedNu }

@[simp] theorem withPhaseLocked_ν : F.withPhaseLocked.ν = F.phaseLockedNu := rfl

@[simp] theorem withPhaseLocked_planar : F.withPhaseLocked.planar = F.planar := rfl

@[simp] theorem withPhaseLocked_σ₀ : F.withPhaseLocked.σ₀ = F.σ₀ := rfl

/-- Changing `ν` does not change the phase-locked sequence. -/
theorem withPhaseLocked_phaseLockedNu :
    F.withPhaseLocked.phaseLockedNu = F.phaseLockedNu := rfl

variable {F}

/-- **Step C2** (`eq:st18-t00763`, lines 13618–13626, unit B0997) for any record whose
viscosities are the phase-locked sequence, under the manuscript's hypothesis `ω ≠ 0`
(line 13620). -/
theorem stepPhaseLocked_of_eq (hω : F.frequency ≠ 0) (hν : F.ν = F.phaseLockedNu) :
    StepPhaseLocked F := by
  rw [StepPhaseLocked, hν]
  exact PhaseLock.lockedNu_spec hω _ _

/-- **Step C2** for `F.withPhaseLocked`, under `ω ≠ 0` (lines 13618–13626, unit B0997). -/
theorem stepPhaseLocked_withPhaseLocked (hω : F.frequency ≠ 0) :
    StepPhaseLocked F.withPhaseLocked :=
  stepPhaseLocked_of_eq hω rfl

/-- `ω ≠ 0` follows from C1 (`-2 < ω < 0`, `eq:st18-t00008`). -/
theorem frequency_ne_zero_of_C1 (h1 : StepReferenceChoice F) : F.frequency ≠ 0 :=
  h1.2.1.2.ne

/-- **Step C2** for `F.withPhaseLocked`, from C1. -/
theorem stepPhaseLocked_withPhaseLocked_of_C1 (h1 : StepReferenceChoice F) :
    StepPhaseLocked F.withPhaseLocked :=
  stepPhaseLocked_withPhaseLocked (frequency_ne_zero_of_C1 h1)

/-- **Step C2** for a record satisfying C1 whose viscosities are the phase-locked sequence. -/
theorem stepPhaseLocked_of_C1 (h1 : StepReferenceChoice F) (hν : F.ν = F.phaseLockedNu) :
    StepPhaseLocked F :=
  stepPhaseLocked_of_eq (frequency_ne_zero_of_C1 h1) hν

/-- C1 does not involve `ν`: `F.withPhaseLocked` satisfies C1 exactly when `F` does. -/
theorem stepReferenceChoice_withPhaseLocked :
    StepReferenceChoice F.withPhaseLocked ↔ StepReferenceChoice F := Iff.rfl

/-- C1 and C2 together for `F.withPhaseLocked`, from C1 for `F`. -/
theorem stepReferenceChoice_and_stepPhaseLocked (h1 : StepReferenceChoice F) :
    StepReferenceChoice F.withPhaseLocked ∧ StepPhaseLocked F.withPhaseLocked :=
  ⟨h1, stepPhaseLocked_withPhaseLocked_of_C1 h1⟩

/-- Existence form of C2: for `ω ≠ 0` some choice of the viscosities makes C2 hold, with all
other fields of `F` unchanged. -/
theorem exists_stepPhaseLocked (hω : F.frequency ≠ 0) :
    ∃ ν : ℕ → ℝ, StepPhaseLocked { F with ν := ν } :=
  ⟨F.phaseLockedNu, stepPhaseLocked_withPhaseLocked hω⟩

/-- `ν_n ↓ 0` (line 13621): the phase-locked viscosities decrease strictly from some index on. -/
theorem phaseLockedNu_eventually_strictAnti (hω : F.frequency ≠ 0) :
    ∃ N : ℕ, StrictAntiOn F.phaseLockedNu (Ici N) :=
  PhaseLock.eventually_strictAnti_lockedNu hω _ _

/-- `ν_n ~ |ω|/(2πn)` (line 13624): `n ν_n → |ω|/(2π)`. -/
theorem tendsto_mul_phaseLockedNu (hω : F.frequency ≠ 0) :
    Tendsto (fun n : ℕ => (n : ℝ) * F.phaseLockedNu n) atTop
      (𝓝 (|F.frequency| / (2 * Real.pi))) :=
  PhaseLock.tendsto_mul_lockedNu hω _ _

end ConstructionData

end UnforcedLeray.Blueprint

