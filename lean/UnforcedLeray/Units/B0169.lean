import UnforcedLeray.Units.B0140
import UnforcedLeray.Lib.Train.Datum

/-!
# B0169 — Exponential-tilt bound for the initial vorticity (`eq:st18-t00166`)

Blueprint unit **B0169**, label `eq:st18-t00166`, `paper/main.tex` lines 2528–2538 (section
`sec:train`); infrastructure INF27 (G9, `Lib/Gaussian/Tilt.lean`, and the train datum layer
`Lib/Train/Datum.lean`, INF16 T1). Dependency: unit **B0140** (`Units/B0140.lean`: the datum
`P_c v₀`, `trainDatum`, its vorticity `curl_trainDatum`, and the train `IsTrain`).

**Statement (tex lines 2528–2538).** The Gaussian initial vorticity satisfies, for every
`λ ≥ 0`, `|ω(q,η,0)| ≤ C exp(-λη + C₀λ²)`, and the same inequality with `η` replaced by `-η`.
"This follows by completing the square in the literal Gaussian; the periodized `q`-sum and its
polynomial prefactor are uniformly bounded." The constants are uniform in the period: the
initial bounds are uniform for `c ≥ 2` (tex line 2182, "Gaussian summation makes the initial
bounds uniform for `c ≥ 2`"; also tex 2511), which is the hypothesis used here.

**What `ω(q,η,0)` is.** The train starts from `v(0) = P_c v₀` (unit B0140, tex 2047, 2146),
so `ω(·,0) = curl(P_c v₀) = P_c ω₀ = ∑ₙ ω₀(q - nc, η)` with
`ω₀ = (2 - |x|²/2) e^{-|x|²/4}` (tex 2138–2139). The bound is stated for three equal
objects: `initialVorticity c = Gaussian.periodize c vorticity` (the lattice sum, defined for
every `c`; it is a convergent sum for `c ≠ 0`), the curl `Cyl.curl (B0140.trainDatum c)` of
the datum (equal to it for `c ≠ 0`, `curl_trainDatum`), and the curl at `s = 0` of any train
`B0140.IsTrain ν c v p ψ` (`curl_train_initial`). `Cyl.curl` is the classical `deriv`-based
curl; the datum is smooth (unit B0140, `Train.datum_contDiff`), so no junk value of `deriv`
enters, and `trainDatum_eq_datum` identifies the B0140 datum with the INF16 T1 `Train.datum`.

**Constants.** `C = 40`, `C₀ = 2`, valid for every real `λ` and every `c` with `c² ≥ 2`
(`abs_initialVorticity_le_tilt`), hence in particular for `λ ≥ 0` and `c ≥ 2` as in the
manuscript. Proof: `|ω₀(x)| ≤ 4 e^{-|x|²/8}` (polynomial prefactor absorbed,
`Train.omega0_abs_le`), the periodized `q`-sum of `e^{-(q-nc)²/8}` is at most `10` for
`c² ≥ 2` (`Gaussian.norm_periodize_le_of_gauss`), and `-η²/8 ≤ -λη + 2λ²` (completing the
square, `(η - 4λ)² ≥ 0`).

**Main declarations.** `initialVorticity`, `initialVorticity_apply`, `hasSum_initialVorticity`,
`vorticity_eq_omega0`, `curl_trainDatum`, `curl_train_initial`, `trainDatum_eq_datum`,
`abs_initialVorticity_le`, `exp_neg_sq_div_eight_le_tilt`, `abs_initialVorticity_le_tilt`,
`abs_initialVorticity_le_tilt_neg`, `abs_initialVorticity_le_tilt_abs`, `initialVorticity_tilt`,
`curl_trainDatum_tilt`, `train_initial_vorticity_tilt`; whole unit `unit_B0169`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.B0169

open UnforcedLeray.GaussianVortex
open UnforcedLeray.Train (Vec toVec)

/-! ### 1. The initial vorticity `ω(·,0) = P_c ω₀` -/

/-- The initial vorticity of the train, `ω(q,η,0) = ∑_{n∈ℤ} ω₀(q - nc, η) = P_c ω₀`
(tex lines 2138–2139, 2146, 2528–2530; unit B0169), with `ω₀` the compiled library vorticity
`GaussianVortex.vorticity = (2 - |x|²/2) e^{-|x|²/4}`. -/
def initialVorticity (c : ℝ) : Plane → ℝ := Gaussian.periodize c vorticity

theorem initialVorticity_apply (c : ℝ) (z : Plane) :
    initialVorticity c z = ∑' n : ℤ, vorticity (z.1 - n * c, z.2) := rfl

/-- The library vorticity `ω₀` is the INF16 profile `Train.omega0` (tex lines 2138–2139). -/
theorem vorticity_eq_omega0 : vorticity = Train.omega0 := by
  funext w
  simp only [Train.omega0, Train.gauss0, vorticity, planarGaussian, radiusSq, neg_div]

/-- `|ω₀(x)| ≤ 4 e^{-|x|²/8}`: the polynomial prefactor is absorbed by half the Gaussian
(tex line 2537, "its polynomial prefactor"). -/
theorem abs_vorticity_le (w : Plane) :
    |vorticity w| ≤ 4 * Real.exp (-(w.1 ^ 2 + w.2 ^ 2) / (4 * 2)) := by
  rw [vorticity_eq_omega0]; exact Train.omega0_abs_le w

/-- The lattice sum defining `ω(q,η,0)` converges absolutely for `c² ≥ 2`. -/
theorem summable_norm_initialVorticity {c : ℝ} (hc : 2 ≤ c ^ 2) (z : Plane) :
    Summable fun n : ℤ => |vorticity (z.1 - n * c, z.2)| := by
  have hsplit : ∀ n : ℤ, 4 * Real.exp (-((z.1 - n * c) ^ 2 + z.2 ^ 2) / (4 * 2)) =
      4 * Real.exp (-z.2 ^ 2 / (4 * 2)) * Real.exp (-(z.1 - n * c) ^ 2 / (4 * 2)) := by
    intro n; rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  have hmaj : Summable fun n : ℤ => 4 * Real.exp (-((z.1 - n * c) ^ 2 + z.2 ^ 2) / (4 * 2)) := by
    simp_rw [hsplit]
    exact (Gaussian.summable_gauss_shift (by norm_num) hc z.1).mul_left _
  exact Summable.of_nonneg_of_le (fun n => abs_nonneg _) (fun n => abs_vorticity_le _) hmaj

/-- `ω(q,η,0) = ∑ₙ ω₀(q - nc, η)` as a genuine (absolutely convergent) sum for `c² ≥ 2`. -/
theorem hasSum_initialVorticity {c : ℝ} (hc : 2 ≤ c ^ 2) (z : Plane) :
    HasSum (fun n : ℤ => vorticity (z.1 - n * c, z.2)) (initialVorticity c z) :=
  (Summable.of_abs (summable_norm_initialVorticity hc z)).hasSum

/-- The vorticity of the train datum is `P_c ω₀` (unit B0140, `curl_trainDatum`):
`curl(P_c v₀) = ω(·,0)`, for `c ≠ 0`. -/
theorem curl_trainDatum {c : ℝ} (hc : c ≠ 0) (z : Plane) :
    Cyl.curl (B0140.trainDatum c) z = initialVorticity c z :=
  B0140.curl_trainDatum hc z

/-- For any train (unit B0140, `IsTrain`, tex lines 2045–2051, 2141–2147), the vorticity at
`s = 0` is `ω(·,0) = P_c ω₀`, for `c ≠ 0`. -/
theorem curl_train_initial {ν c : ℝ} {v : ℝ → Plane → Vec} {p ψ : ℝ → Plane → ℝ}
    (h : B0140.IsTrain ν c v p ψ) (hc : c ≠ 0) (z : Plane) :
    Cyl.curl (v 0) z = initialVorticity c z := by
  rw [h.initial]; exact curl_trainDatum hc z

/-- `v₀` in the `Vec` carrier is the INF16 profile `Train.v0`. -/
theorem toVec_velocity (w : Plane) : toVec (velocity w) = Train.v0 w := by
  have hg : Train.gauss0 w = planarGaussian w := by
    simp only [Train.gauss0, planarGaussian, radiusSq, neg_div]
  have e : velocity w = planarGaussian w • ((-w.2, w.1) : Plane) := by
    ext <;> simp [velocity, mul_comm]
  rw [Train.v0, hg, e, ← Train.toVecL_apply, map_smul, Train.toVecL_apply]

/-- The B0140 datum is the INF16 T1 datum `Train.datum` (`Lib/Train/Datum.lean`). -/
theorem trainDatum_eq_datum (c : ℝ) : B0140.trainDatum c = Train.datum c := by
  funext z
  rw [B0140.trainDatum_apply, Train.datum_apply, ← Train.toVecL_apply,
    Train.toVecL.map_tsum]
  simp only [Train.toVecL_apply, toVec_velocity]

/-! ### 2. The Gaussian bound and the exponential tilt (tex lines 2528–2538) -/

/-- **The periodized `q`-sum is uniformly bounded** (tex lines 2536–2538): for `c² ≥ 2` and
all `(q, η)`, `|ω(q,η,0)| ≤ 40 e^{-η²/8}`. -/
theorem abs_initialVorticity_le {c : ℝ} (hc : 2 ≤ c ^ 2) (z : Plane) :
    |initialVorticity c z| ≤ 40 * Real.exp (-z.2 ^ 2 / 8) := by
  have hf : ∀ w : Plane, ‖vorticity w‖ ≤ 4 * Real.exp (-(w.1 ^ 2 + w.2 ^ 2) / (4 * 2)) :=
    fun w => by rw [Real.norm_eq_abs]; exact abs_vorticity_le w
  have h := Gaussian.norm_periodize_le_of_gauss (by norm_num : (0 : ℝ) < 2) hc hf z
  rw [Real.norm_eq_abs] at h
  have e : -z.2 ^ 2 / (4 * 2) = -z.2 ^ 2 / 8 := by norm_num
  rw [e] at h
  unfold initialVorticity
  linarith

/-- **Completing the square** (tex line 2536): `e^{-η²/8} ≤ e^{-λη + 2λ²}` for all real
`η, λ`, since `η²/8 - λη + 2λ² = (η - 4λ)²/8 ≥ 0`. -/
theorem exp_neg_sq_div_eight_le_tilt (η lam : ℝ) :
    Real.exp (-η ^ 2 / 8) ≤ Real.exp (-lam * η + 2 * lam ^ 2) :=
  Real.exp_le_exp.2 (by nlinarith [sq_nonneg (η - 4 * lam)])

/-- **Exponential tilt, explicit constants** (`eq:st18-t00166`): for every real `λ`, every
period with `c² ≥ 2` and all `(q, η)`, `|ω(q,η,0)| ≤ 40 e^{-λη + 2λ²}`. -/
theorem abs_initialVorticity_le_tilt {c : ℝ} (hc : 2 ≤ c ^ 2) (lam : ℝ) (z : Plane) :
    |initialVorticity c z| ≤ 40 * Real.exp (-lam * z.2 + 2 * lam ^ 2) :=
  (abs_initialVorticity_le hc z).trans
    (mul_le_mul_of_nonneg_left (exp_neg_sq_div_eight_le_tilt _ _) (by norm_num))

/-- The same inequality with `η` replaced by `-η` (tex line 2534). -/
theorem abs_initialVorticity_le_tilt_neg {c : ℝ} (hc : 2 ≤ c ^ 2) (lam : ℝ) (z : Plane) :
    |initialVorticity c z| ≤ 40 * Real.exp (-lam * (-z.2) + 2 * lam ^ 2) := by
  have h := abs_initialVorticity_le_tilt hc (-lam) z
  rwa [neg_sq, show -(-lam) * z.2 = -lam * -z.2 by ring] at h

/-- Two-sided form: `|ω(q,η,0)| ≤ 40 e^{-λ|η| + 2λ²}` (both ends of the line, tex
line 2551; the manuscript uses it for `λ ≥ 0`, it holds for every real `λ`). -/
theorem abs_initialVorticity_le_tilt_abs {c : ℝ} (hc : 2 ≤ c ^ 2) (lam : ℝ) (z : Plane) :
    |initialVorticity c z| ≤ 40 * Real.exp (-lam * |z.2| + 2 * lam ^ 2) := by
  rcases le_total 0 z.2 with hz | hz
  · rw [abs_of_nonneg hz]; exact abs_initialVorticity_le_tilt hc lam z
  · rw [abs_of_nonpos hz]; exact abs_initialVorticity_le_tilt_neg hc lam z

/-- **`eq:st18-t00166` in the manuscript's form** (tex lines 2528–2538). There are constants
`C, C₀ > 0` such that for every period `c ≥ 2`, every `λ ≥ 0` and all `(q, η)`:
`|ω(q,η,0)| ≤ C exp(-λη + C₀λ²)` and the same with `η` replaced by `-η`. The constants do not
depend on `c` (tex line 2182). -/
theorem initialVorticity_tilt : ∃ C C₀ : ℝ, 0 < C ∧ 0 < C₀ ∧
    ∀ c : ℝ, 2 ≤ c → ∀ lam : ℝ, 0 ≤ lam → ∀ q η : ℝ,
      |initialVorticity c (q, η)| ≤ C * Real.exp (-lam * η + C₀ * lam ^ 2) ∧
      |initialVorticity c (q, η)| ≤ C * Real.exp (-lam * (-η) + C₀ * lam ^ 2) :=
  ⟨40, 2, by norm_num, by norm_num, fun _ hc lam _ q η =>
    ⟨abs_initialVorticity_le_tilt (Train.two_le_sq hc) lam (q, η),
      abs_initialVorticity_le_tilt_neg (Train.two_le_sq hc) lam (q, η)⟩⟩

/-- `eq:st18-t00166` for the curl of the train datum `P_c v₀` (unit B0140). -/
theorem curl_trainDatum_tilt : ∃ C C₀ : ℝ, 0 < C ∧ 0 < C₀ ∧
    ∀ c : ℝ, 2 ≤ c → ∀ lam : ℝ, 0 ≤ lam → ∀ q η : ℝ,
      |Cyl.curl (B0140.trainDatum c) (q, η)| ≤ C * Real.exp (-lam * η + C₀ * lam ^ 2) ∧
      |Cyl.curl (B0140.trainDatum c) (q, η)| ≤ C * Real.exp (-lam * (-η) + C₀ * lam ^ 2) := by
  obtain ⟨C, C₀, hC, hC₀, h⟩ := initialVorticity_tilt
  refine ⟨C, C₀, hC, hC₀, fun c hc lam hlam q η => ?_⟩
  rw [curl_trainDatum (by linarith : c ≠ 0)]
  exact h c hc lam hlam q η

/-- `eq:st18-t00166` for the vorticity at `s = 0` of any train (unit B0140, `IsTrain`):
the constants are uniform in the viscosity `ν`, the period `c ≥ 2` and the solution. -/
theorem train_initial_vorticity_tilt : ∃ C C₀ : ℝ, 0 < C ∧ 0 < C₀ ∧
    ∀ (ν c : ℝ) (v : ℝ → Plane → Vec) (p ψ : ℝ → Plane → ℝ), B0140.IsTrain ν c v p ψ →
      2 ≤ c → ∀ lam : ℝ, 0 ≤ lam → ∀ q η : ℝ,
        |Cyl.curl (v 0) (q, η)| ≤ C * Real.exp (-lam * η + C₀ * lam ^ 2) ∧
        |Cyl.curl (v 0) (q, η)| ≤ C * Real.exp (-lam * (-η) + C₀ * lam ^ 2) := by
  obtain ⟨C, C₀, hC, hC₀, h⟩ := initialVorticity_tilt
  refine ⟨C, C₀, hC, hC₀, fun ν c v p ψ htr hc lam hlam q η => ?_⟩
  rw [curl_train_initial htr (by linarith : c ≠ 0)]
  exact h c hc lam hlam q η

/-! ### 3. The whole unit -/

/-- **Unit B0169** (`eq:st18-t00166`, tex lines 2528–2538). There are constants `C, C₀ > 0`,
independent of the period `c ≥ 2` (tex line 2182), such that for every `λ ≥ 0` and all
`(q, η)` the initial vorticity `ω(q,η,0) = ∑ₙ ω₀(q - nc, η)` satisfies
`|ω(q,η,0)| ≤ C exp(-λη + C₀λ²)` and the same inequality with `η` replaced by `-η`; here
`ω(·,0)` is `P_c ω₀`, the curl of the datum `P_c v₀`, and the curl at `s = 0` of any train
(unit B0140). -/
theorem unit_B0169 : ∃ C C₀ : ℝ, 0 < C ∧ 0 < C₀ ∧
    ∀ c : ℝ, 2 ≤ c → ∀ lam : ℝ, 0 ≤ lam → ∀ q η : ℝ,
      -- `ω(q,η,0) = ∑ₙ ω₀(q - nc, η)` (absolutely convergent) …
      HasSum (fun n : ℤ => vorticity (q - n * c, η)) (initialVorticity c (q, η)) ∧
      -- … is the curl of the datum `P_c v₀` …
      Cyl.curl (B0140.trainDatum c) (q, η) = initialVorticity c (q, η) ∧
      -- … and the vorticity at `s = 0` of every train …
      (∀ (ν : ℝ) (v : ℝ → Plane → Vec) (p ψ : ℝ → Plane → ℝ), B0140.IsTrain ν c v p ψ →
        Cyl.curl (v 0) (q, η) = initialVorticity c (q, η)) ∧
      -- … and obeys the exponential tilt bound, and the one with `η ↦ -η`
      |initialVorticity c (q, η)| ≤ C * Real.exp (-lam * η + C₀ * lam ^ 2) ∧
      |initialVorticity c (q, η)| ≤ C * Real.exp (-lam * (-η) + C₀ * lam ^ 2) := by
  obtain ⟨C, C₀, hC, hC₀, h⟩ := initialVorticity_tilt
  refine ⟨C, C₀, hC, hC₀, fun c hc lam hlam q η => ?_⟩
  have hc0 : c ≠ 0 := by linarith
  exact ⟨hasSum_initialVorticity (Train.two_le_sq hc) (q, η), curl_trainDatum hc0 (q, η),
    fun ν v p ψ htr => curl_train_initial htr hc0 (q, η), (h c hc lam hlam q η).1,
    (h c hc lam hlam q η).2⟩

end UnforcedLeray.B0169
