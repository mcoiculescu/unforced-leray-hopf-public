import UnforcedLeray.Units.B0079.Bounds
import UnforcedLeray.Units.B0011

/-!
# Unit B0079 (`eq:st18-t00060`): the Green formula for `Δ_n` on `L²_M` and its pointwise bounds

Blueprint unit `B0079`, label `eq:st18-t00060`, `paper/main.tex` lines 1366–1379 (in the proof
"Transfer to the weighted realizations", Section `sec:st18-1531`; the weighted spaces are those
of `eq:st18-t00003`, lines 653–660, blueprint unit `B0008`).

**Statement.** Let `n ≥ 1`, `M > 1`, and let `w` be the radial profile of an angular-`n` element
`w(r)e^{inθ}` of `L²_M`, i.e. `‖w‖²_{L²_M} = ∫₀^∞ |w(r)|² ⟨r⟩^{2M} r dr < ∞`. Then
`Δ_n⁻¹w(r) = -(2n)⁻¹ [ r⁻ⁿ ∫₀^r s^{n+1} w(s) ds + rⁿ ∫_r^∞ s^{1-n} w(s) ds ]`
(`eq:st18-t00060`, lines 1368–1373):
* both integrals are finite for every `r > 0` (`integrable_parts`, line 1374);
* it is the Green inverse of `Δ_n = ∂_r² + r⁻¹∂_r - n²r⁻²`: `Δ_n(Δ_n⁻¹w) = w` on `(0,∞)`
  (`isDeltaNSol_greenInv` in integrated form, `deltaN_greenInv` pointwise for continuous `w`);
* for `r ≥ 2`, `|Δ_n⁻¹w(r)| ≤ C_{n,M} ‖w‖_{L²_M} (r^{1-M} + r^{-n}(1 + log r)^{1/2})`
  (`norm_greenInv_le_far`, lines 1374–1377);
* the streamfunction tends to `0` at infinity (`tendsto_greenInv_atTop`, line 1379);
* near zero it is bounded by `C r` (`norm_greenInv_le_near`, `n ≥ 2`, valid for all `r > 0`),
  with an additional `C r |log r|^{1/2}` when `n = 1` (`norm_greenInv_le_near_one`, `0 < r ≤ 1`)
  (line 1379);
* hence `Δ_n⁻¹w(r) e^{inθ}` is locally square integrable on `ℝ²` (`memLp_planeStream`, line 1379).

**Formalization choices.**
* Profiles are functions `w : ℝ → ℂ` on `(0,∞)`; `MemL2M M w` is the condition
  `∫₀^∞ |w|² ⟨r⟩^{2M} r dr < ∞` with `⟨r⟩^{2M} = (1+r²)^M` (the polar form of the `L²_M` norm
  of `w(r)e^{inθ}`, up to the factor `2π`), and `normL2M M w` is its square root.
* `greenInv` is the manuscript formula verbatim, with `r⁻ⁿ = ((r:ℂ)ⁿ)⁻¹` and
  `s^{1-n} = (s:ℂ)^{(1-n : ℤ)}`; by `integrable_parts` no junk integral value occurs at `r > 0`.
* `Δ_n ψ = w` for a profile that is only `L²_loc` is formalized in integrated form
  (`IsDeltaNSol`), exactly as `IsDelta2Sol` of unit `B0011` (`n = 2`); `IsDeltaNSol.deltaN_eq`
  shows it is the pointwise equation `DeltaN n ψ = w` when `w` is continuous.
* `(1 + log r)^{1/2}` is `√(1 + log r)`; the constants `C` are produced by the theorems, depend
  only on `n` and `M`, and multiply `‖w‖_{L²_M}`.
* `e^{inθ}` at `z = r e^{iθ} ≠ 0` is `(z/|z|)ⁿ` (`planeStream`); "locally square integrable"
  is `MemLp · 2` on every compact subset of `ℂ = ℝ²`.

The Green-operator machinery (`Psi`, `Phi`, `WProf`, the kernel `(min/max)ⁿ ρ`) is reused from
unit `B0011` (`Units/B0011/Solve.lean`, adapted from the reference formalization
`NonUniqueEuler/lean/NonUniqueEuler/H/Sec4/Sector/GreenSol.lean`); the Cauchy–Schwarz estimates
with weight `⟨s⟩^{2M} s ds` are in `Units/B0079/CauchySchwarz.lean` and `Units/B0079/Bounds.lean`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.B0079

open UnforcedLeray.B0011 (WProf Psi Phi Eps ker kL kR ker_of_le ker_of_ge)

/-! ### Definitions -/

/-- The radial profile `w` of an angular-sector element `w(r)e^{inθ}` of `L²_M`
(`paper/main.tex` line 1366, weighted space of `eq:st18-t00003`, lines 653–660): `w` is
measurable on `(0,∞)` and `∫₀^∞ |w(s)|² ⟨s⟩^{2M} s ds < ∞`, where `⟨s⟩^{2M} = (1+s²)^M`. -/
def MemL2M (M : ℝ) (w : ℝ → ℂ) : Prop :=
  AEStronglyMeasurable w (volume.restrict (Ioi 0)) ∧
    Integrable (fun s => ‖w s‖ ^ 2 * (1 + s ^ 2) ^ M * s) (volume.restrict (Ioi 0))

/-- `‖w‖_{L²_M} = (∫₀^∞ |w(s)|² ⟨s⟩^{2M} s ds)^{1/2}` (`paper/main.tex` line 1376). -/
def normL2M (M : ℝ) (w : ℝ → ℂ) : ℝ :=
  √(∫ s in Ioi (0 : ℝ), ‖w s‖ ^ 2 * (1 + s ^ 2) ^ M * s)

/-- The Green formula `eq:st18-t00060` (`paper/main.tex` lines 1368–1373):
`Δ_n⁻¹w(r) = -(2n)⁻¹ [ r⁻ⁿ ∫₀^r s^{n+1} w(s) ds + rⁿ ∫_r^∞ s^{1-n} w(s) ds ]`.
Only its values at `r > 0` are meaningful (at `r = 0` it is `0`, `greenInv_zero`). -/
def greenInv (n : ℕ) (w : ℝ → ℂ) (r : ℝ) : ℂ :=
  -(1 / (2 * (n : ℂ))) * (((r : ℂ) ^ n)⁻¹ * (∫ s in (0 : ℝ)..r, (s : ℂ) ^ (n + 1) * w s) +
    (r : ℂ) ^ n * ∫ s in Ioi r, (s : ℂ) ^ (1 - (n : ℤ)) * w s)

/-- The angular-`n` radial Laplacian `Δ_nψ = ψ'' + r⁻¹ψ' - n²r⁻²ψ`, pointwise, so that
`Δ(ψ(r)e^{inθ}) = (Δ_nψ)(r)e^{inθ}` (the operator `Δ_n` of `paper/main.tex` line 1369).
It is meaningful at `r > 0` where `ψ` is twice differentiable. -/
def DeltaN (n : ℕ) (ψ : ℝ → ℂ) (r : ℝ) : ℂ :=
  deriv (deriv ψ) r + deriv ψ r / (r : ℂ) - (n : ℂ) ^ 2 * ψ r / (r : ℂ) ^ 2

/-- `ψ` solves `Δ_nψ = w` on `(0, ∞)` in integrated form: `ψ` is differentiable on `(0,∞)` with
a continuous derivative `ψ'`, and `ψ'(b) - ψ'(a) = ∫_a^b (w - ψ'/r + n²ψ/r²) dr` for all
`a, b > 0` (`Δ_n⁻¹`, `paper/main.tex` line 1369; the `n = 2` case is `B0011.IsDelta2Sol`). -/
def IsDeltaNSol (n : ℕ) (w ψ : ℝ → ℂ) : Prop :=
  ∃ ψ' : ℝ → ℂ, (∀ r : ℝ, 0 < r → HasDerivAt ψ (ψ' r) r) ∧ ContinuousOn ψ' (Ioi 0) ∧
    ∀ a b : ℝ, 0 < a → 0 < b →
      ψ' b - ψ' a = ∫ r in a..b, (w r - ψ' r / (r : ℂ) + (n : ℂ) ^ 2 * ψ r / (r : ℂ) ^ 2)

/-- The Cartesian streamfunction `Δ_n⁻¹w(r) e^{inθ}` at `z = r e^{iθ} ∈ ℂ = ℝ²`, written with
`e^{inθ} = (z/|z|)ⁿ` (`paper/main.tex` line 1379). -/
def planeStream (n : ℕ) (w : ℝ → ℂ) (z : ℂ) : ℂ :=
  greenInv n w ‖z‖ * (z / (‖z‖ : ℂ)) ^ n

/-! ### `L²_M` profiles -/

/-- Since `M > 1`, an `L²_M` profile satisfies `r w(r) ∈ L¹(0,∞)` (Cauchy–Schwarz with weight
`⟨s⟩^{2M} s ds`), the hypothesis `WProf` of the Green-operator machinery of unit `B0011`. -/
theorem MemL2M.wprof {M : ℝ} {w : ℝ → ℂ} (hM : 1 < M) (hw : MemL2M M w) : WProf w where
  meas := hw.1
  int := by
    have h1 := (inner_near hw.1 hw.2 (by linarith) 0 one_pos).1
    have h2 := (outer_far hw.1 hw.2 hM 0 one_pos).1
    have h1' : IntegrableOn (fun s => s * ‖w s‖) (Ioc 0 1) :=
      h1.congr_fun (fun s _ => by simp) measurableSet_Ioc
    have h2' : IntegrableOn (fun s => s * ‖w s‖) (Ioi 1) :=
      h2.congr_fun (fun s _ => by simp) measurableSet_Ioi
    have h := h1'.union h2'
    rwa [Ioc_union_Ioi_eq_Ioi zero_le_one] at h

theorem normL2M_nonneg (M : ℝ) (w : ℝ → ℂ) : 0 ≤ normL2M M w := Real.sqrt_nonneg _

theorem norm_ofReal_zpow {s : ℝ} (hs : 0 < s) (n : ℕ) :
    ‖(s : ℂ) ^ (1 - (n : ℤ))‖ = s ^ (1 - (n : ℝ)) := by
  rw [norm_zpow, Complex.norm_real, Real.norm_of_nonneg hs.le, ← Real.rpow_intCast]
  push_cast
  rfl

theorem norm_ofReal_pow {s : ℝ} (hs : 0 ≤ s) (k : ℕ) : ‖(s : ℂ) ^ k‖ = s ^ k := by
  rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg hs]

/-- **Finiteness** (`paper/main.tex` line 1374): for `w ∈ L²_M`, `M > 1`, and every `r > 0`,
both integrals of `eq:st18-t00060` converge absolutely. -/
theorem integrable_parts {M : ℝ} {w : ℝ → ℂ} (hM : 1 < M) (hw : MemL2M M w) (n : ℕ) {r : ℝ}
    (hr : 0 < r) :
    IntervalIntegrable (fun s : ℝ => (s : ℂ) ^ (n + 1) * w s) volume 0 r ∧
      IntegrableOn (fun s : ℝ => (s : ℂ) ^ (1 - (n : ℤ)) * w s) (Ioi r) := by
  constructor
  · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hr.le]
    refine Integrable.mono' (inner_near hw.1 hw.2 (by linarith) n hr).1
      ((Complex.continuous_ofReal.pow _).aestronglyMeasurable.mul
        (hw.1.mono_measure (Measure.restrict_mono Ioc_subset_Ioi_self le_rfl))) ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioc fun s hs => le_of_eq ?_
    rw [norm_mul, norm_ofReal_pow hs.1.le]
  · refine Integrable.mono' (outer_far hw.1 hw.2 hM n hr).1
      (((Complex.continuous_ofReal.continuousOn.zpow₀ (1 - (n : ℤ)) fun s hs =>
        Or.inl (by exact_mod_cast (hr.trans hs).ne')).aestronglyMeasurable
          measurableSet_Ioi).mul
        (hw.1.mono_measure (Measure.restrict_mono (Ioi_subset_Ioi hr.le) le_rfl))) ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun s hs => le_of_eq ?_
    rw [norm_mul, norm_ofReal_zpow (hr.trans hs)]

/-! ### The kernel form and the equation `Δ_n(Δ_n⁻¹w) = w` -/

theorem greenInv_zero {n : ℕ} (hn : n ≠ 0) (w : ℝ → ℂ) : greenInv n w 0 = 0 := by
  simp [greenInv, zero_pow hn]

/-- For `r ≥ 0` and `r w(r) ∈ L¹(0,∞)`, the Green formula is the kernel operator
`-(2n)⁻¹ ∫₀^∞ (min(r,s)/max(r,s))ⁿ s w(s) ds` of unit `B0011` (`Psi`). -/
theorem greenInv_eq_Psi {n : ℕ} (hn : n ≠ 0) {w : ℝ → ℂ} (hw : WProf w) {r : ℝ} (hr : 0 ≤ r) :
    greenInv n w r = -(1 / (2 * (n : ℂ))) * Psi n w r := by
  rcases hr.lt_or_eq with hr | hr
  · have hint : IntegrableOn (fun ρ => (ker n r ρ : ℂ) * w ρ) (Ioi 0) :=
      hw.integrable_ker n hr.le
    have hsplit : (∫ s in Ioi (0 : ℝ), (ker n r s : ℂ) * w s) =
        (∫ ρ in Ioc 0 r, (ker n r ρ : ℂ) * w ρ) + ∫ ρ in Ioi r, (ker n r ρ : ℂ) * w ρ := by
      rw [← Ioc_union_Ioi_eq_Ioi hr.le]
      exact setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
        (hint.mono_set Ioc_subset_Ioi_self) (hint.mono_set (Ioi_subset_Ioi hr.le))
    have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    have h1 : ∫ ρ in Ioc 0 r, (ker n r ρ : ℂ) * w ρ =
        ((r : ℂ) ^ n)⁻¹ * ∫ s in (0 : ℝ)..r, (s : ℂ) ^ (n + 1) * w s := by
      rw [intervalIntegral.integral_of_le hr.le, ← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioc fun ρ hρ => ?_
      rw [ker_of_ge hρ.2, kR]
      push_cast
      have hrn : (r : ℂ) ^ n ≠ 0 := pow_ne_zero _ hr0
      rw [div_pow, pow_succ]
      field_simp
    have h2 : ∫ ρ in Ioi r, (ker n r ρ : ℂ) * w ρ =
        (r : ℂ) ^ n * ∫ s in Ioi r, (s : ℂ) ^ (1 - (n : ℤ)) * w s := by
      rw [← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi fun ρ hρ => ?_
      have hρ0 : (ρ : ℂ) ≠ 0 := by exact_mod_cast (hr.trans hρ).ne'
      rw [ker_of_le (le_of_lt hρ), kL, zpow_sub₀ hρ0, zpow_one, zpow_natCast]
      push_cast
      have hρn : (ρ : ℂ) ^ n ≠ 0 := pow_ne_zero _ hρ0
      rw [div_pow]
      field_simp
    have hk : Psi n w r = ∫ s in Ioi (0 : ℝ), (ker n r s : ℂ) * w s := rfl
    rw [hk, hsplit, h1, h2, greenInv]
  · subst hr
    rw [greenInv_zero hn]
    have h0 : Psi n w 0 = 0 := by
      have : ∀ ρ ∈ Ioi (0 : ℝ), (B0011.ker n 0 ρ : ℂ) * w ρ = 0 := fun ρ hρ => by
        have hρ' : (0 : ℝ) < ρ := hρ
        simp [B0011.ker, min_eq_left hρ'.le, zero_pow hn]
      rw [show Psi n w 0 = ∫ ρ in Ioi (0 : ℝ), (B0011.ker n 0 ρ : ℂ) * w ρ from rfl,
        setIntegral_congr_fun measurableSet_Ioi this, integral_zero]
    rw [h0, mul_zero]

/-- The kernel operator `ψ = -(2n)⁻¹ Psi n w` solves `ψ'' + ψ'/r - n²ψ/r² = w` on `(0,∞)` in
integrated form (the general-`n` version of `B0011.WProf.delta2_solution`). -/
theorem deltaN_solution_of_wprof {n : ℕ} (hn : n ≠ 0) {g : ℝ → ℂ} (h : WProf g) :
    (∀ r : ℝ, 0 < r → HasDerivAt (fun t => -(1 / (2 * (n : ℂ))) * Psi n g t)
        (-(1 / (2 * (n : ℂ))) * Phi n g r) r) ∧
      ContinuousOn (fun t => -(1 / (2 * (n : ℂ))) * Phi n g t) (Ioi 0) ∧
      ∀ a b : ℝ, 0 < a → 0 < b →
        -(1 / (2 * (n : ℂ))) * Phi n g b - -(1 / (2 * (n : ℂ))) * Phi n g a =
          ∫ r in a..b, (g r - -(1 / (2 * (n : ℂ))) * Phi n g r / (r : ℂ) +
            (n : ℂ) ^ 2 * (-(1 / (2 * (n : ℂ))) * Psi n g r) / (r : ℂ) ^ 2) := by
  set c : ℂ := 1 / (2 * (n : ℂ)) with hc
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
  have h2nc : 2 * (n : ℂ) * c = 1 := by rw [hc]; field_simp
  refine ⟨fun t ht => (h.hasDerivAt_Psi n ht).const_mul (-c), ?_, ?_⟩
  · exact continuousOn_const.mul (h.continuousOn_Phi n)
  · have key : ∀ a' b' : ℝ, 0 < a' → a' ≤ b' →
        -c * Phi n g b' - -c * Phi n g a' =
          ∫ r in a'..b', (g r - -c * Phi n g r / (r : ℂ) +
            (n : ℂ) ^ 2 * (-c * Psi n g r) / (r : ℂ) ^ 2) := by
      intro a' b' ha' hab
      have hb' : 0 < b' := ha'.trans_le hab
      have hsub : uIcc a' b' ⊆ Ioi 0 := fun r hr => lt_of_lt_of_le (lt_min ha' hb') hr.1
      have hcont : ContinuousOn (fun r : ℝ => -(-c * Phi n g r / (r : ℂ)) +
          (n : ℂ) ^ 2 * (-c * Psi n g r) / (r : ℂ) ^ 2) (uIcc a' b') := by
        have hP : ContinuousOn (Phi n g) (uIcc a' b') := (h.continuousOn_Phi n).mono hsub
        have hQ : ContinuousOn (Psi n g) (uIcc a' b') :=
          (h.continuousOn_Psi n).mono fun r hr => mem_Ici.2 (le_of_lt (hsub hr))
        have hr0 : ∀ r ∈ uIcc a' b', (r : ℂ) ≠ 0 := fun r hr => by
          exact_mod_cast (ne_of_gt (hsub hr))
        refine ContinuousOn.add (ContinuousOn.neg (ContinuousOn.div (continuousOn_const.mul hP)
          (Complex.continuous_ofReal.continuousOn) hr0)) (ContinuousOn.div
          (continuousOn_const.mul (continuousOn_const.mul hQ))
          (Complex.continuous_ofReal.continuousOn.pow 2) fun r hr => pow_ne_zero 2 (hr0 r hr))
      have hsplit : ∫ r in a'..b', (g r - -c * Phi n g r / (r : ℂ) +
            (n : ℂ) ^ 2 * (-c * Psi n g r) / (r : ℂ) ^ 2) =
          (∫ r in a'..b', g r) + ∫ r in a'..b', (-(-c * Phi n g r / (r : ℂ)) +
            (n : ℂ) ^ 2 * (-c * Psi n g r) / (r : ℂ) ^ 2) := by
        rw [← intervalIntegral.integral_add (h.intervalIntegrable ha' hb')
          (hcont.intervalIntegrable)]
        congr 1
        funext r
        ring
      have hcongr : ∫ r in a'..b', (-(-c * Phi n g r / (r : ℂ)) +
            (n : ℂ) ^ 2 * (-c * Psi n g r) / (r : ℂ) ^ 2) =
          ∫ r in a'..b', -c * Eps n g r := by
        refine intervalIntegral.integral_congr fun r hr => ?_
        have hr0 : 0 < r := hsub hr
        rw [h.Eps_eq n hr0]
        ring
      rw [hsplit, hcongr, intervalIntegral.integral_const_mul]
      have hPhi := h.Phi_sub n ha' hab
      linear_combination (-c) * hPhi + (∫ r in a'..b', g r) * h2nc
    intro a' b' ha' hb'
    rcases le_total a' b' with hab | hba
    · exact key a' b' ha' hab
    · rw [intervalIntegral.integral_symm, ← key b' a' hb' hba]
      ring

/-- **`eq:st18-t00060` is `Δ_n⁻¹`** (`paper/main.tex` lines 1366–1373): for `n ≥ 1` and
`r w(r) ∈ L¹(0,∞)`, `ψ = Δ_n⁻¹w` solves `Δ_nψ = w` on `(0,∞)` in integrated form. -/
theorem isDeltaNSol_greenInv_of_wprof {n : ℕ} (hn : n ≠ 0) {w : ℝ → ℂ} (hw : WProf w) :
    IsDeltaNSol n w (greenInv n w) := by
  obtain ⟨hd, hc, hi⟩ := deltaN_solution_of_wprof hn hw
  refine ⟨fun t => -(1 / (2 * (n : ℂ))) * Phi n w t, fun r hr => ?_, hc, fun a b ha hb => ?_⟩
  · refine (hd r hr).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hr] with t ht
    exact greenInv_eq_Psi hn hw (le_of_lt ht)
  · rw [hi a b ha hb]
    refine intervalIntegral.integral_congr fun t ht => ?_
    have : 0 < t := lt_of_lt_of_le (lt_min ha hb) ht.1
    simp only [greenInv_eq_Psi hn hw this.le]

/-- **`eq:st18-t00060` is `Δ_n⁻¹` on `L²_M`** (`paper/main.tex` lines 1366–1373): for `n ≥ 1`,
`M > 1` and `w ∈ L²_M`, `Δ_n(Δ_n⁻¹w) = w` on `(0,∞)` (integrated form). -/
theorem isDeltaNSol_greenInv {n : ℕ} (hn : 1 ≤ n) {M : ℝ} (hM : 1 < M) {w : ℝ → ℂ}
    (hw : MemL2M M w) : IsDeltaNSol n w (greenInv n w) :=
  isDeltaNSol_greenInv_of_wprof (by omega) (hw.wprof hM)

/-- For continuous `w`, an integrated solution is a classical one: `ψ` is twice differentiable
on `(0, ∞)` and `Δ_nψ = w` pointwise there. -/
theorem IsDeltaNSol.deltaN_eq {n : ℕ} {w ψ : ℝ → ℂ} (h : IsDeltaNSol n w ψ)
    (hf : ContinuousOn w (Ioi 0)) {r : ℝ} (hr : 0 < r) :
    DifferentiableAt ℝ ψ r ∧ DifferentiableAt ℝ (deriv ψ) r ∧ DeltaN n ψ r = w r := by
  obtain ⟨ψ', hd, hc, hi⟩ := h
  set hh : ℝ → ℂ := fun r => w r - ψ' r / (r : ℂ) + (n : ℂ) ^ 2 * ψ r / (r : ℂ) ^ 2 with hhh
  have hhc : ContinuousOn hh (Ioi 0) := by
    have hψcont : ContinuousOn ψ (Ioi 0) := fun r hr =>
      (hd r hr).continuousAt.continuousWithinAt
    have hr0 : ∀ r ∈ Ioi (0 : ℝ), (r : ℂ) ≠ 0 := fun r hr => by exact_mod_cast ne_of_gt hr
    exact (hf.sub (hc.div Complex.continuous_ofReal.continuousOn hr0)).add
      ((continuousOn_const.mul hψcont).div (Complex.continuous_ofReal.continuousOn.pow 2)
        fun r hr => pow_ne_zero 2 (hr0 r hr))
  have hψ'd : HasDerivAt ψ' (hh r) r := by
    have hF : HasDerivAt (fun s => ψ' r + ∫ u in r..s, hh u) (hh r) r :=
      (intervalIntegral.integral_hasDerivAt_right IntervalIntegrable.refl
        (hhc.stronglyMeasurableAtFilter isOpen_Ioi r hr)
        (hhc.continuousAt (Ioi_mem_nhds hr))).const_add _
    refine hF.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hr] with s hs
    linear_combination hi r s hr hs
  have hev : deriv ψ =ᶠ[𝓝 r] ψ' := by
    filter_upwards [Ioi_mem_nhds hr] with t ht
    exact (hd t ht).deriv
  have hdd : HasDerivAt (deriv ψ) (hh r) r := hψ'd.congr_of_eventuallyEq hev
  refine ⟨(hd r hr).differentiableAt, hdd.differentiableAt, ?_⟩
  simp only [DeltaN, hdd.deriv, (hd r hr).deriv, hhh]
  ring

/-- **`eq:st18-t00060`, classical form** (`paper/main.tex` lines 1366–1373): for `n ≥ 1`,
`M > 1`, `w ∈ L²_M` continuous on `(0,∞)`, `Δ_n⁻¹w` is twice differentiable on `(0,∞)` and
`Δ_n(Δ_n⁻¹w)(r) = w(r)` for every `r > 0`. -/
theorem deltaN_greenInv {n : ℕ} (hn : 1 ≤ n) {M : ℝ} (hM : 1 < M) {w : ℝ → ℂ}
    (hw : MemL2M M w) (hwc : ContinuousOn w (Ioi 0)) {r : ℝ} (hr : 0 < r) :
    DifferentiableAt ℝ (greenInv n w) r ∧ DifferentiableAt ℝ (deriv (greenInv n w)) r ∧
      DeltaN n (greenInv n w) r = w r :=
  (isDeltaNSol_greenInv hn hM hw).deltaN_eq hwc hr

/-! ### Pointwise bounds (`paper/main.tex` lines 1374–1379) -/

/-- The triangle inequality for `eq:st18-t00060`:
`|Δ_n⁻¹w(r)| ≤ (2n)⁻¹ (r⁻ⁿ ∫₀^r s^{n+1}|w| + rⁿ ∫_r^∞ s^{1-n}|w|)`. -/
theorem norm_greenInv_le {n : ℕ} (hn : n ≠ 0) (w : ℝ → ℂ) {r : ℝ} (hr : 0 < r) :
    ‖greenInv n w r‖ ≤ 1 / (2 * n) * ((r ^ n)⁻¹ * (∫ s in Ioc 0 r, s ^ (n + 1) * ‖w s‖) +
      r ^ n * ∫ s in Ioi r, s ^ (1 - (n : ℝ)) * ‖w s‖) := by
  have hc : ‖-(1 / (2 * (n : ℂ)))‖ = 1 / (2 * n) := by
    rw [norm_neg, norm_div, norm_one, norm_mul, Complex.norm_natCast]
    norm_num
  have hA : ‖((r : ℂ) ^ n)⁻¹ * ∫ s in (0 : ℝ)..r, (s : ℂ) ^ (n + 1) * w s‖ ≤
      (r ^ n)⁻¹ * ∫ s in Ioc 0 r, s ^ (n + 1) * ‖w s‖ := by
    rw [norm_mul, norm_inv, norm_ofReal_pow hr.le]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [intervalIntegral.integral_of_le hr.le]
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    refine setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
    rw [norm_mul, norm_ofReal_pow hs.1.le]
  have hB : ‖(r : ℂ) ^ n * ∫ s in Ioi r, (s : ℂ) ^ (1 - (n : ℤ)) * w s‖ ≤
      r ^ n * ∫ s in Ioi r, s ^ (1 - (n : ℝ)) * ‖w s‖ := by
    rw [norm_mul, norm_ofReal_pow hr.le]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
    rw [norm_mul, norm_ofReal_zpow (hr.trans hs)]
  rw [greenInv, norm_mul, hc]
  exact mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add hA hB)) (by positivity)

theorem sqrt_rpow_div {r : ℝ} (hr : 0 < r) (a K : ℝ) : √(r ^ a / K) = r ^ (a / 2) / √K := by
  rw [Real.sqrt_div (Real.rpow_nonneg hr.le a), Real.sqrt_eq_rpow, ← Real.rpow_mul hr.le,
    show a * (1 / 2) = a / 2 by ring]

theorem pow_mul_rpow {r : ℝ} (hr : 0 < r) (n : ℕ) (b : ℝ) :
    r ^ n * r ^ b = r ^ ((n : ℝ) + b) := by
  rw [← Real.rpow_natCast, ← Real.rpow_add hr]

theorem inv_pow_mul_rpow {r : ℝ} (hr : 0 < r) (n : ℕ) (b : ℝ) :
    (r ^ n)⁻¹ * r ^ b = r ^ (b - n) := by
  rw [← Real.rpow_natCast, ← Real.rpow_neg hr.le, ← Real.rpow_add hr]
  ring_nf

/-- The inner term is `O(r)` for every `r > 0`: `r⁻ⁿ ∫₀^r s^{n+1}|w| ≤ (2n+2)^{-1/2} ‖w‖ r`. -/
theorem inner_lin {n : ℕ} {M : ℝ} (hM : 1 < M) {w : ℝ → ℂ} (hw : MemL2M M w) {r : ℝ}
    (hr : 0 < r) :
    (r ^ n)⁻¹ * ∫ s in Ioc 0 r, s ^ (n + 1) * ‖w s‖ ≤
      1 / √(2 * (n : ℝ) + 2) * normL2M M w * r := by
  have h := (inner_near hw.1 hw.2 (by linarith) n hr).2
  have e : √(r ^ (2 * n + 2) / (2 * (n : ℝ) + 2)) = r ^ (n + 1) / √(2 * (n : ℝ) + 2) := by
    rw [Real.sqrt_div (pow_nonneg hr.le _), show r ^ (2 * n + 2) = (r ^ (n + 1)) ^ 2 by ring,
      Real.sqrt_sq (pow_nonneg hr.le _)]
  rw [e] at h
  have hrn : 0 < r ^ n := pow_pos hr n
  calc (r ^ n)⁻¹ * ∫ s in Ioc 0 r, s ^ (n + 1) * ‖w s‖ ≤
        (r ^ n)⁻¹ * (r ^ (n + 1) / √(2 * (n : ℝ) + 2) * normL2M M w) :=
        mul_le_mul_of_nonneg_left h (inv_nonneg.2 hrn.le)
    _ = 1 / √(2 * (n : ℝ) + 2) * normL2M M w * r := by
        rw [pow_succ]
        field_simp

/-- **Bound at infinity** (`paper/main.tex` lines 1374–1377): for `n ≥ 1` and `M > 1` there is
`C = C_{n,M}` such that for every `w ∈ L²_M` and every `r ≥ 2`,
`|Δ_n⁻¹w(r)| ≤ C ‖w‖_{L²_M} (r^{1-M} + r^{-n} (1 + log r)^{1/2})`. -/
theorem norm_greenInv_le_far {n : ℕ} (hn : 1 ≤ n) {M : ℝ} (hM : 1 < M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℝ → ℂ, MemL2M M w → ∀ r : ℝ, 2 ≤ r →
      ‖greenInv n w r‖ ≤
        C * normL2M M w * (r ^ (1 - M) + (r ^ n)⁻¹ * √(1 + Real.log r)) := by
  have hc1 : 0 ≤ 1 / √((2 : ℝ) * n + 2 - 2 * M) + 1 := by positivity
  have hc2 : 0 ≤ 1 / √((2 : ℝ) * n + 2 * M - 2) := by positivity
  refine ⟨1 / (2 * n) * ((1 / √((2 : ℝ) * n + 2 - 2 * M) + 1) +
    1 / √((2 : ℝ) * n + 2 * M - 2)), by positivity, fun w hw r hr2 => ?_⟩
  have hr : 0 < r := by linarith
  have hr1 : 1 ≤ r := by linarith
  have hN : 0 ≤ normL2M M w := normL2M_nonneg M w
  have hE : 0 ≤ r ^ (1 - M) := Real.rpow_nonneg hr.le _
  have hL : 0 ≤ (r ^ n)⁻¹ * √(1 + Real.log r) :=
    mul_nonneg (inv_nonneg.2 (pow_nonneg hr.le n)) (Real.sqrt_nonneg _)
  -- the outer term
  have hT2 : r ^ n * ∫ s in Ioi r, s ^ (1 - (n : ℝ)) * ‖w s‖ ≤
      1 / √((2 : ℝ) * n + 2 * M - 2) * normL2M M w * r ^ (1 - M) := by
    have h := (outer_far hw.1 hw.2 hM n hr).2
    have e : r ^ n * r ^ (((2 : ℝ) - 2 * n - 2 * M) / 2) = r ^ (1 - M) := by
      rw [pow_mul_rpow hr]
      congr 1
      ring
    calc r ^ n * ∫ s in Ioi r, s ^ (1 - (n : ℝ)) * ‖w s‖ ≤
          r ^ n * (√(r ^ ((2 : ℝ) - 2 * n - 2 * M) / ((2 : ℝ) * n + 2 * M - 2)) *
            normL2M M w) := mul_le_mul_of_nonneg_left h (pow_nonneg hr.le n)
      _ = 1 / √((2 : ℝ) * n + 2 * M - 2) * normL2M M w *
            (r ^ n * r ^ (((2 : ℝ) - 2 * n - 2 * M) / 2)) := by
          rw [sqrt_rpow_div hr]
          ring
      _ = _ := by rw [e]
  -- the inner term
  have hT1 : (r ^ n)⁻¹ * ∫ s in Ioc 0 r, s ^ (n + 1) * ‖w s‖ ≤
      (1 / √((2 : ℝ) * n + 2 - 2 * M) + 1) * normL2M M w *
        (r ^ (1 - M) + (r ^ n)⁻¹ * √(1 + Real.log r)) := by
    by_cases hlt : M < n + 1
    · have h := inner_far_lt hw.1 hw.2 (by linarith) hlt hr
      have e : (r ^ n)⁻¹ * r ^ (((2 : ℝ) * n + 2 - 2 * M) / 2) = r ^ (1 - M) := by
        rw [inv_pow_mul_rpow hr]
        congr 1
        ring
      have h1 : (r ^ n)⁻¹ * ∫ s in Ioc 0 r, s ^ (n + 1) * ‖w s‖ ≤
          1 / √((2 : ℝ) * n + 2 - 2 * M) * normL2M M w * r ^ (1 - M) := by
        calc (r ^ n)⁻¹ * ∫ s in Ioc 0 r, s ^ (n + 1) * ‖w s‖ ≤
              (r ^ n)⁻¹ * (√(r ^ ((2 : ℝ) * n + 2 - 2 * M) / ((2 : ℝ) * n + 2 - 2 * M)) *
                normL2M M w) := mul_le_mul_of_nonneg_left h (inv_nonneg.2 (pow_nonneg hr.le n))
          _ = 1 / √((2 : ℝ) * n + 2 - 2 * M) * normL2M M w *
                ((r ^ n)⁻¹ * r ^ (((2 : ℝ) * n + 2 - 2 * M) / 2)) := by
              rw [sqrt_rpow_div hr]
              ring
          _ = _ := by rw [e]
      have hd : 0 ≤ 1 / √((2 : ℝ) * n + 2 - 2 * M) := by positivity
      nlinarith [mul_nonneg hd hN, mul_nonneg hN hL, mul_nonneg (mul_nonneg hd hN) hL]
    · have h := inner_far_ge hw.1 hw.2 (not_lt.1 hlt) hr
      have hlog : Real.log (1 + r ^ 2) / 2 ≤ 1 + Real.log r := by
        have h1 : Real.log (1 + r ^ 2) ≤ Real.log (2 * r ^ 2) :=
          Real.log_le_log (by positivity) (by nlinarith)
        rw [Real.log_mul two_ne_zero (by positivity), Real.log_pow] at h1
        have h2 : Real.log 2 ≤ 2 - 1 := Real.log_le_sub_one_of_pos two_pos
        push_cast at h1
        linarith
      have h' : ∫ s in Ioc 0 r, s ^ (n + 1) * ‖w s‖ ≤ √(1 + Real.log r) * normL2M M w :=
        h.trans (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hlog) hN)
      have h1 : (r ^ n)⁻¹ * ∫ s in Ioc 0 r, s ^ (n + 1) * ‖w s‖ ≤
          normL2M M w * ((r ^ n)⁻¹ * √(1 + Real.log r)) := by
        calc (r ^ n)⁻¹ * ∫ s in Ioc 0 r, s ^ (n + 1) * ‖w s‖ ≤
              (r ^ n)⁻¹ * (√(1 + Real.log r) * normL2M M w) :=
              mul_le_mul_of_nonneg_left h' (inv_nonneg.2 (pow_nonneg hr.le n))
          _ = _ := by ring
      have hd : 0 ≤ 1 / √((2 : ℝ) * n + 2 - 2 * M) := by positivity
      nlinarith [mul_nonneg hd hN, mul_nonneg hN hE, mul_nonneg (mul_nonneg hd hN) hL,
        mul_nonneg (mul_nonneg hd hN) hE]
  calc ‖greenInv n w r‖ ≤ 1 / (2 * n) * ((r ^ n)⁻¹ * (∫ s in Ioc 0 r, s ^ (n + 1) * ‖w s‖) +
        r ^ n * ∫ s in Ioi r, s ^ (1 - (n : ℝ)) * ‖w s‖) := norm_greenInv_le (by omega) w hr
    _ ≤ 1 / (2 * n) * ((1 / √((2 : ℝ) * n + 2 - 2 * M) + 1) * normL2M M w *
          (r ^ (1 - M) + (r ^ n)⁻¹ * √(1 + Real.log r)) +
          1 / √((2 : ℝ) * n + 2 * M - 2) * normL2M M w *
          (r ^ (1 - M) + (r ^ n)⁻¹ * √(1 + Real.log r))) := by
        refine mul_le_mul_of_nonneg_left (add_le_add hT1 (hT2.trans ?_)) (by positivity)
        exact mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hc2 hN)
    _ = _ := by ring

/-- **Decay at infinity** (`paper/main.tex` line 1379, "the streamfunction tends to zero at
infinity"): for `n ≥ 1`, `M > 1`, `w ∈ L²_M`, `Δ_n⁻¹w(r) → 0` as `r → ∞`. -/
theorem tendsto_greenInv_atTop {n : ℕ} (hn : 1 ≤ n) {M : ℝ} (hM : 1 < M) {w : ℝ → ℂ}
    (hw : MemL2M M w) : Tendsto (greenInv n w) atTop (𝓝 0) := by
  have hwp := hw.wprof hM
  have h := (hwp.tendsto_Psi_atTop (n := n) (by omega)).const_mul (-(1 / (2 * (n : ℂ))))
  rw [mul_zero] at h
  refine h.congr' ?_
  filter_upwards [Ici_mem_atTop 0] with t ht
  exact (greenInv_eq_Psi (by omega) hwp ht).symm

/-- **Near zero, `n ≥ 2`** (`paper/main.tex` line 1379): there is `C = C_{n,M}` with
`|Δ_n⁻¹w(r)| ≤ C ‖w‖_{L²_M} r` for every `w ∈ L²_M` and every `r > 0` (in particular near zero). -/
theorem norm_greenInv_le_near {n : ℕ} (hn : 2 ≤ n) {M : ℝ} (hM : 1 < M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℝ → ℂ, MemL2M M w → ∀ r : ℝ, 0 < r →
      ‖greenInv n w r‖ ≤ C * normL2M M w * r := by
  refine ⟨1 / (2 * n) * (1 / √(2 * (n : ℝ) + 2) + 1 / √((2 : ℝ) * n - 2)), by positivity,
    fun w hw r hr => ?_⟩
  have hT1 := inner_lin (n := n) hM hw hr
  have hT2 : r ^ n * ∫ s in Ioi r, s ^ (1 - (n : ℝ)) * ‖w s‖ ≤
      1 / √((2 : ℝ) * n - 2) * normL2M M w * r := by
    have h := outer_near hw.1 hw.2 (by linarith) hn hr
    have e : r ^ n * r ^ (((2 : ℝ) - 2 * n) / 2) = r := by
      rw [pow_mul_rpow hr, show (n : ℝ) + ((2 : ℝ) - 2 * n) / 2 = 1 by ring, Real.rpow_one]
    calc r ^ n * ∫ s in Ioi r, s ^ (1 - (n : ℝ)) * ‖w s‖ ≤
          r ^ n * (√(r ^ ((2 : ℝ) - 2 * n) / ((2 : ℝ) * n - 2)) * normL2M M w) :=
          mul_le_mul_of_nonneg_left h (pow_nonneg hr.le n)
      _ = 1 / √((2 : ℝ) * n - 2) * normL2M M w * (r ^ n * r ^ (((2 : ℝ) - 2 * n) / 2)) := by
          rw [sqrt_rpow_div hr]
          ring
      _ = _ := by rw [e]
  calc ‖greenInv n w r‖ ≤ 1 / (2 * n) * ((r ^ n)⁻¹ * (∫ s in Ioc 0 r, s ^ (n + 1) * ‖w s‖) +
        r ^ n * ∫ s in Ioi r, s ^ (1 - (n : ℝ)) * ‖w s‖) := norm_greenInv_le (by omega) w hr
    _ ≤ 1 / (2 * n) * (1 / √(2 * (n : ℝ) + 2) * normL2M M w * r +
          1 / √((2 : ℝ) * n - 2) * normL2M M w * r) :=
        mul_le_mul_of_nonneg_left (add_le_add hT1 hT2) (by positivity)
    _ = _ := by ring

/-- **Near zero, `n = 1`** (`paper/main.tex` line 1379): there is `C = C_M` with
`|Δ₁⁻¹w(r)| ≤ C ‖w‖_{L²_M} (r + r |log r|^{1/2})` for every `w ∈ L²_M` and `0 < r ≤ 1`. -/
theorem norm_greenInv_le_near_one {M : ℝ} (hM : 1 < M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℝ → ℂ, MemL2M M w → ∀ r : ℝ, 0 < r → r ≤ 1 →
      ‖greenInv 1 w r‖ ≤ C * normL2M M w * (r + r * √|Real.log r|) := by
  have hc : 0 ≤ 1 / √(2 * ((1 : ℕ) : ℝ) + 2) := by positivity
  have hd : 0 ≤ √(1 / (2 * M)) := Real.sqrt_nonneg _
  refine ⟨1 / 2 * (1 / √(2 * ((1 : ℕ) : ℝ) + 2) + √(1 / (2 * M)) + 1), by positivity,
    fun w hw r hr hr1 => ?_⟩
  have hN : 0 ≤ normL2M M w := normL2M_nonneg M w
  have hT1 := inner_lin (n := 1) hM hw hr
  have habs : |Real.log r| = -Real.log r := abs_of_nonpos (Real.log_nonpos hr.le hr1)
  have hT2 : r ^ 1 * ∫ s in Ioi r, s ^ (1 - ((1 : ℕ) : ℝ)) * ‖w s‖ ≤
      (√|Real.log r| + √(1 / (2 * M))) * normL2M M w * r := by
    have h := (outer_near_one hw.1 hw.2 hM hr hr1).2
    have hcongr : ∫ s in Ioi r, s ^ (1 - ((1 : ℕ) : ℝ)) * ‖w s‖ = ∫ s in Ioi r, ‖w s‖ :=
      setIntegral_congr_fun measurableSet_Ioi fun s _ => by simp
    rw [hcongr, pow_one, habs]
    calc r * ∫ s in Ioi r, ‖w s‖ ≤
          r * ((√(-Real.log r) + √(1 / (2 * M))) * normL2M M w) :=
          mul_le_mul_of_nonneg_left h hr.le
      _ = _ := by ring
  have hS : 0 ≤ √|Real.log r| := Real.sqrt_nonneg _
  have hNr : 0 ≤ normL2M M w * r := mul_nonneg hN hr.le
  have hNrS : 0 ≤ normL2M M w * r * √|Real.log r| := mul_nonneg hNr hS
  calc ‖greenInv 1 w r‖ ≤ 1 / (2 * ((1 : ℕ) : ℝ)) *
        ((r ^ 1)⁻¹ * (∫ s in Ioc 0 r, s ^ (1 + 1) * ‖w s‖) +
          r ^ 1 * ∫ s in Ioi r, s ^ (1 - ((1 : ℕ) : ℝ)) * ‖w s‖) :=
        norm_greenInv_le one_ne_zero w hr
    _ ≤ 1 / (2 * ((1 : ℕ) : ℝ)) * (1 / √(2 * ((1 : ℕ) : ℝ) + 2) * normL2M M w * r +
          (√|Real.log r| + √(1 / (2 * M))) * normL2M M w * r) :=
        mul_le_mul_of_nonneg_left (add_le_add hT1 hT2) (by positivity)
    _ ≤ _ := by
        push_cast
        nlinarith [mul_nonneg hc hNrS, mul_nonneg hd hNrS, mul_nonneg hc hNr, mul_nonneg hd hNr]

/-! ### Local square integrability of the Cartesian streamfunction -/

/-- `Δ_n⁻¹w` is continuous on `[0, ∞)` (it is `-(2n)⁻¹ Psi n w` there, `greenInv_eq_Psi`). -/
theorem continuousOn_greenInv {n : ℕ} (hn : 1 ≤ n) {M : ℝ} (hM : 1 < M) {w : ℝ → ℂ}
    (hw : MemL2M M w) : ContinuousOn (greenInv n w) (Ici 0) := by
  have hwp := hw.wprof hM
  have h : ContinuousOn (fun r => -(1 / (2 * (n : ℂ))) * Psi n w r) (Ici 0) :=
    continuousOn_const.mul (hwp.continuousOn_Psi n)
  exact h.congr fun r hr => greenInv_eq_Psi (by omega) hwp hr

/-- **Local square integrability** (`paper/main.tex` line 1379): for `n ≥ 1`, `M > 1`,
`w ∈ L²_M`, the Cartesian streamfunction `Δ_n⁻¹w(r) e^{inθ}` is square integrable on every
compact subset of `ℝ² = ℂ`. -/
theorem memLp_planeStream {n : ℕ} (hn : 1 ≤ n) {M : ℝ} (hM : 1 < M) {w : ℝ → ℂ}
    (hw : MemL2M M w) {K : Set ℂ} (hK : IsCompact K) :
    MemLp (planeStream n w) 2 (volume.restrict K) := by
  have hψ : Continuous fun z : ℂ => greenInv n w ‖z‖ :=
    (continuousOn_greenInv hn hM hw).comp_continuous continuous_norm
      fun z => mem_Ici.2 (norm_nonneg z)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hψ.continuousOn
  have : IsFiniteMeasure (volume.restrict K) :=
    isFiniteMeasure_restrict.2 hK.measure_lt_top.ne
  refine MemLp.of_bound ?_ C ?_
  · exact hψ.aestronglyMeasurable.mul
      ((measurable_id.div (Complex.measurable_ofReal.comp measurable_norm)).pow_const
        n).aestronglyMeasurable
  · refine ae_restrict_of_forall_mem hK.measurableSet fun z hz => ?_
    have h1 : ‖(z / (‖z‖ : ℂ)) ^ n‖ ≤ 1 := by
      rw [norm_pow]
      refine pow_le_one₀ (norm_nonneg _) ?_
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg z)]
      rcases eq_or_ne ‖z‖ 0 with h | h
      · rw [h, div_zero]; exact zero_le_one
      · rw [div_self h]
    rw [planeStream, norm_mul]
    calc ‖greenInv n w ‖z‖‖ * ‖(z / (‖z‖ : ℂ)) ^ n‖ ≤ C * 1 :=
          mul_le_mul (hC z hz) h1 (norm_nonneg _) ((norm_nonneg _).trans (hC z hz))
      _ = C := mul_one C

end UnforcedLeray.B0079
