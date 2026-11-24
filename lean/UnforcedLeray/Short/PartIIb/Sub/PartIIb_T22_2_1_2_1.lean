import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_1_2

/-!


Source: `the November 2 reference manuscript`,
lines 2074-2105 (the duality argument for the free cylinder evolution; the time-dependent tests are
approximated by separated sums `Σ χ_k(r) ψ_k(x)`).

With the field `CylEtaTest.decay_r` (`Sub/T22_2.lean`) every `CylEtaTest` `φ` on `[t₀, t₁]` is a
weighted `C¹` limit (`CylTdConv`) of separated sums. Construction, for `R ≥ 1` and `K ≥ 1`:
* `η`-cut-off: `cutTest R φ r x = θ(η/R) φ(r, x)`, `θ = etaBump` (`= 1` on `[-1, 1]`, `= 0` off
  `(-2, 2)`); its slices are `IsCylTest` (`CutSliceTest`);
* age interpolation on the grid `a_k = t₀ + k h`, `h = (t₁ - t₀)/K`: with the `C^∞` partition of
  unity `pou k = σ_k - σ_{k+1}`, `σ_k(r) = smoothTransition((r - a_k)/h + 1/2)` (`σ_0 = 1`,
  `σ_K = 0`), `interp1 g r = Σ_{k<K} pou k r · (g a_k + (r - a_k)/h · (g a_{k+1} - g a_k))`;
  `sepApprox t₀ t₁ K R φ r x = interp1 (fun s => cutTest R φ s x) r` is a separated sum
  (`InterpSepSum`) and `pd j`, `lapP` commute with `interp1` (`InterpCommute`);
* scalar estimates (`Interp1D`): `|interp1 g - g| ≤ A w` and `|(interp1 g)' - g'| ≤ A w` when `g`,
  resp. `g'`, oscillates by at most `w` on scale `2h` (mean value theorem, `Σ pou k = 1`,
  `Σ |pou k'| ≤ D/h`, `PouProps`);
* the oscillation in age of `cutTest R φ`, its planar derivatives and `θ ∂_r φ` is uniformly small
  (`CutModuliPlanar`, `AgeDerivModulus`, through `UnifContBand`: joint continuity on `[t₀,t₁] × ℝ²`,
  `q`-periodicity, support in a band); so `sepApprox → cutTest R φ` uniformly (`InterpApprox`), the
  error vanishing for `|η| ≥ 3R` (`ApproxBand`);
* `cutTest R φ → φ` with weight `(1 + η²)^N` at rate `C_N/(1 + R²)` (`CutTail`: `decay` and `decay_r`
  with `N + 1`).
`cylTdApproxSums_of` is the diagonal choice `R_n = n + 1`, interpolation error
`≤ 1/((n+1)(1 + 9R_n²)^n)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal
open UnforcedLeray.Cons.C03.Concrete

namespace UnforcedLeray.Short.IIb

namespace TdSums

/-! ## Concrete objects -/

/-- The fixed bump `θ`: `θ = 1` on `[-1, 1]`, `θ = 0` off `(-2, 2)`, `0 ≤ θ ≤ 1`, `C^∞`. -/
def etaBump : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩

/-- The `η`-cut-off `θ_R(x) = θ(η/R)` on the plane (`x = (q, η)`). -/
def etaCut (R : ℝ) (x : B0579.Plane) : ℝ := etaBump (x.2 / R)

/-- The cut test `θ_R(x) φ(r, x)`. -/
def cutTest (R : ℝ) (φ : ℝ → B0579.Plane → ℝ) (r : ℝ) (x : B0579.Plane) : ℝ :=
  etaCut R x * φ r x

/-- Grid step `h = (t₁ - t₀)/K`. -/
def gridH (t₀ t₁ : ℝ) (K : ℕ) : ℝ := (t₁ - t₀) / K

/-- Grid point `a_k = t₀ + k h` (`a_0 = t₀`, `a_K = t₁` for `K ≥ 1`). -/
def gridPt (t₀ t₁ : ℝ) (K k : ℕ) : ℝ := t₀ + k * gridH t₀ t₁ K

/-- The smooth steps `σ_0 = 1`, `σ_k(r) = smoothTransition((r - a_k)/h + 1/2)` (`0 < k < K`),
`σ_k = 0` (`k ≥ K`); `σ_k = 0` for `r ≤ a_k - h/2` and `= 1` for `r ≥ a_k + h/2`. -/
def pouStep (t₀ t₁ : ℝ) (K k : ℕ) (r : ℝ) : ℝ :=
  if k = 0 then 1 else if K ≤ k then 0 else
    Real.smoothTransition ((r - gridPt t₀ t₁ K k) / gridH t₀ t₁ K + 1 / 2)

/-- The partition of unity `pou k = σ_k - σ_{k+1}` (`Σ_{k<K} pou k = 1`; `pou k` lives on
`[a_k - h/2, a_{k+1} + h/2]` inside `[t₀, t₁]`). -/
def pou (t₀ t₁ : ℝ) (K k : ℕ) (r : ℝ) : ℝ := pouStep t₀ t₁ K k r - pouStep t₀ t₁ K (k + 1) r

/-- `C¹` interpolation in age: the local linear interpolants on `[a_k, a_{k+1}]` glued by `pou`. -/
def interp1 (t₀ t₁ : ℝ) (K : ℕ) (g : ℝ → ℝ) (r : ℝ) : ℝ :=
  ∑ k ∈ Finset.range K, pou t₀ t₁ K k r *
    (g (gridPt t₀ t₁ K k) + (r - gridPt t₀ t₁ K k) / gridH t₀ t₁ K *
      (g (gridPt t₀ t₁ K (k + 1)) - g (gridPt t₀ t₁ K k)))

/-- The separated-sum approximant: age interpolation of the cut test. -/
def sepApprox (t₀ t₁ : ℝ) (K : ℕ) (R : ℝ) (φ : ℝ → B0579.Plane → ℝ) (r : ℝ)
    (x : B0579.Plane) : ℝ :=
  interp1 t₀ t₁ K (fun s => cutTest R φ s x) r

/-- The planar `C²`-type error of `CylTdConv` at a point (values, `∂_q`, `∂_η`, `Δ`). -/
def planarErr (g h : B0579.Plane → ℝ) (x : B0579.Plane) : ℝ :=
  |g x - h x| + |B0579.pd 0 g x - B0579.pd 0 h x| + |B0579.pd 1 g x - B0579.pd 1 h x| +
    |lapP g x - lapP h x|

theorem planarErr_triangle (g h k : B0579.Plane → ℝ) (x : B0579.Plane) :
    planarErr g k x ≤ planarErr g h x + planarErr h k x := by
  unfold planarErr
  have e1 := abs_sub_le (g x) (h x) (k x)
  have e2 := abs_sub_le (B0579.pd 0 g x) (B0579.pd 0 h x) (B0579.pd 0 k x)
  have e3 := abs_sub_le (B0579.pd 1 g x) (B0579.pd 1 h x) (B0579.pd 1 k x)
  have e4 := abs_sub_le (lapP g x) (lapP h x) (lapP k x)
  linarith

theorem planarErr_nonneg (g h : B0579.Plane → ℝ) (x : B0579.Plane) : 0 ≤ planarErr g h x := by
  unfold planarErr
  positivity

/-! ## Leaves -/

/-- **Leaf `/1`: the `η`-cut-off.** Smooth, between `0` and `1`, `= 1` for `|η| ≤ R`, `= 0` for
`|η| ≥ 2R`, independent of `q`; `∂_q θ_R = 0`, `∂_η θ_R`, `Δθ_R` bounded uniformly in `R ≥ 1` and
zero for `|η| < R`. -/
def EtaCutProps : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 1 ≤ R →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (etaCut R) ∧
    ∀ x : B0579.Plane,
      0 ≤ etaCut R x ∧ etaCut R x ≤ 1 ∧
      (|x.2| ≤ R → etaCut R x = 1) ∧ (2 * R ≤ |x.2| → etaCut R x = 0) ∧
      (∀ a : ℝ, etaCut R (a, x.2) = etaCut R x) ∧
      B0579.pd 0 (etaCut R) x = 0 ∧ |B0579.pd 1 (etaCut R) x| ≤ C ∧ |lapP (etaCut R) x| ≤ C ∧
      (|x.2| < R → B0579.pd 1 (etaCut R) x = 0 ∧ lapP (etaCut R) x = 0)

/-- **Leaf `/2`: cut slices are cylinder tests** (`ψ_k = θ_R φ(a_k, ·)`). -/
def CutSliceTest : Prop :=
  ∀ (c t₀ t₁ R : ℝ) (φ : ℝ → B0579.Plane → ℝ), 1 ≤ R → CylEtaTest c t₀ t₁ φ →
    ∀ r ∈ Icc t₀ t₁, B0579.IsCylTest c (cutTest R φ r)

/-- **Leaf `/3`: the partition of unity in age.** `pou k` is `C^∞`; for `K ≥ 1`,
`Σ_{k<K} pou k = 1`; for `t₀ < t₁`: `pou k ≥ 0`, `Σ_k |pou k'| ≤ D/h` (`D` absolute: at each `r`
at most one `σ_k'` is nonzero, `|σ_k'| ≤ sup|smoothTransition'|/h`), and on `[t₀, t₁]` both
`pou k` and `pou k'` vanish off `[a_k - h/2, a_{k+1} + h/2]`. -/
def PouProps : Prop :=
  (∀ (t₀ t₁ : ℝ) (K k : ℕ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (pou t₀ t₁ K k)) ∧
  (∀ (t₀ t₁ : ℝ) (K : ℕ), 0 < K → ∀ r : ℝ, ∑ k ∈ Finset.range K, pou t₀ t₁ K k r = 1) ∧
  ∃ D : ℝ, 0 ≤ D ∧ ∀ (t₀ t₁ : ℝ) (K : ℕ), t₀ < t₁ → 0 < K →
    (∀ (k : ℕ) (r : ℝ), 0 ≤ pou t₀ t₁ K k r) ∧
    (∀ r : ℝ, ∑ k ∈ Finset.range K, |deriv (pou t₀ t₁ K k) r| ≤ D / gridH t₀ t₁ K) ∧
    (∀ (k : ℕ), ∀ r ∈ Icc t₀ t₁, (pou t₀ t₁ K k r ≠ 0 ∨ deriv (pou t₀ t₁ K k) r ≠ 0) →
      gridPt t₀ t₁ K k - gridH t₀ t₁ K / 2 ≤ r ∧
        r ≤ gridPt t₀ t₁ K (k + 1) + gridH t₀ t₁ K / 2)

/-- **Leaf `/4`: scalar interpolation estimates.** `A` absolute. Value: if `g` oscillates by at
most `w` on `[t₀, t₁]` at scale `2h`, then `|interp1 g - g| ≤ A w` on `[t₀, t₁]`. Derivative: if
`g` is continuous on `[t₀, t₁]` with derivative `g'` on `(t₀, t₁)` oscillating by at most `w` at
scale `2h`, then `|(interp1 g)' - g'| ≤ A w` on `(t₀, t₁)` (mean value theorem twice;
`Σ pou k' = 0`). -/
def Interp1D : Prop :=
  ∃ A : ℝ, 0 ≤ A ∧ ∀ (t₀ t₁ : ℝ) (K : ℕ), t₀ ≤ t₁ → 0 < K →
    (∀ (g : ℝ → ℝ) (w : ℝ),
      (∀ r ∈ Icc t₀ t₁, ∀ r' ∈ Icc t₀ t₁, |r - r'| ≤ 2 * gridH t₀ t₁ K → |g r - g r'| ≤ w) →
      ∀ r ∈ Icc t₀ t₁, |interp1 t₀ t₁ K g r - g r| ≤ A * w) ∧
    (∀ (g g' : ℝ → ℝ) (w : ℝ), ContinuousOn g (Icc t₀ t₁) →
      (∀ r ∈ Ioo t₀ t₁, HasDerivAt g (g' r) r) →
      (∀ r ∈ Ioo t₀ t₁, ∀ r' ∈ Ioo t₀ t₁, |r - r'| ≤ 2 * gridH t₀ t₁ K → |g' r - g' r'| ≤ w) →
      ∀ r ∈ Ioo t₀ t₁, |deriv (interp1 t₀ t₁ K g) r - g' r| ≤ A * w)

/-- **Leaf `/5`: the approximant is a separated sum** (`2K` terms
`pou k (1 - (r - a_k)/h) · θ_R φ(a_k)` and `pou k (r - a_k)/h · θ_R φ(a_{k+1})`). -/
def InterpSepSum : Prop :=
  ∀ (c t₀ t₁ R : ℝ) (K : ℕ) (φ : ℝ → B0579.Plane → ℝ), 1 ≤ R → t₀ ≤ t₁ →
    CylEtaTest c t₀ t₁ φ → CylSepSum c t₀ t₁ (sepApprox t₀ t₁ K R φ)

/-- **Leaf `/6`: planar derivatives commute with the age interpolation** (finite linear
combinations of the `IsCylTest` slices `θ_R φ(a_k)`). -/
def InterpCommute : Prop :=
  ∀ (c t₀ t₁ R : ℝ) (K : ℕ) (φ : ℝ → B0579.Plane → ℝ), 1 ≤ R → t₀ ≤ t₁ →
    CylEtaTest c t₀ t₁ φ → ∀ (r : ℝ) (x : B0579.Plane),
      (∀ j : Fin 2, B0579.pd j (sepApprox t₀ t₁ K R φ r) x =
        interp1 t₀ t₁ K (fun s => B0579.pd j (cutTest R φ s) x) r) ∧
      lapP (sepApprox t₀ t₁ K R φ r) x = interp1 t₀ t₁ K (fun s => lapP (cutTest R φ s) x) r

/-- **Leaf `/7`: uniform continuity in age on a band.** A function jointly continuous on
`[t₀, t₁] × ℝ²`, `c`-periodic in `q` and zero for `|η| ≥ R` (for ages in `I ⊆ [t₀, t₁]`) has a
modulus of continuity in age on `I`, uniform in `x` (compactness of `[t₀,t₁] × [0,c] × [-R,R]`). -/
def UnifContBand : Prop :=
  ∀ (c t₀ t₁ R : ℝ) (I : Set ℝ) (G : ℝ → B0579.Plane → ℝ), 0 < c → I ⊆ Icc t₀ t₁ →
    ContinuousOn (fun z : ℝ × B0579.Plane => G z.1 z.2) (Icc t₀ t₁ ×ˢ univ) →
    (∀ r ∈ I, ∀ x : B0579.Plane, G r (x.1 + c, x.2) = G r x) →
    (∀ r ∈ I, ∀ x : B0579.Plane, R ≤ |x.2| → G r x = 0) →
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ r ∈ I, ∀ r' ∈ I, |r - r'| ≤ δ →
      ∀ x : B0579.Plane, |G r x - G r' x| ≤ ε

/-- **Leaf `/8`: age modulus of the cut test and its planar derivatives.** -/
def CutModuliPlanar : Prop :=
  ∀ (c t₀ t₁ R : ℝ) (φ : ℝ → B0579.Plane → ℝ), 0 < c → 1 ≤ R → CylEtaTest c t₀ t₁ φ →
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ r ∈ Icc t₀ t₁, ∀ r' ∈ Icc t₀ t₁, |r - r'| ≤ δ → ∀ x : B0579.Plane,
        |cutTest R φ r x - cutTest R φ r' x| ≤ ε ∧
        |B0579.pd 0 (cutTest R φ r) x - B0579.pd 0 (cutTest R φ r') x| ≤ ε ∧
        |B0579.pd 1 (cutTest R φ r) x - B0579.pd 1 (cutTest R φ r') x| ≤ ε ∧
        |lapP (cutTest R φ r) x - lapP (cutTest R φ r') x| ≤ ε

/-- **Leaf `/9`: age modulus of the cut age derivative** `θ_R ∂_r φ` on `(t₀, t₁)` (the age
derivative is the `(1, 0)` entry of the within-derivative of the jointly smooth `φ`, continuous on
`[t₀, t₁] × ℝ²`). -/
def AgeDerivModulus : Prop :=
  ∀ (c t₀ t₁ R : ℝ) (φ : ℝ → B0579.Plane → ℝ), 0 < c → 1 ≤ R → CylEtaTest c t₀ t₁ φ →
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ r ∈ Ioo t₀ t₁, ∀ r' ∈ Ioo t₀ t₁, |r - r'| ≤ δ → ∀ x : B0579.Plane,
        |etaCut R x * deriv (fun s => φ s x) r - etaCut R x * deriv (fun s => φ s x) r'| ≤ ε

/-- **Leaf `/10`: the interpolation error vanishes for `|η| ≥ 3R`** (every term carries `θ_R`,
which vanishes on the open set `|η| > 2R`). -/
def ApproxBand : Prop :=
  ∀ (t₀ t₁ R : ℝ) (K : ℕ) (φ : ℝ → B0579.Plane → ℝ), 1 ≤ R →
    ∀ (r : ℝ) (x : B0579.Plane), 3 * R ≤ |x.2| →
      planarErr (sepApprox t₀ t₁ K R φ r) (cutTest R φ r) x = 0 ∧
      deriv (fun s => sepApprox t₀ t₁ K R φ s x) r - etaCut R x * deriv (fun s => φ s x) r = 0

/-- **Leaf `/11`: uniform interpolation of the cut test** (from `/4`, `/6`, `/8`, `/9`: choose
`K` with `2h` below the moduli). -/
def InterpApprox : Prop :=
  ∀ (c t₀ t₁ R : ℝ) (φ : ℝ → B0579.Plane → ℝ), 0 < c → 1 ≤ R → t₀ ≤ t₁ →
    CylEtaTest c t₀ t₁ φ → ∀ ε : ℝ, 0 < ε → ∃ K : ℕ,
      (∀ r ∈ Icc t₀ t₁, ∀ x : B0579.Plane,
        planarErr (sepApprox t₀ t₁ K R φ r) (cutTest R φ r) x ≤ ε) ∧
      (∀ r ∈ Ioo t₀ t₁, ∀ x : B0579.Plane,
        |deriv (fun s => sepApprox t₀ t₁ K R φ s x) r - etaCut R x * deriv (fun s => φ s x) r| ≤ ε)

/-- **Leaf `/12`: the cut-off tail.** The weighted error of `θ_R φ` against `φ` is
`≤ C_N/(1 + R²)`: zero for `|η| < R`; for `|η| ≥ R` use `(1+η²)^N ≤ (1+η²)^(N+1)/(1+R²)`, the
product rules and `decay`, `decay_r` with `N + 1`. -/
def CutTail : Prop :=
  ∀ (c t₀ t₁ : ℝ) (φ : ℝ → B0579.Plane → ℝ), CylEtaTest c t₀ t₁ φ → ∀ N : ℝ, ∃ C : ℝ,
    ∀ R : ℝ, 1 ≤ R →
      (∀ r ∈ Icc t₀ t₁, ∀ x : B0579.Plane,
        planarErr (cutTest R φ r) (φ r) x * (1 + x.2 ^ 2) ^ N ≤ C / (1 + R ^ 2)) ∧
      (∀ r ∈ Ioo t₀ t₁, ∀ x : B0579.Plane,
        |etaCut R x * deriv (fun s => φ s x) r - deriv (fun s => φ s x) r| *
          (1 + x.2 ^ 2) ^ N ≤ C / (1 + R ^ 2))

/-! ## Diagonal assembly -/

/-- On `|η| < 3R` the weight `(1+η²)^N` is at most `(1 + 9R²)^n` once `N ≤ n`. -/
theorem weight_le_of_band {R N : ℝ} {n : ℕ} {x : B0579.Plane} (hN : N ≤ n) (hx : |x.2| < 3 * R) :
    (1 + x.2 ^ 2) ^ N ≤ (1 + 9 * R ^ 2) ^ n := by
  have h0 : 0 ≤ |x.2| := abs_nonneg _
  have hsq : x.2 ^ 2 ≤ 9 * R ^ 2 := by
    have : |x.2| ^ 2 ≤ (3 * R) ^ 2 := pow_le_pow_left₀ h0 hx.le 2
    rw [sq_abs] at this
    nlinarith
  have h1 : (1 : ℝ) ≤ 1 + x.2 ^ 2 := by nlinarith [sq_nonneg x.2]
  calc (1 + x.2 ^ 2) ^ N ≤ (1 + x.2 ^ 2) ^ (n : ℝ) := Real.rpow_le_rpow_of_exponent_le h1 hN
    _ ≤ (1 + 9 * R ^ 2) ^ (n : ℝ) :=
        Real.rpow_le_rpow (by linarith) (by linarith) (Nat.cast_nonneg n)
    _ = (1 + 9 * R ^ 2) ^ n := Real.rpow_natCast _ n

theorem cylTdApproxSums_of (hS : InterpSepSum) (hA : InterpApprox) (hB : ApproxBand)
    (hT : CutTail) : CylTdApproxSums := by
  intro c t₀ t₁ φ hc ht hφ
  have hR1 : ∀ n : ℕ, (1 : ℝ) ≤ (n : ℝ) + 1 := fun n => by
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  have hεpos : ∀ n : ℕ, 0 < 1 / (((n : ℝ) + 1) * (1 + 9 * ((n : ℝ) + 1) ^ 2) ^ n) := fun n => by
    positivity
  choose K hK using fun n : ℕ => hA c t₀ t₁ ((n : ℝ) + 1) φ hc (hR1 n) ht hφ _ (hεpos n)
  refine ⟨fun n => sepApprox t₀ t₁ (K n) ((n : ℝ) + 1) φ,
    fun n => hS c t₀ t₁ ((n : ℝ) + 1) (K n) φ (hR1 n) ht hφ, ?_⟩
  intro N ε hε
  obtain ⟨C, hC⟩ := hT c t₀ t₁ φ hφ N
  obtain ⟨n₀, hn₀⟩ := exists_nat_ge (max N (max (2 / ε) (2 * |C| / ε)))
  have hn₀N : N ≤ n₀ := le_trans (le_max_left _ _) hn₀
  have hn₀a : 2 / ε ≤ n₀ := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn₀
  have hn₀b : 2 * |C| / ε ≤ n₀ := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn₀
  refine ⟨n₀, fun n hn => ?_⟩
  have hnR : (n₀ : ℝ) ≤ n := by exact_mod_cast hn
  set R : ℝ := (n : ℝ) + 1 with hRdef
  have hR : 1 ≤ R := hR1 n
  have hRpos : 0 < R := by linarith
  -- the two small quantities
  have hsmall1 : 1 / R ≤ ε / 2 := by
    rw [div_le_div_iff₀ hRpos (by norm_num : (0 : ℝ) < 2)]
    have h2 : 2 / ε * ε = 2 := div_mul_cancel₀ 2 hε.ne'
    have hge : 2 / ε ≤ R := by rw [hRdef]; linarith
    have := mul_le_mul_of_nonneg_right hge hε.le
    linarith
  have hsmall2 : C / (1 + R ^ 2) ≤ ε / 2 := by
    have hden : 0 < 1 + R ^ 2 := by positivity
    rw [div_le_div_iff₀ hden (by norm_num : (0 : ℝ) < 2)]
    have h2 : 2 * |C| / ε * ε = 2 * |C| := div_mul_cancel₀ _ hε.ne'
    have hRR : R ≤ 1 + R ^ 2 := by nlinarith
    have hC' : C ≤ |C| := le_abs_self C
    have hge : 2 * |C| / ε ≤ R := by rw [hRdef]; linarith
    have h3 := mul_le_mul_of_nonneg_right hge hε.le
    have h4 := mul_le_mul_of_nonneg_left hRR hε.le
    linarith
  have hW : ∀ x : B0579.Plane, 0 ≤ (1 + x.2 ^ 2) ^ N := fun x =>
    Real.rpow_nonneg (by positivity) N
  -- weighted interpolation error bound, given the pointwise bounds
  have hInterp : ∀ (E : ℝ) (x : B0579.Plane), 0 ≤ E →
      E ≤ 1 / ((n + 1) * (1 + 9 * R ^ 2) ^ n) → (3 * R ≤ |x.2| → E = 0) →
      E * (1 + x.2 ^ 2) ^ N ≤ ε / 2 := by
    intro E x hE0 hE hEz
    by_cases hx : 3 * R ≤ |x.2|
    · rw [hEz hx, zero_mul]
      linarith
    · have hx' : |x.2| < 3 * R := lt_of_not_ge hx
      have hw := weight_le_of_band (n := n) (le_trans hn₀N hnR) hx'
      have hpow : 0 < (1 + 9 * R ^ 2) ^ n := by positivity
      calc E * (1 + x.2 ^ 2) ^ N ≤ (1 / ((n + 1) * (1 + 9 * R ^ 2) ^ n)) *
            (1 + 9 * R ^ 2) ^ n := mul_le_mul hE hw (hW x) (by positivity)
        _ = 1 / R := by
            have hp : (1 + 9 * R ^ 2) ^ n ≠ 0 := hpow.ne'
            have hR0 : R ≠ 0 := hRpos.ne'
            rw [← hRdef]
            field_simp
        _ ≤ ε / 2 := hsmall1
  obtain ⟨hK1, hK2⟩ := hK n
  refine ⟨fun r hr x => ?_, fun r hr x => ?_⟩
  · have htri := planarErr_triangle (sepApprox t₀ t₁ (K n) R φ r) (cutTest R φ r) (φ r) x
    have hE1 := hInterp (planarErr (sepApprox t₀ t₁ (K n) R φ r) (cutTest R φ r) x) x
      (planarErr_nonneg _ _ _) (hK1 r hr x) (fun hx => (hB t₀ t₁ R (K n) φ hR r x hx).1)
    have hE2 := (hC R hR).1 r hr x
    have hmono := mul_le_mul_of_nonneg_right htri (hW x)
    change planarErr (sepApprox t₀ t₁ (K n) R φ r) (φ r) x * (1 + x.2 ^ 2) ^ N ≤ ε
    nlinarith
  · have htri := abs_sub_le (deriv (fun s => sepApprox t₀ t₁ (K n) R φ s x) r)
      (etaCut R x * deriv (fun s => φ s x) r) (deriv (fun s => φ s x) r)
    have hE1 := hInterp |deriv (fun s => sepApprox t₀ t₁ (K n) R φ s x) r -
        etaCut R x * deriv (fun s => φ s x) r| x (abs_nonneg _) (hK2 r hr x)
      (fun hx => by rw [(hB t₀ t₁ R (K n) φ hR r x hx).2, abs_zero])
    have hE2 := (hC R hR).2 r hr x
    have hmono := mul_le_mul_of_nonneg_right htri (hW x)
    change |deriv (fun s => sepApprox t₀ t₁ (K n) R φ s x) r - deriv (fun s => φ s x) r| *
      (1 + x.2 ^ 2) ^ N ≤ ε
    nlinarith

end TdSums

end UnforcedLeray.Short.IIb
