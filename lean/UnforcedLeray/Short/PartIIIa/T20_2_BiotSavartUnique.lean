import UnforcedLeray.Short.PartIIIa.Sub.T20
import UnforcedLeray.Lib.CylinderB.Liouville
import UnforcedLeray.Lib.CylinderB.ModePairing
import UnforcedLeray.Lib.CylinderB.Tests
import UnforcedLeray.Lib.CylinderB.Dual

/-!
# Part III-a, task `PartIII-a:T20/2`: `BiotSavartUnique` (Liouville on the cylinder)

Source of record: `the November 2 reference manuscript`, lines 3230-3240
(`eq:ct-embeddings`; the velocity `K_d f` is THE Biot-Savart velocity, `Sub/T20.lean`).

## Route (no Fourier completeness is needed)

For two Biot-Savart velocities `u`, `v` of the same `f`, the difference `w = u - v` is an `L²(cell)`
field with zero weak divergence and zero weak curl (`IsBiotSavart`). Its real and imaginary parts
`a`, `b` are paired with `H^{-1}` through `ofX`, giving `D = (ofX a, ofX b)` with `curl D = 0` and
`div D = 0` (tested with `Sob.IsCylTest` functions). The cylinder Liouville theorem
`UnforcedLeray.Cyl.eq_zero_of_curl_div` (`Lib/CylinderB/Liouville.lean`, CY13) gives `D = 0`. Each
`q`-mode of `a`, `b` then vanishes (tests `cos(k_n q) ψ(η)`, `sin(k_n q) ψ(η)`, `pairC_eq`), so
`ae_eq_zero_of_qMode` gives `a = b = 0 a.e.`, hence `w = 0` and `u = v` a.e.

All helpers live in the namespace `T20_2`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa.CTE

namespace T20_2

/-! ## Identifications of cells, tests and derivatives -/

theorem cell_eq (c : ℝ) : UnforcedLeray.B0579.cell c = UnforcedLeray.Cyl.cell c := by
  unfold UnforcedLeray.B0579.cell UnforcedLeray.Cyl.cell
  rw [neg_div]

theorem cellμ_eq_B0579 (c : ℝ) :
    UnforcedLeray.Cyl.cellμ c = volume.restrict (UnforcedLeray.B0579.cell c) := by
  unfold UnforcedLeray.Cyl.cellμ
  rw [cell_eq]

theorem sob_of_B0579 {c : ℝ} {ψ : ℝ × ℝ → ℝ} (h : UnforcedLeray.B0579.IsCylTest c ψ) :
    UnforcedLeray.Sob.IsCylTest c ψ where
  smooth := h.smooth
  periodic x := by
    have e : x + ((c, 0) : ℝ × ℝ) = (x.1 + c, x.2) := by ext <;> simp
    rw [e]
    exact h.periodic x
  bounded := by
    obtain ⟨R, hR⟩ := h.band
    exact ⟨R, hR⟩

theorem B0579_of_sob {c : ℝ} {ψ : ℝ × ℝ → ℝ} (h : UnforcedLeray.Sob.IsCylTest c ψ) :
    UnforcedLeray.B0579.IsCylTest c ψ where
  smooth := h.smooth
  periodic x := by
    have e : ((x.1 + c, x.2) : ℝ × ℝ) = x + ((c, 0) : ℝ × ℝ) := by ext <;> simp
    rw [e]
    exact h.periodic x
  band := by
    obtain ⟨R, hR⟩ := h.bounded
    exact ⟨R, hR⟩

theorem pd0_eq (ψ : ℝ × ℝ → ℝ) (x : ℝ × ℝ) :
    UnforcedLeray.B0579.pd 0 ψ x = fderiv ℝ ψ x (1, 0) := rfl

theorem pd1_eq (ψ : ℝ × ℝ → ℝ) (x : ℝ × ℝ) :
    UnforcedLeray.B0579.pd 1 ψ x = fderiv ℝ ψ x (0, 1) := rfl

/-! ## The weight `ρ^0` and the `H^1` pairing -/

theorem wμ_one (c : ℝ) : UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
    (1 : UnforcedLeray.Sob.Weight (ℝ × ℝ)) = UnforcedLeray.Cyl.cellμ c := by
  rw [UnforcedLeray.Sob.wμ, UnforcedLeray.Cyl.cylinder_μ_eq]
  have : (fun x => ENNReal.ofReal ((1 : UnforcedLeray.Sob.Weight (ℝ × ℝ)) x)) = 1 := by
    funext x
    simp
  rw [this, withDensity_one]

theorem wμ_rho0 (c : ℝ) : UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
    (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) = UnforcedLeray.Cyl.cellμ c := by
  rw [UnforcedLeray.Sob.wμ, UnforcedLeray.Cyl.cylinder_μ_eq]
  have : (fun x => ENNReal.ofReal ((UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) x)) = 1 := by
    funext x
    simp
  rw [this, withDensity_one]

/-- Transport an a.e. statement along an equality of measures. -/
theorem ae_eq_of_measure_eq {μ ν : Measure (ℝ × ℝ)} {f g : ℝ × ℝ → ℝ} (h : μ = ν)
    (hfg : f =ᵐ[μ] g) : f =ᵐ[ν] g := by
  subst h
  exact hfg

/-- The `H^1` element of a cylinder test has value the test itself (`ρ^0 = 1`). -/
theorem value_testH {c : ℝ} (hc : 0 < c) {φ : ℝ × ℝ → ℝ}
    (hφ : UnforcedLeray.Sob.IsCylTest c φ) :
    (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
        ((UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)).inv) ℝ ℝ 1 2
        (UnforcedLeray.Cyl.testH hc hφ ((UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)).inv) 1) :
          ℝ × ℝ → ℝ) =ᵐ[UnforcedLeray.Cyl.cellμ c] φ := by
  refine ae_eq_of_measure_eq (UnforcedLeray.Cyl.wμ_ρwW_zero_inv c) ?_
  unfold UnforcedLeray.Cyl.testH
  rw [UnforcedLeray.Sob.W.value_ofFields]
  refine (MemLp.coeFn_toLp _).trans ?_
  simp only [UnforcedLeray.Cyl.word_zero, UnforcedLeray.Sob.iterDirDeriv_nil]
  exact Filter.EventuallyEq.rfl

/-- `ofX` of a test element of `H^1` is the `L²` pairing with the test function. -/
theorem ofX_testH {c : ℝ} (hc : 0 < c) {φ : ℝ × ℝ → ℝ}
    (hφ : UnforcedLeray.Sob.IsCylTest c φ)
    (A : UnforcedLeray.Cyl.XR c 0) {a : ℝ × ℝ → ℝ}
    (hA : (A : ℝ × ℝ → ℝ) =ᵐ[UnforcedLeray.Cyl.cellμ c] a) :
    UnforcedLeray.Cyl.ofX c 0 1 A
        (UnforcedLeray.Cyl.testH hc hφ ((UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)).inv) 1) =
      ∫ z in UnforcedLeray.Cyl.cell c, φ z * a z := by
  have hμ : (UnforcedLeray.Sob.cylinder c).μ = UnforcedLeray.Cyl.cellμ c :=
    UnforcedLeray.Cyl.cylinder_μ_eq c
  rw [UnforcedLeray.Cyl.ofX_apply]
  refine (integral_congr_ae ?_).trans (congrArg (fun μ => ∫ x, φ x * a x ∂μ) hμ)
  filter_upwards [ae_eq_of_measure_eq hμ.symm (value_testH hc hφ),
    ae_eq_of_measure_eq hμ.symm hA] with x h1 h2
  rw [h1, h2]

/-! ## Complex integrability against cylinder tests -/

/-- A cylinder test times a complex `L²(cell)` field is integrable on the cell. -/
theorem integrableOn_test_mul_C {c : ℝ} {φ : ℝ × ℝ → ℝ}
    (hφ : UnforcedLeray.Sob.IsCylTest c φ) {g : ℝ × ℝ → ℂ}
    (hg : MemLp g 2 (UnforcedLeray.Cyl.cellμ c)) :
    IntegrableOn (fun z => g z * (φ z : ℂ)) (UnforcedLeray.Cyl.cell c) := by
  have hg' : MemLp g 2 (UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
      (1 : UnforcedLeray.Sob.Weight (ℝ × ℝ))) := by
    rw [wμ_one]
    exact hg
  have h := UnforcedLeray.Sob.integrable_smul_of_memLp (p := 2)
    (UnforcedLeray.Sob.CompactlyBounded.of_adm (D := UnforcedLeray.Sob.cylinder c) hφ) hg'
  rw [UnforcedLeray.Cyl.cylinder_μ_eq] at h
  refine h.congr (Filter.Eventually.of_forall fun z => ?_)
  simp only [Complex.real_smul, mul_comm]

/-- Real and imaginary parts of an integrable complex integral. -/
theorem integral_re_im {s : Set (ℝ × ℝ)} {F : ℝ × ℝ → ℂ} (hF : IntegrableOn F s)
    (h : ∫ z in s, F z = 0) :
    (∫ z in s, (F z).re = 0) ∧ (∫ z in s, (F z).im = 0) := by
  constructor
  · have h1 := integral_re hF
    rw [h] at h1
    simpa using h1
  · have h1 := integral_im hF
    rw [h] at h1
    simpa using h1

/-! ## Mode vanishing and the real Liouville step -/

/-- From the vanishing of the `cos`/`sin` pairings of a real `L²(cell)` function with all
one-dimensional tests, the function vanishes a.e. -/
theorem ae_zero_of_pairings {c : ℝ} (hc : 0 < c) {a : ℝ × ℝ → ℝ}
    (ha : MemLp a 2 (UnforcedLeray.Cyl.cellμ c))
    (h : ∀ (n : ℤ) (ψ : ℝ → ℝ), UnforcedLeray.Cyl.OneD.Test ψ →
      (∫ z in UnforcedLeray.Cyl.cell c,
          UnforcedLeray.Cyl.cosTest (UnforcedLeray.Cyl.freq c n) ψ z * a z = 0 ∧
        ∫ z in UnforcedLeray.Cyl.cell c,
          UnforcedLeray.Cyl.sinTest (UnforcedLeray.Cyl.freq c n) ψ z * a z = 0)) :
    a =ᵐ[UnforcedLeray.Cyl.cellμ c] 0 := by
  have hA : MemLp (fun z => (a z : ℂ)) 2 (UnforcedLeray.Cyl.cellμ c) := ha.ofReal
  have hq : ∀ n : ℤ, UnforcedLeray.Cyl.qMode c hc n (fun z => (a z : ℂ)) =ᵐ[volume] 0 := by
    intro n
    refine ae_eq_zero_of_integral_contDiff_smul_eq_zero
      ((UnforcedLeray.Cyl.memLp_qMode hc n hA).locallyIntegrable one_le_two) ?_
    intro g hg hgc
    have hψ : UnforcedLeray.Cyl.OneD.Test g := ⟨hg, hgc⟩
    have h1 := UnforcedLeray.Cyl.pairC_eq hc n ha hψ
    have h2 : UnforcedLeray.Cyl.pairC c n a g = 0 := by
      unfold UnforcedLeray.Cyl.pairC
      rw [(h n g hψ).1, (h n g hψ).2]
      simp
    rw [h2] at h1
    have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
    exact (mul_eq_zero.mp h1.symm).resolve_left hc0
  filter_upwards [UnforcedLeray.Cyl.ae_eq_zero_of_qMode hc hA hq] with z hz
  simpa using hz

/-- **Real Liouville step.** Real `L²(cell)` functions `a`, `b` with zero weak curl and zero weak
divergence (tested with cylinder tests) vanish a.e. -/
theorem liouville_real {c : ℝ} (hc : 0 < c) {a b : ℝ × ℝ → ℝ}
    (ha : MemLp a 2 (UnforcedLeray.Cyl.cellμ c)) (hb : MemLp b 2 (UnforcedLeray.Cyl.cellμ c))
    (hcurl : ∀ φ : ℝ × ℝ → ℝ, UnforcedLeray.Sob.IsCylTest c φ →
      ∫ z in UnforcedLeray.Cyl.cell c, (fderiv ℝ φ z (0, 1) * a z - fderiv ℝ φ z (1, 0) * b z) = 0)
    (hdiv : ∀ φ : ℝ × ℝ → ℝ, UnforcedLeray.Sob.IsCylTest c φ →
      ∫ z in UnforcedLeray.Cyl.cell c, (fderiv ℝ φ z (1, 0) * a z + fderiv ℝ φ z (0, 1) * b z) = 0) :
    a =ᵐ[UnforcedLeray.Cyl.cellμ c] 0 ∧ b =ᵐ[UnforcedLeray.Cyl.cellμ c] 0 := by
  have ha' : MemLp a 2 (UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))) := by
    rw [wμ_rho0]
    exact ha
  have hb' : MemLp b 2 (UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))) := by
    rw [wμ_rho0]
    exact hb
  obtain ⟨A, hA⟩ : ∃ A : UnforcedLeray.Cyl.XR c 0,
      (A : ℝ × ℝ → ℝ) =ᵐ[UnforcedLeray.Cyl.cellμ c] a :=
    ⟨ha'.toLp a, ae_eq_of_measure_eq (wμ_rho0 c) (MemLp.coeFn_toLp ha')⟩
  obtain ⟨B, hB⟩ : ∃ B : UnforcedLeray.Cyl.XR c 0,
      (B : ℝ × ℝ → ℝ) =ᵐ[UnforcedLeray.Cyl.cellμ c] b :=
    ⟨hb'.toLp b, ae_eq_of_measure_eq (wμ_rho0 c) (MemLp.coeFn_toLp hb')⟩
  -- the cylinder Liouville theorem (CY13) gives `D = 0`
  have hD : (UnforcedLeray.Cyl.ofX c 0 1 A, UnforcedLeray.Cyl.ofX c 0 1 B) = 0 := by
    refine UnforcedLeray.Cyl.eq_zero_of_curl_div hc _ ?_ ?_
    · intro φ hφ
      dsimp only
      rw [ofX_testH hc (hφ.dirDeriv (0, 1)) A hA, ofX_testH hc (hφ.dirDeriv (1, 0)) B hB]
      rw [← integral_sub (UnforcedLeray.Cyl.integrableOn_test_mul (hφ.dirDeriv (0, 1)) ha)
        (UnforcedLeray.Cyl.integrableOn_test_mul (hφ.dirDeriv (1, 0)) hb)]
      exact hcurl φ hφ
    · intro φ hφ
      dsimp only
      rw [ofX_testH hc (hφ.dirDeriv (1, 0)) A hA, ofX_testH hc (hφ.dirDeriv (0, 1)) B hB]
      rw [← integral_add (UnforcedLeray.Cyl.integrableOn_test_mul (hφ.dirDeriv (1, 0)) ha)
        (UnforcedLeray.Cyl.integrableOn_test_mul (hφ.dirDeriv (0, 1)) hb)]
      exact hdiv φ hφ
  have h1 : UnforcedLeray.Cyl.ofX c 0 1 A = 0 := by
    have := congrArg Prod.fst hD
    simpa using this
  have h2 : UnforcedLeray.Cyl.ofX c 0 1 B = 0 := by
    have := congrArg Prod.snd hD
    simpa using this
  have hpa : ∀ (n : ℤ) (ψ : ℝ → ℝ), UnforcedLeray.Cyl.OneD.Test ψ →
      (∫ z in UnforcedLeray.Cyl.cell c,
          UnforcedLeray.Cyl.cosTest (UnforcedLeray.Cyl.freq c n) ψ z * a z = 0 ∧
        ∫ z in UnforcedLeray.Cyl.cell c,
          UnforcedLeray.Cyl.sinTest (UnforcedLeray.Cyl.freq c n) ψ z * a z = 0) := by
    intro n ψ hψ
    constructor
    · rw [← ofX_testH hc (UnforcedLeray.Cyl.isCylTest_cosTest hc n hψ) A hA, h1]
      simp
    · rw [← ofX_testH hc (UnforcedLeray.Cyl.isCylTest_sinTest hc n hψ) A hA, h1]
      simp
  have hpb : ∀ (n : ℤ) (ψ : ℝ → ℝ), UnforcedLeray.Cyl.OneD.Test ψ →
      (∫ z in UnforcedLeray.Cyl.cell c,
          UnforcedLeray.Cyl.cosTest (UnforcedLeray.Cyl.freq c n) ψ z * b z = 0 ∧
        ∫ z in UnforcedLeray.Cyl.cell c,
          UnforcedLeray.Cyl.sinTest (UnforcedLeray.Cyl.freq c n) ψ z * b z = 0) := by
    intro n ψ hψ
    constructor
    · rw [← ofX_testH hc (UnforcedLeray.Cyl.isCylTest_cosTest hc n hψ) B hB, h2]
      simp
    · rw [← ofX_testH hc (UnforcedLeray.Cyl.isCylTest_sinTest hc n hψ) B hB, h2]
      simp
  exact ⟨ae_zero_of_pairings hc ha hpa, ae_zero_of_pairings hc hb hpb⟩

/-! ## The complex difference of two Biot-Savart fields -/

/-- A complex `L²(cell)` field `w = (w_q, w_η)` with zero weak divergence and zero weak curl
vanishes a.e. -/
theorem biot_re {c : ℝ} (hc : 0 < c) (w : ℝ × ℝ → Fin 2 → ℂ)
    (hw : ∀ j, MemLp (fun z => w z j) 2 (UnforcedLeray.Cyl.cellμ c))
    (hdiv : ∀ ψ : ℝ × ℝ → ℝ, UnforcedLeray.Sob.IsCylTest c ψ →
      ∫ z in UnforcedLeray.Cyl.cell c,
        (w z 0 * (fderiv ℝ ψ z (1, 0) : ℂ) + w z 1 * (fderiv ℝ ψ z (0, 1) : ℂ)) = 0)
    (hcurl : ∀ ψ : ℝ × ℝ → ℝ, UnforcedLeray.Sob.IsCylTest c ψ →
      ∫ z in UnforcedLeray.Cyl.cell c,
        (w z 0 * (fderiv ℝ ψ z (0, 1) : ℂ) - w z 1 * (fderiv ℝ ψ z (1, 0) : ℂ)) = 0) :
    ∀ᵐ z ∂(UnforcedLeray.Cyl.cellμ c), w z = 0 := by
  have Idiv : ∀ ψ : ℝ × ℝ → ℝ, UnforcedLeray.Sob.IsCylTest c ψ →
      IntegrableOn (fun z => w z 0 * (fderiv ℝ ψ z (1, 0) : ℂ) +
        w z 1 * (fderiv ℝ ψ z (0, 1) : ℂ)) (UnforcedLeray.Cyl.cell c) := by
    intro ψ hψ
    exact (integrableOn_test_mul_C (hψ.dirDeriv (1, 0)) (hw 0)).add
      (integrableOn_test_mul_C (hψ.dirDeriv (0, 1)) (hw 1))
  have Icurl : ∀ ψ : ℝ × ℝ → ℝ, UnforcedLeray.Sob.IsCylTest c ψ →
      IntegrableOn (fun z => w z 0 * (fderiv ℝ ψ z (0, 1) : ℂ) -
        w z 1 * (fderiv ℝ ψ z (1, 0) : ℂ)) (UnforcedLeray.Cyl.cell c) := by
    intro ψ hψ
    exact (integrableOn_test_mul_C (hψ.dirDeriv (0, 1)) (hw 0)).sub
      (integrableOn_test_mul_C (hψ.dirDeriv (1, 0)) (hw 1))
  -- real and imaginary parts of the two identities
  have e_div : ∀ (ψ : ℝ × ℝ → ℝ) (z : ℝ × ℝ),
      (w z 0 * (fderiv ℝ ψ z (1, 0) : ℂ) + w z 1 * (fderiv ℝ ψ z (0, 1) : ℂ)).re =
        fderiv ℝ ψ z (1, 0) * (w z 0).re + fderiv ℝ ψ z (0, 1) * (w z 1).re := by
    intro ψ z
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      sub_zero]
    ring
  have e_div' : ∀ (ψ : ℝ × ℝ → ℝ) (z : ℝ × ℝ),
      (w z 0 * (fderiv ℝ ψ z (1, 0) : ℂ) + w z 1 * (fderiv ℝ ψ z (0, 1) : ℂ)).im =
        fderiv ℝ ψ z (1, 0) * (w z 0).im + fderiv ℝ ψ z (0, 1) * (w z 1).im := by
    intro ψ z
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      zero_add]
    ring
  have e_curl : ∀ (ψ : ℝ × ℝ → ℝ) (z : ℝ × ℝ),
      (w z 0 * (fderiv ℝ ψ z (0, 1) : ℂ) - w z 1 * (fderiv ℝ ψ z (1, 0) : ℂ)).re =
        fderiv ℝ ψ z (0, 1) * (w z 0).re - fderiv ℝ ψ z (1, 0) * (w z 1).re := by
    intro ψ z
    simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      sub_zero]
    ring
  have e_curl' : ∀ (ψ : ℝ × ℝ → ℝ) (z : ℝ × ℝ),
      (w z 0 * (fderiv ℝ ψ z (0, 1) : ℂ) - w z 1 * (fderiv ℝ ψ z (1, 0) : ℂ)).im =
        fderiv ℝ ψ z (0, 1) * (w z 0).im - fderiv ℝ ψ z (1, 0) * (w z 1).im := by
    intro ψ z
    simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      zero_add]
    ring
  have rdiv : ∀ ψ : ℝ × ℝ → ℝ, UnforcedLeray.Sob.IsCylTest c ψ →
      ∫ z in UnforcedLeray.Cyl.cell c,
        (fderiv ℝ ψ z (1, 0) * (w z 0).re + fderiv ℝ ψ z (0, 1) * (w z 1).re) = 0 := by
    intro ψ hψ
    have h := (integral_re_im (Idiv ψ hψ) (hdiv ψ hψ)).1
    simpa only [e_div] using h
  have idiv : ∀ ψ : ℝ × ℝ → ℝ, UnforcedLeray.Sob.IsCylTest c ψ →
      ∫ z in UnforcedLeray.Cyl.cell c,
        (fderiv ℝ ψ z (1, 0) * (w z 0).im + fderiv ℝ ψ z (0, 1) * (w z 1).im) = 0 := by
    intro ψ hψ
    have h := (integral_re_im (Idiv ψ hψ) (hdiv ψ hψ)).2
    simpa only [e_div'] using h
  have rcurl : ∀ ψ : ℝ × ℝ → ℝ, UnforcedLeray.Sob.IsCylTest c ψ →
      ∫ z in UnforcedLeray.Cyl.cell c,
        (fderiv ℝ ψ z (0, 1) * (w z 0).re - fderiv ℝ ψ z (1, 0) * (w z 1).re) = 0 := by
    intro ψ hψ
    have h := (integral_re_im (Icurl ψ hψ) (hcurl ψ hψ)).1
    simpa only [e_curl] using h
  have icurl : ∀ ψ : ℝ × ℝ → ℝ, UnforcedLeray.Sob.IsCylTest c ψ →
      ∫ z in UnforcedLeray.Cyl.cell c,
        (fderiv ℝ ψ z (0, 1) * (w z 0).im - fderiv ℝ ψ z (1, 0) * (w z 1).im) = 0 := by
    intro ψ hψ
    have h := (integral_re_im (Icurl ψ hψ) (hcurl ψ hψ)).2
    simpa only [e_curl'] using h
  obtain ⟨hr0, hr1⟩ := liouville_real hc (a := fun z => (w z 0).re) (b := fun z => (w z 1).re)
    (hw 0).re (hw 1).re rcurl rdiv
  obtain ⟨hi0, hi1⟩ := liouville_real hc (a := fun z => (w z 0).im) (b := fun z => (w z 1).im)
    (hw 0).im (hw 1).im icurl idiv
  filter_upwards [hr0, hr1, hi0, hi1] with z e1 e2 e3 e4
  have h0 : w z 0 = 0 := Complex.ext (by simpa using e1) (by simpa using e3)
  have h1 : w z 1 = 0 := Complex.ext (by simpa using e2) (by simpa using e4)
  funext j
  fin_cases j
  exacts [h0, h1]

end T20_2

/-- **`BiotSavartUnique`** (SP 3230-3240): two `L²` Biot-Savart velocities of the same zero
circulation datum agree a.e. on the cell. -/
theorem isBiotSavart_unique : UnforcedLeray.Short.IIIa.CTE.BiotSavartUnique := by
  unfold UnforcedLeray.Short.IIIa.CTE.BiotSavartUnique
  intro d hd f u v hu hv
  obtain ⟨hu1, hu2, hu3⟩ := hu
  obtain ⟨hv1, hv2, hv3⟩ := hv
  have hc : 0 < d := hd
  have hu1' : ∀ j, MemLp (fun z => u z j) 2 (UnforcedLeray.Cyl.cellμ d) := fun j => by
    rw [T20_2.cellμ_eq_B0579]
    exact hu1 j
  have hv1' : ∀ j, MemLp (fun z => v z j) 2 (UnforcedLeray.Cyl.cellμ d) := fun j => by
    rw [T20_2.cellμ_eq_B0579]
    exact hv1 j
  -- weak divergence of `u - v`
  have hdiv : ∀ ψ : ℝ × ℝ → ℝ, UnforcedLeray.Sob.IsCylTest d ψ →
      ∫ z in UnforcedLeray.Cyl.cell d,
        ((u z - v z) 0 * (fderiv ℝ ψ z (1, 0) : ℂ) + (u z - v z) 1 * (fderiv ℝ ψ z (0, 1) : ℂ))
        = 0 := by
    intro ψ hψ
    have hψB := T20_2.B0579_of_sob hψ
    have eu := hu2 ψ hψB
    have ev := hv2 ψ hψB
    rw [T20_2.cell_eq] at eu ev
    simp only [T20_2.pd0_eq, T20_2.pd1_eq] at eu ev
    have I1 := T20_2.integrableOn_test_mul_C (hψ.dirDeriv (1, 0)) (hu1' 0)
    have I2 := T20_2.integrableOn_test_mul_C (hψ.dirDeriv (0, 1)) (hu1' 1)
    have J1 := T20_2.integrableOn_test_mul_C (hψ.dirDeriv (1, 0)) (hv1' 0)
    have J2 := T20_2.integrableOn_test_mul_C (hψ.dirDeriv (0, 1)) (hv1' 1)
    have I : IntegrableOn (fun z => u z 0 * (fderiv ℝ ψ z (1, 0) : ℂ) +
        u z 1 * (fderiv ℝ ψ z (0, 1) : ℂ)) (UnforcedLeray.Cyl.cell d) := I1.add I2
    have J : IntegrableOn (fun z => v z 0 * (fderiv ℝ ψ z (1, 0) : ℂ) +
        v z 1 * (fderiv ℝ ψ z (0, 1) : ℂ)) (UnforcedLeray.Cyl.cell d) := J1.add J2
    have key : ∫ z in UnforcedLeray.Cyl.cell d,
        ((u z - v z) 0 * (fderiv ℝ ψ z (1, 0) : ℂ) + (u z - v z) 1 * (fderiv ℝ ψ z (0, 1) : ℂ))
        = (∫ z in UnforcedLeray.Cyl.cell d,
            (u z 0 * (fderiv ℝ ψ z (1, 0) : ℂ) + u z 1 * (fderiv ℝ ψ z (0, 1) : ℂ)))
          - ∫ z in UnforcedLeray.Cyl.cell d,
            (v z 0 * (fderiv ℝ ψ z (1, 0) : ℂ) + v z 1 * (fderiv ℝ ψ z (0, 1) : ℂ)) := by
      rw [← integral_sub I J]
      congr 1
      funext z
      simp only [Pi.sub_apply]
      ring
    rw [key, eu, ev, sub_zero]
  -- weak curl of `u - v`
  have hcurl : ∀ ψ : ℝ × ℝ → ℝ, UnforcedLeray.Sob.IsCylTest d ψ →
      ∫ z in UnforcedLeray.Cyl.cell d,
        ((u z - v z) 0 * (fderiv ℝ ψ z (0, 1) : ℂ) - (u z - v z) 1 * (fderiv ℝ ψ z (1, 0) : ℂ))
        = 0 := by
    intro ψ hψ
    have hψB := T20_2.B0579_of_sob hψ
    have eu := hu3 ψ hψB
    have ev := hv3 ψ hψB
    rw [T20_2.cell_eq] at eu ev
    simp only [T20_2.pd0_eq, T20_2.pd1_eq] at eu ev
    have I1 := T20_2.integrableOn_test_mul_C (hψ.dirDeriv (0, 1)) (hu1' 0)
    have I2 := T20_2.integrableOn_test_mul_C (hψ.dirDeriv (1, 0)) (hu1' 1)
    have J1 := T20_2.integrableOn_test_mul_C (hψ.dirDeriv (0, 1)) (hv1' 0)
    have J2 := T20_2.integrableOn_test_mul_C (hψ.dirDeriv (1, 0)) (hv1' 1)
    have I : IntegrableOn (fun z => u z 0 * (fderiv ℝ ψ z (0, 1) : ℂ) -
        u z 1 * (fderiv ℝ ψ z (1, 0) : ℂ)) (UnforcedLeray.Cyl.cell d) := I1.sub I2
    have J : IntegrableOn (fun z => v z 0 * (fderiv ℝ ψ z (0, 1) : ℂ) -
        v z 1 * (fderiv ℝ ψ z (1, 0) : ℂ)) (UnforcedLeray.Cyl.cell d) := J1.sub J2
    have key : ∫ z in UnforcedLeray.Cyl.cell d,
        ((u z - v z) 0 * (fderiv ℝ ψ z (0, 1) : ℂ) - (u z - v z) 1 * (fderiv ℝ ψ z (1, 0) : ℂ))
        = (∫ z in UnforcedLeray.Cyl.cell d,
            (u z 0 * (fderiv ℝ ψ z (0, 1) : ℂ) - u z 1 * (fderiv ℝ ψ z (1, 0) : ℂ)))
          - ∫ z in UnforcedLeray.Cyl.cell d,
            (v z 0 * (fderiv ℝ ψ z (0, 1) : ℂ) - v z 1 * (fderiv ℝ ψ z (1, 0) : ℂ)) := by
      rw [← integral_sub I J]
      congr 1
      funext z
      simp only [Pi.sub_apply]
      ring
    rw [key, ← eu, ← ev, sub_self]
  have key_w := T20_2.biot_re hc (fun z => u z - v z)
    (fun j => (hu1' j).sub (hv1' j)) hdiv hcurl
  rw [T20_2.cellμ_eq_B0579] at key_w
  filter_upwards [key_w] with z hz
  exact sub_eq_zero.mp hz

end UnforcedLeray.Short.IIIa.CTE
