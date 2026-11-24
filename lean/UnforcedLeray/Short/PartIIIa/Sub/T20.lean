import UnforcedLeray.Short.PartIIIa.CanonicalTransfer
import UnforcedLeray.Units.B0583

/-!
# Part III-a, task `PartIII-a:T20`: `ctEmbeddings` (conditional)

Source of record: `the November 2 reference manuscript`, lines 3230-3240
(`eq:ct-embeddings`): for `d ≥ 1` and `f` in the centrally even zero-circulation class `X_{m,d}`
(`m > 8`),
`|Q_d f| + ‖K_d f‖₂ ≤ C_m ‖f‖_{X_{m,d}}`, `Q_d f = -(2/π) ∫ η² f`, uniformly in `d`.
"The moment bound is weighted Cauchy-Schwarz. For velocity, zero mass gives
`|f̂(ξ)| ≤ |ξ| ∫|y||f|` at low cylindrical frequencies. In Plancherel, the `O(d)` horizontal
frequencies of modulus at most one cancel the measure factor `d⁻¹`; the high frequencies are
bounded by `‖f‖₂`."

Target (`CanonicalTransfer.lean`, unchanged): `CTEmbeddings`.

## Mathematical proof (assembly, proved here)

`ctEmbeddings_of`: from `QuadQBound` (the moment bound), `BiotSavartUnique` (the `L²` Biot-Savart
velocity of `f` is unique) and `BiotSavartExistsUniform` (a `d`-uniformly bounded Biot-Savart
velocity exists). Given any `u` with `IsBiotSavart d f u`, uniqueness identifies `u` a.e. with the
constructed velocity, so `velNorm d u` equals the constructed norm; the constant is
`max C₁ 0 + max C₃ 0`.

## Leaf lemmas (queued as `PartIII-a:T20/1 ... /7`)

* `QuadQBound` (`/1`): weighted Cauchy-Schwarz, `m > 3`.
* `BiotSavartUnique` (`/2`): Liouville on the cylinder (no nonzero `L²` field with `div = curl = 0`).
* `NonzeroVelUniform` (`/3`): `d`-uniform bound of the nonzero-mode velocity `B0581.velNe`
  (the genuine Fourier estimate: first-moment bound at the `O(d)` low horizontal modes,
  `‖bsSym‖ ≤ 1` on the others).
* `VelocityIsBiotSavart` (`/4`): the library velocity `B0583.velocity` of a real vorticity solves
  `IsBiotSavart` (`div = 0` and `curl = ω`, from the weak gradients `velGradQ`, `velGradEta`).
* `VelNormEqLp` (`/5`): `velNorm` of an `L²` vector field equals the `Lp` norm.
* `RealBiotSavartUniform` (`/6`): the real case of `BiotSavartExistsUniform`, from `/3`, `/4`, `/5`
  and `B0583.norm_zeroVelLp_le` (zero mode, Hardy, uniform in `c`).
* `BiotSavartExistsUniform` (`/7`): the complex case from the real case by `f = Re f + i Im f`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

namespace CTE

/-- **Moment bound** (SP 3230-3236, "weighted Cauchy-Schwarz"): for `m > 3`,
`|Q_d f| ≤ C ‖f‖_{X_{m,d}}` for every `d` and every `f` in `L²(cellMeasure d m)`. The constant
is uniform in `d` because `∫_{ℝ²} η⁴ ⟨x⟩^{-2m} dx < ∞` for `m > 3` and the cell is a subset of
the plane. -/
def QuadQBound : Prop :=
  ∀ m : ℝ, 3 < m → ∃ C : ℝ, ∀ (d : ℝ) (f : ℝ × ℝ → ℂ), MemLp f 2 (B0579.cellMeasure d m) →
    ENNReal.ofReal ‖quadQ d f‖ ≤ ENNReal.ofReal C * xNorm d m f

/-- **Uniqueness of the Biot-Savart velocity** on the cylinder `(ℝ/dℤ) × ℝ`: two `L²` fields with
the same weak divergence (`0`) and the same weak curl (`f`) agree a.e. (the difference is an `L²`
harmonic field on the cylinder, hence `0`: its horizontal Fourier modes solve `g' = ∓ κ_k g`,
which has no nonzero `L²(ℝ)` solution, including `κ_0 = 0`). Used in SP 3230-3240 to pass the
bound from the constructed velocity to the arbitrary `u` of `CTEmbeddings`. -/
def BiotSavartUnique : Prop :=
  ∀ d : ℝ, 0 < d → ∀ (f : ℝ × ℝ → ℂ) (u v : ℝ × ℝ → Fin 2 → ℂ),
    IsBiotSavart d f u → IsBiotSavart d f v →
      ∀ᵐ x ∂(volume.restrict (B0579.cell d)), u x = v x

/-- **Uniform existence** (SP 3236-3240): the centrally even zero-circulation class `X_{m,d}`
(`m > 8`, `d ≥ 1`) has a Biot-Savart velocity with `‖K_d f‖₂ ≤ C ‖f‖_{X_{m,d}}`, `C` independent
of `d`. -/
def BiotSavartExistsUniform : Prop :=
  ∀ m : ℝ, 8 < m → ∃ C : ℝ, ∀ d : ℝ, 1 ≤ d → ∀ f : ℝ × ℝ → ℂ,
    MemLp f 2 (B0579.cellMeasure d m) → HasZeroCirculation d f → IsCentrallyEven f →
      ∃ u : ℝ × ℝ → Fin 2 → ℂ, IsBiotSavart d f u ∧
        velNorm d u ≤ ENNReal.ofReal C * xNorm d m f

/-- **`ctEmbeddings` from the three lemmas.** -/
theorem ctEmbeddings_of (h1 : QuadQBound) (h2 : BiotSavartUnique)
    (h3 : BiotSavartExistsUniform) : CTEmbeddings := by
  intro m hm
  obtain ⟨C1, hC1⟩ := h1 m (by linarith)
  obtain ⟨C3, hC3⟩ := h3 m hm
  refine ⟨max C1 0 + max C3 0, fun d hd f hf hz hev u hu => ?_⟩
  obtain ⟨u₃, hu₃, hv₃⟩ := hC3 d hd f hf hz hev
  have hae := h2 d (by linarith) f u u₃ hu hu₃
  have hvel : velNorm d u = velNorm d u₃ := by
    unfold velNorm
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    exact eLpNorm_congr_ae (hae.mono fun x hx => by simp only [hx])
  have hq := hC1 d f hf
  rw [hvel]
  calc ENNReal.ofReal ‖quadQ d f‖ + velNorm d u₃
      ≤ ENNReal.ofReal C1 * xNorm d m f + ENNReal.ofReal C3 * xNorm d m f := add_le_add hq hv₃
    _ ≤ ENNReal.ofReal (max C1 0) * xNorm d m f + ENNReal.ofReal (max C3 0) * xNorm d m f :=
        add_le_add
          (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (le_max_left _ _)) zero_le)
          (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (le_max_left _ _)) zero_le)
    _ = ENNReal.ofReal (max C1 0 + max C3 0) * xNorm d m f := by
        rw [ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _), add_mul]

/-! ## Leaf lemmas for `BiotSavartExistsUniform` -/

/-- **Uniform nonzero-mode velocity bound** (SP 3236-3240). For `m > 2`, `c ≥ 1` and a real
`ω ∈ X_{m,c}` with zero total circulation, the Biot-Savart velocity of the nonzero horizontal
modes satisfies `‖K_c ω_ne‖₂ ≤ C ‖ω‖_{X_m}` with `C` independent of `c` (compare
`B0581.norm_velNe_nonzeroPart_le`, which only gives `(c/2π) ‖ω‖`). Proof: modes `k` with
`|κ_k| = 2π|k|/c ≥ 1` have symbol modulus `≤ 1` (`B0581.norm_bsSym_le`); the `≤ c/π` modes with
`|κ_k| < 1` use `|ω̂(κ, ζ)| ≤ c^{-1/2} |(κ, ζ)| ∫|y||ω|` (zero mass) and
`∫|y||ω| ≤ ‖ω‖_{X_m} (∫ jb^{1-m})^{1/2}`, `m > 2`, so each low mode contributes `≲ c⁻¹ ‖ω‖²`. -/
def NonzeroVelUniform : Prop :=
  ∀ m : ℝ, ∀ hm : 2 < m, ∃ C : ℝ, 0 ≤ C ∧ ∀ (c : ℝ) [Fact (0 < c)], 1 ≤ c → ∀ ω : B0579.X c m,
    ∫ x in B0579.cell c, ω x = 0 →
      ‖B0581.velNe c (B0581.nonzeroPart c (B0581.ofX c m (by linarith) ω))‖ ≤ C * ‖ω‖

/-- **The library velocity solves Biot-Savart.** For `m > 1` and a real `ω ∈ X_{m,c}` with zero
circulation, `B0583.velocity` (nonzero modes plus the zero-mode primitive) is an `L²` field with
`div = 0` and `curl = ω` weakly against all cylinder tests (`IsBiotSavart`). Proof: modewise the
symbol `bsSym κ ζ = (iζ, -iκ)/(κ² + ζ²)` has `iκ · bsSym_0 + iζ · bsSym_1 = 0` and
`iκ · bsSym_1 - iζ · bsSym_0 = 1`; for the zero mode `u = (-F, 0)`, `F' = ω̄`. Use the weak
gradients `B0583.velGradQ`, `velGradEta` (`hasWeakVelDeriv_velocity_q/eta`). -/
def VelocityIsBiotSavart : Prop :=
  ∀ (c : ℝ) [Fact (0 < c)] (m : ℝ) (hm : 1 < m) (ω : B0579.X c m)
    (hcirc : ∫ x in B0579.cell c, ω x = 0),
    IsBiotSavart c (fun x => ((ω x : ℝ) : ℂ))
      (fun x j => (B0583.velocity c hm.le ω hcirc : B0579.Plane → B0581.Vel) x j)

/-- **`velNorm` is the `Lp` norm**: for an `L²(cell; ℂ²)` element `F`,
`velNorm c F = ofReal ‖F‖` (`‖F x‖² = ∑_j |F x j|²` in `EuclideanSpace ℂ (Fin 2)`). -/
def VelNormEqLp : Prop :=
  ∀ (c : ℝ) [Fact (0 < c)] (F : MeasureTheory.Lp B0581.Vel 2 (B0581.cellVol c)),
    velNorm c (fun x j => (F : B0579.Plane → B0581.Vel) x j) = ENNReal.ofReal ‖F‖

/-- **Real case of `BiotSavartExistsUniform`**: for `m > 2`, `c ≥ 1`, real `ω ∈ X_{m,c}` with zero
circulation there is a Biot-Savart velocity of `ω` (viewed as complex) with
`velNorm c u ≤ C ‖ω‖_{X_m}`, `C` independent of `c`. -/
def RealBiotSavartUniform : Prop :=
  ∀ m : ℝ, 2 < m → ∃ C : ℝ, 0 ≤ C ∧ ∀ (c : ℝ) [Fact (0 < c)], 1 ≤ c → ∀ ω : B0579.X c m,
    ∫ x in B0579.cell c, ω x = 0 →
      ∃ u : ℝ × ℝ → Fin 2 → ℂ, IsBiotSavart c (fun x => ((ω x : ℝ) : ℂ)) u ∧
        velNorm c u ≤ ENNReal.ofReal (C * ‖ω‖)

end CTE

end UnforcedLeray.Short.IIIa
