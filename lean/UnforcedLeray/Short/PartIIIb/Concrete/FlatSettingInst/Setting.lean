import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Space
import UnforcedLeray.Short.PartIIIb.Concrete.YoungBlocks
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnAff
import UnforcedLeray.Short.PartIIIb.NearInst.Chart
import UnforcedLeray.Short.PartIIIa.Clock.Frame
import UnforcedLeray.Short.PartIIIa.CanonicalTransfer
import UnforcedLeray.Short.PartIIIa.Clock.Existence.BiotSavartField
import Mathlib.MeasureTheory.Covering.DensityTheorem
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# The concrete flat setting of the actual train (source 4342-4356, 4557-4577, 4605-4612)

Source of record: `the November 2 reference manuscript` (73 pages).

`ConcreteYF.FlatSetting` (`Concrete/YoungFlat.lean`) is a structure with free fields.  This file
builds the instance of the source at one regime, `c = ν⁻²`:

| field of `FlatSetting` | here | source | status |
|---|---|---|---|
| `pk.X` | `Xmc c m`, the centrally even zero-circulation subspace of `L²(cell, ⟨x⟩^{2m}dx)` | 4349-4350 | defined (`Space.lean`) |
| `pk.Uev` | `TrainEvolution.U` | 4352 | **pinned**: no operator exists in Lean, only weak flows; `flow` is `ConcreteYF.IsTrainPkg` |
| `pk.q`, `pk.ell` | `FrozenPair.q`, `.ell` | 4352-4356, 2894-2912 | **pinned** to the explicit formulas `frozenQ`, `frozenEll` |
| `conjX` | `conjX` | 4606 | defined (`Space.lean`) |
| `Hper`, `Rper` | `GaussSources.H`, `.R` | 4563-4570 | **pinned** to the explicit periodizations `HProf`, `RProf` |
| `Mcell` | `v(s) ⊗ K_cξ + K_cξ ⊗ v(s)` | 4610-4612 | defined, `K_c` is the library velocity `realBiotSavart` |
| `chiO`, `c`, `eps3` | `χ̂_o(ν·)`, `c`, `ε³` | 4573-4579 | defined |

A pinned field is a field of a structure whose other fields determine it (`FlatInstData`): the
planar function of an element of `X_{m,c}` determines it (`xmc_ext`), and the weak flow from a datum
is unique.  Elements of `X_{m,c}` cannot be written by a formula without proving that the formula
lies in the space, and an `if`-branch for the contrary case would be a junk branch; existence of the
data is therefore a separate statement (`FlatInstData`, tasks of
`ORG:return-concrete/near/link/kflat/flat-setting`).

## Why a canonical pointwise representative of `K_c ξ`

`FlatSetting.Mcell s ξ` is a function of the point `x`, and the pin `Kflat.IsFlatDuhamelColumn`
compares `(s,x) ↦ Mcell s (ξ(s)) x` with an `H`-function almost everywhere for the *product* measure
on `(s,x)`.  The coercion of `Lp` chooses a representative of `K_cξ(s)` separately for each `s`; the
resulting function of `(s,x)` need not be jointly measurable and such a product-a.e. statement could
not be proved (a set with null sections need not be null).  So `Mcell` reads the Lebesgue value
`lebRep`, which depends only on the class (`lebRep_congr`), equals the class almost everywhere
(`lebRep_ae`), and is jointly measurable along jointly measurable families
(`lebRep_stronglyMeasurable`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.Axi (Merid)
open UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution (realBiotSavart realPartVelocityCLM
  realPartVelocityCLM_apply coeFn_realPartVelocityLp)

/-! ## 1. The Lebesgue value on the cell -/

section LebRep

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The value at `x` of the Lebesgue averages over the shrinking balls of the extension by zero of
`f` off the cell. -/
def lebRep (c : ℝ) (f : ℝ × ℝ → E) (x : ℝ × ℝ) : E :=
  limUnder atTop fun n : ℕ =>
    ⨍ y in Metric.closedBall x ((n : ℝ) + 1)⁻¹, (B0579.cell c).indicator f y

/-- The Lebesgue value depends only on the class of `f` on the cell. -/
theorem lebRep_congr {c : ℝ} {f g : ℝ × ℝ → E}
    (h : f =ᵐ[volume.restrict (B0579.cell c)] g) : lebRep c f = lebRep c g := by
  have hi : (B0579.cell c).indicator f =ᵐ[volume] (B0579.cell c).indicator g :=
    (ae_eq_restrict_iff_indicator_ae_eq (B0579.measurableSet_cell c)).1 h
  funext x
  unfold lebRep
  congr 1
  funext n
  exact average_congr (ae_restrict_of_ae hi)

/-- The radii of `lebRep` shrink to zero. -/
theorem tendsto_lebRadius :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝[>] (0 : ℝ)) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => ?_⟩
  · simpa [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  · show (0 : ℝ) < ((n : ℝ) + 1)⁻¹
    positivity

/-- **The Lebesgue value of an `L²(cell)` class is a representative of it** (Lebesgue
differentiation). -/
theorem lebRep_ae [CompleteSpace E] {c : ℝ} {f : ℝ × ℝ → E}
    (hf : MemLp f 2 (volume.restrict (B0579.cell c))) :
    lebRep c f =ᵐ[volume.restrict (B0579.cell c)] f := by
  have hcell := B0579.measurableSet_cell c
  have hloc : LocallyIntegrable ((B0579.cell c).indicator f) volume :=
    ((memLp_indicator_iff_restrict hcell).2 hf).locallyIntegrable (by norm_num)
  have h := IsUnifLocDoublingMeasure.ae_tendsto_average (μ := (volume : Measure (ℝ × ℝ))) hloc 1
  filter_upwards [ae_restrict_of_ae h, ae_restrict_mem hcell] with x hx hxc
  have ht := hx (ι := ℕ) (l := atTop) (fun _ => x) (fun n => ((n : ℝ) + 1)⁻¹) tendsto_lebRadius
    (Eventually.of_forall fun n => by
      rw [one_mul]
      exact Metric.mem_closedBall_self (by positivity))
  rw [lebRep, ht.limUnder_eq, indicator_of_mem hxc]

/-- **Joint measurability of the Lebesgue value** along a jointly measurable family. -/
theorem lebRep_stronglyMeasurable [CompleteSpace E] {c : ℝ} {F : ℝ × (ℝ × ℝ) → E}
    (hF : StronglyMeasurable F) :
    StronglyMeasurable fun p : ℝ × (ℝ × ℝ) => lebRep c (fun y => F (p.1, y)) p.2 := by
  unfold lebRep
  refine StronglyMeasurable.limUnder fun n => ?_
  set r : ℝ := ((n : ℝ) + 1)⁻¹
  have hvol : ∀ x : ℝ × ℝ, (volume : Measure (ℝ × ℝ)).real (Metric.closedBall x r) =
      (volume : Measure (ℝ × ℝ)).real (Metric.closedBall (0 : ℝ × ℝ) r) := fun x => by
    unfold Measure.real
    rw [Measure.addHaar_closedBall_center]
  have hset : MeasurableSet {q : (ℝ × (ℝ × ℝ)) × (ℝ × ℝ) | dist q.2 q.1.2 ≤ r ∧ q.2 ∈ B0579.cell c} :=
    (measurableSet_le (measurable_snd.dist (measurable_snd.comp measurable_fst))
      measurable_const).inter (measurable_snd (B0579.measurableSet_cell c))
  have hG : StronglyMeasurable fun q : (ℝ × (ℝ × ℝ)) × (ℝ × ℝ) =>
      {q : (ℝ × (ℝ × ℝ)) × (ℝ × ℝ) | dist q.2 q.1.2 ≤ r ∧ q.2 ∈ B0579.cell c}.indicator
        (fun q => F (q.1.1, q.2)) q :=
    (hF.comp_measurable ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).indicator hset
  have hI := (hG.integral_prod_right' (ν := (volume : Measure (ℝ × ℝ)))).const_smul
    ((volume : Measure (ℝ × ℝ)).real (Metric.closedBall (0 : ℝ × ℝ) r))⁻¹
  have e : (fun p : ℝ × (ℝ × ℝ) => ⨍ y in Metric.closedBall p.2 r,
        (B0579.cell c).indicator (fun y => F (p.1, y)) y) =
      fun p => ((volume : Measure (ℝ × ℝ)).real (Metric.closedBall (0 : ℝ × ℝ) r))⁻¹ •
        ∫ y, {q : (ℝ × (ℝ × ℝ)) × (ℝ × ℝ) | dist q.2 q.1.2 ≤ r ∧ q.2 ∈ B0579.cell c}.indicator
          (fun q => F (q.1.1, q.2)) (p, y) := by
    funext p
    rw [setAverage_eq, hvol, ← integral_indicator Metric.isClosed_closedBall.measurableSet]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    by_cases h1 : dist y p.2 ≤ r <;> by_cases h2 : y ∈ B0579.cell c <;>
      simp [indicator, h1, h2, Metric.mem_closedBall]
  rw [e]
  exact hI

end LebRep

/-! ## 2. The Gaussian sources (source 4563-4570) -/

/-- The clock `a = 1 + νs` of the sources at age `s`; the ages `s < 0` are outside the setting and
read the value at `s = 0`, so that `Hper`, `Rper` are defined on all of `ℝ`. -/
def srcA (ν s : ℝ) : ℝ := ageA ν (max s 0)

/-- `E_s = curl V_G` as a radial function, `E_s(r) = a⁻²(2 - r²/(2a))e^{-r²/(4a)}` (source 4565-4568;
`curl_Vj` checks it against `Concrete.Vj`). -/
def gaussE (a r : ℝ) : ℝ := (a ^ 2)⁻¹ * (2 - r ^ 2 / (2 * a)) * Real.exp (-(r ^ 2) / (4 * a))

/-- `rE_s'(r)` (source 4569). -/
def gaussRdE (a r : ℝ) : ℝ := r * deriv (gaussE a) r

/-- `r = |x|` on the plane. -/
def planeR (x : ℝ × ℝ) : ℝ := Real.sqrt (x.1 ^ 2 + x.2 ^ 2)

/-- The angular-two mode `rE_s'(r)e^{2iϑ}` (source 4569), `e^{2iϑ} = IIIa.angTwo`. -/
def hMode (a : ℝ) (x : ℝ × ℝ) : ℂ := ((gaussRdE a (planeR x) : ℝ) : ℂ) * IIIa.angTwo x

/-- The radial mode `rE_s'(r) + 2E_s(r)` (source 4570). -/
def rMode (a : ℝ) (x : ℝ × ℝ) : ℂ :=
  ((gaussRdE a (planeR x) + 2 * gaussE a (planeR x) : ℝ) : ℂ)

/-- `H_{s,c}`, the periodization of `rE_s'(r)e^{2iϑ}` (source 4568-4570). -/
def HProf (ν c s : ℝ) : ℝ × ℝ → ℂ := IIIa.periodizeC c (hMode (srcA ν s))

/-- `R_{s,c}`, the periodization of `rE_s'(r) + 2E_s(r)` (source 4568-4570). -/
def RProf (ν c s : ℝ) : ℝ × ℝ → ℂ := IIIa.periodizeC c (rMode (srcA ν s))

/-- `g_B = -½(d-ie)H_{s,c} - ½(d+ie)H̄_{s,c} - βR_{s,c}` as a planar function, for the matrix `B`
at age `s` (source 4605-4608; `ConcreteYF.FlatSetting.gB` in `X_{m,c}`). -/
def gBProf (ν c s : ℝ) (B : Matrix (Fin 3) (Fin 3) ℝ) (x : ℝ × ℝ) : ℂ :=
  (-(1 / 2 : ℂ) * (((Bd B : ℝ) : ℂ) - Complex.I * ((Be B : ℝ) : ℂ))) * HProf ν c s x
    + (-(1 / 2 : ℂ) * (((Bd B : ℝ) : ℂ) + Complex.I * ((Be B : ℝ) : ℂ))) * conj (HProf ν c s x)
    - ((ConcreteYF.Bbeta B : ℝ) : ℂ) * RProf ν c s x

/-- The derivative of `t ↦ C e^{-(K+t²)/(4a)} t`. -/
theorem hasDerivAt_gaussLin (C K a t : ℝ) (ha : a ≠ 0) :
    HasDerivAt (fun t : ℝ => C * Real.exp (-(K + t ^ 2) / (4 * a)) * t)
      (C * Real.exp (-(K + t ^ 2) / (4 * a)) * (1 - t ^ 2 / (2 * a))) t := by
  have hin : HasDerivAt (fun t : ℝ => -(K + t ^ 2) / (4 * a)) (-(2 * t) / (4 * a)) t := by
    have h := ((hasDerivAt_pow 2 t).const_add K).neg.div_const (4 * a)
    simpa using h
  have hE := (hin.exp.const_mul C).mul (hasDerivAt_id' t)
  refine hE.congr_deriv ?_
  generalize Real.exp (-(K + t ^ 2) / (4 * a)) = E
  field_simp
  ring

/-- `E_s` is the curl of `V_G` (source 4565-4568): `∂_q(V_j)_η - ∂_η(V_j)_q = E_s(|x_j|)`, with
`Concrete.Vj` the Gaussian of the physical affine force (4963-4968). -/
theorem curl_Vj (ν s : ℝ) (j : ℤ) (x : ℝ × ℝ) (ha : ageA ν s ≠ 0) :
    deriv (fun q => (Vj ν s j (q, x.2)).2) x.1 - deriv (fun η => (Vj ν s j (x.1, η)).1) x.2 =
      gaussE (ageA ν s) (planeR (xj ν j x)) := by
  set a := ageA ν s with ha_def
  have hR : planeR (xj ν j x) ^ 2 = (x.1 - (j : ℝ) * cOf ν) ^ 2 + x.2 ^ 2 := by
    unfold planeR xj
    rw [Real.sq_sqrt (by positivity)]
  have h1 : HasDerivAt (fun q => (Vj ν s j (q, x.2)).2)
      ((a ^ 2)⁻¹ * Real.exp (-(x.2 ^ 2 + (x.1 - (j : ℝ) * cOf ν) ^ 2) / (4 * a)) *
        (1 - (x.1 - (j : ℝ) * cOf ν) ^ 2 / (2 * a))) x.1 := by
    have e : (fun q => (Vj ν s j (q, x.2)).2) = fun q =>
        (a ^ 2)⁻¹ * Real.exp (-(x.2 ^ 2 + (q - (j : ℝ) * cOf ν) ^ 2) / (4 * a)) *
          (q - (j : ℝ) * cOf ν) := by
      funext q
      simp only [Vj, Prod.smul_snd, smul_eq_mul, Jrot, xj, ← ha_def, sq2, add_comm]
    rw [e]
    exact (hasDerivAt_gaussLin ((a ^ 2)⁻¹) (x.2 ^ 2) a (x.1 - (j : ℝ) * cOf ν) ha).comp_sub_const
      x.1 ((j : ℝ) * cOf ν)
  have h2 : HasDerivAt (fun η => (Vj ν s j (x.1, η)).1)
      (-((a ^ 2)⁻¹ * Real.exp (-((x.1 - (j : ℝ) * cOf ν) ^ 2 + x.2 ^ 2) / (4 * a)) *
        (1 - x.2 ^ 2 / (2 * a)))) x.2 := by
    have e : (fun η => (Vj ν s j (x.1, η)).1) = fun η =>
        -((a ^ 2)⁻¹ * Real.exp (-((x.1 - (j : ℝ) * cOf ν) ^ 2 + η ^ 2) / (4 * a)) * η) := by
      funext η
      simp only [Vj, Prod.smul_fst, smul_eq_mul, Jrot, xj, ← ha_def, sq2, mul_neg]
    rw [e]
    exact (hasDerivAt_gaussLin ((a ^ 2)⁻¹) ((x.1 - (j : ℝ) * cOf ν) ^ 2) a x.2 ha).neg
  rw [h1.deriv, h2.deriv, gaussE, hR, add_comm (x.2 ^ 2)]
  field_simp
  ring

/-! ## 3. The frozen pair (source 4352-4356, 2894-2912) -/

/-- The fixed band of the flat return: `Σ = 2` (`H = 2/ν`; `ConcreteYF.FlatSettingHyp.young`). -/
def flatSigma : ℝ := 2

/-- The age on the band `0 ≤ s ≤ H = Σ/ν`, on which the pair of the source lives (4344-4346,
4364-4368: "on `0 ≤ s ≤ H`"); outside the band the pair is frozen at the endpoint, so that the Gram
normalization of `ConcreteYF.YoungLaws` makes sense at every `s`. -/
def bandAge (ν s : ℝ) : ℝ := max 0 (min s (flatSigma / ν))

/-- `a(s) = 1 + νs` on the band. -/
def bandA (ν s : ℝ) : ℝ := IIIa.clockA ν (bandAge ν s)

/-- The moving cell length `d = c/√a` on the band (source 2858, 2864). -/
def bandD (ν c s : ℝ) : ℝ := IIIa.cellLen c (bandA ν s)

/-- `+ ↦ 0`, `- ↦ 1` (the indices of `IIIa.PlanarFrameKernels`: `e₀ = q`, `e₁ = q̄`). -/
def pmIdx (j : Bool) : Fin 2 := if j then 0 else 1

/-- `q_{±,s} = J_a E_±`, `E_± = P_d e_±` the two periodized growing vectors at the cell length
`d = c/√a` (source 2894-2896: "the two periodized growing vectors"; 4352-4354: "heat-scaled,
periodized"; `J_a W(x) = a⁻²W(x/√a)`, 3030). -/
def frozenQ (κ : IIIa.PlanarFrameKernels) (ν c : ℝ) (j : Bool) (s : ℝ) : ℝ × ℝ → ℂ :=
  IIIa.Jscale (bandA ν s) (IIIa.perE κ (bandD ν c s) (pmIdx j))

/-- `ℓ_{±,s} f = Λ_±(J_a⁻¹ f)`, `Λ = G⁻¹Λ⁰` the Gram-normalized periodized dual rows at the cell
length `d = c/√a` (source 2896-2902, 2911-2912, 4353-4356: "its finite Gram-normalized dual"), the
pairing being `∫_{cell d}` (the moving coordinate of 2860-2864; on the original cell it reads
`∫_{cell c} Λ_±(x/√a) f(x) dx`). -/
def frozenEll (κ : IIIa.PlanarFrameKernels) (ν c : ℝ) (j : Bool) (s : ℝ) (f : ℝ × ℝ → ℂ) : ℂ :=
  ∫ y in B0579.cell (bandD ν c s),
    IIIa.perLam κ (bandD ν c s) (pmIdx j) y * IIIa.JscaleInv (bandA ν s) f y

/-! ## 4. The Biot-Savart velocity `K_c` and the stress readout (source 4610-4612) -/

section Kc

variable {c m : ℝ}

/-- The real part of an element of the ambient space. -/
def reX (f : XAmb c m) : B0579.X c m := (Complex.reCLM : ℂ →L[ℝ] ℝ).compLp f

theorem coeFn_reX (f : XAmb c m) :
    (reX f : ℝ × ℝ → ℝ) =ᵐ[B0579.cellMeasure c m] fun x => (f x).re := by
  filter_upwards [ContinuousLinearMap.coeFn_compLp (Complex.reCLM : ℂ →L[ℝ] ℝ) f] with x hx
  rw [reX, hx]
  rfl

variable [hm : Fact (1 < m)]

theorem reX_circ (ξ : Xmc c m) : ∫ x in B0579.cell c, reX ξ.1 x = 0 := by
  have h : ∫ x in B0579.cell c, reX ξ.1 x = ∫ x in B0579.cell c, (xFn ξ x).re :=
    integral_congr_ae (ae_cell_of_ae_cellMeasure (coeFn_reX ξ.1))
  rw [h, IIIa.BSAux.integral_re' (xFn_integrableOn ξ), xFn_circ, Complex.zero_re]

theorem one_le_of_fact : 1 ≤ m := (Fact.out : 1 < m).le

variable [hc : Fact (0 < c)]

/-- `K_c(Re ξ)` in `L²(cell)`: the library velocity (B0583, nonzero modes plus the zero-mode
primitive), real part (`K_c = ∇^⊥Δ⁻¹`, source 3236-3240, 4610-4612). -/
def kcLp (ξ : Xmc c m) : Lp Merid 2 (B0581.cellVol c) :=
  realBiotSavart one_le_of_fact (reX ξ.1) (reX_circ ξ)

/-- **`K_c ξ` as a canonical pointwise function** (Lebesgue value of `kcLp`; the source only uses
`K_c ξ` almost everywhere, see the module docstring). -/
def kcMer (ξ : Xmc c m) (x : ℝ × ℝ) : Merid := lebRep c (kcLp ξ : ℝ × ℝ → Merid) x

theorem kcMer_ae (ξ : Xmc c m) :
    kcMer ξ =ᵐ[volume.restrict (B0579.cell c)] (kcLp ξ : ℝ × ℝ → Merid) :=
  lebRep_ae (Lp.memLp (kcLp ξ))

/-- `K_c ξ` complexified, in the format of `IIIa.IsBiotSavart`. -/
def kcC (ξ : Xmc c m) (x : ℝ × ℝ) (j : Fin 2) : ℂ := ((kcMer ξ x j : ℝ) : ℂ)

/-- A real element of `X_{m,c}` has real planar function. -/
theorem xFn_of_real {ξ : Xmc c m} (h : conjX ξ = ξ) :
    xFn ξ =ᵐ[volume.restrict (B0579.cell c)] fun x => ((reX ξ.1 x : ℝ) : ℂ) := by
  have hc := xFn_conjX ξ
  rw [h] at hc
  filter_upwards [hc, ae_cell_of_ae_cellMeasure (coeFn_reX ξ.1)] with x h1 h2
  have h2' : reX ξ.1 x = (xFn ξ x).re := h2
  rw [h2']
  exact (Complex.conj_eq_iff_real.1 h1.symm).choose_spec ▸ by simp

/-- **`K_c ξ` is the Biot-Savart velocity of a real `ξ ∈ X_{m,c}`** (`CTE.velocityIsBiotSavart_one`;
the velocity of `IsLinearisedFlow`, unique by `CTE.BiotSavartUnique`). -/
theorem isBiotSavart_kc {ξ : Xmc c m} (h : conjX ξ = ξ) :
    IIIa.IsBiotSavart c (xFn ξ) (kcC ξ) := by
  have h0 := IIIa.BSAux.isBS_re (IIIa.CTE.velocityIsBiotSavart_one c m one_le_of_fact (reX ξ.1)
    (reX_circ ξ))
  have h1 := IIIa.BSAux.isBS_congr (v := kcC ξ) h0 (fun j => by
    filter_upwards [coeFn_realPartVelocityLp (UnforcedLeray.B0583.velocity c one_le_of_fact
      (reX ξ.1) (reX_circ ξ)), kcMer_ae ξ] with x hx hk
    have e : kcC ξ x j = ((kcMer ξ x j : ℝ) : ℂ) := rfl
    rw [e, hk]
    have e2 : (kcLp ξ : ℝ × ℝ → Merid) x = realPartVelocityCLM
        ((UnforcedLeray.B0583.velocity c one_le_of_fact (reX ξ.1) (reX_circ ξ) :
          ℝ × ℝ → UnforcedLeray.B0581.Vel) x) := hx
    rw [e2, realPartVelocityCLM_apply])
  obtain ⟨h1a, h1b, h1c⟩ := h1
  refine ⟨h1a, h1b, fun ψ hψ => ?_⟩
  rw [← h1c ψ hψ]
  refine integral_congr_ae ?_
  filter_upwards [xFn_of_real h] with x hx
  rw [hx]

end Kc

/-! ## 5. The pinned data and the setting -/

section Data

variable {ν c m : ℝ} [hm : Fact (1 < m)]

/-- **The linearised train evolution `𝒰(s,t)` on `X_{m,c}`** (source 4352, 2819-2836, 2860-2864).
No operator exists in Lean: the evolution is characterized by weak flows, so it is pinned.
* `flow` is `ConcreteYF.IsTrainPkg` (`s ↦ 𝒰(s,t)x` is the weak linearised flow from `x` at age
  `t ≥ 0`, around the actual train `tr`); by uniqueness of the flow it determines `U` on
  `0 ≤ t ≤ s`;
* `off` fixes `U` outside the causal range, where the source has no evolution;
* `cocycle`, `real`, `locBdd`, `jointCont` are the properties of the Volterra evolution used by the
  Duhamel formula (`𝒰(s,r)𝒰(r,t) = 𝒰(s,t)`, 4385-4390; real coefficients; bounded and strongly
  continuous on bounded age strips, 2819-2836). -/
structure TrainEvolution (m : ℝ) [Fact (1 < m)] (tr : UnforcedLeray.B0140.TrainSol ν c) where
  U : ℝ → ℝ → Xmc c m →L[ℂ] Xmc c m
  off : ∀ s t, ¬(0 ≤ t ∧ t ≤ s) → U s t = ContinuousLinearMap.id ℂ (Xmc c m)
  flow : ∀ t, 0 ≤ t → ∀ x : Xmc c m, ∃ u,
    IIIa.IsLinearisedFlow ν c m tr t (xFn x) (fun s => xFn (U s t x)) u
  cocycle : ∀ s r t, 0 ≤ t → t ≤ r → r ≤ s → (U s r).comp (U r t) = U s t
  real : ∀ s t x, conjX (U s t x) = U s t (conjX x)
  locBdd : ∀ T : ℝ, ∃ C : ℝ, ∀ s t, 0 ≤ t → t ≤ s → s ≤ T → ‖U s t‖ ≤ C
  jointCont : ∀ x : Xmc c m,
    ContinuousOn (fun p : ℝ × ℝ => U p.1 p.2 x) {p : ℝ × ℝ | 0 ≤ p.2 ∧ p.2 ≤ p.1}

/-- **The frozen pair** (source 4352-4356, 2894-2912), pinned to `frozenQ`, `frozenEll`: the
elements of `X_{m,c}` and the bounded functionals these formulas define.  The remaining fields are
the laws of the pair on its band (`Λ E = I₂`, 2896; `q_- = q̄_+`, `ℓ_- = ℓ̄_+`; continuity in the age,
4352-4356, 4650-4654). -/
structure FrozenPair (κ : IIIa.PlanarFrameKernels) (ν c m : ℝ) [Fact (1 < m)] where
  q : Bool → ℝ → Xmc c m
  ell : Bool → ℝ → Xmc c m →L[ℂ] ℂ
  q_pin : ∀ j s, xFn (q j s) =ᵐ[volume.restrict (B0579.cell c)] frozenQ κ ν c j s
  ell_pin : ∀ j s x, ell j s x = frozenEll κ ν c j s (xFn x)
  gram : ∀ s i j, ell i s (q j s) = if i = j then 1 else 0
  conj_q : ∀ s, q false s = conjX (q true s)
  conj_ell : ∀ s x, ell false s x = conj (ell true s (conjX x))
  q_cont : ∀ j, Continuous (q j)
  ell_cont : ∀ j, Continuous (ell j)

/-- **The Gaussian sources in `X_{m,c}`** (source 4562-4570: "The vorticity sources are centrally
even and have zero circulation"), pinned to `HProf`, `RProf`; continuous in the age (`a(t) = 1+νt`,
4565). -/
structure GaussSources (ν c m : ℝ) [Fact (1 < m)] where
  H : ℝ → Xmc c m
  R : ℝ → Xmc c m
  H_pin : ∀ s, xFn (H s) =ᵐ[volume.restrict (B0579.cell c)] HProf ν c s
  R_pin : ∀ s, xFn (R s) =ᵐ[volume.restrict (B0579.cell c)] RProf ν c s
  H_cont : Continuous H
  R_cont : Continuous R

/-- The pinned data of the flat setting of the train `tr` at one regime. -/
structure FlatInstData (κ : IIIa.PlanarFrameKernels) (ν c m : ℝ) [Fact (1 < m)]
    (tr : UnforcedLeray.B0140.TrainSol ν c) where
  ev : TrainEvolution m tr
  pair : FrozenPair κ ν c m
  src : GaussSources ν c m

variable {κ : IIIa.PlanarFrameKernels} {tr : UnforcedLeray.B0140.TrainSol ν c}

/-- The evolution package of the actual train: `X_{m,c}`, `𝒰`, `q_±`, `ℓ_±` (source 4349-4356). -/
def actualPk (D : FlatInstData κ ν c m tr) : YoungPkg where
  X := Xmc c m
  Uev := D.ev.U
  q := D.pair.q
  ell := D.pair.ell

/-- The package is the actual train evolution (`ConcreteYF.IsTrainPkg`, the pin of the setting). -/
theorem isTrainPkg_actualPk (D : FlatInstData κ ν c m tr) :
    ConcreteYF.IsTrainPkg (actualPk D) ν c m tr xFn :=
  D.ev.flow

theorem TrainEvolution.refl (ev : TrainEvolution m tr) (s : ℝ) :
    ev.U s s = ContinuousLinearMap.id ℂ (Xmc c m) := by
  by_cases hs : 0 ≤ s
  · ext1 x
    obtain ⟨u, hu⟩ := ev.flow s hs x
    exact xmc_ext hu.initial
  · exact ev.off s s fun h => hs h.1

/-- **The laws of the package** (`ConcreteYF.YoungLaws`, source 4338-4350, 4385-4390). -/
theorem youngLaws_actualPk (D : FlatInstData κ ν c m tr) :
    ConcreteYF.YoungLaws (actualPk D) conjX where
  refl := D.ev.refl
  trans := D.ev.cocycle
  gram := D.pair.gram
  conj_add := conjX_add
  conj_smul := conjX_smul
  conj_norm := norm_conjX
  conj_inv := conjX_conjX
  conj_U := D.ev.real
  conj_q := D.pair.conj_q
  conj_ell := D.pair.conj_ell

variable [hc : Fact (0 < c)]

/-- **The concrete flat setting of the actual train** (source 4557-4577, 4605-4612): the package of
`D`, conjugation, the sources of `D`, the readout `M = v(s)⊗K_cξ + K_cξ⊗v(s)`, the old cutoff
`χ_o(s) = χ̂_o(νs)`, the cell size `c` and the amplitude `ε³`. -/
def actualFlatSetting (D : FlatInstData κ ν c m tr) (χo : ℝ → ℝ) (ε : ℝ) :
    ConcreteYF.FlatSetting where
  pk := actualPk D
  conjX := conjX
  Hper := D.src.H
  Rper := D.src.R
  Mcell := fun s ξ x => IIIa.symOuter (NearInst.trainMer tr (s, x)) (kcMer ξ x)
  chiO := fun s => χo (ν * s)
  c := c
  eps3 := ε ^ 3

/-- `g_B` of the setting (it does not depend on `χ_o, ε`; `gBD_eq`). -/
def gBD (D : FlatInstData κ ν c m tr) (B : ℝ → Matrix (Fin 3) (Fin 3) ℝ) (s : ℝ) : Xmc c m :=
  (actualFlatSetting D (fun _ => 0) 0).gB B s

/-- `ξ_B` of the setting (it does not depend on `χ_o, ε`; `xiD_eq`), source 4610. -/
def xiD (D : FlatInstData κ ν c m tr) (μ : ℂ) (B : ℝ → Matrix (Fin 3) (Fin 3) ℝ) (s : ℝ) :
    Xmc c m :=
  (actualFlatSetting D (fun _ => 0) 0).xi μ B s

theorem gBD_eq (D : FlatInstData κ ν c m tr) (χo : ℝ → ℝ) (ε : ℝ)
    (B : ℝ → Matrix (Fin 3) (Fin 3) ℝ) (s : ℝ) :
    (actualFlatSetting D χo ε).gB B s = gBD D B s := rfl

theorem xiD_eq (D : FlatInstData κ ν c m tr) (χo : ℝ → ℝ) (ε : ℝ) (μ : ℂ)
    (B : ℝ → Matrix (Fin 3) (Fin 3) ℝ) (s : ℝ) :
    (actualFlatSetting D χo ε).xi μ B s = xiD D μ B s := rfl

/-- The explicit form of `g_B` (source 4605-4608). -/
theorem gBD_apply (D : FlatInstData κ ν c m tr) (B : ℝ → Matrix (Fin 3) (Fin 3) ℝ) (s : ℝ) :
    gBD D B s =
      (-(1 / 2 : ℂ) * (((Bd (B s) : ℝ) : ℂ) - Complex.I * ((Be (B s) : ℝ) : ℂ))) • D.src.H s
      + (-(1 / 2 : ℂ) * (((Bd (B s) : ℝ) : ℂ) + Complex.I * ((Be (B s) : ℝ) : ℂ))) •
          conjX (D.src.H s)
      - (((ConcreteYF.Bbeta (B s) : ℝ) : ℂ)) • D.src.R s := rfl

/-- The explicit form of `ξ_B` (source 4610). -/
theorem xiD_apply (D : FlatInstData κ ν c m tr) (μ : ℂ) (B : ℝ → Matrix (Fin 3) (Fin 3) ℝ)
    (s : ℝ) :
    xiD D μ B s = ((s : ℂ) ^ (-μ)) •
      ∫ t in Ioc 0 s, ((t : ℂ) ^ μ) • (D.ev.U s t) (gBD D B t) := rfl

/-- The planar function of `g_B` is `gBProf` (the pins of `H_{s,c}`, `R_{s,c}`). -/
theorem xFn_gBD (D : FlatInstData κ ν c m tr) (B : ℝ → Matrix (Fin 3) (Fin 3) ℝ) (s : ℝ) :
    xFn (gBD D B s) =ᵐ[volume.restrict (B0579.cell c)] gBProf ν c s (B s) := by
  rw [gBD_apply]
  set a := -(1 / 2 : ℂ) * (((Bd (B s) : ℝ) : ℂ) - Complex.I * ((Be (B s) : ℝ) : ℂ))
  set b := -(1 / 2 : ℂ) * (((Bd (B s) : ℝ) : ℂ) + Complex.I * ((Be (B s) : ℝ) : ℂ))
  set d := ((ConcreteYF.Bbeta (B s) : ℝ) : ℂ)
  filter_upwards [xFn_sub (a • D.src.H s + b • conjX (D.src.H s)) (d • D.src.R s),
    xFn_add (a • D.src.H s) (b • conjX (D.src.H s)), xFn_smul a (D.src.H s),
    xFn_smul b (conjX (D.src.H s)), xFn_smul d (D.src.R s), xFn_conjX (D.src.H s),
    D.src.H_pin s, D.src.R_pin s] with x h1 h2 h3 h4 h5 h6 h7 h8
  rw [h1, h2, h3, h4, h5, h6, h7, h8]
  rfl

/-- `ξ_B` vanishes at nonpositive ages (`Ioc 0 s = ∅`). -/
theorem xiD_nonpos (D : FlatInstData κ ν c m tr) (μ : ℂ) (B : ℝ → Matrix (Fin 3) (Fin 3) ℝ)
    {s : ℝ} (hs : s ≤ 0) : xiD D μ B s = 0 := by
  rw [xiD_apply, Ioc_eq_empty (not_lt.2 hs)]
  simp

/-- `R_{s,c}` is real. -/
theorem GaussSources.R_real (S : GaussSources ν c m) (s : ℝ) : conjX (S.R s) = S.R s := by
  refine xmc_ext ?_
  filter_upwards [xFn_conjX (S.R s), S.R_pin s] with x h1 h2
  rw [h1, h2, RProf, IIIa.periodizeC, Complex.conj_tsum]
  refine tsum_congr fun n => ?_
  rw [rMode, Complex.conj_ofReal]

/-- `g_B` is real (source 4606: the two harmonics are conjugate, `R_{s,c}` is real). -/
theorem gBD_real (D : FlatInstData κ ν c m tr) (B : ℝ → Matrix (Fin 3) (Fin 3) ℝ) (s : ℝ) :
    conjX (gBD D B s) = gBD D B s := by
  have e1 : ∀ d e : ℝ, (starRingEnd ℂ) (-(1 / 2 : ℂ) * ((d : ℂ) - Complex.I * (e : ℂ))) =
      -(1 / 2 : ℂ) * ((d : ℂ) + Complex.I * (e : ℂ)) := by
    intro d e
    apply Complex.ext <;> simp
  have e2 : ∀ d e : ℝ, (starRingEnd ℂ) (-(1 / 2 : ℂ) * ((d : ℂ) + Complex.I * (e : ℂ))) =
      -(1 / 2 : ℂ) * ((d : ℂ) - Complex.I * (e : ℂ)) := by
    intro d e
    apply Complex.ext <;> simp
  rw [gBD_apply, conjX_sub, conjX_add, conjX_smul, conjX_smul, conjX_smul, conjX_conjX,
    D.src.R_real, e1, e2, Complex.conj_ofReal, add_comm (_ • conjX (D.src.H s))]

/-- `t^μ` is real for `t > 0`, `μ` real. -/
theorem conj_cpow_real {t μ : ℝ} (ht : 0 < t) :
    conj ((t : ℂ) ^ (μ : ℂ)) = (t : ℂ) ^ (μ : ℂ) := by
  rw [← Complex.ofReal_cpow ht.le, Complex.conj_ofReal]

/-- **`ξ_B` is real** for real `μ` (source 4610: real source `g_B`, real evolution). -/
theorem xiD_real (D : FlatInstData κ ν c m tr) (μ : ℝ) (B : ℝ → Matrix (Fin 3) (Fin 3) ℝ)
    (s : ℝ) : conjX (xiD D (μ : ℂ) B s) = xiD D (μ : ℂ) B s := by
  by_cases hs : 0 < s
  · rw [xiD_apply, conjX_smul]
    have h1 : conj ((s : ℂ) ^ (-(μ : ℂ))) = (s : ℂ) ^ (-(μ : ℂ)) := by
      have := conj_cpow_real (t := s) (μ := -μ) hs
      simpa using this
    have h2 : conjX (∫ t in Ioc 0 s, ((t : ℂ) ^ (μ : ℂ)) • (D.ev.U s t) (gBD D B t)) =
        ∫ t in Ioc 0 s, ((t : ℂ) ^ (μ : ℂ)) • (D.ev.U s t) (gBD D B t) := by
      have h3 := (conjXL (c := c) (m := m)).integral_comp_comm
        (μ := volume.restrict (Ioc 0 s))
        (fun t => ((t : ℂ) ^ (μ : ℂ)) • (D.ev.U s t) (gBD D B t))
      rw [conjXL_apply] at h3
      rw [← h3]
      refine integral_congr_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      rw [conjXL_apply, conjX_smul, D.ev.real, gBD_real, conj_cpow_real ht.1]
    rw [h1, h2]
  · rw [xiD_nonpos D _ B (not_lt.1 hs)]
    refine xmc_ext ?_
    filter_upwards [xFn_conjX (0 : Xmc c m), ae_cell_of_ae_cellMeasure
      (Lp.coeFn_zero ℂ 2 (B0579.cellMeasure c m))] with x h1 h2
    rw [h1]
    have e : xFn (0 : Xmc c m) x = 0 := h2
    rw [e, map_zero]

end Data

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
