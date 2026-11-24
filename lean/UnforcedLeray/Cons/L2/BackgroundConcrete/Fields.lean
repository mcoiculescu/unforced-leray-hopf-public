import UnforcedLeray.Cons.C03Background.RawLift
import UnforcedLeray.Lib.AxisymmetricB.Stream
import UnforcedLeray.Lib.AxisymmetricB.DSS
import UnforcedLeray.Lib.Axisymmetric.PhysicalChart
import UnforcedLeray.Blueprint.Construction.Cylinder
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Theorem B3, concrete scheme: the parameters and the pointwise fields

`paper/main.tex`, Section `sec:background` (lines 5070–5303): the parameters (2.1), the actual
train and the raw lift `U_raw` (Section `sec:st18-6030`, lines 5195–5205; `eq:m3-ring-lift`,
lines 2070–2098; units B0140, B0186), the frozen inlet `E_bg = E_ε`
(`eq:m2-background-inlet`, lines 5143–5160; (2.26)–(2.27), lines 5264–5303; units B0303,
B0297, B0298) and the common DSS datum (2.8) with its stream formula (2.27) (lines 5123–5129,
5288–5303; units B0687, B0298).

## The objects

| Lean | Manuscript |
|---|---|
| `Params` | `ν`, `c`, `ε = R⁻¹`, `Σ` (`H_bg = Σ/ν`), the planar eigenvorticity profile `h` of `q = h(r)e^{2iϑ}` (G1), and the train solvability (B0141) |
| `Params.train` | "the single actual train … with its decaying stream" (line 5199; B0140's `train`) |
| `axisExt` | "its smooth Cartesian extension" (line 5201): the off-axis formula, and on the axis its limit from off the axis |
| `Params.raw` | `U_raw = U_R = √s[v₁e_r + (v₂ + εH)e_z]` (line 5200, `eq:m3-ring-lift`) |
| `ageCutoff` | "a smooth age cutoff equal to one near zero and zero before `H = Σ/ν`" (lines 5282–5283) |
| `Params.frozenStream` | the streams of the frozen columns `(2Re P_cq, −2Im P_cq)` (lines 5145–5147, 5264–5266) |
| `Params.inletProfile` | the normalized components `e_ε = (−χψ_η, χψ_q + ε[(χ − 2sχ')ψ − χηψ_η])` of the cutoff stream lift (B0298; `Axi.ringStreamProfile`) |
| `Params.inlet` | `E_ε` (the ring lift `√s e_ε`) |
| `Params.datum` | the datum `a = a_raw + a_α` of (2.8), in the stream form (2.27) at `q = R log(ϱ/R)`, `η = Rz/ϱ` with the stream `ψ(0) + ψ_α` |

The age cutoff is `χ(s) = smoothTransition(2 - 4s/H)`: equal to one on `s ≤ H/4` and zero on
`s ≥ H/2` (`ageCutoff_eq_one`, `ageCutoff_eq_zero`), a valid instance of "a smooth age cutoff"
(the manuscript's statements hold for every such cutoff).

Junk values: on the axis Lean's `Axi.Nv` is `0` (`√(R²/0) = 0`). The inlet vanishes near the axis
(the cutoff vanishes at large age `s = R²/ϱ²`), and the datum's stream decays in `η = Rz/ϱ`
(exponential transverse tails, (2.26)), so `0` is their value on the axis; `U_raw` is extended
through the axis by `axisExt`.

## Proved here

* `frozenStream_periodic`, `inletProfile_periodic`: the inlet profiles are `c`-periodic in
  `ξ` (the periodization `P_c` is a sum over all cells, reindexed by one cell);
* `raw_eq_off_axis`: `U_raw` is the ring lift off the axis;
* `datum_symmetric`: the datum is axisymmetric without swirl (B0298, (2.27));
* `datum_dss`: `a(e^{P/2}x) = e^{-P/2}a(x)` for every `x` (B0298: "it is the same datum in every
  DSS cell"; (2.8)), from the `c`-periodicity of the train stream `ψ(0)` and of the frozen
  streams.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.Blueprint UnforcedLeray.Axi UnforcedLeray.GaussianVortex
open UnforcedLeray.B0140

/-! ## The parameters -/

/-- The parameters of the background at one level (`background:eq:2.1`, lines 5070–5075, and
lines 5143–5160, 5282–5283): viscosity `ν`, train period `c`, ring parameter `ε = R⁻¹`, slow
terminal age `Σ` (`H_bg = Σ/ν`), the planar eigenvorticity profile `h` (`q = h(r)e^{2iϑ}`, G1),
and the single actual train solving its IVP at `(ν,c)` (B0141). -/
structure Params where
  ν : ℝ
  c : ℝ
  ε : ℝ
  /-- The slow terminal age `Σ`, `H_bg = Σ/ν`. -/
  ageCut : ℝ
  /-- The radial profile `h` of the planar eigenvorticity `q = h(r)e^{2iϑ}` (G1). -/
  mode : Planar.Profile
  ν_pos : 0 < ν
  c_pos : 0 < c
  ε_pos : 0 < ε
  ageCut_pos : 0 < ageCut
  /-- The single actual train at `(ν,c)`; all raw and datum fields use this same witness. -/
  trainData : TrainSol ν c

namespace Params

variable (p : Params)

/-- The period `P = 2εc` (`background:eq:2.1`). -/
def period : ℝ := 2 * p.ε * p.c

theorem period_pos : 0 < p.period := by
  unfold period
  have := p.ε_pos
  have := p.c_pos
  positivity

instance : Fact (0 < p.period) := ⟨p.period_pos⟩

/-- The ring radius `R = ε⁻¹`. -/
def R : ℝ := p.ε⁻¹

theorem R_pos : 0 < p.R := inv_pos.2 p.ε_pos

theorem period_eq : p.period = 2 * p.c / p.R := by
  rw [period, R, div_inv_eq_mul]
  ring

/-- The terminal age `H_bg = Σ/ν` (line 5156). -/
def H : ℝ := p.ageCut / p.ν

theorem H_pos : 0 < p.H := div_pos p.ageCut_pos p.ν_pos

/-- **The actual train** (line 5199: "Use the single actual train of Section
`sec:st18-3303`, with its decaying stream"; B0140, B0141). This is the stored value, not a
second choice from a nonemptiness proof. -/
def train : TrainSol p.ν p.c := p.trainData

end Params

/-! ## The raw lift -/

open Classical in
/-- The extension of a field through the axis by its limit from off the axis ("smooth Cartesian
extension", line 5201). Off the axis it is the field itself. -/
def axisExt (f : Space → Space) (y : Space) : Space :=
  if y ∈ axis then limUnder (𝓝[axisᶜ] y) f else f y

theorem axisExt_of_not_mem {f : Space → Space} {y : Space} (hy : y ∉ axis) :
    axisExt f y = f y := by
  simp only [axisExt, hy, ↓reduceIte]

namespace Params

variable (p : Params)

/-- **`U_raw = U_R = √s[v₁e_r + (v₂ + εH)e_z]`** (line 5200, `eq:m3-ring-lift`, B0186): the
ring lift (radius `R = ε⁻¹`) of the profile `b_raw = (v₁, v₂ + εH)` of the actual train,
extended through the axis. -/
def raw (τ : ℝ) : SpatialField :=
  axisExt (Nv p.R (rawProfile p.ε p.train.v p.train.ψ) τ)

theorem raw_eq_off_axis (τ : ℝ) (y : Space) (hy : y ∉ axis) :
    p.raw τ y = Nv p.ε⁻¹ (rawProfile p.ε p.train.v p.train.ψ) τ y :=
  axisExt_of_not_mem hy

end Params

/-! ## The frozen inlet -/

/-- **The age cutoff** `χ(s) = smoothTransition(2 - 4s/H)` (lines 5282–5283): smooth, equal to
one near zero and zero before `H`. -/
def ageCutoff (H s : ℝ) : ℝ := Real.smoothTransition (2 - 4 * s / H)

theorem ageCutoff_eq_one {H s : ℝ} (hH : 0 < H) (hs : s ≤ H / 4) : ageCutoff H s = 1 := by
  apply Real.smoothTransition.one_of_one_le
  have : 4 * s / H ≤ 1 := by
    rw [div_le_one hH]
    linarith
  linarith

theorem ageCutoff_eq_zero {H s : ℝ} (hH : 0 < H) (hs : H / 2 ≤ s) : ageCutoff H s = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  have : 2 ≤ 4 * s / H := by
    rw [le_div_iff₀ hH]
    linarith
  linarith

theorem contDiff_ageCutoff (H : ℝ) {n : ℕ∞} : ContDiff ℝ n (ageCutoff H) := by
  show ContDiff ℝ n (Real.smoothTransition ∘ fun s => 2 - 4 * s / H)
  exact Real.smoothTransition.contDiff.comp
    (contDiff_const.sub ((contDiff_const.mul contDiff_id).div_const H))

/-- The periodization `P_c` is `c`-periodic in the first variable (the sum over all cells,
reindexed by one cell). -/
theorem periodicStream_add_period (f : Planar.Profile) (c : ℝ) (x : ℝ × ℝ) :
    periodicStream f c (x.1 + c, x.2) = periodicStream f c x := by
  unfold periodicStream
  set g : ℤ → ℂ := fun k => planarStream f (x.1 + k * c, x.2) with hg
  have h : ∀ k : ℤ, planarStream f (x.1 + c + k * c, x.2) = g (Equiv.addRight (1 : ℤ) k) := by
    intro k
    simp only [hg, Equiv.coe_addRight, Int.cast_add, Int.cast_one]
    ring_nf
  rw [tsum_congr h]
  exact (Equiv.addRight (1 : ℤ)).tsum_eq g

namespace Params

variable (p : Params)

/-- **The frozen streams** of the ordered frozen columns `(2Re P_cq, −2Im P_cq)` (lines
5145–5147, 5264–5266; B0303): the streams `2Re P_cΔ⁻¹q` and `-2Im P_cΔ⁻¹q` of the planar
eigenvorticity `q = h(r)e^{2iϑ}`, periodized with period `c`. -/
def frozenStream (i : Fin 2) : ℝ × ℝ → ℝ :=
  ![fun x => 2 * (periodicStream p.mode p.c x).re,
    fun x => -2 * (periodicStream p.mode p.c x).im] i

theorem frozenStream_periodic (i : Fin 2) (x : ℝ × ℝ) :
    p.frozenStream i (x.1 + p.c, x.2) = p.frozenStream i x := by
  fin_cases i <;> simp [frozenStream, periodicStream_add_period]

/-- The cutoff stream `χ(s)ψ_i(ξ, η)` of the inlet column `i` (lines 5283–5285). -/
def cutStream (i : Fin 2) (m : ℝ × (ℝ × ℝ)) : ℝ := ageCutoff p.H m.1 * p.frozenStream i m.2

/-- **The normalized components of the inlet column `i`** (B0298, tex 5288–5295):
`e_ε = (−χψ_η, χψ_q + ε[(χ − 2sχ')ψ − χηψ_η])`, the components of the exact physical stream
lift of `ϱ·χψ` (`Axi.ringStreamProfile`, `Axi.ringStreamLift_components`). -/
def inletProfile (i : Fin 2) : ℝ × (ℝ × ℝ) → Merid :=
  ringStreamProfile p.R (p.cutStream i)

/-- **The frozen inlet column `E_i`** (`eq:m2-background-inlet`, `E_bg = E_ε`): the ring lift
`√s e_ε` of the normalized components. -/
def inlet (i : Fin 2) (τ : ℝ) : SpatialField := Nv p.R (p.inletProfile i) τ

end Params

/-- A function invariant under a translation has translation-invariant derivative. -/
theorem fderiv_add_of_invariant {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {a : E} (hf : ∀ x, f (x + a) = f x)
    (x : E) : fderiv ℝ f (x + a) = fderiv ℝ f x := by
  rw [← fderiv_comp_add_right]
  congr 1
  funext y
  exact hf y

namespace Params

variable (p : Params)

theorem cutStream_add (i : Fin 2) (m : ℝ × (ℝ × ℝ)) :
    p.cutStream i (m + (0, (p.c, 0))) = p.cutStream i m := by
  obtain ⟨s, ξ, η⟩ := m
  simp only [cutStream, Prod.mk_add_mk, add_zero]
  rw [show ((ξ + p.c, η) : ℝ × ℝ) = ((ξ, η).1 + p.c, (ξ, η).2) from rfl,
    p.frozenStream_periodic]

/-- **The inlet profiles are `c`-periodic in `ξ`** ("Periodizing the harmonic part", line
5268; B0297, B0298). -/
theorem inletProfile_periodic (i : Fin 2) (s ξ η : ℝ) :
    p.inletProfile i (s, (ξ + p.c, η)) = p.inletProfile i (s, (ξ, η)) := by
  have hm : ((s, (ξ + p.c, η)) : ℝ × (ℝ × ℝ)) = (s, (ξ, η)) + (0, (p.c, 0)) := by
    simp only [Prod.mk_add_mk, add_zero]
  have hd := fderiv_add_of_invariant (p.cutStream_add i) (s, (ξ, η))
  rw [inletProfile, ringStreamProfile, ringStreamProfile, dEta, dQ, dS, hm, hd,
    p.cutStream_add i]
  simp only [Prod.fst_add, Prod.snd_add, add_zero]
  rfl

end Params

/-! ## The datum -/

/-- The meridional components of the stream datum (2.27) at `(q, η)` for a stream `Ψ(q, η)`:
`(−Ψ_η, Ψ_q + ε(Ψ − ηΨ_η))` (lines 5288–5293). -/
def datumProfile (ε : ℝ) (Ψ : ℝ × ℝ → ℝ) (x : ℝ × ℝ) : Merid :=
  (-(partialEta Ψ x)) • m0 + (partialXi Ψ x + ε * (Ψ x - x.2 * partialEta Ψ x)) • m1

theorem datumProfile_periodic {ε c : ℝ} {Ψ : ℝ × ℝ → ℝ} (hΨ : ∀ x : ℝ × ℝ, Ψ (x.1 + c, x.2) = Ψ x)
    (ξ η : ℝ) : datumProfile ε Ψ (ξ + c, η) = datumProfile ε Ψ (ξ, η) := by
  have hinv : ∀ x : ℝ × ℝ, Ψ (x + (c, 0)) = Ψ x := by
    intro x
    rw [show x + (c, 0) = (x.1 + c, x.2) from Prod.ext rfl (add_zero _)]
    exact hΨ x
  have hm : ((ξ + c, η) : ℝ × ℝ) = (ξ, η) + (c, 0) := by simp
  have hd := fderiv_add_of_invariant hinv (ξ, η)
  rw [datumProfile, datumProfile, partialEta, partialXi, partialEta, partialXi, hm, hd, hinv]
  simp only [Prod.snd_add, add_zero]

namespace Params

variable (p : Params)

/-- The stream of the datum with inlet adjustment `α`: `ψ(0) + α₁ψ⁽¹⁾ + α₂ψ⁽²⁾`, the train's
decaying stream at age zero plus the frozen streams (lines 5283–5293; the cutoff is one at
`s = 0`). -/
def datumStream (α : Fin 2 → ℝ) (x : ℝ × ℝ) : ℝ :=
  p.train.ψ 0 x + ∑ i : Fin 2, α i * p.frozenStream i x

theorem datumStream_periodic (α : Fin 2 → ℝ) (x : ℝ × ℝ) :
    p.datumStream α (x.1 + p.c, x.2) = p.datumStream α x := by
  simp only [datumStream]
  rw [stream_periodic_of_isTrain p.train.isTrain le_rfl x]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [p.frozenStream_periodic]

/-- **The common DSS datum** (`background:eq:2.8`, with the stream form (2.27); lines
5123–5129, 5288–5303, 5852–5870; units B0687, B0298): `a = (R/ϱ)[(−ψ_η)e_r +
(ψ_q + ε(ψ − ηψ_η))e_z]` at `q = R log(ϱ/R)`, `η = Rz/ϱ`, for the stream
`ψ = ψ(0) + ψ_α`. In the library's chart it is the ring lift at phase `τ = 0` of the
age-independent profile `datumProfile ε ψ`. -/
def datum (α : Fin 2 → ℝ) : SpatialField :=
  Nv p.R (fun m => datumProfile p.ε (p.datumStream α) m.2) 0

/-- The datum is axisymmetric without swirl (B0298: "`a_α` is axisymmetric without swirl"). -/
theorem datum_symmetric (α : Fin 2 → ℝ) : IsAxisymmetricNoSwirl (p.datum α) :=
  isAxisymmetricNoSwirl_Nv _ _ _

theorem age_smul {R k : ℝ} (hk : 0 < k) (y : Space) : age R (k • y) = age R y / k ^ 2 := by
  rw [age, age, ϱ_smul, abs_of_pos hk, mul_pow, div_div, mul_comm]

theorem trans_smul {R k : ℝ} (hk : 0 < k) (y : Space) : Axi.trans R (k • y) = Axi.trans R y := by
  by_cases hy : y ∈ axis
  · have h0 : ϱ y = 0 := (mem_axis_iff y).1 hy
    rw [Axi.trans, Axi.trans, ϱ_smul, h0, mul_zero, div_zero, div_zero]
  · have hρ := ϱ_pos hy
    rw [Axi.trans, Axi.trans, ϱ_smul, abs_of_pos hk]
    simp only [PiLp.smul_apply, smul_eq_mul]
    field_simp

/-- **The datum is discretely self-similar** with factor `e^{P/2}` (`background:eq:2.8`;
B0298: "one periodic stream and one coefficient vector … the same datum in every DSS cell"). -/
theorem datum_dss (α : Fin 2 → ℝ) (x : Space) :
    p.datum α (Real.exp (p.period / 2) • x) = Real.exp (-(p.period / 2)) • p.datum α x := by
  set k := Real.exp (p.period / 2) with hk
  have hk0 : 0 < k := Real.exp_pos _
  have hkinv : Real.exp (-(p.period / 2)) = k⁻¹ := by rw [Real.exp_neg]
  rw [hkinv]
  by_cases hx : x ∈ axis
  · have h0 : ϱ x = 0 := (mem_axis_iff x).1 hx
    have h0' : ϱ (k • x) = 0 := by rw [ϱ_smul, h0, mul_zero]
    simp only [datum, Nv, age, h0, h0', ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, div_zero, Real.sqrt_zero, zero_smul, smul_zero]
  · have hR := p.R_pos
    have hage := age_pos hR.ne' hx
    have hlog : Real.log (age p.R (k • x)) = Real.log (age p.R x) - p.period := by
      rw [age_smul hk0, Real.log_div hage.ne' (pow_pos hk0 2).ne', Real.log_pow, hk,
        Real.log_exp]
      push_cast
      ring
    have hphase : phase p.R 0 (k • x) = phase p.R 0 x + p.c := by
      rw [Axi.phase, Axi.phase, hlog, p.period_eq]
      field_simp
      ring
    have hsq : √(age p.R (k • x)) = k⁻¹ * √(age p.R x) := by
      rw [age_smul hk0, Real.sqrt_div' _ (pow_nonneg hk0.le 2), Real.sqrt_sq hk0.le]
      ring
    simp only [datum, Nv, chart]
    rw [hsq, hphase, trans_smul hk0, frameL_smul hk0,
      datumProfile_periodic (p.datumStream_periodic α), smul_smul]

end Params

end UnforcedLeray.Cons.C03.Concrete
